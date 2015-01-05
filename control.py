#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
    control.py
    ~~~~~~~~~~

    GDI control center.
    Use the command line help to find out about functionalities.
    Basically it is:

    - Database creation, reading, updating and deletion.
      Import from various formats and export to XML
    - Use XML database to create spreadsheets

    TODO:

    * Probably switch to click sometime
      http://click.pocoo.org/

    You can use --help, but here is a complete list of commands:

    init [--to-xml $metadata.xml] [--to-encoding $utf-8]
    init --from-cli [--to-xml $metadata.xml] [--to-encoding $utf-8]
    init --from-xml $oldmetadata.xml [--to-xml $metadata.xml] [--to-encoding $utf-8]
    students create [--to-xml $students.xml] [--to-encoding $utf-8]
    students create --from-cli [--to-xml $students.xml] [--to-encoding $utf-8]
    students create [--from-csv $csvfile]+ [--from-encoding $utf-8-sig] [--to-xml $students.xml] [--to-encoding $utf-8]
    students read [--students $students.xml] --to-To-header COMMANDS
    students read [--students $students.xml] --to-unprocessed-registrations COMMANDS
    students read [--students $students.xml] --to-group-meta-preferences COMMANDS
    students read [--students $students.xml] COMMANDS
        where COMMANDS is
            (--group-by-group|--group-by-regdate)
            (--all-email|--all-wikiname|--all-matriculation-number)
            (--filter $key=$value)*
            --filter-newer-than $date
            --filter-older-than $date
    students update [--students $students.xml] --matriculation-number $matrnr
    students update [--students $students.xml] --from-csv $csvfile [--from-encoding $utf-8-sig] [--to-xml $students2.xml] [--to-encoding $utf-8]
    students update [--students $students.xml] --from-xml $otherstudents.xml [--to-xml $students2.xml] [--to-encoding $utf-8]
    students update [--students $students.xml] [--import-grade $spreadsheetcsv]+
    students delete [--students $students.xml] --matriculation-number
    students export [--students $students.xml] --to-csv
    students diff [$file.xml|$file.csv]
    students unify [$file.xml]+
    spreadsheets create [--students $students.xml] [--metadata $metadata.xml] [--grading $GradingPoints.txt] [--grading-encoding $utf-8-sig] [--group $grp_id] [--to-csv $csv_file] [--to-encoding $utf-8-sig]
    spreadsheets read [--students $students.xml] [--group $grp_id]
    spreadsheets update [--students $students.xml] [--group $grp_id]
    foswiki permissions --check $folder
    foswiki permissions --modify $spec
    foswiki users --all-exist $webindexfile
    foswiki users --check-consistency-with-db $folder
    stats create
    recreate

    ./spreadsheets.py pertwikiname "TWikiname is {}" file.csv

    Usecases:
      Validate user-DB and metadata corresponds to ListOfTutors, WikiUsers and RoomsAndGroups


    Requirements:
      - lxml.etree == 3.4.0

    (C) 2014, Lukas Prokop
"""

import io
import re
import sys
import csv
import copy
import math
import os.path
import logging
import argparse
import datetime
import textwrap
import functools
import lxml.etree
import collections
import unicodedata

import click  # http://click.pocoo.org/

__author__ = 'Lukas Prokop'
__version__ = '0.0.1-alpha'
__license__ = 'Public Domain'
__program__ = 'control.py'

# global variables automatically set at runtime
metadata = None
students = None

# tested with python 3.4
assert sys.version_info >= (3, 2), "python2 unsupported"

# -------------------------------- config ---------------------------------

class csv_export_dialect:
    quotechar = '"'
    escapechar = None
    doublequote = True
    skipinitialspace = False
    lineterminator = '\n'
    quoting = csv.QUOTE_ALL

class csv_export_dialect_semicolon(csv_export_dialect):
    delimiter = ';'

# Map CSV header fields to XML elements
MAPPING_CSV_XML = {
    'Gruppe': 'group',
    'Familien- oder Nachname': 'lastname',
    'Vorname': 'firstname',
    'Matrikelnummer': 'matriculation-number',
    'Studium': 'degree-programme',
    'Anmeldedatum': 'registration-date',
    'E-Mail': 'email'
}

# Map XML elements to Main/UnprocessedRegistrations header fields
MAPPING_XML_REGISTRATION = {
    'firstname': 'FirstName',
    'lastname': 'LastName',
    'email': 'Email',
    'wikiname': 'WikiName'
}


# --------------------------------- texts ---------------------------------
#                    you should not need to change that                    

CLI_DIFF = ("Compare database with CSV or foswiki table. "
    "Create new database with users in given file but not database.")
CLI_CREATE = ("Register students. Either via CLI or import data from CSV.")
CLI_READ = ("List students grouped by certain values or "
    "only all values of a particular field. "
    "Also possibly apply some filter.")

ABORT = "Aborted on user request"

NEWLINE = os.linesep

STUDENT_STR = '''Student #{matrnr}
  group        = {group}
  lastname     = {lastname}
  firstname    = {firstname}
  wikiname     = {wikiname}
  degree prg   = {degree}
  registration = {regdate}
  email        = {email}
  grade        = {grade}
'''

UPDATE = '''
  Found {} new students.
  Determined {} removed students.

Shall I …
  (k) keep current students / quit
  (r) replace current students with new dataset
  (n) store only new students not in current dataset
  (i) store the intersection of both datasets
  (u) store the union of both datasets
'''

ERROR_ISO8601 = ('Please stick to ISO-8601 to specify timestamps '
    '(eg. "2014-10-18T23:47:06.722897")')

INIT_PRELUDE = '''Hi!

This routine initializes the control center. We use a file called
metadata.xml to store general information about the course. Afterwards
you can apply some operation to introduce all students, generate
spreadsheets, check your Foswiki installation and finally generate
statistics or your CSV to submit grades.

As an overview:
  Files created by this application:
    students.xml             Database of all students
    metadata.xml             Meta data about the course
                             (tutors, assignments, grades)

  Files used as a source (defined in metadata.xml):
    GradingPoints.txt        Grading points for this term
    TN_LV716231_$DATE.csv    Some CSV source for students.xml

'''

# ------------------------------- CLI tools -------------------------------

def confirm(question, default=True):
    """Ask user a binary question on the CLI. Return True or False.

    :param question:        the question to ask
    :type question:         str
    :param default:         value to take if empty string "" was answered
    :type default:          str
    :return:                Did user type something like 'y', 'Yes', etc?
    :type return:           bool
    """
    yes = {'y', 'j'}

    print()
    print('  ' + question.strip())
    print()
    answer = input('Answer (y/n): ')

    if not answer:
        return default
    return answer[0].lower() in yes


def ask(question, mapping):
    """Ask a question on the CLI. Mapping is a mapping between shortcuts
    and a value to return, if the corresponding shortcut was entered.
    Raises SystemExit if quit is entered.

    Shortcuts are normalized to lowercase and trimmed whitespace.

    :param question:        The general question to ask
    :type question:         str
    :param mapping:         { shortcut(str): value(*) }
    :type mapping:          dict
    :return:                (shortcut, value)
    :type return:           tuple
    """
    mapping = mapping.copy()
    assert 'q' not in mapping.keys(), ('q must not be in mapping. '
                                       'Denotes quit')
    mapping['q'] = 'Quit / abort / exit'

    print(question)
    print()
    for sc, meaning in sorted(mapping.items(), key=lambda x: str(x[0])):
        print("  ({}) {}".format(sc, meaning))
    print()
    while True:
        selection = input('Select {}: '.format('/'.join(map(str, mapping.keys()))))
        selection = selection.lower().strip()
        if selection == 'q':
            raise SystemExit("User triggered quit")
        for sc in mapping.keys():
            if selection == str(sc).lower().strip():
                return (sc, mapping[sc])


def request(question, datatype=str, *, nonempty=True):
    """Request some value of `type` from the CLI.

    :param question:        the general question to ask
    :type question:         str
    :param datatype:        the datatype of the answer
    :type datatype:         type
    :return:                the value of datatype `type`
    """
    if datatype != str:
        msg = 'The answer to this question should be of type {}'
        print(msg.format(datatype.__name__))

    valid = False
    while not valid:
        response = input('  ' + question + ' ')
        try:
            value = response
            if not value and not nonempty:
                return value
            value = datatype(value)
            if datatype is str:
                value = value.strip()
            if datatype is str and not value and nonempty:
                print('Sorry, a non-empty value is required')
                valid = False
            else:
                valid = True
        except (ValueError, TypeError):
            print('Sorry, this value is invalid')
            valid = False
    return value


def info(message, *args, **argf):
    """Inform user with `message`"""
    msg = message.format(*args, **argf)
    print(msg)
    print()


def warn(message, *args, **argf):
    """Warn user with `message`"""
    msg = message.format(*args, **argf)
    print('Warning!  ' + msg, file=sys.stderr)


def print_cli_table(table, indentation=0, *, stream=sys.stdout):
    """Given a `table` like ``[['name', 'date'], ['Alan', 1954]]``,
    the table is printed at the stdout like::

        ==== ====
        name date
        ---- ----
        Alan 1954
        ==== ====

    with an space-based prefix of length `indentation` per line.
    Be aware that the first line is considered to contain table headers.

    :param table:       A list containing the table content
    :type table:        list | tuple
    :param indentation: The indentation to use
    :type indentation:  int
    :param stream:      the stream to print
    :type stream:       filehandler
    """
    center = lambda x, w: str(x).center(w)
    leftify = lambda x, w: str(x).ljust(w)

    E_INC = "Inconsistent CLI table. Had {} columns in header line. " \
          + "Has {} columns at row {}."

    # parameter checks
    indentation = ' ' * indentation
    max_len = [len(col) for col in table[0]]  # per column
    for row_id, row in enumerate(table):
        if len(max_len) != len(row):
            raise ValueError(E_INC.format(len(max_len), len(row), row_id))
        for col_id, col in enumerate(row):
            col = str(col)
            if max_len[col_id] < len(col):
                max_len[col_id] = len(col)

    # print header line
    t0 = table[0]
    header = [center(col, max_len[ci]) for ci, col in enumerate(t0)]
    hl = ['=' * max_len[ci] for ci, col in enumerate(t0)]
    hl = indentation + ' '.join(hl)

    print(hl, file=stream)
    print(indentation + ' '.join(header), file=stream)
    print(hl.replace('=', '-'), file=stream)

    # print following rows
    for row_id, row in enumerate(table[1:]):
        body = [leftify(col, max_len[ci]) for ci, col in enumerate(row)]
        print(indentation + ' '.join(body), file=stream)

    bl = ['-' * max_len[ci] for ci, col in enumerate(t0)]
    print(hl, file=stream)

_ = {
  'arg' : [['name', 'date'], ['Alan', 1954]],
  'expect' : ' ==== ====\n name date\n ---- ----\n Alan 1954\n ==== ====\n',
  'catch' : io.StringIO()
}
print_cli_table(_['arg'], 1, stream=_['catch'])
assert(_['catch'].getvalue() == _['expect'])


# -------------------------------- helpers --------------------------------
#      if you need to change something down here I did something wrong     


def gentolist(f):
    """A decorator converting a generator to a list::

        >>> def func(x):
        ...     for i in range(x):
        ...         yield i
        >>> func(5)
        <generator object func at 0x7f4a646e1048>
        >>> @gentolist
        ... def func(x):
        ...     for i in range(x):
        ...         yield i
        >>> func(5)
        [0, 1, 2, 3, 4]
    """
    @functools.wraps
    def inner(*args, **kwargs):
        return list(f(*args, **kwargs))
    return inner


def read_foswiki_table(filepath, *, encoding='utf-8-sig'):
    """Read a Foswiki table from a Foswiki article.
    Remark. Markup is *not* removed!

    :param filepath:        Filepath to read file from
    :type filepath:         str
    :param encoding:        Encoding of text file at filepath
    :type encoding:         str
    """
    def normalize(f):
        if len(f) > 0 and f.strip() == '':
            return ' '
        else:
            return f

    found_table = False
    table = []
    with open(filepath, encoding=encoding) as fp:
        for line in fp.readlines():
            if '|' not in line:
                if found_table:
                    break
                else:
                    continue
            fields = line.split('|')
            if fields[0] != '':
                raise ValueError('Table line must start with |, but got: ' + fields[0])
            if fields[-1].strip() != '':
                raise ValueError('Table line must end with |, but got: ' + fields[-1])
            table.append([normalize(f) for f in fields[1:-1]])
    return table


def print_foswiki_table(table, *, stream=sys.stdout):
    """Given a `table` like ``[['name', 'date'], ['Alan', 1954]]``,
    the table is printed at the stdout like::

        | *name* | *date* |
        |  Alan  |  1954  |

    Be aware that the first line is considered to contain table headers.
    Headers are centered. Other lines are left-aligned.

    :param table:       A list containing the table content
    :type table:        list | tuple
    :param stream:      the stream to print
    :type stream:       filehandler
    """
    center = lambda x: '  ' + str(x) + '  '
    leftify = lambda x: ' ' + str(x) + ' '
    min_width = 30
    LINE = '|{}|'
    SEP = '|'

    def value(text, is_header):
        text = str(text)
        assert '\n' not in text
        if is_header:
            return center(text and '*' + text + '*' or '')
        else:
            return leftify(text)

    for rowid, row in enumerate(table):
        if rowid == 0:
            print(LINE.format(SEP.join(value(t, True) for t in row)))
        else:
            print(LINE.format(SEP.join(value(t, False) for t in row)))


def parse_group_id(val):
    """Parse a group identifier like 'Standardgruppe' or 'Gruppe 3'.
    Convention.
      Group 0 represents lecture participants.

    :param val:     The group identifier
    :type val:      str
    :return:        the group as non-negative integer
    :type return:   int
    """
    if val.lower() == 'Standardgruppe'.lower():
        return 0
    return int(re.sub(r'\D', '', val), base=10)


def parse_iso8601(datestr):
    """Parse an ISO date like '2014-10-18T23:47:06.722897' as returned
    by (eg.) `datetime.datetime.now().isoformat()`.

    :param datestr:     string representation of a date compling to ISO 8601
    :type datestr:      str
    :return:            datetime instance
    :type return:       datetime
    """
    # TODO: not standard compilant
    return datetime.datetime.strptime(datestr[0:19], '%Y-%m-%dT%H:%M:%S')


def parse_date(datestr):
    """Parse some user string which specifies a date.

    :param datestr:     user string containing datetime
    :type datestr:      str
    :return:            datetime instance
    :type return:       datetime.datetime
    """
    guessed_parsing = [
        lambda t: parse_iso8601(t),
        lambda t: datetime.datetime.strptime(t, '%d.%m.%Y,%H:%M'),
        lambda t: datetime.datetime.strptime(t, '%d-%m-%Y'),
        lambda t: datetime.datetime.strptime(t, '%Y-%m-%d')
    ]
    for parsing_algo in guessed_parsing:
        try:
            return parsing_algo(datestr)
        except ValueError:
            continue

    raise ValueError(ERROR_ISO8601)


def default_spreadsheet_filepath():
    """Return default filepath for group spreadsheet

    :return:        default filepath
    :type return:   str
    """
    return 'group{group}-{assignment}.csv'


def default_gradingpoints_filepath():
    """Return default filepath for grading points

    :return:        default filepath
    :type return:   str
    """
    return 'GradingPoints.txt'

def default_metadata_filepath():
    """Return default filepath for metadata.xml

    :return:        default filepath
    :type return:   str
    """
    return 'metadata-{}.xml'.format(datetime.datetime.now().strftime('%y'))


def default_students_filepath():
    """Return default filepath for students.xml

    :return:        default filepath
    :type return:   str
    """
    return 'students-{}.xml'.format(datetime.datetime.now().strftime('%y'))


# ------------------------------ data model -------------------------------

class HashableDict(dict):
    def __hash__(self):
        return hash(tuple(sorted(self.items())))


class Student:
    """A class representing a student"""
    matrnr = 0
    group = set()
    lastname = ''
    firstname = ''
    degree = ''
    regdate = datetime.datetime.now()
    email = ''
    grade = 0
    _wikiname = ''

    _map = {'matriculation-number': 'matrnr', 'group': 'group',
        'lastname': 'lastname', 'firstname': 'firstname',
        'degree-programme': 'degree', 'registration-date': 'regdate',
        'email': 'email', 'grade': 'grade', 'wikiname': '_wikiname'}

    attributes = ['matrnr', 'group', 'firstname', 'lastname', 'wikiname',
        'email', 'regdate', 'grade', 'degree']

    @staticmethod
    def normalize(attr, val):
        if attr == 'matrnr' or attr == 'grade':
            return int(val, base=10)
        elif attr == 'group':
            return {parse_group_id(val),}
        elif attr == 'registration-date':
            return parse_date(val)
        else:
            return str(val)

    def get_from_xml(self, name):
        try:
            return getattr(self, self._map[name])
        except IndexError:
            raise ValueError("Student data " + name + " unknown")

    def set_from_xml(self, name, value, *, add=False):
        try:
            attr = self._map[name]
            val = self.normalize(attr, value)
            if attr == 'group' and add:
                val = val.union(self.group)
            if attr == 'regdate':
                val = parse_date(val)
            setattr(self, attr, val)
        except IndexError:
            raise ValueError("Student data " + name + " unknown")

    @property
    def wikiname(self):
        """The 'create wikiname out of first and last name' algorithm."""
        if self._wikiname:
            return self._wikiname

        # TODO: in the future replace "ß" with "ss"
        name = self.firstname + " " + self.lastname
        name = name.replace('-', ' ')
        name = name.replace('\'', ' ')
        name = unicodedata.normalize('NFKD', name).encode('ascii', 'ignore')
        names = [n.title() for n in name.decode('ascii').split()]
        return ''.join(names)

    @wikiname.setter
    def wikiname(self, value):
        self._wikiname = value

    def to_xml(self):
        """Represent student as an XML element.

        :return:        Student as XML element
        :type return:   lxml.etree.Element
        """
        def elem(tag, text=None):
            e = lxml.etree.Element(tag)
            if text:
                e.text = text
            return e

        student = elem('student')
        student.append(elem('matriculation-number', str(self.matrnr)))
        for g in self.group:
            student.append(elem('group', str(g)))
        student.append(elem('lastname', self.lastname))
        student.append(elem('firstname', self.firstname))
        student.append(elem('wikiname', self.wikiname))
        if self.degree:
            student.append(elem('degree-programme', self.degree))
        student.append(elem('registration-date', self.regdate.isoformat()))
        student.append(elem('email', self.email))
        if self.grade:
            student.append(elem('grade', str(self.grade)))

        return student

    def copy(self):
        s = Student()
        s.matrnr = self.matrnr
        s.group = {g for g in self.group}
        s.lastname = self.lastname
        s.firstname = self.firstname
        s.degree = self.degree
        s.regdate = self.regdate
        s.email = self.email
        s.grade = self.grade
        s._wikiname = self._wikiname
        return s

    def __eq__(self, other):
        return self.matrnr == other.matrnr

    def __hash__(self):
        return hash(str(self.matrnr) + str(self.firstname) \
            + str(self.lastname))

    def __repr__(self):
        if self.matrnr == 0:
            return '<Student default>'
        else:
            return '<Student #{}>'.format(self.matrnr)

    def __str__(self):
        if self.matrnr == 0:
            return 'Default student'
        return STUDENT_STR.format(**{'matrnr': self.matrnr,
            'group': self.group, 'lastname': self.lastname,
            'firstname': self.firstname, 'wikiname': self.wikiname,
            'degree': self.degree, 'regdate': self.regdate,
            'email': self.email, 'grade': self.grade})


class StudentDatabase:
    """Database of students"""

    def __init__(self, students=None):
        if not students:
            students = set()

        size = len(students)
        self.students = type(students)(s.copy() for s in students)

        if size != len(self.students):
            raise ValueError("Some student got lost by by creating a hash set. Internal error")

        self.consistency_check(self.students)

    @staticmethod
    def consistency_check(db):
        E_DOUBLE = "{} contained twice in dataset: {}"

        # every matriculation number is unique
        nums = set()
        for s in db:
            if s.matrnr in nums:
                raise ValueError(E_DOUBLE.format("Matriculation number", s.matrnr))
            nums.add(s.matrnr)

        # every wikiname is unique
        names = set()
        for s in db:
            if s.wikiname in names:
                raise ValueError(E_DOUBLE.format("Wikiname", s.wikiname))
            names.add(s.wikiname)

        # everybody: 0 <= #none-zero-groups(student) <= 1
        for s in db:
            if len(s.group.difference({0,})) > 1:
                msg = "Student {} registered in more than 1 non-zero groups: {}"
                raise ValueError(msg.format(s.wikiname, s.group))

    def get_latest_registration_date(self):
        if not self.students:
            raise ValueError("Dataset is empty")
        latest = datetime.datetime(2000, 1, 1)
        for s in self.students:
            if s.regdate > latest:
                latest = s.regdate
        if latest == datetime.datetime(2000, 1, 1):
            raise ValueError("Algorithm does not work for such old dates")
        return latest

    def all_registration_dates(self):
        dates = set()
        for s in self.students:
            dates.add(s)
        return dates

    def all_groups(self):
        groups = set()
        for s in self.students:
            groups = groups.union(s.group)
        return groups

    @staticmethod
    def filtered(db, selectors):
        subset = set()
        for s in db:
            if all([selector(s) for selector in selectors]):
                subset.add(s)
        return StudentDatabase(subset)

    def filter(self, *, matrnr=None, group=None, firstname=None, lastname=None,
        wikiname=None, degree=None, regdate=None, email=None, grade=None,
        regdate_smaller=None, regdate_greater=None, not_matrnr=None):
        selectors = []
        if matrnr:
            selectors.append(lambda s: s.matrnr == matrnr)
        if not_matrnr:
            selectors.append(lambda s: s.matrnr != not_matrnr)
        if group:
            selectors.append(lambda s: group in s.group)
        if firstname:
            selectors.append(lambda s: s.firstname.lower() == firstname.lower())
        if lastname:
            selectors.append(lambda s: s.lastname.lower() == lastname.lower())
        if wikiname:
            selectors.append(lambda s: s.wikiname == wikiname)
        if degree:
            selectors.append(lambda s: s.degree == degree)
        if regdate:
            if regdate_smaller:
                selectors.append(lambda s: s.regdate < regdate)
            elif regdate_greater:
                selectors.append(lambda s: s.regdate > regdate)
            else:
                selectors.append(lambda s: s.regdate == regdate)
        if email:
            selectors.append(lambda s: s.email == email)
        if grade:
            selectors.append(lambda s: s.grade == grade)

        criterion = matrnr or group or firstname or lastname or wikiname \
            or degree or regdate or email or grade
        if criterion:
            info("Filtered students DB by value " + str(criterion))

        return self.filtered(self.students, selectors)

    def group_by_regdate(self):
        classes = collections.defaultdict(list)
        for s in self.students:
            classes[s.regdate].append(s)
        return dict(classes)

    def group_by_group(self):
        classes = collections.defaultdict(list)
        for s in self.students:
            for grp in s.group:
                classes[grp].append(s)
        return dict(classes)

    def sorted_by_group(self):
        by_group = list(self.students)
        by_group.sort(key=lambda x: x.group)
        return StudentDatabase(by_group)

    def sorted_by_wikiname(self):
        by_wikiname = list(self.students)
        by_wikiname.sort(key=lambda x: x.wikiname)
        return StudentDatabase(by_wikiname)

    def sorted_by_matriculation_number(self):
        by_matrnr = list(self.students)
        by_matrnr.sort(key=lambda x: x.matrnr)
        return StudentDatabase(by_matrnr)

    def sorted_by_registration_date(self):
        by_regdate = list(self.students)
        by_regdate.sort(key=lambda x: x.regdate)
        return StudentDatabase(by_regdate)

    def add(self, student):
        """Add an individual student"""
        if student in self:
            original = None
            for s in self.students:
                if s.matrnr == student.matrnr:
                    original = s
            assert original is not None
            original.group = original.group.union(self.group)
        else:
            self.students.add(student.copy())

        self.consistency_check(self.students)

    def union(self, other):
        """Merge both databases"""
        info("Merging two data sets of {} and {} students" \
            .format(len(self), len(other)))
        unionset = set()
        assoc = {}  # matrnr : Student
        for s in self.students:
            c = s.copy()
            assoc[c.matrnr] = c
            unionset.add(c)

        for s in other.students:
            c = s.copy()
            # if duplicate, merge groups and skip
            if s.matrnr in assoc.keys():
                assoc[s.matrnr].group = assoc[s.matrnr].group.union(s.group)
                info("Found some student contained in both sets. " +
                     "Merging groups to " + str(list(assoc[s.matrnr].group)))
            # else add to unionset
            else:
                unionset.add(c)
        info("Merge finished. Union set contains {} students" \
            .format(len(unionset)))
        print(unionset)
        return StudentDatabase(unionset)

    def difference(self, other):
        """Compute the difference between the current and the other dataset"""
        diff = set()
        for s in self.students:
            if s not in other:
                diff.add(s.copy())
        info("Compute difference between 2 sets. "
            + "{}-{} students became {} students." \
            .format(len(self), len(other), len(diff)))
        return StudentDatabase(diff)

    def from_xml(self, xml):
        """Read students database from XML and create StudentDatabase.

        :param xml:                 The XML structure to analyze
        :type xml:                  lxml.etree.Element
        :return:                    a StudentDatabase
        :type return:               StudentDatabase
        """
        students = StudentDatabase()

        for student_element in xml:
            student = Student()
            for data in student_element.iterchildren():
                student.set_from_xml(data.tag, data.text, add=True)
            students.add(student)

        return students

    def to_xml(self):
        xml = lxml.etree.Element('students')
        for student in self.sorted_by_matriculation_number():
            xml.append(student.to_xml())
        return xml

    def __contains__(self, member):
        for s in self.students:
            if s.matrnr == member.matrnr:
                return True
        return False

    def __iter__(self):
        return iter(self.students)

    def __len__(self):
        return len(self.students)

    def __repr__(self):
        return '<StudentsDB containing {} students>'.format(len(self.students))

    def __str__(self):
        out = io.StringIO()
        db = self.sorted_by_matriculation_number()
        updates = len(db.all_registration_dates())
        data = [['matrnr', 'wikiname', 'group', 'email']]
        for s in db.students:
            data.append([s.matrnr, s.wikiname, s.group, s.email])
        print_foswiki_table(data, stream=out)
        out.write('\n{} students registered.\n'.format(len(db.students)))
        out.write('{} updates were provided.\n'.format(updates))
        return out.getvalue()


class Config:
    all_grades = ['excellent', 'good', 'satisfactory', 'sufficient', 'insufficient']

    def __init__(self):
        self.courses = set()
        self.tutors = {}
        self.groups = {}
        self.assignments = []
        self.grades = {}
        self.wikiurl = ''
        self.wikipath = ''

    def add_course(self, title, lecturer, type, id):
        self.courses.add(HashableDict({
            'title': title, 'lecturer': lecturer, 'type': type, 'id': id
        }))

    def add_tutor(self, lastname, firstname, email, groups=None):
        if groups is None:
            groups = set()

        i = 1
        proposal = 't' + str(i)
        while proposal in self.tutors:
            i += 1
            proposal = 't' + str(i)

        self.tutors[proposal] = {
            'lastname': lastname,
            'firstname': firstname,
            'email': email,
            'groups': set(groups)
        }

    def add_group(self, tutor, group_id):
        self.tutors[tutor]['groups'].add(group_id)

    def add_assignment(self, name, deadline, submission, partnersubmission):
        assert name not in self.assignments
        self.assignments.append({
            'name': name,
            'deadline': deadline,
            'submission': submission,
            'partnersubmission': partnersubmission
        })

    def add_grade(self, grade, min_points, max_points):
        assert grade not in self.grades
        self.grades[grade] = {
            'min': int(min_points),
            'max': int(max_points)
        }

    def set_wiki(self, wikiurl=None, wikipath=None):
        if wikiurl is not None:
            self.wikiurl = wikiurl
        if wikipath is not None:
            self.wikipath = wikipath

    def from_xml(self, xml):
        """Retrieve data from XML object and store it in the current object.

        :param xml:     The XML structure to analyze
        :type xml:      lxml.etree.Element
        """
        for element in xml.xpath('/metadata/course'):
            self.add_course(element.attrib['title'], element.attrib['lecturer'],
                element.attrib['type'], element.attrib['id'])

        for element in xml.xpath('/metadata/tutor'):
            groups = xml.xpath('/metadata/group[@tutor="' + element.attrib['id'] + '"]')
            group_ids = map(int, [e.attrib['id'] for e in groups])
            self.add_tutor(
                element.find('lastname'),
                element.find('firstname'),
                element.find('email'),
                group_ids
            )

        for element in xml.xpath('/metadata/assignment'):
            p = element.find('partnersubmission')
            partner = p.text if p is not None else ''
            self.add_assignment(element.attrib['id'],
                parse_date(element.find('deadline').text),
                element.find('submission').text,
                partner)

        for grade in self.all_grades:
            g = xml.xpath('/metadata/grades/' + grade)
            assert len(g) == 1
            self.add_grade(int(g[0].attrib['repr']), g[0].attrib['min'], g[0].attrib['max'])

        self.set_wiki(xml.xpath('/metadata/wikiurl')[0].text, xml.xpath('/metadata/wikipath')[0].text)

    def to_xml(self):
        """Represent data of this object as XML object.

        :return:        object data as XML object
        :type return:   lxml.etree.Element
        """
        xml = lxml.etree.Element('metadata')
        for course in self.courses:
            e = lxml.etree.Element('course')
            e.set('title', course['title'])
            e.set('lecturer', course['lecturer'])
            e.set('type', course['type'])
            e.set('id', course['id'])
            xml.append(e)

        for tid, tutor in self.tutors.items():
            e = lxml.etree.Element('tutor')
            e.set('id', tid)
            lastname = lxml.etree.Element('lastname')
            lastname.text = tutor['lastname']
            e.append(lastname)
            firstname = lxml.etree.Element('firstname')
            firstname.text = tutor['firstname']
            e.append(firstname)
            email = lxml.etree.Element('email')
            email.text = tutor['email']
            e.append(email)
            xml.append(e)

        for tid, tutor in self.tutors.items():
            for grp in tutor['groups']:
                group = lxml.etree.Element('group')
                group.set('tutor', tid)
                group.set('id', grp)
                xml.append(group)

        for ass in self.assignments.items():
            assignment = lxml.etree.Element('assignment')
            assignment.set('id', ass['name'])
            dead = lxml.etree.Element('deadline')
            dead.text = ass['deadline'].isoformat()
            assignment.append(dead)
            sub = lxml.etree.Element('submission')
            sub.text = ass['submission']
            assignment.append(sub)
            if ass['partnersubmission']:
                part = lxml.etree.Element('partnersubmission')
                part.text = ass['partnersubmission']
                assignment.append(part)
            xml.append(assignment)
        
        grades = lxml.etree.Element('grades')
        for sign, grade in enumerate(self.all_grades):
            e = lxml.etree.Element(grade)
            e.set('repr', str(sign))
            e.set('min', self.grades[sign]['min'])
            e.set('max', self.grades[sign]['max'])
            grades.append(e)
        xml.append(grades)

        wikiurl = lxml.etree.Element('wikiurl')
        wikiurl.text = self.wikiurl
        xml.append(wikiurl)
        wikipath = lxml.etree.Element('wikipath')
        wikipath.text = self.wikipath
        xml.append(wikipath)

        return xml


# ---------------------------- XML operations -----------------------------

def write_xml(xml_element, xml_filepath, *, encoding='utf-8'):
    """Write `xml_element` to file system.

    :param xml_element:         XML element to store
    :type xml_element:          lxml.etree.Element
    :param xml_filepath:        File path for XML file
    :type xml_filepath:         str
    :param encoding:            the encoding to use (for xml AND filesystem)
    :type encoding:             str
    """
    tree = lxml.etree.ElementTree(xml_element)

    if xml_filepath == '-':
        tree.write(sys.stdout)
        return 0

    if os.path.exists(xml_filepath):
        if not confirm(xml_filepath + " exists already. Overwrite?"):
            print(ABORT, file=sys.stderr)
            return 0

    with open(xml_filepath, 'wb') as fp:
        tree.write(fp, method='xml', encoding=encoding,
            pretty_print=True, xml_declaration=True)
        info('XML written to file ' + xml_filepath)


def read_xml(xml_filepath):
    """Read XML file to `lxml.etree.Element`.

    :param xml_filepath:    Filepath of XML file to read
    :type xml_filepath:     str
    :return:                XML element representing the read XML tree
    :type return:           lxml.etree.Element
    """
    with open(xml_filepath, 'rb') as fp:
        info('Reading XML from ' + xml_filepath)
        return lxml.etree.XML(fp.read())


# ---------------------------- CSV operations -----------------------------

def parse_student_csv(csv_filepath, *, encoding='utf-8-sig'):
    """Read the CSV content given by `csv_filepath`.

    :param csv_filepath:        File path for CSV file
    :type csv_filepath:         str
    :param encoding:            The encoding to use
    :type encoding:             str
    :return:                    a StudentDatabase instance
    :type return:               StudentDatabase
    """
    filehandler = open(csv_filepath, 'r', encoding=encoding)
    first_bytes = filehandler.read(50)  # TODO: that sucks
    if ";" in first_bytes:
        dialect = csv_export_dialect_semicolon
    else:
        dialect = csv_export_dialect
    filehandler.seek(0)
    reader = csv.reader(filehandler, dialect=dialect)
    header_mapping = {}
    fields = 0

    E_REQ = "At least seven of all CSV fields are required. " \
          + "Only found {} in {}. Adjust MAPPING_CSV_XML!"
    E_INC = "Inconsistent number of fields in CSV. Expected {}, was {}."

    header, *rows = list(reader)

    # interpret header
    if len(header) == 1:
        raise ValueError("Only one column read from CSV. "
            "I guess a wrong dialect was configured.")
    fields = len(header)
    for colid, col in enumerate(header):
        try:
            header_mapping[colid] = MAPPING_CSV_XML[col]
        except KeyError:
            pass

    assert len(list(header_mapping.keys())) >= 7, \
        E_REQ.format(list(header_mapping.values()), str(row))

    # interpret student entries
    students = StudentDatabase()

    for rowid, row in enumerate(rows):
        assert len(row) == fields, E_INC.format(fields, len(row))

        student = Student()
        for colid, attr in header_mapping.items():
            student.set_from_xml(attr, row[colid])

        matrnr = student.get_from_xml('matriculation-number')
        students.add(student)

    if len(students) == 0:
        warn("No students given in CSV {}", csv_filepath)

    return students


def export_student_csv(csv_filepath, students, *, encoding='utf-8-sig'):
    """Export the given `students` database to a TU Graz compatible CSV"""
    raise NotImplementedError("Sorry")  # TODO


# ---------------------------- implementation -----------------------------

def parse_grading_points(grading, encoding='utf-8-sig'):
    """Retrieve a Foswiki table from the given file and parse it.

    :param grading:     the filepath to the Foswiki article with the table
    :type grading:      str
    :param encoding:    the encoding of the grading file
    :type encoding:     str
    """
    bold = lambda v: (lambda t: t[0] == '*' and t[-1] == '*' if t else False)(v.strip())

    table = read_foswiki_table(grading, encoding=encoding)
    if not table:
        raise ValueError("Grading scheme table must not be empty")

    grading = collections.OrderedDict()
    check = {}
    assignment, exercise = None, None
    for row in table:
        assert len(row) == 3, "grading points table must always have 3 columns"
        if bold(row[0]) and row[1] == '':
            assignment = row[0].strip()[1:-1]
            exercise = None
            grading[assignment] = collections.OrderedDict()
            check[assignment] = { 'expect': int(row[2]) }
        elif row[0].strip() == '':
            assert assignment, "Assignment line required before exercise"
            assert exercise, "Exercise line required before points line"
            points, pts = row[1].strip(), int(row[2].strip())
            grading[assignment][exercise][points] = int(pts)
        else:
            assert assignment, "Assignment line required before exercise"
            exercise = row[0].strip()
            grading[assignment][exercise] = collections.OrderedDict()
            check[assignment][exercise] = { 'expect': int(row[2]) }

    # consistency check
    for assignment, v1 in grading.items():
        check[assignment]['points'] = 0
        for exercise, v2 in v1.items():
            check[assignment][exercise]['points'] = 0
            for points, pts in v2.items():
                check[assignment][exercise]['points'] += abs(pts)

            if check[assignment][exercise]['points'] != check[assignment][exercise]['expect']:
                msg = 'Sum of points inconsistent in {}, {} ({} != {})'
                raise ValueError(msg.format(assignment, exercise,
                    check[assignment][exercise]['points'],
                    check[assignment][exercise]['expect']))
            check[assignment]['points'] += check[assignment][exercise]['points']

        if check[assignment]['points'] != check[assignment]['expect']:
            msg = 'Sum of points inconsistent in {} ({} != {})'
            raise ValueError(msg.format(assignment, check[assignment]['points'],
                check[assignment]['expect']))

    return grading


def spreadsheet_cell_id(x, y, *, fixed=False):
    """Get (x, y) coordinates and return cell identifier (like A4).
    Set fixed to True to get a static identifier like $A$4.
    """
    tmpl = "${}${}" if fixed else "{}{}"
    if x < 26:
        return tmpl.format(chr(65 + x), y + 1)
    elif x < 676:
        first = chr(65 + (x // 26))
        second = chr(65 + (x % 26))
        return tmpl.format(first, second)
    else:
        raise ValueError("spreadsheet_cell_id does not support cells beyond ZZ")


def create_title_group_spreadsheet(config, db, grading, group, csvpath, csvenc='utf-8-sig'):
    """Create a group.

    :param config:      A Config to read metadata from
    :type config:       Config
    :param db:          StudentDatabase to use
    :type db:           StudentDatabase
    :param grading:     Data specifying grading points
    :type grading:      dict
    :param group:       The group to generate spreadsheet for
    :type group:        int
    :param csvpath:     The filepath to generate file for
    :type csvpath:      str
    :param csvenc:      Encoding of the filepath
    :type csvenc:       str
    """
    db = db.filter(group=group)
    db = db.sorted_by_wikiname()
    assignments = [v['name'] for v in config.assignments]

    # build grades computation
    grade_recursive = 'IF({}<{},"{}",{{}})'
    grades = [(name, g['max']) for name, g in config.grades.items()]
    grades.sort(key=lambda x: x[1])

    header_row = ['Gruppe', 'Matrikelnummer', 'Vorname', 'Nachname',
        'TWiki Name', 'Abgabegespr. (1..3)', '', '', '', 'Möchte weitermachen',
        '', '', '', 'Übungen (1..3) Punkte', '', '', '', 'Gesamtpunkte',
        'Gesamtnote']
    columns = len(header_row)
    row_total_points = collections.OrderedDict()
    for ass, v in grading.items():
        row_total_points[ass] = 2 + 2 * len(v.keys())
        for ex, v2 in v.items():
            row_total_points[ass] += len(v2.keys())

    filepath = csvpath.format(group=group, assignment='overview')
    if os.path.exists(filepath):
        if not confirm('File {} already exists. Overwrite it?'.format(filepath), default=False):
            print("Abort.")
            return

    with open(filepath, "w", encoding=csvenc) as fp:
        writer = csv.writer(fp, quoting=csv.QUOTE_ALL)
        writer.writerow(header_row)
        writer.writerow([''] * columns)

        for s_id, student in enumerate(db):
            s_group = student.group
            if group != 0:
                s_group = s_group.difference({0,})
            s_group = ', '.join(map(str, s_group))

            linked_wikiname = '=HYPERLINK("{url}"; "{name}")'.format(**{
                'url': (config.wikiurl + 'Main/' + student.wikiname),
                'name': student.wikiname
            })

            row = [s_group, student.matrnr, student.firstname,
                student.lastname, linked_wikiname] + [''] * 8
            for ass, total in row_total_points.items():
                row.append("='{}'.{}".format(ass, spreadsheet_cell_id(s_id + 2, total)))
            row.append('')
            row.append('=SUM({}:{})'.format(
                spreadsheet_cell_id(13, 2 + s_id),
                spreadsheet_cell_id(15, 2 + s_id),
            ))

            grade = '={}'
            for name, maximum in grades:
                if name != grades[-1][0]:
                    grade = grade.format(grade_recursive)
                    grade = grade.format(spreadsheet_cell_id(17, 2 + s_id),
                        maximum + 1, name)
                else:
                    grade = grade.format('"' + str(name) + '"')
            row.append(grade)
            grade = grade_recursive
            writer.writerow(row)


def create_group_spreadsheets(config, db, grading, group, csvpath, csvenc='utf-8-sig'):
    """Create a spreadsheet for one group.

    :param config:      A Config to read metadata from
    :type config:       Config
    :param db:          StudentDatabase to use
    :type db:           StudentDatabase
    :param grading:     Data specifying grading points
    :type grading:      dict
    :param group:       The group to generate spreadsheet for
    :type group:        int
    :param csvpath:     The filepath to generate file for
    :type csvpath:      str
    :param csvenc:      Encoding of the filepath
    :type csvenc:       str
    """
    db = db.filter(group=group)
    db = db.sorted_by_wikiname()
    max_values_per_sum = 12

    for assdata in config.assignments:
        filepath = csvpath.format(group=group, assignment=assdata['name'])

        if os.path.exists(filepath):
            if not confirm('File {} already exists. Overwrite it?'.format(filepath), default=False):
                print("Abort.")
                return

        with open(filepath, "w", encoding=csvenc) as fp:
            writer = csv.writer(fp, quoting=csv.QUOTE_ALL)
            rowid = 0
            consider = [[]]

            # {title, "", matrnr+}
            title = '{assignment}, Gruppe {group}, {year}'
            row = [title.format(assignment=assdata['name'], group=group,
                year=datetime.datetime.now().strftime('%Y')), '']
            for student in db:
                if 'partnersubmission' in assdata:
                    # TODO: I'd be better to a have a separate %USERSWEB% variable
                    row.append('=HYPERLINK("{url}"; "{matrnr}")'.format(**{
                        'url': (config.wikiurl + 'Main/' + student.wikiname + assdata['partnersubmission']),
                        'matrnr': student.matrnr
                    }))
                else:
                    row.append(student.matrnr)
            rowid += 1
            writer.writerow(row)

            # {"Matrikelnummer", "", wikiname+}
            hyperlink = '=HYPERLINK("{url}"; "{name}")'
            row = ['Matrikelnummer', '']
            for student in db:
                baseurl = config.wikiurl + 'Main/' + student.wikiname + assdata['submission']
                row.append(hyperlink.format(url=baseurl, name=student.wikiname))
            rowid += 1
            writer.writerow(row)

            for exercise, v1 in grading[assdata['name']].items():
                # {exercise name}
                writer.writerow([exercise, ''] + [''] * len(db))
                rowid += 1

                # {criterion, points}
                for criterion, points in v1.items():
                    writer.writerow([criterion, points] + [''] * len(db))
                    consider[0].append(rowid)
                    rowid += 1

                writer.writerow([''] * (len(db) + 2))
                rowid += 1

            assert len(consider[0]) < 120, ("Sorry, I guess this high number "
                "of point lines will cause troubles with certain "
                "spreadsheet software")

            # reorganize consider according to max_values_per_sum
            values = len(consider[0])
            i = 0
            while i < len(consider):
                special = 2 if i == 0 else 0
                if len(consider[i]) + len(consider) - special > max_values_per_sum:
                    value = consider[i].pop()
                    while i + 1 >= len(consider):
                        consider.append([])
                    consider[i + 1].append(value)
                    i = 0
                else:
                    i += 1

            # {"Gesamt", "", "=SUM(...)"+}
            summ = '=SUM({})'
            if_stmt = 'IF({}="x";{};0)'

            row = ['Gesamt', '']
            for s_id in range(len(db)):
                accu = []
                for row_id in consider[0]:
                    accu.append(if_stmt.format(
                        spreadsheet_cell_id(s_id + 2, row_id),
                        spreadsheet_cell_id(1, row_id, fixed=True)
                    ))
                accu.append(spreadsheet_cell_id(s_id + 2, rowid + 1))
                accu.append(spreadsheet_cell_id(s_id + 2, rowid + 2))
                for i in range(len(consider)):
                    accu.append(spreadsheet_cell_id(s_id + 2, rowid + 3 + i))

                row.append(summ.format(','.join(accu)))
            consider = consider[1:]
            rowid += 1
            writer.writerow(row)

            # {"Deadline missed"}
            row = ['Deadline verpasst', ''] + [''] * len(db)
            rowid += 1
            writer.writerow(row)

            # {"Bonuspunkte"}
            row = ["Bonuspunkte", ''] + [''] * len(db)
            rowid += 1
            writer.writerow(row)

            # remaining consider values
            while len(consider) != 0:
                row = ['[ split ]', '']
                for s_id in range(len(db)):
                    accu = []
                    for c in consider[0]:
                        accu.append(if_stmt.format(
                            spreadsheet_cell_id(s_id + 2, c),
                            spreadsheet_cell_id(1, c, fixed=True)
                        ))
                    row.append(summ.format(', '.join(accu)))
                writer.writerow(row)
                rowid += 1
                consider = consider[1:]




def command_init_cli(xmlfile, *, encoding='utf-8'):
    """Initialize application and ask for parameters via CLI.
    Creates a new `metadata.xml`

    :param output_xmlfile:  The target xml filepath to write
    :type output_xmlfile:   str
    :param output_encoding: The desired encoding
    :type output_encoding:  str
    """
    def suffix(n):
        if n % 10 == 1:
            return 'st'
        elif n % 10 == 2:
            return 'nd'
        else:
            return 'th'
    xml = lxml.etree.Element('metadata')

    print(INIT_PRELUDE)
    print()
    print('This is the routine to generate metadata.xml via CLI.')
    print('So I will ask you several questions about the course')
    print('and generate metadata.xml.')
    print()
    ret = confirm('Is it okay that I ask several questions?', default=False)
    if not ret:
        print('Goodbye.')
        return 0

    print('I guess there are students of several courses you want to add.')
    count_courses = request('How many courses are there?', datatype=int)
    course_ids = set()
    for i in range(count_courses):
        print('Let us discuss the {}{} course.'.format(i + 1, suffix(i + 1)))
        course = lxml.etree.Element('course')
        title = request('How is this course called?')
        course.set('title', title)
        lecturer = request('Who is the lecturer of this course?')
        course.set('lecturer', lecturer)
        course_type = request('What kind of course is this (lecture/practicals)?')
        course.set('type', course_type)
        course_id = request('What is the courses ID?')
        course.set('id', course_id)
        if course_id in course_ids:
            raise ValueError("Course ID used twice. That cannot be right.")
        course_ids.add(course_id)
        xml.append(course)

    print()
    print("Let's talk about the tutors.")
    tutors = {}
    count_tutors = request('How many tutors are there?', datatype=int)
    for i in range(1, count_tutors + 1):
        print('Let us discuss tutor #{}.'.format(i + 1))
        tutor = lxml.etree.Element('tutor')
        tutor.set('id', 't' + str(i))
        lastname = request("What is this tutor's last name?")
        lastname_xml = lxml.etree.Element('lastname')
        lastname_xml.text = lastname
        tutor.append(lastname_xml)
        firstname = request("What is this tutor's first name?")
        firstname_xml = lxml.etree.Element('firstname')
        firstname_xml.text = firstname
        tutor.append(firstname_xml)
        email = request("What is this tutor's email address?")
        email_xml = lxml.etree.Element('email')
        email_xml.text = email
        tutor.append(email_xml)
        tutors[i] = firstname + ' ' + lastname
        xml.append(tutor)

    print()
    print('I guess the course is organized in several groups.')
    count_groups = request('How many groups are there?', datatype=int)
    for i in range(count_groups):
        tutor, _name = ask('For group {}, who is its tutor?'.format(i + 1), tutors)
        group = lxml.etree.Element('group')
        group.set('id', str(i))
        group.set('tutor', 't' + str(tutor))
        xml.append(group)

    print()
    print('Thank you so far. Now I will ask about the assignments.')
    count_ass = request('How many assignments are there?', datatype=int)
    for ass in range(1, count_ass + 1):
        assignment = lxml.etree.Element('assignment')
        name = request("How do you call assignment #{}?".format(ass))
        assignment.set('id', name)

        valid = False
        while not valid:
            deadline = request("When is its deadline?")
            try:
                deadline = parse_date(deadline)
                valid = True
            except ValueError:
                print(ERROR_ISO8601)
        dead = lxml.etree.Element('deadline')
        dead.text = deadline.isoformat()
        assignment.append(dead)

        submission_page = request("Where do students submit (eg. SubmissionOne)?")
        sub_xml = lxml.etree.Element('submission')
        sub_xml.text = submission_page
        assignment.append(sub_xml)

        partner = confirm('Is there some partner submission?', default=False)
        if partner:
            partner_sub = request('Where are partner submissions submitted (eg. PartnerTwo)?')
            partner_xml = lxml.etree.Element('partnersubmission')
            partner_xml.text = partner_sub
            assignment.append(partner_xml)

        xml.append(assignment)

    print()
    print('I guess students can achieve 5 grades.')
    gradenames = ['excellent', 'good', 'satisfactory', 'sufficient', 'insufficient']
    grades = lxml.etree.Element('grades')
    valid = False
    while not valid:
        points = []
        elements = []
        for i in range(1, 6):
            name = gradenames[i - 1]
            grade = lxml.etree.Element(name)
            grade.set('repr', str(i))
            text = 'What are {{}} points of grade {}?'.format(name)
            maxi = request(text.format('maximum'), datatype=int)
            grade.set('max', str(maxi))
            mini = request(text.format('minimum'), datatype=int)
            grade.set('min', str(mini))
            elements.append(grade)
            points.append([mini, maxi])

        valid = True

        # monotonically increasing
        inc = lambda x: x[0] < x[1]
        if not all(map(inc, points)):
            print('Not monotonically decreasing!')
            valid = False

        # all points covered
        prev = points[0][1] + 1
        for pts in points:
            if pts[1] != prev - 1:
                print('points(min_current) - 1 == points(max_next)  must hold for all grades')
                valid = False
            prev = pts[0]

        if valid:
            for e in elements:
                grades.append(e)
    xml.append(grades)

    print()
    base_url = request('What is the base URL for the wiki?')
    wikiurl = lxml.etree.Element('wikiurl')
    wikiurl.text = base_url
    xml.append(wikiurl)

    base_path = request('How do you access the wiki on the filesystem?')
    wikipath = lxml.etree.Element('wikipath')
    wikipath.text = base_path
    xml.append(wikipath)
    
    # write xml to file
    write_xml(xml, xmlfile, encoding=encoding)


def command_init_xml(from_xmlfile, to_xmlfile, *, encoding='utf-8'):
    """Initialize application and retrieve data from xml file.

    It might only apply some consistency checks and terminate
    without writing the file
    (can happen only if from_xmlfile == output_xmlfile).

    :param from_xmlfile:    the XML filepath to read from
    :type from_xmlfile:     str
    :param output_xmlfile:  the XML filepath to write to
    :type output_xmlfile:   str
    """
    if not os.path.exists(from_xmlfile):
        raise ValueError("Source file {} does not exist".format(from_xmlfile))

    abs_from = os.path.abspath(from_xmlfile)
    abs_to = os.path.abspath(to_xmlfile)
    if abs_from != abs_to:
        xml = read_xml(abs_from)
        write_xml(xml, abs_to)
        info('Copied file {} to {}'.format(abs_from, abs_to))
    else:
        info('Nothing to do.')


def student_from_cli():
    """Ask CLI user data about a new user.

    :return:        A new Student
    :type return:   Student
    """
    s = Student()
    matrnr = request('Matriculation number:', datatype=int)
    group = request('Group of this student:', datatype=int)
    sec_group = request('Another group of this student? (press enter to skip)',
        datatype=int, nonempty=False)
    lastname = request('Last name:', nonempty=True)
    firstname = request('First name:')
    degree = request('Degree programme:')
    regdate = datetime.datetime.now()
    email = request('Email address:')
    grade = request('Grade:', nonempty=False, datatype=int)

    s.matrnr = matrnr
    s.group = {group,}
    if sec_group != '':
        s.group.add(sec_group)
    s.lastname = lastname
    s.firstname = firstname
    s.degree = degree
    s.regdate = regdate
    s.email = email
    if grade:
        s.grade = grade

    return s


# ------------------- CLI parsing, main and dispatching -------------------

@click.group()
def cli():
    pass

@cli.command()
@click.option('--from-xml', 'src', default=default_metadata_filepath(), help='initialize application from provided metadata.xml')
@click.option('--from-cli', 'src', flag_value='cli', default='cli', help='request parameters via CLI')
@click.option('--to-xml', 'to', default=default_metadata_filepath(), help='filepath where to write metadata.xml to')
@click.option('--to-encoding', 'toenc', default='utf-8', help='desired encoding of metadata.xml')
def init(src, to, toenc):
    """Initialize application. Provide metadata about the course"""
    if src == 'cli' or not src:
        command_init_cli(to, encoding=toenc)
    else:
        command_init_xml(src, to, encoding=toenc)


@cli.group()
def students():
    """Students database management"""
    pass

@students.command()
@click.option('--from-cli', 'clisrc', default=False, flag_value=True, help="create students DB by retrieving data from CLI")
@click.option('--from-csv', 'src', multiple=True, help="create students DB by retrieving data from CSV")
@click.option('--from-encoding', 'srcenc', default='utf-8-sig', help="encoding of CSV files")
@click.option('--to-xml', 'dest', default=default_students_filepath(), help="new students DB filepath")
@click.option('--to-encoding', 'destenc', default='utf-8', help="new students DB encoding")
def create(clisrc, src, srcenc, dest, destenc):
    """Create a new students.xml database"""
    if clisrc:
        students = lxml.etree.Element('students')
        count = request('How many students to you want to add?', datatype=int)
        for s in range(1, count + 1):
            students.append(student_from_cli().to_xml())

        write_xml(students, dest, encoding=destenc)

    else:
        if not src:
            raise ValueError("Specify at least one --from-csv CSV file")
        data = []
        for source in src:
            data.append(parse_student_csv(source))
        database = functools.reduce(lambda a, b: a.union(b), data)
        write_xml(database.to_xml(), dest, encoding=destenc)


@students.command()
@click.option('--students', 'students', default=default_students_filepath(), help="students.xml file to use")
@click.option('--to-To-header', 'to_header', flag_value='to_header', help="Print as SMTP To-Header")
@click.option('--to-unprocessed-registrations', 'to_reg', flag_value=True, help="Print as Foswiki UnprocessedRegistrations article")
@click.option('--to-group-meta-preferences', 'to_meta', flag_value=True, help="Print as %METAPREFERENCES")
@click.option('--group-by-group', 'group', flag_value='group', default=None, help="Group elements by tutorial group")
@click.option('--group-by-regdate', 'group', flag_value='regdate', help="Group elements by registration date")
@click.option('--all-email', 'elements', flag_value='email', help="Print all email addresses")
@click.option('--all-wikiname', 'elements', flag_value='wikiname', help="Print all wikinames")
@click.option('--all-matriculation-number', 'elements', flag_value='matrnr', help="Print all matriculation numbers")
@click.option('--filter', 'filters', multiple=True, help="Apply filter '--filter X=Y' where X is eg. matrnr")
@click.option('--filter-newer-than', 'newer', help="Only print entries newer than the parameter")
@click.option('--filter-older-than', 'older', help="Only print entries older than the parameter")
def read(students, group, elements, to_header, to_reg, to_meta, filters, newer, older):
    db = StudentDatabase()
    xml = read_xml(students)
    db = db.from_xml(xml)

    # apply filter
    for filt in filters:
        if '=' not in filt:
            raise ValueError('--filter must specify key=value pairs')
        key, value = filt.split('=')
        if key == "matrnr" or key == "group":
            value = int(value)
        db = db.filter(**{ key: value })
    if newer:
        db = db.filter(regdate_greater=parse_date(newer))
    if older:
        db = db.filter(regdate_smaller=parse_date(older))

    # To-Header
    if to_header:
        if elements == 'matrnr':
            raise ValueError('To-Header with matriculation number is nonsense')
        db = db.sorted_by_wikiname()
        if group == 'group':
            by_groups = db.group_by_group()
            for grp, students in by_groups.items():
                addrs = []
                for s in students:
                    addrs.append('"{} {}" <{}>'.format(s.firstname, s.lastname, s.email))
                print('Group {}'.format(grp))
                print('  To: ' + ', '.join(addrs))
        elif group == 'regdate':
            by_regdate = db.group_by_regdate()
            for regdate, students in by_regdate.items():
                addrs = []
                for s in students:
                    addrs.append('"{} {}" <{}>'.format(s.firstname, s.lastname, s.email))
                print('Registration date {}'.format(regdate.isoformat()))
                print('  To: ' + ', '.join(addrs))
        else:
            addrs = []
            for s in db:
                addrs.append('"{} {}" <{}>'.format(s.firstname, s.lastname, s.email))
            print('To: ' + ', '.join(addrs))

    # UnprocessedRegistrations
    elif to_reg:
        if group == 'group':
            db = db.sorted_by_group()
        elif group == 'regdate':
            db = db.sorted_by_registration_date()
        else:
            db = db.sorted_by_wikiname()

        data = [['Email', 'WikiName', 'LastName', 'FirstName']]
        for student in db:
            data.append([s.email, s.wikiname, s.lastname, s.firstname])

        print_foswiki_table(data)

    # %METAPREFERENCES%
    elif to_meta:
        meta = '%META:PREFERENCE{{name="GROUP" title="GROUP" type="Set" value="{}"}}%'

        if group == 'group':
            by_groups = db.group_by_group()
            for grp, students in by_groups.items():
                print('Group {}'.format(grp))
                print('  ' + meta.format(', '.format(s.wikiname for s in students)))
        elif group == 'regdate':
            by_regdate = db.group_by_regdate()
            for regdate, students in by_regdate.items():
                print('Registration date {}'.format(regdate.isoformat()))
                print('  ' + meta.format(', '.format(s.wikiname for s in students)))
        else:
            value = ', '.join([s.wikiname for s in db])
            print(meta.format(value))

    else:
        def grouped(attr):
            if group == 'group':
                by_groups = db.group_by_group()
                for grp, students in by_groups.items():
                    print('---++ Group {}'.format(grp))
                    for s in students:
                        print(getattr(s, attr))
                    print()
            elif group == 'regdate':
                by_regdate = db.group_by_regdate()
                for regdate, students in by_regdate.items():
                    print('---++ Registration date {}'.format(regdate.isoformat()))
                    for s in students:
                        print(getattr(s, attr))
                    print()
            else:
                db = db.sorted_by_matriculation_number()
                for s in db:
                    print(getattr(s, attr))


        if elements == 'matrnr':
            grouped('matrnr')
        elif elements == 'email':
            grouped('email')
        elif elements == 'wikiname':
            grouped('wikiname')
        else:
            data = [['Matriculation number', 'Group', 'Wikiname', 'Lastname',
                'Firstname', 'Degree', 'Registration date', 'Email address',
                'Grade']]
            for s in db:
                data.append([s.matrnr, ','.join(map(str, s.group)), s.wikiname,
                    s.lastname, s.firstname, s.degree, s.regdate, s.email,
                    s.grade])

            print_foswiki_table(data)


@students.command()
@click.option('--students', 'students', default=default_students_filepath(), help='a students.xml to work with')
@click.option('--matriculation-number', 'matrnr', help='update one user with given matriculation number on CLI')
@click.option('--from-xml', 'xmlsrc', help='some other students.xml to merge with students.xml')
@click.option('--from-csv', 'csvsrc', help='retrieve students from a TU Graz CSV export')
@click.option('--from-encoding', 'srcenc', default='utf-8-sig', help='Encoding of source text file')
@click.option('--to-xml', 'dest', default=default_students_filepath(), help='some other students.xml to merge with students.xml')
@click.option('--to-encoding', 'destenc', default='utf-8', help='some other students.xml to merge with students.xml')
@click.option('--import-grade', 'gradescsv', help='Import grades from the CSV file')
def update(students, matrnr, xmlsrc, csvsrc, srcenc, dest, destenc, gradescsv):
    xml = read_xml(students)
    db = StudentDatabase()
    db = db.from_xml(xml)

    if matrnr:
        try:
            matrnr = int(matrnr)
        except ValueError:
            raise ValueError('Matriculation number must be integer')
        student = None
        for st in db:
            if st.matrnr == matrnr:
                student = st
        if not student:
            raise ValueError('Student with matrnr {} not found'.format(matrnr))

        print('Press <Enter> to use default value')
        data = {
            'matrnr': ('Matriculation number', int),
            'group': ('Group', int),
            'lastname': ('Last name', str),
            'firstname': ('First name', str),
            'wikiname': ('Foswiki name', str),
            'degree': ('Degree programme', str),
            'regdate': ('Registration date [type now for now]', str),
            'email': ('Email address', str),
            'grade': ('Grade [type 0 for none]', int)
        }

        values = {}
        for attr, desc in data.items():
            if attr == 'regdate':
                default = getattr(student, attr).isoformat()
            else:
                default = getattr(student, attr)
            msg = desc + " (default: {})".format(default)
            values[attr] = request(msg)

        for attr, val in values.items():
            if attr == 'regdate' and val.strip() == 'now':
                student.regdate = datetime.datetime.now()
            elif attr == 'regdate':
                student.regdate = parse_date(student)
            elif val:
                setattr(student, attr, val)

        write_xml(db.to_xml(), dest, descenc)

    elif csvsrc:
        db2 = parse_student_csv(csvsrc, encoding=srcenc)
        write_xml(db.union(db2).to_xml(), dest, encoding=destenc)

    elif xmlsrc:
        xml = read_xml(xmlsrc)
        db2 = StudentDatabase()
        db2 = db2.from_xml(xml)
        db = db.union(db2)
        write_xml(db.to_xml(), dest, encoding=destenc)

@students.command()
@click.option('--students', 'students', default=default_students_filepath(), help='a students.xml to work with')
@click.option('--matriculation-number', 'matrnr', help='matriculation number of the student to delete')
def delete(students, matrnr):
    # TODO: this sucks
    encoding = ''
    with open(students, 'rb') as fp:
        match = re.search('''encoding=(["'])([^"']+)\\1''', fp.read(50).decode('cp1252'))
        assert match, 'Was not able to detect encoding of original file'
        encoding = match.group(2)

    xml = read_xml(students)
    db = StudentDatabase()
    db = db.from_xml(xml)
    print("Database contained {} students.".format(len(db)))
    db = db.filter(not_matrnr=int(matrnr))
    print("Database now contains {} students.".format(len(db)))
    write_xml(db.to_xml(), students, encoding=encoding)

@students.command()
def export():
    pass

@students.command()
def diff():
    pass

@cli.group()
def spreadsheets():
    """Generate spreadsheets for tutors"""
    pass

@spreadsheets.command()
@click.option('--students', 'students', default=default_students_filepath(), help='students.xml to retrieve students data from')
@click.option('--metadata', 'metadata', default=default_metadata_filepath(), help='metadata.xml to retrieve metadata data from')
@click.option('--grading', 'grading', default=default_gradingpoints_filepath(), help='Foswiki article specifying grading points')
@click.option('--grading-encoding', 'genc', default='utf-8-sig', help='grading points file encoding')
@click.option('--group', 'group', help='group to create spreadsheet for')
@click.option('--to-csv', 'csv', default=default_spreadsheet_filepath(), help='spreadsheet to write')
@click.option('--to-encoding', 'csvenc', help='encoding of spreadsheet CSV')
def create(students, metadata, grading, genc, group, csv, csvenc):
    config = Config()
    config.from_xml(read_xml(metadata))
    xml = read_xml(students)
    db = StudentDatabase()
    db = db.from_xml(xml)
    table = parse_grading_points(grading)

    if group is None:
        groups = db.all_groups()
    else:
        groups = {int(g) for g in group.split(',')}

    for grp in groups:
        if "{group}" not in csv:
            raise ValueError("Please provide '{group}' in --to-csv to insert group name to filename")
        if "{assignment}" not in csv:
            raise ValueError("Please provide '{assignment}' in --to-csv to insert assignment name to filename")
        create_group_spreadsheets(config, db, table, grp, csv, csvenc)
        create_title_group_spreadsheet(config, db, table, grp, csv, csvenc)

@spreadsheets.command()
def read():
    pass

@spreadsheets.command()
def update():
    pass

@cli.group()
def foswiki():
    """Maintenance of Foswiki articles"""
    pass

@foswiki.group()
def permissions():
    pass

@foswiki.group()
def users():
    pass


@cli.group()
def stats():
    """Generate statistics about grades"""
    pass

@stats.command()
def create():
    pass


@cli.group()
def recreate():
    """Getting ready for the next semester"""
    pass


if __name__ == '__main__':
    sys.exit(cli(sys.argv[1:]))
