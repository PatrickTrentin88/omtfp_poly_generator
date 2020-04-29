#!/usr/bin/env python3
#!python

"""
A poly-problem generator for OMT
"""

import argparse
import os
from contextlib import redirect_stdout
from src.polygen import Poly

###
### MAIN
###


def main():
    """The main executable."""
    known_args, other_args = get_cmdline_options()

    formula_generator(known_args, other_args)


###
### COMMAND-LINE PARSING
###


def get_cmdline_options():
    """parses and returns input parameters."""
    parser = argparse.ArgumentParser(description=("A poly-problem generator for OMT."))

    main_group = parser.add_argument_group("Main Options")

    main_group.add_argument("--smt2", metavar="<file>.smt2", type=argparse.FileType('w'),
                            help="Filename for the generated SMT-LIB output",
                            default=None, action=check_file_ext('smt2'))

    main_group.add_argument("--degree", type=check_positive,
                            help="The degree of the polynome",
                            default=3)

    fmt_group = main_group.add_mutually_exclusive_group()

    fmt_group.add_argument("--format", type=check_larger_one, nargs=2,
                           metavar=('ebits', 'sbits'),
                           help="Sets the required Floating-Point format",
                           default=[5, 11])
    fmt_group.add_argument("--float16", action='store_const',
                           dest="format", const=[5, 11],
                           help="Use the Float16 format")
    fmt_group.add_argument("--float32", action='store_const',
                           dest="format", const=[8, 24],
                           help="Use the Float32 format")
    fmt_group.add_argument("--float64", action='store_const',
                           dest="format", const=[11, 53],
                           help="Use the Float64 format")
    fmt_group.add_argument("--float128", action='store_const',
                           dest="format", const=[15, 113],
                           help="Use the Float128 format")

    # parse
    known_args, other_args = parser.parse_known_args()

    return known_args, other_args

def check_positive(value):
    """checks whether the argument is positive"""
    ivalue = int(value)
    if ivalue <= 0:
        raise argparse.ArgumentTypeError("%s is an invalid positive int value" % value)
    return ivalue

def check_larger_one(value):
    """checks whether the argument is larger than one"""
    ivalue = int(value)
    if ivalue <= 1:
        raise argparse.ArgumentTypeError("%s must be larger than one" % value)
    return ivalue

def check_file_ext(extension):
    """checks that the argument extension matches the given extension."""
    class Act(argparse.Action): # pylint: disable=too-few-public-methods
        """Act."""
        def __call__(self, parser, namespace, file, option_string=None):
            """Check that the argument extension matches the given extension"""
            ext = os.path.splitext(file.name)[1][1:]
            if ext != extension:
                option_string = '({})'.format(option_string) if option_string else ''
                parser.error("file doesn't end with `{}' {}".format(extension, option_string))
            else:
                setattr(namespace, self.dest, file.name)
    return Act

###
### FORMULA GENERATOR
###

def formula_generator(known_args, other_args): # pylint: disable=W0613
    """Generates a poly-problem for OMT"""
    poly = Poly(*known_args.format)

    if known_args.smt2:
        with open(known_args.smt2, 'w') as smt2_file:
            with redirect_stdout(smt2_file):
                poly.problem(known_args.degree)
    else:
        poly.problem(known_args.degree)

###
###
###


if __name__ == "__main__":
    main()
