#!/usr/bin/env python3

import sys
import argparse

from call_helper import *


log_parser = argparse.ArgumentParser(
    prog='rnd_log',
    description="Generate logs",
)
sig_parser = log_parser.add_mutually_exclusive_group()
sig_parser.add_argument("-sig", type=str, help="signature file", metavar="<file>")
sig_parser.add_argument("-rnd_sig", nargs=2, type=int, default=[4, 4], help="pred arity", metavar="<int>")

form_parser = log_parser.add_mutually_exclusive_group()
form_parser.add_argument("-form", type=str, help="formula file", metavar="<file>")
form_parser.add_argument("-rnd_form", type=int, default=5, help="size of formula", metavar="<int>")

log_parser.add_argument("-i", type=int, default=10, help="indexrate", metavar="<int>")
log_parser.add_argument("-e", type=int, default=log_parser.get_default(''), help="eventrate", metavar="<int>")
log_parser.add_argument("-r", type=float, default=0.2, help="ratio of new values 0.0-1.0", metavar="<float>")
log_parser.add_argument("-q", type=int, default=10, help="number of queries", metavar="<int>")
log_parser.add_argument("-l", "--len", type=int, default=20, help="length of log", metavar="<int>")
log_parser.add_argument("-log", type=str, default="test.csv", help="output log file", metavar="<int>")
log_parser.add_argument("-logseed", type=int, default=None, help="seed for log generation", metavar="<int>")
log_parser.add_argument("-int_range", nargs=2, type=int, default=None, help="range of integers", metavar="<int> <int>")

log_parser.add_argument("-out", type=str, default="test", help="output log file", metavar="<file>")

extra = log_parser.add_argument_group("Extra options")
extra.add_argument("-seed", type=int, default=None, help="seed for random generation", metavar="<int>")

args = log_parser.parse_args()

if (not args.sig) and args.form:
    print("Error: Signature file is required if formula file is provided. \n -h   Show help message\nExiting...")
    sys.exit(1)

sig, form = main_gen(args.sig, args.rnd_sig[0], args.rnd_sig[1], args.rnd_form, None, None, args.seed, False, args.form)
if not args.sig and not args.form:
    main_file(sig, form, args.out)

if args.sig is None:
    main_print(sig, form)

main_log(sig, args.log, args.i, args.e, args.q, args.r, args.len, args.logseed, args.int_range)
