#!/usr/bin/env python3
"""
Spoof rustup.
"""
import argparse
import subprocess

# everything past @rustVersion@ arbitrary
triple = "@rustVersion@-x86_64-unknown-linux-gnu"

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers()
    parser_show = subparsers.add_parser("show")
    parser_show.add_argument("show")
    parser_toolchain = subparsers.add_parser("toolchain")
    parser_toolchain.add_argument("toolchain")
    parser_run = subparsers.add_parser("run")
    parser_run.add_argument("run", nargs="*")
    args = parser.parse_args()

    if "show" in args and args.show == "active-toolchain":
        print(triple)
    elif "toolchain" in args and args.toolchain == "list":
        print(triple)
    elif "run" in args:
        subprocess.run(args.run[1:])
