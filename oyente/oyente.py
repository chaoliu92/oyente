#!/usr/bin/env python

import os
import re
import six
import json
import symExec
import logging
import requests
import argparse
import subprocess
import global_params
from utils import run_command
from input_helper import InputHelper
from collections import deque


def cmd_exists(cmd):
    return subprocess.call("type " + cmd, shell=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE) == 0


def compare_versions(version1, version2):
    def normalize(v):
        return [int(x) for x in re.sub(r'(\.0+)*$', '', v).split(".")]

    version1 = normalize(version1)
    version2 = normalize(version2)
    if six.PY2:
        return cmp(version1, version2)
    else:
        return (version1 > version2) - (version1 < version2)


def has_dependencies_installed():
    try:
        import z3
        import z3.z3util
        z3_version = z3.get_version_string()
        tested_z3_version = '4.5.1'
        if compare_versions(z3_version, tested_z3_version) > 0:
            logging.warning(
                "You are using an untested version of z3. %s is the officially tested version" % tested_z3_version)
    except:
        logging.critical("Z3 is not available. Please install z3 from https://github.com/Z3Prover/z3.")
        return False

    if not cmd_exists("evm"):
        logging.critical("Please install evm from go-ethereum and make sure it is in the path.")
        return False
    else:
        cmd = "evm --version"
        out = run_command(cmd).strip()
        evm_version = re.findall(r"evm version (\d*.\d*.\d*)", out)[0]
        tested_evm_version = '1.7.3'
        if compare_versions(evm_version, tested_evm_version) > 0:
            logging.warning(
                "You are using evm version %s. The supported version is %s" % (evm_version, tested_evm_version))

    if not cmd_exists("solc"):
        logging.critical("solc is missing. Please install the solidity compiler and make sure solc is in the path.")
        return False
    else:
        cmd = "solc --version"
        out = run_command(cmd).strip()
        solc_version = re.findall(r"Version: (\d*.\d*.\d*)", out)[0]
        tested_solc_version = '0.4.19'
        if compare_versions(solc_version, tested_solc_version) > 0:
            logging.warning("You are using solc version %s, The latest supported version is %s" % (
                solc_version, tested_solc_version))

    return True


# modify to accept guided trace file
def analyze_bytecode(trace_file):
    global args

    helper = InputHelper(InputHelper.BYTECODE, source=args.source, evm=args.evm)
    inp = helper.get_inputs()[0]

    with open(trace_file) as f:
        trace = json.load(f)
    trace = deque([item['PC'] for item in trace])

    symExec.run(disasm_file=inp['disasm_file'], trace=trace, helper=helper)
    helper.rm_tmp_files()


def main():
    # TODO: Implement -o switch.

    global args

    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)

    group.add_argument("-s", "--source", type=str,
                       help="local source file name. Solidity by default. Use -b to process evm instead. Use stdin to read from stdin.")

    parser.add_argument("-t", "--timeout", help="Timeout for Z3 in ms.", action="store", type=int)
    parser.add_argument("-gl", "--gaslimit", help="Limit Gas", action="store", dest="gas_limit", type=int)
    parser.add_argument("-ll", "--looplimit", help="Limit number of loops", action="store", dest="loop_limit", type=int)
    parser.add_argument("-dl", "--depthlimit", help="Limit DFS depth", action="store", dest="depth_limit", type=int)
    parser.add_argument("-glt", "--global-timeout", help="Timeout for symbolic execution", action="store",
                        dest="global_timeout", type=int)
    parser.add_argument("-tf", "--trace-file", help="Specify a real-world trace in file to guide execution",
                        action="store", dest="trace_file", type=str, required=True)

    parser.add_argument("-e", "--evm", help="Do not remove the .evm file.", action="store_true")
    parser.add_argument("-b", "--bytecode", help="read bytecode in source instead of solidity file.",
                        action="store_true", required=True)
    parser.add_argument("-gb", "--globalblockchain", help="Integrate with the global ethereum blockchain",
                        action="store_true")

    args = parser.parse_args()

    args.root_path = ""

    logging.basicConfig(level=logging.INFO)

    global_params.USE_GLOBAL_BLOCKCHAIN = 1 if args.globalblockchain else 0

    if args.timeout:
        global_params.TIMEOUT = args.timeout
    if args.depth_limit:
        global_params.DEPTH_LIMIT = args.depth_limit
    if args.gas_limit:
        global_params.GAS_LIMIT = args.gas_limit
    if args.loop_limit:
        global_params.LOOP_LIMIT = args.loop_limit
    if args.global_timeout:
        global_params.GLOBAL_TIMEOUT = args.global_timeout

    if not has_dependencies_installed():
        return

    analyze_bytecode(args.trace_file)

    exit(0)


if __name__ == '__main__':
    main()
