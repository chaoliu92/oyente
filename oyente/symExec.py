import tokenize
import zlib, base64
from tokenize import NUMBER, NAME, NEWLINE
import re
import math
import sys
import pickle
import json
import traceback
import signal
import time
import logging
import six
from collections import namedtuple
from z3 import *

from vargenerator import *
from ethereum_data import *
from basicblock import BasicBlock
from analysis import *
from test_evm.global_test_params import (TIME_OUT, UNKNOWN_INSTRUCTION,
                                         EXCEPTION, PICKLE_PATH)
from vulnerability import CallStack, TimeDependency, MoneyConcurrency, Reentrancy, AssertionFailure, ParityMultisigBug2, \
    IntegerUnderflow, IntegerOverflow
from input_helper import InputHelper
import global_params

log = logging.getLogger(__name__)

UNSIGNED_BOUND_NUMBER = 2 ** 256 - 1
CONSTANT_ONES_159 = BitVecVal((1 << 160) - 1, 256)

Assertion = namedtuple('Assertion', ['pc', 'model'])
Underflow = namedtuple('Underflow', ['pc', 'model'])
Overflow = namedtuple('Overflow', ['pc', 'model'])


class Parameter:
    def __init__(self, **kwargs):
        attr_defaults = {
            "stack": [],
            "calls": [],
            "memory": [],
            "visited": [],
            "overflow_pcs": [],
            "mem": {},
            "analysis": {},
            "sha3_list": {},
            "exp_list": {},
            "balance_list": {},
            "global_state": {},
            "path_conditions_and_vars": {},
            "var_origins": {},  # map "some_var_" (stemming from arbitrary vars) to its concrete or symbolic origin
            # only in text form, not executable code (like Z3 statement)
            "path_condition_origins": []  # record PC and OPCODE when each path condition element is added
        }
        for (attr, default) in six.iteritems(attr_defaults):
            setattr(self, attr, kwargs.get(attr, default))

    def copy(self):
        _kwargs = custom_deepcopy(self.__dict__)
        return Parameter(**_kwargs)


def initGlobalVars():
    global solver
    # Z3 solver

    solver = Solver()

    solver.set("timeout", global_params.TIMEOUT)

    global revertible_overflow_pcs
    revertible_overflow_pcs = set()

    global g_disasm_file
    with open(g_disasm_file, 'r') as f:
        disasm = f.read()

    global g_timeout
    g_timeout = False

    global visited_pcs
    visited_pcs = set()

    results = {
        'evm_code_coverage': '',
        'vulnerabilities': {
            'integer_underflow': [],
            'integer_overflow': [],
            'callstack': False,
            'money_concurrency': False,
            'time_dependency': False,
            'reentrancy': False,
        }
    }

    global calls_affect_state
    calls_affect_state = {}

    # capturing the last statement of each basic block
    global end_ins_dict
    end_ins_dict = {}

    # capturing all the instructions, keys are corresponding addresses
    global instructions
    instructions = {}

    # capturing the "jump type" of each basic block
    global jump_type
    jump_type = {}

    global vertices
    vertices = {}

    global edges
    edges = {}

    global visited_edges
    visited_edges = {}

    global global_problematic_pcs
    global_problematic_pcs = {"money_concurrency_bug": [], "reentrancy_bug": [], "time_dependency_bug": [],
                              "assertion_failure": [], "integer_underflow": [], "integer_overflow": []}

    global total_no_of_paths
    total_no_of_paths = 0

    # to generate names for symbolic variables
    global gen
    gen = Generator()

    global data_source
    if global_params.USE_GLOBAL_BLOCKCHAIN:
        data_source = EthereumData()


def is_testing_evm():
    return global_params.UNIT_TEST != 0


def compare_storage_and_gas_unit_test(global_state, analysis):
    unit_test = pickle.load(open(PICKLE_PATH, 'rb'))
    test_status = unit_test.compare_with_symExec_result(global_state, analysis)
    exit(test_status)


def change_format():
    with open(g_disasm_file) as disasm_file:
        file_contents = disasm_file.readlines()
        i = 0
        firstLine = file_contents[0].strip('\n')
        for line in file_contents:
            line = line.replace('SELFDESTRUCT', 'SUICIDE')
            line = line.replace('Missing opcode 0xfd', 'REVERT')
            line = line.replace('Missing opcode 0xfe', 'ASSERTFAIL')
            line = line.replace('Missing opcode', 'INVALID')
            line = line.replace(':', '')
            lineParts = line.split(' ')
            try:  # removing initial zeroes
                lineParts[0] = str(int(lineParts[0]))

            except:
                lineParts[0] = lineParts[0]
            lineParts[-1] = lineParts[-1].strip('\n')
            try:  # adding arrow if last is a number
                lastInt = lineParts[-1]
                if (int(lastInt, 16) or int(lastInt, 16) == 0) and len(lineParts) > 2:
                    lineParts[-1] = "=>"
                    lineParts.append(lastInt)
            except Exception:
                pass
            file_contents[i] = ' '.join(lineParts)
            i = i + 1
        file_contents[0] = firstLine
        file_contents[-1] += '\n'

    with open(g_disasm_file, 'w') as disasm_file:
        disasm_file.write("\n".join(file_contents))


def build_cfg_and_analyze():
    change_format()
    with open(g_disasm_file, 'r') as disasm_file:
        disasm_file.readline()  # Remove first line
        tokens = tokenize.generate_tokens(disasm_file.readline)
        collect_vertices(tokens)
        construct_bb()
        construct_static_edges()
        full_sym_exec()  # jump targets are constructed on the fly


def print_cfg():
    for block in vertices.values():
        block.display()
    log.debug(str(edges))


def mapping_push_instruction(current_line_content, current_ins_address, idx, positions, length):
    global g_src_map

    while (idx < length):
        if not positions[idx]:
            return idx + 1
        name = positions[idx]['name']
        if name.startswith("tag"):
            idx += 1
        else:
            if name.startswith("PUSH"):
                if name == "PUSH":
                    value = positions[idx]['value']
                    instr_value = current_line_content.split(" ")[1]
                    if int(value, 16) == int(instr_value, 16):
                        g_src_map.instr_positions[current_ins_address] = g_src_map.positions[idx]
                        idx += 1
                        break
                    else:
                        raise Exception("Source map error")
                else:
                    g_src_map.instr_positions[current_ins_address] = g_src_map.positions[idx]
                    idx += 1
                    break
            else:
                raise Exception("Source map error")
    return idx


def mapping_non_push_instruction(current_line_content, current_ins_address, idx, positions, length):
    global g_src_map

    while (idx < length):
        if not positions[idx]:
            return idx + 1
        name = positions[idx]['name']
        if name.startswith("tag"):
            idx += 1
        else:
            instr_name = current_line_content.split(" ")[0]
            if name == instr_name or name == "INVALID" and instr_name == "ASSERTFAIL" or name == "KECCAK256" and instr_name == "SHA3" or name == "SELFDESTRUCT" and instr_name == "SUICIDE":
                g_src_map.instr_positions[current_ins_address] = g_src_map.positions[idx]
                idx += 1
                break
            else:
                raise Exception("Source map error")
    return idx


# 1. Parse the disassembled file
# 2. Then identify each basic block (i.e. one-in, one-out)
# 3. Store them in vertices
def collect_vertices(tokens):
    global g_src_map
    if g_src_map:
        idx = 0
        positions = g_src_map.positions
        length = len(positions)
    global end_ins_dict
    global instructions
    global jump_type

    current_ins_address = 0
    last_ins_address = 0
    is_new_line = True
    current_block = 0
    current_line_content = ""
    wait_for_push = False
    is_new_block = False

    for tok_type, tok_string, (srow, scol), _, line_number in tokens:
        if wait_for_push is True:
            push_val = ""
            for ptok_type, ptok_string, _, _, _ in tokens:
                if ptok_type == NEWLINE:
                    is_new_line = True
                    current_line_content += push_val + ' '
                    instructions[current_ins_address] = current_line_content
                    idx = mapping_push_instruction(current_line_content, current_ins_address, idx, positions,
                                                   length) if g_src_map else None
                    log.debug(current_line_content)
                    current_line_content = ""
                    wait_for_push = False
                    break
                try:
                    int(ptok_string, 16)
                    push_val += ptok_string
                except ValueError:
                    pass

            continue
        elif is_new_line is True and tok_type == NUMBER:  # looking for a line number
            last_ins_address = current_ins_address
            try:
                current_ins_address = int(tok_string)
            except ValueError:
                log.critical("ERROR when parsing row %d col %d", srow, scol)
                quit()
            is_new_line = False
            if is_new_block:
                current_block = current_ins_address
                is_new_block = False
            continue
        elif tok_type == NEWLINE:
            is_new_line = True
            log.debug(current_line_content)
            instructions[current_ins_address] = current_line_content
            idx = mapping_non_push_instruction(current_line_content, current_ins_address, idx, positions,
                                               length) if g_src_map else None
            current_line_content = ""
            continue
        elif tok_type == NAME:
            if tok_string == "JUMPDEST":
                if last_ins_address not in end_ins_dict:
                    end_ins_dict[current_block] = last_ins_address
                current_block = current_ins_address
                is_new_block = False
            elif tok_string == "STOP" or tok_string == "RETURN" or tok_string == "SUICIDE" or tok_string == "REVERT" or tok_string == "ASSERTFAIL":
                jump_type[current_block] = "terminal"
                end_ins_dict[current_block] = current_ins_address
            elif tok_string == "JUMP":
                jump_type[current_block] = "unconditional"
                end_ins_dict[current_block] = current_ins_address
                is_new_block = True
            elif tok_string == "JUMPI":
                jump_type[current_block] = "conditional"
                end_ins_dict[current_block] = current_ins_address
                is_new_block = True
            elif tok_string.startswith('PUSH', 0):
                wait_for_push = True
            is_new_line = False
        if tok_string != "=" and tok_string != ">":
            current_line_content += tok_string + " "

    if current_block not in end_ins_dict:
        log.debug("current block: %d", current_block)
        log.debug("last line: %d", current_ins_address)
        end_ins_dict[current_block] = current_ins_address

    if current_block not in jump_type:
        jump_type[current_block] = "terminal"

    for key in end_ins_dict:
        if key not in jump_type:
            jump_type[key] = "falls_to"


def construct_bb():
    global vertices
    global edges
    sorted_addresses = sorted(instructions.keys())
    size = len(sorted_addresses)
    for key in end_ins_dict:
        end_address = end_ins_dict[key]
        block = BasicBlock(key, end_address)
        if key not in instructions:
            continue
        block.add_instruction(instructions[key])
        i = sorted_addresses.index(key) + 1
        while i < size and sorted_addresses[i] <= end_address:
            block.add_instruction(instructions[sorted_addresses[i]])
            i += 1
        block.set_block_type(jump_type[key])
        vertices[key] = block
        edges[key] = []


def construct_static_edges():
    add_falls_to()  # these edges are static


def add_falls_to():
    global vertices
    global edges
    key_list = sorted(jump_type.keys())
    length = len(key_list)
    for i, key in enumerate(key_list):
        if jump_type[key] != "terminal" and jump_type[key] != "unconditional" and i + 1 < length:
            target = key_list[i + 1]
            edges[key].append(target)
            vertices[key].set_falls_to(target)


def get_init_global_state(path_conditions_and_vars, path_condition_origins):
    global_state = {"balance": {}, "pc": 0, "seq_num": 0}
    init_is = init_ia = deposited_value = sender_address = receiver_address = gas_price = origin = currentCoinbase = currentNumber = currentDifficulty = currentGasLimit = callData = None

    sender_address = BitVec("Is", 256)
    receiver_address = BitVec("Ia", 256)
    deposited_value = BitVec("Iv", 256)
    init_is = BitVec("init_Is", 256)  # init balance of Is
    init_ia = BitVec("init_Ia", 256)  # init balance of Ia

    path_conditions_and_vars["Is"] = sender_address
    path_conditions_and_vars["Ia"] = receiver_address
    path_conditions_and_vars["Iv"] = deposited_value

    constraint = (deposited_value >= BitVecVal(0, 256))
    path_conditions_and_vars["path_condition"].append(constraint)
    path_condition_origins.append(('Initial', ''))  # initial "PC" for this constraint
    constraint = (init_is >= deposited_value)
    path_conditions_and_vars["path_condition"].append(constraint)
    path_condition_origins.append(('Initial', ''))  # initial "PC" for this constraint
    constraint = (init_ia >= BitVecVal(0, 256))
    path_conditions_and_vars["path_condition"].append(constraint)
    path_condition_origins.append(('Initial', ''))  # initial "PC" for this constraint

    # update the balances of the "caller" and "callee"

    global_state["balance"]["Is"] = (init_is - deposited_value)
    global_state["balance"]["Ia"] = (init_ia + deposited_value)

    # gas price
    new_var_name = gen.gen_gas_price_var()
    gas_price = BitVec(new_var_name, 256)
    path_conditions_and_vars[new_var_name] = gas_price

    # origin
    new_var_name = gen.gen_origin_var()
    origin = BitVec(new_var_name, 256)
    path_conditions_and_vars[new_var_name] = origin

    # current block coinbase
    new_var_name = "IH_c"
    currentCoinbase = BitVec(new_var_name, 256)
    path_conditions_and_vars[new_var_name] = currentCoinbase

    # current block number
    new_var_name = "IH_i"
    currentNumber = BitVec(new_var_name, 256)
    path_conditions_and_vars[new_var_name] = currentNumber

    # current block difficulty
    new_var_name = "IH_d"
    currentDifficulty = BitVec(new_var_name, 256)
    path_conditions_and_vars[new_var_name] = currentDifficulty

    # current block gas limit
    new_var_name = "IH_l"
    currentGasLimit = BitVec(new_var_name, 256)
    path_conditions_and_vars[new_var_name] = currentGasLimit

    # current block timestamp
    new_var_name = "IH_s"
    currentTimestamp = BitVec(new_var_name, 256)
    path_conditions_and_vars[new_var_name] = currentTimestamp

    # the state of the current contract
    if "Ia" not in global_state:
        global_state["Ia"] = {}
    global_state["miu_i"] = 0
    global_state["value"] = deposited_value
    global_state["sender_address"] = sender_address
    global_state["receiver_address"] = receiver_address
    global_state["gas_price"] = gas_price
    global_state["origin"] = origin
    global_state["currentCoinbase"] = currentCoinbase
    global_state["currentTimestamp"] = currentTimestamp
    global_state["currentNumber"] = currentNumber
    global_state["currentDifficulty"] = currentDifficulty
    global_state["currentGasLimit"] = currentGasLimit

    return global_state


def get_start_block_to_func_sig():
    state = 0
    func_sig = None
    for pc, instr in six.iteritems(instructions):
        if state == 0 and instr.startswith('PUSH4'):
            state += 1
            func_sig = instr.split(' ')[1][2:]
        elif state == 1 and instr.startswith('EQ'):
            state += 1
        elif state == 2 and instr.startswith('PUSH'):
            state = 0
            pc = instr.split(' ')[1]
            pc = int(pc, 16)
            start_block_to_func_sig[pc] = func_sig
        else:
            state = 0
    return start_block_to_func_sig


def print_path_condition_and_vars(params):
    global g_helper

    path_conditions_and_vars = params.path_conditions_and_vars
    path_condition_origins = params.path_condition_origins
    var_origins = params.var_origins  # map "some_var_" to its concrete or symbolic origin

    print ""
    print "============ Path Conditions and Variables ==========="
    print path_conditions_and_vars

    print ""
    print "============ Path Condition ==========="
    print simplify(And(*[instance for instance in path_conditions_and_vars['path_condition']]))

    print ""
    print "============ Variables ==========="
    for k in path_conditions_and_vars:
        if k not in ["path_condition"]:
            print "{}{}: {}".format(" " * 4, k, path_conditions_and_vars[k])

    print ""
    print "============ Path Condition Origins ==========="
    for item in path_condition_origins:
        print '{}{}\t{}'.format(" " * 4, item[0], item[1])

    print ""
    print "============ Variable Origins ==========="
    for k in var_origins:
        print "{}{}: {}, PC={}".format(" " * 4, k, var_origins[k][0], var_origins[k][1])

    # print mem
    # print memory

    g_helper.rm_tmp_files()
    exit(0)


def read_mem_word(mem, offset):
    """Read 1 word from mem in words address (i.e., multiple of 32 bytes).

    :param mem:
    :param offset:
    :return:
    """
    assert isReal(offset), 'Symbolic mem address, offset = {}'.format(offset)

    offset = to_real(offset)  # convert from BitVecVal() to int() or long()

    if offset % 32 == 0:  # address aligned to words (i.e., multiple of 32 bytes)
        if offset in mem:
            full_word = mem[offset]
        elif long(offset) in mem:
            full_word = mem[long(offset)]
        else:
            full_word = BitVecVal(0, 256)  # defaults to zero
            mem[offset] = full_word
        full_word = to_symbolic(full_word)  # convert to BitVec(256) sort
    else:
        first_word = int(math.floor(float(offset) / 32)) * 32
        second_word = int(math.floor((float(offset) + 32 - 1) / 32)) * 32
        assert first_word + 32 == second_word, 'Error, first_word and second_word are not consecutive words, ' \
                                               'first_word = {}, second_word = {}'.format(first_word, second_word)

        # read first half
        if first_word in mem:
            first_half = mem[first_word]
        elif long(first_word) in mem:
            first_half = mem[long(first_word)]
        else:
            first_half = BitVecVal(0, 256)  # defaults to zero
            mem[first_word] = first_half
        first_half = to_symbolic(first_half)  # convert to BitVec(256) sort
        head_bits = (offset - first_word) * 8
        first_half = Extract(255 - head_bits, 0, first_half)

        # read second half
        if second_word in mem:
            second_half = mem[second_word]
        elif long(second_word) in mem:
            second_half = mem[long(second_word)]
        else:
            second_half = BitVecVal(0, 256)  # defaults to zero
            mem[second_word] = second_half
        second_half = to_symbolic(second_half)  # convert to BitVec(256) sort
        tail_bits = (second_word + 32 - offset - 32) * 8
        second_half = Extract(255, tail_bits, second_half)

        # concatenate to a full word
        full_word = Concat(first_half, second_half)
        assert full_word.sort() == BitVecSort(256)

    return full_word


def get_mem(mem, offset, length=32):
    """Get mem content.

    :param mem:
    :param offset:
    :param length:
    :return:
    """
    assert isAllReal(offset, length), 'Error, offset and length not fully real, offset = {}, length = {}'. \
        format(str(offset), str(length))

    offset, length = all_to_real(offset, length)  # convert from BitVecVal() to int() or long()

    if length == 0:  # return empty if read length is 0 (NOTE: empty is not equal to 0)
        return ''

    first_word = int(math.floor(float(offset) / 32)) * 32
    last_word = int(math.floor((float(offset) + length - 1) / 32)) * 32

    # print 'offset = {}, length = {}, first_word = {}, last_word = {}'.format(offset, length, first_word, last_word)

    assert first_word <= last_word, 'Error, first_word > last_word, first_word = {}, last_word = {}'. \
        format(first_word, last_word)

    if first_word == last_word:  # only at most 1 word to read (may truncate at both ends)
        head_bits = (offset - first_word) * 8
        tail_bits = (last_word + 32 - offset - length) * 8

        full_word = read_mem_word(mem, first_word)
        truncated = Extract(255 - head_bits, tail_bits, full_word)
        return [truncated]
    else:
        values = []

        # process the first word (may truncate at the beginning)
        head_bits = (offset - first_word) * 8

        full_word = read_mem_word(mem, first_word)
        truncated = Extract(255 - head_bits, 0, full_word)
        values.append(truncated)

        # process the middle part (all full words)
        word = first_word + 32
        while word < last_word:
            full_word = read_mem_word(mem, word)
            values.append(full_word)

            word += 32

        # process the last word (may truncate at the end)
        tail_bits = (last_word + 32 - offset - length) * 8

        full_word = read_mem_word(mem, last_word)
        truncated = Extract(255, tail_bits, full_word)
        values.append(truncated)

    return values


def write_mem_byte(mem, offset, value):
    """Write 1 byte (i.e., value) to memory (i.e., mem) in given address (i.e., offset).

    :param mem:
    :param offset:
    :param value:
    :return:
    """
    assert isReal(offset), 'Error, offset must be real number (or BitVecVal), offset = {}'.format(offset)
    assert value.sort() == BitVecSort(256)

    offset = to_real(offset)  # convert from BitVecVal() to int() or long()

    word = int(math.floor(float(offset) / 32)) * 32

    head_bits = (offset - word) * 8
    tail_bits = (word + 32 - offset - 1) * 8

    origin_word = read_mem_word(mem, word)
    mask = mask_vector(head_bits, tail_bits)
    new_word = value << tail_bits

    mem[word] = simplify(origin_word & mask | new_word)


def write_mem_word(mem, offset, value):
    """Write 1 word (i.e., value) to memory (i.e., mem) in given address (i.e., offset).

    :param mem:
    :param offset:
    :param value:
    :return:
    """
    assert isReal(offset), 'Error, offset must be real number (or BitVecVal), offset = {}'.format(offset)

    offset = to_real(offset)  # convert from BitVecVal() to int() or long()
    value = to_symbolic(value)  # convert from BitVecVal() to int() or long()

    if offset % 32 == 0:  # stored_address aligned in words
        mem[offset] = value  # note that the stored_value could be symbolic
    else:  # stored_address not aligned in words (i.e., access starting from the middle of word)
        # update conflict words (i.e., words that my overlap)
        precede_word = int(math.floor(float(offset) / 32))
        succeed_word = int(math.ceil(float(offset) / 32))
        assert precede_word + 1 == succeed_word, 'incorrect word address, {} + 1 != {}'. \
            format(precede_word, succeed_word)

        precede_word = precede_word * 32
        succeed_word = succeed_word * 32
        if precede_word in mem or long(precede_word) in mem:  # update precede word
            offset_bits = (offset - precede_word) * 8
            overlap_bits = (precede_word + 32 - offset) * 8

            origin_value = mem[precede_word] if precede_word in mem else mem[long(precede_word)]
            new_value = (LShR(origin_value, overlap_bits) << overlap_bits) | LShR(value, offset_bits)
            mem[precede_word] = simplify(new_value) if is_expr(new_value) else new_value
        else:
            offset_bits = (offset - precede_word) * 8
            truncated = LShR(value,
                             offset_bits)  # logical shift right, Note: >> is arithmetic shift right (i.e., signed)
            mem[precede_word] = simplify(truncated) if is_expr(truncated) else truncated

        if succeed_word in mem or long(succeed_word) in mem:  # update succeed word
            offset_bits = (offset - precede_word) * 8
            overlap_bits = (precede_word + 32 - offset) * 8

            origin_value = mem[succeed_word] if succeed_word in mem else mem[long(succeed_word)]
            new_value = LShR((origin_value << offset_bits), offset_bits) | (value << overlap_bits)
            mem[succeed_word] = simplify(new_value) if is_expr(new_value) else new_value
        else:
            overlap_bits = (precede_word + 32 - offset) * 8
            truncated = value << overlap_bits
            mem[succeed_word] = simplify(truncated) if is_expr(truncated) else truncated


def mask_vector(head_bits, tail_bits):
    """Return a mask BitVecVal with head and tail all set to 1, the reset set to 0.

    E.g., mask_vector(1, 1) = BitVecVal(1 [0 ... 0] 1, 256), where num of '0' is 256 - 1 - 1 = 254.
    :param head_bits:
    :param tail_bits:
    :return:
    """
    assert head_bits + tail_bits <= 256
    head = simplify(to_symbolic(2 ** head_bits - 1) << (256 - head_bits))
    tail = to_symbolic(2 ** tail_bits - 1)
    return simplify(head | tail)


def set_mem_code(mem, offset, length, code):
    """Set memory, content is assumed to be CODE (in hex) list.

    :param mem:
    :param offset:
    :param length:
    :param code: code in hex, represented as a str, e.g., '289af712'
    :return:
    """
    assert isAllReal(offset, length), 'Error, offset and length not fully real, offset = {}, length = {}'. \
        format(str(offset), str(length))

    offset, length = all_to_real(offset, length)  # convert from BitVecVal() to int() or long()

    assert len(code) % 2 == 0, 'Error, corrupted code, len(code) is not even, code = {}, len(code) = {}'.\
        format(code, len(code))

    if len(code) < length * 2:  # add trailing STOP (i.e., 0x00) instructions to incomplete code
        code += '00' * (length - len(code) / 2)

    code_pattern = re.compile(r'^([0-9a-fA-F]*)$')
    assert code_pattern.match(code), 'Invalid content, content = {}'.format(code)

    code = bytearray.fromhex(code)  # code in bytearray type

    first_word = int(math.floor(float(offset) / 32)) * 32
    last_word = int(math.floor((float(offset) + length - 1) / 32)) * 32
    assert first_word <= last_word, 'Error, first_word > last_word, first_word = {}, last_word = {}'. \
        format(first_word, last_word)

    def code_word_to_int(code):  # convert code in bytearray to corresponding int value
        assert isinstance(code, bytearray) and len(code) <= 64
        i = 0
        for b in code:
            i = i * 256 + b
        return i

    if first_word == last_word:  # only at most 1 word to read (may truncate at both ends)
        head_bits = (offset - first_word) * 8
        tail_bits = (last_word + 32 - offset - length) * 8

        origin_word = read_mem_word(mem, first_word)
        new_word = to_symbolic(code_word_to_int(code)) << tail_bits
        mask = mask_vector(head_bits, tail_bits)

        mem[first_word] = simplify(origin_word & mask | new_word)
    else:
        # process the first word (may truncate at the beginning)
        head_bits = (offset - first_word) * 8
        num_bytes = first_word + 32 - offset

        origin_word = read_mem_word(mem, first_word)
        new_word = to_symbolic(code_word_to_int(code[:num_bytes * 2]))  # the first 'num_bytes' part of code
        mask = mask_vector(head_bits, 0)

        mem[first_word] = simplify(origin_word & mask | new_word)

        # process the middle part (all full words)
        word = first_word + 32
        code_pos = num_bytes * 2  # copy starts at this index for code
        while word < last_word:
            new_word = to_symbolic(code_word_to_int(code[code_pos:code_pos + 64]))
            mem[word] = simplify(new_word)

            word += 32
            code_pos += 64  # code is stored in hex str, so 1 word equals to 64 nibbles

        # process the last word (may truncate at the end)
        tail_bits = (last_word + 32 - offset - length) * 8

        origin_word = read_mem_word(mem, last_word)
        new_word = to_symbolic(code_word_to_int(code[code_pos:])) << tail_bits
        mask = mask_vector(0, tail_bits)

        mem[last_word] = simplify(origin_word & mask | new_word)


def set_mem_data(mem, offset, length, data_offset, path_conditions_and_vars):
    """Set memory, content is assumed to be input DATA.

    :param mem:
    :param offset: memory offset
    :param length: data size
    :param data_offset: calldata offset
    :param path_conditions_and_vars:
    :return:
    """
    assert 'path_condition' in path_conditions_and_vars, \
        'Unsupported path_conditions_and_vars, path_conditions_and_vars = {}'.format(path_conditions_and_vars)

    assert isAllReal(offset, length), \
        'Error, offset, and length are not fully real, offset = {}, length = {}'.format(offset, length)

    if isReal(data_offset):  # offset, length, and data_offset are all real
        offset, length, data_offset = all_to_real(offset, length,
                                                  data_offset)  # convert from BitVecVal() to int() or long()
    else:
        offset, length = all_to_real(offset, length)  # convert from BitVecVal() to int() or long()
        data_offset = simplify(data_offset)

    # first and last word (32 bytes) in memory that is to load (inclusive)
    first_word = int(math.floor(float(offset) / 32))
    last_word = int(math.floor((float(offset) + length - 1) / 32))
    assert first_word <= last_word, 'Error, first_word > last_word, first_word = {}, last_word = {}'. \
        format(first_word, last_word)

    if first_word == last_word:  # only at most 1 word to read (may truncate at both ends)
        head_bits = (offset - first_word) * 8
        tail_bits = (last_word + 32 - offset - length) * 8

        origin_word = read_mem_word(mem, first_word)

        new_word_name = gen.gen_data_var(data_offset, length)
        if new_word_name in path_conditions_and_vars:
            new_word = path_conditions_and_vars[new_word_name]
        else:
            new_word = BitVec(new_word_name, length * 8)  # BitVec size is length * 8
            path_conditions_and_vars[new_word_name] = new_word
        new_word = to_256_bits(new_word)  # extend data BitVec to 256 bits (at head)
        new_word = simplify(new_word << tail_bits)  # NOTE: new_word is of sort BitVec(256)

        mask = mask_vector(head_bits, tail_bits)
        mem[first_word] = simplify(origin_word & mask | new_word)
    else:
        # process the first word (may truncate at the beginning)
        head_bits = (offset - first_word) * 8
        num_bytes = first_word + 32 - offset

        origin_word = read_mem_word(mem, first_word)

        new_word_name = gen.gen_data_var(data_offset, num_bytes)
        if new_word_name in path_conditions_and_vars:
            new_word = path_conditions_and_vars[new_word_name]
        else:
            new_word = BitVec(new_word_name, num_bytes * 8)  # BitVec size is num_bytes * 8
            path_conditions_and_vars[new_word_name] = new_word
        new_word = to_256_bits(new_word)  # extend data BitVec to 256 bits (at head)

        mask = mask_vector(head_bits, 0)
        mem[first_word] = simplify(origin_word & mask | new_word)

        # process the middle part (all full words)
        word = first_word + 32
        data_pos = data_offset + num_bytes  # copy starts at this index for data
        while word < last_word:
            new_word_name = gen.gen_data_var(data_pos, 32)
            if new_word_name in path_conditions_and_vars:
                new_word = path_conditions_and_vars[new_word_name]
            else:
                new_word = BitVec(new_word_name, 256)
                path_conditions_and_vars[new_word_name] = new_word

            mem[word] = new_word

            word += 32
            data_pos += 32

        # process the last word (may truncate at the end)
        tail_bits = (last_word + 32 - offset - length) * 8
        num_bytes = offset + length - last_word

        origin_word = read_mem_word(mem, last_word)

        new_word_name = gen.gen_data_var(data_pos, num_bytes)
        if new_word_name in path_conditions_and_vars:
            new_word = path_conditions_and_vars[new_word_name]
        else:
            new_word = BitVec(new_word_name, num_bytes * 8)  # BitVec size is num_bytes * 8
            path_conditions_and_vars[new_word_name] = new_word
        new_word = to_256_bits(new_word, extend_at_tail=True)  # extend data BitVec to 256 bits (at tail)

        mask = mask_vector(0, tail_bits)
        mem[last_word] = simplify(origin_word & mask | new_word)


def full_sym_exec():
    # executing, starting from beginning
    path_conditions_and_vars = {"path_condition": []}
    path_condition_origins = []
    global_state = get_init_global_state(path_conditions_and_vars, path_condition_origins)
    analysis = init_analysis()
    params = Parameter(path_conditions_and_vars=path_conditions_and_vars, path_condition_origins=path_condition_origins,
                       global_state=global_state, analysis=analysis)
    sym_exec_block(params, 0, 0, 0, -1, 'fallback')


# Symbolically executing a block from the start address
def sym_exec_block(params, block, pre_block, depth, func_call, current_func_name):
    global solver
    global visited_edges
    global money_flow_all_paths
    global path_conditions
    global global_problematic_pcs
    global results
    global g_trace

    visited = params.visited
    stack = params.stack
    mem = params.mem
    memory = params.memory
    global_state = params.global_state
    sha3_list = params.sha3_list
    exp_list = params.exp_list
    balance_list = params.balance_list
    path_conditions_and_vars = params.path_conditions_and_vars
    path_condition_origins = params.path_condition_origins
    var_origins = params.var_origins  # map "some_var_" to its concrete or symbolic origin
    analysis = params.analysis
    calls = params.calls
    overflow_pcs = params.overflow_pcs

    Edge = namedtuple("Edge", ["v1", "v2"])  # Factory Function for tuples is used as dictionary key
    if block < 0:
        raise Exception("UNKNOWN JUMP ADDRESS. TERMINATING THIS PATH")

    if len(g_trace) == 0:  # Reach end of this trace
        print_path_condition_and_vars(params)

    assert block == g_trace[0], "Entering incorrect block: {}, expected: {}".format(block, g_trace[0])

    # current_edge = Edge(pre_block, block)
    # if current_edge in visited_edges:
    #     updated_count_number = visited_edges[current_edge] + 1
    #     visited_edges.update({current_edge: updated_count_number})
    # else:
    #     visited_edges.update({current_edge: 1})

    # Execute every instruction, one at a time
    try:
        block_ins = vertices[block].get_instructions()
    except KeyError:
        raise Exception("This path results in an exception, possibly an invalid jump address")

    for instr in block_ins:
        sym_exec_ins(params, block, instr, func_call, current_func_name)

    # # Mark that this basic block in the visited blocks
    # visited.append(block)

    if len(g_trace) == 0:  # Reach end of this trace
        print_path_condition_and_vars(params)

    # Go to next Basic Block(s)
    if jump_type[block] == "terminal":
        global total_no_of_paths
        global no_of_test_cases

        total_no_of_paths += 1
    elif jump_type[block] == "unconditional":  # executing "JUMP"
        successor = vertices[block].get_jump_target()
        new_params = params.copy()
        new_params.global_state["pc"] = successor
        sym_exec_block(new_params, successor, block, depth, func_call, current_func_name)
    elif jump_type[block] == "falls_to":  # just follow to the next basic block
        successor = vertices[block].get_falls_to()
        new_params = params.copy()
        new_params.global_state["pc"] = successor
        sym_exec_block(new_params, successor, block, depth, func_call, current_func_name)
    elif jump_type[block] == "conditional":  # executing "JUMPI"
        branch_expression = vertices[block].get_branch_expression()

        left_branch = vertices[block].get_jump_target()
        right_branch = vertices[block].get_falls_to()

        assert left_branch != right_branch and g_trace[0] in [left_branch, right_branch], \
            "No branch to go, invalid trace: {} or {}, expected: {}".format(left_branch, right_branch, g_trace[0])

        if g_trace[0] == left_branch:
            left_branch = vertices[block].get_jump_target()
            new_params = params.copy()
            new_params.global_state["pc"] = left_branch
            new_params.path_conditions_and_vars["path_condition"].append(branch_expression)
            new_params.path_condition_origins.append((params.global_state["pc"], 'JUMPI'))
            sym_exec_block(new_params, left_branch, block, depth, func_call, current_func_name)
        elif g_trace[0] == right_branch:
            negated_branch_expression = Not(branch_expression)
            right_branch = vertices[block].get_falls_to()
            new_params = params.copy()
            new_params.global_state["pc"] = right_branch
            new_params.path_conditions_and_vars["path_condition"].append(negated_branch_expression)
            new_params.path_condition_origins.append((params.global_state["pc"], 'JUMPI'))
            sym_exec_block(new_params, right_branch, block, depth, func_call, current_func_name)
        else:
            raise ValueError

        updated_count_number = visited_edges[current_edge] - 1
        visited_edges.update({current_edge: updated_count_number})
    else:
        updated_count_number = visited_edges[current_edge] - 1
        visited_edges.update({current_edge: updated_count_number})
        raise Exception('Unknown Jump-Type')


# Symbolically executing an instruction
def sym_exec_ins(params, block, instr, func_call, current_func_name):
    global visited_pcs
    global solver
    global vertices
    global edges
    global calls_affect_state
    global data_source
    global g_trace
    global g_helper
    global args

    stack = params.stack
    mem = params.mem  # sybolic memory
    memory = params.memory  # concrete memory
    global_state = params.global_state
    sha3_list = params.sha3_list
    exp_list = params.exp_list
    balance_list = params.balance_list
    path_conditions_and_vars = params.path_conditions_and_vars
    path_condition_origins = params.path_condition_origins
    var_origins = params.var_origins  # map "some_var_" to its concrete or symbolic origin
    analysis = params.analysis
    calls = params.calls
    overflow_pcs = params.overflow_pcs

    visited_pcs.add(global_state["pc"])

    instr_parts = str.split(instr, ' ')
    opcode = instr_parts[0]

    if len(g_trace) == 0:  # Reach end of this trace
        print_path_condition_and_vars(params)

    global_state['seq_num'] += 1  # increase instruction sequence number (i.e., number of instructions executed yet)

    # print 'PC = {}, opcode = {}'.format(g_trace[0], opcode)
    # print 'PC = {}, opcode = {}, miu_i = {}'.format(g_trace[0], opcode, global_state['miu_i'])

    assert global_state["pc"] == g_trace[0], "Incorrect PC: {}, expected: {}".format(global_state["pc"], g_trace[0])
    g_trace.popleft()

    if opcode == "INVALID":
        return
    elif opcode == "ASSERTFAIL":
        return

    #
    #  0s: Stop and Arithmetic Operations
    #
    if opcode == "STOP":
        global_state["pc"] = global_state["pc"] + 1
        return
    elif opcode == "ADD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # # Type conversion is needed when they are mismatched
            # if isReal(first) and isSymbolic(second):
            #     first = to_real(first)  # convert from BitVecVal() to int() or long()
            #
            #     first = BitVecVal(first, 256)
            #     computed = first + second
            # elif isSymbolic(first) and isReal(second):
            #     second = to_real(second)  # convert from BitVecVal() to int() or long()
            #
            #     second = BitVecVal(second, 256)
            #     computed = first + second
            # else:
            #     # both are real and we need to manually modulus with 2 ** 256
            #     # if both are symbolic z3 takes care of modulus automatically
            #     computed = (first + second) % (
            #             2 ** 256)  # if is concrete, the result type is long (suffix "L" in str like "32L") instead of int
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(first + second)
            stack.insert(0, computed)

            # print 'PC = {}, ADD, first = {}, second = {}, computed = {}'.format(global_state['pc'] - 1, first, second, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MUL":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isReal(first) and isSymbolic(second):
            #     first = to_real(first)  # convert from BitVecVal() to int() or long()
            #
            #     first = BitVecVal(first, 256)
            # elif isSymbolic(first) and isReal(second):
            #     second = to_real(second)  # convert from BitVecVal() to int() or long()
            #
            #     second = BitVecVal(second, 256)

            # print 'PC={}, first={}, second={}'.format(global_state['pc'] - 1, first, second)

            # computed = first * second & UNSIGNED_BOUND_NUMBER
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(first * second)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SUB":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isReal(first) and isSymbolic(second):
            #     first = to_real(first)  # convert from BitVecVal() to int() or long()
            #
            #     first = BitVecVal(first, 256)
            #     computed = first - second
            # elif isSymbolic(first) and isReal(second):
            #     second = to_real(second)  # convert from BitVecVal() to int() or long()
            #
            #     second = BitVecVal(second, 256)
            #     computed = first - second
            # else:
            #     computed = (first - second) % (2 ** 256)
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(first - second)
            stack.insert(0, computed)

            # print 'SUB, PC = {}, first = {}, second = {}, computed = {}'.format(global_state['pc'] - 1, first, second, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "DIV":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isAllReal(first, second):
            #     first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
            #
            #     if second == 0:
            #         computed = 0
            #     else:
            #         first = to_unsigned(first)
            #         second = to_unsigned(second)
            #         computed = first / second
            # else:
            #     first = to_symbolic(first)
            #     second = to_symbolic(second)
            #     computed = UDiv(first, second)  # remove boundary condition check
            #
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(UDiv(first, second))
            stack.insert(0, computed)

            # print 'DIV, PC = {}, first = {}, second = {}, computed = {}'.format(global_state['pc'] - 1, first, second, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SDIV":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isAllReal(first, second):
            #     first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
            #
            #     first = to_signed(first)
            #     second = to_signed(second)
            #     if second == 0:
            #         computed = 0
            #     elif first == -2 ** 255 and second == -1:
            #         computed = -2 ** 255
            #     else:
            #         sign = -1 if (first / second) < 0 else 1
            #         computed = sign * (abs(first) / abs(second))
            # else:
            #     first = to_symbolic(first)
            #     second = to_symbolic(second)
            #     sign = If(first / second < 0, -1, 1)
            #
            #     z3_abs = lambda x: If(x >= 0, x, -x)
            #     first = z3_abs(first)
            #     second = z3_abs(second)
            #     computed = sign * (first / second)  # remove boundary condition check
            #
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(first / second)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MOD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isAllReal(first, second):
            #     first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
            #
            #     if second == 0:
            #         computed = 0
            #     else:
            #         first = to_unsigned(first)
            #         second = to_unsigned(second)
            #         computed = first % second & UNSIGNED_BOUND_NUMBER
            # else:
            #     first = to_symbolic(first)
            #     second = to_symbolic(second)
            #     computed = URem(first, second)  # remove boundary condition check
            #
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(URem(first, second))
            stack.insert(0, computed)

            # print 'MOD, PC = {}, first = {}, second = {}, computed = {}'.format(global_state['pc'] - 1, first, second, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SMOD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isAllReal(first, second):
            #     first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
            #
            #     if second == 0:
            #         computed = 0
            #     else:
            #         first = to_signed(first)
            #         second = to_signed(second)
            #         sign = -1 if first < 0 else 1
            #         computed = sign * (abs(first) % abs(second))
            # else:
            #     first = to_symbolic(first)
            #     second = to_symbolic(second)
            #     sign = If(first < 0, BitVecVal(-1, 256), BitVecVal(1, 256))
            #
            #     z3_abs = lambda x: If(x >= 0, x, -x)
            #     first = z3_abs(first)
            #     second = z3_abs(second)
            #
            #     computed = sign * (first % second)  # remove boundary condition check
            #
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(SRem(first, second))
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "ADDMOD":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)

            if isAllReal(first, second, third):
                first, second, third = all_to_real(first, second, third)  # convert from BitVecVal() to int() or long()
                if third == 0:
                    computed = 0
                else:
                    computed = (first + second) % third  # intermediate value are not restricted in 256 bits
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)

                first = ZeroExt(256, first)  # concatenate 256 bits of 0 in the left
                second = ZeroExt(256, second)
                third = ZeroExt(256, third)
                computed = (first + second) % third
                computed = Extract(255, 0, computed)  # extract last 256 bits

            computed = simplify(computed) if is_expr(computed) else to_symbolic(computed)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MULMOD":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)

            if isAllReal(first, second, third):
                first, second, third = all_to_real(first, second, third)  # convert from BitVecVal() to int() or long()
                if third == 0:
                    computed = 0
                else:
                    computed = (first * second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)

                first = ZeroExt(256, first)  # concatenate 256 bits of 0 in the left
                second = ZeroExt(256, second)
                third = ZeroExt(256, third)
                computed = URem(first * second, third)
                computed = Extract(255, 0, computed)  # extract last 256 bits

            computed = simplify(computed) if is_expr(computed) else to_symbolic(computed)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EXP":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            base = stack.pop(0)
            exponent = stack.pop(0)
            # Type conversion is needed when they are mismatched
            if isAllReal(base, exponent):
                base, exponent = all_to_real(base, exponent)  # convert from BitVecVal() to int() or long()
                computed = pow(base, exponent, 2 ** 256)
            else:
                # The computed value is unknown, this is because power is
                # not supported in bit-vector theory
                exp_key = "EXP({}, {})".format(str(base), str(exponent))
                if exp_key in exp_list:
                    new_var = exp_list[exp_key]
                else:
                    new_var_name = gen.gen_arbitrary_var()
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var

                    exp_list[exp_key] = new_var
                    var_origins[new_var_name] = (exp_key, global_state["pc"] - 1)  # mark origin
                computed = new_var

            computed = simplify(computed) if is_expr(computed) else to_symbolic(computed)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SIGNEXTEND":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
                if first >= 32 or first < 0:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    if second & (1 << signbit_index_from_right):
                        computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & ((1 << signbit_index_from_right) - 1)
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                signbit_index_from_right = 8 * first + 7

                computed = If(second & (1 << signbit_index_from_right) == 0,
                              second & ((1 << signbit_index_from_right) - 1),
                              second | (2 ** 256 - (1 << signbit_index_from_right)))  # remove boundary condition check

            computed = simplify(computed) if is_expr(computed) else to_symbolic(computed)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SHL":
        raise NotImplementedError('PC = {}, SHL is not supported currently'.format(global_state['pc'] - 1))
    elif opcode == "SHR":
        raise NotImplementedError('PC = {}, SHR is not supported currently'.format(global_state['pc'] - 1))
    elif opcode == "SAR":
        raise NotImplementedError('PC = {}, SAR is not supported currently'.format(global_state['pc'] - 1))
    #
    #  10s: Comparison and Bitwise Logic Operations
    #
    elif opcode == "LT":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isAllReal(first, second):
            #     first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
            #
            #     first = to_unsigned(first)
            #     second = to_unsigned(second)
            #     if first < second:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     computed = If(ULT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
            #
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(If(ULT(first, second), BitVecVal(1, 256), BitVecVal(0, 256)))
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "GT":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isAllReal(first, second):
            #     first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
            #
            #     first = to_unsigned(first)
            #     second = to_unsigned(second)
            #     if first > second:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     computed = If(UGT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(If(UGT(first, second), BitVecVal(1, 256), BitVecVal(0, 256)))
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SLT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isAllReal(first, second):
            #     first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
            #
            #     first = to_signed(first)
            #     second = to_signed(second)
            #     if first < second:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(If(first < second, BitVecVal(1, 256), BitVecVal(0, 256)))
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SGT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isAllReal(first, second):
            #     first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
            #
            #     first = to_signed(first)
            #     second = to_signed(second)
            #     if first > second:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(If(first > second, BitVecVal(1, 256), BitVecVal(0, 256)))
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EQ":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isAllReal(first, second):
            #     first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
            #
            #     if first == second:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     computed = If(first == second, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(If(first == second, BitVecVal(1, 256), BitVecVal(0, 256)))
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "ISZERO":
        # Tricky: this instruction works on both boolean and integer,
        # when we have a symbolic expression, type error might occur
        # Currently handled by try and catch
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            # if isReal(first):
            #     first = to_real(first)  # convert from BitVecVal() to int() or long()
            #
            #     if first == 0:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     computed = If(first == 0, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(If(first == 0, BitVecVal(1, 256), BitVecVal(0, 256)))
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "AND":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            # computed = first & second
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(first & second)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "OR":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)

            # computed = first | second
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(first | second)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "XOR":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)

            # computed = first ^ second
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(first ^ second)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "NOT":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            # computed = (~first) & UNSIGNED_BOUND_NUMBER
            # computed = simplify(computed) if is_expr(computed) else computed

            computed = simplify(~first)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "BYTE":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            byte_index = 32 - first - 1
            second = stack.pop(0)

            if isAllReal(first, second):
                first, second = all_to_real(first, second)  # convert from BitVecVal() to int() or long()
                if first >= 32 or first < 0:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed = computed >> (8 * byte_index)
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)

                computed = second & (255 << (8 * byte_index))
                computed = LShR(computed, (8 * byte_index))  # remove boundary condition check

            computed = simplify(computed) if is_expr(computed) else to_symbolic(computed)
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    # 20s: SHA3
    #
    elif opcode == "SHA3":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            s0 = stack.pop(0)
            s1 = stack.pop(0)

            if isAllReal(s0, s1):
                s0, s1 = all_to_real(s0, s1)  # convert from BitVecVal() to int() or long()

                sha3_input = [str(value) for value in get_mem(mem, s0, s1)]  # get SHA3 input in symbolic form
                sha3_key = "SHA3({})".format(
                    " | ".join(sha3_input))  # unique key for sha3_list, represent as a symbolic expression

                if sha3_key in sha3_list:
                    new_var = sha3_list[sha3_key]
                else:
                    new_var_name = gen.gen_arbitrary_var()  # use a new symbol
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var

                    sha3_list[sha3_key] = new_var
                    var_origins[new_var_name] = (sha3_key, global_state["pc"] - 1)

                max_word = to_symbolic(int(math.ceil(float(s0 + s1) / 32)))
                global_state['miu_i'] = simplify(If(max_word > global_state['miu_i'], max_word, global_state['miu_i']))  # update miu_i

                stack.insert(0, new_var)
            else:
                raise NotImplementedError('PC = {}, SHA3, s0 and s1 are not fully real, s0 = {}, s1 = {}'.
                                          format(global_state['pc'] - 1, s0, s1))
                # # push into the execution a fresh symbolic variable
                # new_var_name = gen.gen_arbitrary_var()  # use an arbitrary variable, lead to lose of information
                # var_origins[new_var_name] = ("SHA3(mem[{}: {}])".format(str(s0), str(s0 + s1)), global_state["pc"] - 1)
                #
                # new_var = BitVec(new_var_name, 256)
                # path_conditions_and_vars[new_var_name] = new_var
                # stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    #
    # 30s: Environment Information
    #
    elif opcode == "ADDRESS":  # get address of currently executing account
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, path_conditions_and_vars["Ia"])
    elif opcode == "BALANCE":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)

            if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
                address = to_real(address)  # convert from BitVecVal() to int() or long()
                new_var = data_source.getBalance(address)
            else:
                balance_key = 'Balance[{}]'.format(hex(to_real(address)) if isReal(address) else address)
                if balance_key in balance_list:
                    new_var = balance_list[balance_key]
                else:
                    new_var_name = gen.gen_arbitrary_var()
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var

                    balance_list[balance_key] = new_var
                    var_origins[new_var_name] = (balance_key, global_state["pc"] - 1)

            if isReal(address):
                address = to_real(address)  # convert from BitVecVal() to int() or long()
                hashed_address = "concrete_address[{}]".format(hex(address))
            else:
                hashed_address = str(address)

            global_state["balance"][hashed_address] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLER":  # get caller address
        # that is directly responsible for this execution
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["sender_address"])
    elif opcode == "ORIGIN":  # get execution origination address
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["origin"])
    elif opcode == "CALLVALUE":  # get value of this transaction
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["value"])
    elif opcode == "CALLDATALOAD":  # from input data from environment
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            position = stack.pop(0)

            new_var_name = gen.gen_data_var(position, 32)  # refer to 1 word of data
            if new_var_name in path_conditions_and_vars:
                new_var = path_conditions_and_vars[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                path_conditions_and_vars[new_var_name] = new_var

            # print 'CALLDATALOAD, PC={}, position={}'.format(global_state['pc'] - 1, position)
            # print new_var_name

            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLDATASIZE":
        global_state["pc"] = global_state["pc"] + 1

        new_var_name = gen.gen_data_size()
        if new_var_name in path_conditions_and_vars:
            new_var = path_conditions_and_vars[new_var_name]
        else:
            new_var = BitVec(new_var_name, 256)
            path_conditions_and_vars[new_var_name] = new_var
        stack.insert(0, new_var)
    elif opcode == "CALLDATACOPY":  # Copy input data to memory
        #  TODO: Don't know how to simulate this yet
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            mem_location = stack.pop(0)
            calldata_from = stack.pop(0)
            no_bytes = stack.pop(0)

            # print 'CALLDATACOPY, PC={}, mem_location = {}, calldata_from = {}, no_bytes = {}'.format(global_state['pc'] - 1, mem_location, calldata_from, no_bytes)

            if isAllReal(mem_location, no_bytes):
                mem_location, no_bytes = all_to_real(mem_location, no_bytes)  # convert from BitVecVal() to int() or long()
                set_mem_data(mem, mem_location, no_bytes, calldata_from,
                             path_conditions_and_vars)  # call a specific function to set memory content

                max_word = to_symbolic(int(math.ceil(float(mem_location + no_bytes) / 32)))
                global_state['miu_i'] = simplify(If(max_word > global_state['miu_i'], max_word, global_state['miu_i']))  # update miu_i

            # elif isReal(mem_location):
            #     mem_location = to_real(mem_location)  # convert from BitVecVal() to int() or long()
            #
            #     assert mem_location % 32 == 0, 'Memory location not aligned: {}, PC={}, CALLDATACOPY'. \
            #         format(mem_location, global_state['pc'] - 1)
            #
            #     new_var_name = gen.gen_data_var(calldata_from, no_bytes)
            #     if new_var_name in path_conditions_and_vars:
            #         new_var = path_conditions_and_vars[new_var_name]
            #     else:
            #         new_var = BitVec(new_var_name, 256)  # modeled as a 256 bits variable, not precise
            #         path_conditions_and_vars[new_var_name] = new_var
            #     mem[mem_location] = new_var
            else:
                raise NotImplementedError(
                    'PC = {}, CALLDATACOPY, mem_location and no_bytes are not fully real, mem_location = {}, '
                    'no_bytes = {}'.format(global_state['pc'] - 1, mem_location, no_bytes))
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CODESIZE":
        global_state["pc"] = global_state["pc"] + 1

        if g_disasm_file.endswith('.disasm'):
            evm_file_name = g_disasm_file[:-7]
        else:
            evm_file_name = g_disasm_file

        with open(evm_file_name, 'r') as evm_file:
            evm = evm_file.read()[:-1]
            code_size = len(evm) / 2
            stack.insert(0, code_size)
    elif opcode == "CODECOPY":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)

            if isAllReal(mem_location, code_from, no_bytes):
                mem_location, code_from, no_bytes = all_to_real(mem_location, code_from, no_bytes)  # convert from BitVecVal() to int() or long()

                if g_disasm_file.endswith('.disasm'):
                    evm_file_name = g_disasm_file[:-7]
                else:
                    evm_file_name = g_disasm_file
                with open(evm_file_name, 'r') as evm_file:
                    evm = evm_file.read()[:-1]
                    start = code_from * 2
                    end = start + no_bytes * 2
                    code = evm[start: end]

                set_mem_code(mem, mem_location, no_bytes, code)  # call a specific function to set memory content

                max_word = to_symbolic(int(math.ceil(float(mem_location + no_bytes) / 32)))
                global_state['miu_i'] = simplify(If(max_word > global_state['miu_i'], max_word, global_state['miu_i']))  # update miu_i
            else:
                raise NotImplementedError(
                    'PC = {}, CODECOPY, mem_location, code_from, and no_bytes are not fully real, mem_location = {}, '
                    'code_from = {}, no_bytes = {}'.format(global_state['pc'] - 1, mem_location, code_from, no_bytes))
                # new_var_name = gen.gen_code_var("Ia", code_from, no_bytes)
                # if new_var_name in path_conditions_and_vars:
                #     new_var = path_conditions_and_vars[new_var_name]
                # else:
                #     new_var = BitVec(new_var_name, 256)  # this may not be 256 bits, too naive
                #     path_conditions_and_vars[new_var_name] = new_var
                #
                # mem.clear()  # very conservative
                # # print '{}: PC={}'.format('CODECOPY', global_state["pc"] - 1)
                # mem[str(mem_location)] = new_var
        else:
            raise ValueError('STACK underflow')
    # elif opcode == "RETURNDATACOPY":
    #     #  TODO: Don't know how to simulate this yet
    #     if len(stack) > 2:
    #         # global_state["pc"] += 1
    #         # stack.pop(0)
    #         # stack.pop(0)
    #         # stack.pop(0)
    #
    #         raise NotImplementedError('PC = {}, RETURNDATACOPY is not supported currently'.
    #                                   format(global_state['pc'] - 1))
    #     else:
    #         raise ValueError('STACK underflow')
    # elif opcode == "RETURNDATASIZE":
    #     global_state["pc"] += 1
    #     new_var_name = gen.gen_arbitrary_var()  # not precise, can change name to return_data
    #     var_origins[new_var_name] = ("RETURNDATASIZE()", global_state["pc"] - 1)  # miss stack depth and call position
    #
    #     new_var = BitVec(new_var_name, 256)
    #     stack.insert(0, new_var)
    elif opcode == "GASPRICE":
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["gas_price"])
    elif opcode == "EXTCODESIZE":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)

            if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
                address = to_real(address)  # convert from BitVecVal() to int() or long()
                code = data_source.getCode(address)
                stack.insert(0, len(code) / 2)
            else:
                # not handled yet
                new_var_name = gen.gen_code_size_var(address)
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var
                stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EXTCODECOPY":
        if len(stack) > 3:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)

            if isAllReal(address, mem_location, code_from, no_bytes) and global_params.USE_GLOBAL_BLOCKCHAIN:
                address, mem_location, code_from, no_bytes = all_to_real(address, mem_location, code_from, no_bytes)  # convert from BitVecVal() to int() or long()

                evm = data_source.getCode(address)
                start = code_from * 2
                end = start + no_bytes * 2
                code = evm[start: end]

                set_mem_code(mem, mem_location, no_bytes, code)  # call a specific function to set memory content

                max_word = to_symbolic(int(math.ceil(float(mem_location + no_bytes) / 32)))
                global_state['miu_i'] = simplify(If(max_word > global_state['miu_i'], max_word, global_state['miu_i']))  # update miu_i
            else:
                raise NotImplementedError(
                    'PC = {}, EXTCODECOPY, address, mem_location, code_from, and no_bytes are not fully real, '
                    'or GLOBAL_BLOCKCHAIN is not used, address = {}, mem_location = {}, code_from = {}, no_bytes = {}, '
                    'USE_GLOBAL_BLOCKCHAIN = {}'.format(
                        global_state['pc'] - 1, address, mem_location, code_from, no_bytes,
                        global_params.USE_GLOBAL_BLOCKCHAIN))
                # new_var_name = gen.gen_code_var(address, code_from, no_bytes)
                # if new_var_name in path_conditions_and_vars:
                #     new_var = path_conditions_and_vars[new_var_name]
                # else:
                #     new_var = BitVec(new_var_name, 256)  # may not be 256 bits, too naive
                #     path_conditions_and_vars[new_var_name] = new_var
                #
                # mem.clear()  # very conservative
                # # print '{}: PC={}'.format('EXTCODECOPY', global_state["pc"] - 1)
                # mem[str(mem_location)] = new_var
        else:
            raise ValueError('STACK underflow')
    elif opcode == "RETURNDATASIZE":
        # global_state["pc"] += 1
        # new_var_name = gen.gen_arbitrary_var()  # not precise, can change name to return_data
        # var_origins[new_var_name] = ("RETURNDATASIZE()", global_state["pc"] - 1)  # miss stack depth and call position
        #
        # new_var = BitVec(new_var_name, 256)
        # stack.insert(0, new_var)

        raise NotImplementedError('PC = {}, RETURNDATASIZE is not supported currently'.format(global_state['pc'] - 1))
    elif opcode == "RETURNDATACOPY":
        #  TODO: Don't know how to simulate this yet
        if len(stack) > 2:
            # global_state["pc"] += 1
            # stack.pop(0)
            # stack.pop(0)
            # stack.pop(0)

            raise NotImplementedError('PC = {}, RETURNDATACOPY is not supported currently'.format(global_state['pc'] - 1))
        else:
            raise ValueError('STACK underflow')
    #
    #  40s: Block Information
    #
    elif opcode == "BLOCKHASH":  # information from block header
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            new_var_name = "IH_blockhash"
            if new_var_name in path_conditions_and_vars:
                new_var = path_conditions_and_vars[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                path_conditions_and_vars[new_var_name] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "COINBASE":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentCoinbase"])
    elif opcode == "TIMESTAMP":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentTimestamp"])
    elif opcode == "NUMBER":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentNumber"])
    elif opcode == "DIFFICULTY":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentDifficulty"])
    elif opcode == "GASLIMIT":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentGasLimit"])
    #
    #  50s: Stack, Memory, Storage, and Flow Information
    #
    elif opcode == "POP":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MLOAD":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)

            if isReal(address):
                address = to_real(address)  # convert from BitVecVal() to int() or long()
                value = read_mem_word(mem, address)

                max_word = to_symbolic(int(math.ceil(float(address + 32) / 32)))
                global_state['miu_i'] = simplify(If(max_word > global_state['miu_i'], max_word, global_state['miu_i']))  # update miu_i

                stack.insert(0, value)
            else:
                raise NotImplementedError('PC = {}, MLOAD, address is not real, address = {}'.
                                          format(global_state['pc'] - 1, address))

            # if isReal(address) and to_real(address) in mem:
            #     address = to_real(address)  # convert from BitVecVal() to int() or long()
            #
            #     # assert address % 32 == 0, 'Memory location not aligned: {}, PC={}, MLOAD'. \
            #     #     format(address, global_state['pc'] - 1)
            #
            #     value = read_mem_word(mem, address)
            #     # value = mem[address]
            #     stack.insert(0, value)
            # else:
            #     # print '{}, PC={}, mem={}'.format('MLOAD', global_state['pc'] - 1, mem)
            #
            #     new_var_name = gen.gen_mem_var(address)
            #     if new_var_name in path_conditions_and_vars:
            #         new_var = path_conditions_and_vars[new_var_name]
            #     else:
            #         new_var = BitVec(new_var_name, 256)
            #         path_conditions_and_vars[new_var_name] = new_var
            #     stack.insert(0, new_var)
            #     if isReal(address):
            #         address = to_real(address)
            #
            #         mem[address] = new_var
            #     else:
            #         mem[str(address)] = new_var
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MSTORE":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)

            # print 'PC = {}, MSTORE, stored_address = {}, stored_value = {}'.\
            #     format(global_state['pc'] - 1, stored_address, stored_value)
            # print 'mem = {}'.format(mem)

            if isReal(stored_address):
                stored_address = to_real(stored_address)  # convert from BitVecVal() to int() or long()
                write_mem_word(mem, stored_address, stored_value)  # call specific function

                max_word = to_symbolic(int(math.ceil(float(stored_address + 32) / 32)))
                global_state['miu_i'] = simplify(If(max_word > global_state['miu_i'], max_word, global_state['miu_i']))  # update miu_i
            else:
                if isZero(stored_value):
                    max_word = simplify(UDiv((stored_address + 32 + 31), 32))  # the same as math.ceil((x + 32) / 32)
                    global_state['miu_i'] = simplify(If(max_word > global_state['miu_i'], max_word, global_state['miu_i']))  # update miu_i
                else:
                    raise NotImplementedError(
                        'PC = {}, MSTORE, stored_address is not real, or stored_value is not 0, stored_address = {}, '
                        'stored_value = {}'.format(global_state['pc'] - 1, stored_address, stored_value))
                # mem.clear()  # very conservative
                # # print '{}: PC={}, stored_address={}'.format('MSTORE', global_state["pc"] - 1, stored_address)
                # mem[str(stored_address)] = stored_value

            # print 'mem after: {}'.format(mem)
            # print ''
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MSTORE8":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            stored_address = stack.pop(0)
            temp_value = stack.pop(0)
            stored_value = temp_value % 256  # get the least byte

            if isReal(stored_address):
                stored_address = to_real(stored_address)  # convert from BitVecVal() to int() or long()
                write_mem_byte(mem, stored_address, stored_value)  # call a specific function to write memory in a word

                max_word = to_symbolic(int(math.ceil(float(stored_address + 1) / 32)))
                global_state['miu_i'] = simplify(If(max_word > global_state['miu_i'], max_word, global_state['miu_i']))  # update miu_i
            else:
                raise NotImplementedError(
                    'PC = {}, MSTORE8, stored_address is not real, stored_address = {}'.
                        format(global_state['pc'] - 1, stored_address))
                # mem.clear()  # very conservative
                # # print '{}: PC={}'.format('MSTORE8', global_state["pc"] - 1)
                # mem[str(stored_address)] = stored_value
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SLOAD":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            position = stack.pop(0)

            if isReal(position) and position in global_state["Ia"]:
                position = to_real(position)  # convert from BitVecVal() to int() or long()
                value = global_state["Ia"][position]
                stack.insert(0, value)
            elif global_params.USE_GLOBAL_STORAGE and isReal(position) and position not in global_state["Ia"]:
                position = to_real(position)  # convert from BitVecVal() to int() or long()
                value = data_source.getStorageAt(position)
                global_state["Ia"][position] = value
                stack.insert(0, value)
            else:
                if str(position) in global_state["Ia"]:
                    value = global_state["Ia"][str(position)]
                    stack.insert(0, value)
                else:
                    if is_expr(position):
                        position = simplify(position)
                    new_var_name = gen.gen_owner_store_var(position)

                    if new_var_name in path_conditions_and_vars:
                        new_var = path_conditions_and_vars[new_var_name]
                    else:
                        new_var = BitVec(new_var_name, 256)
                        path_conditions_and_vars[new_var_name] = new_var
                    stack.insert(0, new_var)
                    if isReal(position):
                        position = to_real(position)  # convert from BitVecVal() to int() or long()

                        global_state["Ia"][position] = new_var
                    else:
                        global_state["Ia"][str(position)] = new_var
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SSTORE":
        if len(stack) > 1:
            for call_pc in calls:
                calls_affect_state[call_pc] = True
            global_state["pc"] = global_state["pc"] + 1
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)

            if isReal(stored_address):
                stored_address = to_real(stored_address)  # convert from BitVecVal() to int() or long()
                # note that the stored_value could be unknown
                global_state["Ia"][stored_address] = stored_value
            else:
                # note that the stored_value could be unknown
                global_state["Ia"][str(stored_address)] = stored_value
        else:
            raise ValueError('STACK underflow')
    elif opcode == "JUMP":
        if len(stack) > 0:
            target_address = stack.pop(0)

            if isSymbolic(target_address):
                try:
                    target_address = int(str(simplify(target_address)))
                except:
                    raise TypeError("Target address must be an integer")
            target_address = to_real(target_address)  # convert from BitVecVal() to int() or long()

            vertices[block].set_jump_target(target_address)
            if target_address not in edges[block]:
                edges[block].append(target_address)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "JUMPI":
        # We need to prepare two branches
        if len(stack) > 1:
            target_address = stack.pop(0)

            if isSymbolic(target_address):
                try:
                    target_address = int(str(simplify(target_address)))
                except:
                    raise TypeError("Target address must be an integer")
            target_address = to_real(target_address)  # convert from BitVecVal() to int() or long()

            vertices[block].set_jump_target(target_address)
            flag = stack.pop(0)
            # branch_expression = (BitVecVal(0, 1) == BitVecVal(1, 1))

            # print 'PC = {}, flag = {}'.format(global_state['pc'] - 1, flag)

            if isReal(flag):
                flag = to_real(flag)  # convert from BitVecVal() to int() or long()

                if flag != 0:
                    branch_expression = True
                else:
                    branch_expression = False
            else:
                branch_expression = (flag != 0)
            vertices[block].set_branch_expression(branch_expression)
            if target_address not in edges[block]:
                edges[block].append(target_address)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "PC":
        stack.insert(0, global_state["pc"])
        global_state["pc"] = global_state["pc"] + 1
    elif opcode == "MSIZE":
        global_state["pc"] = global_state["pc"] + 1

        msize = to_symbolic(32 * global_state["miu_i"])  # modeled as BitVecVal(msize, 256), miu_i may be symbolic expr
        stack.insert(0, msize)
    elif opcode == "GAS":
        # In general, we do not have this precisely. It depends on both
        # the initial gas and the amount has been depleted
        # we need o think about this in the future, in case precise gas
        # can be tracked
        global_state["pc"] = global_state["pc"] + 1

        new_var_name = gen.gen_gas_var(global_state['seq_num'], global_state['pc'] - 1)
        new_var = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = new_var
        stack.insert(0, new_var)
    elif opcode == "JUMPDEST":
        # Literally do nothing
        global_state["pc"] = global_state["pc"] + 1
    #
    #  60s & 70s: Push Operations
    #
    elif opcode.startswith('PUSH', 0):  # this is a push instruction
        position = int(opcode[4:], 10)
        global_state["pc"] = global_state["pc"] + 1 + position

        pushed_value = to_symbolic(int(instr_parts[1], 16))  # store value in symbol (i.e., BitVecVal(256) instance)
        stack.insert(0, pushed_value)
    #
    #  80s: Duplication Operations
    #
    elif opcode.startswith("DUP", 0):
        global_state["pc"] = global_state["pc"] + 1
        position = int(opcode[3:], 10) - 1

        if len(stack) > position:
            duplicate = stack[position]
            stack.insert(0, duplicate)
        else:
            raise ValueError('STACK underflow')
    #
    #  90s: Swap Operations
    #
    elif opcode.startswith("SWAP", 0):
        global_state["pc"] = global_state["pc"] + 1
        position = int(opcode[4:], 10)

        if len(stack) > position:
            temp = stack[position]
            stack[position] = stack[0]
            stack[0] = temp
        else:
            raise ValueError('STACK underflow')
    #
    #  a0s: Logging Operations
    #
    elif opcode in ("LOG0", "LOG1", "LOG2", "LOG3", "LOG4"):
        global_state["pc"] = global_state["pc"] + 1

        # We do not simulate these log operations
        num_of_pops = 2 + int(opcode[3:])
        while num_of_pops > 0:
            stack.pop(0)
            num_of_pops -= 1
    #
    #  f0s: System Operations
    #
    elif opcode == "CREATE":
        if len(stack) > 2:
            raise NotImplementedError('PC = {}, CREATE is not supported currently'.format(global_state['pc'] - 1))
            # global_state["pc"] += 1
            # value = stack.pop(0)
            # offset = stack.pop(0)
            # length = stack.pop(0)
            #
            # new_var_name = gen.gen_arbitrary_var()
            # var_origins[new_var_name] = (
            #     "CREATE({}, mem[{}, {}])".format(str(value), str(offset), str(length)), global_state["pc"] - 1)
            #
            # new_var = BitVec(new_var_name, 256)
            # stack.insert(0, new_var)  # this operation can fail
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALL":
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            raise NotImplementedError('PC = {}, CALL is not supported currently'.format(global_state['pc'] - 1))
            # calls.append(global_state["pc"])
            #
            # global_state["pc"] = global_state["pc"] + 1
            # outgas = stack.pop(0)
            # recipient = stack.pop(0)
            # transfer_amount = stack.pop(0)
            # start_data_input = stack.pop(0)
            # size_data_input = stack.pop(0)
            # start_data_output = stack.pop(0)
            # size_data_ouput = stack.pop(0)
            # # in the paper, it is shaky when the size of data output is
            # # min of stack[6] and the | o |
            #
            # if isReal(transfer_amount):
            #     transfer_amount = to_real(transfer_amount)
            #
            #     if transfer_amount == 0:
            #         stack.insert(0, 1)  # x = 1, assume this call will always succeed without side effects
            #         return
            #
            # # Let us ignore the call depth
            # balance_ia = global_state["balance"]["Ia"]
            # is_enough_fund = (transfer_amount <= balance_ia)
            # solver.push()
            # solver.add(is_enough_fund)
            #
            # if check_sat(solver) == unsat:
            #     # this means not enough fund, thus the execution will result in exception
            #     solver.pop()
            #     stack.insert(0, 0)  # x = 0
            # else:
            #     # the execution is possibly okay
            #     stack.insert(0, 1)  # x = 1, do not consider the specific execution, assume it is correct
            #     solver.pop()
            #     solver.add(is_enough_fund)
            #     path_conditions_and_vars["path_condition"].append(is_enough_fund)
            #     path_condition_origins.append((params.global_state["pc"] - 1, 'CALL'))
            #     new_balance_ia = (balance_ia - transfer_amount)
            #     global_state["balance"]["Ia"] = new_balance_ia
            #     address_is = path_conditions_and_vars["Is"]
            #     address_is = (address_is & CONSTANT_ONES_159)  # 2^160 - 1
            #     boolean_expression = (recipient != address_is)  # if can call back to caller
            #     solver.push()
            #     solver.add(boolean_expression)
            #     if check_sat(solver) == unsat:  # recipient is the same as (current) caller
            #         solver.pop()
            #         new_balance_is = (global_state["balance"]["Is"] + transfer_amount)
            #         global_state["balance"]["Is"] = new_balance_is
            #     else:
            #         solver.pop()
            #         if isReal(recipient):
            #             recipient = to_real(recipient)
            #
            #             new_address_name = "concrete_address_" + str(recipient)
            #         else:
            #             new_address_name = gen.gen_arbitrary_address_var()
            #             var_origins[new_address_name] = ("ADDRESS({})".format(str(recipient)), global_state["pc"] - 1)
            #
            #         old_balance_name = gen.gen_arbitrary_var()
            #         var_origins[old_balance_name] = ("BALANCE({})".format(str(recipient)), global_state["pc"] - 1)
            #
            #         old_balance = BitVec(old_balance_name, 256)  # balance for the callee before this CALL
            #         path_conditions_and_vars[old_balance_name] = old_balance
            #         constraint = (old_balance >= 0)
            #         solver.add(constraint)
            #         path_conditions_and_vars["path_condition"].append(constraint)
            #         path_condition_origins.append((params.global_state["pc"] - 1, 'CALL'))
            #         new_balance = (old_balance + transfer_amount)
            #         global_state["balance"][new_address_name] = new_balance
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLCODE":
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            raise NotImplementedError('PC = {}, CALLCODE is not supported currently'.format(global_state['pc'] - 1))
            # calls.append(global_state["pc"])
            #
            # global_state["pc"] = global_state["pc"] + 1
            # outgas = stack.pop(0)
            # recipient = stack.pop(0)  # this is not used as recipient
            # if global_params.USE_GLOBAL_STORAGE:
            #     if isReal(recipient):
            #         recipient = to_real(recipient)  # convert from BitVecVal() to int() or long()
            #
            #         recipient = hex(recipient)
            #         if recipient[-1] == "L":
            #             recipient = recipient[:-1]
            #         recipients.add(recipient)
            #     else:
            #         recipients.add(None)
            #
            # transfer_amount = stack.pop(0)
            # start_data_input = stack.pop(0)
            # size_data_input = stack.pop(0)
            # start_data_output = stack.pop(0)
            # size_data_ouput = stack.pop(0)
            # # in the paper, it is shaky when the size of data output is
            # # min of stack[6] and the | o |
            #
            # if isReal(transfer_amount):
            #     transfer_amount = to_real(transfer_amount)  # convert from BitVecVal() to int() or long()
            #
            #     if transfer_amount == 0:
            #         stack.insert(0, 1)  # x = 1, assume execution is correct without side effects
            #         return
            #
            # # Let us ignore the call depth
            # balance_ia = global_state["balance"]["Ia"]
            # is_enough_fund = (transfer_amount <= balance_ia)
            # solver.push()
            # solver.add(is_enough_fund)
            #
            # if check_sat(solver) == unsat:
            #     # this means not enough fund, thus the execution will result in exception
            #     solver.pop()
            #     stack.insert(0, 0)  # x = 0
            # else:
            #     # the execution is possibly okay
            #     stack.insert(0, 1)  # x = 1
            #     solver.pop()
            #     solver.add(is_enough_fund)
            #     path_conditions_and_vars["path_condition"].append(is_enough_fund)
            #     path_condition_origins.append((params.global_state["pc"] - 1, 'CALLCODE'))
        else:
            raise ValueError('STACK underflow')
    elif opcode in ("DELEGATECALL", "STATICCALL"):
        if len(stack) > 5:
            raise NotImplementedError('PC = {}, {} is not supported currently'.format(global_state['pc'] - 1, opcode))
            # global_state["pc"] += 1
            # outgas = stack.pop(0)
            # recipient = stack.pop(0)
            #
            # if global_params.USE_GLOBAL_STORAGE:
            #     if isReal(recipient):
            #         recipient = to_real(recipient)  # convert from BitVecVal() to int() or long()
            #
            #         recipient = hex(recipient)
            #         if recipient[-1] == "L":
            #             recipient = recipient[:-1]
            #         recipients.add(recipient)
            #     else:
            #         recipients.add(None)
            #
            # start_data_input = stack.pop(0)
            # size_data_input = stack.pop(0)
            # start_data_output = stack.pop(0)
            # size_data_ouput = stack.pop(0)
            #
            # new_var_name = gen.gen_arbitrary_var()
            # var_origins[new_var_name] = ("{}({}, {}, {}, {}, {}, {})".\
            #     format(opcode, str(outgas), str(recipient), str(start_data_input), str(size_data_input),
            #            str(start_data_output), str(size_data_ouput)), global_state["pc"] - 1)
            #
            # new_var = BitVec(new_var_name, 256)
            # stack.insert(0, new_var)  # so these two operations can fail
        else:
            raise ValueError('STACK underflow')
    elif opcode in ("RETURN", "REVERT"):
        # TODO: Need to handle miu_i
        if len(stack) > 1:
            if opcode == "REVERT":
                global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            stack.pop(0)
            # TODO
            pass
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SUICIDE":
        raise NotImplementedError('PC = {}, SUICIDE is not supported currently'.format(global_state['pc'] - 1))
        # global_state["pc"] = global_state["pc"] + 1
        # recipient = stack.pop(0)
        # transfer_amount = global_state["balance"]["Ia"]
        # global_state["balance"]["Ia"] = 0
        #
        # if isReal(recipient):
        #     recipient = to_real(recipient)  # convert from BitVecVal() to int() or long()
        #
        #     new_address_name = "concrete_address_" + str(recipient)
        # else:
        #     new_address_name = gen.gen_arbitrary_address_var()
        #     var_origins[new_address_name] = ("ADDRESS({})".format(str(recipient)), global_state["pc"] - 1)
        #
        # old_balance_name = gen.gen_arbitrary_var()
        # var_origins[old_balance_name] = ("BALANCE({})".format(str(recipient)), global_state["pc"] - 1)
        #
        # old_balance = BitVec(old_balance_name, 256)  # balance for beneficial address before this SUICIDE
        # path_conditions_and_vars[old_balance_name] = old_balance
        # constraint = (old_balance >= 0)
        # solver.add(constraint)
        # path_conditions_and_vars["path_condition"].append(constraint)
        # path_condition_origins.append((params.global_state["pc"] - 1, 'SUICIDE'))
        # new_balance = (old_balance + transfer_amount)
        # global_state["balance"][new_address_name] = new_balance
        # # TODO
        return

    else:
        log.debug("UNKNOWN INSTRUCTION: " + opcode)
        raise Exception('UNKNOWN INSTRUCTION: ' + opcode)


def closing_message():
    global g_disasm_file
    global results

    log.info("\t====== Analysis Completed ======")


class TimeoutError(Exception):
    pass


class Timeout:
    """Timeout class using ALARM signal."""

    def __init__(self, sec=10, error_message=os.strerror(errno.ETIME)):
        self.sec = sec
        self.error_message = error_message

    def __enter__(self):
        signal.signal(signal.SIGALRM, self._handle_timeout)
        signal.alarm(self.sec)

    def __exit__(self, *args):
        signal.alarm(0)  # disable alarm

    def _handle_timeout(self, signum, frame):
        raise TimeoutError(self.error_message)


def do_nothing():
    pass


def run_build_cfg_and_analyze():
    initGlobalVars()
    global g_timeout

    try:
        with Timeout(sec=global_params.GLOBAL_TIMEOUT):
            build_cfg_and_analyze()
    except TimeoutError:
        g_timeout = True


def get_recipients(disasm_file, contract_address):
    global recipients
    global data_source
    global g_src_map
    global g_disasm_file
    global g_source_file

    g_src_map = None
    g_disasm_file = disasm_file
    g_source_file = None
    data_source = EthereumData(contract_address)
    recipients = set()

    evm_code_coverage = float(len(visited_pcs)) / len(instructions.keys())

    run_build_cfg_and_analyze()

    return {
        'addrs': list(recipients),
        'evm_code_coverage': evm_code_coverage,
        'timeout': g_timeout
    }


def analyze():
    run_build_cfg_and_analyze()


# modify to accept specific guided trace file
def run(disasm_file=None, source_file=None, source_map=None, trace=None, helper=None):
    global g_disasm_file
    global g_source_file
    global g_src_map
    global g_trace
    global g_helper
    global results

    g_disasm_file = disasm_file
    g_source_file = source_file
    g_src_map = source_map
    g_trace = trace
    g_helper = helper

    log.info("\t============ Results ===========")
    analyze()
