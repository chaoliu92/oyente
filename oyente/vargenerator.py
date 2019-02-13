from utils import isReal, to_real
from z3 import *


class Generator:
    def __init__(self):
        self.countstack = 0
        self.count = 0

    def gen_stack_var(self):
        self.countstack += 1
        return "s[{}]".format(str(self.countstack))

    def gen_data_var(self, offset, length):
        return "Id[{}; {}]".format(str(to_real(offset)) if isReal(offset) else '({})'.format(simplify(offset)),
                                  str(to_real(length)) if isReal(length) else '({})'.format(simplify(length)))

    def gen_data_size(self):
        return "Id_size"

    def gen_mem_var(self, address):
        return "mem[{}]".format(str(address))

    def gen_arbitrary_var(self):
        self.count += 1
        return "var[{}]".format(str(self.count))

    def gen_arbitrary_address_var(self):
        self.count += 1
        return "address[{}]".format(str(self.count))

    def gen_owner_store_var(self, position):
        return "Ia_store[{}]".format(str(position))

    def gen_gas_var(self):
        self.count += 1
        return "gas[{}]".format(str(self.count))

    def gen_gas_price_var(self):
        return "Ip"

    def gen_address_var(self):
        return "Ia"

    def gen_caller_var(self):
        return "Is"

    def gen_origin_var(self):
        return "Io"

    def gen_balance_var(self):
        self.count += 1
        return "balance[{}]".format(str(self.count))

    def gen_code_var(self, address, offset, length):
        return "code[{}][{}; {}]".format(str(to_real(address)) if isReal(address) else '({})'.format(simplify(address)),
                                        str(to_real(offset)) if isReal(offset) else '({})'.format(simplify(offset)),
                                        str(to_real(length)) if isReal(length) else '({})'.format(simplify(length)))

    def gen_code_size_var(self, address):
        return "code_size[{}]".format(str(address))
