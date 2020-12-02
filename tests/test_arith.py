import random
import logging
import warnings
import copy

import cocotb

from cocotb.clock import Clock
from cocotb.triggers import Timer, RisingEdge, ReadOnly, FallingEdge
from cocotb.drivers import BusDriver, ValidatedBusDriver
from cocotb.monitors import BusMonitor
from cocotb.regression import TestFactory
from cocotb.scoreboard import Scoreboard
from cocotb.utils import hexdump
from cocotb.binary import BinaryValue, BinaryRepresentation
from cocotb.result import TestError
from cocotb.result import TestFailure, TestSuccess
from cocotb_coverage.coverage import *
from cocotb_coverage.crv import *

CLK_PERIOD_NS = 20

class APBTransaction(Randomized):
    '''
    APB Transaction
    '''

    def __init__(self, DATA_WIDTH = 32, ADDR_SIZE = 32, ADDR_MAX = 4):

        Randomized.__init__(self)

        self.data = None
        self.addr = None
        self.rw = None
        self.slverr = BinaryValue(n_bits=1, value=0, bigEndian=False)

        self.add_rand("addr",list(range(ADDR_MAX*4)))
        self.add_rand("rw"    ,list([0,1]))

    def post_randomize(self):
        self.data = random.randint(0,0xFFFFFFFF)

        self.data = BinaryValue(value=self.data, n_bits=32, bigEndian=False)
        self.addr = BinaryValue(value=self.addr, n_bits=32, bigEndian=False)
        self.rw   = BinaryValue(value=self.rw, n_bits=1, bigEndian=False)

    def print_tr(self):
        print ("Data: ", type(self.data), " Addr: ", type(self.addr), " RW: ", type(self.rw), " SLVERR: ", type(self.slverr))

    def __eq__(self,other):
        if (isinstance(other, APBTransaction)):
            return self.addr == other.addr and self.data  == other.data and self.rw == other.rw and self.slverr == other.slverr
        else:
            return False


class ArithRefmod:
    '''
    DUT Model
    '''

    def __init__ (self):
        self.reg_bank = [None] * 4

        for i in range(4):
            self.reg_bank[i] = BinaryValue(value=0,n_bits=32, bigEndian=False, binaryRepresentation=BinaryRepresentation.TWOS_COMPLEMENT)


    def predict(self, tr_in):
        tr_out = copy.copy(tr_in)

        if(tr_in.rw == 1):
            if(tr_in.addr.integer < 16):
                tr_out.data = self.reg_bank[tr_in.addr.integer // 4]
                tr_out.slverr <= 0
            else:
                tr_out.data <= 0
                tr_out.slverr <= 1
        else:
            if(tr_in.addr.integer < 8):
                self.reg_bank[tr_in.addr.integer // 4] = tr_in.data
                tr_out.slverr <= 0
            elif (8 <= tr_in.addr.integer < 12):
                self.reg_bank[tr_in.addr.integer // 4] = tr_in.data
                tr_out.slverr <= 0

                if (self.reg_bank[2][31]):
                    if (self.reg_bank[2][0]):
                        self.reg_bank[3] <= self.reg_bank[2].integer + self.reg_bank[1].integer
                    else:
                        self.reg_bank[3] <= self.reg_bank[2].integer * self.reg_bank[1].integer
            else:
                tr_out.slverr <= 1
        
        return tr_out

class APBDriver(BusDriver):
    '''
    APB Driver
    '''

    _signals = ["paddr", "pwdata", "psel", "pwrite", "penable", "prdata", "pslverr", "pready"]

    def __init__(self, entity, name, clock, **kwargs):
        BusDriver.__init__(self, entity, name, clock, **kwargs)
        self.bus.paddr.setimmediatevalue(0)
        self.bus.pwdata.setimmediatevalue(0)
        self.bus.psel.setimmediatevalue(0)
        self.bus.pwrite.setimmediatevalue(0)
        self.bus.penable.setimmediatevalue(0)
    
    @cocotb.coroutine
    def send(self, tr):
        
        yield RisingEdge(self.clock)

        if (tr.rw):
            self.bus.paddr <= tr.addr
            self.bus.pwrite <= 0
            self.bus.psel <= 1

            yield RisingEdge(self.clock)

            self.bus.penable <= 1

            while True:
                yield ReadOnly()
                if (self.bus.pready == 1):
                    tr.data = self.bus.prdata
                    tr.slverr = self.bus.pslverr
                    break
            
            yield RisingEdge(self.clock)

            self.bus.psel <= 0
            self.bus.penable <= 0

        else: 
            self.bus.paddr <= tr.addr
            self.bus.pwrite <= 1
            self.bus.psel <= 1
            self.bus.pwdata <= tr.data

            yield RisingEdge(self.clock)

            self.bus.penable <= 1

            while True:
                yield ReadOnly()
                if (self.bus.pready):
                    tr.slverr = self.bus.pslverr
                    break
            
            yield RisingEdge(self.clock)

            self.bus.psel <= 0
            self.bus.penable <= 0

class APBMonitor(BusMonitor):
    '''
    APB Monitor
    '''

    _signals = ["paddr", "pwdata", "psel", "pwrite", "penable", "prdata", "pslverr", "pready"]

    def __init__(self, entity, name, clock, callback=None, reset_n=None):
        BusMonitor.__init__(self, entity, name, clock, callback=callback, event=None, reset_n=None)

    @cocotb.coroutine
    def _monitor_recv(self):
        transCollected = APBTransaction()
        transCollected.randomize()

        while True:
            yield RisingEdge(self.clock)
            
            if (self.bus.psel == 1 and self.bus.penable == 1):
                while True:
                    yield ReadOnly()
                    if (self.bus.pready):
                        transCollected.addr = self.bus.paddr.value
                        transCollected.slverr = self.bus.pslverr.value
                    
                        if (self.bus.pwrite == 1):
                            transCollected.data = self.bus.pwdata.value
                        else:
                            transCollected.data = self.bus.prdata.value

                        transCollected.rw <= 0 if self.bus.pwrite else 1
                        break
            
                self._recv(transCollected)

class ArithTB(object):
    def __init__(self, dut):

        self.missmatch = 0

        self.dut = dut

        self.driver = APBDriver(entity=dut, clock=dut.pclk, name=None)

        self.exp_out = []

        self.rec_out = []

        self.refmod = ArithRefmod()

        self.in_mon = APBMonitor(entity=dut, name=None, clock=dut.pclk, reset_n=dut.presetn, callback=self.rec)

        self.dut_mon = APBMonitor(entity=dut, name=None, clock=dut.pclk, reset_n=dut.presetn, callback=self.model)

    def model(self, transaction):        
        tr_in = copy.copy(transaction)
        # tr_in.print_tr()
        tr_out = self.refmod.predict(tr_in)
        self.exp_out.append(tr_out)
        self.compare()

    def rec(self, transaction):
        self.rec_out.append(transaction)
        self.compare()

    def compare(self):
        if(len(self.exp_out) and len(self.rec_out)):

            if(self.exp_out[-1] == self.rec_out[-1]):
                print("[COMPARATOR MATCH]")
            else:
                print("[COMPARATOR MISSMATCH] Expected: ", self.exp_out[-1].print_tr(), " Received: ", self.rec_out[-1].print_tr())
                self.missmatch += 1

            self.exp_out.pop()
            self.rec_out.pop()
        else:
            pass       

async def reset(dut):
    dut.presetn <= 1
    await Timer(25, units='ns')
    dut.presetn <= 0
    await Timer(200, units='ns')
    dut.presetn <= 1    


def setup_dut(dut):
    clock = Clock(dut.pclk, CLK_PERIOD_NS, units="ns")  # Create a 10us period clock on port clk
    cocotb.fork(clock.start())  # Start the clock

@cocotb.test()
async def simple_test(dut):
    """Simple Test"""

    cycles = 0

    setup_dut(dut)

    await reset(dut)
    tb = ArithTB(dut)
    tr = APBTransaction()

    while (True):

        tr.randomize()
        
        await tb.driver.send(tr)

        cycles += 1
        if (cycles >= 10000):
            break
    
    if (tb.missmatch == 0):
        raise TestSuccess("============= PASS =============")
    else:
        raise TestFailure("============= FAIL =============")