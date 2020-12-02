TOPLEVEL := arith
TOPLEVEL_LANG := verilog

PWD=$(shell pwd)
DUT = $(PWD)/../hdl

SIM ?= xcelium

VERILOG_SOURCES  = $(DUT)/arith.sv

MODULE := test_arith

include $(shell cocotb-config --makefiles)/Makefile.sim