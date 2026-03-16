
# AutoFV Generator

## Automated Formal Verification Framework Generator

AutoFV Generator is an automated tool that generates a complete **Formal Property Verification (FPV) framework** from RTL sources written in Verilog or SystemVerilog.

The tool analyzes RTL files and automatically produces a reusable verification infrastructure including wrappers, property macros, filelists, TCL scripts, and Makefile automation. The generated framework can be used with industrial formal verification tools such as Cadence JasperGold and similar environments.

AutoFV is designed to help **new hardware engineers and researchers quickly adopt formal verification methodologies** without manually constructing the entire verification infrastructure.

---

## Key Features

- Automated generation of formal verification environments
- Compatible with industrial formal verification tools
- Supports **Verilog and SystemVerilog RTL**
- Property reuse across hierarchical verification levels
- Standardized **SystemVerilog Assertion (SVA) macro conventions**
- Dual execution modes:
  - GUI (interactive)
  - CLI (automation / CI)

---

## Motivation

Setting up a formal verification environment often requires significant manual effort, including:

- writing formal wrapper modules
- creating filelists
- configuring TCL scripts
- defining verification macros
- building Makefile automation

AutoFV Generator eliminates this repetitive setup by automatically generating a ready‑to‑use FPV framework directly from RTL sources.

---

## Quick Start

Generate a framework:

python autofv.py -d ./rtl -o ./formal

Run formal verification:

cd formal
make <module>_top
