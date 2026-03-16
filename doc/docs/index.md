# AutoJasper-FPV

## Automated Formal Verification Framework Generator for Cadence JasperGold

AutoJasper-FPV is an automated tool that generates a complete **Formal Property Verification (FPV) framework** from RTL sources written in Verilog or SystemVerilog.

The tool scans RTL files and automatically produces a reusable verification infrastructure compatible with **Cadence JasperGold**, including wrappers, macros, filelists, TCL scripts, and Makefile automation.

AutoJasper-FPV is designed to help **new hardware engineers and researchers quickly adopt formal verification methodologies** without manually building the entire infrastructure.

---

## Key Features

- Automated generation of formal verification environments
- Compatible with **Cadence JasperGold**
- Supports **Verilog and SystemVerilog RTL**
- Property reuse across hierarchical verification levels
- Standardized **SVA macro conventions**
- Dual execution modes:
  - GUI (interactive)
  - CLI (automation / CI)

---

## Motivation

Setting up a formal verification environment typically requires significant manual effort, including:

- writing wrapper modules
- creating filelists
- configuring TCL scripts
- defining verification macros
- building Makefile automation

AutoJasper-FPV eliminates this repetitive setup by generating a ready-to-run FPV framework directly from RTL sources.

---

## Quick Start

Generate a framework:

```
python autojasper_fpv.py -d ./rtl -o ./formal
```

Run JasperGold verification:

```
cd formal
make <module>_top
```

---

## Documentation

- Installation Guide
- System Overview
- Generated Verification Infrastructure
- Property Macros
- Examples

---

## Requirements

- Python ≥ 3.9
- Cadence JasperGold (only required for running verification)
- Tkinter (GUI mode)
