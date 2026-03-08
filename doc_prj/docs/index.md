# AutoJasper-FPV

## An Automated Formal Verification Framework Generator for JasperGold

---

## Abstract

AutoJasper-FPV is a lightweight and automated framework generator designed to accelerate the setup of Formal Property Verification (FPV) environments for hardware designs written in Verilog/SystemVerilog. The tool parses RTL source files and automatically produces a reusable verification scaffold compatible with Cadence JasperGold. It supports both graphical (GUI) and command-line (CLI) execution modes, enabling seamless integration in local development environments and remote Linux servers. The framework emphasizes property reuse, modular verification, and standardized macro-based assertion management.

---

## Introduction

Formal verification has become a critical methodology for ensuring correctness in modern digital hardware systems. However, the initial setup of a formal verification environment—especially for modular or hierarchical designs—often requires repetitive boilerplate configuration, including:

- Formal wrapper modules  
- Property macro definitions  
- File lists (flists)  
- TCL scripts for tool configuration  
- Makefile targets for automation  

AutoJasper-FPV addresses this gap by automatically generating a structured FPV environment from RTL inputs, reducing setup time while promoting consistency and reuse.

---

## Contributions

The main contributions of this work are:

- **An automated environment generator for JasperGold** that creates a complete, runnable formal project from an RTL directory, including Makefile orchestration, TCL run script, and analysis/compile filelists.
- **A standardized project structure** for properties and constraints that promotes reproducibility, readability, and scalable growth of the formal testbench across modules and integration levels.
- **Non-intrusive instrumentation support** via SystemVerilog **bind**, enabling verification logic reuse without RTL modifications.
- **Macros SVA conventions** for uniform assertion/assumption/cover authoring and easier maintenance of large property suites.
- **"REUSE" mechanisms** for specification across contexts (e.g., assertion vs. assumption) while keeping a single source without duplicating content.

---

## Requirements

- **Python ≥ 3.9**
- **No third-party dependencies** — relies exclusively on Python Standard Library modules
- **Tkinter** (GUI mode only)


