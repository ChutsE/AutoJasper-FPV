# AutoJasper-FPV Architecture

AutoJasper-FPV is composed of three major components:

1. RTL Parser
2. Framework Generator
3. Verification Infrastructure Builder

---

## Architecture Overview

RTL Files
   │
   ▼
RTL Parser
   │
   ▼
Module Extraction
   │
   ▼
Framework Generator
   │
   ├── Wrapper Generator
   ├── Macro Generator
   ├── Filelist Builder
   ├── TCL Generator
   └── Makefile Generator
   │
   ▼
Formal Verification Environment

---

## Core Modules

| Module | Function |
|------|------|
RTL parser | Extract modules and ports |
Wrapper generator | Create fv modules |
Macro generator | Create property macros |
Filelist generator | Build analyze.flist |
TCL generator | Configure JasperGold |
Makefile generator | Automate runs |

---

## Design Philosophy

### Automation

Minimize manual setup for formal verification environments.

### Reusability

Properties can be reused across block-level and top-level verification.

### Scalability

The framework can scale from small modules to full SoC verification.
