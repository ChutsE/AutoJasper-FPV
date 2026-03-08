# System Overview

AutoJasper-FPV is designed with flexibility at its core, supporting two distinct execution modes that cater to different workflows and environments. The tool automatically detects which mode to use based on the provided arguments, ensuring a seamless user experience across development and production settings.

---

## Execution Modes

### Dual-Mode Architecture

AutoJasper-FPV intelligently switches between operating modes based on the input parameters:

| Condition | Mode | Use Case |
|-----------|------|----------|
| File or directory **AND** output directory specified | **CLI** | Automation, CI/CD, batch processing |
| No arguments or incomplete arguments | **GUI** | Interactive development, prototyping |

This design eliminates the need to maintain separate tool versions while maximizing usability across different deployment scenarios.

---

## Command-Line Interface (CLI)

The CLI mode is optimized for automation and integration into existing workflows. It provides a non-interactive, scriptable interface suitable for continuous integration pipelines and headless environments.

### Recommended for:
- **Linux servers** and headless systems
- **SSH sessions** and remote execution
- **Continuous Integration (CI)** pipelines
- **Automated formal flows** and batch processing
- **Integration** with makefiles and build systems

### CLI Usage

**Single RTL file:**
```bash
python autojasper_fpv.py -f ./rtl/design.sv -o ./out
```

**Directory with all RTL files:**
```bash
python autojasper_fpv.py -d ./rtl -o ./out
```

**Recursive directory search:**
```bash
python autojasper_fpv.py -d ./rtl -o ./out -r
```

CLI mode activates only when both a file or directory AND an output directory are explicitly specified.

---

## Graphical User Interface (GUI)

The GUI mode provides an intuitive, interactive interface for users who prefer visual feedback and step-by-step workflows. It is particularly useful for rapid prototyping and learning the tool's capabilities.

### Recommended for:
- **Local development** environments on Windows/macOS/Linux
- **Rapid prototyping** and experimentation
- **Interactive use** without memorizing CLI arguments
- **Beginners** exploring AutoJasper-FPV capabilities

### GUI Workflow

1. **Load RTL Files** — Select one or more RTL files or an entire directory
2. **Select Output Directory** — Choose where to generate the formal verification framework
3. **Configure Options** — Set additional parameters (e.g., recursive search)
4. **Generate Framework** — Click to create all verification artifacts

### Activating GUI Mode

Simply run the tool without CLI arguments:
```bash
python autojasper_fpv.py
```

---

## Mode Selection Guide

| Scenario | Recommended Mode | Rationale |
|----------|------------------|-----------|
| Automated nightly formal run on Linux server | CLI | No interactive interface required; integrates easily with cron/scheduler |
| First-time setup of formal project | GUI | Visual feedback helps users understand generated artifacts |
| Integration into CI/CD pipeline | CLI | Enables fully automated, scriptable verification flows |
| Quick local project generation | GUI | Faster than remembering CLI flags; provides immediate visual confirmation |
| Docker container deployment | CLI | Headless execution without display server overhead |

---

## Generated Output

Regardless of execution mode, AutoJasper-FPV generates identical artifacts designed to create a complete, production-ready Cadence JasperGold formal verification environment. These artifacts include:

- **Formal wrapper modules** for block and top-level verification
- **Property macro definitions** for standardized SVA conventions
- **Makefile** with per-module targets
- **TCL script** configured for JasperGold flow
- **Filelist** for analysis and compilation

The generated framework is immediately ready for formal verification runs without additional manual setup.


```
