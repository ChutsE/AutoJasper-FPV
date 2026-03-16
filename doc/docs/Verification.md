# Generated Verification Infrastructure

AutoJasper-FPV automatically generates a complete, production-ready formal verification environment for Cadence JasperGold. This section details each artifact created and explains its role within the overall verification framework.

---

## Overview

When processing one or multiple RTL files (`.sv` or `.v`), AutoJasper-FPV creates the following artifacts:

| Artifact | Purpose | Used By |
|----------|---------|---------|
| **Formal Wrapper Modules** | Enable block and top-level verification | JasperGold elaboration |
| **Property Macro Definitions** | Standardized SVA authoring conventions | Property files |
| **Makefile** | Orchestrate verification flows | Build system |
| **File List (analyze.flist)** | Specify files and compilation options | JasperGold analysis |
| **TCL Script (jg_fpv.tcl)** | Configure and execute JasperGold | JasperGold runtime |

All artifacts are generated in a well-organized directory structure, maintaining consistency and enabling scalability across hierarchical verification efforts.

---

## 1. Formal Wrapper Modules

### Purpose

Formal wrapper modules are the foundation of the verification infrastructure. They enable verification at multiple hierarchical levels without modifying the original RTL design.

### Generated File

For each RTL module, AutoJasper-FPV creates:

```
fv_<module_name>.sv
```

### Wrapper Contents

Each formal wrapper includes:

- **Port Mirroring** — All ports from the original module are replicated to ensure complete interface capture
- **Parameter Propagation** — Generic and parameter declarations are preserved, enabling parameterized verification
- **Conditional TOP Define Handling** — Automatic detection of `*_TOP` defines to enable top-level and block-level verification modes
- **Assumption/Assumption Management (ASM) Configuration** — Enables or disables assumptions based on verification context
- **Bind Statement Instantiation** — Allows properties to be bound to the module without RTL modifications

### Verification Reuse

This design pattern enables:

- **Block-level verification** — Verify individual modules in isolation with assumptions on inputs
- **Top-level verification** — Convert assumptions to assertions when verifying the complete system
- **Compositional verification** — Reuse properties across different hierarchical levels

### Example Structure

```systemverilog
module fv_adder (
  input  logic [7:0] a, b,
  input  logic       clk, rst_n,
  output logic [8:0] sum
);

  // Bind properties to parent module
  bind adder adder_properties i_props(.*);

endmodule
```

---

## 2. Property Macro Definitions

### Purpose

Property macros provide standardized conventions for assertion, assumption, and coverage authoring, promoting consistency and maintainability across large property suites.

### Generated File

```
property_defines.svh
```

### Defined Macros

| Macro | Purpose | Example |
|-------|---------|---------|
| **AST** | Assertion property — Always true during verification | `AST(valid_output)` |
| **ASM** | Assumption property — Constrains input space | `ASM(input_valid)` |
| **COV** | Coverage property — Tracks verification progress | `COV(reset_occurred)` |
| **REUSE** | Context-aware property reuse — Switches semantics | `REUSE(constraint, assumption)` |

### The REUSE Macro — Compositional Verification

The REUSE macro is a powerful mechanism for compositional verification. It enables a single property specification to adapt based on verification context:

- **At block level** — Acts as an **assumption**, constraining the input space
- **At top level** — Acts as an **assertion**, verifying the property holds end-to-end

This eliminates property duplication and maintains a single source of truth:

```systemverilog
// Define once, use at multiple levels
`REUSE_PROP(input_valid, assumption)  // Block-level
`REUSE_PROP(input_valid, assertion)   // Top-level
```

### Benefits

- **Reduced redundancy** — Avoid duplicate property specifications
- **Consistency** — Ensures block-level assumptions are verified at the top level
- **Maintainability** — Single definition is easier to update and track
- **Scalability** — Enables hierarchical verification strategies

---

## 3. Makefile

### Purpose

The generated Makefile provides a simple, consistent interface for invoking formal verification runs across all modules.

### Generated File

```
Makefile
```

### Structure

A Makefile target is created for each RTL module in the design:

```makefile
<module_name>_top:
	jg jg_fpv.tcl -allow_unsupported_OS -define <MODULE_NAME>_TOP 1&
```

### Usage

Run formal verification on a specific module:

```bash
make <module_name>_top
```

**Example:**

If your design contains modules `adder`, `multiplier`, and `alu`:

```bash
make adder_top        # Verify adder module
make multiplier_top   # Verify multiplier module
make alu_top          # Verify ALU module
```

### Integration

The Makefile integrates seamlessly with:

- **CI/CD pipelines** — Automated nightly formal runs
- **Development workflows** — Quick module-level verification during design
- **Build systems** — Part of larger design verification schedules

---

## 4. File List (analyze.flist)

### Purpose

The filelist specifies all files, include paths, and macro definitions required by JasperGold for RTL analysis and compilation.

### Generated File

```
analyze.flist
```

### Contents

The generated filelist includes:

| Entry | Purpose |
|-------|---------|
| **Include Directories** | `+incdir+.` — Paths for `include` statements in RTL |
| **Macro Definitions** | Top-level defines for conditional compilation |
| **RTL Design Files** | All `.sv` and `.v` files being analyzed |
| **Generated Formal Wrappers** | `fv_*.sv` files for verification binding |

### Example

```
+incdir+./rtl
+incdir+./inc

// Macro definitions
+define+FORMAL

// RTL files
./rtl/adder.sv
./rtl/multiplier.sv

// Formal wrappers
./formal/fv_adder.sv
./formal/fv_multiplier.sv
```

### JasperGold Integration

JasperGold uses this filelist during the analysis phase:

```bash
jg jg_fpv.tcl -flist analyze.flist
```

---

## 5. TCL Script (jg_fpv.tcl)

### Purpose

The TCL script encapsulates the complete JasperGold formal verification flow, including setup, elaboration, and proof configuration.

### Generated File

```
jg_fpv.tcl
```

### Configuration Elements

The generated TCL script automatically configures:

| Element | Purpose |
|---------|---------|
| **SystemVerilog Analysis** | `-sv12` option for SystemVerilog 2012 support |
| **Dynamic Top Module Selection** | Uses `*_TOP` defines to select verification target |
| **Elaboration Constraints** | Library path and elaboration settings |
| **Clock & Reset Specification** | Automatic clock and reset signal detection |
| **Proof Configuration** | `prove -all` for comprehensive formal verification |
| **Result Output** | Generates proof reports and coverage data |

### Example TCL Flow

```tcl
// Analyze RTL and formal wrappers
analyze -flist analyze.flist

// Elaborate based on TOP define
elaborate -top <module_name> -define <MODULE_NAME>_TOP 1

// Set clock and reset
clock clk
reset ~rst_n

// Prove all properties
prove -all

// Generate reports
report
```

### Verification Flow

The TCL script orchestrates the complete verification pipeline:

1. **Analysis** — Parse RTL and formal wrapper files
2. **Elaboration** — Build design hierarchy with selected top module
3. **Setup** — Configure timing and reset constraints
4. **Proof** — Verify all assertions, assumptions, and coverage
5. **Reporting** — Generate results and coverage metrics

---

## Directory Structure

AutoJasper-FPV organizes generated artifacts as follows:

```
output_directory/
├── fv_adder.sv
├── fv_multiplier.sv
├── analyze.flist
├── jg_fpv.tcl
└── Makefile
```

This flat structure (by default) keeps all verification artifacts together and accessible, making the generated environment easy to navigate and deploy.

---

## Workflow Integration

The generated verification infrastructure integrates seamlessly with existing development workflows:

### Local Development

```bash
# Generate framework
python autojasper_fpv.py -d ./rtl -o ./formal

# Verify specific module
cd formal
make adder_top

# View results
cat prove.out
```

### Automated CI/CD

```bash
# Generate in headless environment
python autojasper_fpv.py -d ./rtl -o ./formal

# Run all formal verifications
cd formal
make -k  # Continue even if one module fails

# Collect and report results
# (integrate with CI/CD dashboard)
```

---

## Summary

The generated verification infrastructure provides a complete, ready-to-use formal verification environment that:

✓ **Eliminates manual setup** — All artifacts are generated automatically  
✓ **Promotes consistency** — Standardized macros and naming conventions  
✓ **Enables reuse** — Properties scale across hierarchical levels  
✓ **Integrates easily** — Works seamlessly with JasperGold and build systems  
✓ **Scales gracefully** — Handles small modules to complex hierarchical designs  

With these artifacts, verification teams can immediately focus on property authoring and coverage analysis rather than infrastructure setup.
