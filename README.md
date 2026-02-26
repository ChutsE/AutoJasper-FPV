📘 AutoJasper-FPV
# AutoJasper-FPV

AutoJasper-FPV is a template-driven generator that creates a standardized, reproducible formal verification environment for Cadence JasperGold directly from an RTL directory.

The framework enforces structured separation between RTL and formal infrastructure, provides macro-based SVA conventions, and enables multi-level property reuse for scalable compositional verification.

---

## 🎯 Motivation

Formal Property Verification (FPV) flows are often rebuilt manually for each RTL block, leading to:

- Inconsistent project structures
- Repeated infrastructure effort
- Poor reproducibility
- Difficulty scaling across integration levels

AutoJasper-FPV addresses this by automatically generating a structured, deterministic verification skeleton that allows engineers to focus on property specification instead of environment setup.

---

## 🏗️ Generated Project Structure

The generator emits a standardized hierarchy:


project/
│
├── Makefile
├── jg_fpv.tcl
├── analyze.flist
│
├── rtl/
│ └── rtl_files.flist
│
├── fv/
│ ├── fv_files.flist
│ ├── property_defines.svh
│ └── skeleton_properties.sv
│
└── README.md


### Execution Flow

1. **Makefile** selects the verification target.
2. **jg_fpv.tcl** configures JasperGold (clock/reset, engines, top module).
3. **analyze.flist** orchestrates compilation.
4. `rtl_files.v` enumerates synthesizable RTL sources.
5. `fv_files.sv` enumerates formal infrastructure.
6. `property_defines.svh` standardizes assert/assume/cover and intent reuse.

---

## 🔬 Key Features

### ✅ Deterministic Infrastructure
Single compilation root (`analyze.flist`) ensures reproducibility.

### ✅ RTL / FV Separation
Formal logic is attached via `bind`, preserving RTL purity.

### ✅ Macro-Based SVA Conventions
Standardized:
- `assert`
- `assume`
- `cover`

### ✅ Multi-Level Property Reuse
The same intent can act as:
- Assertion at block-level
- Assumption at top-level

This enables scalable compositional verification.

---

## 🚀 Quick Start

### 1. Clone the repository

bash
git clone https://github.com/<org>/AutoJasper-FPV.git
cd AutoJasper-FPV
2. Generate a formal environment
./generate_fpv.sh <rtl_directory>

3. Run JasperGold
make <target>
🧪 Example

The repository includes minimal academic RTL examples demonstrating:

Block-level verification

Top-level integration

Property reuse patterns

No proprietary RTL or tool binaries are distributed.

📖 Academic Context

AutoJasper-FPV was developed as part of research on scalable formal verification methodologies and compositional reasoning in industrial FPV flows.

If you use this framework in academic work, please cite:

AutoJasper-FPV: Template-Driven Formal Verification Framework Generator.

(Full citation information available upon publication.)

📜 License

This project is released under the MIT License.

You are free to use, modify, and distribute this software, provided that the original copyright notice is retained.

🤝 Contributing

Contributions are welcome. Please:

Follow the existing directory structure

Preserve separation between RTL and formal infrastructure

Maintain macro-based SVA conventions

⚠️ Disclaimer

AutoJasper-FPV does not include Cadence JasperGold binaries.
Users must provide their own licensed installation.
