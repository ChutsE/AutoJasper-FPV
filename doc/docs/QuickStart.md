# Quick Start

This guide demonstrates how to generate a formal verification framework in less than one minute.

---

## Step 1 — Prepare RTL

Example RTL directory:

rtl/
 ├── adder.sv
 ├── multiplier.sv
 └── alu.sv

---

## Step 2 — Run AutoJasper-FPV

```
python autojasper_fpv.py -d ./rtl -o ./formal
```

---

## Step 3 — Generated Files

formal/
 ├── fv_adder.sv
 ├── fv_multiplier.sv
 ├── analyze.flist
 ├── jg_fpv.tcl
 └── Makefile

---

## Step 4 — Run JasperGold

```
cd formal
make adder_top
```

---

## Step 5 — Verify Results

JasperGold will analyze the design and prove the generated properties.
