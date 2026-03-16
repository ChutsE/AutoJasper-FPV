
# Quick Start

1. Prepare RTL files

rtl/
 ├── adder.sv
 ├── multiplier.sv

2. Run AutoFV

python autofv.py -d ./rtl -o ./formal

3. Run verification

cd formal
make adder_top
