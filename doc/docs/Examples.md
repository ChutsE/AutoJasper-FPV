# Examples

This section demonstrates how AutoJasper-FPV works with real designs.

---

## Example 1 — Adder

RTL:

```
module adder(
 input logic [7:0] a,
 input logic [7:0] b,
 output logic [8:0] sum
);

assign sum = a + b;

endmodule
```

---

## Generated Wrapper

```
fv_adder.sv
```

---

## Run Verification

```
make adder_top
```
