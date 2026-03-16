# Property Macros

AutoJasper-FPV defines a set of standardized macros for writing SystemVerilog Assertions.

---

## Available Macros

| Macro | Description |
|------|------|
AST | Assertion property |
ASM | Assumption property |
COV | Coverage property |
REUSE | Context-aware property reuse |

---

## AST — Assertion

```
`AST(output_valid)
```

Ensures a property must always hold during verification.

---

## ASM — Assumption

```
`ASM(input_valid)
```

Constrains input behavior.

---

## COV — Coverage

```
`COV(reset_event)
```

Tracks verification coverage.

---

## REUSE — Context-Aware Property

The REUSE macro enables the same property to be used in different verification contexts.
