
# Property Macros

AutoFV defines standardized macros for SystemVerilog Assertions to simplify property authoring.

---

## Available Macros

| Macro | Description |
|------|------|
AST | Assertion property |
ASM | Assumption property |
COV | Coverage property |
ROLE | Context‑dependent property role |

---

## ROLE — Context‑Dependent Property Role

The `ROLE` macro enables **intent‑preserving property reuse across hierarchical verification levels**.

- **Block‑level verification** → property behaves as an **assumption**
- **Top‑level verification** → property becomes an **assertion**

This supports **assume‑guarantee reasoning** and avoids property duplication.
