# Inky

See `program` for some examples.

# Build Instructions

1. Install `idris2` and the two libraries `collie` and `flap`.
2. `idris2 --build`.

# Running

- `inky format term` is a highly-opinionated, non-customizable code formatter.
- `inky check term` type checks an expression, assuming its type is synthesizable.
- `inky compile term` compiles a term to Guile Scheme.
