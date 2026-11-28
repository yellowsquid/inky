# Artyst

See `program` for some examples.

# Build Instructions

1. Install `idris2` and the two libraries `collie` and `flap`.
2. `idris2 --build`.

# Running

- `artyst format term` is a highly-opinionated, non-customizable code formatter.
- `artyst check term` synthesises a type for a term. It returns a non-zero exit code on failure.
