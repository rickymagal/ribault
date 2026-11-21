# Ribault - Haskell TALM Compiler

Repository for the final undergraduate project presented at the Department of Computing, **UFES**.
**Author**: Ricardo Magalhaes Santos Filho
**Advisor**: Prof. Dr. Alberto Ferreira de Souza
**Co-advisor**: Prof. Dr. Tiago Assumpcao de Oliveira Alves

Code documents: https://rickymagal.github.io/Ribault

## Introduction

This work proposes the translation of programs written in a Haskell subset into Dataflow executable code, bridging the functional paradigm—based on pure expressions—with a data-driven parallel execution model. The compiler automatically generates graphs compatible with distributed execution environments, with additional support for generating TALM assembly code.

## Repository Structure

| Directory | Content |
|---|---|
| `src/Analysis` | Parsing + analysis stages (Lexer/Parser/AST). |
| `src/Synthesis` | Dataflow + TALM code generation. |
| `test/` | Unit test programs (`*.hss`); `make` renders AST/DF artifacts here (git-ignored). |
| `tools/` | Supers build helpers + Haddock API docs builder (`build_module_docs.sh`). |
| `TALM/` | Trebuchet interpreter + assembler (git submodule → [tiagoaoa/TALM](https://github.com/tiagoaoa/TALM), pinned). |

## Build / Targets

Prerequisites: `ghc`, `alex`, `happy`, `dot` (Graphviz), `python3`, `gcc`.
The TALM interpreter/assembler is the `TALM` git submodule
([tiagoaoa/TALM](https://github.com/tiagoaoa/TALM), pinned by SHA). Initialize it
before building:

```bash
git submodule update --init TALM
```

`TALM_DIR` overrides the path (default: `TALM`), e.g. `make TALM_DIR=/path/to/TALM`.

```bash
# Build everything for test programs
make

# Generate specific artifacts for tests
make ast      # AST .dot + .png
make df       # Dataflow .dot + .png
make code     # TALM .fl
make supers   # Supers.hs + libsupers.so
```

Executables produced:
- `analysis`  -> AST `.dot`
- `synthesis` -> Dataflow `.dot`
- `codegen`   -> TALM `.fl`
- `supersgen` -> Supers Haskell for super-instructions

## Generating Artifacts for a New Program (outside `test/`)

Assuming a new file `myprog.hsk`:

```bash
./analysis  /path/to/myprog.hsk > /tmp/myprog.ast.dot
./synthesis /path/to/myprog.hsk > /tmp/myprog.df.dot
./codegen   /path/to/myprog.hsk > /tmp/myprog.fl

# Render images (optional)
dot -Tpng /tmp/myprog.ast.dot -o /tmp/myprog.ast.png
dot -Tpng /tmp/myprog.df.dot  -o /tmp/myprog.df.png
```

Generate supers + shared lib for that program:

```bash
mkdir -p /tmp/myprog_supers
tools/build_supers.sh /path/to/myprog.hsk /tmp/myprog_supers/Supers.hs
# Output: /tmp/myprog_supers/libsupers.so (+ ghc-deps/)
```

## Running on TALM (Trebuchet)

`TALM_DIR` points at the TALM checkout (default: `TALM`; set it to use another one):

```bash
TALM_DIR=TALM
P=8

# Assemble
python3 "$TALM_DIR/asm/assembler.py" -a -n "$P" -o /tmp/myprog /tmp/myprog.fl

# Run
"$TALM_DIR/interp/interp" "$P" \
  /tmp/myprog.flb \
  /tmp/myprog_auto.pla \
  /tmp/myprog_supers/libsupers.so
```

Notes:
- `-a` enables autoplacement (generates `*_auto.pla`).
- `-n P` defines the number of processing elements (PEs).

## Build Flags / Options

Makefile variables (override on the command line):

```bash
GHC=ghc-9.6.4 ALEX=alex HAPPY=happy DOT=dot make
```

Supers-specific flags:

```bash
SUPERS_THREADED=1        # default: 1 (link against threaded RTS)
SUPERS_WRAPPERS_MAX=256  # number of superN wrappers exported
make supers
```

Other useful overrides (advanced):
- `SUPERS_LINK_FLAGS` (custom link flags for `libsupers.so`)
- `TESTS` (limit which `test/*.hsk` are built)

## Design Decisions (catalog)

- **Dataflow graph is the source of truth**: `.dot` (Dataflow) and `.fl` (TALM) represent the same graph; `.fl` is the executable form for Trebuchet.
- **Function calls use TALM's call protocol**: each call site is a `callgroup`; arguments go through `callsnd f[i], arg, cg` (the call instance is identified by the exec tag, tags pass through unchanged), the return address through `retsnd`, and `ret f, result, [retsnds]` routes the result back to output `f.cg`. Multi-argument calls synchronize their arguments first so every `callsnd` of a callgroup sees the call instances in the same order.
- **Float multiply/divide are builtin supers** (`s10`/`s11`; user supers start at `s12`): Trebuchet has no `fmul`/`fdiv`. Float subtraction/negation flip the sign bit with `addi`.
- **Placement**: `ribault` spreads instructions over the PEs in contiguous blocks and raises the PE count if needed, since Trebuchet holds at most 500 instructions per PE.
- **Supers are compiled as shared libraries**: `libsupers.so` is produced with `-no-hs-main` and an RTS shim. Dependencies are bundled under `ghc-deps/` and loaded via rpath.
- **Threaded RTS by default**: `SUPERS_THREADED=1` to allow parallel execution in Trebuchet.
