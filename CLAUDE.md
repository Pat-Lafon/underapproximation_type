# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is the **Poirot** type system library — a coverage (underapproximation) refinement type checker for verifying test input generators, from the PLDI 2023 paper "Covering All the Bases." It is used as a core library by the Cobb synthesizer (parent directory `../`). See `../CLAUDE.md` for the broader synthesis context.

Coverage types specify **what inputs a generator must produce** (underapproximation), unlike standard refinement types which specify what outputs are allowed (overapproximation).

## Build Commands

```bash
# Build
dune build

# Run tests
dune test

# Type-check a benchmark
dune exec -- bin/main.exe coverage-type-check meta-config.json \
  data/benchmark/quickchick/sizedlist/prog.ml \
  data/benchmark/quickchick/sizedlist/_under.ml

# Type inference (abduction) — writes result to .abd file
dune exec -- bin/main.exe type-infer meta-config.json <source.ml>

# Subtype check between two refinement types
dune exec -- bin/main.exe subtype-check meta-config.json <source.ml>

# Print coverage types from a refinement type file
dune exec -- bin/main.exe print-coverage-types meta-config.json <_under.ml>

# Print source code at different pipeline stages
dune exec -- bin/main.exe print-source-code [raw|erase] meta-config.json <source.ml>

# Generate axioms for proof assistants
dune exec -- bin/main.exe coq-axioms meta-config.json
dune exec -- bin/main.exe lean-axioms meta-config.json
```

## Architecture

### Processing Pipeline

OCaml source + refinement type file go through:

1. **Parsing** (`Ocaml5_parser.Frontend.parse`) — OCaml 5 parser
2. **Item conversion** (`frontend_opt/to_item.ml`) — OCaml AST to internal `Item` type
3. **Normal type checking** (`preprocessing/`) — basic type inference and normalization
4. **ANF translation** (`translate/`) — convert to Monadic Normal Form (A-Normal Form variant)
5. **Coverage type checking** (`typing/termcheck.ml`) — check against refinement types
6. **Subtyping via SMT** (`subtyping/` + `backend/`) — discharge subtyping obligations to Z3

### Library Dependency Graph

```
bin/commands (executable entry points: cre.ml, ctest.ml)
  └── typing (termcheck.ml, termsyn.ml, itemcheck.ml)
        ├── subtyping (subrty.ml, subcty.ml)
        │     └── backend (check.ml, smtquery.ml → Z3)
        ├── inference (cegis.ml, feature.ml)
        └── frontend_opt (to_*.ml converters)
              ├── syntax (AST: term, rty, prop, cty, lit, op — unwrapped)
              └── preprocessing (normal type checking)
                    └── language (language.ml, simp.ml — unwrapped)
env (zzenv.ml — global config, debug flags, prim_path)
```

Key: `syntax` and `language`/`translate` are **unwrapped** libraries (modules exposed at top level), everything else is **wrapped**.

### Key Module Interfaces

- **`FrontendTyped`** — main interface for working with typed terms; provides `layout_rty`, `layout_item_to_coq`, `pprint_typectx_subtyping`, etc.
- **`FrontendRaw`** — interface for raw (untyped) terms
- **`Env`** — global environment: `load_meta`, `get_prim_path`, `show_debug_typing`, `get_resfile`, debug flag accessors
- **`Item`** — top-level declaration ADT: `MFuncImp`, `MRty`, `MAxiom`, `MTyDecl`, `MMethodPred`, `MValDecl`

### Two Entry Point Commands

The executable (`bin/main.ml`) dispatches to one of two command groups:

- **`cre.ml`** — the main Poirot commands: `type-check`, `type-infer`, `subtype-check`, `coq-axioms`, `lean-axioms`, `print-source-code`
- **`ctest.ml`** — legacy/alternate commands: `coverage-type-check`, `print-coverage-types`, `split-source-code`, `check-fv-in-code`

Currently `main.ml` uses `Cre.test` as the entry point. The `coverage-type-check` command is in `ctest.ml` while `type-check` is in `cre.ml` — they have different interfaces (ctest takes a separate refinement type file, cre loads it from config).

### Type System Concepts

- **Coverage type** `[v:b | φ]` — underapproximation base type (generator must produce values satisfying φ)
- **Overapproximation type** `{v:b | φ}` — standard refinement base type (values must satisfy φ)
- **Function type** `let x = T₁ in T₂` — represents `x:T₁ → T₂`
- **Method predicates** — uninterpreted functions for datatype properties (e.g., `len`, `sorted`, `complete_tree`), defined in `data/predefined/axioms_of_predicates.ml`
- **`cty`** — core type (base type + refinement prop)
- **`rty`** — refinement type (base arr or arr-arr, with over/under distinction)

### SMT Backend

- `backend/smtquery.ml` — manages a global Z3 context (`Smtquery.ctx`)
- `backend/dtencoding.ml` — encodes list and tree datatypes into Z3
- `backend/propencoding.ml` / `litencoding.ml` — encode propositions/literals to Z3 expressions
- `backend/check.ml` — top-level validity/satisfiability checks
- Custom datatypes are registered via `Z3aux.create_and_register_datatype`

## Configuration

`meta-config.json` controls all behavior:

- **`prim_path`** — paths to predefined types (`data_type_decls`, `normal_typing`, `coverage_typing`, `axioms`, `templates`)
- **`debug_tags`** — uncomment to enable: `"preprocess"`, `"ntyping"`, `"typing"`, `"queries"`, `"result"`
- **`resfile`/`logfile`/`abdfile`** — output file extensions (`.result`, `.log`, `.abd`)
- **`abd_templates`** — abduction templates for type inference
- **`num_quantifier`** — controls quantifier depth

## Data Directory

- `data/predefined/` — built-in types, axioms, and templates shared across benchmarks
  - `data_type_decls.ml` — supported OCaml types
  - `normal_typing.ml` — standard type signatures for primitives
  - `coverage_typing.ml` — coverage type annotations for primitives
  - `axioms.ml` — axioms about method predicates
  - `templates.ml` — templates including `rec_arg` constraints for recursive functions
  - `lean_preamble.lean` — prepended to dumped Lean subtyping query files; contains type declarations, helper predicates, method predicates, and imports (e.g., `ProofAutomation`)
  - `builtin_datatype_coverage_typing/` — per-datatype coverage type files
- `data/benchmark/` — evaluation benchmarks from the PLDI paper
- `data/validation/` — validation benchmarks (including `*_imprecise` for synthesis testing)

## Common Errors

**`(name: none) =? none`** — Missing type signature. Add to `data/predefined/normal_typing.ml` and `data/predefined/coverage_typing.ml`.

**Z3 build failures** — Z3 installation requires ~32GB RAM. Use pre-built binaries or Docker.

**RecArgCheckFailure** — Recursive argument constraint check failed during type checking of recursive functions. Check `rec_arg`/`rec_arg2` templates in `data/predefined/templates.ml`.
