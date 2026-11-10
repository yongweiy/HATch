# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

**Primary build command:**
```bash
dune build --profile release
```

**Run the tool directly:**
```bash
_build/default/bin/main.exe infer-incorrectness meta-config.json data/ri-with-bug/${bench}.ml
```


## Project Architecture

**Marple** is a verification tool for representation invariants using Hoare Automata Types (HATs) and Symbolic Finite Automata (SFAs). The codebase implements effect tracking alongside types with type inference and backward symbolic reasoning capabilities.

### Core Type and Effect System

- **syntax/**: Core language AST, type definitions, and effect syntax
  - Defines refinement types, automata predicates, HAT syntax, and effect tracking
  - Key files: `rty.ml`, `sfa.ml`, `aevent.ml`, `qualifier.ml`

- **inferincor/**: Type and effect inference engine
  - Infers precise types and effects for programs
  - Computes intersection ("weakening") with user-provided type/effect queries
  - Key files: `inferincor.ml`, `typing.ml`, `weaken.ml`, `rty_processor.ml`

- **backwards/**: Backward symbolic reasoning over effect language
  - Operates on effect language for symbolic analysis
  - Facilitates effect intersection computations
  - Key files: `backwards.ml`, `step.ml`, `config.ml`

### Automata and State Machine Infrastructure

- **stateMachine/**: Automata library backbone
  - Core automata/transducer operations supporting symbolic reasoning
  - Key files: `automaton.ml`, `transducer.ml`, `sig.ml`

- **automatize/**: SFA manipulation and effect-to-automata conversion
  - Converts LTLf formulas to symbolic finite automata
  - Swaps opaque effectful operations with automata/transducer representations
  - Enables symbolic reasoning over effects
  - Key files: `automatize.ml`, `derivative.ml`, `transducize.ml`

### Type Checking and Verification

- **typecheck/**: Core type checking logic
  - `bidirectional.ml`: Bidirectional type checking algorithm
  - Implements HAT type checking and refinement type verification

- **ntypecheck/**: Basic (OCaml) type checking and normalization
  - Converts code to A-normal form
  - Basic type inference before HAT verification

- **subtyping/**: Refinement subtyping logic
  - Handles subtype relationships between refinement types
  - SMT-based constraint solving for subtype checks

### Frontend and Parsing

- **bin/**: Main entry point and command-line interface
  - `main.ml`: Primary executable entry point
  - `commands/`: Command implementations (cri.ml for type checking, ctest.ml for testing)

- **frontend/**: Parser and source code transformation
  - Modified OCaml parser for handling HAT annotations and effects
  - Converts source code to internal AST representation

### Supporting Infrastructure

- **smtquery/**: Z3 SMT solver integration
  - Encodes refinement type constraints as SMT queries
  - Z3 wrapper and query optimization

- **desymbolic/**: Minterm transformation
  - Converts SFAs to finite automata for concrete execution
  - Decision tree data structures for instantiation

- **normalization/**: Code normalization to A-normal form
  - Required preprocessing step before type checking
  - Handles monadic normal form conversion

- **coersion/**: Type and effect coercion operations
  - Handles conversions between different type/effect representations

### Data Structure

- **data/ri/**: Benchmark inputs with correct implementations
- **data/ri-with-bug/**: Benchmark inputs with buggy implementations for testing
- **data/predefined/**: Built-in type definitions and axioms
- **data/incorrect/**: Additional test cases for validation

Each benchmark directory contains:
- `lib_nty.ml`: Basic OCaml types for underlying library
- `lib_rty.ml`: HAT types for underlying library  
- `automata_preds.ml`: Automata predicates (optional)
- `ri.ml`: Representation invariant shared by all interfaces
- `<interface>.ml`: Source code and HAT specifications

### Configuration

`meta-config.json` controls tool behavior:
- `debug_tags`: Controls debug output (preprocess, typing, result)
- `uninterops`: Built-in operators and predicates
- `prim_path`: Paths to predefined type files
- Output file paths for logs, results, and statistics

## Development Notes

- The tool expects precise type annotations on all functions and let bindings
- Supports subset of OCaml (no references, effects, parametric polymorphism, concurrency)
- Effect tracking is integrated alongside the type system
- Type inference engine can infer both types and effects before weakening with user queries
- Backward symbolic reasoning operates over the effect language
- Effectful operations can be symbolically represented as automata/transducers
- Terminal must support escape sequences for colored output
- Python virtual environment required for benchmark scripts (../.venv/bin/python)
- Coq formalization available in `formalization/` directory

- Run command like `_build/default/bin/main.exe infer-incorrectness meta-config.json data/incorrect/Dummy_IntStore/even.ml` whenever it is appropriate to test out the benchmark program.
- Remember to rebuild the executable before running it.
- the executable (after building) is `_build/default/bin/main.exe`
- If there is a lock. simply run the executable.
- Remember that this is the list benchmarks that we care:
```
|---------------------------------+--------+-----------+------------------+--------|
| task                            |   time | scaled up | note             | result |
|---------------------------------+--------+-----------+------------------+--------|
| Set_KVStore/insert_buggy        |   0.13 |           |                  |        |
| Heap_LinkedList/insert_buggy    |   2.28 |           |                  |        |
| LinkedList_KVStore/remove_buggy |   1.64 | yes       |                  |        |
| LinkedList_KVStore/concat       |   6.17 | yes       |                  |        |
| FileSystem_KVStore/delete_buggy | 184.51 |           | functional tree? |        |
| RedBlackTree_Tree/insert        |        |           | functional tree? |        |
| JS_Magnifier/magnifier          |   3.05 |           |                  |        |
| JS_Facebook/scraper             | 138.01 |           | functional tree  |        |
| Dafny_Graph/shortest_path       | 927.48 |           |                  |        |
| Dafny_Queue/to_stream           |   2.54 | yes       |                  |        |
| Dafny_Set/iterate               | 137.57 |           |                  |        |
|---------------------------------+--------+-----------+------------------+--------|
#+
```
