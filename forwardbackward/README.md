# Bidirectional Search for Incorrectness Reasoning

## Overview

This module implements **bidirectional search** for finding incorrectness witnesses by simultaneously exploring from both the **precondition** (forward) and **postcondition** (backward) and meeting in the middle.

## Motivation

The pure backward search in `backwards/` suffers from exponential search space growth with higher unroll bounds:

- **Problem**: With `unroll_bound=2`, effect depth doubles, creating exponentially more configurations
- **Example**: RedBlackTree works with `unroll_bound=1` (251 configs) but times out with `unroll_bound=2` (700+ configs)

**Bidirectional search** reduces complexity from **O(b^d)** to **O(b^(d/2))** by meeting in the middle.

## Architecture

### Modules

1. **`config.ml`**: Configuration types and worklist management
   - `backward_config`: Configuration for backward search
   - `forward_config`: Configuration for forward search
   - Separate worklists with different prioritization strategies

2. **`backward_step.ml`**: Backward stepping rules (from `backwards/step.ml`)
   - Works backwards from postcondition
   - Consumes effect from right to left
   - Composes automata backwards

3. **`forward_step.ml`**: Forward stepping rules (NEW)
   - Works forwards from precondition
   - Consumes effect from left to right
   - Composes automata forwards

4. **`forwardbackward.ml`**: Main bidirectional search algorithm
   - Alternates between forward and backward steps
   - Detects when searches meet
   - Combines paths from both directions

## How It Works

### Initialization

```ocaml
(* Backward search: start from postcondition *)
backward_worklist <- { rctx; eff; sfa = post; ... }

(* Forward search: start from precondition *)
forward_worklist <- { rctx; eff = Id; sfa = pre; ... }
```

### Search Loop

```
1. Pop config from backward worklist
2. Check if it matches any forward state (meeting point)
3. If yes: combine paths and check for witness
4. If no: expand backward config, add successors to worklist
5. Pop config from forward worklist
6. Check if it matches any backward state (meeting point)
7. If yes: combine paths and check for witness
8. If no: expand forward config, add successors to worklist
9. Repeat until witness found or worklists empty
```

### Meeting Detection

We use a **state fingerprint** based on:
- Effect depth (how much effect remains)
- Automaton difficulty (complexity of SFA)

Two states "meet" if their fingerprints are similar (within tolerance).

### Path Combination

When forward and backward searches meet:

```ocaml
combined_path = forward_path ; backward_path
```

The combined path represents the full execution from precondition to postcondition.

## Comparison with Pure Backward Search

| Aspect | Pure Backward | Bidirectional |
|--------|---------------|---------------|
| **Search space** | O(b^d) | O(b^(d/2)) |
| **Configs explored** | All at depth d before d+1 | Half depth from each end |
| **Memory** | Single worklist | Two worklists + state tables |
| **Complexity** | Simpler | More complex (meeting detection) |

### Example: RedBlackTree with unroll_bound=2

**Pure backward:**
- Effect depth: 26
- Configs at each depth: ~30
- Total configs: 30^26 (astronomical)
- Result: Timeout after 700+ configs

**Bidirectional (expected):**
- Forward depth: 13
- Backward depth: 13
- Configs from each end: 30^13
- Total configs: 2 × 30^13 (much smaller)
- Result: Should find witness faster

## Forward Stepping Rules

The forward stepping rules are the **dual** of backward stepping:

### Backward (from `backwards/step.ml`)

```ocaml
(* SBSeq: Process right-to-left *)
Seq (eff1, eff2) →
  step eff2, then prepend eff1

(* SBAtom: Compose backwards *)
Trans (Explicit sft) →
  sfa_pre = sft ∘ sfa_post
```

### Forward (NEW in `forward_step.ml`)

```ocaml
(* FSeq: Process left-to-right *)
Seq (eff1, eff2) →
  step eff1, then continue with eff2

(* FAtom: Compose forwards *)
Trans (Explicit sft) →
  sfa_post = sfa_pre ∘ sft
```

## Prioritization Strategies

### Backward Worklist
Uses the same lexicographic strategy as `backwards/`:
- Primary: Effect depth (lower = higher priority)
- Secondary: Difficulty/width ratio

### Forward Worklist
Inverted priority:
- Primary: Effect depth (higher = higher priority, prefer to consume effect)
- Secondary: Difficulty/width ratio

This ensures forward search makes progress consuming the effect.

## Usage

The module provides the same interface as `backwards/`:

```ocaml
val run : 
  ROpTypectx.ctx -> 
  RTypectx.ctx -> 
  Eff.t -> 
  Sft.sft -> (* post *)
  Sft.sft -> (* pre *)
  (RTypectx.ctx * Eff.t) option
```

To use bidirectional search instead of pure backward:

```ocaml
(* Old: *)
let result = Backwards.run opctx rctx eff post pre

(* New: *)
let result = Forwardbackward.run opctx rctx eff post pre
```

## Expected Benefits

1. **Reduced search space**: O(b^(d/2)) vs O(b^d)
2. **Better scaling**: Should handle higher unroll bounds
3. **Earlier termination**: Finds witnesses faster by meeting in middle
4. **Parallelization potential**: Forward and backward can run in parallel

## Potential Challenges

1. **Meeting detection**: Fingerprinting may miss exact matches
2. **Memory overhead**: Two worklists + state tables
3. **Path combination**: Ensuring correctness when combining paths
4. **Tuning**: May need to adjust meeting tolerance and alternation strategy

## Future Improvements

1. **Parallel execution**: Run forward and backward in separate threads
2. **Adaptive alternation**: Dynamically choose which direction to expand
3. **Better fingerprinting**: More precise state matching
4. **Incremental meeting**: Check for partial matches during search
5. **Heuristic guidance**: Use program structure to guide search direction

## Testing

To test the bidirectional search:

```bash
# Build
dune build --profile release

# Run on RedBlackTree with unroll_bound=2
_build/default/bin/main.exe infer-incorrectness-bidirectional \
  meta-config.json \
  data/ri-with-bug/RedBlackTree_CElem/insert_single_path.ml \
  -unroll-bound 2
```

Expected output:
```
[Config #1] [BACKWARD #1] width: 2, steps: 0, remaining: 26, difficulty: 12
[Config #2] [FORWARD #1] width: 3, steps: 0, remaining: 0, difficulty: 8
...
*** MEETING POINT FOUND! ***
Forward steps: 13, Backward steps: 13, Total: 26
Witness found at meeting point!
```

## References

- **Bidirectional search**: Classic AI search technique (Russell & Norvig)
- **Meet-in-the-middle**: Reduces exponential complexity by half
- **Symbolic execution**: Forward symbolic execution (King 1976)
- **Backward reasoning**: Weakest precondition calculus (Dijkstra 1975)

