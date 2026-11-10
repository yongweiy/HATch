# HATch baseline specifications (`lib_rty_old.ml`)

The two tools in this repo read different library specifications for the same
benchmark:

| | new tool (`infer-incorrectness`) | HATch baseline (`symb-exec-incor`) |
|---|---|---|
| spec file | `lib_rty.ml` | `lib_rty_old.ml` (`bin/commands/cri.ml`, `prepare_symb_exec_incor`) |
| format | `{ ret; eff }` with `Admit` / `Append` / `Reject` / `Choice` | `{ pre; res; newadding }`, multi-case `[| ... |]` |
| history | rewritten: `Reject` erases past events (overwrite, delete, dequeue) | append-only; every call, reads included, is logged |
| existentials | `let (x : T) = ... in` inside `eff` | `((x : T) [@ghost])` parameters |

The client query is written once, as a new-format `Constrain (pre, post)` in the
client file. `bin/commands/constrain_to_htriple.ml` translates it for HATch:
- each event `Op (args, ret)` becomes the `pre` of `Op`'s `lib_rty_old.ml` case
  whose `res` admits `ret`;
- sequential events are conjoined;
- the result is the Htriple `{pre} e {res; post = ¬post}`.

`symb-exec-incor` reads this Htriple in reachability mode (`srlexec/utils.ml`,
`reach_mode`). A witness must terminate with its trace inside the query's
post-SFA **and** its result satisfying `res`.

For the comparison to be fair, each `lib_rty_old.ml` must express the same
library behaviour as `lib_rty.ml`.

## Encoding rules

- **State after `Reject`.** A read returns the *last* write that has not been
  erased since:
  `_F (Put ((k [@d]), (a [@d]), u, true) && _X (_G (not (Put ((k [@d]), b, u, true) || Del ((k [@d]), u, true)))))`.
- **Results.** A result that `lib_rty.ml` constrains through `ret` becomes a
  ghost `g` with `res = (v == g)`.
- **Negative cases.** A multi-case false branch is the negation of the true
  branch whenever that is expressible.
- **Under-approximation over unsoundness.** When an append-only history can't
  express a `Reject` exactly, the spec under-approximates: some executions match
  no case. Every HATch witness is then a real execution under `lib_rty.ml`'s
  semantics, at the cost of possibly missing witnesses.
- **Event binder names.** Don't name an event binder `x_i` at an argument
  position other than `i`. The frontend renames positional arguments to `x_0`,
  `x_1`, …, so `PutContact ((id [@d]), x_0, u, true)` silently constrains the
  wrong field.

## Approximations per benchmark

| Benchmark | Approximation |
|---|---|
| Set_KVStore | `hasValue` false case: "never stored" (ignores values overwritten or deleted since). |
| Heap_LinkedList, LinkedList_KVStore | `hasPrev` false case: "never linked" (ignores overwritten links). |
| FileSystem_KVStore | `hasNext` / `isDir` false cases: "no child added before" (ignore `DelChild`); no cross-event "every child was deleted". |
| JS_Magnifier | FIFO event queue by position, exact for ≤ 2 consumed events. |
| Dafny_Queue | FIFO queue and stream by position, exact for ≤ 5 dequeued elements; values may repeat. |
| Dafny_Graph_List_Variants | FIFO queue by successor (the head is the value added right after the last one taken). `add` requires a fresh value and `connect` a fresh edge. BFS satisfies both. |
| Dafny_Set | `add` does not drop duplicates (`lib_rty.ml` `Reject`s them). |
| RedBlackTree_CElem, JS_Facebook | none beyond the last-write rule |

## Queries the adapter cannot express

Conjoining sequential events is wrong when a later event consumes state, i.e.
when its `lib_rty.ml` spec `Reject`s. Such a benchmark gets a HATch-only client
whose query is a hand-written Htriple, registered in `HATCH_CLIENT_OVERRIDE` in
`scripts/run_paper_benchmarks.py`:

- `Dafny_Queue/to_stream_hatch.ml` (five consuming `GetChar`s).
