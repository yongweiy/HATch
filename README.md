This is the artifact of *Derivative-Guided Symbolic Execution* under
submission to POPL 2025. The derivative-guided symbolic execution engine
**HATch**, along with its derivative-free variant, are provided. Please
follow the instructions below for installation and reproduction of
experiment results.

# Getting Started

We recommend the use of machines with at least 8 GB memory – **HATch**
raises errors when memory usage exceeds 8GB. All experiments were
performed on AMD Ryzen 7 PRO 6850U with 32 GB RAM. The artifact is
provided as a [Docker](https://docs.docker.com/get-docker/) image.
Before proceeding, try `docker run
hello-world` to ensure that Docker works as intended.

You may either load the pre-built docker image:

``` shell
docker load < ../hatch.tar.gz
```

or build the docker image on your own:

``` shell
docker build . --tag hatch
```

Then start a shell environment in the docker image:

``` shell
docker run -i --rm -t hatch
```

Lastly, compile **HATch** and find the executable at
\`\_build/default/bin/main.exe\`:

``` shell
dune build --profile release
```

# Falsify Individual ADT implementations

Directory `data/ri` stores various benchmarks in its subfolders, each
corresponding to an abstract data type (ADT) and its underlying stateful
representation type. Consider the implementation of `Stack` using
`LinkedList`, the sub-directory `data/ri/Stack_LinkedList` contains:

- the auxiliary definitions of common symbolic regular expressions in
  `automata_preds.ml`;
- the specification of `LinkedList`'s methods in `lib_rty.ml`;
- the safety property represented by a symbolic regular expression in
  `ri.ml`, and;
- the definition of `Stack`'s methods, e.g., `cons.ml` and
  `concat_aux.ml`, and their respective buggy variant (`_buggy`
  postfix), with accompanying specification that manifest the safety
  property.

Now we have **HATch** falsify the buggy implementation of
`data/ri/Stack_LinkedList/cons` (in place of `${bench}` below):

``` shell
timeout -v 1m _build/default/bin/main.exe symb-exec meta-config.json data/ri/${bench}_buggy.ml -empty-aware -exec-bound 20 -eff-append-bound 5
```

**HATch** falsifies the implementation by finding an execution path with

- `Phi` : the path condition collected along the execution path
- `Trace` : the trace of symbolic events that witness the execution path
- `R_cont` : a symbolic regular expression accepting traces that the
  execution can produce without violating the safety property
- `expr` : the term under execution

``` shell
Preemptive Hatch
Phi    = x:{v:Elem.t | true}, s:{v:Cell.t | true}, x_30_2:{v:bool | ¬v}, _x_5:{v:Cell.t | true}, c_2:{v:Cell.t | v == _x_5}, x_31_2:{v:bool | v <=> c_2 == s}, x_32_2:{v:bool | (v <=> ¬x_31_2) ∧ v}, x_30_11:{v:bool | ¬v}, _x_14:{v:Cell.t | true}, c_11:{v:Cell.t | v == _x_14}, x_31_11:{v:bool | v <=> c_11 == s}, x_32_11:{v:bool | (v <=> ¬x_31_11) ∧ ¬v}
Trace  = ⟨hasPrev x_0 = vret | ¬vret⟩; ⟨newCell x_0 = vret | vret == _x_5 ∧ ¬vret == c_11⟩; ⟨hasPrev x_0 = vret | ¬vret⟩; ⟨newCell x_0 = vret | vret == _x_14 ∧ vret == c_11⟩; ⟨putCellContent x_0 x_1 = vret | x_0 == c_11 ∧ x_1 == x⟩; ⟨setNext x_0 x_1 = vret | x_0 == c_11 ∧ x_1 == s ∧ x_0 == x_1⟩
R_cont = ∅
expr   =
(let (f_1 : Cell.t) =
   (let (c'_2 : Cell.t) = (c_11 : Cell.t) in (c'_2 : Cell.t) : Cell.t) in
 (f_1 : Cell.t) : Cell.t)
DT(Stack)  Task 1(cons): exec time 0.519420(s), check failed
```

In this case, `Phi` and `Trace` together are satisfiable – the
associated state is reachable – and `R_cont` is empty. Therefore,
**HATch** determines that the execution path is falsified.

The derivative-free variant of `HATch` can also falsify the buggy
implementation, though it takes longer:

``` shell
timeout -v 1m _build/default/bin/main.exe symb-exec meta-config.json data/ri/${bench}_buggy.ml -no-deriv -exec-bound 20
```

``` shell
Terminated Hatch
Phi    = x:{v:Elem.t | true}, s:{v:Cell.t | true}, x_30_2:{v:bool | ¬v}, _x_5:{v:Cell.t | true}, c_2:{v:Cell.t | v == _x_5}, x_31_2:{v:bool | v <=> c_2 == s}, x_32_2:{v:bool | (v <=> ¬x_31_2) ∧ ¬v}
R_curr = ((((((((.\⟨setNext x_0 x_1 = vret | x_0 == x_1⟩)* ∧ (.*;(⟨setNext x_0 x_1 = vret | x_1 == s⟩;.*))ᶜ);⟨hasPrev x_0 = vret | ¬vret⟩) ∧ .*);⟨newCell x_0 = vret | vret == _x_5⟩) ∧ (.*;(⟨newCell x_0 = vret | vret == c_2⟩;.*)));⟨putCellContent x_0 x_1 = vret | x_0 == c_2 ∧ x_1 == x⟩) ∧ .*);⟨setNext x_0 x_1 = vret | x_0 == c_2 ∧ x_1 == s⟩
expr   =
(c_2 : Cell.t)
DT(Stack)  Task 1(cons): exec time 1.592408(s), check failed
```

We regard prior work on type checking automata-augmented refinement type
as the baseline verifier:

``` shell
timeout -v 1m _build/default/bin/main.exe ri-type-check meta-config.json data/ri/${bench}_buggy.ml
```

Compared to **HATch**, the verifier also takes longer time to falsify
the same buggy implementation:

``` shell
DT(Stack)  Task 1(cons): exec time 1.556991(s), check failed
```

See Section <span class="spurious-link"
target="*Experiments">*Experiments*</span> for the complete list of
methods associated with each pair of ADT and its representation type.

# Experiments

The following table lists all methods whose buggy implementation are
falsified by **HATch** (first column). The next three columns are also
illustrated in Table 1 of the paper while the last two columns are
omitted.

|                                     |         |         |          |          |          |
|:------------------------------------|--------:|--------:|---------:|---------:|---------:|
| ADT_ReprType/method                 |   HATch |   Naive | SpeedUp/ | Verifier | SpeedUp/ |
|                                     | time(s) | time(s) |    Naive |  time(s) | Verifier |
| Stack_LinkedList/cons               |    0.29 |    0.91 |    × 3.1 |     1.03 |    × 3.6 |
| Stack_LinkedList/concat_aux         |    0.17 |    7.40 |   × 43.5 |     2.08 |   × 12.2 |
| Stack_KVStore/cons                  |    0.76 |   10.87 |   × 14.3 |     3.20 |    × 4.2 |
| Stack_KVStore/concat_aux            |    0.58 |     T/O |      T/O |     3.85 |    × 6.6 |
| Queue_LinkedList/append             |    0.49 |    1.21 |    × 2.5 |     1.25 |    × 2.6 |
| Queue_Graph/append                  |    1.11 |   14.45 |   × 13.0 |     8.15 |    × 7.3 |
| Set_KVStore/insert                  |    0.56 |   24.97 |   × 44.6 |     0.79 |    × 1.4 |
| Set_Tree/insert_aux                 |    0.70 |    3.33 |    × 4.8 |     7.75 |   × 11.1 |
| Heap_LinkedList/insert_aux          |    0.07 |    0.90 |   × 12.9 |     0.92 |   × 13.1 |
| Heap_Tree/insert_aux                |    0.64 |    1.52 |    × 2.4 |     1.58 |    × 2.5 |
| MinSet_Set/minset_singleton         |    0.72 |    0.91 |    × 1.3 |     0.92 |    × 1.3 |
| MinSet_Set/minset_insert            |    0.82 |    8.09 |    × 9.9 |     7.89 |    × 9.6 |
| MinSet_KVStore/minset_singleton     |    0.42 |    7.53 |   × 17.9 |     1.78 |    × 4.2 |
| MinSet_KVStore/minset_insert        |    1.17 |   13.23 |   × 11.3 |    18.22 |   × 15.6 |
| LazySet_Tree/insert_aux             |    0.70 |    3.32 |    × 4.7 |     7.82 |   × 11.2 |
| LazySet_Set/lazy_insert             |    0.31 |    0.40 |    × 1.3 |     0.42 |    × 1.4 |
| LazySet_KVStore/insert_aux          |    0.56 |   25.37 |   × 45.3 |     0.79 |    × 1.4 |
| DFA_KVStore/add_transition          |    0.41 |   12.59 |   × 30.7 |    12.59 |   × 30.7 |
| DFA_KVStore/del_transition          |    0.66 |    9.95 |   × 15.1 |     9.93 |   × 15.0 |
| DFA_Graph/add_transition            |    0.64 |    8.00 |   × 12.5 |     8.75 |   × 13.7 |
| DFA_Graph/del_transition            |    1.19 |   11.63 |    × 9.8 |    10.28 |    × 8.6 |
| ConnectedGraph_Set/singleton        |    0.18 |   54.51 |  × 302.8 |     2.82 |   × 15.7 |
| ConnectedGraph_Set/add_node         |    0.83 |     O/M |      O/M |     8.31 |   × 10.0 |
| ConnectedGraph_Set/add_transition   |    0.91 |     O/M |      O/M |    10.29 |   × 11.3 |
| ConnectedGraph_Graph/singleton      |    0.72 |    1.28 |    × 1.8 |     1.25 |    × 1.7 |
| ConnectedGraph_Graph/add_node       |    1.25 |    7.65 |    × 6.1 |     7.61 |    × 6.1 |
| ConnectedGraph_Graph/add_transition |    1.50 |   23.93 |   × 16.0 |    31.09 |   × 20.7 |
| ColoredGraph_Graph/add_edge         |    2.31 |     T/O |      T/O |      T/O |      T/O |
| ColoredGraph_KVStore/add_edge       |    4.88 |     T/O |      T/O |      T/O |      T/O |
| LinkedList_KVStore/remove_aux       |    4.98 |     T/O |      T/O |      N/A |      N/A |

The data in the table is produced using [org-babel shipped with
Emacs](https://orgmode.org/worg/org-contrib/babel/). With a recent
installation of **Emacs** (for scripting) and **pandoc** (for conversion
to markdown), one may rerun all experiments (takes about 20 minutes on
AMD Ryzen 7 PRO 6850U) and regenerate this file, including the above
table, using the following shell commands.

``` shell
emacs --batch -l ob -l ob-shell --eval "
  (let ((org-confirm-babel-evaluate nil))
    (dolist (file command-line-args-left)
  (with-current-buffer (find-file-noselect file)
    (org-table-recalculate-buffer-tables)
    (save-buffer))))
" README.org
pandoc -s README.org --to=gfm -o README.md
```
