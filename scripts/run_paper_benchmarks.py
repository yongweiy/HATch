#!/usr/bin/env python3
"""Reproduce the evaluation table of the paper (IncorrectHAT, eval.tex).

For each of the 11 client programs it runs

  * our tool   : main.exe infer-incorrectness <bench> -unroll-bound k
                 with iterative deepening k = 1, 2, ..., --max-bound, stopping
                 at the first k that finds a witness.  The reported time is the
                 cumulative exec time over all attempted bounds (this is how
                 the "Buffered Write" number in the paper was obtained).
  * HATch      : main.exe symb-exec-incor <bench>   (baseline)

and prints a side-by-side comparison with the numbers currently in the paper.

Usage:
  scripts/run_paper_benchmarks.py                 # everything
  scripts/run_paper_benchmarks.py --only "Set"    # substring filter
  scripts/run_paper_benchmarks.py --no-hatch      # skip the baseline
Outputs go to benchmark_results/ (git-ignored): results.json, summary.md,
table.tex, and one log per run.
"""

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / "_build/default/bin/main.exe"
META = ROOT / "meta-config.json"
DATA = ROOT / "data/ri-with-bug"
OUT = ROOT / "benchmark_results"

# (paper name, benchmark file, paper "Our time", paper "HATch time")
# Order and numbers follow Table 3 of IncorrectHAT eval.tex (github/main 4299036).
# None for HATch = cell left empty in the paper ("projected to be T/O").
#
# TODO (HATch / symb-exec-incor baseline specs):
#   - Profile Scraper (JS_Facebook/lib_rty_old.ml): update findByClass (Node.t vs
#     Iterator.t) and 1-arg hasNext/next to match JS_Facebook/lib_nty.ml.
#   - Graph BFS (Dafny_Graph_List_Variants/lib_rty_old.ml): currently a copy of
#     lib_rty.ml ({ ret; eff }) instead of HATch Htriple ({ pre; res; newadding }).
#   - Set Copy (Dafny_Set/lib_rty_old.ml): hasNext/next have stub `pre = _G (Any true)`
#     instead of the iterator temporal precondition in Dafny_Set/lib_rty.ml.
#   - RB Tree Insert (RedBlackTree_CElem/insert_single_path.ml): Constrain query
#     observation events (GetLeft/GetRight on x) are not emitted by the client body.
BENCHMARKS = [
    ("Set Insert",      "Set_KVStore/insert_buggy.ml",                         0.45,  "0.70"),
    ("Heap Insert",     "Heap_LinkedList/insert_buggy.ml",                     0.96,  "0.85"),
    ("List Remove",     "LinkedList_KVStore/remove_buggy.ml",                  1.39,  "T/O"),
    ("List Concat",     "LinkedList_KVStore/concat.ml",                        0.61,  "T/O"),
    ("FS Delete",       "FileSystem_KVStore/delete_buggy.ml",                  36.19, None),
    ("RB Tree Insert",  "RedBlackTree_CElem/insert_single_path.ml",            17.84, "T/O"),
    ("Profile Scraper", "JS_Facebook/scraper.ml",                              8.51,  None),
    ("UI Interact",     "JS_Magnifier/magnifier.ml",                           0.66,  "1.11"),
    ("Buffered Write",  "Dafny_Queue/to_stream.ml",                            9.11,  "T/O"),
    ("Graph BFS",       "Dafny_Graph_List_Variants/single_queue_counter.ml",   37.57, None),
    ("Set Copy",        "Dafny_Set/iterate.ml",                                27.68, None),
]

EXEC_TIME_RE = re.compile(r"exec time\s+([\d.]+)\(s\)")


def run(cmd, timeout, log_path):
    start = time.time()
    try:
        p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        out, err, rc, timed_out = p.stdout, p.stderr, p.returncode, False
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        err = e.stderr.decode(errors="replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
        rc, timed_out = None, True
    wall = time.time() - start
    log_path.write_text(
        f"$ {' '.join(map(str, cmd))}\nrc={rc} timed_out={timed_out} wall={wall:.2f}s\n"
        f"=== STDOUT ===\n{out}\n=== STDERR ===\n{err}\n"
    )
    m = EXEC_TIME_RE.search(out)
    return {
        "rc": rc,
        "timed_out": timed_out,
        "wall": wall,
        "exec_time": float(m.group(1)) if m else None,
        "stdout": out,
        "stderr": err,
    }


def run_ours(bench, max_bound, timeout):
    attempts = []
    for k in range(1, max_bound + 1):
        log = OUT / f"ours_{bench.replace('/', '_')[:-3]}_k{k}.log"
        r = run([EXE, "infer-incorrectness", META, DATA / bench, "-unroll-bound", str(k)], timeout, log)
        ok = (not r["timed_out"]) and "type check succeeded" in r["stdout"]
        t = r["exec_time"] if r["exec_time"] is not None else r["wall"]
        attempts.append({"bound": k, "ok": ok, "timed_out": r["timed_out"], "time": t,
                         "crashed": (r["rc"] not in (0, None))})
        if ok:
            break
    ok = attempts[-1]["ok"]
    return {
        "status": "ok" if ok else ("T/O" if attempts[-1]["timed_out"] else "fail"),
        "bound": attempts[-1]["bound"] if ok else None,
        "time_at_bound": attempts[-1]["time"] if ok else None,
        "cumulative": sum(a["time"] for a in attempts),
        "attempts": attempts,
    }


def run_hatch(bench, timeout):
    log = OUT / f"hatch_{bench.replace('/', '_')[:-3]}.log"
    r = run([EXE, "symb-exec-incor", META, DATA / bench], timeout, log)
    if r["timed_out"]:
        status = "T/O"
    elif r["rc"] not in (0, None):
        status = "error"
    elif "Hatch" in r["stdout"]:  # "Terminated Hatch" / "Preemptive Hatch" = bug witness found
        status = "ok"
    else:
        status = "no witness"
    return {"status": status,
            "time": r["exec_time"] if r["exec_time"] is not None else r["wall"],
            "wall": r["wall"]}


def fmt(x):
    return "—" if x is None else f"{x:.2f}"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--only", help="substring filter on paper name or file")
    ap.add_argument("--max-bound", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=300, help="per-attempt timeout for our tool (s)")
    ap.add_argument("--hatch-timeout", type=int, default=300, help="timeout for HATch (s)")
    ap.add_argument("--no-hatch", action="store_true")
    args = ap.parse_args()

    if not EXE.exists():
        sys.exit(f"{EXE} not found; run `dune build --profile release` first")
    OUT.mkdir(exist_ok=True)

    benches = [b for b in BENCHMARKS
               if not args.only or args.only.lower() in (b[0] + b[1]).lower()]
    results = []
    for name, bench, paper_ours, paper_hatch in benches:
        print(f"[{name}] {bench}", flush=True)
        ours = run_ours(bench, args.max_bound, args.timeout)
        print(f"   ours : {ours['status']} bound={ours['bound']} "
              f"cumulative={fmt(ours['cumulative'])}s (paper {paper_ours})", flush=True)
        hatch = None
        if not args.no_hatch:
            hatch = run_hatch(bench, args.hatch_timeout)
            print(f"   hatch: {hatch['status']} {fmt(hatch['time'])}s (paper {paper_hatch or 'empty'})",
                  flush=True)
        results.append({"name": name, "file": bench, "paper_ours": paper_ours,
                        "paper_hatch": paper_hatch, "ours": ours, "hatch": hatch})

    (OUT / "results.json").write_text(json.dumps(results, indent=2))

    def hatch_cell(h):
        if h is None:
            return "skipped"
        return fmt(h["time"]) if h["status"] == "ok" else h["status"]

    lines = [
        f"# Paper benchmark reproduction ({time.strftime('%Y-%m-%d %H:%M')})",
        "",
        f"Our tool: iterative deepening of `-unroll-bound` 1..{args.max_bound}, "
        f"{args.timeout}s per attempt; time = cumulative exec time. HATch timeout: {args.hatch_timeout}s.",
        "",
        "| Client | File | Bound | Ours (s) | Paper ours | HATch (s) | Paper HATch |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    for r in results:
        o = r["ours"]
        ours_cell = fmt(o["cumulative"]) if o["status"] == "ok" else o["status"]
        lines.append(f"| {r['name']} | `{r['file']}` | {o['bound'] or '—'} | {ours_cell} | "
                     f"{r['paper_ours']} | {hatch_cell(r['hatch'])} | {r['paper_hatch'] or '(empty)'} |")
    (OUT / "summary.md").write_text("\n".join(lines) + "\n")

    tex = ["    \\begin{tabular}{lrc}", "         Client&  Our time&  HATch time\\\\"]
    for r in results:
        o = r["ours"]
        ours_cell = fmt(o["cumulative"]) if o["status"] == "ok" else "T/O"
        h = r["hatch"]
        hc = "" if h is None else (fmt(h["time"]) if h["status"] == "ok" else "T/O")
        tex.append(f"         {r['name']}&  {ours_cell}&  {hc}\\\\")
    tex.append("    \\end{tabular}")
    (OUT / "table.tex").write_text("\n".join(tex) + "\n")

    print("\n" + "\n".join(lines))


if __name__ == "__main__":
    main()
