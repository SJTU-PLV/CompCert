# Repository Guidelines

## Project Structure & Module Organization

This repository is a Coq + OCaml verified compiler project. Core Rust frontend sources live in `rustfrontend/` and `rustparser/`. The verified pipeline is composed in `driver/Compiler.v`, while the executable entrypoint and dump hooks live in `driver/DriverRust.ml` and `driver/Driver.ml`. CompCertO backend code is in `backend/`, `cfrontend/`, and architecture-specific directories such as `x86_64/`. Rust examples and regression inputs are under `rustexamples/`, especially `rustexamples/test/`.

## Build, Test, and Development Commands

- `./configure x86_64-linux && make depend && make all`: configure and build the full compiler.
- `make rust_comp`: rebuild the generated Rust compiler binary only.
- `./rust_comp test.rs -o test -dclight`: compile one Rustsurface file and emit frontend dumps.
- `cd rustexamples/test && make test`: run the Rust example compilation tests.
- `cd rustexamples/test && make compare-rustc`: compare `rust_comp` against nightly `rustc`.
- `cd coqrel && ./configure && make`: build the required `coqrel` dependency first.

## Coding Style & Naming Conventions

Use the existing style of each language and file. Coq files use concise definitions and proofs with section-local helpers; OCaml/lexer/parser files follow the current formatting already in the tree. Prefer editing source files such as `.v`, `.ml`, `.mly`, and `.mll`, not generated artifacts in `extraction/` or generated parser outputs. For diagnostic-only changes in proof-sensitive passes like `MoveChecking.v` or `BorrowCheckPolonius.v`, change only `Error (...)` payloads or helper `errmsg` builders unless a deeper refactor is explicitly required.

## Testing Guidelines

Keep validation targeted. For parser or frontend changes, rebuild with `make rust_comp` and run one focused `.rs` example that exercises the change. For broader Rust compatibility work, rerun `make compare-rustc`. Put new Rust regression cases under `rustexamples/test/` and use descriptive filenames matching the existing corpus.

## Commit & Pull Request Guidelines

Recent commit messages are short, imperative, and scoped to the user-visible change, for example: `Rename Rust compiler binary to rust_comp` and `Improve Rust place diagnostics and linked-list tests`. Follow that pattern. Keep commits focused, exclude generated files and unrelated worktree noise, and mention verification steps in the PR description. If a change affects dumps or diagnostics, include one representative command and output snippet.

## Proof Guidelines

Read ~/rocq-emacs-for-cli-agents/skills/rocqemacs/SKILL.md if asked to work on Coq proofs.

## Incremental proof workflow (Coq)

For Coq proof work in this repo, use the live Emacs session via the rocqagent API
(`~/rocq-emacs-for-cli-agents/rocqagent-call SERVER '(coqcheck_until ...)'`)
instead of re-running full `make` compiles after each edit:

- **Ask the user which Emacs server to use** at the start of a proof task. Do not
  guess the server name and do not silently fall back to `coqc`. Multiple servers
  may exist (e.g. `codexmem1`, `server`) with only one live. Once the user names
  the server, keep using it for the rest of the session.
- Before any shell-side edit to a `.v` file that is open in Emacs, call `save-file`.
- After a current-file edit, check with `coqcheck_until ... restart=nil` so Proof
  General only replays from the first changed sentence.
- Use `coqcheck_until` to inspect the current goal/error state at the failing point
  rather than guessing; then make the next edit.
- Use `restart=t` only after a dependency `.v` file changes; keep it `nil` otherwise.
- Reserve full `make`/`coqc` for final verification, not for per-edit iteration.

### Environment notes (macOS)

- `rocqagent-health` reports `socket_exists: false` even for a healthy server,
  because it looks for the Linux path `/run/user/UID/emacs/NAME` while the socket
  actually lives under `$TMPDIR/emacs501/NAME`. **Trust `rpc_state` / `rpc_ok`,
  not `socket_exists`.** A dead server instead reports
  `no_status_dead_socket` and `rocqagent-call` refuses it outright.
- `restart=t` requires a `dune-workspace` above the file (`find-root` in
  `rocqagent.el`). This repo builds via `Makefile` + `_CoqProject` and has no dune
  config, so the restart path is unavailable — incremental checking needs the
  reuse path, which requires the target file to be **open in Emacs with Proof
  General scripting active**. If it is not open, ask the user to open it.
- Full-file fallback (only when incremental checking is unavailable):
  `coqc $(cat _CoqProject) rustfrontend/File.v` from the repo root. If the working
  tree has an in-progress proof with no `Qed.`/`Admitted.`, coqc fails at the *next*
  `Lemma` with "Nested proofs are not allowed" — verify on a patched copy rather
  than editing the user's in-progress proof.


# RustCompCert Frontend Architecture (`rustfrontend/`)

A short overview of the verified Rust frontend of this CompCertO-based compiler:
the language layers, the pass pipeline, the verification structure, and how
pass correctness is proved with **forward simulation** — using `BorrowCheckSim.v`
as the worked example.

See [`README.md`](README.md) for build instructions and examples, and
[`docs/rustc-forward-borrow-checker-design.md`](docs/rustc-forward-borrow-checker-design.md)
for the borrow-checker design.

## What this is

`rust_comp` compiles Rust surface code to Clight, then the CompCertO backend to
Asm. The whole pipeline is verified in Coq. The top-level correctness statement
is `transf_rustlight_program_correct` in `driver/Compiler.v` (which yields a
`backward_simulation` of the `Rustlightown` semantics by the `Asm` semantics);
the pass composition is `transf_rustlight_program` in the same file.

## Repository layout

Status tag: `[legacy]` = not part of the current build (absent from or commented
out in `Makefile`'s `RUSTFRONTEND` list), kept for reference. Files without a
tag are in the build. Only tracked files are listed.

```
rustfrontend/
  Languages & semantics
    Rustsyntax.v                Rust surface syntax (formalized)
    Rusttypes.v                 shared type system: types, sizeof/alignof, composite_env, field offsets
    Rustlight.v                 Rustlight source language
    Rustlightown.v              Rustlight semantics with ownership
    InitDomain.v                components of the ownership semantics
    RustIR.v                    RustIR syntax
    RustIRcfg.v                 RustIR control-flow graph
    RustIRsem.v                 RustIR semantics without ownership
    RustIRown.v                 RustIR semantics with ownership
    RustIRbor.v                 RustIR semantics + stacked-borrow memory   [legacy]
    RustOp.v                    arithmetic / logical operators
    Rusttyping.v                typing of operators

  Compilation passes (implementation + verification)
    Rustlightgen.v              Rustsurface -> Rustlight (parse)
    RustIRgen.v                 Rustlight -> RustIR             [proof: RustIRgenProof.v]
    InitAnalysis.v              ownership analysis
    ElaborateDrop.v             drop elaboration                [proof: ElaborateDropProof.v]
    Clightgen.v                 RustIR -> Clight + drop glue    [spec: Clightgenspec.v, proof: Clightgenproof.v]

  Borrow & move checking (soundness largely WIP)
    MoveChecking.v              move-checking pass
    MoveCheckingDomain.v        domain / invariants used by move checking  [legacy]
    MoveCheckingSafe.v          legacy move-checking soundness             [legacy]
    MoveCheckingFootprint.v     footprint-based move-checking variant      [legacy]
    MoveCheckingFootprint1.v    footprint-based variant                    [legacy]
    BorrowCheck.v               main borrow checker (move + type + borrow checks)
    BorrowCheckDomain.v         region-state lattice / loan-flow domain
    BorrowCheckPolonius.v       Polonius-based borrow checking (dataflow)
    BorrowCheckPoloniusInterp.v Polonius with diagnostics logs
    BorrowCheckPoloniusForward.v  forward abstract-interpreter formulation
    BorrowCheckInv.v            borrow-check invariant (borrowck_inv, footprint well-formedness)
    BorrowCheckSim.v            forward simulation: spec semantics -> execution (WIP)
    BorrowCheckSound.v          borrow-check soundness (WIP)
    BorrowCheckLegacy.v         abstract-interpretation checker            [legacy]
    StkBorPermission.v          stacked-borrow permission model            [legacy]
    StkborDomain.v              static-analysis domain over stacked borrows [legacy]
    RegionLiveness.v            region liveness analysis
    ReplaceOrigins.v            freshen origins at function calls

  RustIR specification layer
    RustIRspec.v                functional spec: footprint maps, wt_state
    RustIRspecMem.v             memory-level spec: sem_wt_loc, sem_wt_val, coherent_fpm, fields_loc_sep
    RustIRspec1.v, RustIRspec2.v  earlier spec variants                    [legacy]

  Utilities
    Listmisc.v                  list helpers

  OCaml (printing / dumping)
    Dropglue.ml, PrintRustsyntax.ml, PrintRustlight.ml, PrintRustIR.ml, PrintBorrowCheck.ml

Adjacent files (outside rustfrontend/)
  rustparser/                lexer / parser: Rustsurface.ml, RustsurfaceLexer.mll, RustsurfaceParser.mly
  driver/Compiler.v          pipeline composition (transf_rustlight_program) + top-level correctness
```

## Language layers

- **Rustsurface** — the user-facing language: OCaml parser `rustparser/Rustsurface.ml`,
  formalized syntax in `Rustsyntax.v`.
- **Rustlight** — the verified source language: `Rustlight.v`, type system
  `Rusttypes.v`, ownership semantics `Rustlightown.v` + `InitDomain.v`.
- **RustIR** — the CFG-based intermediate language: `RustIR.v` (syntax),
  `RustIRcfg.v` (CFG), `RustIRsem.v` (semantics without ownership),
  `RustIRown.v` (semantics with ownership).
- **Clight** — the C-level target language (CompCert's `cfrontend/Clight.v`).

## Compiler passes

In pipeline order, mirroring `transf_rustlight_program`:

1. **Parse**: `RustsurfaceLexer.mll` / `RustsurfaceParser.mly` (in `rustparser/`)
   plus `Rustlightgen.v` (Rustsurface → Rustlight).
2. **Lower**: `RustIRgen.v` (Rustlight → RustIR).
3. **Drop elaboration**: ownership analysis `InitAnalysis.v` + `ElaborateDrop.v`.
4. **Borrow checking**: `MoveChecking.v` (move checking), then `BorrowCheck.v`
   with `BorrowCheckDomain.v` and `BorrowCheckPolonius*.v` (type + Polonius-style
   borrow checking). This is the still-evolving part of the frontend.
5. **Clight generation**: `Clightgen.v` (RustIR → Clight + drop glue).

## Verification structure

- **Per-pass correctness**: `RustIRgenProof.v`, `ElaborateDropProof.v`,
  `Clightgenproof.v` (each gives a `forward_simulation` between the source
  and target semantics); `Clightgenspec.v` is the translation specification
  (`tr_stmt` / `tr_function` / `tr_fundef` + `meet_spec` lemmas) that
  `Clightgenproof.v` builds on. They are chained with
  `compose_forward_simulations` in `driver/Compiler.v`.
- **RustIR spec/semantics layer**: `RustIRspec.v` (functional spec; `wt_state`),
  `BorrowCheckInv.v` (`borrowck_inv`), and `RustIRspecMem.v` (memory-level spec:
  `sem_wt_loc`, `sem_wt_val`, `sem_wt_val_list`, `coherent_fpm`, `fields_loc_sep`).
- **Borrow-checker soundness** is work in progress: `BorrowCheckSim.v`,
  `BorrowCheckSound.v`, `MoveCheckingSafe.v` (legacy). Several proofs still
  contain `admit`s / `Admitted`.

## Forward simulation, explained via `BorrowCheckSim.v`

### What it proves

`BorrowCheckSim.v` proves that the borrow-checking *spec* semantics of a RustIR
module is refined by its concrete *execution* semantics:

```
borrow_check_refinement : borrow_check_program M = OK M' ->
  forward_simulation rs_bor rs_bor (RustIRspec.semantics M) (RustIRsem.semantics M)
```

So if `M` passes borrow checking, safety of the spec semantics transfers to the
real execution semantics. (Currently `Admitted` — the file is a work in progress.)

### Infrastructure (`common/Smallstep.v`)

A forward simulation is a record `Forward_simulation` / `fsim_properties`
packing a well-founded order `fsim_order` on an index type, the relation
`fsim_match_states : index -> state_src -> state_tgt -> Prop`, and the step
diagram `fsim_simulation`:

```
source step S1 --t--> S1'   and   match_states i S1 S2   implies
  exists i' S2', (Plus L2 S2 t S2'  ∨  (Star L2 S2 t S2' ∧ order i' i))
              ∧  match_states i' S1' S2'
```

i.e. each source step is matched by one-or-more target steps with the same
trace (`Plus`), or by zero target steps (`Star`) with the index decreasing along
the well-founded order (stuttering). Derived diagrams
`forward_simulation_plus / _star / _step / _opt` specialize this, and the `fsim`
tactic assembles the record fields.

### The simulation relation is the crux

The hard part is defining `match_states`. In `BorrowCheckSim.v` the spec state
only carries the footprint map `fpm`, the frame index `fidx`, and the memory
block support `Mem.support m`; the concrete state carries the full memory `m`
and stack. `match_states` (with the mutually inductive `match_cont` /
`match_stacks`) glues them with separation logic:

```
match_regular_states:  coherent_fpm ce fpm MP  ∧  match_cont k tk FMP
                       ∧  m |= MP ** FMP
  match_states (RustIRspec.State f s k fpm fidx (Mem.support m))
               (State f s tk fpm m)
```

and call/return states additionally carry `sem_wt_val` / `sem_wt_val_list` and
`coherent_fpm` for the in/out footprints. Packaging the borrow-checking
invariants into a state correspondence like this is exactly the hard, most
error-prone step of every simulation proof.

### The step proof

`step_simulation` in `BorrowCheckSim.v`:

```
forall s1 t s2 s1',
  RustIRspec.step ge s1 t s2 -> match_states s1 s1' ->
  borrowck_inv s1 -> wt_state s1 ->
  exists s2', plus RustIRsem.step tge s1' t s2' ∧ match_states s2 s2' ∧ borrowck_inv s2
```

Note the extra `borrowck_inv s1` / `wt_state s1` hypotheses: the spec-state
invariants are needed to close each case. The proof shape is
`inv STEP; inv MATCH; inv BORINV; inv WTST` — **one case per spec step
constructor**, each showing "source takes one step, target takes one (or a few)
steps", then re-establishing `match_states` and the invariants.

### Top-down expression / place simulation

Each step case is discharged by *top-down* simulation lemmas over the
expression/place AST, plus invariant-preservation lemmas:

- `eval_pexpr_match`: spec `eval_pexpr ... = OK (vfp, fpm2)` implies the
  concrete `Rustlightown.eval_pexpr ... pe v` with `sem_wt_val ce vfp v mp` and
  `m |= mp ** MP ** FMP` (the separation predicate is threaded through);
- `eval_expr_match_by_value`, `get_owner_path_map_eval_place`: evaluating an
  expression / resolving the owner location of a place in the spec matches the
  concrete evaluation;
- invariant-preservation: `eval_expr_preserve_borchk_inv`,
  `borrow_check_inv_shallow_write`, `borrow_check_inv_set_fp`,
  `clear_is_dropped_fp_map_coherent`, ...

### Status and contrast with the pass proofs

`BorrowCheckSim.v` is not finished (contains `admit`s; `borrow_check_refinement`
is `Admitted`). The completed frontend pass proofs use the same `fsim` machinery
but with simpler `match_states` relations: `RustIRgenProof.v` (Rustlight → RustIR)
relates states structurally (translated function/statement/continuation, same
memory `m`); `Clightgenproof.v` (RustIR → Clight) is value-level — its
`match_states` uses `Mem.inject j m tm`, `match_env`, and `Val.inject`, and its
top-down lemmas are `eval_place_inject` / `eval_expr_inject` (source evaluation
implies the translated expression evaluates to the injected value).

## Proof development guidelines

### Lemma decomposition and proof order

When proving a lemma that requires helper sub-lemmas:

1. **Judge feasibility first**: Before introducing a sub-lemma, perform a high-level
   assessment of whether it can be proven given the current context and invariants.
   If you're uncertain, state your reasoning explicitly.

2. **Complete the main lemma first**: Write the complete proof of the main lemma,
   using `admit` for sub-lemma applications. This ensures the overall proof structure
   is sound before investing effort in helpers. Only after the main lemma's structure
   is validated should you go back and prove the admitted sub-lemmas.

3. **Decompose aggressively into named lemmas**: Most cases in `BorrowCheckSim.v` are
   step cases (not preservation or weakening). When a step case requires intricate
   reasoning about separation logic (`sem_wt_loc`, `coherent_fpm`, `massert_imp`),
   or about footprint transformations (`invalidate_conflict_ref_fpm`,
   `kill_views_ref_fpm`, `clear_footprint_map`), factor that reasoning into a named
   lemma with a precise statement. This keeps the main proof readable and makes
   sub-goals reusable.

4. **Never try to prove a false statement**: If a proof obligation doesn't go through,
   **do not force it**. Instead, identify and name the missing invariant or hypothesis.
   For example, if `coherent_fpm` is insufficient to close a goal, introduce a
   conjunct like `wt_fpm` or `fp_ref_loc_wf_fpm` and add it to the state invariant
   (`borrowck_inv` or `wt_state`). State clearly: "This goal requires invariant X;
   adding it as a hypothesis and deferring its preservation proof."

5. **Explain proofs bottom-up**: When presenting a completed proof (or proof sketch),
   explain it from the leaves to the root: start with the small lemmas (what they
   prove, why they're true), then show how they combine in the next layer, and finally
   how the top-level goal follows. This matches the dependency order and makes it
   easier to verify that no step is missing.

## Build and check

- **Full build**: From the repository root, run `make -j12` (adjust thread count as needed).
  Initial setup requires `./configure x86_64-linux && make depend` first.
- **Rebuild compiler binary**: `make rust_comp` in the root directory.
- **Incremental proof work**: Use the workflow in `AGENTS.md` (live Emacs + Proof General
  via the `rocqagent` API, e.g. `coqcheck_until`), not full `coqc` rebuilds after each edit.

## Incremental Proof Workflow Pitfalls

Use the live Emacs + Proof General session through `~/rocq-emacs-for-cli-agents/rocqagent-call SERVER ...`; do not iterate by repeatedly running full `coqc` or `make`. The following issues were observed while checking `rustfrontend/RustIRspecMem.v` on macOS:

- Ask for and use the user-specified Emacs server name. Do not assume `server`, `mem1`, or any other name. Check it with `rocqagent-health NAME`; a dead server reports `no_status_dead_socket`.
- `rocqagent-health` may report `socket_exists: false` even when the server is usable because it checks a Linux socket path. Trust `rpc_state` / `rpc_ok` and the actual macOS socket under `$TMPDIR/emacs501/NAME`.
- The helper may need permission to inspect local processes (it invokes `ps`). If the sandbox denies `ps`, the call fails before contacting Emacs; retry the same helper with the environment's approved elevated/local-process permission.
- Before a shell-side edit to a file open in Emacs, call `save-file` first. After editing the file on disk, do not call `save-file` again before checking, because that can overwrite the edit with a stale buffer. Run `coqcheck_until FILE LINE COL nil` so Proof General replays from the first changed sentence.
- The target `.v` file must be open with Proof General scripting active for the reuse path. If scripting is inactive, activate it in that buffer; `restart=t` is not a general fallback in this Makefile-based repository because there is no `dune-workspace`.
- Older Emacs versions may lack `while-let`, causing `coqcheck_until` to fail with `Symbol’s function definition is void: while-let`. Load `subr-x` and define the documented compatibility shim in the Emacs server, then retry.
- Use `restart=t` only after an imported dependency changed; use `restart=nil` for edits to the current file. Reserve a full `coqc`/`make` run for final verification.
- Keep demonstration or exploratory lemmas standalone and near the end of the file. Check the exact target line after editing, and report the returned `(:ok t ...)` result together with any pre-existing worktree changes.
