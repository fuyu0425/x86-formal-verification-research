# Differential checks of glibc's `memrchr` variants

This directory compares glibc 2.43's `memrchr` variants **with each other**, not with a contract. Two variants run on
the same call, in the release's x86-64 model, and the theorems compare the `rax` that each returns. The goal is to
see how much relational (differential) verification gives compared with the end-to-end (e2e) proofs of
`glibc-2.43-ubuntu-26.04-amd64/Glibc243Ubuntu/MemrchrStatement.lean`.

## Results

Lean's kernel checks each theorem (`Memrchr.lean`). Each depends only on `propext`, `Quot.sound` and
`Classical.choice`. No theorem uses a contract's result or a proof export.

| Theorem | Call | Result |
|---|---|---|
| `evex_sse2_disagree` | `s = 0x10000001`, `n = 2^32`, the last byte is `c` | evex returns `s - 1`, sse2 returns `s + 2^32 - 1` |
| `evex_evexFixed_disagree` | the same | the `subq` fix returns `s + 2^32 - 1` |
| `avx2_sse2_disagree` | page 0 mapped, `s = 5`, `n = 140`, `c` absent | avx2 returns `0xffffffffffffffff`, sse2 returns `0` |
| `avx2_avx2Fixed_disagree` | the same | the `jb` fix returns `0` |

Each theorem has the same form. This is the evex one (`Memrchr.lean`):

```lean
theorem evex_sse2_disagree : ¬ Agree Code.evex Code.sse2 (MemrchrCalls Code.evex Code.sse2)
```

The relation is `Agree` (`Relational.lean`). On each input in `P`, if both codes return, they return the same `rax`:

```lean
def Agree (code₁ code₂ : List Byte) (P : Input → Prop) : Prop :=
  ∀ i, P i → ∀ X₁ X₂, FirstReturn prof quiet (call code₁ i) 0 ra X₁ → FirstReturn prof quiet (call code₂ i) 0 ra X₂ →
    X₁.cpu.gpr.rax = X₂.cpu.gpr.rax
```

"Return" is the first state of the model's own `run` at the return address:

```lean
def FirstReturn (prof : Profile) (o : Oracle) (s₀ : State) (t : Nat) (ra : Addr) (X : State) : Prop :=
  ∃ n evs t', run prof o n s₀ t = (.running X, evs, t') ∧ X.cpu.rip = ra ∧
    ∀ m < n, ∀ Y evs' t'', run prof o m s₀ t = (.running Y, evs', t'') → Y.cpu.rip ≠ ra
```

The inputs in `P` are valid calls of `memrchr` for both codes, by the release's own `CallOf` of `C.memrchr`
(`Valid.lean`). So the disagreement does not come from an invalid input:

```lean
def MemrchrCalls (code₁ code₂ : List Byte) (i : Input) : Prop :=
  CallOf prof entry [(entry, code₁)] C.memrchr (call code₁ i) ra ∧
    CallOf prof entry [(entry, code₂)] C.memrchr (call code₂ i) ra
```

The proof evaluates both runs with `decide +kernel` (`retRax`, a fuel-bounded runner that `retRax_firstReturn` ties
to `FirstReturn`) and applies `not_agree_of_retRax`.

## How to check

1. Get the archive: `bash get-libc.sh`.
2. Build and check the theorems: `lake build Differential` (about 10 s, under 2 GB).
3. Check that `Code.lean` holds the bytes of `libc.a` and `fixed/`: `bash Differential/code.sh --check`.
4. Optional, on a CPU with AVX-512F/VL/BW: run the native differential test: `bash Differential/native.sh`.

## Files

| File | Content |
|---|---|
| `Run.lean` | The processor, an environment that does nothing (`quiet`), the entry state of a call (`call`), and a runner that stops at the first return (`retRax`) |
| `Relational.lean` | `FirstReturn`, `Agree`, and the proof that the runner finds the first return of `run` |
| `Valid.lean` | Both inputs are valid `memrchr` calls (`CallOf`), for any code of at most 4096 bytes |
| `Inputs.lean` | The two inputs from the blog post |
| `Memrchr.lean` | The kernel-evaluated runs and the four theorems |
| `Code.lean`, `code.sh` | The code bytes of the variants, generated from the objects |
| `native.c`, `native.sh` | The same comparison on the real CPU: random calls, then calls near `n = 2^32` |

## What the theorems do not say

- A disagreement does not say which variant is wrong. That sse2 is correct comes from the e2e proof `sse2_holds`.
- Each theorem is about one call. It says nothing about other calls.
- Lean does not prove that `Code.lean` holds glibc's bytes. `code.sh --check` compares them with the objects in
  `libc.a` and `fixed/`, as `Examples/Memcmp/Code.lean` does for `memcmp`.
- The environment is fixed (`quiet`, which is `Undisturbed`: `quiet_undisturbed`). A refutation needs only one
  environment. An agreement theorem would need every environment that `Undisturbed` allows, because undefined values
  and processor choices come from it.

## Evaluation: relational verification compared with e2e proofs

### What each method cost here

| | E2E proof (release) | Differential refutation (this directory) | Native differential test |
|---|---|---|---|
| Needs a spec | yes (`C.memrchr`, 69 lines) | no | no |
| Needs loop invariants | yes, for each variant | no | no |
| Needs proof automation | yes (not public) | no: `decide +kernel` evaluates the model | no |
| Hand-written Lean | not published for `memrchr` | about 570 lines with comments (`Run`, `Relational`, `Valid`, `Memrchr`) | none (98 lines of C) |
| Check time | under 4 minutes per theorem, exports of 4 to 50 MB | about 10 s for all four theorems | under 1 s |
| Scope of the result | every call | one call | the calls that were tried |
| Finds the evex bug | yes | yes, if you give it the input | yes, only with inputs near `n = 2^32` |
| Finds the avx2 bug | yes: per the blog post, the open proof obligations pointed at it | yes, if you give it the input | no: page 0 cannot be mapped without root |

The native test's 2,000,000 random calls have `n < 700` and objects away from page 0, so by construction they cannot
reach either bug, and they show no difference. The 24 calls with `n` near `2^32` were chosen for the evex bug, and 10
of them show it.

### Findings

1. **A refutation is cheap, and the kernel checks it.** The model is executable inside the kernel. Its memory is a
   function, so a 4 GiB object costs nothing. The six runs here (22 to 95 instructions each) take 8.5 s together. A
   counterexample from any source (a fuzzer, a review, a failed proof obligation) becomes a checked theorem in
   minutes, without a spec.
2. **Relational verification does not find the input.** The hard part is the witness. The evex bug occurs only for
   `n ≥ 2^32`, because the release proves evex correct below that (`evexHolds`, `evexOk`). The known witnesses
   (`evexBug`'s and ours) also put the last byte in the first 32 bytes of a page. The avx2 bug occurs only for
   `s < 32` (`avx2Holds`, `avx2Ok`), so page 0 must be mapped. A random input generator must aim at these cases to
   hit them. The blog post reports that the avx2 bug was found from the e2e proof's last open obligations, not by a
   test.
3. **Equivalence of different algorithms is not easier than e2e.** evex, avx2 and sse2 scan with different window
   sizes and alignments, so their loops do not run in lockstep. The invariant that relates two such loops says
   "both have the correct result for the bytes scanned so far". That is the spec. [INFERENCE] A proof of
   `Agree evex sse2` for all calls with `n < 2^32` would cost about as much as the e2e proofs. This is an estimate,
   not a measurement. It would still need sse2's e2e proof to say that the shared result is correct.
4. **Equivalence of nearly identical code is where relational verification is easier.** The shipped evex and the
   fixed evex differ in one instruction at offset `0x238` and one jump displacement at `0x227`. A lockstep proof
   relates two states that differ only in the code bytes. It needs no loop invariant and no knowledge of the
   algorithm. The proof needs three parts (not built here):
   - A generic step theorem for the model: from two states that differ only in code bytes that the instruction does
     not fetch, one step gives two states that differ in the same way. The decoder reads at most 15 bytes
     (`Decode.next`), and the interpreter reaches memory only through `check`, `readByte` and `writeByte`
     (`Machine.lean`). This part is written once for the model.
   - A frame fact: no data read reaches the bytes that differ. An e2e contract gives this through `reads`. Without a
     contract, an execute-only code page (a protection key, `pkeyDenies`) gives it.
   - A local proof at the three instructions that differ. After the `sub`, the two `rdx` values are equal when
     `n < 2^32`. This gives `Agree evex evexFixed (n < 2^32)` for every call.

   [INFERENCE] The generic part is several days of work, and each patch after that takes hours. This is the best
   fit for relational proofs: patches, backports and rebuilds of code that is already proved or trusted.
5. **A differential result needs a reference.** If every variant has the same bug, they all agree, and differential
   checking finds nothing. This is the main limit of relational verification compared with e2e.

### Practical workflow

The release already states e2e theorems for all six variants (`MemrchrStatement.lean:65-91`). The bugs are carve-outs
in those statements, not missing proofs:

| Statement | Calls it covers |
|---|---|
| `sse2Holds` | every call (with `sse2Reads`) |
| `evexHolds` | `n < 2^32` (`evexOk`) |
| `avx2Holds`, `avx2RtmHolds` | `s ≥ 32` (`avx2Ok`) |
| `evexFixedHolds`, `avx2FixedHolds` | every call |

Relational verification adds two things to that:

1. **Cheap refutations.** Turn each confirmed counterexample (from a fuzzer, a review, or a failed proof obligation)
   into a kernel-checked theorem, as in `Memrchr.lean`. Do this first. It takes seconds and needs no spec.
2. **A cheaper route to derived variants.** [INFERENCE] These are estimates, and the generic step theorem of
   finding 4 does not exist yet.
   - `avx2RtmHolds`, fully: glibc 2.43's `memrchr-avx2-rtm.S` redefines only the return macros and then includes
     `memrchr-avx2.S`. A lockstep proof against avx2, with `avx2Holds`, gives the same statement and the same
     `s ≥ 32` carve-out.
   - `evexFixedHolds` and `avx2FixedHolds`, partly: lockstep with the shipped code covers only the calls where the
     shipped code is correct (`n < 2^32`, `s ≥ 32`). The calls that the fix repairs still need a local e2e argument
     on the changed path, because there the shipped code is the wrong reference.

For a new variant:

- If it is a small diff of a proved variant (an rtm build, a patch, a backport, a rebuild), use a lockstep relational
  proof against that variant.
- If its algorithm is different, write its own e2e statement and proof. [INFERENCE] A relational proof against
  another variant would cost about the same, because the invariant that couples two different loops is the spec.
- Keep an e2e proof of at least one reference variant. It finds bugs that no test aims at (per the blog post, the
  avx2 bug), and it gives "agrees with the reference" its meaning.
