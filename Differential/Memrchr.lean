import Differential.Relational
import Differential.Valid
import Differential.Code
/-!
# glibc 2.43's `memrchr` variants, differentially

No contract's result is used: each theorem compares two variants' code on one valid `memrchr` call (`CallOf` of
`C.memrchr`, `Valid.lean`), run in the model (`decide +kernel` over the model's `step`, tied to `run` by
`Relational.lean`). A disagreement refutes the variants' equivalence; it does not say which one is wrong.
-/
namespace Differential
open ZellicX86

/-- The calls on which two variants are compared: a valid call of `memrchr` for each (`CallOf` of `C.memrchr`, the code
at `entry`, returning to `ra`). -/
def MemrchrCalls (code₁ code₂ : List Byte) (i : Input) : Prop :=
  CallOf prof entry [(entry, code₁)] C.memrchr (call code₁ i) ra ∧
    CallOf prof entry [(entry, code₂)] C.memrchr (call code₂ i) ra

/-! ## The runs, evaluated by the kernel -/

theorem sse2_evexInput : retRax 64 Code.sse2 evexInput = some (0x110000000, 27) := by decide +kernel
theorem evex_evexInput : retRax 64 Code.evex evexInput = some (0x10000000, 22) := by decide +kernel
theorem evexFixed_evexInput : retRax 64 Code.evexFixed evexInput = some (0x110000000, 22) := by decide +kernel
theorem sse2_avx2Input : retRax 128 Code.sse2 avx2Input = some (0, 95) := by decide +kernel
theorem avx2_avx2Input : retRax 128 Code.avx2 avx2Input = some (0xffffffffffffffff, 45) := by decide +kernel
theorem avx2Fixed_avx2Input : retRax 128 Code.avx2Fixed avx2Input = some (0, 45) := by decide +kernel

/-! ## Disagreements -/

/-- **`__memrchr_evex` and `__memrchr_sse2` are not equivalent**: on the call with `n = 2 ^ 32` from `s = 0x10000001`
whose last byte is the one looked for, evex returns `s - 1` and sse2 `s + 2 ^ 32 - 1`. -/
theorem evex_sse2_disagree : ¬ Agree Code.evex Code.sse2 (MemrchrCalls Code.evex Code.sse2) :=
  not_agree_of_retRax ⟨evexInput_call _ (by decide +kernel), evexInput_call _ (by decide +kernel)⟩ evex_evexInput
    sse2_evexInput (by decide)

/-- **The `subq` fix changes `__memrchr_evex`'s result** on that call (where the fixed code agrees with sse2). -/
theorem evex_evexFixed_disagree : ¬ Agree Code.evex Code.evexFixed (MemrchrCalls Code.evex Code.evexFixed) :=
  not_agree_of_retRax ⟨evexInput_call _ (by decide +kernel), evexInput_call _ (by decide +kernel)⟩ evex_evexInput
    evexFixed_evexInput (by decide)

/-- **`__memrchr_avx2` and `__memrchr_sse2` are not equivalent**: with page 0 mapped, on the call `s = 5`, `n = 140`
for a byte that does not occur, avx2 returns `(void *) -1` and sse2 null. -/
theorem avx2_sse2_disagree : ¬ Agree Code.avx2 Code.sse2 (MemrchrCalls Code.avx2 Code.sse2) :=
  not_agree_of_retRax ⟨avx2Input_call _ (by decide +kernel), avx2Input_call _ (by decide +kernel)⟩ avx2_avx2Input
    sse2_avx2Input (by decide)

/-- **The `jb` fix changes `__memrchr_avx2`'s result** on that call (where the fixed code agrees with sse2). -/
theorem avx2_avx2Fixed_disagree : ¬ Agree Code.avx2 Code.avx2Fixed (MemrchrCalls Code.avx2 Code.avx2Fixed) :=
  not_agree_of_retRax ⟨avx2Input_call _ (by decide +kernel), avx2Input_call _ (by decide +kernel)⟩ avx2_avx2Input
    avx2Fixed_avx2Input (by decide)

end Differential
