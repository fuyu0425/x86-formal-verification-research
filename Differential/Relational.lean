import Differential.Run
/-!
# Differential agreement of two functions' code

Two codes agree on a set of inputs when, from the same call, their first returns give the same `rax`. Stated with the
model's `run`; `toReturn` (which evaluates) is tied to it by `toReturn_firstReturn`.
-/
namespace Differential
open ZellicX86

/-- `X` is the first state at `ra` of the run from `s₀` (from stream position `t`): the run is at `X` after some
number of steps, `X`'s `rip` is `ra`, and no earlier state of the run is at `ra`. -/
def FirstReturn (prof : Profile) (o : Oracle) (s₀ : State) (t : Nat) (ra : Addr) (X : State) : Prop :=
  ∃ n evs t', run prof o n s₀ t = (.running X, evs, t') ∧ X.cpu.rip = ra ∧
    ∀ m < n, ∀ Y evs' t'', run prof o m s₀ t = (.running Y, evs', t'') → Y.cpu.rip ≠ ra

/-- What `toReturn` finds is the first return of the run, when the run does not start at `ra`. -/
theorem toReturn_firstReturn {prof : Profile} {o : Oracle} {ra : Addr} :
    ∀ (fuel : Nat) (s : State) (t : Nat) (X : State) (k : Nat),
      toReturn prof o ra fuel s t = some (X, k) → s.cpu.rip ≠ ra →
      (∃ evs t', run prof o k s t = (.running X, evs, t')) ∧ X.cpu.rip = ra ∧
        ∀ m < k, ∀ Y evs' t'', run prof o m s t = (.running Y, evs', t'') → Y.cpu.rip ≠ ra
  | 0, _, _, _, _, h, _ => by simp [toReturn] at h
  | fuel + 1, s, t, X, k, h, hs => by
    unfold toReturn at h
    rcases hstep : (step prof s).runStream o t with ⟨r, t'⟩
    rw [hstep] at h
    cases r with
    | stopped _ => simp at h
    | running s' ev =>
      simp only at h
      split at h
      · next hra =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨⟨ev.toList, t', by simp [run, hstep]⟩, hra, ?_⟩
        intro m hm Y _ _ hY
        obtain rfl : m = 0 := by omega
        simp only [run, Status.running.injEq, Prod.mk.injEq] at hY
        exact hY.1 ▸ hs
      · next hra =>
        obtain ⟨⟨X', k'⟩, hrec, hXk⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hXk
        obtain ⟨rfl, rfl⟩ := hXk
        obtain ⟨⟨evs, t'', hrun⟩, hX, hbefore⟩ := toReturn_firstReturn fuel s' t' X' k' hrec hra
        refine ⟨⟨ev.toList ++ evs, t'', by simp [run, hstep, hrun]⟩, hX, ?_⟩
        intro m hm Y evs' t''' hY
        cases m with
        | zero =>
          simp only [run, Status.running.injEq, Prod.mk.injEq] at hY
          exact hY.1 ▸ hs
        | succ m =>
          simp only [run, hstep] at hY
          rcases hm' : run prof o m s' t' with ⟨st, evs'', t4⟩
          rw [hm'] at hY
          simp only [Prod.mk.injEq] at hY
          obtain ⟨rfl, -, -⟩ := hY
          exact hbefore m (by omega) Y evs'' t4 hm'

/-- `retRax` finds the first return of the call of `code` on input `i`. -/
theorem retRax_firstReturn {fuel : Nat} {code : List Byte} {i : Input} {r : Addr} {k : Nat}
    (h : retRax fuel code i = some (r, k)) :
    ∃ X, FirstReturn prof quiet (call code i) 0 ra X ∧ X.cpu.gpr.rax = r := by
  obtain ⟨⟨X, k'⟩, hX, hr⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hr
  obtain ⟨⟨evs, t', hrun⟩, hra, hbefore⟩ :=
    toReturn_firstReturn fuel _ 0 X k' hX (by simp [call, entryCpu, entry, ra])
  exact ⟨X, ⟨k', evs, t', hrun, hra, hbefore⟩, hr.1⟩

/-- **Differential agreement**: the codes `code₁` and `code₂`, each placed at `entry`, return the same `rax` on every
input satisfying `P`, where both return (their first returns to `ra`, in the environment `quiet`). -/
def Agree (code₁ code₂ : List Byte) (P : Input → Prop) : Prop :=
  ∀ i, P i → ∀ X₁ X₂, FirstReturn prof quiet (call code₁ i) 0 ra X₁ → FirstReturn prof quiet (call code₂ i) 0 ra X₂ →
    X₁.cpu.gpr.rax = X₂.cpu.gpr.rax

/-- Two codes that return different `rax` on an input satisfying `P` do not agree on `P`: the form every
counterexample below takes, from two evaluations. -/
theorem not_agree_of_retRax {code₁ code₂ : List Byte} {P : Input → Prop} {i : Input} (hi : P i)
    {fuel₁ fuel₂ k₁ k₂ : Nat} {r₁ r₂ : Addr} (h₁ : retRax fuel₁ code₁ i = some (r₁, k₁))
    (h₂ : retRax fuel₂ code₂ i = some (r₂, k₂)) (hne : r₁ ≠ r₂) : ¬ Agree code₁ code₂ P := by
  intro hA
  obtain ⟨X₁, hX₁, rfl⟩ := retRax_firstReturn h₁
  obtain ⟨X₂, hX₂, rfl⟩ := retRax_firstReturn h₂
  exact hne (hA i hi X₁ X₂ hX₁ hX₂)

end Differential
