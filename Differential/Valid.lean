import Differential.Inputs
import ZellicX86.Spec.Lib.C.String
/-!
# Both inputs are calls of `memrchr`

`evexInput` and `avx2Input` are valid calls of glibc's `memrchr` as the release states it (`C.memrchr`, `CallOf`), for
any code of 1 to 4096 bytes at `entry`. The proof is generic over an `Input` whose object pages lie apart from the code
and stack pages, below the end of the user address space, and hold the `n` bytes at `s` (`Placed`, `callOf`).
-/
namespace Differential
open ZellicX86

theorem pageOf_toNat (a : Addr) : (pageOf a).toNat = a.toNat / 4096 := by
  have := a.isLt
  simp only [pageOf, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

theorem pageOffset_toNat (a : Addr) : (pageOffset a).toNat = a.toNat % 4096 := by
  simp only [pageOffset, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

theorem ofNat_page (a : Addr) : BitVec.ofNat 64 (4096 * (pageOf a).toNat + (pageOffset a).toNat) = a := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [pageOf_toNat, pageOffset_toNat, BitVec.toNat_ofNat]
  omega

theorem canonical_of (a : Addr) (h : a.toNat < 2 ^ 47) : a.canonical false = true := by
  have : a >>> 47 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt h
  simp [Addr.canonical, this]

theorem entry_toNat : entry.toNat = 0x401000 := rfl
theorem rsp_toNat : rsp.toNat = 0x7fffffffe008 := rfl
theorem codePage_eq : codePage = 0x401 := rfl
theorem stackPage_eq : stackPage = 0x7fffffffe := rfl
theorem prof_la57 : prof.feat.la57 = false := rfl
theorem prof_pku : prof.feat.pku = false := rfl

theorem call_rsp (code : List Byte) (i : Input) : (call code i).cpu.gpr.rsp = rsp := rfl

/-- The pages `memory` maps: the code page (read and execute), the stack page and the object's pages (read and
write). -/
theorem map_pageOf (code : List Byte) (i : Input) (a : Addr) : (memory code i).map (pageOf a) =
    if inRuns [(codePage, 1), (stackPage, 1), (i.objPage, i.objPages)] (a.toNat / 4096) then
      (if a.toNat / 4096 = codePage then page ⟨true, false, true⟩ (pageOf a)
       else page ⟨true, true, false⟩ (pageOf a))
    else none := by
  simp only [memory, mapOn, pageOf_toNat]

/-- Each mapped page is backed by its page number, is its own area, is not special, and may be read. -/
theorem map_backing {code : List Byte} {i : Input} {p : PageNum} {m : Mapping}
    (h : (memory code i).map p = some m) : m.backing = p.toNat ∧ m.area = p.toNat ∧ m.special = false ∧
      m.maxProt.read = true := by
  simp only [memory, mapOn] at h
  split at h
  · split at h <;> (simp only [page, Option.some.injEq] at h; subst h; simp)
  · simp at h

theorem check_eq (code : List Byte) (i : Input) (pk : BitVec 32) (acc : Access) (a : Addr) :
    (memory code i).check prof.feat pk acc a =
      match (memory code i).map (pageOf a) with
      | none => some .notPresent
      | some m => if !m.allows prof.feat acc then some .protection else none := by
  unfold Memory.check Memory.check.rest
  cases (memory code i).map (pageOf a) with
  | none => rfl
  | some m => simp [memory, Backing.filePage, Backing.noSource, Backing.unpopulated, prof_pku]

/-- The byte at a mapped address: the code's on the code page, the return address's at `rsp`, the object's else. -/
theorem readByte_eq (code : List Byte) (i : Input) (a : Addr) (h : (memory code i).map (pageOf a) ≠ none) :
    (memory code i).readByte a =
      if a.toNat / 4096 = codePage then code.getD (a.toNat % 4096) 0
      else if a.toNat / 4096 = stackPage then
        (if rsp ≤ a ∧ a < rsp + 8 then (ra >>> (8 * (a - rsp).toNat)).setWidth 8 else 0)
      else i.obj a := by
  unfold Memory.readByte
  cases hm : (memory code i).map (pageOf a) with
  | none => exact absurd hm h
  | some m =>
    simp only [(map_backing hm).1, memory, Backing.frame, ofNat_page]
    simp only [pageOf_toNat, pageOffset_toNat]

/-- Where `i`'s object lies: on pages apart from the code and stack pages, ending before the last user page, and
holding the `n` bytes at `s`. -/
structure Placed (i : Input) : Prop where
  code : ¬ (i.objPage ≤ codePage ∧ codePage < i.objPage + i.objPages)
  stack : ¬ (i.objPage ≤ stackPage ∧ stackPage < i.objPage + i.objPages)
  lo : i.objPage * 4096 ≤ i.s.toNat
  hi : i.s.toNat + i.n.toNat ≤ (i.objPage + i.objPages) * 4096
  /-- The object's pages end at `2 ^ 47 - 4096`, `TASK_SIZE` (`34359738367 = 2 ^ 35 - 1` pages). -/
  user : i.objPage + i.objPages ≤ 34359738367

/-- The return address is the word at `rsp`. -/
theorem word_ra (code : List Byte) (i : Input) : Word (call code i) rsp ra := by
  have h8 : ∀ k ∈ List.range 8, (memory code i).readByte (rsp.add k) = (ra >>> (8 * k)).setWidth 8 := by
    intro k hk
    simp only [List.mem_range] at hk
    have hk' : (rsp.add k).toNat = 0x7fffffffe008 + k := by
      simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, rsp_toNat]; omega
    have hsub : (rsp.add k - rsp).toNat = k := by
      simp only [BitVec.toNat_sub, hk', rsp_toNat]; omega
    rw [readByte_eq]
    · simp only [hk', codePage_eq, stackPage_eq, hsub, BitVec.le_def, BitVec.lt_def, rsp_toNat,
        BitVec.toNat_add, show (8 : Addr).toNat = 8 from rfl]
      repeat' split
      all_goals first | omega | rfl
    · have h1 : inRuns [(codePage, 1), (stackPage, 1), (i.objPage, i.objPages)] ((rsp.add k).toNat / 4096) =
          true := by simp [inRuns, hk', stackPage_eq]; omega
      have h2 : ¬ (rsp.add k).toNat / 4096 = codePage := by rw [hk', codePage_eq]; omega
      simp [map_pageOf, h1, h2, page]
  unfold Word readBytes byteAddrs
  rw [List.map_map]
  show ofBytesLE 64 ((List.range 8).map fun k => (memory code i).readByte (rsp.add k)) = ra
  rw [List.map_congr_left h8]
  decide

theorem codeBytes (code : List Byte) (i : Input) (h : code.length ≤ 4096) :
    CodeBytes prof.feat (call code i) entry code := by
  have hmap : ∀ a : Addr, a.toNat / 4096 = codePage →
      (memory code i).map (pageOf a) = page ⟨true, false, true⟩ (pageOf a) := by
    intro a ha
    simp [map_pageOf, ha, inRuns]
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [Rgn.Mem, entry_toNat] at ha
    have ha' : a.toNat / 4096 = codePage := by rw [codePage_eq]; omega
    refine ⟨?_, ?_⟩
    · rw [prof_la57]; exact canonical_of a (by omega)
    · show (memory code i).check _ _ _ _ = none
      rw [check_eq, hmap a ha']
      simp [page, Mapping.allows]
  · unfold Bytes readBytes byteAddrs
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro k hk _
    simp only [List.length_map, List.length_range] at hk
    have hp : (entry.add k).toNat = 0x401000 + k := by
      simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, entry_toNat]; omega
    have ha : (entry.add k).toNat / 4096 = codePage := by rw [codePage_eq]; omega
    simp only [List.getElem_map, List.getElem_range, Function.comp]
    show (memory code i).readByte (entry.add k) = code[k]
    rw [readByte_eq _ _ _ (by rw [hmap _ ha]; simp [page]), ite_eq_left_of_eq_true _ _ (eq_true ha)]
    simp [hp, show (0x401000 + k) % 4096 = k by omega, List.getD_eq_getElem?_getD, hk]

theorem layoutOk (code : List Byte) (i : Input) (hp : Placed i) : LayoutOk prof.feat (call code i) where
  growsDown := by intro g hg; cases hg
  below p m h := by
    have := (map_backing h).1
    show m.backing < 2 ^ 52
    rw [this]; exact p.isLt
  brkMinPos := show 0 < (0x1000 : BitVec 64).toNat by decide
  brkMinLe := show (0x1000 : BitVec 64).toNat ≤ (0x1000 : BitVec 64).toNat from Nat.le_refl _
  maxRead p m h := (map_backing h).2.2.2
  user p m h := by
    left
    show (p.toNat + 1) * 4096 ≤ 34359738367 * 4096
    have hu := hp.user
    change (memory code i).map p = some m at h
    have hr : (1025 ≤ p.toNat ∧ p.toNat < 1025 + 1) ∨ (34359738366 ≤ p.toNat ∧ p.toNat < 34359738366 + 1) ∨
        (i.objPage ≤ p.toNat ∧ p.toNat < i.objPage + i.objPages) := by
      simp only [memory, mapOn, inRuns, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        decide_eq_true_eq, codePage_eq, stackPage_eq] at h
      split at h
      · assumption
      · simp at h
    clear h
    exact Nat.mul_le_mul_right 4096 (by omega)
  brkPage := show pageUp (0x1000 : BitVec 64).toNat ≤ taskSize prof.feat + 2 ^ 30 by decide
  areaBelow p m h := by
    have := (map_backing h).2.1
    show m.area < 2 ^ 52
    rw [this]; exact p.isLt

theorem frame_eq (code : List Byte) (i : Input) :
    frame (call code i) (C.memrchr.stack (call code i)) = ⟨rsp, 8⟩ := by
  simp [frame, call_rsp, C.memrchr, C.memrchrWith]

theorem foot_eq (code : List Byte) (i : Input) : C.memrchr.footprint [(entry, code)] (call code i) =
    { writes := [⟨rsp, 8⟩], own := [], reads := [⟨i.s, i.n.toNat⟩], code := [(entry, code)] } := by
  simp only [Contract.footprint, Contract.writesWithFrame, frame_eq]; rfl

/-- A call of `memrchr` on input `i` placed as `Placed` says, with code of 1 to 4096 bytes at `entry`. -/
theorem callOf (code : List Byte) (h : 0 < code.length ∧ code.length ≤ 4096) (i : Input) (hp : Placed i) :
    CallOf prof entry [(entry, code)] C.memrchr (call code i) ra := by
  have hlo := hp.lo
  have hhi := hp.hi
  have hu := hp.user
  have hc := hp.code
  have hs := hp.stack
  rw [codePage_eq] at hc
  rw [stackPage_eq] at hs
  -- an address of the object is on one of its pages
  have objPage : ∀ a : Addr, i.s.toNat ≤ a.toNat → a.toNat < i.s.toNat + i.n.toNat →
      i.objPage ≤ a.toNat / 4096 ∧ a.toNat / 4096 < i.objPage + i.objPages := by
    intro a h1 h2; omega
  have hrseq : rseqArea (call code i) = [] := by simp only [rseqArea]; rfl
  refine ⟨⟨rfl, ?_, by decide, ?_⟩, ⟨⟨rfl, rfl, rfl, rfl⟩, ?_, layoutOk code i hp⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, trivial⟩
  · rw [call_rsp]; exact word_ra code i
  · exact ⟨by rw [call_rsp]; decide, rfl, rfl⟩
  · exact trivial
  -- fits
  · rw [foot_eq]
    intro r hr
    simp [Footprint.data, Footprint.codeRgns] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [Rgn.Fits, rsp_toNat, entry_toNat] <;> omega
  -- writable: the return address's slot, on the stack page
  · rw [foot_eq]
    intro r hr a ha
    simp at hr
    subst hr
    simp only [Rgn.Mem, rsp_toNat] at ha
    refine ⟨by rw [prof_la57]; exact canonical_of a (by omega), ?_⟩
    show (memory code i).check _ _ _ _ = none
    have hp : a.toNat / 4096 = 0x7fffffffe := by omega
    rw [check_eq, map_pageOf]
    simp [hp, inRuns, codePage_eq, stackPage_eq, page, Mapping.allows]
  -- readable: the object, on its pages
  · rw [foot_eq]
    intro r hr a ha
    simp at hr
    subst hr
    obtain ⟨h1, h2⟩ := ha
    have ⟨p1, p2⟩ := objPage a h1 h2
    refine ⟨by rw [prof_la57]; exact canonical_of a (by omega), ?_⟩
    show (memory code i).check _ _ _ _ = none
    rw [check_eq, map_pageOf]
    have : inRuns [(codePage, 1), (stackPage, 1), (i.objPage, i.objPages)] (a.toNat / 4096) = true := by
      simp [inRuns]; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true this)]
    by_cases hcp : a.toNat / 4096 = codePage <;> simp [hcp, page, Mapping.allows]
  -- code
  · rw [foot_eq]
    intro c hc
    simp at hc
    subst hc
    exact codeBytes code i h.2
  -- notKernel, noAlias, notShared: every page has its own private backing
  · intro a _ m _
    exact ⟨fun f hf => (by cases hf), fun f hf => (by cases hf)⟩
  · intro a b _ _ hab m n hm hn
    refine ⟨?_, fun fp hf => by cases hf⟩
    rw [(map_backing hm).1, (map_backing hn).1]
    exact fun e => hab (BitVec.eq_of_toNat_eq e)
  · intro a _ m _ fp hf
    cases hf
  -- notFixed: nothing owned
  · rw [foot_eq]
    intro a ⟨r, hr, _⟩
    cases hr
  -- codeApart
  · rw [foot_eq]
    intro r hr q hq a ha hqa
    simp [Footprint.data, Footprint.codeRgns] at hr hq
    subst hq
    simp only [Rgn.Mem, entry_toNat] at hqa
    rcases hr with rfl | rfl
    · simp only [Rgn.Mem, rsp_toNat] at ha; omega
    · have := objPage a ha.1 ha.2; omega
  -- rseqApart
  · rw [hrseq]
    intro r hr
    cases hr
  -- frameApart
  · rw [frame_eq]
    intro r hr q hq a ha hqa
    simp [C.memrchr, C.memrchrWith, C.memrchrObject, Layout.owned] at hr hq
    subst hr hq
    simp only [Rgn.Mem, rsp_toNat] at ha
    have := objPage a hqa.1 hqa.2
    omega

theorem evexInput_call (code : List Byte) (h : 0 < code.length ∧ code.length ≤ 4096) :
    CallOf prof entry [(entry, code)] C.memrchr (call code evexInput) ra :=
  callOf code h evexInput ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem avx2Input_call (code : List Byte) (h : 0 < code.length ∧ code.length ≤ 4096) :
    CallOf prof entry [(entry, code)] C.memrchr (call code avx2Input) ra :=
  callOf code h avx2Input ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem quiet_undisturbed : Undisturbed quiet := fun _ _ _ h => nomatch h

end Differential
