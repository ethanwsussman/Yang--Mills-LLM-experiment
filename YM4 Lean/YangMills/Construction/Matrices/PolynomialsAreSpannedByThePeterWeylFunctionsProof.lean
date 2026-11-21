import YangMills.Construction.Matrices.ClassicalHarmonicAnalysisOnG
import YangMills.Construction.Matrices.PolynomialsAreSpannedByThePeterWeylFunctionsForm
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.HilbertSpaceBasics
noncomputable section
namespace YangMills.Construction.SpinHarmonics.PeterWeylPolynomials
abbrev coeffSpanAll : Submodule ℂ C(specialUnitary, ℂ) := ⨆ t, coeffSpan t
abbrev normalizedCoeffSpan : Submodule ℂ C(specialUnitary, ℂ) :=
  Submodule.span ℂ (Set.range normalizedCoeff)
abbrev peterWeylFnSpan (J : Type) [Finite J] : Submodule ℂ C(J → specialUnitary, ℂ) :=
  Submodule.span ℂ (Set.range (peterWeylFn : PeterWeylIndex J → C(J → specialUnitary, ℂ)))
section OneVariable
theorem isPolyInEntries_iff_exists_mem (h : HarmonicAnalysisFacts) (F : specialUnitary → ℂ) :
    IsPolyInEntries F ↔ ∃ ψ ∈ coeffSpanAll, ∀ g, ψ g = F g :=
  (h ⟨0⟩ ⟨0⟩).2.1.isPolyInEntries_iff F
theorem mul_mem_coeffSpanAll (h : HarmonicAnalysisFacts) {a c : C(specialUnitary, ℂ)}
    (ha : a ∈ coeffSpanAll) (hc : c ∈ coeffSpanAll) : a * c ∈ coeffSpanAll := by
  obtain ⟨p, hp⟩ := (isPolyInEntries_iff_exists_mem h a).mpr ⟨a, ha, fun _ => rfl⟩
  obtain ⟨q, hq⟩ := (isPolyInEntries_iff_exists_mem h c).mpr ⟨c, hc, fun _ => rfl⟩
  obtain ⟨ψ, hψ, hev⟩ := (isPolyInEntries_iff_exists_mem h fun g => a g * c g).mp
    ⟨p * q, fun g => by simp [hp g, hq g]⟩
  have hψeq : ψ = a * c := ContinuousMap.ext hev
  rwa [← hψeq]
theorem one_mem_coeffSpanAll (h : HarmonicAnalysisFacts) :
    (1 : C(specialUnitary, ℂ)) ∈ coeffSpanAll := by
  obtain ⟨ψ, hψ, hev⟩ := (isPolyInEntries_iff_exists_mem h fun _ => 1).mp ⟨1, fun g => by simp⟩
  have hψeq : ψ = 1 := ContinuousMap.ext hev
  rwa [← hψeq]
theorem entryMap_mem_coeffSpanAll (h : HarmonicAnalysisFacts) (i j : Fin 2) :
    entryMap i j ∈ coeffSpanAll := by
  obtain ⟨ψ, hψ, hev⟩ := (isPolyInEntries_iff_exists_mem h (entryMap i j)).mp
    ⟨MvPolynomial.X (i, j), fun g => by simp [entryMap, entryValues]⟩
  have hψeq : ψ = entryMap i j := ContinuousMap.ext hev
  rwa [← hψeq]
theorem star_mem_coeffSpanAll (h : HarmonicAnalysisFacts) {a : C(specialUnitary, ℂ)}
    (ha : a ∈ coeffSpanAll) : star a ∈ coeffSpanAll := by
  refine Submodule.iSup_induction coeffSpan (motive := fun x => star x ∈ coeffSpanAll) ha
    (fun t x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · obtain ⟨ψ, hψ, hev⟩ := (h t t).2.1.star_mem x hx
    have hψeq : ψ = star x := ContinuousMap.ext hev
    rw [← hψeq]
    exact Submodule.mem_iSup_of_mem t hψ
  · rw [star_add]
    exact Submodule.add_mem _ hx hy
theorem normalizedCoeff_mem_coeffSpanAll (ℓ : PeterWeylLabel) : normalizedCoeff ℓ ∈ coeffSpanAll :=
  Submodule.mem_iSup_of_mem ℓ.spin
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(ℓ.rowIdx, ℓ.colIdx), rfl⟩))
theorem coeffSpanAll_le_normalizedCoeffSpan : coeffSpanAll ≤ normalizedCoeffSpan := by
  refine iSup_le fun t => Submodule.span_le.mpr ?_
  rintro _ ⟨⟨a, c⟩, rfl⟩
  have hnn : 0 ≤ t.toReal := by
    simp only [HalfNatural.toReal]
    positivity
  have hpos : 0 < Real.sqrt (2 * t.toReal + 1) := Real.sqrt_pos.mpr (by linarith)
  have hne : ((Real.sqrt (2 * t.toReal + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hrepr : spinCoeffMap t a c =
      ((Real.sqrt (2 * t.toReal + 1) : ℝ) : ℂ)⁻¹ • normalizedCoeff ⟨t, a, c⟩ := by
    simp only [normalizedCoeff, smul_smul, inv_mul_cancel₀ hne, one_smul]
  change spinCoeffMap t a c ∈ normalizedCoeffSpan
  rw [hrepr]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
end OneVariable
section SeveralVariables
variable {J : Type} [Finite J]
theorem coordProduct_update_apply [Fintype J] [DecidableEq J] (f : J → C(specialUnitary, ℂ)) (b : J)
    (x : C(specialUnitary, ℂ)) (u : J → specialUnitary) :
    coordProduct (Function.update f b x) u =
      x (u b) * ∏ c ∈ Finset.univ.erase b, f c (u c) := by
  change (∏ᶠ c, Function.update f b x c (u c)) = _
  rw [finprod_eq_prod_of_fintype, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
  simp only [Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun c hc => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hc)]
theorem coordProduct_mem_of_finset [Fintype J] [DecidableEq J] (s : Finset J) :
    ∀ f : J → C(specialUnitary, ℂ), (∀ b ∈ s, f b ∈ normalizedCoeffSpan) →
      (∀ b, b ∉ s → f b ∈ Set.range normalizedCoeff) → coordProduct f ∈ peterWeylFnSpan J := by
  induction s using Finset.induction_on with
  | empty =>
    intro f _ hf
    choose α hα using fun b => hf b (Finset.notMem_empty b)
    have hfeq : f = fun b => normalizedCoeff (α b) := funext fun b => (hα b).symm
    rw [hfeq]
    exact Submodule.subset_span ⟨α, rfl⟩
  | insert b s hb ih =>
    intro f hin hout
    have hstep : ∀ x ∈ normalizedCoeffSpan,
        coordProduct (Function.update f b x) ∈ peterWeylFnSpan J := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        refine ih _ (fun c hc => ?_) (fun c hc => ?_)
        · have hcb : c ≠ b := fun hcb => hb (hcb ▸ hc)
          rw [Function.update_of_ne hcb]
          exact hin c (Finset.mem_insert_of_mem hc)
        · by_cases hcb : c = b
          · subst hcb
            rw [Function.update_self]
            exact hx
          · rw [Function.update_of_ne hcb]
            exact hout c (by simp [hcb, hc])
      | zero =>
        have hzero : coordProduct (Function.update f b 0) = 0 := by
          ext u
          rw [coordProduct_update_apply]
          simp
        rw [hzero]
        exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have hadd : coordProduct (Function.update f b (x + y)) =
            coordProduct (Function.update f b x) + coordProduct (Function.update f b y) := by
          ext u
          simp only [ContinuousMap.add_apply, coordProduct_update_apply]
          ring
        rw [hadd]
        exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        have hsmul : coordProduct (Function.update f b (a • x)) =
            a • coordProduct (Function.update f b x) := by
          ext u
          simp only [ContinuousMap.smul_apply, coordProduct_update_apply, smul_eq_mul]
          ring
        rw [hsmul]
        exact Submodule.smul_mem _ a hx
    have hfb := hstep (f b) (hin b (Finset.mem_insert_self _ _))
    rwa [Function.update_eq_self] at hfb
theorem coordProduct_mem {f : J → C(specialUnitary, ℂ)} (hf : ∀ b, f b ∈ coeffSpanAll) :
    coordProduct f ∈ peterWeylFnSpan J := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  exact coordProduct_mem_of_finset Finset.univ f
    (fun b _ => coeffSpanAll_le_normalizedCoeffSpan (hf b)) fun b hb => absurd (Finset.mem_univ b) hb
def evalCoord (b : J) : C(J → specialUnitary, specialUnitary) := ⟨fun u => u b, continuous_apply b⟩
theorem mul_comp_evalCoord_mem (h : HarmonicAnalysisFacts) {H : C(J → specialUnitary, ℂ)}
    (hH : H ∈ peterWeylFnSpan J) (b : J) {f : C(specialUnitary, ℂ)} (hf : f ∈ coeffSpanAll) :
    H * f.comp (evalCoord b) ∈ peterWeylFnSpan J := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, rfl⟩ := hx
    have hprod : peterWeylFn α * f.comp (evalCoord b) =
        coordProduct (Function.update (fun c => normalizedCoeff (α c)) b
          (normalizedCoeff (α b) * f)) := by
      ext u
      rw [coordProduct_update_apply]
      change (∏ᶠ c, normalizedCoeff (α c) (u c)) * f (u b) = _
      rw [finprod_eq_prod_of_fintype, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
      simp only [ContinuousMap.mul_apply]
      ring
    rw [hprod]
    refine coordProduct_mem fun c => ?_
    by_cases hc : c = b
    · subst hc
      rw [Function.update_self]
      exact mul_mem_coeffSpanAll h (normalizedCoeff_mem_coeffSpanAll _) hf
    · rw [Function.update_of_ne hc]
      exact normalizedCoeff_mem_coeffSpanAll _
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ a hx
omit [Finite J] in
theorem exists_entryEval_eq (h : HarmonicAnalysisFacts) (x : EntryVar J) :
    ∃ (b : J) (f : C(specialUnitary, ℂ)), f ∈ coeffSpanAll ∧
      ∀ u : J → specialUnitary, entryEval u x = f (u b) := by
  rcases x with ⟨b, i, j⟩ | ⟨b, i, j⟩
  · exact ⟨b, entryMap i j, entryMap_mem_coeffSpanAll h i j, fun _ => rfl⟩
  · exact ⟨b, star (entryMap i j),
      star_mem_coeffSpanAll h (entryMap_mem_coeffSpanAll h i j), fun _ => rfl⟩
theorem exists_mem_eval_eq (h : HarmonicAnalysisFacts)
    (p : MvPolynomial (EntryVar J) ℂ) :
    ∃ H ∈ peterWeylFnSpan J, ∀ u, MvPolynomial.eval (entryEval u) p = H u := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a • coordProduct fun _ => 1, Submodule.smul_mem _ a
      (coordProduct_mem fun _ => one_mem_coeffSpanAll h), fun u => ?_⟩
    change _ = a • ∏ᶠ b : J, (1 : C(specialUnitary, ℂ)) (u b)
    simp
  | add p q hp hq =>
    obtain ⟨H₁, hH₁, hev₁⟩ := hp
    obtain ⟨H₂, hH₂, hev₂⟩ := hq
    exact ⟨H₁ + H₂, Submodule.add_mem _ hH₁ hH₂, fun u => by simp [hev₁ u, hev₂ u]⟩
  | mul_X p x hp =>
    obtain ⟨H, hH, hev⟩ := hp
    obtain ⟨b, f, hf, hx⟩ := exists_entryEval_eq h x
    exact ⟨H * f.comp (evalCoord b), mul_comp_evalCoord_mem h hH b hf, fun u => by
      simp [hev u, hx u, evalCoord]⟩
theorem isEntryPolynomial_peterWeylFn (h : HarmonicAnalysisFacts) (α : PeterWeylIndex J) :
    IsEntryPolynomial (peterWeylFn α : (J → specialUnitary) → ℂ) := by
  let _ : Fintype J := Fintype.ofFinite J
  have hq : ∀ b, IsPolyInEntries (normalizedCoeff (α b)) := fun b =>
    (h (α b).spin (α b).spin).2.1.isPolyInEntries_of_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨((α b).rowIdx, (α b).colIdx), rfl⟩))
  choose q hq using hq
  refine ⟨∏ b, (MvPolynomial.rename (fun p : Fin 2 × Fin 2 => Sum.inl (b, p.1, p.2)) (q b) :
    MvPolynomial (EntryVar J) ℂ), fun u => ?_⟩
  change (∏ᶠ b, normalizedCoeff (α b) (u b)) = _
  rw [finprod_eq_prod_of_fintype, map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [hq b (u b), MvPolynomial.eval_rename]
  rfl
theorem isEntryPolynomial_of_mem (h : HarmonicAnalysisFacts) {H : C(J → specialUnitary, ℂ)}
    (hH : H ∈ peterWeylFnSpan J) : IsEntryPolynomial (H : (J → specialUnitary) → ℂ) := by
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, rfl⟩ := hx
    exact isEntryPolynomial_peterWeylFn h α
  | zero => exact ⟨0, fun u => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, fun u => by simp [hp u, hq u]⟩
  | smul a x _ hx =>
    obtain ⟨p, hp⟩ := hx
    exact ⟨MvPolynomial.C a * p, fun u => by simp [hp u]⟩
end SeveralVariables
theorem polynomialIffInPeterWeylSpan_holds (h : HarmonicAnalysisFacts) :
    PolynomialIffInPeterWeylSpan := by
  intro J _ _ F
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨H, hH, hev⟩ := exists_mem_eval_eq h p
    exact ⟨H, hH, fun u => (hp u).trans (hev u)⟩
  · rintro ⟨H, hH, hev⟩
    obtain ⟨p, hp⟩ := isEntryPolynomial_of_mem h hH
    exact ⟨p, fun u => (hev u).trans (hp u)⟩
end YangMills.Construction.SpinHarmonics.PeterWeylPolynomials
end
