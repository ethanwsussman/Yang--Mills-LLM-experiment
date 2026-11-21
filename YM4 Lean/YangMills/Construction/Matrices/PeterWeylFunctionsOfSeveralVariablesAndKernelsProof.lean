import YangMills.Construction.Matrices.OrthogonalityRelationsAndPeterWeylOnGProof
import YangMills.Construction.Matrices.PeterWeylFunctionsOfSeveralVariablesAndKernelsForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics.SeveralVariablesProof
open SeveralVariables Matrices Matrices.ComplexMatrix2 HilbertSpaceBasics
theorem label_ext {e e' : PeterWeylLabel} (hs : e.spin = e'.spin)
    (hr : (e.rowIdx : ℕ) = e'.rowIdx) (hc : (e.colIdx : ℕ) = e'.colIdx) : e = e' := by
  obtain ⟨l, a, c⟩ := e
  obtain ⟨l', a', c'⟩ := e'
  simp only at hs hr hc
  subst hs
  have h₁ : a = a' := Fin.ext hr
  have h₂ : c = c' := Fin.ext hc
  subst h₁ h₂
  rfl
theorem normalizedCoeff_apply (e : PeterWeylLabel) (g : specialUnitary) :
    normalizedCoeff e g =
      ((Real.sqrt (2 * e.spin.toReal + 1) : ℝ) : ℂ) * spinCoeff e.spin e.rowIdx e.colIdx g :=
  rfl
theorem two_mul_toReal_add_one_pos (l : HalfNatural) : 0 < 2 * l.toReal + 1 := by apply _root_.YangMills.Construction.SpinHarmonics.PeterWeylOrthogonality.two_mul_toReal_add_one_pos <;> assumption
theorem integral_star_normalizedCoeff_mul (facts : HarmonicAnalysisFacts) (e e' : PeterWeylLabel)
    [Decidable (e = e')] :
    ∫ g, star (normalizedCoeff e g) * normalizedCoeff e' g ∂haarProb = if e = e' then 1 else 0 := by
  classical
  have h := (facts e.spin e'.spin).2.1.integral_star_spinCoeff_mul e.rowIdx e.colIdx e'.rowIdx e'.colIdx
  have hform : (fun g : specialUnitary => star (normalizedCoeff e g) * normalizedCoeff e' g) =
      fun g => (((Real.sqrt (2 * e.spin.toReal + 1) : ℝ) : ℂ) *
          ((Real.sqrt (2 * e'.spin.toReal + 1) : ℝ) : ℂ)) *
        (star (spinCoeff e.spin e.rowIdx e.colIdx g) *
          spinCoeff e'.spin e'.rowIdx e'.colIdx g) := by
    funext g
    simp only [normalizedCoeff_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  rw [hform, integral_const_mul, h]
  by_cases hee : e = e'
  · subst hee
    have hpos := two_mul_toReal_add_one_pos e.spin
    have hne : ((2 * e.spin.toReal + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    have hsq : ((Real.sqrt (2 * e.spin.toReal + 1) : ℝ) : ℂ) *
        ((Real.sqrt (2 * e.spin.toReal + 1) : ℝ) : ℂ) = ((2 * e.spin.toReal + 1 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
    rw [hsq]
    rw [if_pos ⟨rfl, rfl, rfl⟩, if_pos rfl]
    field_simp
  · have hnot : ¬(e.spin = e'.spin ∧ (e.rowIdx : ℕ) = e'.rowIdx ∧ (e.colIdx : ℕ) = e'.colIdx) :=
      fun hh => hee (label_ext hh.1 hh.2.1 hh.2.2)
    simp [hnot, hee]
variable {J : Type} [Finite J]
theorem peterWeylFn_apply [Fintype J] (α : PeterWeylIndex J) (u : J → specialUnitary) :
    peterWeylFn α u = ∏ b, normalizedCoeff (α b) (u b) := by
  change (∏ᶠ b, normalizedCoeff (α b) (u b)) = _
  rw [finprod_eq_prod_of_fintype]
theorem inner_peterWeylVec (facts : HarmonicAnalysisFacts)
    (α β : PeterWeylIndex J) [Decidable (α = β)] :
    (inner ℂ (peterWeylVec α) (peterWeylVec β) : ℂ) = if α = β then 1 else 0 := by
  classical
  cases nonempty_fintype J
  have hpi : haarPi J = Measure.pi fun _ : J => haarProb := Measure.infinitePi_eq_pi _
  rw [peterWeylVec, peterWeylVec, ContinuousMap.inner_toLp, hpi]
  have hform : (fun u : J → specialUnitary =>
      peterWeylFn β u * (starRingEnd ℂ) (peterWeylFn α u)) =
      fun u => ∏ b, (fun (b : J) (g : specialUnitary) => star (normalizedCoeff (α b) g) *
        normalizedCoeff (β b) g) b (u b) := by
    funext u
    rw [peterWeylFn_apply, peterWeylFn_apply, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => mul_comm _ _
  rw [hform, integral_fintype_prod_eq_prod (𝕜 := ℂ) (E := fun _ : J => specialUnitary)
    (fun (b : J) (g : specialUnitary) => star (normalizedCoeff (α b) g) * normalizedCoeff (β b) g)
    (μ := fun _ : J => haarProb)]
  simp only [integral_star_normalizedCoeff_mul facts]
  by_cases hαβ : α = β
  · subst hαβ
    simp
  · obtain ⟨b, hb⟩ := Function.ne_iff.1 hαβ
    rw [if_neg hαβ]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb)
theorem orthonormal_peterWeylVec (facts : HarmonicAnalysisFacts) :
    Orthonormal ℂ (peterWeylVec : PeterWeylIndex J → HaarL2 J) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  exact inner_peterWeylVec facts α β
theorem linearIndependent_peterWeylFn (facts : HarmonicAnalysisFacts)
    (l : J → HalfNatural) :
    LinearIndependent ℂ (fun α : {α : PeterWeylIndex J // spins α = l} => peterWeylFn α.1) := by
  have h := (orthonormal_peterWeylVec (J := J) facts).linearIndependent.comp
    (Subtype.val : {α : PeterWeylIndex J // spins α = l} → PeterWeylIndex J) Subtype.val_injective
  exact LinearIndependent.of_comp
    (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ).toLinearMap h
def indexOfPairs (l : J → HalfNatural)
    (x : ∀ b, Fin ((l b).doubled + 1) × Fin ((l b).doubled + 1)) : PeterWeylIndex J :=
  fun b => ⟨l b, (x b).1, (x b).2⟩
omit [Finite J] in
theorem spins_indexOfPairs (l : J → HalfNatural)
    (x : ∀ b, Fin ((l b).doubled + 1) × Fin ((l b).doubled + 1)) : spins (indexOfPairs l x) = l :=
  rfl
theorem normalizedCoeff_mem (e : PeterWeylLabel) : normalizedCoeff e ∈ coeffSpan e.spin :=
  Submodule.smul_mem _ _ (Submodule.subset_span ⟨(e.rowIdx, e.colIdx), rfl⟩)
theorem exists_eq_sum_normalizedCoeff (l : HalfNatural) (ψ : C(specialUnitary, ℂ))
    (hψ : ψ ∈ coeffSpan l) :
    ∃ c : Fin (l.doubled + 1) × Fin (l.doubled + 1) → ℂ,
      ψ = ∑ p, c p • normalizedCoeff ⟨l, p.1, p.2⟩ := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hψ
  have hpos := two_mul_toReal_add_one_pos l
  have hne : ((Real.sqrt (2 * l.toReal + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  refine ⟨fun p => c p * ((Real.sqrt (2 * l.toReal + 1) : ℝ) : ℂ)⁻¹, ?_⟩
  rw [← hc]
  refine Finset.sum_congr rfl fun p _ => ?_
  change c p • spinCoeffMap l p.1 p.2 = _ • (((Real.sqrt (2 * l.toReal + 1) : ℝ) : ℂ) •
    spinCoeffMap l p.1 p.2)
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hne, mul_one]
theorem coordProduct_mem_span (l : J → HalfNatural) (ψ : J → C(specialUnitary, ℂ))
    (hψ : ∀ b, ψ b ∈ coeffSpan (l b)) :
    coordProduct ψ ∈ Submodule.span ℂ (peterWeylFn '' {α : PeterWeylIndex J | spins α = l}) := by
  classical
  cases nonempty_fintype J
  choose c hc using fun b => exists_eq_sum_normalizedCoeff (l b) (ψ b) (hψ b)
  have key : coordProduct ψ =
      ∑ x ∈ Fintype.piFinset fun b =>
          (Finset.univ : Finset (Fin ((l b).doubled + 1) × Fin ((l b).doubled + 1))),
        (∏ b, c b (x b)) • peterWeylFn (indexOfPairs l x) := by
    ext u
    change (∏ᶠ b, ψ b (u b)) = _
    rw [finprod_eq_prod_of_fintype, ContinuousMap.coe_sum, Finset.sum_apply]
    have hfactor : ∀ b, ψ b (u b) = ∑ p, c b p * normalizedCoeff ⟨l b, p.1, p.2⟩ (u b) := by
      intro b
      conv_lhs => rw [hc b]
      rw [ContinuousMap.coe_sum, Finset.sum_apply]
      rfl
    simp only [hfactor]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ContinuousMap.smul_apply, peterWeylFn_apply, smul_eq_mul, Finset.prod_mul_distrib]
    rfl
  rw [key]
  exact Submodule.sum_mem _ fun x _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨indexOfPairs l x, spins_indexOfPairs l x, rfl⟩)
theorem span_peterWeylFn (l : J → HalfNatural) :
    Submodule.span ℂ (peterWeylFn '' {α : PeterWeylIndex J | spins α = l}) =
      prodCoeffSpan l := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨α, hα, rfl⟩
    refine Submodule.subset_span ⟨fun b => normalizedCoeff (α b), fun b => ?_, rfl⟩
    have hb : l b = (α b).spin := (congrFun hα b).symm
    rw [hb]
    exact normalizedCoeff_mem (α b)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨ψ, hψ, rfl⟩
    exact coordProduct_mem_span l ψ hψ
theorem kernelFactor_eq_sum (facts : HarmonicAnalysisFacts) (l : HalfNatural)
    (g g' : specialUnitary) :
    ((2 * l.toReal + 1 : ℝ) : ℂ) * spinCharacter l (g * g'⁻¹) =
      ∑ p : Fin (l.doubled + 1) × Fin (l.doubled + 1),
        normalizedCoeff ⟨l, p.1, p.2⟩ g * star (normalizedCoeff ⟨l, p.1, p.2⟩ g') := by
  rw [(facts l l).2.2.2.2.1.kernel_eq_sum g g', Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hpos := two_mul_toReal_add_one_pos l
  have hsq : ((Real.sqrt (2 * l.toReal + 1) : ℝ) : ℂ) * ((Real.sqrt (2 * l.toReal + 1) : ℝ) : ℂ) =
      ((2 * l.toReal + 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
  simp only [normalizedCoeff_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
  rw [← hsq]
  ring
theorem mem_indicesWithSpins {l : J → HalfNatural} {α : PeterWeylIndex J} :
    α ∈ indicesWithSpins l ↔ spins α = l :=
  Set.Finite.mem_toFinset _
theorem isotypicKernel_eq_sum (facts : HarmonicAnalysisFacts) (l : J → HalfNatural)
    (u u' : J → specialUnitary) :
    isotypicKernel l u u' =
      ∑ α ∈ indicesWithSpins l, peterWeylFn α u * star (peterWeylFn α u') := by
  classical
  cases nonempty_fintype J
  rw [isotypicKernel, finprod_eq_prod_of_fintype]
  simp only [kernelFactor_eq_sum facts]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_nbij (indexOfPairs l) ?_ ?_ ?_ ?_
  · intro x _
    exact mem_indicesWithSpins.2 (spins_indexOfPairs l x)
  · intro x _ y _ hxy
    funext b
    have hb := congrFun hxy b
    simp only [indexOfPairs, PeterWeylLabel.mk.injEq, heq_eq_eq, true_and] at hb
    exact Prod.ext hb.1 hb.2
  · intro α hα
    have hs : spins α = l := mem_indicesWithSpins.1 hα
    subst hs
    exact ⟨fun b => ((α b).rowIdx, (α b).colIdx), by simp, rfl⟩
  · intro x _
    rw [peterWeylFn_apply, peterWeylFn_apply, star_prod, ← Finset.prod_mul_distrib]
    rfl
theorem isotypicKernel_im (facts : HarmonicAnalysisFacts) (l : J → HalfNatural)
    (u u' : J → specialUnitary) : (isotypicKernel l u u').im = 0 := by
  classical
  cases nonempty_fintype J
  have hreal : ∀ b, ∃ r : ℝ,
      ((2 * (l b).toReal + 1 : ℝ) : ℂ) * spinCharacter (l b) (u b * (u' b)⁻¹) = (r : ℂ) := by
    intro b
    have him := (facts (l b) (l b)).2.2.1.im_eq_zero (u b * (u' b)⁻¹)
    refine ⟨(2 * (l b).toReal + 1) * (spinCharacter (l b) (u b * (u' b)⁻¹)).re, ?_⟩
    rw [Complex.ofReal_mul]
    congr 1
    exact Complex.ext rfl (by simpa using him)
  choose r hr using hreal
  rw [isotypicKernel, finprod_eq_prod_of_fintype]
  simp only [hr]
  rw [← Complex.ofReal_prod, Complex.ofReal_im]
omit [Finite J] in
theorem isotypicKernel_symm (facts : HarmonicAnalysisFacts) (l : J → HalfNatural)
    (u u' : J → specialUnitary) : isotypicKernel l u u' = isotypicKernel l u' u := by
  refine finprod_congr fun b => ?_
  have h := (facts (l b) (l b)).2.2.1.apply_inv (u b * (u' b)⁻¹)
  rw [mul_inv_rev, inv_inv] at h
  rw [h]
theorem peterWeylOrthonormalAndKernel_holds (facts : HarmonicAnalysisFacts) :
    PeterWeylOrthonormalAndKernel := by
  intro J _ _ l
  exact ⟨orthonormal_peterWeylVec facts, linearIndependent_peterWeylFn facts l,
    span_peterWeylFn l, isotypicKernel_eq_sum facts l,
    fun u u' => ⟨isotypicKernel_im facts l u u', isotypicKernel_symm facts l u u'⟩⟩
end YangMills.Construction.SpinHarmonics.SeveralVariablesProof
end
