import YangMills.Construction.Matrices.FactsOnFunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.Matrices.ProjectionsOntoSpacesOfSeveralVariablesProof
import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjections
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics.IsotypicPartSums
open SeveralVariables
variable {J : Type} [Finite J]
theorem toHaarL2_continuousMap (H : C(J → specialUnitary, ℂ)) :
    toHaarL2 (H : (J → specialUnitary) → ℂ) = ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ H := by
  have hae := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarPi J) H
  have hm : MemLp (H : (J → specialUnitary) → ℂ) 2 (haarPi J) :=
    (memLp_congr_ae hae).1 (Lp.memLp _)
  unfold toHaarL2
  rw [dif_pos hm]
  exact Lp.ext ((hm.coeFn_toLp).trans hae.symm)
theorem inner_peterWeylVec_ae (a : PeterWeylIndex J) (F : HaarL2 J) :
    (fun u => (inner ℂ (peterWeylVec a u) (F u) : ℂ)) =ᵐ[haarPi J]
      fun u => star (peterWeylFn a u) * F u := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarPi J) (peterWeylFn a)]
    with u hu
  have hu' : peterWeylVec a u = peterWeylFn a u := hu
  rw [hu', RCLike.inner_apply]
  simp [mul_comm]
theorem integrable_star_peterWeylFn_mul (a : PeterWeylIndex J) (F : HaarL2 J) :
    Integrable (fun u => star (peterWeylFn a u) * F u) (haarPi J) :=
  (L2.integrable_inner (𝕜 := ℂ) (peterWeylVec a) F).congr (inner_peterWeylVec_ae a F)
theorem inner_peterWeylVec_eq_integral (a : PeterWeylIndex J) (F : HaarL2 J) :
    (inner ℂ (peterWeylVec a) F : ℂ) =
      ∫ u, star (peterWeylFn a u) * F u ∂haarPi J := by apply _root_.YangMills.Construction.SpinHarmonics.ProjectionFormulas.inner_peterWeylVec <;> assumption
theorem isotypicPartSum_apply (s : J → HalfNatural) (F : HaarL2 J) (u : J → specialUnitary) :
    isotypicPartSum s F u = ∑ a ∈ indicesWithSpins s,
      (inner ℂ (peterWeylVec a) F : ℂ) * peterWeylFn a u := by
  simp [isotypicPartSum, ContinuousMap.sum_apply]
theorem isotypicPart_eq_isotypicPartSum {s : J → HalfNatural}
    (hK : ∀ u v : J → specialUnitary, isotypicKernel s u v =
      ∑ a ∈ indicesWithSpins s, peterWeylFn a u * star (peterWeylFn a v))
    (F : HaarL2 J) (u : J → specialUnitary) :
    isotypicPart s F u = isotypicPartSum s F u := by
  rw [isotypicPartSum_apply]
  simp only [isotypicPart, Schatten.kernelApply, hK, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_peterWeylVec_eq_integral, mul_comm, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun v => by simp [mul_assoc])
  · intro a _
    exact ((integrable_star_peterWeylFn_mul a F).const_mul (peterWeylFn a u)).congr
      (Filter.Eventually.of_forall fun v => by simp [mul_assoc])
theorem toLp_isotypicPartSum (s : J → HalfNatural) (F : HaarL2 J) :
    ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ (isotypicPartSum s F) =
      ∑ a ∈ indicesWithSpins s,
        (inner ℂ (peterWeylVec a) F : ℂ) • peterWeylVec a := by
  simp only [isotypicPartSum, map_sum, map_smul]
  rfl
theorem isotypicProj_hasKernel {s : J → HalfNatural}
    (hK : ∀ u v : J → specialUnitary, isotypicKernel s u v =
      ∑ a ∈ indicesWithSpins s, peterWeylFn a u * star (peterWeylFn a v)) :
    Schatten.HasKernel (haarPi J) (fun p => isotypicKernel s p.1 p.2)
      (isotypicProj s) := by
  refine Classical.epsilon_spec (p := Schatten.HasKernel (haarPi J)
    (fun p : (J → specialUnitary) × (J → specialUnitary) => isotypicKernel s p.1 p.2))
    ⟨∑ a ∈ indicesWithSpins s,
      (innerSL ℂ (peterWeylVec a)).smulRight (peterWeylVec a), fun F => ?_⟩
  have hT : (∑ a ∈ indicesWithSpins s,
      (innerSL ℂ (peterWeylVec a)).smulRight (peterWeylVec a) :
        HaarL2 J →L[ℂ] HaarL2 J) F =
      ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ (isotypicPartSum s F) := by
    rw [toLp_isotypicPartSum]
    simp
  rw [hT]
  refine (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarPi J) _).trans
    (Filter.Eventually.of_forall fun u => ?_)
  exact (isotypicPart_eq_isotypicPartSum hK F u).symm
theorem isotypicPartSum_add (s : J → HalfNatural) (F H : HaarL2 J) :
    isotypicPartSum s (F + H) = isotypicPartSum s F + isotypicPartSum s H := by
  simp [isotypicPartSum, inner_add_right, add_smul, Finset.sum_add_distrib]
theorem isotypicPartSum_smul (s : J → HalfNatural) (c : ℂ) (F : HaarL2 J) :
    isotypicPartSum s (c • F) = c • isotypicPartSum s F := by
  simp [isotypicPartSum, inner_smul_right, mul_smul, Finset.smul_sum]
theorem isotypicPartSum_zero (s : J → HalfNatural) :
    isotypicPartSum s (0 : HaarL2 J) = 0 := by
  simp [isotypicPartSum]
open Classical in
theorem isotypicPartSum_of_mem_prodCoeffSpan {s : J → HalfNatural}
    (hon : Orthonormal ℂ (peterWeylVec : PeterWeylIndex J → HaarL2 J))
    (hspan : Submodule.span ℂ (peterWeylFn '' {a : PeterWeylIndex J | spins a = s}) =
      prodCoeffSpan s)
    {ψ : C(J → specialUnitary, ℂ)} (hψ : ψ ∈ prodCoeffSpan s) (t : J → HalfNatural) :
    isotypicPartSum t (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ ψ) =
      if t = s then ψ else 0 := by
  rw [← hspan] at hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : spins b = s := hb
    have hc : ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ (peterWeylFn b) =
      peterWeylVec b := rfl
    rw [hc]
    simp only [isotypicPartSum, orthonormal_iff_ite.1 hon, ite_smul, one_smul, zero_smul]
    split_ifs with h
    · rw [Finset.sum_ite_eq']
      rw [if_pos]
      simp [indicesWithSpins, h, hb']
    · refine Finset.sum_eq_zero fun a ha => if_neg fun hab => h ?_
      have ha' : spins a = t := by simpa [indicesWithSpins] using ha
      rw [← ha', hab, hb']
  | zero =>
    rw [map_zero, isotypicPartSum_zero]
    simp
  | add x y _ _ hx hy =>
    rw [map_add, isotypicPartSum_add, hx, hy]
    split_ifs <;> simp
  | smul c x _ hx =>
    rw [map_smul, isotypicPartSum_smul, hx]
    split_ifs <;> simp
theorem statement_holds (h : SeveralVariables.SeveralVariablesFacts) :
    IsotypicPartSums.Statement := by
  intro J _ _
  have hB : ∀ s : J → HalfNatural, OrthonormalBasisAndProjections s ⟨0⟩ := fun s => (h J s ⟨0⟩).1
  refine ⟨fun s F => ?_, fun s H u => ?_, fun s t ψ hψ => ?_⟩
  · obtain ⟨_, _, hspan, hK, _⟩ := hB s
    refine ⟨?_, funext fun u => (isotypicPart_eq_isotypicPartSum hK F u).symm, ?_⟩
    · rw [← hspan]
      refine Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨a, by simpa [indicesWithSpins] using ha, rfl⟩
    · rw [toHaarL2_continuousMap]
      refine Lp.ext ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarPi J) _).trans ?_)
      refine Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun u => ?_)
        (isotypicProj_hasKernel hK F).symm
      exact (isotypicPart_eq_isotypicPartSum hK F u).symm
  · obtain ⟨_, _, _, hK, _⟩ := hB s
    rw [← isotypicPart_eq_isotypicPartSum hK]
    refine integral_congr_ae ?_
    rw [toHaarL2_continuousMap]
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarPi J) H] with v hv
    simp only [hv]
  · obtain ⟨hon, _, hspan, _⟩ := hB s
    rw [toHaarL2_continuousMap]
    refine ⟨?_, fun hne => ?_⟩
    · simpa using isotypicPartSum_of_mem_prodCoeffSpan hon hspan hψ s
    · simpa [hne] using isotypicPartSum_of_mem_prodCoeffSpan hon hspan hψ t
end YangMills.Construction.SpinHarmonics.IsotypicPartSums
end
