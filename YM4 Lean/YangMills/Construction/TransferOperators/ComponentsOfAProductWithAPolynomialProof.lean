import YangMills.Construction.Matrices.MultiplicationByAPolynomialOnPowersOfGForm
import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjectionsProof
import YangMills.Construction.TransferOperators.ComponentsOfAProductWithAPolynomial
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Matrices.ComplexMatrix2
namespace SpinHarmonics.MulPullbackComponents
open SeveralVariables
section Linear
variable {J : Type} [Finite J]
theorem toHaarL2_continuousMap (H : C(J → specialUnitary, ℂ)) :
    toHaarL2 (H : (J → specialUnitary) → ℂ) = ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ H := by apply _root_.YangMills.Construction.SpinHarmonics.IsotypicPartSums.toHaarL2_continuousMap <;> assumption
theorem isotypicPartSum_add (l : J → HalfNatural) (F G : HaarL2 J) :
    isotypicPartSum l (F + G) = isotypicPartSum l F + isotypicPartSum l G := by
  simp only [isotypicPartSum, inner_add_right, add_smul, Finset.sum_add_distrib]
theorem isotypicPartSum_smul (l : J → HalfNatural) (c : ℂ) (F : HaarL2 J) :
    isotypicPartSum l (c • F) = c • isotypicPartSum l F := by
  simp only [isotypicPartSum, inner_smul_right, Finset.smul_sum, mul_smul]
def isotypicPartMap (l : J → HalfNatural) :
    C(J → specialUnitary, ℂ) →ₗ[ℂ] C(J → specialUnitary, ℂ) where
  toFun H := isotypicPartSum l (toHaarL2 (H : (J → specialUnitary) → ℂ))
  map_add' H H' := by
    simp only [toHaarL2_continuousMap, map_add, isotypicPartSum_add]
  map_smul' c H := by
    simp only [toHaarL2_continuousMap, map_smul, isotypicPartSum_smul, RingHom.id_apply]
theorem isotypicPartMap_apply (l : J → HalfNatural) (H : C(J → specialUnitary, ℂ)) :
    isotypicPartMap l H = isotypicPartSum l (toHaarL2 (H : (J → specialUnitary) → ℂ)) := rfl
theorem nearbySpins_finite (B : Set J) (D : ↥B → ℕ) (lam : J → HalfNatural) :
    {l' : J → HalfNatural | (∀ b : ↥B, |(l' b).toReal - (lam b).toReal| ≤ (D b : ℝ) / 2) ∧
      ∀ b, b ∉ B → l' b = lam b}.Finite := by
  have hfin : ∀ b : J, {h : HalfNatural | (∀ hb : b ∈ B,
      |h.toReal - (lam b).toReal| ≤ (D ⟨b, hb⟩ : ℝ) / 2) ∧ (b ∉ B → h = lam b)}.Finite := by
    intro b
    by_cases hb : b ∈ B
    · have hinj : Set.InjOn HalfNatural.doubled
          (HalfNatural.doubled ⁻¹' Set.Iic ((lam b).doubled + D ⟨b, hb⟩)) := by
        rintro ⟨x⟩ - ⟨y⟩ - h
        cases h
        rfl
      refine ((Set.finite_Iic ((lam b).doubled + D ⟨b, hb⟩)).preimage hinj).subset fun h hh => ?_
      have hup := (abs_le.mp (hh.1 hb)).2
      unfold HalfNatural.toReal at hup
      have hreal : (h.doubled : ℝ) ≤ (lam b).doubled + D ⟨b, hb⟩ := by linarith
      exact show h.doubled ≤ (lam b).doubled + D ⟨b, hb⟩ from by exact_mod_cast hreal
    · exact (Set.finite_singleton (lam b)).subset fun h hh => hh.2 hb
  exact (Set.Finite.pi' hfin).subset fun l' hl' b => ⟨fun hb => hl'.1 ⟨b, hb⟩, hl'.2 b⟩
end Linear
theorem statement_holds (hparts : SpinHarmonics.IsotypicPartSums.Statement)
    (hmul : SpinHarmonics.AllPolyMulShiftSpins) : SpinHarmonics.MulPullbackComponents.Statement := by
  intro J _ _ B f hf D lam ψ hB hdeg hψ
  classical
  obtain ⟨H, hH, hgH⟩ := (hmul J lam).1 B hB D f hdeg ψ hψ
  have hg : mulPullback B f hf ψ = H := ContinuousMap.ext fun u => hgH u
  rw [hg]
  have hc := (hparts J).2.2
  have hN := nearbySpins_finite B D lam
  have hker : ∀ l' : J → HalfNatural, l' ∉ {l' : J → HalfNatural |
      (∀ b : ↥B, |(l' b).toReal - (lam b).toReal| ≤ (D b : ℝ) / 2) ∧
        ∀ b, b ∉ B → l' b = lam b} →
      nearbySpinSpan B D lam ≤ LinearMap.ker (isotypicPartMap l') := by
    intro l' hl'
    refine iSup₂_le fun l₁ hl₁ φ hφ => LinearMap.mem_ker.2 ((hc l₁ l' φ hφ).2 ?_)
    rintro rfl
    exact hl' hl₁
  have hsum : nearbySpinSpan B D lam ≤
      LinearMap.eqLocus LinearMap.id (∑ l' ∈ hN.toFinset, isotypicPartMap l') := by
    refine iSup₂_le fun l₁ hl₁ φ hφ => ?_
    rw [LinearMap.mem_eqLocus, LinearMap.sum_apply, Finset.sum_eq_single l₁]
    · exact ((hc l₁ l₁ φ hφ).1).symm
    · intro l' _ hne
      exact (hc l₁ l' φ hφ).2 hne
    · intro h
      exact absurd (hN.mem_toFinset.2 hl₁) h
  have hsupport : ∀ l' : J → HalfNatural,
      isotypicPartSum l' (toHaarL2 (H : (J → specialUnitary) → ℂ)) ≠ 0 →
      (∀ b : ↥B, |(l' b).toReal - (lam b).toReal| ≤ (D b : ℝ) / 2) ∧
        ∀ b, b ∉ B → l' b = lam b := by
    intro l' hl'
    by_contra h
    exact hl' (LinearMap.mem_ker.1 (hker l' h hH))
  refine ⟨hN.subset fun l' hl' => hsupport l' hl', fun l' hl' => ?_, fun u => ?_⟩
  · exact ⟨(hsupport l' hl').2, fun b => (hsupport l' hl').1 b⟩
  · rw [tsum_eq_sum (s := hN.toFinset) fun l' hl' => ?_]
    · have h := LinearMap.mem_eqLocus.1 (hsum hH)
      rw [LinearMap.sum_apply] at h
      have hu := congrArg (fun G : C(J → specialUnitary, ℂ) => G u) h
      simpa [isotypicPartMap_apply, ContinuousMap.sum_apply] using hu
    · have h0 : isotypicPartSum l' (toHaarL2 (H : (J → specialUnitary) → ℂ)) = 0 := by
        by_contra h
        exact hl' (hN.mem_toFinset.2 (hsupport l' h))
      rw [h0]
      rfl
end SpinHarmonics.MulPullbackComponents
end YangMills.Construction
end
