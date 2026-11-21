import YangMills.Construction.ClusterExpansionOfAStep.GeometryOfFreeBonds
import YangMills.Construction.ClusterExpansionOfAStep.SharesAreACurvatureFamily
import YangMills.Construction.ResponseInTheExpansion.RemaindersOfAResponseAreCarried
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts ShareFamilies FreeBonds WeightedResponses
namespace RemaindersInvariant
variable {n : ℕ} [NeZero n]
theorem sum_mapSite (g : TorusIsometry) (G : TorusSite n → ℝ) : ∑ y, G (g.mapSite y) = ∑ y, G y := by
  have hb : Function.Bijective (g.mapSite (n := n)) :=
    Finite.injective_iff_bijective.mp (mapSite_injective g)
  exact Function.Bijective.sum_comp hb G
theorem levelShares_transport (hS : LevelSharesFormCurvatureFamily) {T : ParameterAssignment} (hT : T.Admissible)
    {y : ℝ} (hy : T.floorMin ≤ y) (t : ℕ) (hn : T.n₀ ≤ n) {g : TorusIsometry} {W W' : TorusField n}
    (hW : IsCold T.threshold W) (hW' : IsCold T.threshold W') (hc : g.Transports W W') :
    ∑ z, levelShare T.coupling T.side t Finset.univ z W' = ∑ z, levelShare T.coupling T.side t Finset.univ z W ∧
      actionAtLevel T.coupling T.side t Finset.univ W' = actionAtLevel T.coupling T.side t Finset.univ W := by
  cases t with
  | zero =>
    have e : actionAtLevel T.coupling T.side 0 Finset.univ W' = actionAtLevel T.coupling T.side 0 Finset.univ W :=
      wilsonAction_of_transports hc
    rw [sum_levelShare_zero, sum_levelShare_zero]
    exact ⟨e, e⟩
  | succ t =>
    obtain ⟨-, h₂, h₃⟩ := hS T hT y hy t
    have a := h₂ n hn g W W' hW hW' hc
    have ne : n ≠ 0 := NeZero.ne n
    have b₁ := h₃ n hn W hW
    have b₂ := h₃ n hn W' hW'
    refine ⟨?_, by rw [← b₁, ← b₂, a]⟩
    simp only [centered, levelShareFamily, dif_neg ne, Finset.sum_sub_distrib] at a
    linarith
end RemaindersInvariant
open RemaindersInvariant in
theorem remaindersInvariantUnderIsometries_proof (hS : LevelSharesFormCurvatureFamily) :
    remaindersInvariantUnderIsometries := by
  intro T hT y hy R A hR hA
  have hℓ := hR.params_eq
  have ha : R.params.coupling = T.coupling := by rw [hℓ]; rfl
  have hL : R.params.side = T.side := by rw [hℓ]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [hℓ]; rfl
  have hn₀ : R.params.n₀ = T.n₀ := by rw [hℓ]; rfl
  have row := hA.bounds
  have hP : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (g : TorusIsometry) (W W' : TorusField n),
      IsCold R.params.threshold W → g.Transports W W' →
      ∑ z, centeredResponse A.cold n z W' (constOneWeight _) = ∑ z, centeredResponse A.cold n z W (constOneWeight _) := by
    intro n _ hn g W W' hW hc
    simp only [centeredResponse, Finset.sum_sub_distrib]
    congr 1
    rw [← sum_mapSite g fun z => A.cold n z W' (constOneWeight _)]
    exact Finset.sum_congr rfl fun z _ => row.cold_carried n hn g z W W' hW hc
  refine ⟨?_, ?_⟩
  · intro n _ hn g W W' hW hW' hc
    have c₀ := levelShares_transport hS hT hy R.depth (hn₀ ▸ hn) (hσ ▸ hW) (hσ ▸ hW') hc
    rw [← ha, ← hL] at c₀
    have e₁ := row.share_total n hn W hW
    have e₂ := row.share_total n hn W' hW'
    have e₃ := hP n hn g W W' hW hc
    rw [c₀.2] at e₂
    linarith
  · intro n _ hn g W W' hW hW' hc
    have c₀ := levelShares_transport hS hT hy R.depth (hn₀ ▸ hn) (hσ ▸ hW) (hσ ▸ hW') hc
    rw [← ha, ← hL] at c₀
    have e₁ : ∑ z, centeredResponse A.cold n z W (constOneWeight _) =
        A.coeff * ∑ z, levelShare R.params.coupling R.params.side R.depth Finset.univ z W +
          ∑ z, centered A.siteRemainder n z W := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => row.share_site n hn z W hW
    have e₂ : ∑ z, centeredResponse A.cold n z W' (constOneWeight _) =
        A.coeff * ∑ z, levelShare R.params.coupling R.params.side R.depth Finset.univ z W' +
          ∑ z, centered A.siteRemainder n z W' := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => row.share_site n hn z W' hW'
    have e₃ := hP n hn g W W' hW hc
    rw [c₀.1] at e₂
    linarith
end YangMills.Construction.ResponseInTheExpansion
end
