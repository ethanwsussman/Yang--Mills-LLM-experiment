import YangMills.Construction.WindowOfTheParameters.CoefficientIsOneNumber
import YangMills.Construction.WindowOfTheParameters.TotalFlowIsOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensityFlow
open TorusLumps WeightedResponses SlopeCoefficient
private theorem sideFilter_neBot (L : ℕ) : (sideFilter L).NeBot := by
  unfold sideFilter
  infer_instance
private theorem hasNextCoupling_unique (hc : SlopeCoefficientUnique) {L : ℕ} {D : TorusFunctional} {y y' : ℝ}
    (hy : HasNextCoupling L D y) (hy' : HasNextCoupling L D y') : y = y' := by
  have := sideFilter_neBot L
  have h := hc (sideFilter L) (logRatio D) (-y) (-y') hy.2 hy'.2
  linarith
private theorem nextCoupling_eq (hc : SlopeCoefficientUnique) {L : ℕ} {D : TorusFunctional} {y y' : ℝ}
    (hy' : HasNextCoupling L D y') : nextCoupling L y D = y' := by
  have hex : ∃ z : ℝ, HasNextCoupling L D z := ⟨y', hy'⟩
  unfold nextCoupling
  rw [dif_pos hex]
  exact hasNextCoupling_unique hc hex.choose_spec hy'
private theorem chainFunctional_congr (ℓ : StepParameters) (β : ℝ) {x y : ℕ → ℝ} :
    ∀ j : ℕ, (∀ i < j, x i = y i) → chainFunctional ℓ β x j = chainFunctional ℓ β y j
  | 0, _ => rfl
  | j + 1, h => by
    have hj := chainFunctional_congr ℓ β j fun i hi => h i (Nat.lt_succ_of_lt hi)
    simp only [chainFunctional]
    rw [hj, h j (Nat.lt_succ_self j)]
private theorem eq_flowData_of_isFlowUpTo (hc : SlopeCoefficientUnique) {ℓ : StepParameters} {β : ℝ} {t : ℕ}
    {x : ℕ → ℝ} (hx : IsFlowUpTo ℓ β t x) :
    ∀ j : ℕ, j ≤ t → x j = coupling ℓ β j ∧ chainFunctional ℓ β x j = (flowData ℓ β j).2
  | 0, _ => ⟨hx.init, rfl⟩
  | j + 1, hj => by
    obtain ⟨h₁, h₂⟩ := eq_flowData_of_isFlowUpTo hc hx j (Nat.le_of_succ_le hj)
    have hlt : j < t := hj
    have harr : chainFunctional ℓ β x (j + 1) = (flowData ℓ β (j + 1)).2 := by
      simp only [chainFunctional, flowData]
      rw [h₂, h₁]
      rfl
    refine ⟨?_, harr⟩
    have hread := hx.succ j hlt
    rw [harr] at hread
    exact (nextCoupling_eq hc hread).symm
theorem flowIsUnique (hc : SlopeCoefficientUnique) : FlowIsUnique := by
  intro ℓ β t x _ hx
  have hag := eq_flowData_of_isFlowUpTo hc hx
  refine ⟨⟨rfl, fun j hj => ?_, fun j hj => ?_⟩, fun j hj => (hag j hj).1⟩
  · rw [← (hag j hj.le).1]
    exact hx.pos j hj
  · have hcongr : chainFunctional ℓ β (coupling ℓ β) (j + 1) = chainFunctional ℓ β x (j + 1) :=
      chainFunctional_congr ℓ β (j + 1) fun i hi => ((hag i (by omega)).1).symm
    rw [hcongr, ← (hag (j + 1) hj).1]
    exact hx.succ j hj
end YangMills.Construction.TotalDensityFlow
end
