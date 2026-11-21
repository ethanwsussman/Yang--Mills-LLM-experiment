import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
open TorusLumps StepReturn ClusterExpansionOfAStep WeightedResponses
private theorem expansion_step_of_returns {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
theorem expansionAlongFlow_holds : expansionAlongFlow := by
  intro ℓ hS β t hr
  have key : ∀ u : ℕ, u ≤ t → HasExpansion ℓ u (flowCoupling ℓ β u) (flowFunctional ℓ β u) := by
    intro u
    induction u with
    | zero => exact fun _ => hS.wilson_expansion β (hr 0 (Nat.zero_le _))
    | succ u ih =>
      intro hu
      exact (expansion_step_of_returns hS.returns_at (hr u (by omega)) (ih (by omega))).1
  refine ⟨key t le_rfl, fun j hj => ?_⟩
  exact (expansion_step_of_returns hS.returns_at (hr j hj.le) (key j hj.le)).2
end YangMills.Construction.FreeEnergies
end
