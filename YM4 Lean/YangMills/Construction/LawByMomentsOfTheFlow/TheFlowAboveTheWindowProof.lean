import YangMills.Construction.LawByMomentsOfTheFlow.TheFlowAboveTheWindow
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
open YangMills.Construction.TorusLumps YangMills.Construction.StepReturn YangMills.Construction.WeightedResponses
private theorem expansion_next_of_returns {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
theorem couplingFlowAboveWindow : CouplingFlowAboveWindow := by
  intro ℓ hℓ g hg hy β K hβ hK
  have hB : 0 < ℓ.B := hℓ.admissible.B_pos
  have hTop : ℓ.y₁ ≤ couplingWindowTop ℓ g := by
    unfold couplingWindowTop
    linarith
  have hβy : ℓ.y₁ ≤ β := hTop.trans hβ
  have hlt : ∀ j < K, ℓ.y₁ ≤ (couplingFlow ℓ β j).1 := fun j hj => hTop.trans (hK.2 j hj).le
  have hexp : ∀ t : ℕ, (∀ j < t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) →
      HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by
    intro t
    induction t with
    | zero => exact fun _ => hℓ.wilson_hasExpansion β hβy
    | succ t ih =>
      intro hj
      exact (expansion_next_of_returns hℓ.returns (hj t (Nat.lt_succ_self t))
        (ih fun j hjt => hj j (Nat.lt_succ_of_lt hjt))).1
  have hstep : ∀ t < K, |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := by
    intro t ht
    exact (expansion_next_of_returns hℓ.returns (hlt t ht) (hexp t fun j hj => hlt j (hj.trans ht))).2
  refine ⟨fun j hj => ?_, fun u v huv hv => ?_⟩
  · rcases Nat.lt_or_ge j K with h | h
    · exact hlt j h
    · have hjK : j = K := le_antisymm hj h
      subst hjK
      cases j with
      | zero => exact hβy
      | succ j =>
        have h1 := abs_le.mp (hstep j (Nat.lt_succ_self j))
        have h2 := hK.2 j (Nat.lt_succ_self j)
        unfold couplingWindowTop at h2
        linarith [h1.1]
  · induction v, huv using Nat.le_induction with
    | base => simp
    | succ v huv ih =>
      have h1 := ih (by omega)
      have h2 := hstep v (by omega)
      have h3 := abs_sub_le (couplingFlow ℓ β (v + 1)).1 (couplingFlow ℓ β v).1 (couplingFlow ℓ β u).1
      push_cast
      linarith
end YangMills.Construction.LevelTestFunctions
end
