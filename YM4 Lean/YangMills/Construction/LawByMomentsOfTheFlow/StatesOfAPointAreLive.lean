import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusLumps WeightedResponses
namespace MomentLaw
def liveStatesStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S => ∀ u ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide Λ.stepParams n →
    ∀ᵐ w ∂(S.law u n),
      IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight
        (S.state u n w).1 (S.state u n w).2.1 (S.state u n w).2.2
end MomentLaw
end YangMills.Construction
end
