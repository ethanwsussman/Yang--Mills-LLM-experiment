import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def supportTotalBoundStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S => ∀ i : Fin Λ.k,
    AEMeasurable (fun w => S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) (S.law S.lastSeparated (S.levelSide S.lastSeparated)) ∧
    ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)), 1 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) ∧
      |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)| ≤
        Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) * S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
end YangMills.Construction.MomentLaw
end
