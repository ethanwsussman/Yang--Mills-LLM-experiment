import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def levelCumulantApproxStatement : Prop :=
  ForAllPoints fun Λ C c _ S => ∀ d : ℕ, S.lastSeparated + d = S.data.windowLevel →
    ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian
        (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side)) μ →
    |jointCumulant μ (fun i => S.halfForm d (S.data.period Λ.stepParams.side) i) -
        jointCumulant μ (fun i =>
          S.observableAt (S.lastSeparated + d) (S.data.period Λ.stepParams.side) i)| ≤
      C 0 * Real.exp (-(c * (S.range : ℝ))) ∧
    (S.lastSeparated = 0 →
      jointCumulant μ (fun i => S.halfForm d (S.data.period Λ.stepParams.side) i) =
        jointCumulant μ (fun i =>
          S.observableAt (S.lastSeparated + d) (S.data.period Λ.stepParams.side) i))
end YangMills.Construction.MomentLaw
end
