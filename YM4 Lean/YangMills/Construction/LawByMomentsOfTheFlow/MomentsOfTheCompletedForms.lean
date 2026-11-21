import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormsOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def completedFormMomentsStatement : Prop :=
  ForAllPoints fun P C _ _ S => ∀ s : ℕ, s = S.data.windowLevel →
    ∀ μ : Measure (LevelChain P.stepParams.side s (S.data.period P.stepParams.side)),
    IsCanonicalGaussian (levelEnergy P.stepParams.coupling s (S.data.period P.stepParams.side)) μ →
    ∀ (j : ℕ) (hj : j ≤ s), s - j ≤ S.lastSeparated → ∀ i : Fin P.k,
      Integrable (fun X => |S.completedForm (s - j) j (S.data.period P.stepParams.side) i
        (CompletedForms.truncateTop j s (S.data.period P.stepParams.side) hj X)| ^ P.k) μ ∧
      ∫ X, |S.completedForm (s - j) j (S.data.period P.stepParams.side) i
        (CompletedForms.truncateTop j s (S.data.period P.stepParams.side) hj X)| ^ P.k ∂μ ≤
        (C 0 * (P.stepParams.side : ℝ) ^ (5 * (S.data.scaleLevel - (s - j)))) ^ P.k
end YangMills.Construction.MomentLaw
end
