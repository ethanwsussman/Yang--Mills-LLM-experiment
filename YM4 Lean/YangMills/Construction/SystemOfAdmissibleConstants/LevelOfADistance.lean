import YangMills.Construction.SystemOfAdmissibleConstants.AdmissibleSideLengths
import YangMills.Construction.SystemOfAdmissibleConstants.ThresholdsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
def separationLevelStatement : Prop :=
  ForAllTrajectoryCouplings fun T y D g =>
    ∀ d : ℝ, 0 < d → d < 1 → ∀ (K : ℕ) (β : ℝ), AdmissibleConstants.IsDatumAtDistance D g d K β →
      IsGreatest {k : ℕ | k ≤ K ∧ StateLaws.IsSeparatedAt (T.stepParameters y) β K d k}
        (StateLaws.separationLevel (T.stepParameters y) β K d) ∧
      StateLaws.separationLevel (T.stepParameters y) β K d < K ∧
      StateLaws.lengthInSites T.side K (StateLaws.separationLevel (T.stepParameters y) β K d) d ≤
        2 ^ 13 * (T.side : ℝ) *
          (TorusLumps.clusterRange (D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d)) : ℝ)
end YangMills.Construction.SystemOfAdmissibleConstants
end
