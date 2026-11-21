import YangMills.Construction.SystemOfAdmissibleConstants.AdmissibleSideLengths
import YangMills.Construction.SystemOfAdmissibleConstants.ThresholdsOfTheLaw
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
def levelEnvelopesStatement : Prop :=
  ForAllTrajectoryCouplings fun T y D g =>
    (∀ d : ℝ, 0 < d → d < 1 → ∀ (K : ℕ) (β : ℝ), AdmissibleConstants.IsDatumAtDistance D g d K β →
      AdmissibleConstants.lowerCouplingEnvelope D g d ≤
        D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d) ∧
      D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d) ≤
        AdmissibleConstants.upperCouplingEnvelope D g d ∧
      (K : ℝ) - StateLaws.separationLevel (T.stepParameters y) β K d ≤
        AdmissibleConstants.scaleDepthEnvelope D g d ∧
      |TrajectoryData.logSlope * Real.log (1 / d) -
          D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d)| ≤
        AdmissibleConstants.heightBound D g d) ∧
    AntitoneOn (AdmissibleConstants.lowerCouplingEnvelope D g) (Set.Ioo 0 1) ∧
    AntitoneOn (AdmissibleConstants.upperCouplingEnvelope D g) (Set.Ioo 0 1) ∧
    (∀ d : ℝ, 0 < d → d < 1 → 8 < AdmissibleConstants.lowerCouplingEnvelope D g d) ∧
    BddAbove ((fun d => AdmissibleConstants.heightBound D g d /
      AdmissibleConstants.lowerCouplingEnvelope D g d) '' Set.Ioo 0 1) ∧
    Tendsto (fun d => AdmissibleConstants.heightBound D g d /
      AdmissibleConstants.lowerCouplingEnvelope D g d) (𝓝[>] 0) (𝓝 0)
end YangMills.Construction.SystemOfAdmissibleConstants
end
