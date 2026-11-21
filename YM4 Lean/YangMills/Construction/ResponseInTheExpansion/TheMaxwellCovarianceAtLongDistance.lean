import YangMills.Construction.ResponseInTheExpansion.KernelOfTheCurvature
import YangMills.Construction.ResponseInTheExpansion.TheStepsAddUpToTheMaxwellCovariance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def maxwellCovarianceLongDistanceStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∃ C : ℝ, ∀ (k N : ℕ) [NeZero N], Tb.n₀ ≤ N →
    ∀ Tt : TorusFields.TorusPlaquette N → TorusFields.TorusPlaquette N → ℝ,
    IsMaxwellCovariance Tb.coupling (Tb.stepParameters y).side k Tt →
    ∀ P ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite N)),
    ∀ P' ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite N)),
      1 ≤ LinearResponse.sqNorm (LinearResponse.plaquetteCentreDisplacement P P') →
      LinearResponse.sqNorm (LinearResponse.plaquetteCentreDisplacement P P') ≤ ((N : ℝ) / 8) ^ 2 →
      |Tt P P' - LinearResponse.continuumCurvatureKernel (LinearResponse.plaquetteCentreDisplacement P P')
          P.2.1 P.2.2 P'.2.1 P'.2.2| ≤
        C * (LinearResponse.sqNorm (LinearResponse.plaquetteCentreDisplacement P P') ^ (-(5 / 2 : ℝ)) +
          (N : ℝ) ^ (-(4 : ℤ)))
end YangMills.Construction.ResponseInTheExpansion
end
