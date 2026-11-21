import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction
namespace BoxGaussian
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters
open YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages
def curlCovarianceBoundsStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∃ R₀ : ℕ, ∀ (k n : ℕ) [NeZero n] (o : TorusSite n) (R : ℕ),
    R₀ ≤ R → 16 * R < n →
    IsUnit (regularizedHessian Tb.coupling Tb.side k o R).det ∧
    (∀ p p' : TorusPlaquette n,
      curlCovariance Tb.coupling Tb.side k o R p p' = curlCovariance Tb.coupling Tb.side k o R p' p) ∧
    ∀ u : TorusPlaquette n → Fin 3 → ℝ, 0 ≤ curlQuadForm Tb.coupling Tb.side k o R u ∧
      curlQuadForm Tb.coupling Tb.side k o R u ≤
        (2 * Tb.coercivity)⁻¹ * ∑ e : Fin 3, ∑ p ∈ plaquettesIn (supBall o (2 * R)), u p e ^ 2
end BoxGaussian
end YangMills.Construction
end
