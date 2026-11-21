import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps RenormalizationStepParameters StepSettings WeightedResponses ResponseInTheExpansion BlockAverages LimitForms
def curlCovarianceNearMaxwellStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb _ => ∃ (C : ℝ) (R₀ : ℕ), ∀ (k n : ℕ) [NeZero n] (o : TorusSite n) (R : ℕ),
    R₀ ≤ R → 16 * R < n →
    ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 8)), ∀ p' ∈ plaquettesIn (supBall o ((R : ℝ) / 8)),
      ∀ z : Fin 4 → ℤ, (∀ i, z i = ((p.1 - p'.1) i).valMinAbs) → z ≠ 0 →
        |curlCovariance Tb.coupling Tb.side k o R p p' - maxwellKernel z p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
          C * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ + C * ((R : ℝ) ^ 4)⁻¹
end YangMills.Construction.BoxGaussian
end
