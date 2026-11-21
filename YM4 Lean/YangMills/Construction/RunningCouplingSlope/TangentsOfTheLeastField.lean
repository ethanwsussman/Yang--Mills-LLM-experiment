import YangMills.Construction.ClusterExpansionOfAStep.OffsetsAboveABox
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeThroughAFieldMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps RenormalizationStepParameters SlopeCoefficient
namespace RunningCouplingSlope
def MinimizerDerivativeDecay : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧
    ∃ Z : (t n : ℕ) → TorusBond n → imaginaryQuaternions → TorusBond (n * T.side) → imaginaryQuaternions, ∀ t : ℕ,
      (∀ (n : ℕ) [NeZero n], 64 ≤ n → HasFlatTangents (minimizerOnFinerTorus T.coupling T.ρA T.side t n) (Z t n) ∧
        ∀ (c : TorusBond n) (X : imaginaryQuaternions) (b : TorusBond (n * T.side)), ‖X‖ = 1 →
          ‖Z t n c X b‖ ≤ M * Real.exp (-(θ * (supDist (parentBlock T.side b.1) c.1 : ℝ)))) ∧
      ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (r : ℕ) (u e : Fin 4 → ℤ) (i k : Fin 4) (X : imaginaryQuaternions),
        64 ≤ n → 64 ≤ n' → 16 ≤ r → 2 * r + 2 < n → 2 * r + 2 < n' → ‖X‖ = 1 →
        (∀ j, |e j - CongruentBoxes.coarseOffset T.side u j| + 1 ≤ (r : ℤ)) →
        ‖((Z t n (siteOfInt e, k) X (siteOfInt u, i) : imaginaryQuaternions) : ℍ[ℝ]) -
            ((Z t n' (siteOfInt e, k) X (siteOfInt u, i) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
          M * Real.exp (-(θ * (r : ℝ)))
end RunningCouplingSlope
end YangMills.Construction
end
