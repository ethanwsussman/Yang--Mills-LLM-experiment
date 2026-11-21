import YangMills.Construction.Continuum.RulesOfTheOrthogonalAction
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.OrthogonalAction
open Orthogonal SeparatedTuples
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
def gradSup (f : RealValued) : ℝ := ⨆ x, euclidNormVec (gradR4 f x)
def gradOscillation (f : RealValued) (δ : ℝ) : ℝ :=
  sSup {r | ∃ x y : AmbientSpace, euclidNormVec (x - y) ≤ δ ∧
    r = euclidNormVec (gradR4 f x - gradR4 f y)}
def rotationBound (M R : ℝ) (f : RealValued) (s : ℝ) : ℝ :=
  max (gradSup f * s * R)
    (40 * M * (s * gradSup f + gradOscillation f (s * R)))
def SharpNormRotationModulus : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∀ f : RealValued, IsC1c f → ∀ R : ℝ, 0 < R →
    tsupport f ⊆ TestFunctions.closedBallR4 0 R →
    (∀ Q : orthogonalGroupFour,
      TestFunctions.sharpNormR4 M (orthogonalAct Q f - f) ≤
        rotationBound M R f (matrixOperatorNorm (Q.1 - 1))) ∧
    Tendsto (fun Q : orthogonalGroupFour => rotationBound M R f (matrixOperatorNorm (Q.1 - 1)))
      (comap (fun Q : orthogonalGroupFour => matrixOperatorNorm (Q.1 - 1)) (𝓝 0)) (𝓝 0)
end YangMills.Construction.OrthogonalAction
end
