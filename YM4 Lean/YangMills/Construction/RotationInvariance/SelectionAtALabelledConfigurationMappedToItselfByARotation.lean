import YangMills.Construction.RotationInvariance.HarmonicsAtLabelledSets
import Mathlib
set_option autoImplicit false
open Complex (I)
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.RotationFixedSelection
def Holds : Prop :=
  ∀ (L : SharpScale) (A : ConnFamily) (P : PlaneDataWithAperture L A) (k : ℕ), 2 ≤ k →
    ∀ (x : RealPlane.LabelledPoints k), x.points ∈ RealPlane.injectivePointTuples k →
    ∀ (θ : ℝ) (c : RealPlane) (σ : Equiv.Perm (Fin k)),
      (∀ j, c + RealPlane.rotate θ (x.points j - c) = x.points (σ j)) →
      (∀ j, x.labelVec (σ j) = x.labelVec j) →
      ∀ q : ℤ,
        (1 - Complex.exp (4 * I * (q : ℂ) * (θ : ℂ))) * configHarmonic A P.angle q x = 0
end YangMills.Construction.EuclideanFunctionals.RotationFixedSelection
end
