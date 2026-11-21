import YangMills.Construction.RotationInvariance.HarmonicsAtLabelledSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open RealPlane
def harmonicSum (S : ConnFamily) (φ₀ : RealPlane.openingAngles) (n : ℕ)
    (φ : Fin n → RealPlane.realLabels) (y : Fin n → RealPlane) : ℂ :=
  ∑ m ∈ Finset.Icc (-(maxFrequency S φ₀ n : ℤ)) (maxFrequency S φ₀ n),
    pointHarmonic S φ₀ m n φ y
end YangMills.Construction.EuclideanFunctionals
end
