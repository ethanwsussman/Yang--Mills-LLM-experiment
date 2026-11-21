import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import YangMills.Construction.EuclideanFunctionals.CombinationsOfTuplesComplexComponentsAndConvergenceInC1
import YangMills.Construction.Rotation.ProductFunctionsOnFourSpace
import YangMills.Construction.RotationInvariance.DiscsMotionsAndComplexPositionsOfThePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.ProductSumApprox
def IsProductSumIn (y z : RealPlane) (r : ℝ) (g : R4 → ℂ) : Prop :=
  ∃ (n : ℕ) (_ : 1 ≤ n) (a : Fin n → RealPlane → ℂ) (b : Fin n → RealPlane → ℝ),
    (∀ i, a i ∈ complexProfiles ∧ b i ∈ realLabels ∧
      tsupport (a i) ⊆ openDiscAt y r ∧ tsupport (b i) ⊆ openDiscAt z r) ∧
    g = ∑ i, productFunction (a i) (b i)
def ProductSumsDenseC1 : Prop :=
  ∀ (c : R4) (r : ℝ), 0 < r →
    ∀ f ∈ C1c ℂ, tsupport f ⊆ EuclideanBalls.euclidBall c r →
      ∃ g : ℕ+ → R4 → ℂ,
        (∀ j, g j ∈ C1c ℂ) ∧
        TendstoC1 (fun k : ℕ => g k.succPNat) f ∧
        ∀ j, IsProductSumIn (planeComponent c) (orthogonalComponent c) (2 * r) (g j)
end EuclideanFunctionals.ProductSumApprox
end YangMills.Construction
end
