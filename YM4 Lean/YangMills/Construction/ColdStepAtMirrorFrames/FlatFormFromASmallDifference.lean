import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASide
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusLumps TorusFields
namespace ColdStepAtMirrorFrames
def bondWeight (r : ℝ) (u : (Fin 4 → ℤ) × Fin 4) : ℝ :=
  (1 + (offsetSupNorm u.1 : ℝ)) * Real.exp (-(r * offsetSupNorm u.1))
def flatLimitDifferenceConstant (r : ℝ) : ℝ := 8 * (∑' u, bondWeight r u) ^ 2
def flatLimitFromSmallDifference : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (t : ℕ) (C w : ℝ) (g g₀ : TopLevelFamily), ℓ.Admissible → 0 ≤ C → 0 ≤ w →
    IsCurvatureFamilyOnMultiples ℓ 1 C (densityOfTopFamily ℓ.side t g) →
    IsCurvatureFamilyOnMultiples ℓ 1 C (densityOfTopFamily ℓ.side t g₀) →
    (∀ n, ℓ.n₀ ≤ n → ContDiffThreeAlongBonds (g (torusFrame ℓ.side t n) 0) (uniformField _ _)) →
    (∀ n, ℓ.n₀ ≤ n → ContDiffThreeAlongBonds (g₀ (torusFrame ℓ.side t n) 0) (uniformField _ _)) →
    HasBoundedFlatLimitForm ℓ.side t g₀ 0 →
    (∀ (b b' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
      ∀ᶠ n in Filter.atTop,
        |secondDerivAtUniform g ℓ.side t n b b' X X' - secondDerivAtUniform g₀ ℓ.side t n b b' X X'| ≤ w) →
    HasBoundedFlatLimitForm ℓ.side t g
      (flatLimitDifferenceConstant (ℓ.weightRate / 6) * C ^ (1 / 3 : ℝ) * w ^ (2 / 3 : ℝ))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
