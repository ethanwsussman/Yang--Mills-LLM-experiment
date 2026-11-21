import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASide
import YangMills.Construction.ColdStepAtMirrorFrames.ChainOfConstantCurvature
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
open BlockAverages TorusFields TorusLumps
def constantCurvatureTop (L t n : ℕ) (X : imaginaryQuaternions) (μ ν : Fin 4) : TorusField n :=
  restrictToTorus n (constantCurvatureChain (torusFrame L t n) X μ ν 1 (torusFrame L t n).top)
def FlatLimitFromExpansion : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (t : ℕ) (C e : ℝ) (g : TopLevelFamily), ℓ.Admissible → 0 ≤ e →
    IsCurvatureFamilyOnMultiples ℓ 1 C (densityOfTopFamily ℓ.side t g) →
    (∀ (X : imaginaryQuaternions) (μ ν : Fin 4), ‖X‖ = 1 → μ < ν → ∀ ε : ℝ, 0 < ε →
      ∃ n₁ : ℕ, ∀ (n : ℕ) [NeZero n], n₁ ≤ n →
      |centered (densityOfTopFamily ℓ.side t g) n 0 (constantCurvatureTop ℓ.side t n X μ ν)| ≤
        (e / 2 + ε) * (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) ^ 2) →
    HasBoundedFlatLimitForm ℓ.side t g e
end ColdStepAtMirrorFrames
end YangMills.Construction
end
