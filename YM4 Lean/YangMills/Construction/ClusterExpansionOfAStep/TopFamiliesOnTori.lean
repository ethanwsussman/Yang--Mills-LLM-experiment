import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open BlockAverages ColdStepAtMirrorFrames TorusFields
def TopFamilyOnTori : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (t : ℕ) (s : ℝ) (g : TopLevelFamily), ℓ.threshold ≤ s →
    (IsLocalDensity ℓ.side t ℓ.n₀ s g → IsAdmissibleDensity ℓ (densityOfTopFamily ℓ.side t g)) ∧
    (∀ e : ℕ → ℕ → ℝ, ColdStepAtMirrorFrames.DerivDecay ℓ.side t ℓ.n₀ s g e →
      TorusLumps.DerivDecay ℓ (densityOfTopFamily ℓ.side t g) e) ∧
    (∀ e : ℕ → ℝ, IsLocalOnTori ℓ.side t ℓ.n₀ s g e →
      LocalComparison ℓ (densityOfTopFamily ℓ.side t g) e) ∧
    (∀ e : ℕ → ℝ, IsLocalOnTori ℓ.side t ℓ.n₀ s (centredFamily g) e →
      LocalComparison ℓ (centeredFamily (densityOfTopFamily ℓ.side t g)) e) ∧
    ∀ (b b' : LatticeBond) (X X' : imaginaryQuaternions) (n : ℕ), ℓ.n₀ ≤ n →
      mixedDeriv (densityOfTopFamily ℓ.side t g n 0) (trivialField n)
          ![bondFrom 0 b, bondFrom 0 b'] ![X, X'] =
        secondDerivAtUniform g ℓ.side t n b b' X X'
end YangMills.Construction.TorusLumps
end
