import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongAFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ExpansionCoefficientsNearUniformField : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame)
    (T : Finset (F.Site F.depth × Fin 4)) (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (r k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsRegularFamily L t n₀ σ δ E E₃ f → IsCubicTorusAbove L t n₀ F → 0 ≤ δ → 0 ≤ E → E ≤ E₃ → (∀ b, b ∈ T) →
    IsSmallCurvature σ W →
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) u)) →
    AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r → 1 ≤ k → k ≤ 2 → AreUnitVectors X →
    |bondDeriv (subtractTrivial f F y) W c X - bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X| ≤
      3 * E / torusDecayFactor L δ r + C₀ * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖
end YangMills.Construction.ColdStepAtMirrorFrames
end
