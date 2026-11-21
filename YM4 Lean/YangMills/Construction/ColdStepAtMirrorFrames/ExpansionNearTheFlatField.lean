import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongAFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def UniformFieldDerivComparison : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame)
    (T : Finset (F.Site F.depth × Fin 4)) (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (B : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (r k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsRegularFamily L t n₀ σ δ E E₃ f → IsCubicTorusAbove L t n₀ F → 0 ≤ δ → 0 ≤ E → E ≤ E₃ → (∀ b, b ∈ T) →
    IsSmallCurvature σ W →
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) s)) →
    AgreeOnBox W (expFlow B (uniformField F F.depth) 1) y y r → k ≤ 2 → (∀ l, BondWithinRadius r (h l)) →
    AreUnitVectors X →
    |bondDeriv (subtractTrivial f F y) W (bondsAt y h) X -
      bondDeriv (subtractTrivial f F y) (uniformField F F.depth) (bondsAt y h) X| ≤
      E / torusDecayFactor L δ r + C₀ * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖
end ColdStepAtMirrorFrames
end YangMills.Construction
end
