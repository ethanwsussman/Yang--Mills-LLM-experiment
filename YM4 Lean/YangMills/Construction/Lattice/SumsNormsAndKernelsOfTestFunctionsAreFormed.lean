import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.TestFunctions
open TorusMetric PeriodicLattice
def ObjectsAreWellFormed : Prop :=
  (∀ (L m : ℕ) (j : ℤ), 0 < L → Finite (Plaquette L m j)) ∧
  (∀ (X E : Type) [Norm E] (f : X → E), IsBoundedFun f →
    (∀ x, ‖f x‖ ≤ uniformNorm f) ∧
      (Nonempty X → ∀ C : ℝ, (∀ x, ‖f x‖ ≤ C) → uniformNorm f ≤ C)) ∧
  (∀ (X E : Type) [NormedAddCommGroup E] (d : X → X → ℝ) (f : X → E),
    (∀ x y, 0 ≤ d x y) → IsLipschitzFor d f →
    0 ≤ bestLipschitzConstant d f ∧
      (∀ x y, ‖f x - f y‖ ≤ bestLipschitzConstant d f * d x y) ∧
      ∀ C : ℝ, 0 ≤ C → (∀ x y, ‖f x - f y‖ ≤ C * d x y) → bestLipschitzConstant d f ≤ C) ∧
  (∀ (L m : ℕ) (E : Type) [NormedAddCommGroup E] (f : FourTorus L m → E), 0 < L →
    IsLipschitzFor euclidDistTorus f → IsBoundedFun f) ∧
  (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (Fin 4 → ℝ) → E) (μ : Fin 4)
    (x : Fin 4 → ℝ), IsC1R4 f →
    DifferentiableAt ℝ (fun t : ℝ => f (x + t • Pi.single μ (1 : ℝ))) 0) ∧
  (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : ℝ) (f : Torus4 ℓ → E)
    (μ : Fin 4) (x : Torus4 ℓ), IsC1Torus f →
    DifferentiableAt ℝ (fun t : ℝ => f (x + torusProj ℓ (t • Pi.single μ (1 : ℝ)))) 0) ∧
  (∀ (E : Type) [AddCommMonoid E] [TopologicalSpace E] (ℓ : ℝ) (A : Set (Fin 4 → ℝ))
    (f : (Fin 4 → ℝ) → E), 0 < ℓ → IsPeriodizable ℓ A f →
    (∀ (v : Fin 4 → ℝ) (k k' : Fin 4 → ℤ), f (v + latticeTranslate ℓ k) ≠ 0 →
      f (v + latticeTranslate ℓ k') ≠ 0 → k = k') ∧
      (∀ v ∈ A, periodize ℓ f (torusProj ℓ v) = f v) ∧
      ∀ x, x ∉ torusProj ℓ '' A → periodize ℓ f x = 0) ∧
  (∀ (𝕜 : Type) [RCLike 𝕜] (f h : (Fin 4 → ℝ) → 𝕜), IsKernelPairR4 f h →
    Integrable fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      f z.1 * h z.2 * ((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : 𝕜)) ∧
  (∀ (𝕜 : Type) [RCLike 𝕜] (ℓ : ℝ) (f h : Torus4 ℓ → 𝕜) (c : Fin 4 → ℝ) (r : ℝ),
    IsBoundedFun f → IsBoundedFun h → Measurable (f ∘ torusProj ℓ) → Measurable (h ∘ torusProj ℓ) →
    IsKernelBallTorus f h c r →
    inverseEighthKernelTorus f h = inverseEighthKernel (liftToBall ℓ c r f) (liftToBall ℓ c r h))
end YangMills.Construction.TestFunctions
end
