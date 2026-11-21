import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.LumpContours
def ExpansionBasicBounds : Prop :=
  ∀ (ℓ : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) (f : LocalDensity) (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ),
    ℓ.Admissible → 1 ≤ ℓ.E → 0 < x → 4 * ℓ.n₀ + 2 ^ 16 ≤ clusterRange x → ColdExpansion ℓ t x D f →
    HullExpansion ℓ t x D f Λ Dq Φ φ →
    (∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
      |centered f n y W| ≤ ℓ.E) ∧
    (∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n))
      (ω : Y → Λ.Ω) (y : TorusSite n), IsHullState ℓ (clusterRange x) W Y →
      (∀ X ∈ chainComponents (clusterRange x) Y, Φ n W Y ω X ≠ 0) →
      (∀ z ∈ Y, (clusterRange x : ℝ) / 4 ≤ supDist y z) → |φ n y W Y ω| ≤ 2 * ℓ.E) ∧
    (∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ W : TorusField n,
      D n W ≤ D n (trivialField n) * 2 ^ Fintype.card (TorusSite n) *
        Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)))
end YangMills.Construction.TorusLumps
end
