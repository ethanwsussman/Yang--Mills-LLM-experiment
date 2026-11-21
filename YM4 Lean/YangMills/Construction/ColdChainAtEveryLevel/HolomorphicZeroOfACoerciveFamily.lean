import Mathlib
set_option autoImplicit false
noncomputable section
open Matrix
namespace YangMills.Construction.Analytic
structure IsRealCoordSeminorm {m : ℕ} (p : (Fin m → ℝ) → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  triangle : ∀ x x', p (x + x') ≤ p x + p x'
  smul_real : ∀ (c : ℝ) x, p (c • x) = |c| * p x
def realParts {m : ℕ} (t : Fin m → ℂ) : Fin m → ℝ := fun i => (t i).re
def imagParts {m : ℕ} (t : Fin m → ℂ) : Fin m → ℝ := fun i => (t i).im
def complexifiedSeminorm {m : ℕ} (p : (Fin m → ℝ) → ℝ) (t : Fin m → ℂ) : ℝ := p (realParts t) + p (imagParts t)
def matrixFormPairing {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (t : Fin m → ℂ) (α : Fin m → ℝ) : ℂ :=
  ∑ i, t i * (((M *ᵥ α) i : ℝ) : ℂ)
def directionPairing {m : ℕ} (v : Fin m → ℂ) (α : Fin m → ℝ) : ℂ := ∑ j, (α j : ℂ) * v j
def HolomorphicZeroOfCoerciveFamilyProperty : Prop :=
  ∀ (m k : ℕ) (ι : Type) (p q : ι → (Fin m → ℝ) → ℝ) (Y : (Fin m → ℝ) → ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (g : (Fin m → ℂ) × (Fin k → ℂ) → (Fin m → ℂ)) (Ω : Set (Fin k → ℂ)) (κ ε : (Fin k → ℂ) → ℝ) (Ca K r : ℝ),
    Nonempty ι → IsRealCoordSeminorm Y → (∀ x, Y x = 0 → x = 0) → (∀ i, IsRealCoordSeminorm (p i)) →
    (∀ i α, 0 ≤ q i α) → (∀ i x, p i x ≤ Y x) → (∀ x β, 0 ≤ β → (∀ i, p i x ≤ β) → Y x ≤ β) →
    0 < Ca → 0 ≤ K → 0 < r → IsOpen Ω →
    (∀ i x β, 0 ≤ β → (∀ α, |x ⬝ᵥ (M *ᵥ α)| ≤ β * q i α) → p i x ≤ Ca * β) →
    (∀ ζ ∈ Ω, ∀ t, complexifiedSeminorm Y t ≤ r → AnalyticAt ℂ g (t, ζ)) →
    (∀ ζ ∈ Ω, 0 ≤ κ ζ ∧ 0 ≤ ε ζ ∧ 8 * Ca * ε ζ ≤ r ∧ 4 * Ca * K * (2 * r + κ ζ) ≤ 1) →
    (∀ ζ ∈ Ω, ∀ i α, ‖directionPairing (g (0, ζ)) α‖ ≤ ε ζ * q i α) →
    (∀ ζ ∈ Ω, ∀ t t', complexifiedSeminorm Y t ≤ r → complexifiedSeminorm Y t' ≤ r → ∀ i α,
      ‖directionPairing (g (t, ζ) - g (t', ζ)) α - matrixFormPairing M (t - t') α‖ ≤
        K * (complexifiedSeminorm Y t + complexifiedSeminorm Y t' + κ ζ) * complexifiedSeminorm (p i) (t - t') * q i α) →
    ∃ w : (Fin k → ℂ) → (Fin m → ℂ), ∀ ζ ∈ Ω, AnalyticAt ℂ w ζ ∧ g (w ζ, ζ) = 0 ∧
      complexifiedSeminorm Y (w ζ) ≤ 4 * Ca * ε ζ ∧
      ((∀ t, imagParts t = 0 → complexifiedSeminorm Y t ≤ r → imagParts (g (t, ζ)) = 0) → imagParts (w ζ) = 0)
end YangMills.Construction.Analytic
end
