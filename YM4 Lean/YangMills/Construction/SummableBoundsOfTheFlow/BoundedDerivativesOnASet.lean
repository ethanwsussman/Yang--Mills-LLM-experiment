import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.UniformDerivativeBounds
def UniformlyBoundedDerivs : ℕ → ℝ → Set ℝ → (ℝ → ℝ) → Prop
  | 0, D, S, f => (∀ x ∈ S, |f x| ≤ D) ∧ ContinuousOn f S
  | n + 1, D, S, f => (∀ x ∈ S, |f x| ≤ D) ∧
      ∃ f' : ℝ → ℝ, (∀ x ∈ S, HasDerivAt f (f' x) x) ∧ UniformlyBoundedDerivs n D S f'
structure ClosureProperties : Prop where
  mono : ∀ (n : ℕ) (D D' : ℝ) (S : Set ℝ) (f : ℝ → ℝ), D ≤ D' → UniformlyBoundedDerivs n D S f →
    UniformlyBoundedDerivs n D' S f
  of_succ : ∀ (n : ℕ) (D : ℝ) (S : Set ℝ) (f : ℝ → ℝ), UniformlyBoundedDerivs (n + 1) D S f →
    UniformlyBoundedDerivs n D S f
  congr : ∀ (n : ℕ) (D : ℝ) (S : Set ℝ) (f g : ℝ → ℝ), IsOpen S → (∀ x ∈ S, f x = g x) →
    UniformlyBoundedDerivs n D S f → UniformlyBoundedDerivs n D S g
  mono_set : ∀ (n : ℕ) (D : ℝ) (S S' : Set ℝ) (f : ℝ → ℝ), S' ⊆ S → UniformlyBoundedDerivs n D S f →
    UniformlyBoundedDerivs n D S' f
  const : ∀ (n : ℕ) (S : Set ℝ) (c : ℝ), UniformlyBoundedDerivs n |c| S fun _ => c
  add : ∀ (n : ℕ) (D D' : ℝ) (S : Set ℝ) (f g : ℝ → ℝ), UniformlyBoundedDerivs n D S f →
    UniformlyBoundedDerivs n D' S g → UniformlyBoundedDerivs n (D + D') S fun x => f x + g x
  mul : ∀ (n : ℕ) (D D' : ℝ) (S : Set ℝ) (f g : ℝ → ℝ), 0 ≤ D → 0 ≤ D' → UniformlyBoundedDerivs n D S f →
    UniformlyBoundedDerivs n D' S g → UniformlyBoundedDerivs n (2 ^ n * D * D') S fun x => f x * g x
  exp : ∀ (n : ℕ) (D : ℝ), 0 ≤ D → ∃ D' : ℝ, 0 ≤ D' ∧ ∀ (S : Set ℝ) (f : ℝ → ℝ),
    UniformlyBoundedDerivs n D S f → UniformlyBoundedDerivs n D' S fun x => Real.exp (f x)
  of_contDiff : ∀ (n : ℕ) (D : ℝ) (S : Set ℝ) (e : ℝ → ℝ), IsOpen S → (∀ x ∈ S, ContDiffAt ℝ n e x) →
    (∀ j, j ≤ n → ∀ x ∈ S, |iteratedDeriv j e x| ≤ D) → UniformlyBoundedDerivs n D S e
  contDiffOn : ∀ (n : ℕ) (D : ℝ) (S : Set ℝ) (f : ℝ → ℝ), IsOpen S → UniformlyBoundedDerivs n D S f →
    ContDiffOn ℝ n f S
  indicator_mul_flat : ∀ (n : ℕ) (D B : ℝ) (I S : Set ℝ) (f χ : ℝ → ℝ), IsOpen S → S ⊆ I → 0 ≤ D → 0 ≤ B →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → (∀ x ∈ I \ S, ∀ j : ℕ, iteratedDeriv j χ x = 0) →
    (∀ j, j ≤ n → ∀ x ∈ I, |iteratedDeriv j χ x| ≤ B) → UniformlyBoundedDerivs n D S f →
    UniformlyBoundedDerivs n (2 ^ n * D * B) I (S.indicator fun x => f x * χ x)
  integral : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (n : ℕ) (D : ℝ) (S : Set ℝ)
    (Q : ℝ → Ω → ℝ), IsOpen S → (∀ᵐ ω ∂μ, UniformlyBoundedDerivs n D S fun t => Q t ω) →
    (∀ t ∈ S, AEStronglyMeasurable (Q t) μ) →
    UniformlyBoundedDerivs n (D * μ.real univ) S fun t => ∫ ω, Q t ω ∂μ
def closureProperties_statement : Prop := ClosureProperties
end YangMills.Construction.UniformDerivativeBounds
end
