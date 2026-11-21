import YangMills.Construction.TorusOrFourSpace.BoxesStockOfSupportsAndFamilyOfTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
namespace C1NormComparison
open Kind
variable (D : Params) (E : Kind)
def GradNormBetweenPartials (u : E.Pt D → ℝ) (y : E.Pt D) : Prop :=
  (⨆ μ : Fin 4, |partialDeriv D E μ u y|) ≤ gradNorm D E u y ∧
    gradNorm D E u y ≤ 2 * ⨆ μ : Fin 4, |partialDeriv D E μ u y|
def C1NormsCompared (u : E.Pt D → ℝ) : Prop :=
  c1NormQ D E u ≤ euclidC1Norm D E u ∧ euclidC1Norm D E u ≤ 2 * c1NormQ D E u
def FiniteAndBoundsSharp (u : E.Pt D → ℝ) : Prop :=
  c1NormQ D E u < ⊤ ∧ euclidC1Norm D E u < ⊤ ∧
    sharpNormQ D E u ≤ ENNReal.ofReal (40 * D.M) * euclidC1Norm D E u ∧
    ENNReal.ofReal (40 * D.M) * euclidC1Norm D E u ≤ ENNReal.ofReal (80 * D.M) * c1NormQ D E u
structure IsNormOnSubmodule (V : Submodule ℝ (E.Pt D → ℝ)) (N : (E.Pt D → ℝ) → ℝ≥0∞) : Prop where
  finite : ∀ u ∈ V, N u < ⊤
  eq_zero_iff : ∀ u ∈ V, N u = 0 ↔ u = 0
  homogeneous : ∀ (α : ℝ), ∀ u ∈ V, N (α • u) = ENNReal.ofReal |α| * N u
  triangle : ∀ u ∈ V, ∀ u' ∈ V, N (u + u') ≤ N u + N u'
def ConvergesWrt (N : (E.Pt D → ℝ) → ℝ≥0∞) (V : Submodule ℝ (E.Pt D → ℝ))
    (s : ℕ → E.Pt D → ℝ) : Prop :=
  ∃ u ∈ V, ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, N (s j - u) < ENNReal.ofReal ε
def IsCauchyWrt (N : (E.Pt D → ℝ) → ℝ≥0∞) (s : ℕ → E.Pt D → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ i ≥ J, ∀ j ≥ J, N (s i - s j) < ENNReal.ofReal ε
def EquivalentNormsOn (V : Submodule ℝ (E.Pt D → ℝ)) : Prop :=
  IsNormOnSubmodule D E V (euclidC1Norm D E) ∧ IsNormOnSubmodule D E V (c1NormQ D E) ∧
    (∀ s : ℕ → E.Pt D → ℝ, (∀ j, s j ∈ V) →
      (ConvergesWrt D E (euclidC1Norm D E) V s ↔ ConvergesWrt D E (c1NormQ D E) V s) ∧
      (IsCauchyWrt D E (euclidC1Norm D E) s ↔ IsCauchyWrt D E (c1NormQ D E) s)) ∧
    ∀ A : Set (E.Pt D → ℝ), A ⊆ V →
      (IsDenseWrt D E (euclidC1Norm D E) V A ↔ IsDenseWrt D E (c1NormQ D E) V A)
end C1NormComparison
open Kind C1NormComparison in
def C1NormComparison.statement : Prop :=
  ∀ (D : Params) (E : Kind),
    (∀ u ∈ c1Set D E,
      (∀ y, GradNormBetweenPartials D E u y) ∧ C1NormsCompared D E u ∧
        (IsCompactQ D E (supportQ D E u) → FiniteAndBoundsSharp D E u)) ∧
    ∀ V : Submodule ℝ (E.Pt D → ℝ),
      (∀ u ∈ V, u ∈ c1Set D E ∧ euclidC1Norm D E u < ⊤) →
        EquivalentNormsOn D E V
end YangMills.Construction.PeriodicSpace
