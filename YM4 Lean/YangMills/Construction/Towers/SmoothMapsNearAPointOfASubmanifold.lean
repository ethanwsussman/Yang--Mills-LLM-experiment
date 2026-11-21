import YangMills.Construction.Towers.TwoStagesOfAConstraintDefs
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.Manifolds
open Matrices.EmbeddedSubmanifold
def LocalSmoothCalculus : Prop :=
  (∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
      [FiniteDimensional ℝ P] (M : Set E) (O : Set P) (φ : P → E) (z : P),
      IsSmoothParametrization M O φ → z ∈ O →
      ∃ (Ω : Set E) (ρ : E → P), IsOpen Ω ∧ φ z ∈ Ω ∧ ContDiffOn ℝ ∞ ρ Ω ∧
        ∀ p ∈ M ∩ Ω, ρ p ∈ O ∧ φ (ρ p) = p) ∧
  (∀ (E E' P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
      [NormedSpace ℝ E'] [NormedAddCommGroup P] [NormedSpace ℝ P] (M O : Set E) (f : E → E')
      (c : P → E) (u : P), IsChartedSubset M → IsSmoothOnOpen M O f → ContDiffAt ℝ ∞ c u →
      (∀ᶠ u' in 𝓝 u, c u' ∈ M) → c u ∈ O → ContDiffAt ℝ ∞ (f ∘ c) u) ∧
  (∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
      [FiniteDimensional ℝ P] (M : Set E) (O : Set P) (φ : P → E) (z : P),
      IsChartedSubset M → IsSmoothParametrization M O φ → z ∈ O →
      tangentSpace M (φ z) = LinearMap.range (fderiv ℝ φ z : P →ₗ[ℝ] E)) ∧
  (∀ (E E' P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
      [NormedSpace ℝ E'] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
      (M O' : Set E) (f : E → E') (O : Set P) (φ : P → E) (z a : P)
      (v : tangentSpace M (φ z)), IsChartedSubset M → IsSmoothOnOpen M O' f →
      IsSmoothParametrization M O φ → z ∈ O → φ z ∈ O' → (v : E) = fderiv ℝ φ z a →
      tangentDifferential M f (φ z) v = fderiv ℝ (f ∘ φ) z a) ∧
  (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (M O : Set E),
      IsChartedSubset M → Matrices.ComplexMatrix2.IsRelativelyOpen M O → IsChartedSubset O) ∧
  (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Set E) (c : Chart M),
      IsSmoothParametrization M (Chart.source c) (Chart.param c)) ∧
  (∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
      [FiniteDimensional ℝ P] (N N' : Set E) (O : Set P) (φ : P → E),
      IsSmoothParametrization N O φ → Matrices.ComplexMatrix2.IsRelativelyOpen N N' →
      IsSmoothParametrization N' (O ∩ φ ⁻¹' N') φ)
end YangMills.Construction.Manifolds
end
