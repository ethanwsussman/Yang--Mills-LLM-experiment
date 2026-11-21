import YangMills.Construction.Towers.TwoStagesOfAConstraintDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Manifolds
def CoordinatesOfTwoSubmersions : Prop :=
  (∀ (E₁ E₂ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
      [NormedSpace ℝ E₂] (X : Set E₁) (Y : Set E₂) (f : E₁ → E₂) (y : E₂),
      Matrices.EmbeddedSubmanifold.IsChartedSubset X →
      Matrices.EmbeddedSubmanifold.IsChartedSubset Y →
      IsSmoothSubmersion X Y f →
      Matrices.EmbeddedSubmanifold.IsChartedSubset (fiber X f y)) ∧
  (∀ (E₁ E₂ E₃ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
      [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
      (X : Set E₁) (Y : Set E₂) (Z : Set E₃) (f : E₁ → E₂) (g : E₂ → E₃),
      Matrices.EmbeddedSubmanifold.IsChartedSubset X →
      Matrices.EmbeddedSubmanifold.IsChartedSubset Y →
      Matrices.EmbeddedSubmanifold.IsChartedSubset Z →
      IsSmoothSubmersion X Y f → IsSmoothSubmersion Y Z g → IsSmoothSubmersion X Z (g ∘ f)) ∧
  (∀ (E₁ E₂ E₃ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
      [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
      (X : Set E₁) (Y : Set E₂) (Z : Set E₃) (f : E₁ → E₂) (g : E₂ → E₃) (x₀ : E₁),
      Matrices.EmbeddedSubmanifold.IsChartedSubset X →
      Matrices.EmbeddedSubmanifold.IsChartedSubset Y →
      Matrices.EmbeddedSubmanifold.IsChartedSubset Z →
      IsSmoothSubmersion X Y f → IsSmoothSubmersion Y Z g → x₀ ∈ X →
      ∃ (a b c : ℕ) (W : Set (Fin a → ℝ)) (V : Set (Fin b → ℝ)) (U : Set (Fin c → ℝ))
        (w₀ : Fin a → ℝ) (v₀ : Fin b → ℝ) (u₀ : Fin c → ℝ)
        (ε : (Fin a → ℝ) → E₃) (η : (Fin a → ℝ) × (Fin b → ℝ) → E₂)
        (ξ : (Fin a → ℝ) × (Fin b → ℝ) × (Fin c → ℝ) → E₁),
        w₀ ∈ W ∧ v₀ ∈ V ∧ u₀ ∈ U ∧ ξ (w₀, v₀, u₀) = x₀ ∧
        IsOpen W ∧ IsOpen V ∧ IsOpen U ∧
        IsSmoothParametrization Z W ε ∧
        IsSmoothParametrization Y (W ×ˢ V) η ∧
        IsSmoothParametrization X (W ×ˢ V ×ˢ U) ξ ∧
        (∀ w ∈ W, ∀ v ∈ V, g (η (w, v)) = ε w) ∧
        (∀ w ∈ W, ∀ v ∈ V, ∀ u ∈ U, f (ξ (w, v, u)) = η (w, v)) ∧
        (∀ w ∈ W, IsSmoothParametrization (fiber Y g (ε w)) V fun v => η (w, v)) ∧
        (∀ w ∈ W, IsSmoothParametrization (fiber X (g ∘ f) (ε w)) (V ×ˢ U)
          fun p => ξ (w, p)) ∧
        (∀ w ∈ W, ∀ v ∈ V, IsSmoothParametrization (fiber X f (η (w, v))) U
          fun u => ξ (w, v, u)))
end YangMills.Construction.Manifolds
end
