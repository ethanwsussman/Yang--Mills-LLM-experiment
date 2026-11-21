import YangMills.Construction.Matrices.SpecialUnitaryPowerCharts
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.specialUnitaryPower
namespace Composition
def DifferentiableContinuous (σ F : Type) [Fintype σ] [NormedAddCommGroup F]
    [NormedSpace ℝ F] : Prop :=
  ∀ (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → F),
    EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f → ContinuousOn f O
def CoordinateSelectionsDifferentiable (σ τ : Type) [Fintype σ] [Fintype τ] : Prop :=
  ∀ ι : τ → σ, IsDifferentiableInto (specialUnitaryPower σ) fun w t => w (ι t)
def CompDifferentiable (σ τ F : Type) [Fintype σ] [Fintype τ] [NormedAddCommGroup F]
    [NormedSpace ℝ F] : Prop :=
  ∀ (O : Set (σ → ComplexMatrix2)) (g : (σ → ComplexMatrix2) → τ → ComplexMatrix2)
    (O₂ : Set (τ → ComplexMatrix2)) (f : (τ → ComplexMatrix2) → F),
    IsDifferentiableInto O g →
      EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower τ) O₂ f →
      ContinuousOn g O ∧ IsOpenSubset (O ∩ g ⁻¹' O₂) ∧
        EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) (O ∩ g ⁻¹' O₂) (f ∘ g)
def CompositionProperties : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Nonempty σ] [Fintype τ] [Nonempty τ],
    DifferentiableContinuous σ ℂ ∧ DifferentiableContinuous σ ComplexMatrix2 ∧
    CoordinateSelectionsDifferentiable σ τ ∧
    CompDifferentiable σ τ ℂ ∧ CompDifferentiable σ τ ComplexMatrix2
end Composition
end YangMills.Construction.Matrices.specialUnitaryPower
end
