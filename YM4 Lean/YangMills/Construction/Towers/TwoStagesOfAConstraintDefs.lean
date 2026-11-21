import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
namespace ConstraintStages
variable {E F F' : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
def restrictToInnerKernel (M : E →ₗ[ℝ] F) (N : F →ₗ[ℝ] F')
    (T : QuadraticForm ℝ (LinearMap.ker (N ∘ₗ M))) : QuadraticForm ℝ (LinearMap.ker M) :=
  T.comp (Submodule.inclusion (LinearMap.ker_le_ker_comp M N))
def IsFiberwiseMinimum (M : E →ₗ[ℝ] F) (N : F →ₗ[ℝ] F')
    (T : QuadraticForm ℝ (LinearMap.ker (N ∘ₗ M))) (Q : LinearMap.ker N → ℝ) : Prop :=
  ∀ ζ : LinearMap.ker N,
    IsLeast {t | ∃ ξ : LinearMap.ker (N ∘ₗ M), M (ξ : E) = (ζ : F) ∧ T ξ = t} (Q ζ)
end ConstraintStages
namespace Manifolds
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
def IsSmoothOnOpen (M O : Set E) (f : E → E') : Prop :=
  Matrices.ComplexMatrix2.IsRelativelyOpen M O ∧
    ∀ c : Matrices.EmbeddedSubmanifold.Chart M, ContDiffOn ℝ ∞ (c.pullback f) (c.coords O)
structure IsSmoothSubmersion (M : Set E) (M' : Set E') (m : E → E') : Prop where
  mapsTo : MapsTo m M M'
  smooth : IsSmoothOnOpen M M m
  differential_surjective : ∀ x ∈ M,
    LinearMap.range (Matrices.EmbeddedSubmanifold.tangentDifferential M m x) =
      Matrices.EmbeddedSubmanifold.tangentSpace M' (m x)
def fiber (M : Set E) (m : E → E') (y : E') : Set E := {x ∈ M | m x = y}
def IsSmoothParametrization {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (N : Set E) (O : Set P) (φ : P → E) : Prop :=
  Matrices.EmbeddedSubmanifold.IsC2Parametrization N O φ ∧ ContDiffOn ℝ ∞ φ O
end Manifolds
end YangMills.Construction
end
