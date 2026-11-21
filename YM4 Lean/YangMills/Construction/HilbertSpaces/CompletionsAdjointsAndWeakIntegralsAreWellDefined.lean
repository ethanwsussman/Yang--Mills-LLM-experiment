import YangMills.Construction.HilbertSpaces.CompletionsAdjointsProjectionValuedMeasuresAndWeakIntegrals
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.HilbertWellDefined
open OneLoopNotation ComplexHilbert SesquilinearForms HilbertToolkit ProjectionMeasures
def FormPairCondition : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (form : V → V → ℂ), IsPosSemidefForm form →
    FormCompletion.IsPosSemidefHermitianForm form ∧
    ∃ j : V →ₗ[ℂ] FormQuotientCompletion form,
      (∀ v, j v = quotientClass form v) ∧ IsDenseIsometricPair form j
def AdjointSelfAdjointCondition : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : BddOp H), adjointOp T = T ↔ IsSymmetricOp T
def IntegralIndependence : Prop :=
  ∀ (ν : FourBorelSet → ℂ) (f : (Fin 4 → ℝ) → ℂ), IsFinComplexMeasure ν → IsBddMeasurableFun f →
    (∃ w, IsDecompIntegral ν f w) ∧ ∀ w, IsDecompIntegral ν f w → w = complexMeasureIntegral ν f
def WeakIntegralUnique : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X : Type) [TopologicalSpace X] [MeasureSpace X] [OpensMeasurableSpace X]
    (S : Set X) (Ψ : X → H) (g : X → ℂ), HasWeakIntegrandData S Ψ g →
      HasWeakIntegral S Ψ g (weakInt S Ψ g) ∧
      ∀ v, HasWeakIntegral S Ψ g v → v = weakInt S Ψ g
def WellDefinedStatement : Prop :=
  FormPairCondition ∧ AdjointSelfAdjointCondition ∧ IntegralIndependence ∧ WeakIntegralUnique
end YangMills.Construction.HilbertWellDefined
