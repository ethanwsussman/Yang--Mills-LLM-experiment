import YangMills.Construction.HilbertSpaces.FormsContractionsSemigroupsAndUnitaryRepresentations
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace HilbertToolkit
open OneLoopNotation ComplexHilbert SesquilinearForms
section Vocabulary
variable {V : Type} [AddCommGroup V] [Module ℂ V]
  {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
structure IsDenseIsometricPair [CompleteSpace X] (q : V → V → ℂ) (cl : V →ₗ[ℂ] X) : Prop where
  denseRange : IsDenseSet (Set.range cl)
  inner_eq : ∀ F F', ⟪cl F, cl F'⟫_ℂ = q F F'
def RepresentsFunctional [CompleteSpace X] (l : X →ₛₗ[starRingEnd ℂ] ℂ) (v : X) : Prop :=
  ∀ χ, l χ = ⟪χ, v⟫_ℂ
def FunctionalRieszProp [CompleteSpace X] (l : X →ₛₗ[starRingEnd ℂ] ℂ) (c : ℝ) : Prop :=
  (∃! v, RepresentsFunctional l v) ∧ ∀ v, RepresentsFunctional l v → ‖v‖ ≤ c
def RepresentsForm [CompleteSpace X] (b : X → X → ℂ) (A : BddOp X) : Prop :=
  ∀ χ χ', ⟪χ, A χ'⟫_ℂ = b χ χ'
def FormRieszProp [CompleteSpace X] (b : X → X → ℂ) (c : ℝ) : Prop :=
  (∃! A, RepresentsForm b A) ∧ ∀ A, RepresentsForm b A → opNormOf A ≤ c
def IsAdjointOp [CompleteSpace X] (A B : BddOp X) : Prop :=
  ∀ χ χ', ⟪B χ, χ'⟫_ℂ = ⟪χ, A χ'⟫_ℂ
def adjointOp [CompleteSpace X] (A : BddOp X) : BddOp X :=
  Classical.epsilon (IsAdjointOp A)
end Vocabulary
def CompletionPart : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (q : V → V → ℂ), IsPosSemidefForm q →
    IsHermitianForm q ∧
    (∀ F F', ‖q F F'‖ ≤ formSeminorm q F * formSeminorm q F') ∧
    (∀ F F', formSeminorm q (F + F') ≤ formSeminorm q F + formSeminorm q F') ∧
    (∃ N : Submodule ℂ V, (N : Set V) = formNullSpace q) ∧
    (∃ (X : Type) (_ : NormedAddCommGroup X) (_ : InnerProductSpace ℂ X) (_ : CompleteSpace X)
      (cl : V →ₗ[ℂ] X), IsDenseIsometricPair q cl) ∧
    ∀ (X X' : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
      [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [CompleteSpace X']
      (cl : V →ₗ[ℂ] X) (cl' : V →ₗ[ℂ] X'), IsDenseIsometricPair q cl → IsDenseIsometricPair q cl' →
        (∀ F F', cl F = cl F' ↔ F - F' ∈ formNullSpace q) ∧
        ∃! W : X →ₗ[ℂ] X', IsUnitaryMap W ∧ ∀ F, W (cl F) = cl' F
def ExtensionPart : Prop :=
  ∀ (X X' : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [CompleteSpace X'],
    (∀ (X₀ : Submodule ℂ X) (c : ℝ) (A₀ : X₀ →ₗ[ℂ] X'),
      IsDenseSet (X₀ : Set X) → 0 ≤ c → (∀ χ, ‖A₀ χ‖ ≤ c * ‖(χ : X)‖) →
        (∃! A : BddOpBetween X X', ∀ χ : X₀, A χ = A₀ χ) ∧
        ∀ A : BddOpBetween X X', (∀ χ : X₀, A χ = A₀ χ) →
          opNormOf A ≤ c ∧
          ((∀ χ, ‖A₀ χ‖ = ‖(χ : X)‖) →
            IsIsometry (A : X →ₗ[ℂ] X') ∧
            (∀ χ χ', ⟪A χ, A χ'⟫_ℂ = ⟪χ, χ'⟫_ℂ) ∧
            IsClosedSet (Set.range A) ∧
            (IsDenseSet (Set.range A₀) → IsUnitaryMap (A : X →ₗ[ℂ] X')))) ∧
    ∀ (A B : BddOpBetween X X') (D : Set X), IsDenseSet D →
      (∀ χ ∈ D, A χ = B χ) → A = B
def DecompositionPart : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X],
    (∀ Y : Submodule ℂ X, IsClosedSet (Y : Set X) →
      (∀ χ : X, ∃! p : X × X, p.1 ∈ Y ∧ p.2 ∈ orthSet (Y : Set X) ∧ χ = p.1 + p.2) ∧
      orthSet (orthSet (Y : Set X)) = (Y : Set X)) ∧
    ∀ Z : Set X,
      (∀ χ, (∀ χ' ∈ orthSet Z, IsOrth χ χ') → χ ∈ closedLinSpan Z) ∧
      (orthSet Z = {0} → IsDenseSet (Submodule.span ℂ Z : Set X))
def FunctionalPart : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (l : X →ₛₗ[starRingEnd ℂ] ℂ) (c : ℝ), 0 ≤ c → (∀ χ, ‖l χ‖ ≤ c * ‖χ‖) →
      FunctionalRieszProp l c
def FormPart : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (b : X → X → ℂ) (c : ℝ), 0 ≤ c → IsSesqForm b → (∀ χ χ', ‖b χ χ'‖ ≤ c * ‖χ‖ * ‖χ'‖) →
      FormRieszProp b c
def AdjointPart : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X],
    (∀ A : BddOp X,
      IsAdjointOp A (adjointOp A) ∧
      (∀ B, IsAdjointOp A B → B = adjointOp A) ∧
      opNormOf (adjointOp A) = opNormOf A ∧
      adjointOp (adjointOp A) = A) ∧
    (∀ A A' : BddOp X, adjointOp (A * A') = adjointOp A' * adjointOp A) ∧
    (∀ (c c' : ℂ) (A A' : BddOp X),
      adjointOp (c • A + c' • A') = conj c • adjointOp A + conj c' • adjointOp A') ∧
    ∀ U : BddOp X, IsUnitaryMap (U : X →ₗ[ℂ] X) → IsTwoSidedInverse U (adjointOp U)
def HilbertCompletionExtensionRiesz : Prop :=
  CompletionPart ∧ ExtensionPart ∧ DecompositionPart ∧ FunctionalPart ∧ FormPart ∧
    AdjointPart
end HilbertToolkit
end YangMills.Construction
