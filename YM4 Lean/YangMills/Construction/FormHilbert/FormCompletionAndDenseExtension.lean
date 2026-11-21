import YangMills.Construction.HilbertSpace.FormCompletionsAndBorelPVMs
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.FormHilbert
open HilbertSpace
namespace DenseExtension
def IsClosedSubmoduleSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (M : Set H) : Prop :=
  IsClosed M ∧ ∃ N : Submodule ℂ H, (N : Set H) = M
def IsUnitaryOntoClosure {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (A : H →L[ℂ] H') (R : Set H') : Prop :=
  (∀ x y, inner ℂ (A x) (A y) = inner ℂ x y) ∧
  Set.range A = closure R ∧
  ∃ M : Submodule ℂ H', (M : Set H') = closure R ∧ IsClosed (M : Set H') ∧
    ∃ U : H →ₗ[ℂ] M, IsUnitaryLinearMap U ∧ ∀ x, (U x : H') = A x
section Forms
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def SesqFormCauchySchwarz (b : SesqForm V) : Prop :=
  b.IsConjSymm ∧
  (∀ u v, ‖b u v‖ ^ 2 ≤ (b u u).re * (b v v).re) ∧
  ∃ p : Seminorm ℂ V, ∀ u, p u = b.diagSqrt u
def FormCompletionClasses (b : SesqForm V) : Prop :=
  CompleteSpace (FormCompletion b) ∧
  IsLinearMap ℂ (formClass b) ∧
  (∀ u v, inner ℂ (formClass b u) (formClass b v) = b u v) ∧
  ∃ M : Submodule ℂ (FormCompletion b),
    (M : Set (FormCompletion b)) = Set.range (formClass b) ∧
    Dense (M : Set (FormCompletion b))
def ExtendsFromFormClasses (b : SesqForm V) (H' : Type*) [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] : Prop :=
  ∀ (c : ℝ) (a : V →ₗ[ℂ] H'), 0 ≤ c → (∀ u, ‖a u‖ ^ 2 ≤ c ^ 2 * (b u u).re) →
    (∃! A : FormCompletion b →L[ℂ] H', ∀ u, A (formClass b u) = a u) ∧
    ∀ A : FormCompletion b →L[ℂ] H', (∀ u, A (formClass b u) = a u) →
      ‖A‖ ≤ c ∧
      ((∀ u, ‖a u‖ ^ 2 = (b u u).re) → IsUnitaryOntoClosure A (Set.range a))
end Forms
section Operators
variable (H H' : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
def ExtendsFromDenseSubmodule : Prop :=
  ∀ (D : Submodule ℂ H) (c : ℝ) (a : D →ₗ[ℂ] H'), Dense (D : Set H) → 0 ≤ c →
    (∀ x : D, ‖a x‖ ≤ c * ‖(x : H)‖) →
    (∃! A : H →L[ℂ] H', ∀ x : D, A x = a x) ∧
    ∀ A : H →L[ℂ] H', (∀ x : D, A x = a x) →
      ‖A‖ ≤ c ∧
      ((∀ x : D, ‖a x‖ = ‖(x : H)‖) → IsUnitaryOntoClosure A (Set.range a))
def PolarizationBounded : Prop :=
  (∀ (A : H →L[ℂ] H) (x y : H),
    inner ℂ y (A x) = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4, Complex.I ^ k *
      inner ℂ (x + Complex.I ^ k • y) (A (x + Complex.I ^ k • y))) ∧
  (∀ A : H →L[ℂ] H, (∀ x, inner ℂ x (A x) = 0) → A = 0) ∧
  ∀ (A : H →L[ℂ] H) (ε : ℝ), 0 ≤ ε → (∀ x, ‖inner ℂ x (A x)‖ ≤ ε * ‖x‖ ^ 2) → ‖A‖ ≤ 2 * ε
def OrthProjRangeKer [CompleteSpace H] : Prop :=
  (∀ P : H →L[ℂ] H, IsStarProjection P →
    Set.range P = {x | P x = x} ∧
    IsClosedSubmoduleSet (Set.range P) ∧
    (∀ x, ‖P x‖ ≤ ‖x‖) ∧
    IsStarProjection (1 - P) ∧
    Set.range (1 - P : H →L[ℂ] H) = {x | P x = 0} ∧
    {x | P x = 0} = orthSet (Set.range P)) ∧
  ∀ P Q : H →L[ℂ] H, IsStarProjection P → IsStarProjection Q → Set.range P = Set.range Q → P = Q
def SelfAdjointCriteria [CompleteSpace H] : Prop :=
  (∀ (A : H →L[ℂ] H) (D : Submodule ℂ H), Dense (D : Set H) →
    (∀ x ∈ D, ∀ y ∈ D, inner ℂ x (A y) = inner ℂ (A x) y) →
      IsSelfAdjoint A ∧ ((∀ x ∈ D, 0 ≤ inner ℂ x (A x)) → 0 ≤ A)) ∧
  (∀ A B : H →L[ℂ] H, IsSelfAdjoint A → IsSelfAdjoint B → Commute A B → IsSelfAdjoint (A * B)) ∧
  ∀ J : H →L[ℂ] H, IsSelfAdjoint J → J * J = 1 → 0 ≤ J → J = 1
end Operators
def FormCompletionAndExtensionTheorem : Prop :=
  ∀ (V H H' : Type) [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (b : SesqForm V),
    IsPosSesqForm b →
    SesqFormCauchySchwarz b ∧
    FormCompletionClasses b ∧
    ExtendsFromDenseSubmodule H H' ∧
    ExtendsFromFormClasses b H' ∧
    PolarizationBounded H ∧
    OrthProjRangeKer H ∧
    SelfAdjointCriteria H
end DenseExtension
end YangMills.Construction.FormHilbert
