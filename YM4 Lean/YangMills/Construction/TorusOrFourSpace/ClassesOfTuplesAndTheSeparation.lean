import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TupleClasses
open YangMills.Construction.PeriodicSpace YangMills.Construction.PeriodicSpace.Kind
variable (P : Params) (Y : Kind)
def LipTuplesMonotone (n : ℕ) : Prop :=
  ∀ d' d R R' : ℝ, 0 < d' → d' ≤ d → R ∈ allowedRadii P Y → R' ∈ allowedRadii P Y → R ≤ R' →
    lipTuplesSpacedInBalls P Y n d R ⊆ lipTuplesSpacedInBalls P Y n d' R'
def SupportGapPos (n : ℕ) : Prop :=
  2 ≤ n → ∀ h ∈ sepLipTuples P Y n, supportGap P Y h ∈ Set.Ioc (0 : ℝ≥0∞) ∞
def SupportsAtMostOneNonempty {n : ℕ} (h : FnTuple P Y n) : Prop :=
  {i | (supportQ P Y (h i)).Nonempty}.Subsingleton
def SupportGapTopIff (n : ℕ) : Prop :=
  2 ≤ n → ∀ h ∈ sepLipTuples P Y n,
    (supportGap P Y h = ∞ ↔ SupportsAtMostOneNonempty P Y h) ∧
      (SupportsAtMostOneNonempty P Y h → ∃ i, ∀ y, h i y = 0)
def SepC1TupleInBall (n : ℕ) : Prop :=
  ∀ f ∈ sepC1Tuples P Y n, ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ρ < ∞ ∧
    f ∈ sepC1TuplesWithin P Y n (centredBall P Y ρ)
def SepC1TupleRestrictPerm (n : ℕ) : Prop :=
  ∀ f ∈ sepC1Tuples P Y n,
    (∀ J : Finset (Fin n), J.Nonempty → restrictTuple P Y f J ∈ sepC1Tuples P Y J.card) ∧
      ∀ σ : Equiv.Perm (Fin n), (fun i => f (σ i)) ∈ sepC1Tuples P Y n
def Statement : Prop :=
  ∀ (P : Params) (Y : Kind) (n : ℕ), 1 ≤ n →
    LipTuplesMonotone P Y n ∧
    SupportGapPos P Y n ∧
    SupportGapTopIff P Y n ∧
    SepC1TupleInBall P Y n ∧
    SepC1TupleRestrictPerm P Y n
end YangMills.Construction.PeriodicSpace.TupleClasses
