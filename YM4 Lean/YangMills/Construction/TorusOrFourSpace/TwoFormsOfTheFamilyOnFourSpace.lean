import YangMills.Construction.TorusOrFourSpace.ChoiceWithStableEntriesAndUnstableFamily
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.EuclideanFamilyForms
open Kind SupportAdapted StableEntriesUnstableFamily
variable (D : Params)
def nilTuple : Σ n : ℕ, Fin n → Kind.Pt D Kind.euclidean → ℝ := ⟨0, Fin.elim0⟩
def familyWithNil (C : Kind.supportStock D Kind.euclidean → Set (Kind.Pt D Kind.euclidean → ℝ)) :
    Set (Σ n : ℕ, Fin n → Kind.Pt D Kind.euclidean → ℝ) :=
  insert (nilTuple D) (Kind.tupleFamily D Kind.euclidean C)
def sepComponentTuplesWithNil
    (C : Kind.supportStock D Kind.euclidean → Set (Kind.Pt D Kind.euclidean → ℝ)) :
    Set (Σ n : ℕ, Fin n → Kind.Pt D Kind.euclidean → ℝ) :=
  insert (nilTuple D)
    {p | 1 ≤ p.1 ∧ p.2 ∈ Kind.sepC1Tuples D Kind.euclidean p.1 ∧
      ∀ i, p.2 i ∈ Kind.choiceComponents D Kind.euclidean C}
def familyWithNil_subset_and_countable
    (C : Kind.supportStock D Kind.euclidean → Set (Kind.Pt D Kind.euclidean → ℝ)) : Prop :=
  familyWithNil D C ⊆ sepComponentTuplesWithNil D C ∧
    (familyWithNil D C).Countable ∧ (sepComponentTuplesWithNil D C).Countable
def ApproximatesSepTuples
    (C : Kind.supportStock D Kind.euclidean → Set (Kind.Pt D Kind.euclidean → ℝ)) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ f ∈ Kind.sepC1Tuples D Kind.euclidean n,
    ∀ W : Fin n → Set (Kind.Pt D Kind.euclidean), (∀ i, Kind.IsOpenQ D Kind.euclidean (W i)) →
      (∀ i, Kind.supportQ D Kind.euclidean (f i) ⊆ W i) →
      ∃ φ : ℕ+ → Kind.FnTuple D Kind.euclidean n,
        (∀ l, (⟨n, φ l⟩ : Σ n : ℕ, Fin n → Kind.Pt D Kind.euclidean → ℝ) ∈ familyWithNil D C) ∧
        (∀ l, (⟨n, φ l⟩ : Σ n : ℕ, Fin n → Kind.Pt D Kind.euclidean → ℝ) ∈
          sepComponentTuplesWithNil D C) ∧
        (∀ l i, Kind.supportQ D Kind.euclidean (φ l i) ⊆ W i) ∧
        (∀ i, Filter.Tendsto (fun l => SupportAdapted.c1EuclidNorm D Kind.euclidean (φ l i - f i))
          Filter.atTop (nhds 0)) ∧
        ∀ i, Filter.Tendsto (fun l => Kind.sharpNormQ D Kind.euclidean (φ l i - f i))
          Filter.atTop (nhds 0)
def IsErasedChoice (C' : Kind.supportStock D Kind.euclidean → Set (Kind.Pt D Kind.euclidean → ℝ)) :
    Prop :=
  ∃ (C : Kind.supportStock D Kind.euclidean → Set (Kind.Pt D Kind.euclidean → ℝ))
    (φ₀ ψ : Kind.Pt D Kind.euclidean → ℝ),
    Kind.IsCountableDenseChoice D Kind.euclidean C ∧ Kind.HasClosedValues D Kind.euclidean C ∧
      Kind.IsSaturated D Kind.euclidean C ∧ StableEntriesUnstableFamily.IsComponentPair D Kind.euclidean C φ₀ ψ ∧
      C' = StableEntriesUnstableFamily.choiceErase D Kind.euclidean C φ₀
def ExistsStrictGap : Prop :=
  ∃ C' : Kind.supportStock D Kind.euclidean → Set (Kind.Pt D Kind.euclidean → ℝ),
    Kind.IsCountableDenseChoice D Kind.euclidean C' ∧ ¬ Kind.IsSaturated D Kind.euclidean C' ∧
      familyWithNil D C' ⊂ sepComponentTuplesWithNil D C' ∧
      IsErasedChoice D C'
def Statement : Prop :=
  ∀ D : Params,
    (∀ C : Kind.supportStock D Kind.euclidean → Set (Kind.Pt D Kind.euclidean → ℝ),
      Kind.IsCountableDenseChoice D Kind.euclidean C →
        Kind.tupleFamily D Kind.euclidean C = Kind.choiceTupleFamily D Kind.euclidean C ∧
          familyWithNil_subset_and_countable D C ∧
          ApproximatesSepTuples D C) ∧
      ExistsStrictGap D
end YangMills.Construction.PeriodicSpace.EuclideanFamilyForms
