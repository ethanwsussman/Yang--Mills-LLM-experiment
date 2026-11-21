import YangMills.Construction.TorusOrFourSpace.ClosedMembersAndSaturatedChoices
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SaturatedChoices
variable (D : Params) (E : Kind)
def disjointComponentTuples
    (C : Kind.supportStock D E → Set (E.Pt D → ℝ)) :
    Set (Σ n : ℕ, Fin n → E.Pt D → ℝ) :=
  {p | 1 ≤ p.1 ∧ (∀ i, p.2 i ∈ Kind.choiceComponents D E C) ∧
    ∀ i k, i ≠ k → Kind.supportQ D E (p.2 i) ∩ Kind.supportQ D E (p.2 k) = ∅}
def IsAdicIsometryInvariant (S : Set (Σ n : ℕ, Fin n → E.Pt D → ℝ)) : Prop :=
  ∀ g : E.Pt D ≃ E.Pt D, ⇑g ∈ Kind.adicIsometriesQ D E →
    ∀ p ∈ S, (⟨p.1, Kind.pushTuple D E g p.2⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ S
def IsClosedUnderAppend (S : Set (Σ n : ℕ, Fin n → E.Pt D → ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, Kind.SupportsDisjoint D E p.2 q.2 →
    (⟨p.1 + q.1, Kind.appendTuples D E p.2 q.2⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ S
def ExistsCountableClosedSaturatedChoice : Prop :=
  ∃ C : Kind.supportStock D E → Set (E.Pt D → ℝ),
    Kind.IsCountableDenseChoice D E C ∧ Kind.HasClosedValues D E C ∧ Kind.IsSaturated D E C
def SaturatedFamilyEqDisjointEntryTuples : Prop :=
  ∀ C : Kind.supportStock D E → Set (E.Pt D → ℝ),
    Kind.IsDenseChoice D E C → Kind.IsSaturated D E C →
      Kind.choiceTupleFamily D E C = disjointComponentTuples D E C
def ChoiceSetsAreRatSubmodules
    (C : Kind.supportStock D E → Set (E.Pt D → ℝ)) : Prop :=
  ∀ Q, ∃ V : Submodule ℚ (E.Pt D → ℝ), (V : Set (E.Pt D → ℝ)) = C Q
def ChoiceSetsEquivariant
    (C : Kind.supportStock D E → Set (E.Pt D → ℝ)) : Prop :=
  ∀ g : E.Pt D ≃ E.Pt D, ⇑g ∈ Kind.adicIsometriesQ D E →
    ∀ Q : Kind.supportStock D E, ∃ hQ : g '' Q.1 ∈ Kind.supportStock D E,
      Kind.pushFn D E g '' C Q = C ⟨g '' Q.1, hQ⟩
def ClosedSaturatedChoiceStable : Prop :=
  ∀ C : Kind.supportStock D E → Set (E.Pt D → ℝ),
    Kind.IsDenseChoice D E C → Kind.HasClosedValues D E C → Kind.IsSaturated D E C →
      ChoiceSetsAreRatSubmodules D E C ∧
        ChoiceSetsEquivariant D E C ∧
        IsAdicIsometryInvariant D E (Kind.choiceTupleFamily D E C) ∧
        IsClosedUnderAppend D E (Kind.choiceTupleFamily D E C)
def ListingsEquivariant : Prop :=
  ∀ C : Kind.supportStock D E → Set (E.Pt D → ℝ),
    Kind.IsDenseChoice D E C → Kind.HasClosedValues D E C → Kind.IsSaturated D E C →
      ∀ g : E.Pt D ≃ E.Pt D, ⇑g ∈ Kind.adicIsometriesQ D E →
        ∀ (n : ℕ) (φ : Fin n → E.Pt D → ℝ) (Q : Fin n → Set (E.Pt D)),
          (⟨n, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ Kind.choiceTupleFamily D E C →
          Kind.IsListedOver D E C φ Q →
            Kind.IsListedOver D E C (Kind.pushTuple D E g φ) (fun i => g '' Q i) ∧
              ∀ i k, i ≠ k →
                Kind.setInfDist D E (g '' Q i) (g '' Q k) = Kind.setInfDist D E (Q i) (Q k)
def ClosedChoiceDisjointTuplesStable : Prop :=
  ∀ C : Kind.supportStock D E → Set (E.Pt D → ℝ),
    Kind.IsDenseChoice D E C → Kind.HasClosedValues D E C →
      IsAdicIsometryInvariant D E (disjointComponentTuples D E C) ∧
        IsClosedUnderAppend D E (disjointComponentTuples D E C)
def Claim : Prop :=
  ∀ (D : Params) (E : Kind),
    ExistsCountableClosedSaturatedChoice D E ∧ SaturatedFamilyEqDisjointEntryTuples D E ∧
      ClosedSaturatedChoiceStable D E ∧ ListingsEquivariant D E ∧
      ClosedChoiceDisjointTuplesStable D E
end YangMills.Construction.PeriodicSpace.SaturatedChoices
