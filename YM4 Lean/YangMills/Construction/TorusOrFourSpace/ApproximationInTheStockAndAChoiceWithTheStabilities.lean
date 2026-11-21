import YangMills.Construction.TorusOrFourSpace.ClosedMembersAndSaturatedChoices
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import YangMills.Construction.TorusOrFourSpace.StandingSignsOfTheSupportAdaptedFamily
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SupportAdapted
open Kind
open PeriodicLattice (SignedFrame)
variable (D : Params) (E : Kind)
abbrev SizedTuple : Type := Σ n : ℕ, Fin n → E.Pt D → ℝ
def ratCombOp : Operation (E.Pt D → ℝ) :=
  fun l => {g | IsRatCombination D E (fun i : Fin l.length => l.get i) g}
def ratCombCommonOp : Operation (E.Pt D → ℝ) :=
  fun l => {g | (∃ Q : supportStock D E, ∀ f ∈ l, SupportedIn D E f (Q : Set (E.Pt D))) ∧
    IsRatCombination D E (fun i : Fin l.length => l.get i) g}
def disjointAppendOp : Operation (SizedTuple D E) :=
  fun l => {z | ∃ p p' : SizedTuple D E, l = [p, p'] ∧ SupportsDisjoint D E p.2 p'.2 ∧
    z = ⟨p.1 + p'.1, appendTuples D E p.2 p'.2⟩}
def frameActSized (w : SignedFrame) (p : SizedTuple D E) : SizedTuple D E :=
  ⟨p.1, frameActTuple D E w p.2⟩
def shiftSized (a : E.Pt D) (p : SizedTuple D E) : SizedTuple D E :=
  ⟨p.1, shiftTuple D E a p.2⟩
def adicPointsQ : Set (E.Pt D) :=
  E.quotMap D '' adicPoints4 D.L
structure IsSymmetricChoice (C : supportStock D E → Set (E.Pt D → ℝ)) : Prop where
  components_frame :
    IsStableUnderAction (frameActFn D E) (Set.univ : Set SignedFrame) (choiceComponents D E C)
  components_shift :
    IsStableUnderAction (shiftFn D E) (adicPointsQ D E) (choiceComponents D E C)
  components_ratComb : IsStableUnder (ratCombOp D E) (choiceComponents D E C)
  family_frame :
    IsStableUnderAction (frameActSized D E) (Set.univ : Set SignedFrame)
      (tupleFamily D E C)
  family_shift :
    IsStableUnderAction (shiftSized D E) (adicPointsQ D E)
      (tupleFamily D E C)
  family_append : IsStableUnder (disjointAppendOp D E) (tupleFamily D E C)
def disjointComponentTuples (C : supportStock D E → Set (E.Pt D → ℝ)) :
    Set (SizedTuple D E) :=
  {p | 1 ≤ p.1 ∧ (∀ i, p.2 i ∈ choiceComponents D E C) ∧
    Pairwise fun i k => Disjoint (supportQ D E (p.2 i)) (supportQ D E (p.2 k))}
def ApproxAndSymmetricChoice : Prop :=
  ∀ (D : Params) (E : Kind),
    (∀ C : supportStock D E → Set (E.Pt D → ℝ), IsCountableDenseChoice D E C →
      ∀ f ∈ c1Set D E, IsCompactQ D E (supportQ D E f) →
      ∀ W : Set (E.Pt D), IsOpenQ D E W → supportQ D E f ⊆ W →
        (∃ Q : supportStock D E,
          supportQ D E f ⊆ (Q : Set (E.Pt D)) ∧ (Q : Set (E.Pt D)) ⊆ W) ∧
        ∀ Q : supportStock D E,
          supportQ D E f ⊆ (Q : Set (E.Pt D)) → (Q : Set (E.Pt D)) ⊆ W →
          f ∈ c1VanishingOutside D E Q ∧
          ∃ φ : ℕ+ → E.Pt D → ℝ, (∀ k, φ k ∈ C Q) ∧
            (∀ k : ℕ+, c1EuclidNorm D E (f - φ k) < ENNReal.ofReal (1 / ((k : ℕ) : ℝ))) ∧
            ∀ k, supportQ D E (φ k) ⊆ (Q : Set (E.Pt D)) ∧ (Q : Set (E.Pt D)) ⊆ W) ∧
    (∃ C : supportStock D E → Set (E.Pt D → ℝ),
      IsCountableDenseChoice D E C ∧ IsSymmetricChoice D E C) ∧
    (∀ C : supportStock D E → Set (E.Pt D → ℝ), IsCountableDenseChoice D E C →
      HasClosedValues D E C → IsSaturated D E C →
        IsSymmetricChoice D E C ∧
        (∀ Q : supportStock D E, C Q = choiceComponents D E C ∩ c1VanishingOutside D E Q) ∧
        tupleFamily D E C = disjointComponentTuples D E C) ∧
    ∀ C : supportStock D E → Set (E.Pt D → ℝ), IsDenseChoice D E C →
      (∀ (p : ℕ) (f : Fin p → E.Pt D → ℝ), (∀ i, f i ∈ choiceComponents D E C) →
        ∃ Q : supportStock D E, ∀ i, SupportedIn D E (f i) (Q : Set (E.Pt D))) ∧
      (IsStableUnder (ratCombOp D E) (choiceComponents D E C) ↔
        IsStableUnder (ratCombCommonOp D E) (choiceComponents D E C))
end YangMills.Construction.PeriodicSpace.SupportAdapted
