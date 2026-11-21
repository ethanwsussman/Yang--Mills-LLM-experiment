import YangMills.Construction.TorusOrFourSpace.ClosedMembersAndSaturatedChoices
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import YangMills.Construction.TorusOrFourSpace.StandingSignsOfTheSupportAdaptedFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.StableEntriesUnstableFamily
open PeriodicLattice (SignedFrame)
open Kind SupportAdapted
def outerBox : RationalBox where
  lo := fun _ => 1 / 4
  hi := fun _ => 1 / 2
  lo_lt_hi := fun _ => by norm_num
def leftSlab : RationalBox where
  lo := fun _ => 1 / 4
  hi := ![5 / 16, 1 / 2, 1 / 2, 1 / 2]
  lo_lt_hi := fun j => by fin_cases j <;> norm_num
def rightSlab : RationalBox where
  lo := ![3 / 8, 1 / 4, 1 / 4, 1 / 4]
  hi := fun _ => 1 / 2
  lo_lt_hi := fun j => by fin_cases j <;> norm_num
def e1 : Fin 4 → ℝ := ![1, 0, 0, 0]
def negFrame : SignedFrame := (1, fun _ => -1)
variable (D : Params) (E : Kind)
def boxImage (b : RationalBox) : Set (E.Pt D) := E.quotMap D '' b.toSet
def choiceAt (C : supportStock D E → Set (E.Pt D → ℝ)) (A : Set (E.Pt D)) :
    Set (E.Pt D → ℝ) :=
  {f | ∃ hA : A ∈ supportStock D E, f ∈ C ⟨A, hA⟩}
open Classical in
def choiceErase (C : supportStock D E → Set (E.Pt D → ℝ)) (g : E.Pt D → ℝ) :
    supportStock D E → Set (E.Pt D → ℝ) :=
  fun Q => if (Q : Set (E.Pt D)) = boxImage D E outerBox then C Q else C Q \ {g}
def disjointTuplesOf (S : Set (E.Pt D → ℝ)) :
    Set (Σ n : ℕ, Fin n → E.Pt D → ℝ) :=
  {t | 1 ≤ t.1 ∧ (∀ i, t.2 i ∈ S) ∧
    Pairwise fun i k => Disjoint (supportQ D E (t.2 i)) (supportQ D E (t.2 k))}
def negEquiv : E.Pt D ≃ E.Pt D := Equiv.neg (E.Pt D)
def shiftE1 : E.Pt D ≃ E.Pt D :=
  Equiv.addRight (E.quotMap D e1)
def SlabsInOuterBox : Prop :=
  E.AdmitsBox D outerBox ∧ E.AdmitsBox D leftSlab ∧ E.AdmitsBox D rightSlab ∧
    Set.InjOn (E.quotMap D) outerBox.toSet ∧
    boxImage D E leftSlab ∩ boxImage D E rightSlab = ∅ ∧
    boxImage D E leftSlab ∪ boxImage D E rightSlab ⊆ boxImage D E outerBox ∧
    c1VanishingOutside D E (boxImage D E leftSlab) ≠ {0} ∧
    c1VanishingOutside D E (boxImage D E rightSlab) ≠ {0}
def IsComponentPair (C : supportStock D E → Set (E.Pt D → ℝ))
    (g h : E.Pt D → ℝ) : Prop :=
  g ∈ choiceAt D E C (boxImage D E leftSlab) \ {0} ∧
    h ∈ choiceAt D E C (boxImage D E rightSlab) \ {0}
def ElementPairExists (C : supportStock D E → Set (E.Pt D → ℝ)) : Prop :=
  (∃ g h, IsComponentPair D E C g h) ∧
    ∀ g h, IsComponentPair D E C g h →
      (supportQ D E g).Nonempty ∧ (supportQ D E h).Nonempty ∧
        Disjoint (supportQ D E g) (supportQ D E h) ∧
        g ∈ choiceAt D E C (boxImage D E outerBox)
def ErasedClosedNotSaturated (C : supportStock D E → Set (E.Pt D → ℝ))
    (g : E.Pt D → ℝ) : Prop :=
  IsCountableDenseChoice D E (choiceErase D E C g) ∧
    choiceComponents D E (choiceErase D E C g) = choiceComponents D E C ∧
    HasClosedValues D E (choiceErase D E C g) ∧
    ¬ IsSaturated D E (choiceErase D E C g) ∧
    choiceAt D E (choiceErase D E C g) (boxImage D E leftSlab) ≠
      choiceComponents D E C ∩ c1VanishingOutside D E (boxImage D E leftSlab)
def AppendNotInFamily (C : supportStock D E → Set (E.Pt D → ℝ))
    (g h : E.Pt D → ℝ) : Prop :=
  (⟨1, ![g]⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈
      choiceTupleFamily D E (choiceErase D E C g) ∧
    (∃ Q : Fin 1 → supportStock D E, (Q 0 : Set (E.Pt D)) = boxImage D E outerBox ∧
      IsBuiltFrom D E (choiceErase D E C g) ![g] Q) ∧
    (⟨1, ![h]⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈
      choiceTupleFamily D E (choiceErase D E C g) ∧
    (∃ Q : Fin 1 → supportStock D E, (Q 0 : Set (E.Pt D)) = boxImage D E rightSlab ∧
      IsBuiltFrom D E (choiceErase D E C g) ![h] Q) ∧
    SupportsDisjoint D E (n := 1) (m := 1) ![g] ![h] ∧
    (⟨1 + 1, appendTuples D E (n := 1) (m := 1) ![g] ![h]⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∉
      choiceTupleFamily D E (choiceErase D E C g) ∧
    choiceTupleFamily D E (choiceErase D E C g) ⊂
      disjointTuplesOf D E (choiceComponents D E C)
def PushedPairWitness (C : supportStock D E → Set (E.Pt D → ℝ))
    (g h : E.Pt D → ℝ) (r : E.Pt D ≃ E.Pt D) : Prop :=
  ⇑r ∈ adicIsometriesQ D E ∧
    r '' boxImage D E outerBox ∩ boxImage D E outerBox = ∅ ∧
    (⟨2, pushTuple D E r ![g, h]⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈
      choiceTupleFamily D E (choiceErase D E C g) ∧
    ⇑r.symm ∈ adicIsometriesQ D E ∧
    pushTuple D E r.symm (pushTuple D E r ![g, h]) = ![g, h] ∧
    (⟨2, ![g, h]⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∉
      choiceTupleFamily D E (choiceErase D E C g)
def MapsInduced : Prop :=
  InducedBy D E negFrame.actOnVector (negEquiv D E) ∧
    e1 ∈ adicPoints4 D.L ∧
    InducedBy D E (translateR4 e1) (shiftE1 D E)
def FamilyNotStable (C : supportStock D E → Set (E.Pt D → ℝ))
    (g : E.Pt D → ℝ) : Prop :=
  ¬ IsStableUnderAction
      (fun (w : SignedFrame) (t : Σ n : ℕ, Fin n → E.Pt D → ℝ) =>
        (⟨t.1, frameActTuple D E w t.2⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ))
      Set.univ (choiceTupleFamily D E (choiceErase D E C g)) ∧
    ¬ IsStableUnderAction
      (fun (a : E.Pt D) (t : Σ n : ℕ, Fin n → E.Pt D → ℝ) =>
        (⟨t.1, shiftTuple D E a t.2⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ))
      (E.quotMap D '' adicPoints4 D.L)
      (choiceTupleFamily D E (choiceErase D E C g))
def Statement : Prop :=
  ∀ (D : Params) (E : Kind) (C : supportStock D E → Set (E.Pt D → ℝ)),
    IsCountableDenseChoice D E C → HasClosedValues D E C → IsSaturated D E C →
      SlabsInOuterBox D E ∧ ElementPairExists D E C ∧ MapsInduced D E ∧
        ∀ g h, IsComponentPair D E C g h →
          ErasedClosedNotSaturated D E C g ∧
            AppendNotInFamily D E C g h ∧
            PushedPairWitness D E C g h (negEquiv D E) ∧
            PushedPairWitness D E C g h (shiftE1 D E) ∧
            FamilyNotStable D E C g
end YangMills.Construction.PeriodicSpace.StableEntriesUnstableFamily
