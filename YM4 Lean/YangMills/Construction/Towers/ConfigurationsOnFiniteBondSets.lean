import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Matrices.GroupLieProducts
import YangMills.Construction.Matrices.SpecialUnitaryPowerCharts
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.BondSetFields
variable {β : Type}
def restrictTo (P : Set β) (U : β → Matrices.ComplexMatrix2) : P → Matrices.ComplexMatrix2 :=
  fun b => U b.1
def fieldsOn (IsField : Set β → (β → Matrices.ComplexMatrix2) → Prop) (P : Set β) :
    Set (P → Matrices.ComplexMatrix2) :=
  {w | ∃ U, IsField P U ∧ w = restrictTo P U}
def positivePart (pos : β → Prop) (P : Set β) : Set β := {b | b ∈ P ∧ pos b}
def readPositive (pos : β → Prop) (P : Set β) (V : P → Matrices.ComplexMatrix2) :
    positivePart pos P → Matrices.ComplexMatrix2 :=
  fun b => V ⟨b.1, b.2.1⟩
def nearIdentity {P : Set β} (C : Set (P → Matrices.ComplexMatrix2)) (ε : ℝ) :
    Set (P → Matrices.ComplexMatrix2) :=
  {V | V ∈ C ∧ ∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ε}
def PositivePartCovers (rev : β → β) (pos : β → Prop) (P : Set β) : Prop :=
  (positivePart pos P).Finite ∧ (positivePart pos P).Nonempty ∧
    ∀ b ∈ P, Xor (b ∈ positivePart pos P) (∃! c, c ∈ positivePart pos P ∧ rev c = b)
def IsReadByPositivePart (pos : β → Prop) (P : Set β) (C : Set (P → Matrices.ComplexMatrix2))
    (T : Set (positivePart pos P → Matrices.ComplexMatrix2)) : Prop :=
  BijOn (readPositive pos P) C T ∧
    ContinuousOn (readPositive pos P) C ∧
    ContinuousOn (Function.invFunOn (readPositive pos P) C) T ∧
    (∀ O, O ⊆ C → (Matrices.ComplexMatrix2.IsRelativelyOpen C O ↔
      Matrices.ComplexMatrix2.IsRelativelyOpen T (readPositive pos P '' O))) ∧
    ∀ ε : ℝ, 0 < ε → Matrices.ComplexMatrix2.IsRelativelyOpen C (nearIdentity C ε) ∧
      Matrices.ComplexMatrix2.IsRelativelyOpen T (readPositive pos P '' nearIdentity C ε)
def ProductStructureAt (rev : β → β) (pos : β → Prop)
    (IsField : Set Matrices.ComplexMatrix2 → Set β → (β → Matrices.ComplexMatrix2) → Prop)
    (P : Set β) : Prop :=
  PositivePartCovers rev pos P ∧
    IsReadByPositivePart pos P (fieldsOn (IsField PeriodicLattice.complexGaugeGroup) P)
      (Matrices.GroupLieProduct.unimodularPi (positivePart pos P)) ∧
    IsReadByPositivePart pos P (fieldsOn (IsField PeriodicLattice.compactGaugeGroup) P)
      (Matrices.specialUnitaryPower (positivePart pos P))
def readAllPositive {L n k j : ℕ} (U : Tower.Edge L n k j → Matrices.ComplexMatrix2) :
    PeriodicLattice.PositivelyOrientedBond L n (PeriodicLattice.levelDepth k j) →
      Matrices.ComplexMatrix2 :=
  fun b => U b.1
def FullLatticeProductStructure (L n k j : ℕ) : Prop :=
  (univ : Set (Tower.Edge L n k j)).Finite ∧
    (univ : Set (Tower.Edge L n k j)).Nonempty ∧
    PeriodicLattice.IsReversalClosed (univ : Set (Tower.Edge L n k j)) ∧
    fieldsOn (PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup) univ =
      restrictTo (univ : Set (Tower.Edge L n k j)) '' Tower.fieldSpace L n k j ∧
    positivePart PeriodicLattice.Bond.IsPositivelyOriented univ =
      {b : Tower.Edge L n k j | b.IsPositivelyOriented} ∧
    (∀ O, O ⊆ Tower.fieldSpace L n k j →
      (Matrices.ComplexMatrix2.IsRelativelyOpen (Tower.fieldSpace L n k j) O ↔
        Matrices.ComplexMatrix2.IsRelativelyOpen
          (fieldsOn (PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup) univ)
          (restrictTo (univ : Set (Tower.Edge L n k j)) '' O))) ∧
    (∀ O, O ⊆ PeriodicLattice.complexGaugeFields (univ : Set (Tower.Edge L n k j)) →
      (Matrices.ComplexMatrix2.IsRelativelyOpen (PeriodicLattice.complexGaugeFields univ) O ↔
        Matrices.ComplexMatrix2.IsRelativelyOpen
          (fieldsOn (PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup) univ)
          (restrictTo (univ : Set (Tower.Edge L n k j)) '' O))) ∧
    (∀ O, O ⊆ Tower.fieldSpace L n k j →
      (Matrices.ComplexMatrix2.IsRelativelyOpen (Tower.fieldSpace L n k j) O ↔
        Matrices.ComplexMatrix2.IsRelativelyOpen
          (Matrices.specialUnitaryPower
            (PeriodicLattice.PositivelyOrientedBond L n (PeriodicLattice.levelDepth k j)))
          (readAllPositive '' O))) ∧
    ∀ O, O ⊆ PeriodicLattice.complexGaugeFields (univ : Set (Tower.Edge L n k j)) →
      (Matrices.ComplexMatrix2.IsRelativelyOpen (PeriodicLattice.complexGaugeFields univ) O ↔
        Matrices.ComplexMatrix2.IsRelativelyOpen
          (Matrices.GroupLieProduct.unimodularPi
            (PeriodicLattice.PositivelyOrientedBond L n (PeriodicLattice.levelDepth k j)))
          (readAllPositive '' O))
def ProductStructureHolds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    (∀ n : ℕ, 1 ≤ n →
      (∀ P : Set (Tower.Edge L n k j), P.Finite → P.Nonempty →
        PeriodicLattice.IsReversalClosed P →
          ProductStructureAt PeriodicLattice.Bond.opposite
            PeriodicLattice.Bond.IsPositivelyOriented PeriodicLattice.IsGaugeField P) ∧
        FullLatticeProductStructure L n k j) ∧
    ∀ P : Set (Tower.FullSpace.Edge L k j), P.Finite → P.Nonempty →
      (∀ b ∈ P, b.opposite ∈ P) →
        ProductStructureAt InfiniteLattice.Link.opposite
          InfiniteLattice.Link.IsPositivelyOriented Tower.FullSpace.IsFieldOn P
end YangMills.Construction.Tower.BondSetFields
end
