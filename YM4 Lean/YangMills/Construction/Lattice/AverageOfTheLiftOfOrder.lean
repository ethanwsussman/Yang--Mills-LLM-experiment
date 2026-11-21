import YangMills.Construction.Lattice.AverageOfAConfigurationTrivialInsideTwoBlocks
import YangMills.Construction.Lattice.TwoCasesOfTheLiftOfOrder
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K k : ℕ}
def orderLiftAsPartialField (j : ℕ) (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    PartialGaugeField L m (levelDepth K j) where
  support := bondsInsideOrOverCoarse j S
  field := orderLift j V
def ExactlyOneStepCase {j : ℕ} (S : Set (BondAtLevel L m K k))
    (e : BondAtLevel L m K (j + 1)) : Prop :=
  (IsInsideSomeBlock k e ∧ ¬(∃ c ∈ S, CoversBond c e) ∧
      ¬(∃ c, c ∉ S ∧ CoversBond c e)) ∨
    (¬IsInsideSomeBlock k e ∧ (∃ c ∈ S, CoversBond c e) ∧
      ¬(∃ c, c ∉ S ∧ CoversBond c e)) ∨
    (¬IsInsideSomeBlock k e ∧ ¬(∃ c ∈ S, CoversBond c e) ∧
      ∃ c, c ∉ S ∧ CoversBond c e)
def StepCaseInsideBlock {j : ℕ} (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (e : BondAtLevel L m K (j + 1)) : Prop :=
  ∀ y : SiteAtLevel L m K k, IsInsideBlockAt (j + 1) y e →
    e ∈ bondsInsideOrOverCoarse (j + 1) S ∧
      (∀ b ∈ (bondsInDoubleBlock e : Set (BondAtLevel L m K j)), IsInsideBlockAt j y b) ∧
      (bondsInDoubleBlock e : Set (BondAtLevel L m K j)) ⊆ bondsInsideOrOverCoarse j S ∧
      ∀ b ∈ (bondsInDoubleBlock e : Set (BondAtLevel L m K j)),
        orderLift j V b = twoBlockFieldValues (levelDepth K j) e 1 b
def StepCaseOverBond {j : ℕ} (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (e : BondAtLevel L m K (j + 1)) : Prop :=
  ∀ c ∈ S, CoversBond c e →
    e ∈ bondsInsideOrOverCoarse (j + 1) S ∧
      (∀ b ∈ (bondsInside (unitBlock e.source) : Set (BondAtLevel L m K j)),
        IsInsideBlockAt j c.source b) ∧
      (∀ b ∈ (bondsInside (unitBlock e.target) : Set (BondAtLevel L m K j)),
        IsInsideBlockAt j c.target b) ∧
      (∀ b ∈ (bondCorridor e : Set (BondAtLevel L m K j)),
        CoversBond c b ∧ CoversBond c.opposite b.opposite) ∧
      (bondsInDoubleBlock e : Set (BondAtLevel L m K j)) ⊆ bondsInsideOrOverCoarse j S ∧
      (∀ b ∈ (bondsInDoubleBlock e : Set (BondAtLevel L m K j)),
        orderLift j V b = twoBlockFieldValues (levelDepth K j) e (V c) b) ∧
      ∀ (S' : Set (BondAtLevel L m K k)) (V' : BondAtLevel L m K k → Matrices.ComplexMatrix2),
        IsReversalClosed S' → IsGaugeField complexGaugeGroup S' V' → c ∈ S' →
        V' c = V c → V' c.opposite = V c.opposite →
        ∀ b ∈ (bondsInDoubleBlock e : Set (BondAtLevel L m K j)),
          orderLift j V' b = orderLift j V b
def StepCaseOverAbsentBond {j : ℕ} (S : Set (BondAtLevel L m K k))
    (e : BondAtLevel L m K (j + 1)) : Prop :=
  ∀ c, c ∉ S → CoversBond c e →
    e ∉ bondsInsideOrOverCoarse (j + 1) S ∧
      (bondCorridor e : Set (BondAtLevel L m K j)).Nonempty ∧
      (∀ b ∈ (bondCorridor e : Set (BondAtLevel L m K j)), b ∉ bondsInsideOrOverCoarse j S) ∧
      ¬(bondsInDoubleBlock e : Set (BondAtLevel L m K j)) ⊆ bondsInsideOrOverCoarse j S
def ComplexAverageOfOrderLift (j : ℕ) (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  (complexPartialBlockAverage (orderLiftAsPartialField j S V) :
      PartialGaugeField L m (levelDepth K (j + 1))).support = bondsInsideOrOverCoarse (j + 1) S ∧
    ∀ e ∈ bondsInsideOrOverCoarse (j + 1) S,
      (complexPartialBlockAverage (orderLiftAsPartialField j S V) :
        PartialGaugeField L m (levelDepth K (j + 1))).field e = orderLift (j + 1) V e
def CompactAverageOfOrderLift (ω : ℝ) (j : ℕ) (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  (realPartialBlockAverage ω (orderLiftAsPartialField j S V) :
      PartialGaugeField L m (levelDepth K (j + 1))).support = bondsInsideOrOverCoarse (j + 1) S ∧
    ∀ e ∈ bondsInsideOrOverCoarse (j + 1) S,
      (realPartialBlockAverage ω (orderLiftAsPartialField j S V) :
        PartialGaugeField L m (levelDepth K (j + 1))).field e = orderLift (j + 1) V e ∧
      partialBlockAverageCase ω (orderLift j V) e = .logarithmOfMeans
def OrderLiftAverageStep : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
  ∀ j k : ℕ, j < k → k ≤ K →
  ∀ S : Set (BondAtLevel L m K k), IsReversalClosed S →
  ∀ V : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsGaugeField complexGaugeGroup S V →
    IsGaugeField complexGaugeGroup (bondsInsideOrOverCoarse j S) (orderLift j V) ∧
    (∀ e : BondAtLevel L m K (j + 1),
      ExactlyOneStepCase S e ∧ StepCaseInsideBlock S V e ∧ StepCaseOverBond S V e ∧
        StepCaseOverAbsentBond (j := j) S e) ∧
    ComplexAverageOfOrderLift j S V ∧
    (IsGaugeField compactGaugeGroup S V →
      CompactAverageOfOrderLift (Averaging.smoothingRadius L) j S V)
end YangMills.Construction.PeriodicLattice
