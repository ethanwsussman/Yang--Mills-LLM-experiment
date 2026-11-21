import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import YangMills.Construction.Lattice.LevelCoordinates
import YangMills.Construction.Lattice.LiftToLevelOfAConfigurationOnBonds
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
section
variable {L m : ℕ} {i : ℤ}
def PartialGaugeField.Coincides (U U' : PartialGaugeField L m i) : Prop :=
  U.support = U'.support ∧ ∀ b ∈ U.support, U.field b = U'.field b
end
variable {L m K k : ℕ}
def orderLiftPartial (j : ℕ) (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    PartialGaugeField L m (levelDepth K j) :=
  ⟨bondsInsideOrOverCoarse j S, orderLift j V⟩
def bareAverageIterAtSmoothingRadius (j : ℕ) (U : PartialGaugeField L m (levelDepth K 0)) :
    PartialGaugeField L m (levelDepth K j) :=
  cast (by rw [Nat.zero_add])
    (partialBlockAverageIter (K := K) (Averaging.smoothingRadius L) 0 U j)
def HasScaledDisplacement (j : ℕ) (b : BondAtLevel L m K j) (c : BondAtLevel L m K k) : Prop :=
  ∃ (s : ℝ) (μ : Fin 4), (s = 1 ∨ s = -1) ∧
    (b.target : FourTorus L m) = shiftBy L m K j b.source (s • coordVec μ) ∧
    (c.target : FourTorus L m) =
      shiftBy L m K j c.source ((s * (L : ℝ) ^ (k - j)) • coordVec μ)
def MatchesScaledBond (j : ℕ) (b : BondAtLevel L m K j) (c : BondAtLevel L m K k) : Prop :=
  HasScaledDisplacement j b c ∧ c.axis = b.axis ∧
    (c.IsPositivelyOriented ↔ b.IsPositivelyOriented)
def BlocksPartitionLevel (L m K j k : ℕ) : Prop :=
  (∀ y : SiteAtLevel L m K k, (blockAtLevel j y).Nonempty ∧
    blockAtLevel j y ⊆ {z | ∃ x : SiteAtLevel L m K j, (x : FourTorus L m) = z}) ∧
  ∀ x : SiteAtLevel L m K j, ∃! y : SiteAtLevel L m K k, (x : FourTorus L m) ∈ blockAtLevel j y
def InsideOrCoveringDichotomy (j k : ℕ) (b : BondAtLevel L m K j) : Prop :=
  (EndsInOneBlock k b ∨ ∃! c : BondAtLevel L m K k, CoversBond c b) ∧
  ¬(EndsInOneBlock k b ∧ ∃ c : BondAtLevel L m K k, CoversBond c b) ∧
  (∀ c : BondAtLevel L m K k, CoversBond c b →
    MatchesScaledBond j b c ∧ CoversBond c.opposite b.opposite ∧
      (∀ c' : BondAtLevel L m K k, CoversBond c' b.opposite → c' = c.opposite) ∧
      MatchesScaledBond j b.opposite c.opposite) ∧
  ∀ y : SiteAtLevel L m K k, IsInsideBlockAt j y b → IsInsideBlockAt j y b.opposite
def LiftsAreGaugeFields (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  bareLiftSupport (K := K) S = bondsInsideOrOverCoarse 0 S ∧
  bareLiftSupport (K := K) S = {b | ∀ c : BondAtLevel L m K k, CoversBond c b → c ∈ S} ∧
  IsReversalClosed (bareLiftSupport (K := K) S) ∧
  IsGaugeField complexGaugeGroup (bareLiftSupport (K := K) S) (bareLiftFromLevel (K := K) V) ∧
  (IsGaugeField compactGaugeGroup S V →
    IsGaugeField compactGaugeGroup (bareLiftSupport (K := K) S)
      (bareLiftFromLevel (K := K) V)) ∧
  (∀ j ≤ k,
    IsReversalClosed (bondsInsideOrOverCoarse j S) ∧
    IsGaugeField complexGaugeGroup (bondsInsideOrOverCoarse j S) (orderLift j V) ∧
    (IsGaugeField compactGaugeGroup S V →
      IsGaugeField compactGaugeGroup (bondsInsideOrOverCoarse j S) (orderLift j V))) ∧
  (∀ b ∈ bondsInsideOrOverCoarse 0 S, orderLift 0 V b = bareLiftFromLevel (K := K) V b) ∧
  (∀ b ∈ S, orderLift k V b = V b) ∧
  bondsInsideOrOverCoarse k S = S
def AverageStepOfLift (j : ℕ) (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  (complexPartialBlockAverage (orderLiftPartial j S V) :
      PartialGaugeField L m (levelDepth K (j + 1))).Coincides (orderLiftPartial (j + 1) S V) ∧
  (∀ c ∈ bondsInsideOrOverCoarse (j + 1) S,
    onSetElseOne (bondsInDoubleBlock c) (orderLift j V) ∈
      complexAveragingDomainNearOne c.positivelyOriented) ∧
  (IsGaugeField compactGaugeGroup S V →
    (realPartialBlockAverage (Averaging.smoothingRadius L) (orderLiftPartial j S V) :
        PartialGaugeField L m (levelDepth K (j + 1))).Coincides
          (orderLiftPartial (j + 1) S V) ∧
    ∀ c ∈ bondsInsideOrOverCoarse (j + 1) S,
      partialBlockAverageCase (Averaging.smoothingRadius L) (orderLift j V) c =
        .logarithmOfMeans ∧
      (realPartialBlockAverage (Averaging.smoothingRadius L) (orderLiftPartial j S V) :
          PartialGaugeField L m (levelDepth K (j + 1))).field c.positivelyOriented =
        regularAverageValue
          (onSetElseOne (bondsInDoubleBlock c.positivelyOriented) (orderLift j V))
          c.positivelyOriented)
def LevelLiftsConsistent (G : Set Matrices.ComplexMatrix2)
    (avg : ∀ j : ℕ, PartialGaugeField L m (levelDepth K j) →
      PartialGaugeField L m (levelDepth K (j + 1)))
    (W : ∀ j : ℕ, PartialGaugeField L m (levelDepth K j))
    (S : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    Prop :=
  (∀ j ≤ k,
    IsReversalClosed (W j).support ∧ IsGaugeField G (W j).support (W j).field ∧
    (W j).Coincides (orderLiftPartial j S V) ∧
    ∀ b : BondAtLevel L m K j,
      (EndsInOneBlock k b → b ∈ (W j).support ∧ (W j).field b = 1) ∧
      (∀ c ∈ S, CoversBond c b → b ∈ (W j).support ∧ (W j).field b = V c) ∧
      ∀ c : BondAtLevel L m K k, c ∉ S → CoversBond c b → b ∉ (W j).support) ∧
  (W 0).Coincides (bareLiftPartial (K := K) ⟨S, V⟩) ∧
  (W k).Coincides ⟨S, V⟩ ∧
  ∀ j < k, (avg j (W j)).Coincides (W (j + 1))
def compactLevelLifts (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (j : ℕ) :
    PartialGaugeField L m (levelDepth K j) :=
  levelLiftPartial j (⟨S, V⟩ : PartialGaugeField L m (levelDepth K k))
def complexLevelLifts (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (j : ℕ) :
    PartialGaugeField L m (levelDepth K j) :=
  complexLevelLiftPartial j (⟨S, V⟩ : PartialGaugeField L m (levelDepth K k))
def LiftsOnFullLattice (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  bareLiftFromLevel (K := K) V ∈ gaugeFieldsAtLevel L m K 0 ∧
  ∀ j ≤ k,
    (compactLevelLifts (K := K) univ V j).support = univ ∧
    (compactLevelLifts (K := K) univ V j).field ∈ gaugeFieldsAtLevel L m K j ∧
    (compactLevelLifts (K := K) univ V j).field =
      blockFieldAtLevel (Averaging.smoothingRadius L) j (bareLiftFromLevel (K := K) V)
def LiftsOnRegion (j : ℕ) (X : Set (FourTorus L m)) (S : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  (bondsInside X : Set (BondAtLevel L m K j)) ⊆ bondsInsideOrOverCoarse j S ∧
  (∀ b ∈ (bondsInside X : Set (BondAtLevel L m K j)), ¬EndsInOneBlock k b →
    ∃ c ∈ (bondsInside X : Set (BondAtLevel L m K k)), CoversBond c b) ∧
  (bondsInside X : Set (BondAtLevel L m K j)) ⊆
    (bareAverageIterAtSmoothingRadius j (⟨bondsInside X, bareLiftFromLevel (K := K) V⟩ :
      PartialGaugeField L m (levelDepth K 0))).support ∧
  ∀ b ∈ (bondsInside X : Set (BondAtLevel L m K j)),
    (bareAverageIterAtSmoothingRadius j (⟨bondsInside X, bareLiftFromLevel (K := K) V⟩ :
      PartialGaugeField L m (levelDepth K 0))).field b = (compactLevelLifts S V j).field b
def LiftConsistentWithAverages : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ k : ℕ, k ≤ K →
  ∀ S : Set (BondAtLevel L m K k), IsReversalClosed S →
  ∀ V : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    (IsGaugeField compactGaugeGroup S V ∨ IsGaugeField complexGaugeGroup S V) →
    (∀ j ≤ k, BlocksPartitionLevel L m K j k ∧
      ∀ b : BondAtLevel L m K j, InsideOrCoveringDichotomy j k b) ∧
    LiftsAreGaugeFields S V ∧
    (∀ j < k, AverageStepOfLift j S V) ∧
    LevelLiftsConsistent complexGaugeGroup (fun _ => complexPartialBlockAverage)
      (complexLevelLifts S V) S V ∧
    (IsGaugeField compactGaugeGroup S V →
      LevelLiftsConsistent compactGaugeGroup
        (fun _ => realPartialBlockAverage (Averaging.smoothingRadius L))
        (compactLevelLifts S V) S V ∧
      ∀ j ≤ k, (compactLevelLifts S V j).Coincides (complexLevelLifts S V j)) ∧
    (S = univ → V ∈ gaugeFieldsAtLevel L m K k → LiftsOnFullLattice V) ∧
    (IsGaugeField compactGaugeGroup S V → ∀ X : Set (FourTorus L m),
      IsPartitionRegion (levelDepth K k) X →
      (bondsInside X : Set (BondAtLevel L m K k)) ⊆ S → ∀ j ≤ k, LiftsOnRegion j X S V)
end PeriodicLattice
end YangMills.Construction
