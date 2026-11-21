import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.CaseAtBond
import YangMills.Construction.Lattice.LiftOfABlockFieldAndOfTheMembersOfADatum
import YangMills.Construction.Lattice.LiftToLevelOfAConfigurationOnBonds
import YangMills.Construction.Lattice.SetsOfBondsOfASequenceOfRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def transportPartialGaugeField {j : ℤ} (σ : FourTorus L m ≃ FourTorus L m)
    (V : PartialGaugeField L m j) : PartialGaugeField L m j where
  support := bondImage σ '' V.support
  field := transportGaugeField σ V.field
def PartialGaugeField.EqOnSupport {j : ℤ} (V W : PartialGaugeField L m j) : Prop :=
  V.support = W.support ∧ ∀ b ∈ V.support, V.field b = W.field b
def BlockAverageStepEquivariant (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ k : ℕ, k < K → i ≤ levelDepth K (k + 1) →
    (∀ c : BondAtLevel L m K (k + 1),
      transportGaugeField σ '' smallPlaquetteFields (j' := levelDepth K k) (Averaging.smoothingRadius L) c =
        smallPlaquetteFields (Averaging.smoothingRadius L) (bondImage σ c)) ∧
    ∀ U ∈ compactGaugeFields L m (levelDepth K k),
      (∀ c : BondAtLevel L m K (k + 1), blockAverageCaseAtBond (K := K) (n := k) (Averaging.smoothingRadius L) U c =
        blockAverageCaseAtBond (K := K) (n := k) (Averaging.smoothingRadius L) (transportGaugeField σ U)
          (bondImage σ c)) ∧
      (blockAverage (Averaging.smoothingRadius L) (transportGaugeField σ U) :
          BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2) =
        transportGaugeField σ (blockAverage (Averaging.smoothingRadius L) U)
def BlockFieldEquivariant (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ k : ℕ, k ≤ K → i ≤ levelDepth K k → ∀ U ∈ compactGaugeFields L m (levelDepth K 0),
    blockFieldAtLevel (K := K) (Averaging.smoothingRadius L) k (transportGaugeField σ U) =
      transportGaugeField σ (blockFieldAtLevel (K := K) (Averaging.smoothingRadius L) k U)
def LinearBlockAverageEquivariant (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ k : ℕ, k < K → i ≤ levelDepth K (k + 1) → ∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm complexLieAlgebra A →
      (linearBlockAverage (transportForm σ A) : BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2) =
        transportForm σ (linearBlockAverage A) ∧
      (scaledLinearBlockAverage (transportForm σ A) : BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2) =
        transportForm σ (scaledLinearBlockAverage A)
def LinearBlockIterateEquivariant (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ k n : ℕ, k + n ≤ K → i ≤ levelDepth K (k + n) → ∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm complexLieAlgebra A →
      linearBlockIterateBetween (K := K) k n (transportForm σ A) =
        transportForm σ (linearBlockIterateBetween (K := K) k n A) ∧
      scaledLinearBlockIterateFrom (K := K) k n (transportForm σ A) =
        transportForm σ (scaledLinearBlockIterateFrom (K := K) k n A)
def PartialBlockAverageEquivariant (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ k : ℕ, k < K → ∀ a : ℤ, i ≤ a → a ≤ levelDepth K (k + 1) → ∀ X : Set (FourTorus L m), IsPartitionRegion a X →
    ∀ U : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsGaugeField compactGaugeGroup (bondsInside X) U →
      ∀ b ∈ (bondsInside (σ '' X) : Set (BondAtLevel L m K (k + 1))),
        partialBlockAverage (K := K) (j := k) (Averaging.smoothingRadius L) 1 (bondsInside (σ '' X))
            (transportGaugeField σ U) b =
          transportGaugeField σ
            (partialBlockAverage (K := K) (j := k) (Averaging.smoothingRadius L) 1 (bondsInside X) U) b
def RegionBlockFieldEquivariant (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ k : ℕ, k ≤ K → i ≤ levelDepth K k → ∀ a : ℤ, i ≤ a → a ≤ levelDepth K 0 →
    ∀ Ω₀ : Set (FourTorus L m), IsPartitionRegion a Ω₀ →
    ∀ U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2, IsGaugeField compactGaugeGroup (bondsInside Ω₀) U →
      ∀ c : BondAtLevel L m K k,
        (IsAverageFormedOnRegion (σ '' Ω₀) (bondImage σ c) ↔ IsAverageFormedOnRegion Ω₀ c) ∧
        (IsAverageFormedOnRegion Ω₀ c →
          regionBlockField k (σ '' Ω₀) (transportGaugeField σ U) (bondImage σ c) =
            regionBlockField k Ω₀ U c)
def LevelLiftEquivariant (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (k j : ℕ), i ≤ levelDepth K k → ∀ V : PartialGaugeField L m (levelDepth K k),
    (∀ 𝒢 : Set Matrices.ComplexMatrix2, (𝒢 = compactGaugeGroup ∨ 𝒢 = complexGaugeGroup) → IsLevelLiftData (K := K) 𝒢 j V →
      IsLevelLiftData (K := K) 𝒢 j (transportPartialGaugeField σ V) ∧
      (bareLiftPartial (K := K) (transportPartialGaugeField σ V)).EqOnSupport
        (transportPartialGaugeField σ (bareLiftPartial (K := K) V)) ∧
      (complexLevelLiftPartial (K := K) j (transportPartialGaugeField σ V)).EqOnSupport
        (transportPartialGaugeField σ (complexLevelLiftPartial (K := K) j V))) ∧
    (IsLevelLiftData (K := K) compactGaugeGroup j V →
      (levelLiftPartial (K := K) j (transportPartialGaugeField σ V)).EqOnSupport
        (transportPartialGaugeField σ (levelLiftPartial (K := K) j V)))
def IsDeterminingChainFrom (K k : ℕ) (i : ℤ) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  k ≤ K ∧ IsDeterminingChain K k Ω ∧ ∀ q ≤ k, ∃ a : ℤ, i ≤ a ∧ a ≤ levelDepth K q ∧ IsPartitionRegion a (Ω q)
def DeterminingAverageEquivariant (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (k : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsDeterminingChainFrom K k i Ω →
    ∀ U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2, IsGaugeField compactGaugeGroup (bondsInside (Ω 0)) U →
      ∀ j ≤ k, ∀ c ∈ determiningBondsAt K k (imageChain σ Ω) j,
        averagingOnDeterminingSet (Averaging.smoothingRadius L) K (imageChain σ Ω 0)
            (transportGaugeField σ U) j c =
          datumImage σ (averagingOnDeterminingSet (Averaging.smoothingRadius L) K (Ω 0) U) j c
def InducedDatumEquivariant (K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (k : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsDeterminingChainFrom K k i Ω →
    ∀ V ∈ compactGaugeFields L m (levelDepth K k),
      ∀ j ≤ k, ∀ c ∈ determiningBondsAt K k (imageChain σ Ω) j,
        averagingOnDeterminingSet (Averaging.smoothingRadius L) K (imageChain σ Ω 0)
            (bareLiftFromLevel (K := K) (k := k) (transportGaugeField σ V)) j c =
          datumImage σ (averagingOnDeterminingSet (Averaging.smoothingRadius L) K (Ω 0)
            (bareLiftFromLevel (K := K) (k := k) V)) j c ∧
        blockFieldLift (K := K) (k := k) j (transportGaugeField σ V) c =
          transportGaugeField σ (blockFieldLift (K := K) (k := k) j V) c
def AveragingMapsEquivariant : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    ∀ σ ∈ latticeIsometries L m i, ∀ K : ℕ,
      BlockAverageStepEquivariant K i σ ∧
      BlockFieldEquivariant K i σ ∧
      LinearBlockAverageEquivariant K i σ ∧
      LinearBlockIterateEquivariant K i σ ∧
      PartialBlockAverageEquivariant K i σ ∧
      RegionBlockFieldEquivariant K i σ ∧
      LevelLiftEquivariant K i σ ∧
      DeterminingAverageEquivariant K i σ ∧
      InducedDatumEquivariant K i σ
end PeriodicLattice
end YangMills.Construction
