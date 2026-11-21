import YangMills.Construction.Lattice.FurtherSeminormsOfSolutionsAndSources
import YangMills.Construction.SeparatedSequences.SystemAtTheTrivialTriple
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedSequences.TrivialTripleEnds
variable {L m : ℕ} (S : SeparatedSequences.ScaleData) (Ω : ℕ → Set (PeriodicLattice.FourTorus L m))
def InverseInClassForPair {C D : Type} [AddCommGroup C] [Module ℂ C] [Nonempty C]
    [AddCommGroup D] [Module ℂ D] (X : Set C) (Y : Set D) (T : C → C) (j : D → C)
    (ν : PeriodicLattice.FourTorus L m → D → ℝ≥0∞) (μ : PeriodicLattice.FourTorus L m → C → ℝ≥0∞)
    (δ B : ℝ) : Prop :=
  SeparatedSequences.TrivialTripleSystem.SeminormsFormFamilies S Ω X Y μ ν ∧
    SequenceTriples.InverseInDecayClass S Ω X Y T j μ ν δ B
section MapsInClass
variable [∀ (n : ℕ) (c : PeriodicLattice.BondAtLevel L m S.levels (n + 1)),
  Fintype (PeriodicLattice.PositiveBondsOf (PeriodicLattice.doubleBlockSymmetricSet c))]
def AugmentedMapInClass
    (ν : PeriodicLattice.FourTorus L m → SequenceTriples.AugmentedSourceTuple L m S → ℝ≥0∞)
    (μ : PeriodicLattice.FourTorus L m → SequenceTriples.FullTuple L m S → ℝ≥0∞) (δ B : ℝ) : Prop :=
  InverseInClassForPair S Ω (SequenceTriples.fullTupleSpace S Ω)
    (SequenceTriples.augmentedSourceTupleSpace S Ω)
    (SeparatedSequences.TrivialTripleSystem.baseFullOp S Ω)
    (SequenceTriples.augmentedSourceEmbedding S Ω (GreenInputs.oneFieldOnFirst S Ω)) ν μ δ B
def ReducedAugmentedMapInClass
    (ν : PeriodicLattice.FourTorus L m → SequenceTriples.ReducedAugmentedSourceTuple L m S → ℝ≥0∞)
    (μ : PeriodicLattice.FourTorus L m → SequenceTriples.ReducedTuple L m S → ℝ≥0∞) (δ B : ℝ) : Prop :=
  InverseInClassForPair S Ω (SequenceTriples.reducedTupleSpace S Ω)
    (SequenceTriples.reducedAugmentedSourceTupleSpace S Ω)
    (SeparatedSequences.TrivialTripleSystem.baseReducedOp S Ω)
    (SequenceTriples.reducedAugmentedSourceEmbedding S Ω (GreenInputs.oneFieldOnFirst S Ω)) ν μ δ B
def SourceMapInClass
    (ν : PeriodicLattice.FourTorus L m → SequenceTriples.SourceTuple L m S → ℝ≥0∞)
    (μ : PeriodicLattice.FourTorus L m → SequenceTriples.FullTuple L m S → ℝ≥0∞) (δ B : ℝ) : Prop :=
  InverseInClassForPair S Ω (SequenceTriples.fullTupleSpace S Ω)
    (SequenceTriples.sourceTupleSpace S Ω)
    (SeparatedSequences.TrivialTripleSystem.baseFullOp S Ω)
    (SequenceTriples.sourceEmbedding S Ω (GreenInputs.oneFieldOnFirst S Ω)) ν μ δ B
def ReducedSourceMapInClass
    (ν : PeriodicLattice.FourTorus L m → SequenceTriples.ReducedSourceTuple L m S → ℝ≥0∞)
    (μ : PeriodicLattice.FourTorus L m → SequenceTriples.ReducedTuple L m S → ℝ≥0∞) (δ B : ℝ) : Prop :=
  InverseInClassForPair S Ω (SequenceTriples.reducedTupleSpace S Ω)
    (SequenceTriples.reducedSourceTupleSpace S Ω)
    (SeparatedSequences.TrivialTripleSystem.baseReducedOp S Ω)
    (SequenceTriples.reducedSourceEmbedding S Ω (GreenInputs.oneFieldOnFirst S Ω)) ν μ δ B
structure ExponentMemberships (δ B β ε : ℝ) : Prop where
  holderToSup : AugmentedMapInClass S Ω
    (SequenceTriples.augmentedSourceHoelderSeminormAt S Ω ε (GreenInputs.oneFieldOnFirst S Ω))
    (SequenceTriples.solutionSeminormAt S Ω (GreenInputs.oneFieldOnFirst S Ω)) δ B
  supToWeak : AugmentedMapInClass S Ω (SequenceTriples.augmentedSourceSeminormAt S Ω)
    (SequenceTriples.solutionWeakHoelderSeminormAt S Ω β (GreenInputs.oneFieldOnFirst S Ω)) δ B
  holderToStrong : β + ε < 1 → AugmentedMapInClass S Ω
    (SequenceTriples.augmentedSourceHoelderSeminormAt S Ω (β + ε) (GreenInputs.oneFieldOnFirst S Ω))
    (SequenceTriples.solutionStrongHoelderSeminormAt S Ω β (GreenInputs.oneFieldOnFirst S Ω)) δ B
  sourceToStrong : SourceMapInClass S Ω (SequenceTriples.sourceSeminormAt S Ω)
    (SequenceTriples.solutionStrongHoelderSeminormAt S Ω β (GreenInputs.oneFieldOnFirst S Ω)) δ B
  reducedHolderToSup : ReducedAugmentedMapInClass S Ω
    (SequenceTriples.reducedAugmentedSourceHoelderSeminormAt S Ω ε (GreenInputs.oneFieldOnFirst S Ω))
    (SequenceTriples.reducedSolutionSeminormAt S Ω (GreenInputs.oneFieldOnFirst S Ω)) δ B
  reducedSupToWeak : ReducedAugmentedMapInClass S Ω
    (SequenceTriples.reducedAugmentedSourceSeminormAt S Ω)
    (SequenceTriples.reducedSolutionWeakHoelderSeminormAt S Ω β (GreenInputs.oneFieldOnFirst S Ω)) δ B
  reducedHolderToStrong : β + ε < 1 → ReducedAugmentedMapInClass S Ω
    (SequenceTriples.reducedAugmentedSourceHoelderSeminormAt S Ω (β + ε)
      (GreenInputs.oneFieldOnFirst S Ω))
    (SequenceTriples.reducedSolutionStrongHoelderSeminormAt S Ω β (GreenInputs.oneFieldOnFirst S Ω)) δ B
  reducedSourceToStrong : ReducedSourceMapInClass S Ω (SequenceTriples.reducedSourceSeminormAt S Ω)
    (SequenceTriples.reducedSolutionStrongHoelderSeminormAt S Ω β (GreenInputs.oneFieldOnFirst S Ω)) δ B
structure L2Memberships (δ B : ℝ) : Prop where
  augmented : AugmentedMapInClass S Ω (SequenceTriples.augmentedSourceL2SeminormAt S Ω)
    (SequenceTriples.solutionL2SeminormAt S Ω (GreenInputs.oneFieldOnFirst S Ω)) δ B
  source : SourceMapInClass S Ω (SequenceTriples.sourceL2SeminormAt S Ω)
    (SequenceTriples.solutionStrongL2SeminormAt S Ω (GreenInputs.oneFieldOnFirst S Ω)) δ B
  reducedAugmented : ReducedAugmentedMapInClass S Ω
    (SequenceTriples.reducedAugmentedSourceL2SeminormAt S Ω)
    (SequenceTriples.reducedSolutionL2SeminormAt S Ω (GreenInputs.oneFieldOnFirst S Ω)) δ B
  reducedSource : ReducedSourceMapInClass S Ω (SequenceTriples.reducedSourceL2SeminormAt S Ω)
    (SequenceTriples.reducedSolutionStrongL2SeminormAt S Ω (GreenInputs.oneFieldOnFirst S Ω)) δ B
end MapsInClass
def IsExponentBound (L : ℕ) (β ε B : ℝ) : Prop :=
  0 ≤ B ∧
    ∀ (m : ℕ) (S : SeparatedSequences.ScaleData) (Ω : ℕ → Set (PeriodicLattice.FourTorus L m)) (g : ℝ),
      GreenInputs.IsInputSequence S Ω (SeparatedSequences.InputConstants.blockPow L)
        (SeparatedSequences.InputConstants.gapLength L : ℝ) g →
      ∀ (_ : ∀ (n : ℕ) (c : PeriodicLattice.BondAtLevel L m S.levels (n + 1)),
          Fintype (PeriodicLattice.PositiveBondsOf (PeriodicLattice.doubleBlockSymmetricSet c))),
        ExponentMemberships S Ω (SeparatedSequences.decayingInputRate L) B β ε
def IsL2Bound (L : ℕ) (B : ℝ) : Prop :=
  0 ≤ B ∧
    ∀ (m : ℕ) (S : SeparatedSequences.ScaleData) (Ω : ℕ → Set (PeriodicLattice.FourTorus L m)) (g : ℝ),
      GreenInputs.IsInputSequence S Ω (SeparatedSequences.InputConstants.blockPow L)
        (SeparatedSequences.InputConstants.gapLength L : ℝ) g →
      ∀ (_ : ∀ (n : ℕ) (c : PeriodicLattice.BondAtLevel L m S.levels (n + 1)),
          Fintype (PeriodicLattice.PositiveBondsOf (PeriodicLattice.doubleBlockSymmetricSet c))),
        L2Memberships S Ω (SeparatedSequences.decayingInputRate L) B
end YangMills.Construction.SeparatedSequences.TrivialTripleEnds
end
