import YangMills.Construction.Lattice.DataAndConclusionsOfTheSystemAtLayerZero
import YangMills.Construction.SeparatedSequences.NumbersOfTheInputs
import YangMills.Construction.SeparatedSequences.OperatorsAndBoundsOfTheInputs
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedSequences.TrivialTripleSystem
variable {L m : ℕ} (S : SeparatedSequences.ScaleData) (Ω : ℕ → Set (PeriodicLattice.FourTorus L m))
section Operators
variable [∀ (n : ℕ) (c : PeriodicLattice.BondAtLevel L m S.levels (n + 1)),
  Fintype (PeriodicLattice.PositiveBondsOf (PeriodicLattice.doubleBlockSymmetricSet c))]
abbrev baseReducedOp : SequenceTriples.ReducedTuple L m S → SequenceTriples.ReducedTuple L m S :=
  SequenceTriples.reducedOp S Ω univ (GreenInputs.oneField S) 0 0
abbrev baseFullOp : SequenceTriples.FullTuple L m S → SequenceTriples.FullTuple L m S :=
  SequenceTriples.fullOp S Ω univ (GreenInputs.oneField S) 0 0
end Operators
def SeminormsFormFamilies {C D : Type} [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (X : Set C) (Y : Set D) (N : PeriodicLattice.FourTorus L m → C → ℝ≥0∞)
    (N' : PeriodicLattice.FourTorus L m → D → ℝ≥0∞) : Prop :=
  ∃ (W : Submodule ℂ C) (W' : Submodule ℂ D), (W : Set C) = X ∧ (W' : Set D) = Y ∧
    SeparatedSequences.IsLayerSeminormFamily S Ω (fun y (u : W) => N y u) ∧
    SeparatedSequences.IsLayerSeminormFamily S Ω (fun y (g : W') => N' y g)
structure SystemSeminormsFormFamilies : Prop where
  first : SeminormsFormFamilies S Ω (SequenceTriples.firstBlockSpace S Ω)
    (SequenceTriples.firstBlockSourceSpace S Ω)
    (SequenceTriples.firstBlockSolutionSeminormAt S Ω (GreenInputs.oneFieldOnFirst S Ω))
    (SequenceTriples.firstBlockSourceSeminormAt S Ω)
  site : SeminormsFormFamilies S Ω (SequenceTriples.siteTripleSpace S Ω)
    (SequenceTriples.siteSourceTripleSpace S Ω)
    (SequenceTriples.siteSolutionSeminormAt S Ω (GreenInputs.oneFieldOnFirst S Ω))
    (SequenceTriples.siteSourceSeminormAt S Ω)
  reduced : SeminormsFormFamilies S Ω (SequenceTriples.reducedTupleSpace S Ω)
    (SequenceTriples.reducedSourceTupleSpace S Ω)
    (SequenceTriples.reducedSolutionSeminormAt S Ω (GreenInputs.oneFieldOnFirst S Ω))
    (SequenceTriples.reducedSourceSeminormAt S Ω)
  full : SeminormsFormFamilies S Ω (SequenceTriples.fullTupleSpace S Ω)
    (SequenceTriples.sourceTupleSpace S Ω)
    (SequenceTriples.solutionSeminormAt S Ω (GreenInputs.oneFieldOnFirst S Ω))
    (SequenceTriples.sourceSeminormAt S Ω)
def ConstantSuffices (L : ℕ) (B : ℝ) : Prop :=
  0 ≤ B ∧
    ∀ (m : ℕ) (S : SeparatedSequences.ScaleData) (Ω : ℕ → Set (PeriodicLattice.FourTorus L m)) (g : ℝ),
      GreenInputs.IsInputSequence S Ω (SeparatedSequences.InputConstants.blockPow L)
        (SeparatedSequences.InputConstants.gapLength L : ℝ) g →
      ∀ (_ : ∀ (n : ℕ) (c : PeriodicLattice.BondAtLevel L m S.levels (n + 1)),
          Fintype (PeriodicLattice.PositiveBondsOf (PeriodicLattice.doubleBlockSymmetricSet c))),
        SequenceTriples.SystemsInvertibleInDecayClass S Ω (SeparatedSequences.decayingInputRate L) B univ
            (GreenInputs.oneField S) 0 ∧
          SystemSeminormsFormFamilies S Ω
def constant (L : ℕ) : ℝ := Classical.epsilon (ConstantSuffices L)
end YangMills.Construction.SeparatedSequences.TrivialTripleSystem
end
