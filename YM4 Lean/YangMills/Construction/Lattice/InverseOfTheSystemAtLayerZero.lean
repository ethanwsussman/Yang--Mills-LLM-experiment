import YangMills.Construction.Lattice.DataAndConclusionsOfTheSystemAtLayerZero
import YangMills.Construction.SeparatedSequences.RatesOfTheInputsAndOfTheExpansion
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SequenceTriples
variable {L m : ℕ} (S : SeparatedSequences.ScaleData)
def BaseLayerConstantsWork (L : ℕ) (α B : ℝ) : Prop :=
  α ∈ Ioo 0 (SeparatedSequences.classCeiling L) ∧ 1 ≤ B ∧
    ∀ (m : ℕ) (S : SeparatedSequences.ScaleData)
      (_ : ∀ (n : ℕ) (c : PeriodicLattice.BondAtLevel L m S.levels (n + 1)),
        Fintype (PeriodicLattice.PositiveBondsOf (PeriodicLattice.doubleBlockSymmetricSet c)))
      (g : ℝ) (Y Ω : Set (PeriodicLattice.FourTorus L m))
      (V J U A' : SeparatedSequences.FineBond L m S → Matrices.ComplexMatrix2),
      IsUnionOfSiteBlocks S Y → Y ⊆ Ω →
        IsAmbientTriple S (singleRegionSequence Y) g Ω V J 0 →
        IsSmallOnAmbient S α Ω V J U A' →
        SystemsInvertibleInDecayClass S (singleRegionSequence Y) SeparatedSequences.baseShellRate B Ω
            V J ∧
          ((∀ b ∈ (PeriodicLattice.bondsInside Ω : Set (SeparatedSequences.FineBond L m S)), V b = U b) →
            FormBoundedBelowByHalf S (singleRegionSequence Y) Ω U)
def baseLayerConstants (L : ℕ) : ℝ × ℝ :=
  Classical.epsilon fun p : ℝ × ℝ => BaseLayerConstantsWork L p.1 p.2
def baseLayerSmallness (L : ℕ) : ℝ := (baseLayerConstants L).1
def baseLayerBound (L : ℕ) : ℝ := (baseLayerConstants L).2
end YangMills.Construction.SequenceTriples
end
