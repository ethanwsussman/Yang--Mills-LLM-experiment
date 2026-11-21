import YangMills.Construction.Lattice.ClassesOfMapsWithExponentialDecay
import YangMills.Construction.Lattice.RegionSequenceExtension
import YangMills.Construction.Lattice.SolutionsAndSourcesOfTheSystemOfATriple
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SequenceTriples
variable {L m : ℕ} (S : SeparatedSequences.ScaleData)
abbrev singleRegionSequence (Y : Set (PeriodicLattice.FourTorus L m)) :
    ℕ → Set (PeriodicLattice.FourTorus L m) :=
  RegionSequences.extendByEmpty 0 fun _ => Y
structure IsUnionOfSiteBlocks (Y : Set (PeriodicLattice.FourTorus L m)) : Prop where
  extendable : RegionSequences.IsExtendableTo S.levels 0 S.top fun _ => Y
  eq_iUnion : Y = ⋃ x ∈ SeparatedRegions.siteIndexSet S Y, SeparatedSequences.siteBlock S x
structure IsSmallOnAmbient (α : ℝ) (R : Set (PeriodicLattice.FourTorus L m))
    (W J U A' : SeparatedSequences.FineBond L m S → Matrices.ComplexMatrix2) : Prop where
  isGaugeField : PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup
    (PeriodicLattice.bondsInside R) U
  mem_forms : A' ∈ (PeriodicLattice.Bare.bondFormSpace R :
    Set (SeparatedSequences.FineBond L m S → Matrices.ComplexMatrix2))
  eq_expTwist : ∀ b ∈ (PeriodicLattice.bondsInside R : Set (SeparatedSequences.FineBond L m S)),
    W b = PeriodicLattice.expTwist (fun c => ((S.finestMesh L : ℝ) : ℂ) • A' c) U b
  plaquette_le : ∀ p ∈ (PeriodicLattice.plaquettesInside R :
      Set (PeriodicLattice.PlaquetteAtLevel L m S.levels 0)),
    Matrices.ComplexMatrix2.operatorNorm (PeriodicLattice.plaquetteHolonomy U p - 1) ≤ α
  form_le : ∀ b ∈ (PeriodicLattice.bondsInside R : Set (SeparatedSequences.FineBond L m S)),
    S.finestMesh L * Matrices.ComplexMatrix2.operatorNorm (A' b) ≤ α
  current_le : ∀ b ∈ (PeriodicLattice.bondsInside R : Set (SeparatedSequences.FineBond L m S)),
    S.finestMesh L ^ 3 * Matrices.ComplexMatrix2.operatorNorm (J b) ≤ 1
variable (Ω : ℕ → Set (PeriodicLattice.FourTorus L m))
def InverseInDecayClass {C D : Type} [AddCommGroup C] [Module ℂ C] [Nonempty C] [AddCommGroup D]
    [Module ℂ D] (X : Set C) (Y : Set D) (K : C → C) (ι : D → C)
    (N : PeriodicLattice.FourTorus L m → C → ℝ≥0∞)
    (N' : PeriodicLattice.FourTorus L m → D → ℝ≥0∞) (δ B : ℝ) : Prop :=
  PeriodicLattice.IsBijectiveOn X K ∧
    ∃ (V : Submodule ℂ C) (V' : Submodule ℂ D) (_ : FiniteDimensional ℂ V)
      (_ : FiniteDimensional ℂ V') (T : V' →ₗ[ℂ] V),
      (V : Set C) = X ∧ (V' : Set D) = Y ∧
        (∀ g : V', (T g : C) = PeriodicLattice.inverseOn X K (ι g)) ∧
        T ∈ SeparatedSequences.expDecayMaps S Ω δ B (fun y (g : V') => N' y g)
          (fun y (Ψ : V) => N y Ψ)
section Operators
variable [∀ (n : ℕ) (c : PeriodicLattice.BondAtLevel L m S.levels (n + 1)),
  Fintype (PeriodicLattice.PositiveBondsOf (PeriodicLattice.doubleBlockSymmetricSet c))]
structure SystemsInvertibleInDecayClass (δ B : ℝ) (R : Set (PeriodicLattice.FourTorus L m))
    (W J : SeparatedSequences.FineBond L m S → Matrices.ComplexMatrix2) : Prop where
  firstBlock : InverseInDecayClass S Ω (firstBlockSpace S Ω) (firstBlockSourceSpace S Ω)
    (firstBlockOp S Ω W) (firstBlockSourceEmbedding S)
    (firstBlockSolutionSeminormAt S Ω (firstMemberRestriction S Ω W))
    (firstBlockSourceSeminormAt S Ω) δ B
  siteBlock : InverseInDecayClass S Ω (siteTripleSpace S Ω) (siteSourceTripleSpace S Ω)
    (siteBlockOp S Ω W) (siteSourceEmbedding S)
    (siteSolutionSeminormAt S Ω (firstMemberRestriction S Ω W)) (siteSourceSeminormAt S Ω) δ B
  reduced : InverseInDecayClass S Ω (reducedTupleSpace S Ω) (reducedSourceTupleSpace S Ω)
    (reducedOp S Ω R W J 0)
    (reducedSourceEmbedding S Ω (firstMemberRestriction S Ω W))
    (reducedSolutionSeminormAt S Ω (firstMemberRestriction S Ω W))
    (reducedSourceSeminormAt S Ω) δ B
  full : InverseInDecayClass S Ω (fullTupleSpace S Ω) (sourceTupleSpace S Ω)
    (fullOp S Ω R W J 0) (sourceEmbedding S Ω (firstMemberRestriction S Ω W))
    (solutionSeminormAt S Ω (firstMemberRestriction S Ω W)) (sourceSeminormAt S Ω) δ B
end Operators
def FormBoundedBelowByHalf (R : Set (PeriodicLattice.FourTorus L m))
    (U : SeparatedSequences.FineBond L m S → Matrices.ComplexMatrix2) : Prop :=
  ∀ A ∈ SeparatedRegions.regionBondFormSpace S (Ω 0),
    PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra A →
    1 / 2 * (PeriodicLattice.Bare.bondFormInnerOn (Ω 0) (S.finestMesh L) A A).re ≤
      (PeriodicLattice.Bare.bondFormInnerOn (Ω 0) (S.finestMesh L) A
        (A + ((S.finestMesh L ^ 2 : ℝ) : ℂ) • compressedHessian S Ω R U A)).re
structure IsLayerZeroData (α g : ℝ) (Y R : Set (PeriodicLattice.FourTorus L m))
    (W J U A' : SeparatedSequences.FineBond L m S → Matrices.ComplexMatrix2) : Prop where
  isUnion : IsUnionOfSiteBlocks S Y
  subset : Y ⊆ R
  triple : IsAmbientTriple S (singleRegionSequence Y) g R W J 0
  small : IsSmallOnAmbient S α R W J U A'
end YangMills.Construction.SequenceTriples
end
