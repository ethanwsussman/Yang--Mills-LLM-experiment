import YangMills.Construction.Lattice.AveragesOfSmallPlaquettes
import YangMills.Construction.Lattice.BareDoubleBlocks
import YangMills.Construction.Lattice.KindsOfBondsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
open YangMills.Construction.SeparatedSequences
open YangMills.Construction.SeparatedSequences.BondKinds
variable {L m K n k : ℕ}
def blockPairBondsAt (n : ℕ) (c : BondAtLevel L m K k) : Set (BondAtLevel L m K n) :=
  {b | (n < k ∧ b ∈ bondsAmong (sitesIn (bondBlockPairAt n c))) ∨ ∃ h : n = k, b = h ▸ c}
def blockPairSymmetricBondsAt (n : ℕ) (c : BondAtLevel L m K k) : SymmetricBondSet L m K n where
  bonds := {b | b ∈ blockPairBondsAt n c ∨ b.opposite ∈ blockPairBondsAt n c}
  opposite_mem := fun _ hb => hb.symm
def blockPairSupNormAt (n : ℕ) (c : BondAtLevel L m K k)
    (f : BondAtLevel L m K n → ComplexMatrix2) : ℝ :=
  ⨆ b : ↥(blockPairBondsAt n c), ComplexMatrix2.operatorNorm (f b)
structure IsFinestBlockPairData (k : ℕ) (c : BondAtLevel L m K k) (α₀ : ℝ)
    (U A' A : BondAtLevel L m K 0 → ComplexMatrix2) : Prop where
  one_le_level : 1 ≤ k
  level_le : k ≤ K
  isPositivelyOriented : c.IsPositivelyOriented
  isGaugeField : IsGaugeField compactGaugeGroup (bareBondsInBlockPair c) U
  curvatureSmall : FinestCurvatureSmallOn k α₀ U (bareBondBlockPair c)
  isLieOneForm_left : IsLieOneFormOn complexLieAlgebra (bareBondsInBlockPair c) A'
  isLieOneForm_right : IsLieOneFormOn complexLieAlgebra (bareBondsInBlockPair c) A
end YangMills.Construction.PeriodicLattice
