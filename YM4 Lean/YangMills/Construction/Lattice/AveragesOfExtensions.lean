import YangMills.Construction.Lattice.BondsWithinSiteSets
import YangMills.Construction.Lattice.LevelCubesAndBlocks
import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K i j : ℕ}
def sitesInBondBlockPair (i : ℕ) (c : BondAtLevel L m K j) : Set (SiteAtLevel L m K i) :=
  {x | (x : FourTorus L m) ∈ bondBlockPair i c}
def ExtendsAround (c : BondAtLevel L m K j) (W U : BondAtLevel L m K i → Matrices.ComplexMatrix2) :
    Prop :=
  U ∈ gaugeFieldsAtLevel L m K i ∧ ∀ b ∈ (bondsWithin (sitesInBondBlockPair i c)).bonds, U b = W b
def iteratedAverageOfExtension (ω : ℝ) (i q : ℕ) (W : BondAtLevel L m K i → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K (i + q)) : Matrices.ComplexMatrix2 :=
  iterateFromLevel (blockAverageStep ω) i q (Classical.epsilon (ExtendsAround c W)) c
def IsSchemeAverageDefinedAt {j' : ℤ} {j : ℤ} (s : AveragingScheme)
    (W : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) : Prop :=
  open Classical in
  if c.IsPositivelyOriented then IsSchemeAverageDefined s W c
  else IsSchemeAverageDefined s W c.opposite
end PeriodicLattice
end YangMills.Construction
