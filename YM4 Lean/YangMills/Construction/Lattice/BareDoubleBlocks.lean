import YangMills.Construction.Lattice.AveragingOnPart
import YangMills.Construction.Lattice.BondsWithinSiteSets
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import YangMills.Construction.Lattice.LevelCubesAndBlocks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K q i : ℕ} {j : ℤ}
def toBareUnits (L K : ℕ) (r : ℝ) : ℝ := toLevelUnits L K 0 r
def cubePartitionOfSide (L m K q : ℕ) : Set (Set (FourTorus L m)) :=
  standardCubePartition L m (levelDepth K q)
theorem blockAtLevel_eq_cubeAtLevel_inter (h : i ≤ q) (y : SiteAtLevel L m K q) :
    blockAtLevel i y = cubeAtLevel y ∩ (sublattice L m (levelDepth K i) : Set (FourTorus L m)) := by
  have hd : levelDepth K q + ((q - i : ℕ) : ℤ) = levelDepth K i := by
    simp only [levelDepth]
    omega
  simp only [blockAtLevel, refinedBlock, hd]
abbrev bareBlock (y : SiteAtLevel L m K q) : Set (FourTorus L m) := blockAtLevel 0 y
abbrev bareBlockPair (c : BondAtLevel L m K q) : Set (FourTorus L m) := bondBlockPair 0 c
def bareAxialPath (c : BondAtLevel L m K q) : List (BondAtLevel L m K 0) :=
  axialPath (c.source.toSublattice (levelDepth K 0)) (c.target.toSublattice (levelDepth K 0))
def bareParallelTransport (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K q) : Matrices.ComplexMatrix2 :=
  pathHolonomy U (bareAxialPath c)
def bondsAmong (Y : Set (Site L m j)) : Set (Bond L m j) := {b | b.LiesIn Y}
theorem bondsAmong_isReversalClosed (Y : Set (Site L m j)) :
    IsReversalClosed (bondsAmong Y) :=
  fun _ hb => ⟨hb.2, hb.1⟩
theorem bondsAmong_sitesIn (Ω : Set (FourTorus L m)) :
    bondsAmong (sitesIn Ω : Set (Site L m j)) = bondsInside Ω :=
  rfl
def bareBondsInBlockPair (c : BondAtLevel L m K q) : Set (BondAtLevel L m K 0) :=
  bondsAmong (sitesIn (bareBlockPair c))
def IsDefinedOnBareBlockPair (B : Set (BondAtLevel L m K 0))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (c : BondAtLevel L m K q) : Prop :=
  IsReversalClosed B ∧ IsGaugeField compactGaugeGroup B U ∧ bareBondsInBlockPair c ⊆ B
def bareBlockPairExtension (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K q) : BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  extendByOne (bareBondsInBlockPair c) U
theorem bareBlockPairExtension_mem {B : Set (BondAtLevel L m K 0)}
    {U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2}
    {c : BondAtLevel L m K q} (h : IsDefinedOnBareBlockPair B U c) :
    bareBlockPairExtension U c ∈ gaugeFieldsAtLevel L m K 0 :=
  extendByOne_mem_compactGaugeFields (bondsAmong_isReversalClosed _)
    ⟨fun b hb => h.2.1.1 b (h.2.2 hb), fun b hb => h.2.1.2 b (h.2.2 hb)⟩
def partialBareBlockField (ω : ℝ) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K q) : Matrices.ComplexMatrix2 :=
  blockFieldAtLevel ω q (bareBlockPairExtension U c) c
def IsDefinedOnDoubleBlock (B : Set (BondAtLevel L m K i))
    (W : BondAtLevel L m K i → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K (i + 1)) : Prop :=
  IsReversalClosed B ∧ IsGaugeField compactGaugeGroup B W ∧ bondsInDoubleBlock c ⊆ B
def doubleBlockExtension (W : BondAtLevel L m K i → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K (i + 1)) : BondAtLevel L m K i → Matrices.ComplexMatrix2 :=
  extendByOne (bondsInDoubleBlock c) W
theorem doubleBlockExtension_mem {B : Set (BondAtLevel L m K i)}
    {W : BondAtLevel L m K i → Matrices.ComplexMatrix2}
    {c : BondAtLevel L m K (i + 1)} (h : IsDefinedOnDoubleBlock B W c) :
    doubleBlockExtension W c ∈ gaugeFieldsAtLevel L m K i :=
  extendByOne_mem_compactGaugeFields (fun _ hb => ⟨hb.2, hb.1⟩)
    ⟨fun b hb => h.2.1.1 b (h.2.2 hb), fun b hb => h.2.1.2 b (h.2.2 hb)⟩
def partialBlockAverageStep (ω : ℝ) (W : BondAtLevel L m K i → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K (i + 1)) : Matrices.ComplexMatrix2 :=
  blockAverageStep ω i (doubleBlockExtension W c) c
end YangMills.Construction.PeriodicLattice
