import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences
noncomputable section
namespace YangMills.Construction.SeparatedSequences.BondKinds
variable {L m : ℕ}
section Kinds
variable (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)) {j : ℕ}
def IsInteriorBond (c : BondAtLevel L m S.levels j) : Prop :=
  j ≤ S.top ∧ c ∈ determiningBondsAt S.levels S.top Ω j ∧
    c.source ∈ layerLatticeSites S Ω j ∧ c.target ∈ layerLatticeSites S Ω j
def IsEndAcross (c : BondAtLevel L m S.levels j) (z : SiteAtLevel L m S.levels j) : Prop :=
  (c.source ∈ layerLatticeSites S Ω j ∧ z = c.target) ∨
    (c.target ∈ layerLatticeSites S Ω j ∧ z = c.source)
def IsOuterEndpoint (c : BondAtLevel L m S.levels j) (z : SiteAtLevel L m S.levels j) : Prop :=
  j ≤ S.top ∧ c ∈ determiningBondsAt S.levels S.top Ω j ∧ IsEndAcross S Ω c z ∧
    z ∉ (sitesIn (truncatedMember S Ω j) : Set (SiteAtLevel L m S.levels j))
def IsOutwardBond (c : BondAtLevel L m S.levels j) : Prop :=
  ∃ z : SiteAtLevel L m S.levels j, IsOuterEndpoint S Ω c z
def flatBondSet : Set (Σ j : ℕ, BondAtLevel L m S.levels j) :=
  {q | q ∈ determiningBondSet S.levels S.top Ω ∧
    (IsInteriorBond S Ω q.2 ∨ IsOutwardBond S Ω q.2)}
end Kinds
section Blocks
variable {K j n : ℕ}
abbrev bareBondBlockPair (c : BondAtLevel L m K j) : Set (FourTorus L m) := bondBlockPair 0 c
abbrev bondBlockPairAt (n : ℕ) (c : BondAtLevel L m K j) : Set (FourTorus L m) :=
  bondBlockPair n c
end Blocks
end YangMills.Construction.SeparatedSequences.BondKinds
