import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
def cubeAround (y : Site L m j) : Set (FourTorus L m) :=
  {x | TorusMetric.torusSupNorm (x - (y : FourTorus L m)) ≤ meshSize L j / 2}
def refinedBlock (n : ℕ) (y : Site L m j) : Set (FourTorus L m) :=
  cubeAround y ∩ (sublattice L m (j + n) : Set (FourTorus L m))
abbrev unitBlock (y : Site L m j) : Set (FourTorus L m) := refinedBlock 1 y
def refinedBlockUnion (n : ℕ) (Y : Set (Site L m j)) : Set (FourTorus L m) :=
  ⋃ y ∈ Y, refinedBlock n y
def bondDoubleBlock (c : Bond L m j) : Set (FourTorus L m) :=
  unitBlock c.source ∪ unitBlock c.target
def doubleBlockPlaquettes (c : Bond L m j) : Set (Plaquette L m j') :=
  plaquettesInside (bondDoubleBlock c)
def bondCorridor (c : Bond L m j) : Set (Bond L m j') :=
  {b | (b.source : FourTorus L m) ∈ unitBlock c.source ∧
    (b.target : FourTorus L m) ∈ unitBlock c.target}
instance : Nonempty (Bond L m j) := ⟨Bond.forwardFrom 0 0⟩
def IsPivot (c : Bond L m j) (b : Bond L m j') : Prop :=
  b ∈ bondCorridor c ∧ b ∈ axialPath (c.source.toSublattice j') (c.target.toSublattice j')
def pivot (c : Bond L m j) : Bond L m j' := Classical.epsilon (IsPivot c)
def nonPivotBonds (K k : ℕ) (X : Set (FourTorus L m)) : Set (BondAtLevel L m K k) :=
  {b | b ∈ bondsMeeting X ∧
    ¬∃ c : BondAtLevel L m K (k + 1), c ∈ bondsMeeting X ∧ b = pivot c}
end YangMills.Construction.PeriodicLattice
