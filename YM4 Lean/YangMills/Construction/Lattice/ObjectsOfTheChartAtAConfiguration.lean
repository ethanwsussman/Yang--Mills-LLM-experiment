import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
open Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K k : ℕ}
def coarsePositiveBonds (L m K k : ℕ) : Set (BondAtLevel L m K (k + 1)) :=
  {c | c.IsPositivelyOriented}
abbrev ChartIndex (L m K k : ℕ) : Type := PositivelyOrientedBond L m (levelDepth K k)
def chartSpace (L m K k : ℕ) : Submodule ℂ (ChartIndex L m K k → Matrices.ComplexMatrix2) :=
  Submodule.pi univ fun _ => Matrices.ComplexMatrix2.traceless
def extendAntisymm (β : ChartIndex L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel L m K k → Matrices.ComplexMatrix2 :=
  open Classical in
  fun b => if h : b.IsPositivelyOriented then β ⟨b, h⟩
    else if h' : b.opposite.IsPositivelyOriented then -β ⟨b.opposite, h'⟩
    else 0
end YangMills.Construction.PeriodicLattice
