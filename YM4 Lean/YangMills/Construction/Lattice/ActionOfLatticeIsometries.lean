import YangMills.Construction.Lattice.ImagesOfBondsAndPlaquettesUnderLatticeIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace TorusLatticeSymmetry
variable {L m K : ℕ} (s : TorusLatticeSymmetry L m K)
def plaquetteMap (p : Plaquette L m (K : ℤ)) : Plaquette L m (K : ℤ) :=
  open Classical in
  if h : ∃ q : Plaquette L m (K : ℤ), q.vertices = s.pointMap '' p.vertices then h.choose else p
def pullback (U : compactGaugeFields L m (K : ℤ)) : compactGaugeFields L m (K : ℤ) :=
  ⟨fun b => U.1 (s.bondMap b),
    fun b _ => U.2.1 (s.bondMap b) (mem_univ _),
    fun b _ => by
      change U.1 (s.bondMap b.opposite) = (U.1 (s.bondMap b))⁻¹
      rw [s.bondMap_opposite]
      exact U.2.2 (s.bondMap b) (mem_univ _)⟩
end TorusLatticeSymmetry
end PeriodicLattice
namespace InfiniteLattice
def LatticeSymmetry.plaquetteMap {a : ℝ} (s : LatticeSymmetry a) (p : ElementaryPlaquette a) :
    ElementaryPlaquette a :=
  open Classical in
  if h : ∃ q : ElementaryPlaquette a, q.cornerSet = s.pointMap '' p.cornerSet then h.choose else p
end InfiniteLattice
end YangMills.Construction
