import YangMills.Construction.Lattice.CubePartitionsAndRegions
import YangMills.Construction.Lattice.SupDistancesOfCells
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
universe u
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def IsWithinFinestMesh (K t : ℕ) (x : FourTorus L m) (Y : Set (FourTorus L m)) : Prop :=
  setSupDistInLevelUnits K t {x} Y ≤ ENNReal.ofReal (finestMeshInLevelUnits L t)
def IsInteriorRegion (K t : ℕ) (Y A : Set (FourTorus L m)) : Prop :=
  (∃ i : ℤ, -(m : ℤ) ≤ i ∧ IsPartitionRegion i Y) ∧ Y ⊆ A ∧
    ∀ x : SiteAtLevel L m K 0, IsWithinFinestMesh K t (x : FourTorus L m) Y → (x : FourTorus L m) ∈ A
def plaquettesInsideNear (K t : ℕ) (A : Set (FourTorus L m)) (b : BondAtLevel L m K 0) :
    Set (PlaquetteAtLevel L m K 0) :=
  {p | p ∈ plaquettesInside A ∧
    ∃ c ∈ p.vertices, IsWithinFinestMesh K t (c : FourTorus L m) {(b.source : FourTorus L m)}}
def nearbyCurvature (K t : ℕ) (A : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (b : BondAtLevel L m K 0) : ℝ :=
  (finestMeshInLevelUnits L t)⁻¹ ^ 2 *
    sSup ((fun p => Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1)) ''
      plaquettesInsideNear K t A b)
end YangMills.Construction.PeriodicLattice
