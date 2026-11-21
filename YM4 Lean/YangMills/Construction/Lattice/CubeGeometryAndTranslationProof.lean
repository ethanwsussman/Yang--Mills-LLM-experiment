import YangMills.Construction.Lattice.ClosedCubesOfTheCoarseSitesOfACubeProof
import YangMills.Construction.Lattice.CubeGeometryAndTranslation
import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open ScaledFun
variable {d N : ℕ}
section Translations
variable {s : Mesh N}
end Translations
namespace Scales
variable {L j : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh))
variable (hF : ∀ (s : Mesh N) (v : GridPoint d s),
    LinearMap.adjoint (multiFieldTranslation (Fin d) v : OneForm d s →ₗ[ℝ] OneForm d s) =
      (multiFieldTranslation (Fin d) v).symm.toLinearMap)
end Scales
end PeriodicLattice
namespace CubeCovering
open SeparatedSequences PeriodicLattice
variable {L m : ℕ}
theorem mem_complementRegion (hL : 0 < L) (i : ℤ) {X : Set (PeriodicLattice.FourTorus L m)}
    {x : PeriodicLattice.FourTorus L m} (hx : x ∉ X) : x ∈ complementRegion i X := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.mem_complementRegion <;> assumption
namespace CubeData
variable (C : CubeData L m)
theorem base_pos (C : CubeData L m) : 0 < L := by
  have := C.two_le_base
  omega
theorem levelScale_pos (n : ℕ) : 0 < C.levelScale n := by apply _root_.YangMills.Construction.CubeCovering.CoarseSiteCubes.levelScale_pos <;> assumption
end CubeData
namespace Cube
variable {C : CubeData L m} (Q : Cube C)
end Cube
end CubeCovering
end YangMills.Construction
