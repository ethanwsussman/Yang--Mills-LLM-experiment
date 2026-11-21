import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Torus.PartsOfTheGeometryOfCubes
import YangMills.Construction.Torus.LayersCellsBlocksAndTheDistanceProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus.BondSupports
variable {S : ℝ}
theorem torusSupNorm_eq_norm (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem torusSupNorm_sub_eq_dist (x y : Torus4 S) : torusSupNorm (x - y) = dist x y := by
  rw [torusSupNorm_eq_norm, dist_eq_norm]
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
variable {D : ScaleData} {m : ℕ}
theorem src_mem_bondSupport (c : D.PosBond m) : (c.1.src : D.Space) ∈ ScaleData.bondSupport c := by
  left
  show torusSupNorm ((c.1.src : D.Space) - (c.1.src : D.Space)) ≤ D.levelSpacing m / 2
  rw [torusSupNorm_sub_eq_dist, dist_self]
  exact (half_pos (levelSpacing_pos D m)).le
theorem tgt_mem_bondSupport (c : D.PosBond m) : (c.1.tgt : D.Space) ∈ ScaleData.bondSupport c := by
  right
  show torusSupNorm ((c.1.tgt : D.Space) - (c.1.tgt : D.Space)) ≤ D.levelSpacing m / 2
  rw [torusSupNorm_sub_eq_dist, dist_self]
  exact (half_pos (levelSpacing_pos D m)).le
end GeneralTorus.BondSupports
end YangMills.Construction
end
