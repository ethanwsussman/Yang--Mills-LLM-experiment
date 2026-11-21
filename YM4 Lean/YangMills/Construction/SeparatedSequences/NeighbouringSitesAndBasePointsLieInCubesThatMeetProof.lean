import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.SeparatedSequences.NeighbouringSitesAndBasePointsLieInCubesThatMeet
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice
namespace SeparatedClasses
namespace BlockAdjacency
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem norm_target_sub_source_le (C : ClassData) (b : C.BareBond) :
    ‖(b.1.target : C.Point) - (b.1.source : C.Point)‖ ≤ meshSize C.L (levelDepth C.cutoff 0) := by
  have hL : (0 : ℝ) < C.L := by exact_mod_cast C.isAdmissible.1.pos
  obtain ⟨μ, hμ⟩ := b.2
  have e : (b.1.target : C.Point) - (b.1.source : C.Point) =
      pointOnAxis C.L C.m μ (meshSize C.L (levelDepth C.cutoff 0)) := congrArg Subtype.val hμ
  have hs : 0 ≤ meshSize C.L (levelDepth C.cutoff 0) := (zpow_pos hL _).le
  rw [e]
  refine (pi_norm_le_iff_of_nonneg hs).2 fun ν => ?_
  by_cases h : ν = μ
  · subst h
    simp only [pointOnAxis, Pi.single_eq_same]
    exact (addCircle_norm_coe_le_abs _).trans (abs_of_nonneg hs).le
  · simp only [pointOnAxis, Pi.single_eq_of_ne h, norm_zero]
    exact hs
end BlockAdjacency
end SeparatedClasses
end YangMills.Construction
end
