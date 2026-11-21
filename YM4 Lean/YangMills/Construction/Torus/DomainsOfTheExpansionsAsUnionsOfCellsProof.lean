import YangMills.Construction.Torus.CellsThatMeetAreNearProof
import YangMills.Construction.Torus.ClosedFormsWithVanishingAveragesAreGradientsProof
import YangMills.Construction.Torus.CompressionOfTheCutOperatorToACubeProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.GeneralTorus.CoarseSupportCells
open Set TorusMetric
noncomputable section
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem torusSupNorm_sub_eq_dist {S : ℝ} (x y : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - y) = dist x y := by
  rw [torusSupNorm_eq_norm, dist_eq_norm]
theorem torusSupNorm_torusProj_le {S r : ℝ} (hr : 0 ≤ r) {v : Fin 4 → ℝ} (hv : ∀ μ, |v μ| ≤ r) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (torusProj S v) ≤ r := by apply _root_.YangMills.Construction.GeneralTorus.MeetingCells.torusSupNorm_torusProj_le <;> assumption
variable {D : ScaleData} (B : SeparatedChain D)
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem levelSpacing_succ (k : ℕ) : D.levelSpacing (k + 1) = (D.L : ℝ) * D.levelSpacing k := by apply _root_.YangMills.Construction.GeneralTorus.ClosedMeanFree.levelSpacing_succ <;> assumption
theorem thirteen_le_L : (13 : ℝ) ≤ D.L := by
  exact_mod_cast D.blocking.thirteen_le
theorem admitsPartition_levelSpacing {n : ℕ} (hn : n ≤ D.lastLevel) :
    D.AdmitsPartition (D.levelSpacing n) := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.admitsPartition_levelSpacing_of_le_lastLevel <;> assumption
theorem localSpacing_eq (hl : B.ShellsAreCubeUnions) {n : ℕ} {y : D.Space}
    (hy : y ∈ B.shellSites n) : B.localSpacing y = D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.MeetingCells.localSpacing_eq <;> assumption
theorem self_mem_cubeAt (n : ℕ) (y : D.Space) : y ∈ D.cubeAt n y := by apply _root_.YangMills.Construction.GeneralTorus.CubeGreenCompressionProof.mem_cubeAt_self <;> assumption
theorem partitionCubes_levelSpacing (hp : CubePartitions.CubePartitionFacts) {n : ℕ}
    (hn : n ≤ D.lastLevel) : CubePartitions.PartitionCubes D (D.levelSpacing n) := by
  obtain ⟨hpos, hev⟩ := admitsPartition_levelSpacing (D := D) hn
  exact (hp D (D.levelSpacing n) 1 hpos le_rfl odd_one (by simpa using hev)).1
theorem cubeAt_mem_cubePartition {n : ℕ} (hn : n ≤ D.lastLevel) {y : D.Space}
    (hy : y ∈ D.levelSublattice n) : D.cubeAt n y ∈ D.cubePartition (D.levelSpacing n) :=
  ⟨admitsPartition_levelSpacing hn, y, hy, rfl⟩
theorem cubeAt_subset_shell (hp : CubePartitions.CubePartitionFacts) {k : ℕ}
    (hk : k + 1 ≤ D.lastLevel) {y : D.Space} (hy : y ∈ D.levelSublattice (k + 1))
    (hsub : D.cubeAt (k + 1) y ⊆ B.set k)
    (hdis : Disjoint (interior (D.cubeAt (k + 1) y)) (B.set (k + 1))) :
    D.cubeAt (k + 1) y ⊆ B.shell k := by
  have hlt : k < D.lastLevel := by omega
  have hshell : B.shell k = closure (B.set k \ B.set (k + 1)) := by
    unfold SeparatedChain.shell
    rw [if_pos hlt]
  have hcl := (partitionCubes_levelSpacing (D := D) hp hk).2.2.2.2.1 _ (cubeAt_mem_cubePartition hk hy)
  rw [hshell]
  calc D.cubeAt (k + 1) y = closure (interior (D.cubeAt (k + 1) y)) := hcl.symm
    _ ⊆ closure (B.set k \ B.set (k + 1)) :=
      closure_mono fun q hq =>
        ⟨hsub (interior_subset hq), fun hqm => Set.disjoint_left.1 hdis hq hqm⟩
theorem torusSupNorm_posBond_le {n : ℕ} (b : D.PosBond n) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm ((b.1.tgt : D.Space) - (b.1.src : D.Space)) ≤ D.levelSpacing n := by
  obtain ⟨μ, hμ⟩ := b.2
  have hpos := levelSpacing_pos (D := D) n
  have h0 := congrArg Subtype.val hμ
  rw [AddSubgroup.coe_sub] at h0
  rw [h0]
  have hstep : ((unitStep D.torusSide (D.levelSpacing n) μ : D.SiteAt n) : D.Space) =
      torusProj D.torusSide (Pi.single μ (D.levelSpacing n)) := rfl
  rw [hstep]
  refine torusSupNorm_torusProj_le hpos.le fun ν => ?_
  by_cases hν : ν = μ
  · subst hν
    rw [Pi.single_eq_same, abs_of_pos hpos]
  · rw [Pi.single_eq_of_ne hν, abs_zero]
    exact hpos.le
end
end YangMills.Construction.GeneralTorus.CoarseSupportCells
