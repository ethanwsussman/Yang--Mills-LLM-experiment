import YangMills.Construction.Geometry.ToriGeneralSide
import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Torus.PropertiesOfTheWeightedDistanceAndCells
import YangMills.Construction.Torus.LayersCellsBlocksAndTheDistanceProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace MeetingCells
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem torusSupNorm_torusProj_le {S r : ℝ} (hr : 0 ≤ r) {v : Fin 4 → ℝ}
    (hv : ∀ μ, |v μ| ≤ r) : torusSupNorm (torusProj S v) ≤ r := by
  rw [torusSupNorm_eq_norm]
  exact (pi_norm_le_iff_of_nonneg hr).2 fun μ => (addCircle_norm_coe_le_abs (v μ)).trans (hv μ)
variable {D : ScaleData} (B : SeparatedChain D)
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem admitsPartition_levelSpacing {n : ℕ} (hn : n ≤ D.lastLevel) :
    D.AdmitsPartition (D.levelSpacing n) := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.admitsPartition_levelSpacing_of_le_lastLevel <;> assumption
theorem set_antitone {m n : ℕ} (hmn : m ≤ n) : B.set n ⊆ B.set m := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.Chain.set_antitone <;> assumption
theorem le_lastLevel_of_mem_shellSites {n : ℕ} {y : D.Space} (hy : y ∈ B.shellSites n) :
    n ≤ D.lastLevel := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.Chain.le_lastLevel_of_mem_shellSites <;> assumption
theorem localSpacing_eq (hl : B.ShellsAreCubeUnions) {n : ℕ} {y : D.Space}
    (hy : y ∈ B.shellSites n) : B.localSpacing y = D.levelSpacing n := by
  have hn := le_lastLevel_of_mem_shellSites B hy
  have hmem : y ∈ B.set n := by
    have h := hy
    rw [(hl n hn).2.2.1] at h
    exact h.2.1
  have hinf : sInf {m | y ∈ B.shellSites m} = n := by
    apply le_antisymm (Nat.sInf_le hy)
    refine le_csInf ⟨n, hy⟩ ?_
    intro m hm
    by_contra hlt
    have hm' : y ∈ B.shellSites m := hm
    rw [(hl m (by omega)).2.2.1] at hm'
    exact hm'.2.2 (set_antitone B (by omega) hmem)
  unfold SeparatedChain.localSpacing
  rw [hinf]
end MeetingCells
end YangMills.Construction.GeneralTorus
end
