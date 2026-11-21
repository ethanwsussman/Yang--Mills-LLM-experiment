import YangMills.Construction.Torus.CubeSetsBumpsCutOffsAndProductRuleProof
import YangMills.Construction.Torus.DomainsOfTheExpansionsAsUnionsOfCellsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus.CubeLevels
variable {S : ℝ}
theorem torusSupNorm_le_of_norm_le {x : Torus4 S} {r : ℝ} (h : ∀ μ, ‖x μ‖ ≤ r) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm x ≤ r := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_le_of_forall <;> assumption
theorem torusSupNorm_add_le (x y : Torus4 S) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (x + y) ≤ _root_.YangMills.Construction.TorusMetric.torusSupNorm x + _root_.YangMills.Construction.TorusMetric.torusSupNorm y := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_add_le <;> assumption
theorem torusSupNorm_sub_comm_le (x y : Torus4 S) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - y) ≤ _root_.YangMills.Construction.TorusMetric.torusSupNorm (y - x) := by apply _root_.YangMills.Construction.GeneralTorus.CubeBumpCutoff.supNorm_sub_comm_le <;> assumption
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem torusSupNorm_bond_le {D : ScaleData} {i : ℕ} (b : D.PosBond i) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm ((b.1.tgt : D.Space) - (b.1.src : D.Space)) ≤ D.levelSpacing i := by apply _root_.YangMills.Construction.GeneralTorus.CoarseSupportCells.torusSupNorm_posBond_le <;> assumption
theorem torusSupNorm_sub_end_le {D : ScaleData} {i : ℕ} (b : D.PosBond i) {p w : D.Space}
    (hp : p ∈ ScaleData.bondSupport b)
    (hw : w = (b.1.src : D.Space) ∨ w = (b.1.tgt : D.Space)) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (p - w) ≤ 3 / 2 * D.levelSpacing i := by
  have hpos := levelSpacing_pos D i
  have hedge := torusSupNorm_bond_le b
  have hedge' := (torusSupNorm_sub_comm_le _ _).trans hedge
  rcases hp with hp | hp
  · have hp' : _root_.YangMills.Construction.TorusMetric.torusSupNorm (p - (b.1.src : D.Space)) ≤ D.levelSpacing i / 2 := hp
    rcases hw with rfl | rfl
    · linarith
    · have h := torusSupNorm_add_le (p - (b.1.src : D.Space))
        ((b.1.src : D.Space) - (b.1.tgt : D.Space))
      rw [sub_add_sub_cancel] at h
      linarith
  · have hp' : _root_.YangMills.Construction.TorusMetric.torusSupNorm (p - (b.1.tgt : D.Space)) ≤ D.levelSpacing i / 2 := hp
    rcases hw with rfl | rfl
    · have h := torusSupNorm_add_le (p - (b.1.tgt : D.Space))
        ((b.1.tgt : D.Space) - (b.1.src : D.Space))
      rw [sub_add_sub_cancel] at h
      linarith
    · linarith
end GeneralTorus.CubeLevels
end YangMills.Construction
