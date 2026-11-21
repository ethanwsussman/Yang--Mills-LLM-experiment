import YangMills.Construction.Lattice.GeometryOfASeparatedSequenceProof
import YangMills.Construction.Torus.CubeSetsBumpsCutOffsAndProductRule
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus.CubeBumpCutoff
open Set TorusMetric
variable {L : ℝ}
theorem coord_norm_le_supNorm (x : Torus4 L) (i : Fin 4) : ‖x i‖ ≤ _root_.YangMills.Construction.TorusMetric.torusSupNorm x := by apply _root_.YangMills.Construction.SequenceGeometryProof.norm_apply_le_torusSupNorm <;> assumption
theorem supNorm_le_of_coord_norm_le {x : Torus4 L} {r : ℝ} (h : ∀ i, ‖x i‖ ≤ r) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm x ≤ r := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_le_of_forall <;> assumption
theorem supNorm_add_le (x y : Torus4 L) : _root_.YangMills.Construction.TorusMetric.torusSupNorm (x + y) ≤ _root_.YangMills.Construction.TorusMetric.torusSupNorm x + _root_.YangMills.Construction.TorusMetric.torusSupNorm y := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_add_le <;> assumption
theorem supNorm_sub_comm_le (x y : Torus4 L) : _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - y) ≤ _root_.YangMills.Construction.TorusMetric.torusSupNorm (y - x) :=
  supNorm_le_of_coord_norm_le fun i => by
    show ‖x i - y i‖ ≤ _
    rw [norm_sub_rev]
    exact coord_norm_le_supNorm (y - x) i
theorem supNorm_proj_le {v : Fin 4 → ℝ} {r : ℝ} (h : ∀ i, |v i| ≤ r) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (torusProj L v) ≤ r :=
  supNorm_le_of_coord_norm_le fun i => (addCircle_norm_coe_le_abs _).trans (h i)
theorem abs_clamp_sub_le (a b : ℝ) : |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
    rcases le_total a 1 with ha' | ha' <;> rcases le_total b 1 with hb' | hb' <;>
    simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, ha, hb, ha', hb',
      zero_le_one] <;>
    rw [abs_le] <;> constructor <;>
    linarith [le_abs_self (a - b), neg_abs_le (a - b)]
end YangMills.Construction.GeneralTorus.CubeBumpCutoff
