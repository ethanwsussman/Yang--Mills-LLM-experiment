import YangMills.Construction.Torus.CubeSetsBumpsCutOffsAndProductRuleProof
import YangMills.Construction.Torus.PartsOfTheGeometryOfCubes
import YangMills.Construction.Torus.QuadraticFormsAndMatricesOfTheAveragesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus.RowSums
open Set YangMills.Construction.TorusMetric
variable {S : ℝ}
theorem norm_apply_le_torusSupNorm (x : Torus4 S) (μ : Fin 4) : ‖x μ‖ ≤ torusSupNorm x := by apply _root_.YangMills.Construction.SequenceGeometryProof.norm_apply_le_torusSupNorm <;> assumption
theorem torusSupNorm_torusProj_le {v : Fin 4 → ℝ} {r : ℝ} (h : ∀ μ, |v μ| ≤ r) :
    torusSupNorm (torusProj S v) ≤ r := by apply _root_.YangMills.Construction.GeneralTorus.CubeBumpCutoff.supNorm_proj_le <;> assumption
end YangMills.Construction.GeneralTorus.RowSums
