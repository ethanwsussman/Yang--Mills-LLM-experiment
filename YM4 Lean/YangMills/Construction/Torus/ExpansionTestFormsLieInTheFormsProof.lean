import YangMills.Construction.SeparatedSequences.ExpansionsOfACoarseRegionProof
import YangMills.Construction.Torus.ProfilesAndTestForms
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus.CoarseTestForms
theorem torusSupNorm_torusProj_le {S a : ℝ} (v : Fin 4 → ℝ) (h : ∀ ν, |v ν| ≤ a) :
    torusSupNorm (torusProj S v) ≤ a := by apply _root_.YangMills.Construction.GeneralTorus.CoarseRegionExpansions.torusSupNorm_proj_le <;> assumption
end YangMills.Construction.GeneralTorus.CoarseTestForms
