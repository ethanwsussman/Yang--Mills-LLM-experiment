import YangMills.Construction.SoftAverages.ChainWithCouplingsForm
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.SoftAverages.FiniteLinkFunctions
def pureQuaternionCLM : (Fin 3 → ℝ) →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (⟨0, w 0, w 1, w 2⟩ : ℍ[ℝ])
      map_add' := fun w w' => by
        refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
        · show (0 : ℝ) = 0 + 0
          simp
        · rfl
        · rfl
        · rfl
      map_smul' := fun r w => by
        refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
        · show (0 : ℝ) = r * 0
          simp
        · rfl
        · rfl
        · rfl }
theorem expImag_eq_exp (w : Fin 3 → ℝ) : expImag w = NormedSpace.exp (pureQuaternionCLM w) := rfl
theorem contDiff_expImag : ContDiff ℝ ⊤ expImag := by
  have hexp : ContDiff ℝ ⊤ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
    contDiff_iff_contDiffAt.mpr fun q => (NormedSpace.exp_analytic (𝕂 := ℝ) q).contDiffAt
  exact hexp.comp pureQuaternionCLM.contDiff
end YangMills.Construction.SoftAverages.FiniteLinkFunctions
end
