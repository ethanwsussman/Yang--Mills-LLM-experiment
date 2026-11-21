import YangMills.Construction.WindowOfTheParameters.CoefficientIsOneNumber
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction.SlopeCoefficient
open BlockAverages TorusLumps
private def basisImaginaryI : imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
private theorem inner_basisImaginaryI_ne_zero :
    inner ℝ (basisImaginaryI : ℍ[ℝ]) (basisImaginaryI : ℍ[ℝ]) ≠ 0 := by
  intro h
  have h0 : (basisImaginaryI : ℍ[ℝ]) = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp h
  have h1 := congrArg (fun q : ℍ[ℝ] => q.imI) h0
  simp [basisImaginaryI] at h1
theorem slopeCoefficientUnique_holds : SlopeCoefficientUnique := by
  intro l _ H b b' ⟨K, hK, hb⟩ ⟨K', hK', hb'⟩
  have hKK : K = K' := by
    funext c c'
    exact mul_left_cancel₀ inner_basisImaginaryI_ne_zero
      (tendsto_nhds_unique (hK.tendsto_kernel c c' basisImaginaryI basisImaginaryI)
        (hK'.tendsto_kernel c c' basisImaginaryI basisImaginaryI))
  subst hKK
  exact hb.unique hb'
end YangMills.Construction.SlopeCoefficient
end
