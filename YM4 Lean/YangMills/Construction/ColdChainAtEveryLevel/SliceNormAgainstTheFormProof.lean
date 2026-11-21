import YangMills.Construction.ColdChainAtEveryLevel.SliceNormAgainstTheForm
import YangMills.Construction.ColdChainAtEveryLevel.SliceNormWithTheRadius
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockAverages
theorem sliceNormFormBound (hR : sliceNormRadiusBoundStatement) :
    sliceNormFormBoundStatement := by
  intro a ha
  obtain ⟨c, Ca, L1, hc, hCa, h⟩ := hR a ha
  refine ⟨c, Ca, L1, hc, hCa, ?_⟩
  intro F m S hodd h5 hamb hm hreg s V hs hsc hcold φ θ δ p hθ hδ hφ U hU
  have h1 := h F m S hodd h5 hamb hm hreg s V hs hsc hcold φ θ δ p hθ hδ hφ U hU
  have h2 : 0 ≤ weightedBondL2Norm S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
      (fun x i => U.fine x i) := Real.sqrt_nonneg _
  linarith
end YangMills.Construction.BlockAverages
end
