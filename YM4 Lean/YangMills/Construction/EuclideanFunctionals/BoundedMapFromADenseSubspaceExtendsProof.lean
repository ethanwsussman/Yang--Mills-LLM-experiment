import YangMills.Construction.EuclideanFunctionals.BoundedMapFromADenseSubspaceExtends
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.DenseExtension
theorem denseExtensionTheorem_holds : DenseExtensionTheorem := by
  intro s K τ V c T hV hc hT
  let g : V →L[ℂ] τ.space := T.mkContinuous c hT
  have hdr : DenseRange (V.subtypeL : V →L[ℂ] τ.space) := hV.denseRange_val
  have hui : IsUniformInducing (V.subtypeL : V →L[ℂ] τ.space) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨g.extend V.subtypeL, ?_, ?_, ?_⟩
  · intro v
    exact g.extend_eq hdr hui v
  · intro T' hT'
    exact (g.extend_unique hdr hui T' (ContinuousLinearMap.ext hT')).symm
  · have hle : ‖g.extend V.subtypeL‖ ≤ (1 : NNReal) * ‖g‖ :=
      g.opNorm_extend_le hdr (fun x => by simp)
    have hg : ‖g‖ ≤ c := LinearMap.mkContinuous_norm_le _ hc hT
    simpa using hle.trans (by simpa using hg)
end YangMills.Construction.EuclideanFunctionals.DenseExtension
