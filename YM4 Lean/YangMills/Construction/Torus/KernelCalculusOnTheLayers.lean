import YangMills.Construction.Torus.AdmissiblePairs
import YangMills.Construction.Torus.AveragingOperatorAndMatrices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
def LayerKernelCalculus : Prop :=
  ∀ (D : TorusData) (C : SeparatedChain D), (C.stage 0).Nonempty →
    Finite ↥C.allSites ∧
    (∀ a : ↥C.allSites, (a : D.Space) ∈ C.stage 0) ∧
    (∀ a : ↥C.allSites, 0 < C.siteScale a) ∧
    (∀ (T : C.LayerOp) (u : C.LayerFn) (a : ↥C.allSites),
      T u a = ∑ᶠ b : ↥C.allSites, C.kernel T a b * u b) ∧
    (∀ (T T' : C.LayerOp) (a b : ↥C.allSites),
      C.kernel (T ∘ₗ T') a b =
        ∑ᶠ c : ↥C.allSites, C.kernel T a c * C.kernel T' c b) ∧
    (∀ (T : C.LayerOp) (φ φ' : ↥C.allSites → ℝ) (a b : ↥C.allSites),
      C.kernel (C.mulOp φ ∘ₗ T ∘ₗ C.mulOp φ') a b =
        φ a * C.kernel T a b * φ' b) ∧
    Ring.inverse (C.scaleOnLayer : Module.End ℝ C.LayerFn) =
      C.mulOp (fun a => (C.siteScale a)⁻¹) ∧
    ∀ (U : Set D.Space) (T : Module.End ℝ ↥(C.layerSpaceOn U)),
      C.extendByZeroFromBlocks U
          (Ring.inverse (C.scaleOnLayerOn U) ^ 2 * T * Ring.inverse (C.scaleOnLayerOn U) ^ 2) =
        (Ring.inverse (C.scaleOnLayer : Module.End ℝ C.LayerFn) ^ 2 *
            (C.extendByZeroFromBlocks U T : Module.End ℝ C.LayerFn) *
          Ring.inverse (C.scaleOnLayer : Module.End ℝ C.LayerFn) ^ 2 :
            Module.End ℝ C.LayerFn)
end YangMills.Construction.Weighted
