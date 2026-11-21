import YangMills.Construction.Weighted.GivenChain
import YangMills.Construction.Weighted.LayerOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def scaleSqOnLayer : B.LayerOp :=
  (B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 2
def inverseScaleSqOnLayer : B.LayerOp :=
  Ring.inverse (B.scaleOnLayer : Module.End ℝ B.LayerFn) ^ 2
def KernelViaScaledMatrices (K : B.LayerOp) (y y' : ↥B.allSites) : Prop :=
  B.kernel K y y' =
      B.siteScale y' ^ 4 *
        B.matrixOf (B.inverseScaleSqOnLayer ∘ₗ K ∘ₗ B.inverseScaleSqOnLayer) y y' ∧
    B.siteScale y' ^ 4 *
        B.matrixOf (B.inverseScaleSqOnLayer ∘ₗ K ∘ₗ B.inverseScaleSqOnLayer) y y' =
      B.siteScale y ^ (-4 : ℤ) *
        B.matrixOf (B.scaleSqOnLayer ∘ₗ K ∘ₗ B.scaleSqOnLayer) y y' ∧
    B.siteScale y ^ (-4 : ℤ) *
        B.matrixOf (B.scaleSqOnLayer ∘ₗ K ∘ₗ B.scaleSqOnLayer) y y' =
      B.matrixOf (B.inverseScaleSqOnLayer ∘ₗ K ∘ₗ B.scaleSqOnLayer) y y'
end SeparatedChain
def KernelViaScaledMatricesClaim : Prop :=
  ∀ (G : GivenChain) (K : G.chain.LayerOp) (y y' : ↥G.chain.allSites),
    G.chain.KernelViaScaledMatrices K y y'
end YangMills.Construction.Weighted
end
