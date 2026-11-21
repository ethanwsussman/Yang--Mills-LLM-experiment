import YangMills.Construction.Towers.TheFactorsOfTheBackgroundKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.BracketDescent
open Conventions
open Periodisation
open PeriodicOperators (BackgroundKernelFactors swapKernel)
def AssembledFactorsDescend : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n → ∀ (I₀ I₁ I₂ : WeightedIndexSet k)
    (F : BackgroundKernelFactors (Idx L I₀) (Idx L I₁) (Idx L I₂))
    (G : BackgroundKernelFactors (I₀.ImageCarrier L n) (I₁.ImageCarrier L n) (I₂.ImageCarrier L n)),
    BackgroundFactorsDescend L n F G →
      KernelDescends L n I₁ I₁ F.assembled G.assembled ∧
      KernelDescends L n I₁ I₁ (swapKernel F.assembled) (swapKernel G.assembled)
end YangMills.Construction.LocalKernels.BracketDescent
end
