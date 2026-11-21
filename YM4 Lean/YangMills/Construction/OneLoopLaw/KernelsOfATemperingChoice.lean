import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.TemperedKernels
open YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.OneLoopLaw.TemperedStiffness
def KernelLimitAndReality : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (F : FieldFamily L) (δ : ℝ)
    (σ : SymbolArray) (e : ℕ → ℝ),
    IsLatticeFunctional L F → IsTemperedWitness L F δ σ e →
      KernelsTendTo L F σ ∧ ∀ (μ ν : Fin 4) (u : Fin 4 → ℤ), (symbolKernel (σ μ ν) u).im = 0
end YangMills.Construction.OneLoopLaw.TemperedKernels
end
