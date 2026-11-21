import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.SymbolKernelDecay
def SymbolKernelDecayClaim : Prop :=
  ∀ (δ : ℝ) (g : (Fin 4 → ℂ) → ℂ), 0 < δ → PeriodicOperators.RiemannSums.HolomorphicNearStrip δ g →
    PeriodicOperators.RiemannSums.PeriodicOnStrip δ g →
    PeriodicOperators.RiemannSums.BoundedOnStrip δ g → ∀ u : Fin 4 → ℤ,
      ‖TemperedStiffness.symbolKernel g u‖ ≤
        PeriodicOperators.RiemannSums.stripSup δ g * Real.exp (-δ * TorusMetric.l1NormVec (PeriodicOperators.castVec u))
end YangMills.Construction.OneLoopLaw.SymbolKernelDecay
end
