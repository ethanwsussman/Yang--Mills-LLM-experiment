import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.SymbolFourierSeries
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.OneLoopLaw.TemperedStiffness
def FourierExpansionOfSymbol : Prop :=
  ∀ (δ : ℝ) (g : (Fin 4 → ℂ) → ℂ), 0 < δ → HolomorphicNearStrip δ g → PeriodicOnStrip δ g →
    BoundedOnStrip δ g → ∀ p : InfiniteLattice.AmbientSpace,
      HasSum (fun u : Fin 4 → ℤ => symbolKernel g u *
        Complex.exp (-(Complex.I * bilinDot (toComplexVec p) (toComplexVec (castVec u)))))
        (g (toComplexVec p))
end YangMills.Construction.OneLoopLaw.SymbolFourierSeries
end
