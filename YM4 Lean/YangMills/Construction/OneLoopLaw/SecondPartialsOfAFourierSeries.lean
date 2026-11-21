import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.FourierSecondDerivatives
open YangMills.Construction.PeriodicOperators YangMills.Construction.OneLoopLaw.TemperedStiffness
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (l1NormVec)
def TermwiseSecondDerivativeClaim : Prop :=
  ∀ (δ C : ℝ) (c : (Fin 4 → ℤ) → ℂ) (g : (Fin 4 → ℂ) → ℂ), 0 < δ →
    (∀ u, ‖c u‖ ≤ C * Real.exp (-δ * l1NormVec (castVec u))) →
    (∀ p : AmbientSpace, HasSum (fun u : Fin 4 → ℤ => c u *
      Complex.exp (-(Complex.I * bilinDot (toComplexVec p) (toComplexVec (castVec u)))))
      (g (toComplexVec p))) →
    ∀ μ ν : Fin 4, HasSum (fun u : Fin 4 → ℤ => c u * (u μ : ℂ) * (u ν : ℂ))
      (-secondPartialAtZero g μ ν)
end YangMills.Construction.OneLoopLaw.FourierSecondDerivatives
end
