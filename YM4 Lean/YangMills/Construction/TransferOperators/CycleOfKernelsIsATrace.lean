import YangMills.Construction.TransferOperators.KernelBetweenSquareRootsOfTheBondKernel
import YangMills.Construction.TransferOperators.TraceInequalityOfContractions
import YangMills.Construction.TransferOperators.TransferOperatorOfACubicTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics
noncomputable section
namespace YangMills.Construction.TransferOperators
namespace CubicPeriodSublattice
variable (Λ : CubicPeriodSublattice) (μ : Fin 4)
def kernelCycle (β : ℝ) (X : Fin Λ.side → Λ.SliceL2 μ →L[ℂ] Λ.SliceL2 μ)
    (U : Λ.lattice.QuotientField) : ℂ :=
  ∏ k : Fin Λ.side,
    Complex.exp (-Λ.sliceEnergy β (Λ.sliceField (μ := μ) U (Λ.levelClass ((k : ℕ) + 1)))) *
      sqrtKernelSandwich β (X k) (Λ.sliceField (μ := μ) U (Λ.levelClass ((k : ℕ) + 1)))
        (Λ.orbitGaugeAct
          (Λ.temporalSliceField (μ := μ) U (Λ.levelClass ((k : ℕ) + 1)))
          (Λ.sliceField (μ := μ) U (Λ.levelClass ((k : ℕ) + 1) + 1)))
end CubicPeriodSublattice
namespace KernelCycleTrace
def Statement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (Λ : CubicPeriodSublattice) (μ : Fin 4)
    (X : Fin Λ.side → Λ.SliceL2 μ →L[ℂ] Λ.SliceL2 μ),
    (∀ k, ‖X k‖ ≤ 1) →
    TraceSummablePW (interleavedProd X (Λ.transfer μ β)) ∧
      Integrable (Λ.kernelCycle μ β X) Λ.lattice.quotientHaar ∧
      ∫ U, Λ.kernelCycle μ β X U ∂Λ.lattice.quotientHaar =
        tracePW (interleavedProd X (Λ.transfer μ β))
end KernelCycleTrace
end YangMills.Construction.TransferOperators
end
