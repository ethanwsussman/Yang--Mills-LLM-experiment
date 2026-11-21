import YangMills.Construction.TransferOperators.PropertiesOfAnOperatorBetweenTwoSquareRootsOfTheBondKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators
open SpinHarmonics InfiniteLattice SandwichConditions
def SandwichOperatorStatement : Prop :=
  ∀ β : ℝ, 0 < β →
    (∀ (ι : Type) [Finite ι] [Nonempty ι] (T : HaarL2 ι →L[ℂ] HaarL2 ι),
      KernelBoundedContinuousSeries β T ∧ SandwichTraceClassWithKernel β T) ∧
    (∀ (ι : Type) [Finite ι] [Nonempty ι], KernelLinearReal β ι) ∧
    (∀ (μ : Fin 4) (Q : Block μ)
      (T : HaarL2 (Q.links : Set (SliceLink μ)) →L[ℂ]
        HaarL2 (Q.links : Set (SliceLink μ))), KernelGaugeInvariant β Q T) ∧
    (∀ (ι : Type) [Finite ι] [Nonempty ι] (n : ℕ) (pieces : Fin n → Set ι) (rest : Set ι)
      (Ts : ∀ i, HaarL2 ↥(pieces i) →L[ℂ] HaarL2 ↥(pieces i)),
      IsPartitionWithRest pieces rest → KernelProductFormula β pieces rest Ts) ∧
    ∀ (ι ι' : Type) [Finite ι] [Nonempty ι] [Finite ι'] (e : ι → ι')
      (T : HaarL2 ι →L[ℂ] HaarL2 ι),
      Function.Bijective e → KernelRelabelEquivariant β e T
end YangMills.Construction.TransferOperators
end
