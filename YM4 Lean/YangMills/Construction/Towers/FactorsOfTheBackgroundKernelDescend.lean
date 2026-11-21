import YangMills.Construction.Towers.TheFactorsOfTheBackgroundKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open LocalKernels LocalKernels.Periodisation
def BackgroundFactorsDescendClaim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ U ∈ smallIterateFields L n k, ∀ J ∈ complexEdgeForms L n k 0,
      ∀ μ ∈ complexEdgeForms L n k k,
        BackgroundFactorsDescend L n (fullFactors L n k U J μ) (quotFactors L n k U J μ)
end YangMills.Construction.Tower
end
