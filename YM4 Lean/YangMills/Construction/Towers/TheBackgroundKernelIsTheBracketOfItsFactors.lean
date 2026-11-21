import YangMills.Construction.Towers.TheFactorsOfTheBackgroundKernel
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open LocalKernels LocalKernels.Periodisation
def HessianKernelIsAssembledFactors : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ U ∈ smallIterateFields L n k, ∀ J ∈ complexEdgeForms L n k 0,
      ∀ μ ∈ complexEdgeForms L n k k,
        (fun ι' ι => FullSpace.FieldValueFunctions.rawHessianKernel
            (liftGaugeField L n k 0 U)
            (liftGaugeField L n k 0 J)
            (liftGaugeField L n k k μ) ι'.2 ι.2) =
          (fullFactors L n k U J μ).assembled
end YangMills.Construction.Tower
end
