import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
structure CompFacts (I I' I'' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ)
    (S : I.Carrier → I''.Carrier → ℂ) (δ : ℝ) : Prop where
  comp_periodic : (∀ ι' ι'', CompSummableAt T S ι' ι'') ∧
    IsPeriodicKernel I'' I' (compKernel T S)
  comp_decay : ∀ δ', 0 < δ' → δ' < δ → IsDecayRate I'' I' (compKernel T S) δ'
def CompClaim : Prop :=
  ∀ I I' I'' : PeriodicData, IsPeriodic I → IsPeriodic I' → IsPeriodic I'' →
    ∀ (T : I'.Carrier → I.Carrier → ℂ) (S : I.Carrier → I''.Carrier → ℂ) (δ : ℝ),
      IsPeriodicKernel I I' T → IsDecayRate I I' T δ →
      IsPeriodicKernel I'' I S → IsDecayRate I'' I S δ →
        CompFacts I I' I'' T S δ
end PeriodicOperators
end YangMills.Construction
end
