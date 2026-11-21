import YangMills.Construction.PeriodicOperators.BlockMatricesAndCopiesOfIndexSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CopyQuotients
def Claim : Prop :=
  ∀ V : Fin 2 → PeriodicData, (∀ b, IsPeriodic (V b)) →
    BlockJets.QuotOfCopies V
end YangMills.Construction.PeriodicOperators.CopyQuotients
end
