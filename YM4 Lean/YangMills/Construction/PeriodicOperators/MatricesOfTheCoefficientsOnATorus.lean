import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
variable (F I : PeriodicData)
def periodicCoeffOneMatrix (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (s : ℕ)
    (ζ : F.QuotMod s → ℂ) : Module.End ℂ (I.QuotMod s → ℂ) :=
  linearMapOfEntries (descendMatrix I I s (periodicCoeffOne F I I T s ζ))
def periodicCoeffTwoMatrix (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (s : ℕ)
    (ζ ζ' : F.QuotMod s → ℂ) : Module.End ℂ (I.QuotMod s → ℂ) :=
  linearMapOfEntries (descendMatrix I I s (periodicCoeffTwo F I I T s ζ ζ'))
end YangMills.Construction.PeriodicOperators
end
