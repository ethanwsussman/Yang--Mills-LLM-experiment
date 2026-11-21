import YangMills.Construction.Towers.PropertiesOfAbelianFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace AbelianKernelEntries
open Tower.AbelianFieldFacts Tower.UnitLatticeL2
def EntriesAreTrigPolynomials : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → KernelLocality L
end AbelianKernelEntries
end Tower
end YangMills.Construction
end
