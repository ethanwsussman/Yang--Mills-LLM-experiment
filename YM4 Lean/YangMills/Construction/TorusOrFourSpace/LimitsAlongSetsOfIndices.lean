import YangMills.Construction.TorusOrFourSpace.DiagonalExtractionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.IndexedLimits
abbrev ConvergesToAlong (A : Sequences.PNatIndexSet) (j₀ : ℤ) (w : (A.filterGe j₀).carrier → ℂ)
    (z : ℂ) : Prop :=
  DiagonalLimits.TendsToAlong A j₀ w z
abbrev LimitExistsAlong (A : Sequences.PNatIndexSet) (j₀ : ℤ)
    (w : (A.filterGe j₀).carrier → ℂ) : Prop :=
  DiagonalLimits.HasLimitAlong A j₀ w
end YangMills.Construction.PeriodicSpace.IndexedLimits
