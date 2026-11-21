import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels
def DescendingKernelAlgebra : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k m : ℕ, 0 < m →
    Periodisation.DescendsAlgebra (k := k) L m
end YangMills.Construction.LocalKernels
