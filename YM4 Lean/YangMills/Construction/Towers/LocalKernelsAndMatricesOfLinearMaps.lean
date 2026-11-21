import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels
open Periodisation Tower
def KernelsAndLinearMapMatrices : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k m : ℕ, 0 < m →
    LocalKernelFacts (k := k) L ∧ LinearMapHasMatrix (k := k) L m
end YangMills.Construction.LocalKernels
