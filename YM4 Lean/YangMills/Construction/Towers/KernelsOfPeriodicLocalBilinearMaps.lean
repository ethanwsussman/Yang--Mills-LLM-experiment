import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels.LocalBilinearKernels
open Periodisation Tower
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    BilinearDescends (k := k) L n
end YangMills.Construction.LocalKernels.LocalBilinearKernels
