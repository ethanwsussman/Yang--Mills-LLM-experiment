import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels.PairBrackets
open Periodisation Tower
def BracketsAndTransposes : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    PairBracketTranspose (k := k) L
end YangMills.Construction.LocalKernels.PairBrackets
