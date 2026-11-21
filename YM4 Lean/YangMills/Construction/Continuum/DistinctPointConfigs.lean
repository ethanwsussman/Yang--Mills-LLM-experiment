import YangMills.Construction.Continuum.ConfigurationSpace
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ConfigurationSpace
def distinctConfigs (n : ℕ) : Set (Config n) :=
  YangMills.Construction.TestFunctions.injectiveTuples (Fin 4 → ℝ) n
end YangMills.Construction.ConfigurationSpace
