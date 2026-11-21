import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels.ZeroExtensionOfVertexFunctions
open Periodisation Tower
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    1 ≤ k → ZeroExtendDescends L n k
end YangMills.Construction.LocalKernels.ZeroExtensionOfVertexFunctions
