import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.EuclideanFunctionals
noncomputable def complexExtensionGauge (z : Fin 4 → ℂ) : ℝ :=
  |(z 3).re| + ∑ j : Fin 3, |(z j.castSucc).im|
def complexExtensionDomain (η : ℝ) : Set (Fin 4 → ℂ) :=
  {z | |(z 3).re| + ∑ j : Fin 3, |(z j.castSucc).im| < η / 8}
end YangMills.Construction.EuclideanFunctionals
