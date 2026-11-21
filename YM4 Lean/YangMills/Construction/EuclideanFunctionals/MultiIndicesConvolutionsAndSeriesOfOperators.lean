import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
abbrev Multiindex : Type := Fin 4 → ℕ
def Multiindex.order (γ : Multiindex) : ℕ := ∑ μ, γ μ
def Multiindex.fact (γ : Multiindex) : ℕ := ∏ μ, (γ μ).factorial
def iteratedPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (γ : Multiindex)
    (f : R4 → E) : R4 → E :=
  (TestFunctions.partialDerivR4 0)^[γ 0] ((TestFunctions.partialDerivR4 1)^[γ 1]
    ((TestFunctions.partialDerivR4 2)^[γ 2] ((TestFunctions.partialDerivR4 3)^[γ 3] f)))
def conv (φ g : R4 → ℂ) (x : R4) : ℂ := ∫ x', φ x' * g (x - x')
end YangMills.Construction.EuclideanFunctionals
