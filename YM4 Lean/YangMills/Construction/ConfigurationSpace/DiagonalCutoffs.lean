import YangMills.Construction.BumpFunctions.ExpNegInvDerivedFunctions
import YangMills.Construction.Continuum.ConfigurationSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open YangMills.Construction.BumpFunctions
def pairCutoff (j : ℕ) (y : Fin 4 → ℝ) : ℝ :=
  1 - ∏ c : Fin 4, (1 - evenSmoothStep (2 ^ j * y c))
def pairCutoffProd {n : ℕ} (j : ℕ) (x : Config n) : ℝ :=
  ∏ p ∈ orderedPairs n, pairCutoff j (x p.1 - x p.2)
theorem pairCutoffProd_one (j : ℕ) (x : Config 1) : pairCutoffProd j x = 1 :=
  prod_orderedPairs_one _
def shellDiff {n : ℕ} : ℕ → Config n → ℝ
  | 0 => pairCutoffProd 0
  | j + 1 => pairCutoffProd (j + 1) - pairCutoffProd j
def pairCutoffConst : ℝ := blockConst * integralConstBound ^ 4
end YangMills.Construction.ConfigurationSpace
end
