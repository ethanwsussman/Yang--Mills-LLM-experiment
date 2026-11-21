import YangMills.Construction.GrowingTori.NormsOfFunctionsOnTheSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.GrowingTori.GrowthParameters
variable (D : GrowthParameters)
def gradOscSup (g : (Fin 4 → ℝ) → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ (x : Fin 4 → ℝ) (y : Fin 4 → ℝ) (_ : TorusMetric.euclidNormVec (x - y) ≤ δ),
    ENNReal.ofReal (TorusMetric.euclidNormVec
      ((Ambient.euclidean : Ambient D.L).grad g x - (Ambient.euclidean : Ambient D.L).grad g y))
def gradModulus (g : (Fin 4 → ℝ) → ℝ) (δ : ℝ) : ℝ :=
  (D.gradOscSup g δ).toReal
def shiftModulus (g : (Fin 4 → ℝ) → ℝ) (δ : ℝ) : ℝ :=
  max ((Ambient.euclidean : Ambient D.L).gradSup g * δ)
    (40 * (D.choice.M : ℝ) * D.gradModulus g δ)
end YangMills.Construction.GrowingTori.GrowthParameters
end
