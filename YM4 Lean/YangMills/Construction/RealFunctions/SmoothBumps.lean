import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Bumps
open MeasureTheory
def expNegInv (t : ℝ) : ℝ := if 0 < t then Real.exp (-1 / t) else 0
def stepNormalizer : ℝ := ∫ τ in (0 : ℝ)..1, expNegInv τ * expNegInv (1 - τ)
def bumpNormalizer : ℝ := ∫ t : ℝ, expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t)
def smoothTransition (t : ℝ) : ℝ :=
  1 / stepNormalizer * ∫ τ in Set.Iic t, expNegInv τ * expNegInv (1 - τ)
def symmetricTransition (t : ℝ) : ℝ := smoothTransition (|t| - 1)
def unitBump (t : ℝ) : ℝ :=
  1 / bumpNormalizer * expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t)
def mollifiedIndicator (t : ℝ) : ℝ :=
  ∫ τ : ℝ, (Set.Ico (-(1 / 2) : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) τ * unitBump (t - τ)
def cubeBump (y : Fin 4 → ℝ) : ℝ := ∏ c : Fin 4, (1 - smoothTransition (4 * |y c| - 3))
def normalizerBound : ℝ := max 1 (max stepNormalizer⁻¹ bumpNormalizer⁻¹)
def gevreyConst : ℝ := 9
def twiceGevreyConst : ℝ := 2 * gevreyConst
def cubeBumpGradConst : ℝ := 8 * normalizerBound * twiceGevreyConst
end Bumps
end YangMills.Construction
