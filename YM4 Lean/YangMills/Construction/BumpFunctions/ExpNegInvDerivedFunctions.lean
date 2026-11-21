import YangMills.Construction.BumpFunctions.ExpNegInvIntegralBounds
import Mathlib
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.BumpFunctions
def bumpProfile : ℝ → ℝ := expNegInv
def stepIntegralConst : ℝ := ∫ s in (0 : ℝ)..1, bumpProfile s * bumpProfile (1 - s)
def bumpIntegralConst : ℝ := ∫ t : ℝ, bumpProfile (t + 1 / 4) * bumpProfile (1 / 4 - t)
def smoothStep (t : ℝ) : ℝ :=
  1 / stepIntegralConst * ∫ s in Iic t, bumpProfile s * bumpProfile (1 - s)
def evenSmoothStep (t : ℝ) : ℝ := smoothStep (|t| - 1)
def normalizedBump (t : ℝ) : ℝ :=
  1 / bumpIntegralConst * bumpProfile (t + 1 / 4) * bumpProfile (1 / 4 - t)
def mollifiedUnitIndicator : ℝ → ℝ :=
  convolution ((Ico (-(1 / 2) : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ))) normalizedBump
    (ContinuousLinearMap.mul ℝ ℝ) volume
def productCubeCutoff (y : Fin 4 → ℝ) : ℝ :=
  ∏ i : Fin 4, (1 - smoothStep (4 * |y i| - 3))
def integralConstBound : ℝ := max 1 (max stepIntegralConst⁻¹ bumpIntegralConst⁻¹)
def gevreyConst : ℝ := 9
def blockConst : ℝ := 2 * gevreyConst
def cutoffConst : ℝ := 8 * integralConstBound * blockConst
end YangMills.Construction.BumpFunctions
