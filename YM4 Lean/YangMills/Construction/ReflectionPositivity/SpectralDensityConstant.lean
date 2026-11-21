import YangMills.Construction.Functions.SmearingFilterWeight
import YangMills.Construction.ReflectionPositivity.SpectralVariablesOfTheTwoPictures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmearingFilter
open scoped Real
def spectralDensityConst : ℝ :=
  (2 * π) ^ (-3 : ℤ) *
    (64 * absCoeffSum + 26624 / (ReflectionPositivity.DirectionPictures.slopeConstant * π) +
      3407872 / (ReflectionPositivity.DirectionPictures.slopeConstant * π) ^ 3)
end YangMills.Construction.SmearingFilter
