import YangMills.Construction.ReflectionPositivity.SpectralDensityConstant
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmearingFilter
def spectralRateConst : ℝ :=
  192 * YangMills.Construction.SmearingFilter.spectralDensityConst /
    (YangMills.Construction.SmearingFilter.weightConst *
      YangMills.Construction.ReflectionPositivity.DirectionPictures.slopeConstant ^ 3)
def spectralRateFn (u : ℝ) : ℝ :=
  spectralRateConst * (u ^ 2 + u ^ 3)
end YangMills.Construction.SmearingFilter
