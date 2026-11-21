import YangMills.Construction.ReflectionPositivity.RateConstantAndRateFunction
import YangMills.Construction.ReflectionPositivity.ReflectionGroupAndCubeReflectionSize
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (unitRegionObservables)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
def CubeVectorDecay : Prop :=
  0 < YangMills.Construction.SmearingFilter.spectralRateConst ∧
    ∀ (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+),
      ∀ A ∈ unitRegionObservables (cubeOfRadius r), ∀ n : ℕ, 1 ≤ n →
        0 ≤ inner ℂ (cubeVector ν μ r A)
            ((ReflectionPair.site.transferOp ν μ ^ n * (1 - groundProjection μ ReflectionPair.site ν))
              (cubeVector ν μ r A)) ∧
          inner ℂ (cubeVector ν μ r A)
              ((ReflectionPair.site.transferOp ν μ ^ n * (1 - groundProjection μ ReflectionPair.site ν))
                (cubeVector ν μ r A)) ≤
            ((YangMills.Construction.SmearingFilter.spectralRateConst *
                ((((r : ℕ) : ℝ) / (n : ℝ)) ^ 2 + (((r : ℕ) : ℝ) / (n : ℝ)) ^ 3) *
                cubeReflectionNorm ν r A : ℝ) : ℂ)
end YangMills.Construction.ReflectionPositivity.DirectionPictures
