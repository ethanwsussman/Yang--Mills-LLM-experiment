import YangMills.Construction.ReflectionPositivity.MatrixElementsAreCorrelations
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
theorem matrixElementsEqCorrelations_of_reflectionPairTheorem (hPairs : ReflectionPairTheorem) :
    MatrixElementsEqCorrelations :=
  fun ν μ F hF H hH n w hw =>
    ⟨(hPairs ν μ ReflectionPair.link).2.2.1 F hF H hH n w hw,
      (hPairs ν μ ReflectionPair.site).2.2.1 F hF H hH n w hw⟩
end YangMills.Construction.ReflectionPositivity.DirectionPictures
