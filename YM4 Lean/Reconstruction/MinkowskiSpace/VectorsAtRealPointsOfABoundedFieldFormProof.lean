import Reconstruction.MinkowskiSpace.BoundaryVectorsOfTheSmearedVectors
import Reconstruction.MinkowskiSpace.ClosureOfTheTensorVectorsAndTheEuclideanVectors
import Reconstruction.MinkowskiSpace.L1NormsOfTimeDerivativesByTheWeightedNorm
import Reconstruction.MinkowskiSpace.MatrixElementsOfTheFieldVectorsOnTheTube
import Reconstruction.MinkowskiSpace.ScalarProductsOfTheVectorsAtRealPoints
import Reconstruction.MinkowskiSpace.SchwartzFunctionsThatStandInTheVectorsAtRealPoints
import Reconstruction.MinkowskiSpace.TimeDerivativesOfATensorInTheL1Norm
import Reconstruction.MinkowskiSpace.TranslationsAndProjectionsKeepTheClosureOfTheTensorVectors
import Reconstruction.MinkowskiSpace.TranslationsOfTheVectorsAtRealPoints
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsOfABoundedFieldForm
import Reconstruction.MinkowskiSpace.WightmanValuesAsBoundaryValuesOfTheVacuumFunction
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.RealPointVectors
theorem boundaryVectorsStatement_holds
    (hMatrix : TubeMatrixElements.Statement)
    (hSmeared : SmearedBoundaryVectors.Statement)
    (hBoundary : WightmanBoundaryValues.BoundaryValueTheorem)
    (hInner : RealPointInnerProducts.Statement)
    (hTranslate : RealPointVectors.TranslationOfTestStatesStatement)
    (hSchwartz : RealPointVectors.SchwartzClosure)
    (hTensorBound : RealPointVectors.TensorTimeDerivBound)
    (hL1 : TimeDerivativeL1Bound.Statement)
    (hClosure : RealPointVectors.TensorClosure.Statement)
    (hInvariant : RealPointVectors.ClosureInvarianceStatement) :
    BoundaryVectorsStatement := by
  intro K _ _ _ E Ω A P C hC
  have hS := hSmeared E Ω A P C hC
  have hB := hBoundary E Ω A P C hC
  obtain ⟨hDom, hVec, hFld⟩ := hClosure E Ω A P C hC
  obtain ⟨hTr, hPr⟩ := hInvariant E Ω A P C hC
  obtain ⟨hStar, hStarTensor, hTransl, hTens⟩ := hSchwartz
  exact
    { hasWeakIntegrandData := fun m φ hφ Y hY =>
        ((hMatrix E Ω A P C hC m 0).2.2.2 Y hY φ hφ).1
      isBoundaryLimit_testState := hS.isBoundaryLimit_testState
      eq_testState_of_isBoundaryLimit := hS.eq_testState_of_isBoundaryLimit
      testState_linear := hS.testState_linearCombination
      norm_testState_le := hS.norm_testState_le
      wightmanFunctional_zero := hB.wightmanFunctional_zero
      integrable_vacuumIntegrand := hB.integrable_vacuumIntegrand
      exists_continuousOn_extension := hB.exists_continuousOn_extension
      norm_wightmanFunctional_le := hB.norm_wightmanFunctional_le
      starVal_mem := hStar
      tensorVal_starVal_mem := hStarTensor
      inner_testState_eq := hInner E Ω A P C hC
      translateVal_mem := hTransl
      spectralTranslation_testState := hTranslate E Ω A P C hC
      tensorVal_mem := hTens
      fieldFormNorm_tensorProd_le := fun m f hf => hTensorBound _ m f hf
      maxPartialL1_le := hL1
      tensorDomainClosure_eq := hDom
      testState_mem := hVec
      stateVector_mem := hFld
      spectralTranslation_mem := hTr
      proj_mem := hPr }
end YangMills.Construction.RealPointVectors
