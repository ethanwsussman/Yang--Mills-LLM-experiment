import YangMills.Construction.Matrices.CoefficientSpacesOfSeveralVariablesArePolynomial
import YangMills.Construction.Matrices.DiagonalsAndDimensionsOfSeveralVariables
import YangMills.Construction.Matrices.EveryPolynomialOnPowersOfGHasFiniteDegrees
import YangMills.Construction.Matrices.ExpansionInThePeterWeylBasis
import YangMills.Construction.Matrices.FactsOnFunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.Matrices.MultiplicationByAPolynomialOnPowersOfGForm
import YangMills.Construction.Matrices.OperatorsAreDeterminedByMatrixElementsForm
import YangMills.Construction.Matrices.PeterWeylFunctionsOfSeveralVariablesAndKernelsForm
import YangMills.Construction.Matrices.ProjectionsCommuteWithTwoSidedTranslations
import YangMills.Construction.Matrices.ProjectionsOntoSpacesOfSeveralVariables
import YangMills.Construction.Matrices.RealPolynomialsOfADisjointUnionOfIndexSets
import YangMills.Construction.Matrices.RealPolynomialsOnPowersOfGAreDense
import YangMills.Construction.Matrices.SeriesOfTheTensorOperatorConverges
import YangMills.Construction.Matrices.TensorOperatorOfAnIntegralOperator
import YangMills.Construction.Matrices.TensorOperatorOnProductsAndItsMatrixElements
import YangMills.Construction.Matrices.TensorOperatorsOfDisjointPartsCommute
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SpinHarmonics.SeveralVariables
theorem severalVariablesFacts_holds
    (hPW : PeterWeylOrthonormalAndKernel)
    (hProj : IsotypicProjProperties)
    (hExp : PeterWeylExpansionHolds)
    (hBi : AllIsotypicProjCommuteBiTranslate)
    (hDiag : KernelDiagonalsAreDims)
    (hPoly : CoeffSpansArePolynomial)
    (hMul : AllPolyMulShiftSpins)
    (hDeg : PolynomialDegrees.Statement)
    (hDense : RealPolyDenseOnPowers)
    (hUnion : AllRealPolyDisjointUnionSplit)
    (hSeries : TensorOneSeriesConvergesForAll)
    (hProd : TensorOneOnProductsForAll)
    (hEntries : AllOpsDeterminedByEntries)
    (hKer : TensorOneKernelOpForAll)
    (hComm : TensorOneDisjointCommuteForAll) :
    SeveralVariablesFacts := by
  intro J _ _ l κ
  obtain ⟨a₁, a₂, a₃, a₄, a₅⟩ := hPW J l
  obtain ⟨-, p₁, p₂, p₃⟩ := hProj J l κ
  obtain ⟨c₁, c₂⟩ := hPoly J l κ
  exact ⟨⟨a₁, a₂, a₃, a₄, a₅, p₁, p₂, p₃⟩, hExp J, hBi J l, hDiag J l κ, c₁, c₂, hMul J l, hDeg J,
    hDense J, hUnion J, fun B hB hB' X =>
      ⟨hSeries J B hB hB' X, hProd J B hB hB' X, hEntries J, hKer J B hB hB' X, hComm J B hB hB' X⟩⟩
end YangMills.Construction.SpinHarmonics.SeveralVariables
