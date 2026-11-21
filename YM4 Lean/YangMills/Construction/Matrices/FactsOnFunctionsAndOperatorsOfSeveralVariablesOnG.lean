import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.HilbertSpaceBasics
noncomputable section
namespace YangMills.Construction.SpinHarmonics.SeveralVariables
def SeveralVariablesFacts : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (l : J → HalfNatural) (κ : HalfNatural),
    OrthonormalBasisAndProjections l κ ∧
    PeterWeylExpansion J ∧
    IsotypicProjCommutesBiTranslate l ∧
    KernelDiagonalEqDim l κ ∧
    IsStarClosedPolySpan (truncatedCoeffSpan J κ) ∧
    IsStarClosedPolySpan (prodCoeffSpan l) ∧
    PolyMulShiftsSpins l ∧
    PolyHasFiniteDegrees J ∧
    RealPolyDense J ∧
    RealPolyDisjointUnionSplit J ∧
    ∀ (B : Set J), B.Nonempty → B ≠ Set.univ →
      ∀ X : HaarL2 ↥B →L[ℂ] HaarL2 ↥B,
        TensorOneSeriesConverges B X ∧
        TensorOneOnProducts B X ∧
        OpDeterminedByEntries J ∧
        TensorOneKernelOp B X ∧
        TensorOneDisjointCommute B X
end YangMills.Construction.SpinHarmonics.SeveralVariables
end
