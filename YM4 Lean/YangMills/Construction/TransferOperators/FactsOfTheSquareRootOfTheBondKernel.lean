import YangMills.Construction.Matrices.HilbertSchmidtOperatorsTraceClassAndTraceOnG
import YangMills.Construction.TransferOperators.BondKernelAndLayerEnergy
import YangMills.Construction.TransferOperators.CubicToriAndProductsOfOperatorsOnPowersOfG
import YangMills.Construction.TransferOperators.SquareRootOfTheBondKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.TransferOperators.SqrtLinkFacts
def HasAbsUniformSum {ι X : Type*} (f : ι → X → ℂ) (F : X → ℂ) : Prop :=
  (∀ x, Summable fun i => ‖f i x‖) ∧
    TendstoUniformly (fun (s : Finset ι) x => ∑ i ∈ s, f i x) F Filter.atTop
def toHaarL2 {S : Type} [Finite S] (φ : C(S → ComplexMatrix2.specialUnitary, ℂ)) : HaarL2 S :=
  ContinuousMap.toLp (E := ℂ) 2 (ComplexMatrix2.haarPi S) ℂ φ
theorem measurePreserving_funUnique_haar (I : Type) [Unique I] :
    MeasurePreserving (MeasurableEquiv.funUnique I ComplexMatrix2.specialUnitary)
      (ComplexMatrix2.haarPi I) ComplexMatrix2.haarProb :=
  ⟨(MeasurableEquiv.funUnique I ComplexMatrix2.specialUnitary).measurable,
    Measure.infinitePi_map_eval (fun _ : I => ComplexMatrix2.haarProb) default⟩
def liftToUnique (I : Type) [Unique I]
    (A : Lp ℂ 2 ComplexMatrix2.haarProb →L[ℂ] Lp ℂ 2 ComplexMatrix2.haarProb) :
    HaarL2 I →L[ℂ] HaarL2 I :=
  (Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_funUnique_haar I)).toContinuousLinearMap ∘L A ∘L
    (Lp.compMeasurePreservingₗᵢ ℂ _
      (measurePreserving_funUnique_haar I).symm).toContinuousLinearMap
section Properties
variable (β : ℝ) (S : Type) [Finite S]
def SqrtKernelRealSymmContinuous : Prop :=
  (∀ x y : S → ComplexMatrix2.specialUnitary, (sqrtLinkKernel β x y).im = 0) ∧
  (∀ x y : S → ComplexMatrix2.specialUnitary, sqrtLinkKernel β x y = sqrtLinkKernel β y x) ∧
  Continuous fun q : (S → ComplexMatrix2.specialUnitary) × (S → ComplexMatrix2.specialUnitary) =>
    sqrtLinkKernel β q.1 q.2
def KernelExpansions : Prop :=
  HasAbsUniformSum
    (fun (j : S → HalfNatural)
        (q : (S → ComplexMatrix2.specialUnitary) × (S → ComplexMatrix2.specialUnitary)) =>
      (sqrtCharCoeffProd β j : ℂ) * isotypicKernel j q.1 q.2)
    (fun q => sqrtLinkKernel β q.1 q.2) ∧
  HasAbsUniformSum
    (fun (a : PeterWeylIndex S)
        (q : (S → ComplexMatrix2.specialUnitary) × (S → ComplexMatrix2.specialUnitary)) =>
      (sqrtPeterWeylCoeff β a : ℂ) * peterWeylFn a q.1 * star (peterWeylFn a q.2))
    (fun q => sqrtLinkKernel β q.1 q.2) ∧
  HasAbsUniformSum
    (fun (j : S → HalfNatural)
        (q : (S → ComplexMatrix2.specialUnitary) × (S → ComplexMatrix2.specialUnitary)) =>
      charCoeffProd β j * isotypicKernel j q.1 q.2)
    (fun q => linkProductKernel β q.1 q.2)
def PeterWeylBounds : Prop :=
  (∀ a : PeterWeylIndex S, ‖peterWeylFn a‖ ≤ ∏ᶠ s, (2 * (spins a s).toReal + 1)) ∧
  ∀ σ : ℝ, 0 < σ →
    Summable fun a : PeterWeylIndex S => (peterWeylCoeff β a).re ^ σ * ‖peterWeylFn a‖ ^ 2
def IsotypicEigenvalues : Prop :=
  ∀ (j : S → HalfNatural) (φ : C(S → ComplexMatrix2.specialUnitary, ℂ)), φ ∈ prodCoeffSpan j →
    sqrtLinkOperator β S (toHaarL2 φ) = (sqrtCharCoeffProd β j : ℂ) • toHaarL2 φ ∧
      linkProductOperator β S (toHaarL2 φ) = charCoeffProd β j • toHaarL2 φ
def StrongExpansions : Prop :=
  ∀ F : HaarL2 S,
    HasSum (fun j : S → HalfNatural => (sqrtCharCoeffProd β j : ℂ) • isotypicProj j F)
        (sqrtLinkOperator β S F) ∧
      HasSum (fun j : S → HalfNatural => charCoeffProd β j • isotypicProj j F)
        (linkProductOperator β S F)
def IsRealSymmPosContraction (A : HaarL2 S →L[ℂ] HaarL2 S) : Prop :=
  IsRealPreserving A ∧ IsSymmetricOp A ∧ IsPositiveOp A ∧ ‖A‖ ≤ 1 ∧
    ∀ j : S → HalfNatural, A * isotypicProj j = isotypicProj j * A
def SqrtSquared : Prop :=
  sqrtLinkOperator β S * sqrtLinkOperator β S = linkProductOperator β S ∧
  ∀ x y : S → ComplexMatrix2.specialUnitary,
    ∫ z, sqrtLinkKernel β x z * sqrtLinkKernel β z y ∂ComplexMatrix2.haarPi S =
      linkProductKernel β x y
def HilbertSchmidtAndTraceClass : Prop :=
  IsHilbertSchmidtPW (sqrtLinkOperator β S) ∧ IsTraceClassPW (linkProductOperator β S)
def TruncInvSqrtProps : Prop :=
  ∀ k : HalfNatural,
    IsRealPreserving (truncInvSqrtLinkOperator β S k) ∧
    IsSymmetricOp (truncInvSqrtLinkOperator β S k) ∧
    (∀ j : S → HalfNatural, truncInvSqrtLinkOperator β S k * isotypicProj j =
      isotypicProj j * truncInvSqrtLinkOperator β S k) ∧
    sqrtLinkOperator β S * truncInvSqrtLinkOperator β S k = truncationProj S k ∧
    truncInvSqrtLinkOperator β S k * sqrtLinkOperator β S = truncationProj S k
end Properties
def SqrtSquaredOnGroup (β : ℝ) : Prop :=
  ∀ g h : ComplexMatrix2.specialUnitary,
    ∫ z, sqrtKernel β g z * sqrtKernel β z h ∂ComplexMatrix2.haarProb =
      InfiniteLattice.singleBondWeight β (g * h⁻¹)
def HilbertSchmidtAndTraceClassOnGroup (β : ℝ) : Prop :=
  ∀ (I : Type) [Unique I],
    IsHilbertSchmidtPW (liftToUnique I (sqrtOperator β)) ∧
      IsTraceClassPW (liftToUnique I (singleLinkOperator β))
def SqrtLinkKernelFacts : Prop :=
  ∀ β : ℝ, 0 < β →
    (∀ (S : Type) [Finite S] [Nonempty S],
      SqrtKernelRealSymmContinuous β S ∧ KernelExpansions β S ∧ PeterWeylBounds β S ∧
      IsotypicEigenvalues β S ∧ StrongExpansions β S ∧
      IsRealSymmPosContraction S (sqrtLinkOperator β S) ∧
      IsRealSymmPosContraction S (linkProductOperator β S) ∧
      SqrtSquared β S ∧ HilbertSchmidtAndTraceClass β S ∧ TruncInvSqrtProps β S) ∧
    SqrtSquaredOnGroup β ∧ HilbertSchmidtAndTraceClassOnGroup β
end YangMills.Construction.TransferOperators.SqrtLinkFacts
end
