import YangMills.Construction.Lattice.FluctuationFormAtAComplexPair
import YangMills.Construction.Lattice.FluctuationFormOfAStepAtAPoint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubesOfStep
variable (c : ParameterChoice.ChoiceUpToDegreeConstants) {m K k : ℕ} (D : StepData c.L m K k)
  (p : BondAtLevel c.L m K k → Matrices.ComplexMatrix2)
def realPartForm (B : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  fun e => (1 / 2 : ℂ) • (B e + (B e).conjTranspose)
def imagPartForm (B : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  fun e => (2 * Complex.I)⁻¹ • (B e - (B e).conjTranspose)
def complexHessianBilin (U W : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) : ℂ :=
  ((hessianBilin c D p (realPartForm c U) (realPartForm c W) -
      hessianBilin c D p (imagPartForm c U) (imagPartForm c W) : ℝ) : ℂ) +
    Complex.I *
      ((hessianBilin c D p (realPartForm c U) (imagPartForm c W) +
        hessianBilin c D p (imagPartForm c U) (realPartForm c W) : ℝ) : ℂ)
def eliminatedBilin (U W : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) : ℂ :=
  complexHessianBilin c D p (eliminateAt c D p U) (eliminateAt c D p W)
def IsCompressedOperatorValue (Y : Set (BondAtLevel c.L m K k))
    (A G : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) : Prop :=
  G ∈ ComplexPairFluctuation.formsSupportedOn Y ∧
    ∀ A' ∈ ComplexPairFluctuation.formsSupportedOn Y, bondFormInner 1 A' G = eliminatedBilin c D p A' A
def compressedOperator (Y : Set (BondAtLevel c.L m K k))
    (A : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  Classical.epsilon (IsCompressedOperatorValue c D p Y A)
def freeOperator (A : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  compressedOperator c D p (freeVariableBonds c D) A
def restrictForm (Y : Set (BondAtLevel c.L m K k))
    (A : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  open Classical in
  fun e => if (e.IsPositivelyOriented ∧ e ∈ Y) ∨ (e.opposite.IsPositivelyOriented ∧ e.opposite ∈ Y)
    then A e else 0
def fluctuationCovariance (Y : Set (BondAtLevel c.L m K k)) :
    (BondAtLevel c.L m K k → Matrices.ComplexMatrix2) →
      BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  Function.invFunOn (compressedOperator c D p Y) (ComplexPairFluctuation.formsSupportedOn Y)
def conditionalForm (Y : Set (BondAtLevel c.L m K k))
    (A : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) : ℂ :=
  bondFormInner 1 A (freeOperator c D p A) -
    bondFormInner 1 (freeOperator c D p A)
      (restrictForm c Y (fluctuationCovariance c D p Y
        (restrictForm c Y (freeOperator c D p A))))
end YangMills.Construction.PeriodicLattice.CubesOfStep
