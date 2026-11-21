import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.TransferOperators
structure CubicPeriodSublattice where
  side : ℕ
  one_le_side : 1 ≤ side
  lattice : InfiniteLattice.PeriodSublattice 1
  periods_eq : lattice.periods = InfiniteLattice.cubicSublattice 1 (side : ℝ)
section Operators
variable {J : Type} [Countable J]
def IsRealPreserving (A : HaarL2 J →L[ℂ] HaarL2 J) : Prop :=
  ∀ φ : HaarL2 J,
    (∀ᵐ u ∂ComplexMatrix2.haarPi J, ((φ : (J → ComplexMatrix2.specialUnitary) → ℂ) u).im = 0) →
      ∀ᵐ u ∂ComplexMatrix2.haarPi J, ((A φ : (J → ComplexMatrix2.specialUnitary) → ℂ) u).im = 0
def IsSymmetricOp (A : HaarL2 J →L[ℂ] HaarL2 J) : Prop :=
  ∀ φ ψ : HaarL2 J, inner ℂ φ (A ψ) = inner ℂ (A φ) ψ
def IsPositiveOp (A : HaarL2 J →L[ℂ] HaarL2 J) : Prop :=
  IsSymmetricOp A ∧
    ∀ φ : HaarL2 J, 0 ≤ (inner ℂ φ (A φ) : ℂ).re ∧ (inner ℂ φ (A φ) : ℂ).im = 0
def OpLE (A A' : HaarL2 J →L[ℂ] HaarL2 J) : Prop :=
  IsPositiveOp (A' - A)
end Operators
end YangMills.Construction.TransferOperators
end
