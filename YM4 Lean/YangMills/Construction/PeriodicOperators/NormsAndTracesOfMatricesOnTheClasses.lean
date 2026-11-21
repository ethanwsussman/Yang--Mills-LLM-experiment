import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.QuotMatrixNorms
def NormAxioms (I I' : PeriodicData) : Prop :=
  (∀ M : QuotHom I I', quotHomNorm M < ∞) ∧
  (∀ M N : QuotHom I I', quotHomNorm (M + N) ≤ quotHomNorm M + quotHomNorm N) ∧
  (∀ (a : ℂ) (M : QuotHom I I'), quotHomNorm (a • M) ≤ ENNReal.ofReal ‖a‖ * quotHomNorm M) ∧
  quotHomNorm (0 : QuotHom I I') = 0 ∧
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : QuotHom I I') (c' : I'.UnitQuot) (c : I.UnitQuot),
    ‖linearMapEntry M c' c‖ ≤ C * (quotHomNorm M).toReal
def NormSubmul (I I' I'' : PeriodicData) : Prop :=
  ∀ (M : QuotHom I I') (N : QuotHom I'' I),
    quotHomNorm (M.comp N) ≤ quotHomNorm M * quotHomNorm N
def UnitTraceBound (I : PeriodicData) : Prop :=
  quotHomNorm (LinearMap.id : QuotHom I I) ≤ 1 ∧
  ∃ C : ℝ, 0 ≤ C ∧ ∀ M : QuotHom I I,
    ‖LinearMap.trace ℂ (I.UnitQuot → ℂ) M‖ ≤ C * (quotHomNorm M).toReal
def Claim : Prop :=
  ∀ I I' I'' : PeriodicData, IsPeriodic I → IsPeriodic I' → IsPeriodic I'' →
    NormAxioms I I' ∧ NormSubmul I I' I'' ∧ UnitTraceBound I
end YangMills.Construction.PeriodicOperators.QuotMatrixNorms
end
