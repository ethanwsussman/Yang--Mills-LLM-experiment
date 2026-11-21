import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodSublattice
variable (Γ : PeriodSublattice 1)
def cosetSumOfShifts (Q' : AddSubgroup (LatticePoint 1)) (φ : GaugeField 1 → ℂ)
    (U : Γ.QuotientField) : ℝ :=
  ∑ᶠ c : Q' ⧸ Γ.periods.addSubgroupOf Q',
    (Γ.periodize ((shift ((Quotient.out c : Q') : LatticePoint 1)).actOn φ) U).re
def ExpShiftSumInequality (β : ℝ) (Q' : AddSubgroup (LatticePoint 1)) (φ : GaugeField 1 → ℂ) :
    Prop :=
  ∫ U, Real.exp (Γ.cosetSumOfShifts Q' φ U) * Γ.boltzmannWeight β U ∂Γ.quotientHaar ≤
    ∫ U, Γ.boltzmannWeight β U ∂Γ.quotientHaar
end PeriodSublattice
def PeriodicBoundsPassToInvariantGibbs : Prop :=
  ∀ β : ℝ, 0 < β → ∀ φ ∈ continuousLocalFunctions 1, (∀ U, (φ U).im = 0) →
    ∀ Q' : AddSubgroup (LatticePoint 1), Q'.FiniteIndex →
      (∃ s₀ : ℕ, 3 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → cubicSublattice 1 (s : ℝ) ≤ Q' →
        ∀ Γ : PeriodSublattice 1, Γ.periods = cubicSublattice 1 (s : ℝ) →
          Γ.ExpShiftSumInequality β Q' φ) →
      ∀ ν ∈ subgroupInvariantGibbsClass one_pos β Q', ∫ U, φ U ∂ν ≤ 0
end YangMills.Construction.InfiniteLattice
