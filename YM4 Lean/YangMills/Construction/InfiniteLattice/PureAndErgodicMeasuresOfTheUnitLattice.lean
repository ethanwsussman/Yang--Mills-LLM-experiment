import YangMills.Construction.InfiniteLattice.GibbsKernelAndPeriodicGibbsStatesOfTheUnitLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def IsExtremalUnitPeriodicGibbs (β : ℝ) (μ : Measure (GaugeField (1 : ℝ))) : Prop :=
  μ ∈ periodicGibbsUnit β ∧ ∀ s : ℝ, 0 < s → s < 1 →
    ∀ μ₁ ∈ periodicGibbsUnit β, ∀ μ₂ ∈ periodicGibbsUnit β,
      μ = ENNReal.ofReal s • μ₁ + ENNReal.ofReal (1 - s) • μ₂ → μ₁ = μ ∧ μ₂ = μ
def IsUnitShiftErgodic (μ : Measure (GaugeField (1 : ℝ))) : Prop :=
  IsProbabilityMeasure μ ∧ IsPeriodicMeasure μ ∧
    ∀ E : Set (GaugeField (1 : ℝ)), MeasurableSet[shiftInvariantSigma 1] E → μ E = 0 ∨ μ E = 1
theorem isExtremalUnitPeriodicGibbs_iff (β : ℝ)
    (μ : Measure (GaugeField (1 : ℝ))) :
    IsExtremalUnitPeriodicGibbs β μ ↔ IsExtremalPeriodicGibbs β μ :=
  ⟨fun h => ⟨h.1, fun μ₁ μ₂ h₁ h₂ s hs0 hs1 e => h.2 s hs0 hs1 μ₁ h₁ μ₂ h₂ e⟩,
    fun h => ⟨h.1, fun s hs0 hs1 μ₁ h₁ μ₂ h₂ e => h.2 μ₁ μ₂ h₁ h₂ s hs0 hs1 e⟩⟩
end YangMills.Construction.InfiniteLattice
