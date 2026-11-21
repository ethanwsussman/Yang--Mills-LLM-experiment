import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.RefinedLattices
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicGibbsAtCutoff
open YangMills.Construction.InfiniteLattice
variable (L K : ℕ)
abbrev gibbsSet (β : ℝ) : Set (Measure (RefinedGaugeField L K)) :=
  periodicGibbsSet L K β
variable {L K}
theorem isProbabilityMeasure_of_mem_gibbsSet {β : ℝ} {μ : Measure (RefinedGaugeField L K)}
    (hμ : μ ∈ gibbsSet L K β) : IsProbabilityMeasure μ :=
  hμ.1.1
abbrev smearedObservable (f : AmbientSpace → ℝ) : RefinedGaugeField L K → ℝ :=
  smearedEnergy f
abbrev connectedCorrelation (μ : Measure (RefinedGaugeField L K)) (n : ℕ)
    (f : Fin n → AmbientSpace → ℝ) : ℂ :=
  ursellFunction μ n f
abbrev expectation (μ : Measure (RefinedGaugeField L K)) (A : RefinedGaugeField L K → ℂ) : ℂ :=
  ∫ U, A U ∂μ
end YangMills.Construction.PeriodicGibbsAtCutoff
