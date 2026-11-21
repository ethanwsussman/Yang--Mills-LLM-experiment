import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
def TorusStatesAreLimitsOfTori : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (K : ℕ+) (β : ℝ), 0 < β →
    ∀ μ : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (((K : ℕ)) : ℤ))),
      (μ ∈ InfiniteLattice.torusLimitSet L K β ∨ InfiniteLattice.IsInfiniteVolumeLimit L K β μ) →
      ∃ sizes : ℕ → ℕ, (∀ j, 0 < sizes j) ∧ Tendsto (fun j => PeriodicLattice.torusSide L (sizes j)) atTop atTop ∧
        ∀ (n : ℕ) (g : Fin n → (Fin 4 → ℝ) → ℝ), 2 ≤ n →
          (∀ j, TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 (g j)) →
          (∀ j, HasCompactSupport (g j)) →
          (∀ j k, j ≠ k → Disjoint (tsupport (g j)) (tsupport (g k))) →
          Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 L (sizes j) K β g) atTop
            (𝓝 (InfiniteLattice.smearedEnergyCumulant μ g))
end YangMills.Construction.TotalDensitiesGiveASystem
end
