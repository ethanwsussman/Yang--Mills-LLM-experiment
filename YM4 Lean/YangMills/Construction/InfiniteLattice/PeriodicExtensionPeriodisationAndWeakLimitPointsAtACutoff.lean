import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import YangMills.Construction.InfiniteLattice.TorusMeasuresConnectedFunctionsAndCentredMomentsOfTheInfiniteLattice
import YangMills.Construction.Lattice.KernelsLocalLogarithmAndConnectedFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff
def projectPair (L m : ℕ) (b : InfiniteLattice.AmbientSpace × InfiniteLattice.AmbientSpace) :
    PeriodicLattice.FourTorus L m × PeriodicLattice.FourTorus L m :=
  (TorusMetric.torusProj (PeriodicLattice.torusSide L m) b.1,
    TorusMetric.torusProj (PeriodicLattice.torusSide L m) b.2)
section Periodization
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
def periodizeTuple (L m : ℕ) {n : ℕ} (f : Fin n → InfiniteLattice.AmbientSpace → E) :
    Fin n → PeriodicLattice.FourTorus L m → E :=
  fun i => TestFunctions.periodize (PeriodicLattice.torusSide L m) (f i)
end Periodization
abbrev cutoffConnectedFunction (L m K : ℕ) (β : ℝ) {n : ℕ}
    (f : Fin n → PeriodicLattice.FourTorus L m → ℝ) : ℂ :=
  PeriodicLattice.connectedFunction L m K (β : ℂ) f
def IsWeakClusterPoint (L K : ℕ) (β : ℝ)
    (ν : ProbabilityMeasure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :
    Prop :=
  ∀ U ∈ @nhds _ (InfiniteLattice.probabilityMeasuresWeakTopology _) ν, ∀ r₀ : ℝ,
    ∃ m : ℕ, 0 < m ∧ r₀ ≤ PeriodicLattice.torusSide L m ∧ ∃ ρ ∈ U,
      (ρ : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) =
        InfiniteLattice.PeriodicTorusMeasures.pushforwardWilsonMeasure L m K β
def weakClusterPoints (L K : ℕ) (β : ℝ) :
    Set (ProbabilityMeasure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :=
  {ν | IsWeakClusterPoint L K β ν}
end YangMills.Construction.InfiniteLattice.PeriodicLiftAtCutoff
end
