import YangMills.Construction.InfiniteLattice.ErgodicPhases
import YangMills.Construction.InfiniteLattice.RationalPolynomialsInTheEntriesAndMeansOverBoxes
import YangMills.Construction.InfiniteLattice.StatesAtOneSpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def meanVarianceDefect (ρ : GaugeFieldProbability a)
    (F : GaugeField a → ℝ) (n : ℕ) : ℂ :=
  ρ.expect (fun U => cornerCubeAverage n (fun V => (F V : ℂ)) U ^ 2) -
    ρ.expect (fun U => (F U : ℂ)) ^ 2
def ConditionalStatesAreErgodic (L K : ℕ) (β : ℝ) : Prop :=
  ∀ ν ∈ periodicGibbsStates L K β,
    ∀ κ : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) →
        GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)),
      IsInvariantDisintegration ν.1 κ →
        ∃ N : Set (GaugeField (PeriodicLattice.meshSize L (K : ℤ))),
          MeasurableSet N ∧ ν.1 N = 0 ∧
            ∀ U, U ∉ N → κ U ∈ periodicGibbsStates L K β ∧
              IsShiftErgodic (κ U).1
def ErgodicIffMeanVarianceVanishes (L K : ℕ) (β : ℝ) : Prop :=
  ∀ ρ ∈ periodicGibbsStates L K β,
    IsShiftErgodic ρ.1 ↔
      ∀ F ∈ ratPolyObservables (PeriodicLattice.meshSize L (K : ℤ)),
        Tendsto (meanVarianceDefect ρ F) atTop (𝓝 0)
def ErgodicPeriodicStatesMeasurable (L K : ℕ) (β : ℝ) : Prop :=
  MeasurableSet {ρ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)) |
    ρ ∈ periodicGibbsStates L K β ∧ IsShiftErgodic ρ.1}
def ErgodicDecompositionStatement : Prop :=
  ∀ L K : ℕ, Odd L → 13 ≤ L → 0 < K → ∀ β : ℝ, 0 < β →
    ConditionalStatesAreErgodic L K β ∧
    ErgodicIffMeanVarianceVanishes L K β ∧
    ErgodicPeriodicStatesMeasurable L K β
end YangMills.Construction.InfiniteLattice
