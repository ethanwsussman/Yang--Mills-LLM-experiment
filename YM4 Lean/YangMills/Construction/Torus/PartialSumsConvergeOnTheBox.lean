import YangMills.Construction.Torus.PeriodBoxModesCoefficientsAndPartialSums
import YangMills.Construction.Torus.TestFunctionsAndDistributionsOnOpenSetsOfTuples
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.FourierPartialSums
open AmbientPoints Torus.FourierBox
def Statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (p : ℕ), 1 ≤ p → ∀ P : ℝ, 0 < P →
    ∀ F ∈ testFns (fundamentalBoxPow s p P), ∀ α : YangMills.Construction.PowerSeries.MultiIndex (4 * p),
      Tendsto
        (fun t : ℕ+ => ⨆ u ∈ fundamentalCube (4 * p) P, ENNReal.ofReal
          ‖(∑ k ∈ modesWithin (t : ℕ), fourierCoeff P F k * iteratedPartial α (fourierMode P k) u) -
            multiDeriv α F (tupleProj s .euclidean p u)‖)
        atTop (𝓝 0)
end YangMills.Construction.FourierPartialSums
