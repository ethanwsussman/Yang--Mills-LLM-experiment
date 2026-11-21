import YangMills.Construction.TorusOrFourSpace.PeriodBoxCharactersAndCoefficients
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.FourierSeriesConvergence
open Kind.Tuple (partialDeriv proj)
open PeriodCell
def TestFnFourierSeriesConverges : Prop :=
  ∀ (D : Params) (p : ℕ+) (P : ℝ), 0 < P → ∀ F ∈ cellTestFns D p P,
    ∀ α : CoordIndex p,
      Tendsto
        (fun t : ℕ+ => ⨆ u ∈ coordCube p P, ENNReal.ofReal
          ‖(∑ k ∈ IntCoords.cubeUpTo t,
              fourierCoeff D P F k * Coords.iterPartial α (fourierChar P k) u) -
            partialDeriv D Kind.euclidean α F (proj D Kind.euclidean u)‖)
        atTop (𝓝 0)
end YangMills.Construction.PeriodicSpace.FourierSeriesConvergence
