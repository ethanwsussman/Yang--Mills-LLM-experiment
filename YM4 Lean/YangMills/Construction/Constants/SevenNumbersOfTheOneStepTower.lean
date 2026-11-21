import YangMills.Construction.Lattice.OneStepBoundsOfTheGaugeFunctional
import YangMills.Construction.Lattice.SmallPlaquetteThresholdInTheToolbox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneStepTower
open PeriodicLattice
def bondCurvature (L : ℕ) : ℝ := 11 * bondFieldRadius L ^ (-2 : ℤ)
def averageGrowth (L : ℕ) : ℝ :=
  8 * (L : ℝ) ^ 4 * ((admissibleStepRadius L)⁻¹ + 2) * (3 * Real.pi * (L : ℝ)) *
    (admissibleStepRadius L)⁻¹
def gaugeSize (L : ℕ) : ℝ := 2 + 32 * gaugeStepMultiplier L
def logRadius (L : ℕ) : ℝ :=
  min 1 (min (bondFieldRadius L / 4) (Real.log 2 / (64 * bondCurvature L * (L : ℝ) ^ 2)))
def averageConstant (L : ℕ) : ℝ := max (8 * averageGrowth L / (L : ℝ) ^ 3) (8 / logRadius L)
def plaquetteSmallness (L : ℕ) : ℝ :=
  min (smallPlaquetteThreshold L) (min (1 / averageConstant L)
    (min (Real.log 2 / (8 * averageGrowth L * (L : ℝ)))
      ((L : ℝ) ^ 2 / (4 * gaugeStepMultiplier L * gaugeSize L))))
end YangMills.Construction.OneStepTower
end
