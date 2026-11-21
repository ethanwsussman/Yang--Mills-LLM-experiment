import YangMills.Construction.Lattice.AveragesOfSmallPlaquettes
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def stepBondRemainderConst (L : ℕ) : ℝ := 11 / stepBondRadius L ^ 2
def stepCurvatureDeviationConst (L : ℕ) : ℝ :=
  8 * (L : ℝ) ^ 4 * ((stepRadius L)⁻¹ + 2) * (3 * Real.pi * (L : ℝ)) / stepRadius L
def straightenedRadius (L : ℕ) : ℝ :=
  min 1 (min (stepBondRadius L / 4)
    (min ((L : ℝ) ^ 2 * Real.log 2 / (8 * stepBondRemainderConst L))
      (Real.log 2 / (64 * stepBondRemainderConst L * (L : ℝ) ^ 2))))
def straightenedRemainderConstant (L : ℕ) : ℝ :=
  max (8 * stepCurvatureDeviationConst L * (L : ℝ) ^ (-3 : ℤ)) (8 / straightenedRadius L)
def straightenedDerivConstant (L : ℕ) : ℝ := 4 / straightenedRadius L
def accumulatedFactorConstant (L : ℕ) : ℝ := 2 * stepBallConstant L
def straightenedCurvatureThreshold (L : ℕ) : ℝ :=
  min (smallCurvatureThreshold L)
    (min ((L : ℝ) ^ 3 * Real.log 2 / (8 * stepCurvatureDeviationConst L))
      (min (1 / straightenedRemainderConstant L)
        (Real.log 2 / (8 * stepCurvatureDeviationConst L * (L : ℝ)))))
end YangMills.Construction.PeriodicLattice
