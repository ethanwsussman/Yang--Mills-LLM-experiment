import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import YangMills.Construction.Towers.TheFamiliesOfTheTotalNormaliser
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields
namespace RunningCouplingSlope
def thirdGenerator : imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
def centredCoords {s : ℕ} (x : TorusSite s) : Fin 4 → ℤ := fun μ => (x μ).valMinAbs
def cosinePhase {s : ℕ} (t : ℝ) (x : TorusSite s) : ℝ := Real.cos (t * (centredCoords x 0 : ℝ))
def chainCosineSum (a ρ : ℝ) (L n k : ℕ) [NeZero (2 * L ^ n)] (t : ℝ) : ℝ :=
  ∑ x : TorusSite (2 * L ^ n), SlopeCoefficient.hessianAtTrivial (SlopeCoefficient.chainLogarithm a ρ L k) (2 * L ^ n)
    (0, SlopeCoefficient.secondAxis) (x, SlopeCoefficient.secondAxis) thirdGenerator thirdGenerator * cosinePhase t x
def differenceCosineSum (a : ℝ) (L n k : ℕ) [NeZero (2 * L ^ n)] (t : ℝ) : ℝ :=
  ∑ x : TorusSite (2 * L ^ n), differenceKernelFinite a L n k (centredCoords x) * cosinePhase t x
def normaliserCosineSum (L n k : ℕ) (t : ℝ) : ℝ :=
  ((((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
    PeriodicOperators.Tempered.complexHessian (Tower.logNormaliserFamily L k) n
      (PeriodicOperators.Tempered.fourierModeForm L n 2 (Pi.single 0 t) SlopeCoefficient.secondAxis)
      (PeriodicOperators.Tempered.fourierModeForm L n 2 (-Pi.single 0 t) SlopeCoefficient.secondAxis)).re
end RunningCouplingSlope
end YangMills.Construction
end
