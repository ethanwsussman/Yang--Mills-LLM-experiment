import YangMills.Construction.Conventions.RealPowerAndLogarithm
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
open Filter Topology
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.Strip
abbrev UnitStrip : Type := Set.Icc (0 : ℝ) 1 × ℝ
def unitStripPow (t : Set.Icc (0 : ℝ) 1) (a : ℝ) : ℝ :=
  if a = 0 then 1 else YangMills.Construction.RealPower.rpowPos t a
def stripZeroAtInfty : Set (UnitStrip → ℂ) :=
  {g | Continuous g ∧
    Tendsto (fun R : ℝ => ⨆ p : UnitStrip, ⨆ _ : R ≤ |p.2|, ‖g p‖ₑ) atTop (𝓝 0)}
def stripUniformNorm (g : UnitStrip → ℂ) : ℝ :=
  YangMills.Construction.TestFunctions.uniformNorm g
def gaussianDensity (v m y : ℝ) : ℝ :=
  YangMills.Construction.RealPower.rpowPos (2 * Real.pi * v) (-(1 / 2)) *
    Real.exp (-(y - m) ^ 2 / (2 * v))
def gaussianModulatedMonomial (n : ℕ) (m v : ℝ) (p : UnitStrip) : ℂ :=
  (unitStripPow p.1 n : ℂ) * Complex.exp (Complex.I * m * p.2 - v * (p.2 : ℂ) ^ 2 / 2)
def gaussianModulatedSpan : Submodule ℂ (UnitStrip → ℂ) :=
  Submodule.span ℂ {g | ∃ (n : ℕ) (m v : ℝ), 0 < v ∧ g = gaussianModulatedMonomial n m v}
end YangMills.Construction.EuclideanAnalysis.Strip
