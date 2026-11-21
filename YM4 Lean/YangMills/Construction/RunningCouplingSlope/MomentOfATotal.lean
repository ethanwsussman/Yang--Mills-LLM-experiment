import YangMills.Construction.RunningCouplingSlope.CoefficientOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
variable {n : ℕ}
def momentCutoff (n : ℕ) : ℕ := n / 16
def firstCoordDiff (y y' : TorusFields.TorusSite n) : ℤ := (y' 0 - y 0).valMinAbs
def kernelSecondMoment [NeZero n]
    (K : TorusFields.TorusBond n → TorusFields.TorusBond n → ℝ) : ℝ :=
  -(1 / 2) * ∑ y : TorusFields.TorusSite n, if TorusFields.supDist 0 y ≤ 2 * momentCutoff n then
    ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 *
      K (0, SlopeCoefficient.secondAxis) (y, SlopeCoefficient.secondAxis) else 0
def gaugeTotalMoment (H : SlopeCoefficient.GaugeTotal) (n : ℕ) [NeZero n]
    (X : BlockAverages.imaginaryQuaternions) : ℝ :=
  kernelSecondMoment fun c c' => SlopeCoefficient.hessianAtTrivial H n c c' X X
def linearPotential (c : TorusFields.TorusBond n) : ℝ :=
  if c.2 = SlopeCoefficient.secondAxis then (((c.1 0).valMinAbs : ℤ) : ℝ) else 0
def IsNearOriginBond (h : ℕ) (c : TorusFields.TorusBond n) : Prop :=
  TorusFields.supDist 0 c.1 ≤ h ∧ TorusFields.supDist 0 (c.1 + TorusFields.unitStep n c.2) ≤ h
def siteGradient (φ : TorusFields.TorusSite n → ℝ) (c : TorusFields.TorusBond n) : ℝ :=
  φ (c.1 + TorusFields.unitStep n c.2) - φ c.1
structure IsDecayingFormFamily [NeZero n] (M₀ v : ℝ)
    (H : TorusFields.TorusSite n → TorusFields.TorusBond n → TorusFields.TorusBond n → ℝ) : Prop where
  symm : ∀ Y c c', H Y c c' = H Y c' c
  translation_invariant : ∀ (Y u : TorusFields.TorusSite n) (c c' : TorusFields.TorusBond n),
    H (Y + u) (c.1 + u, c.2) (c'.1 + u, c'.2) = H Y c c'
  vanish_on_gradient : ∀ (Y : TorusFields.TorusSite n) (φ : TorusFields.TorusSite n → ℝ)
    (c : TorusFields.TorusBond n), ∑ b, H Y b c * siteGradient φ b = 0
  exp_decay : ∀ Y c c', |H Y c c'| ≤ M₀ * Real.exp (-(v * TorusFields.supportDiam Y ![c, c']))
def formOnLinearPotential [NeZero n] (h : ℕ)
    (H : TorusFields.TorusBond n → TorusFields.TorusBond n → ℝ) : ℝ := open Classical in
  ∑ c : TorusFields.TorusBond n, ∑ c' : TorusFields.TorusBond n,
    if IsNearOriginBond h c ∧ IsNearOriginBond h c' then
      H c c' * linearPotential c * linearPotential c' else 0
def latticeLinearPotential (c : TorusLumps.LatticeBond) : ℝ :=
  if c.2 = SlopeCoefficient.secondAxis then ((c.1 0 : ℤ) : ℝ) else 0
end YangMills.Construction.RunningCouplingSlope
end
