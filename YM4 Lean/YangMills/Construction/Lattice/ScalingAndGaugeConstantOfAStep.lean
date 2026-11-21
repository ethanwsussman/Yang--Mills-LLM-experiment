import YangMills.Construction.Lattice.GaugeFixingFactor
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def positiveFreeBondCount (K j : ℕ) (Y : Set (FourTorus L m)) : ℕ :=
  {b : BondAtLevel L m K j | b ∈ nonPivotBonds K j Y ∧ b.IsPositivelyOriented}.ncard
def coarserSiteCount (K j : ℕ) (Y : Set (FourTorus L m)) : ℕ :=
  (sitesIn Y : Set (SiteAtLevel L m K (j + 1))).ncard
def stepScalingGaugeConstant (A₀ : ℝ) (p₀ : ℕ) (x : ℕ → ℝ) (K j : ℕ)
    (Y : Set (FourTorus L m)) : ℝ :=
  (Real.log Matrices.ComplexMatrix2.haarChartDensity -
        (1 / 2) * (Matrices.ComplexMatrix2.realLieDimension : ℝ) * Real.log (x j)) *
      (positiveFreeBondCount K j Y : ℝ) -
    ((L : ℝ) ^ 4 - 1) * Real.log (axialNormalizer (x j) (Thresholds.epsThreshold A₀ p₀ x j)) *
      (coarserSiteCount K j Y : ℝ)
end PeriodicLattice
end YangMills.Construction
