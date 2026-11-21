import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter PeriodicLattice
namespace LatticeCounts
def AxisPointCount (L m K : ℕ) : Prop :=
  pointsPerAxis L m K = torusSide L m / meshSize L (K : ℤ) ∧
    pointsPerAxis L m K = 2 * (L : ℝ) ^ (m + K) ∧
    ∀ (y : Site L m (K : ℤ)) (μ : Fin 4),
      ((axisLine y μ).ncard : ℝ) = pointsPerAxis L m K
def FieldsDeterminedByPositiveBonds (L m : ℕ) (j : ℤ) : Prop :=
  Function.Bijective fun U : CompactGaugeField L m j =>
    U.restrictTo (forwardBonds L m j)
def EvenAxisCountAndHalfSide (L m K : ℕ) : Prop :=
  (∃ n : ℤ, Even n ∧ pointsPerAxis L m K = (n : ℝ)) ∧
    3 ≤ pointsPerAxis L m K ∧
    meshSize L (K : ℤ) < torusSide L m / 2
def TorusSidesUnbounded (L : ℕ) : Prop :=
  ¬BddAbove (torusSides L) ∧
    ∀ u : ℕ → ℝ, StrictMono u → (∀ i, u i ∈ torusSides L) → Tendsto u atTop atTop
def torusLatticeFacts : Prop :=
  ∀ s : Conventions.StandingParameters,
    AxisPointCount s.L s.m s.K ∧
      FieldsDeterminedByPositiveBonds s.L s.m ((s.K : ℕ) : ℤ) ∧
      EvenAxisCountAndHalfSide s.L s.m s.K ∧
      TorusSidesUnbounded s.L
end LatticeCounts
end YangMills.Construction
end
