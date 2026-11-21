import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def SupBallDeterminesCentre : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ t : ℕ, t ≤ K →
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ sideInLevelUnits L m K t / 4 →
  ∀ y z : FourTorus L m,
    {x : FourTorus L m | toLevelUnits L K t (TorusMetric.torusSupNorm (x - y)) ≤ ρ} =
      {x : FourTorus L m | toLevelUnits L K t (TorusMetric.torusSupNorm (x - z)) ≤ ρ} →
    y = z
end YangMills.Construction.PeriodicLattice
