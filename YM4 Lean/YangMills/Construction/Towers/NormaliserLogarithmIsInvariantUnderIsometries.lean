import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LogNormaliserRatioSymmetryInvariant : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → ∀ i : ℕ, i + 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
      ∀ s : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
        IsLevelSymmetry k (i + 1) s →
        logNormaliserRatio L n k i (pushField s W) = logNormaliserRatio L n k i W
end YangMills.Construction.Tower
end
