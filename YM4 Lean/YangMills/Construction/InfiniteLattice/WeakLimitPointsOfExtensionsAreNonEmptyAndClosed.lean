import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions
def subsequentialLimits (L K : ℕ) (β : ℝ) :
    Set (RealWeakState (PeriodicLattice.meshSize L (K : ℤ))) :=
  {ν | ∃ (i : ℕ → ℕ) (ρ : ℕ → RealWeakState (PeriodicLattice.meshSize L (K : ℤ))),
    StrictMono i ∧ (∀ n, 1 ≤ i n) ∧
    (∀ n, (ρ n).measure = InfiniteLattice.liftedWilsonMeasure L (i n) K β) ∧
    RealWeakState.TendstoWeakly ρ ν}
def LimitSetIsNonemptyClosed : Prop :=
  ∀ (s : Conventions.StandingParameters) (β : ℝ), 0 < β →
    limitsOfLiftedMeasures s.L s.K β = subsequentialLimits s.L s.K β ∧
    (limitsOfLiftedMeasures s.L s.K β).Nonempty ∧
    IsClosed (limitsOfLiftedMeasures s.L s.K β)
end YangMills.Construction.InfiniteLattice.PeriodicExtensions
