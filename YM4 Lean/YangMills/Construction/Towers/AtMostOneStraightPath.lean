import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace AxisPathUniqueness
def OnPeriodicLattice (L n₀ k i : ℕ) : Prop :=
  (∀ (α β : Fin 4) (m m' : ℤ),
    ((|m| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L n₀ / 2 →
    ((|m'| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L n₀ / 2 →
    m • PeriodicLattice.unitStep L n₀ (PeriodicLattice.levelDepth k i) α =
      m' • PeriodicLattice.unitStep L n₀ (PeriodicLattice.levelDepth k i) β →
    (m = 0 ∧ m' = 0) ∨ (α = β ∧ m = m')) ∧
  ∀ (u v : Vertex L n₀ k i) (α β : Fin 4) (m m' : ℤ),
    v - u = m • PeriodicLattice.unitStep L n₀ (PeriodicLattice.levelDepth k i) α →
    ((|m| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L n₀ / 2 →
    v - u = m' • PeriodicLattice.unitStep L n₀ (PeriodicLattice.levelDepth k i) β →
    ((|m'| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L n₀ / 2 →
    PeriodicLattice.flowAlong u α m = PeriodicLattice.flowAlong u β m' ∧
      PeriodicLattice.axialPath u v = PeriodicLattice.flowAlong u α m
def OnFullSpace (L k i : ℕ) : Prop :=
  (∀ (α β : Fin 4) (m m' : ℤ),
    m • InfiniteLattice.axisStep (meshAt L k i) α =
      m' • InfiniteLattice.axisStep (meshAt L k i) β →
    (m = 0 ∧ m' = 0) ∨ (α = β ∧ m = m')) ∧
  ∀ (u v : FullSpace.Vertex L k i) (α β : Fin 4) (m m' : ℤ),
    FullSpace.IsAxisDisplacement u v α m → FullSpace.IsAxisDisplacement u v β m' →
    FullSpace.signedSteps u α m = FullSpace.signedSteps u β m' ∧
      FullSpace.axisPath u v = FullSpace.signedSteps u α m
def AxisPathsUnique : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k i : ℕ, i ≤ k →
    (∀ n₀ : ℕ, 0 < n₀ → OnPeriodicLattice L n₀ k i) ∧ OnFullSpace L k i
end AxisPathUniqueness
end Tower
end YangMills.Construction
end
