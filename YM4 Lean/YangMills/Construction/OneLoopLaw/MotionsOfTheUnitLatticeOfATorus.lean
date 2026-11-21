import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace UnitLatticeMotions
open Tower PeriodicOperators Tower.OrthogonalMotions
def IsInducedByMotion {L n : ℕ}
    (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (m : Fin 4 → ℤ) : Prop :=
  ∀ x : InfiniteLattice.AmbientSpace,
    f (TorusMetric.torusProj (PeriodicLattice.torusSide L n) x) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L n) (R.mulVec x + castVec m)
def permMatrix (σ : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun ν μ => if ν = σ μ then 1 else 0
def axisReflectionMatrix (ρ : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun μ => if μ = ρ then -1 else 1
def Statement : Prop :=
  (∀ σ, permMatrix σ ∈ Matrix.orthogonalGroup (Fin 4) ℝ ∧
    IsIntegerMatrix (permMatrix σ)) ∧
  (∀ ρ, axisReflectionMatrix ρ ∈ Matrix.orthogonalGroup (Fin 4) ℝ ∧
    IsIntegerMatrix (axisReflectionMatrix ρ)) ∧
  IsIntegerMatrix 1 ∧
  ∀ L n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, IsIntegerMatrix R → ∀ m : Fin 4 → ℤ,
      ∃ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
        IsInducedByMotion f R m ∧ IsDistancePreserving f ∧ MapsSublatticeOnto 0 0 f
end UnitLatticeMotions
end YangMills.Construction
end
