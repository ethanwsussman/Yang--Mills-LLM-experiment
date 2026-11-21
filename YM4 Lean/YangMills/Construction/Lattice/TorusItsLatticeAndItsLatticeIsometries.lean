import YangMills.Construction.Conventions.TorusPeriodsAndIsometries
import YangMills.Construction.Geometry.CenteredRepresentative
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Conventions.StandingParameters
variable (s : StandingParameters)
def meshLatticeVectors : Set (Fin 4 → ℝ) :=
  Set.range (TestFunctions.latticeTranslate s.cutoffMesh)
def SideOverMeshAndSiteLifts : Prop :=
  PeriodicLattice.torusSide s.L s.m / s.cutoffMesh = 2 * (s.L : ℝ) ^ ((s.m : ℕ) + (s.K : ℕ)) ∧
    (∃ n : ℤ, PeriodicLattice.torusSide s.L s.m / s.cutoffMesh = (n : ℝ)) ∧
    s.periodLattice ⊆ s.meshLatticeVectors ∧
    ∀ x : Fin 4 → ℝ,
      TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) x ∈ s.cutoffLattice ↔
        x ∈ s.meshLatticeVectors
def TorusProjIsSurjectiveHom : Prop :=
  (∀ y y' : s.Torus, y + y' = y' + y) ∧
    (∀ x x' : Fin 4 → ℝ,
      TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) (x + x') =
        TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) x +
          TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) x') ∧
    Function.Surjective (TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m)) ∧
    ∀ x ζ : Fin 4 → ℝ,
      s.addVector (TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) x) ζ =
        TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) (x + ζ)
def CutoffIsometriesFormGroup : Prop :=
  (1 : Equiv.Perm s.Torus) ∈ s.cutoffLatticeIsometries ∧
    (∀ r r' : Equiv.Perm s.Torus, r ∈ s.cutoffLatticeIsometries →
      r' ∈ s.cutoffLatticeIsometries → r * r' ∈ s.cutoffLatticeIsometries) ∧
    (∀ r : Equiv.Perm s.Torus, r ∈ s.cutoffLatticeIsometries → r⁻¹ ∈ s.cutoffLatticeIsometries) ∧
    ∃ H : Subgroup (Equiv.Perm s.Torus), (H : Set (Equiv.Perm s.Torus)) = s.cutoffLatticeIsometries
def TorusLatticeAndIsometryFacts : Prop :=
  ∀ s : StandingParameters,
    s.SideOverMeshAndSiteLifts ∧
      s.TorusProjIsSurjectiveHom ∧
      (∀ y : s.Torus, ∃! z : Fin 4 → ℝ, s.IsCenteredLift y z) ∧
      s.CutoffIsometriesFormGroup
end Conventions.StandingParameters
end YangMills.Construction
