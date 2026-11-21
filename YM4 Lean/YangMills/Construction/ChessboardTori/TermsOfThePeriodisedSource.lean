import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
def PeriodizedSourceTerms.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ C ∈ g.cellSet, ∀ (v : AmbientSpace → ℂ) (Q : Set AmbientSpace), (∃ M : ℝ, ∀ x, ‖v x‖ ≤ M) →
      (∀ x, x ∉ Q → v x = 0) → IsCompact Q → Q ⊆ interior C →
      (∀ x ∈ Q, ∀ y ∈ g.walls, 1 ≤ TorusMetric.euclidNormVec (x - y)) →
      (fun U => Complex.exp (D.smeared v U)) ∈ ReflectionGrid.cellObservables (D := D) C ∧
      (∀ x, {r : g.reflectionGroup |
        Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x)) ≠ 0}.Subsingleton) ∧
      g.IsReflectionPeriodic fun x =>
        ∑ᶠ r : g.reflectionGroup, Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x))
end YangMills.Construction.ChessboardTori
end
