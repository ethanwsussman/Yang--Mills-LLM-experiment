import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
def PeriodizedSourceExpectation.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D),
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ S ∈ g.cellSet, ∀ (v : AmbientSpace → ℂ) (Q : Set AmbientSpace), (∃ C : ℝ, ∀ x, ‖v x‖ ≤ C) →
      (∀ x, x ∉ Q → v x = 0) → IsCompact Q → Q ⊆ interior S →
      (∀ x ∈ Q, ∀ y ∈ g.walls, 1 ≤ TorusMetric.euclidNormVec (x - y)) →
      (∀ (x : AmbientSpace) (k : Fin 4 → ℤ),
        (∑ᶠ r : g.reflectionGroup, Conventions.signedConj (orientationSign r.1)
            (v (r.1⁻¹ (x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k)))) =
          ∑ᶠ r : g.reflectionGroup, Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x))) ∧
      ∀ B ∈ g.blocks,
        D.liftedExpectation (fun U => ∏ᶠ S' ∈ g.cellsWithin B,
            g.transportTo S S' (fun U' => Complex.exp (D.smeared v U')) U) =
          D.partitionFunctionOfPeriodic
              (fun x => ∑ᶠ r : g.reflectionGroup,
                Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x))) /
            D.partitionFunction 0
end YangMills.Construction.ChessboardTori
end
