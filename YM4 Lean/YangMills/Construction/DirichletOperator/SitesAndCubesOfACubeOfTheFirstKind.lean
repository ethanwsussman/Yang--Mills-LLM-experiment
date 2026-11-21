import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.LocalOperators
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.FirstTypeLattice
def Statement : Prop :=
  ∀ (S : RegionSequence.NestedRegions) (K m M R₁ : ℕ), S.IsLevelUnitChain K m M R₁ →
    ∀ Q : LevelCube S M, Q.IsFirstType →
      ∀ j : ℕ, j ≤ Q.level ∨ (j = Q.level + 1 ∧ Q.level < S.s) →
        Q.system.embed '' ((spacingLattice 4 S.side (S.scale j) : Set S.Point) ∩ Q.strictPts) =
            (spacingLattice 4 Q.system.setting.side (S.scale j) : Set Q.system.setting.Point) ∩
              (fun p : Fin 4 → ℝ => (torusProj 4 Q.system.setting.side p : Q.system.setting.Point)) ''
                {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide S M Q.level} ∧
          (fun C => Q.system.embed '' C) ''
              {C | C ∈ cubePartition 4 S.side (S.scale j) ∧ C ⊆ Q.strictPts} =
            {C | C ∈ cubePartition 4 Q.system.setting.side (S.scale j) ∧
              C ⊆ (fun p : Fin 4 → ℝ =>
                  (torusProj 4 Q.system.setting.side p : Q.system.setting.Point)) ''
                {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide S M Q.level}}
end YangMills.Construction.PartitionCubes.FirstTypeLattice
