import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.LocalOperators
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.FirstTypeMaps
def Statement : Prop :=
  ∀ (S : RegionSequence.NestedRegions) (K m M R₁ : ℕ), S.IsLevelUnitChain K m M R₁ →
    ∀ Q : LevelCube S M, Q.IsFirstType →
      let O : Set (Fin 4 → ℝ) := {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide S M Q.level}
      let proj : (Fin 4 → ℝ) → Q.system.setting.Point := torusProj 4 Q.system.setting.side
      (∃ h : Q.IsAdmissible, Q.system.setting = Q.torusSetting h) ∧
      BijOn (torusProj 4 S.side) O Q.strictPts ∧
      InjOn proj (closedCube Q.liftedCentre (6 * cubeSide S M Q.level)) ∧
      (∀ p ∈ O, Q.system.embed (torusProj 4 S.side p) = proj p) ∧
      BijOn Q.system.embed Q.strictPts (proj '' O) ∧
      ∀ p v : Fin 4 → ℝ, p ∈ O → p + v ∈ O →
        Q.system.embed (torusProj 4 S.side p + torusProj 4 S.side v) =
          Q.system.embed (torusProj 4 S.side p) + proj v
end YangMills.Construction.PartitionCubes.FirstTypeMaps
