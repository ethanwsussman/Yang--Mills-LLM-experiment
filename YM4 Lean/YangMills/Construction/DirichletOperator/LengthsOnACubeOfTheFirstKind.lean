import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.LocalOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.FirstTypeCubeNorms
def Claim : Prop :=
  ∀ (S : RegionSequence.NestedRegions) (K m M R₁ : ℕ), S.IsLevelUnitChain K m M R₁ →
    ∀ Q : LevelCube S M, Q.IsFirstType → ∀ p p' : Fin 4 → ℝ,
      (∀ μ, |p μ - Q.liftedCentre μ| < cubeSide S M Q.level) →
      (∀ μ, |p' μ - Q.liftedCentre μ| < cubeSide S M Q.level) →
      lOneNorm ((torusProj 4 Q.system.setting.side p : Q.system.setting.Point) -
          (torusProj 4 Q.system.setting.side p' : Q.system.setting.Point)) = ∑ μ, |p μ - p' μ| ∧
      supNorm ((torusProj 4 Q.system.setting.side p : Q.system.setting.Point) -
          (torusProj 4 Q.system.setting.side p' : Q.system.setting.Point)) = ‖p - p'‖ ∧
      lOneNorm (torusProj 4 S.side p - torusProj 4 S.side p') ≤ ∑ μ, |p μ - p' μ| ∧
      supNorm (torusProj 4 S.side p - torusProj 4 S.side p') ≤ ‖p - p'‖
end PartitionCubes.FirstTypeCubeNorms
end YangMills.Construction
