import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds
structure BoundedDerivsAtScale {S : RegionSequence.NestedRegions} (c r : ℝ)
    (φ : S.Point → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  le_one : ∀ x, φ x ≤ 1
  smooth : ContDiff ℝ 2 fun p : Fin 4 → ℝ => φ (Torus.torusProj 4 S.side p)
  deriv_bound : ∀ i ≤ 2, ∀ (μ : Fin i → Fin 4) (p : Fin 4 → ℝ),
    |iteratedFDeriv ℝ i (fun p : Fin 4 → ℝ => φ (Torus.torusProj 4 S.side p)) p
      fun k => Pi.single (μ k) 1| ≤ c * r⁻¹ ^ i
def Claim : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ (K m M R₁ : ℕ) (S : RegionSequence.NestedRegions),
    S.IsLevelUnitChain K m M R₁ → S.L ^ 5 ≤ M → ∀ Q : LevelCube S M,
      BoundedDerivsAtScale c (mollifyRadius S M Q.level) Q.partitionFn ∧
        BoundedDerivsAtScale c (mollifyRadius S M Q.level) Q.smallCutoff ∧
        BoundedDerivsAtScale c (mollifyRadius S M Q.level) Q.largeCutoff
end YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds
