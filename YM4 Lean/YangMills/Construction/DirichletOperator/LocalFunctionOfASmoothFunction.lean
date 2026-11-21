import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.LocalOperators
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff
open YangMills.Construction.Torus YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.TransferOfSmooth
def Statement : Prop :=
  ∀ (S : RegionSequence.NestedRegions) (K m M R₁ : ℕ), S.IsLevelUnitChain K m M R₁ →
    ∀ Q : LevelCube S M, Q.IsFirstType → ∀ f : S.Point → ℝ, tsupport f ⊆ Q.thicken (5 / 6) →
      ContDiff ℝ ∞ (fun p => f (torusProj 4 S.side p)) →
      ContDiff ℝ ∞ (fun p => Q.system.transferFn f (torusProj 4 Q.system.setting.side p)) ∧
      (∀ (k : ℕ) (ν : Fin k → Fin 4),
        ⨆ p, |iteratedFDeriv ℝ k
            (fun p => Q.system.transferFn f (torusProj 4 Q.system.setting.side p)) p
            fun i => Pi.single (ν i) 1| =
          ⨆ p, |iteratedFDeriv ℝ k (fun p => f (torusProj 4 S.side p)) p
            fun i => Pi.single (ν i) 1|) ∧
      ∀ x x' : Q.system.setting.Point,
        |Q.system.transferFn f x - Q.system.transferFn f x'| ≤
          (⨆ μ : Fin 4, ⨆ p, |iteratedFDeriv ℝ 1 (fun p => f (torusProj 4 S.side p)) p
            fun _ => Pi.single μ 1|) * lOneNorm (x - x')
end YangMills.Construction.PartitionCubes.TransferOfSmooth
