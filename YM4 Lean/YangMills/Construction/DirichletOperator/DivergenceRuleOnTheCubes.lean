import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.LocalOperators
import YangMills.Construction.RegionSequence.FineLatticeNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace CubeDivergence
variable {S : NestedRegions} {M : ℕ}
def leibnizRemainder (φ : S.FineSite → ℝ) (J : S.Tensor 1) : S.FineBond → ℝ :=
  ∑ ν, smulSiteBond (translateBackward ν (forwardDiff ν φ)) fun b => J (constIdx ν) (shiftDown ν b)
def pushBonds (C : CubeSystem S) (g : S.FineBond → ℝ) : C.setting.FineBond → ℝ :=
  fun c => ∑ᶠ b ∈ {b : S.FineBond | C.mapBond b = c}, g b
def formDiv (C : CubeSystem S) (w : C.setting.Tensor 1) :
    C.setting.FineBond → ℝ :=
  adjointValue (C.forms : Set (C.setting.FineBond → ℝ)) bondInner tensorInner nablaOne w
open Classical in
def pushedRemainder (Q : LevelCube S M) (J : S.Tensor 1) :
    Q.system.setting.FineBond → ℝ :=
  pushBonds Q.system
    (if Q.IsSecondType then projBonds (leibnizRemainder (fun x => Q.partitionFn x) J)
    else leibnizRemainder (fun x => Q.partitionFn x) J)
def Claim : Prop :=
  ∀ (K m M R₁ : ℕ) (S : NestedRegions), S.IsLevelUnitChain K m M R₁ → S.L ^ 5 ≤ M →
    ∀ Q ∈ active S M, ∀ J : S.Tensor 1,
      Q.system.pullBonds Q.partitionFn (divOne J) =
        formDiv Q.system (Q.system.pullTensor Q.partitionFn J) + pushedRemainder Q J
end CubeDivergence
end YangMills.Construction
