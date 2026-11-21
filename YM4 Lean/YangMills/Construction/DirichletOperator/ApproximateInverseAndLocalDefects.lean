import YangMills.Construction.DirichletOperator.BoundsOnTheToriOfTheCubes
import YangMills.Construction.RegionSequence.BlockOperatorNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
open Classical in
def LevelCube.localPart (Q : LevelCube 𝒮 M) (v : Q.system.setting.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  if Q.IsSecondType then projBonds (Q.system.curlComm Q.partitionFn v)
  else Q.system.lapComm Q.partitionFn v + Q.system.avgComm Q.partitionFn v
def LevelCube.localPartAdjoint (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ) :
    Q.system.setting.FineBond → ℝ :=
  adjointValue (Q.system.forms : Set (Q.system.setting.FineBond → ℝ)) bondInner bondInner
    Q.localPart A
def LevelCube.supNbhd (Q : LevelCube 𝒮 M) (X : Set 𝒮.Point) : Set 𝒮.Point :=
  {x | supSetDist {x} X ≤ ENNReal.ofReal (2 * 𝒮.scale (Q.level + 1))}
def LevelCube.toCubeTorusSet (Q : LevelCube 𝒮 M) (X : Set 𝒮.Point) : Set Q.system.setting.Point :=
  Q.system.embed '' (X ∩ Q.thicken (5 / 6))
structure LevelCube.AdjointDivergenceForm (Q : LevelCube 𝒮 M) (C : ℝ)
    (w : 𝒮.oneForms →ₗ[ℝ] Q.system.setting.Tensor 1)
    (u : 𝒮.oneForms →ₗ[ℝ] Q.system.forms) : Prop where
  adjoint_eq : ∀ A : 𝒮.oneForms,
    Q.localPartAdjoint (A : 𝒮.FineBond → ℝ) = divOne (w A) + (u A : _ → ℝ)
  tensor_supported : ∀ A : 𝒮.oneForms,
    CubeTorus.TensorAnchorSupported (Q.toCubeTorusSet (Q.supNbhd Q.supp)) (w A)
  form_supported : ∀ A : 𝒮.oneForms,
    AnchorSupported (Q.toCubeTorusSet (Q.supNbhd Q.supp)) (u A : _ → ℝ)
  bound : ∀ (p : NormExponent) (X : Set 𝒮.Point) (A : 𝒮.oneForms),
    𝒮.scale Q.level *
        (tensorCutSpace Q.system.setting 1).pNorm p (restrictTensor (Q.toCubeTorusSet X) (w A)) +
      𝒮.scale Q.level ^ 2 *
        (formCutSpace Q.system.setting).pNorm p (restrictBonds (Q.toCubeTorusSet X) (u A : _ → ℝ)) ≤
      C * (M : ℝ)⁻¹ *
        (formCutSpace 𝒮).pNorm p (restrictBonds (Q.supNbhd X) (A : 𝒮.FineBond → ℝ))
end PartitionCubes
namespace ApproxInverse
open PartitionCubes
end ApproxInverse
end YangMills.Construction
