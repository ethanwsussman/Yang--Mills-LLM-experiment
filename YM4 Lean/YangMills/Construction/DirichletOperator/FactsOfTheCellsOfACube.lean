import YangMills.Construction.DirichletOperator.CellsOfACube
import YangMills.Construction.DirichletOperator.FactsOfALocalOperatorOfACube
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes
variable {𝒮 : NestedRegions} {M : ℕ}
def LevelCube.closedSupBall (Q : LevelCube 𝒮 M) (s : 𝒮.Point) : Set 𝒮.Point :=
  {x | supNorm (x - s) ≤ 4 * 𝒮.scale (Q.level + 1)}
def LevelCube.torusSupBall (Q : LevelCube 𝒮 M) (s : Q.system.setting.Point) :
    Set Q.system.setting.Point :=
  {x | supNorm (x - s) ≤ 4 * 𝒮.scale (Q.level + 1)}
def LevelCube.pullSiteFn (Q : LevelCube 𝒮 M) (f : 𝒮.FineSite → ℝ) :
    Q.system.setting.FineSite → ℝ :=
  Q.system.pullSites (indicator (Q.thicken (5 / 6)) fun _ => 1) f
def LevelCube.pullTensorNear {r : ℕ} (Q : LevelCube 𝒮 M) (J : 𝒮.Tensor r) :
    Q.system.setting.Tensor r :=
  Q.system.pullTensor (indicator (Q.thicken (5 / 6)) fun _ => 1) J
def LevelCube.SiteFnNear (Q : LevelCube 𝒮 M) (f : 𝒮.FineSite → ℝ) : Prop :=
  ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∉ Q.thicken (5 / 6) → f x = 0
def LevelCube.BondFnNear (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ) : Prop :=
  ∀ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∉ Q.thicken (5 / 6) → A b = 0
def LevelCube.TensorFnNear {r : ℕ} (Q : LevelCube 𝒮 M) (J : 𝒮.Tensor r) : Prop :=
  ∀ ν, Q.BondFnNear (J ν)
structure LevelCube.CellProperties (Q : LevelCube 𝒮 M) : Prop where
  side : ∀ w ∈ Q.cellPoints,
    Q.cellSide w = 𝒮.scale Q.level ∨ Q.cellSide w = 𝒮.scale (Q.level + 1)
  forms_sum : ∀ v ∈ Q.system.forms,
    v = fun c => ∑ᶠ w ∈ Q.cellPoints, Q.restrictBondsToCell w v c
  forms_restrict : ∀ v ∈ Q.system.forms, ∀ w ∈ Q.cellPoints,
    Q.restrictBondsToCell w v ∈ Q.system.forms
  tensors_sum : ∀ J : Q.system.setting.Tensor 1,
    J = fun ν c => ∑ᶠ w ∈ Q.cellPoints, Q.restrictTensorToCell w J ν c
  cell_subset_strict : ∀ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    𝒮.cellOf y ⊆ Q.strictPts
  embed_mem_cellPoints : ∀ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    Q.system.embed y ∈ Q.cellPoints
  cellAt_embed : ∀ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    Q.cellAt (Q.system.embed y) = Q.system.embed '' 𝒮.cellOf y
  cellSide_embed : ∀ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    Q.cellSide (Q.system.embed y) = 𝒮.levelScale y
  anchoredIn_iff : ∀ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    ∀ b : 𝒮.FineBond,
    (Q.IsSecondType ∨ ((b.source : 𝒮.Point) ∈ Q.strictPts ∧ 𝒮.anchor b = b.source)) →
      (AnchoredIn (𝒮.cellOf y) b ↔
        AnchoredIn (Q.cellAt (Q.system.embed y)) (Q.system.mapBond b))
structure LevelCube.EmbeddingProperties (Q : LevelCube 𝒮 M) : Prop where
  bijOn_ball : ∀ s ∈ Q.thicken (5 / 6),
    BijOn Q.system.embed (Q.closedSupBall s) (Q.torusSupBall (Q.system.embed s))
  lOneNorm_eq : ∀ s ∈ Q.thicken (5 / 6), ∀ x ∈ Q.closedSupBall s, ∀ x' ∈ Q.closedSupBall s,
    lOneNorm (Q.system.embed x - Q.system.embed x') = lOneNorm (x - x')
  supNorm_eq : ∀ s ∈ Q.thicken (5 / 6), ∀ x ∈ Q.closedSupBall s, ∀ x' ∈ Q.closedSupBall s,
    supNorm (Q.system.embed x - Q.system.embed x') = supNorm (x - x')
  holderSite_eq : ∀ f : 𝒮.FineSite → ℝ, Q.SiteFnNear f → ∀ α lam : ℝ,
    lam ≤ 𝒮.scale (Q.level + 1) →
      holderSite α lam (Q.pullSiteFn f) = holderSite α lam f
  holderBond_eq : ∀ A : 𝒮.FineBond → ℝ, Q.BondFnNear A → ∀ α lam : ℝ,
    lam ≤ 𝒮.scale (Q.level + 1) →
      holderBond α lam (Q.localForm A) = holderBond α lam A
  holderTensor_eq : ∀ (r : ℕ) (J : 𝒮.Tensor r), Q.TensorFnNear J → ∀ α lam : ℝ,
    lam ≤ 𝒮.scale (Q.level + 1) →
      holderTensor α lam (Q.pullTensorNear J) = holderTensor α lam J
  vanishesOff_iff : ∀ f : 𝒮.FineSite → ℝ, Q.SiteFnNear f → ∀ o ∈ Q.thicken (5 / 6),
    ∀ lam : ℝ, lam ≤ 4 * 𝒮.scale (Q.level + 1) →
      (VanishesOff (cubeHalfSide o lam) f ↔
        VanishesOff (cubeHalfSide (Q.system.embed o) lam) (Q.pullSiteFn f))
  anchorSupported_iff : ∀ A : 𝒮.FineBond → ℝ, Q.BondFnNear A → ∀ o ∈ Q.thicken (5 / 6),
    ∀ lam : ℝ, lam ≤ 4 * 𝒮.scale (Q.level + 1) →
      (AnchorSupported (cubeHalfSide o lam) A ↔
        AnchorSupported (cubeHalfSide (Q.system.embed o) lam) (Q.localForm A))
  tensorAnchorSupported_iff : ∀ (r : ℕ) (J : 𝒮.Tensor r), Q.TensorFnNear J →
    ∀ o ∈ Q.thicken (5 / 6), ∀ lam : ℝ, lam ≤ 4 * 𝒮.scale (Q.level + 1) →
      (CubeTorus.TensorAnchorSupported (cubeHalfSide o lam) J ↔
        CubeTorus.TensorAnchorSupported (cubeHalfSide (Q.system.embed o) lam)
          (Q.pullTensorNear J))
  thickened_image : ∀ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    Q.thickened (Q.system.embed '' 𝒮.cellOf y) = Q.system.embed '' Q.nearSet (𝒮.cellOf y)
end PartitionCubes
end YangMills.Construction
