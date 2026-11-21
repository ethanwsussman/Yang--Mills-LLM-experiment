import YangMills.Construction.DirichletOperator.FactsOfTheCellsOfACube
import YangMills.Construction.PartitionCubes.CubeTorusTransfer
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
noncomputable section
namespace YangMills.Construction.CubeObservable
variable {S : NestedRegions} {M : ℕ}
structure IsLocalIsometry (Q : LevelCube S M) : Prop where
  bijOn_ball : ∀ s ∈ Q.thicken (5 / 6),
    BijOn Q.system.embed (Q.closedSupBall s) (Q.torusSupBall (Q.system.embed s))
  lOneNorm_sub : ∀ s ∈ Q.thicken (5 / 6), ∀ x ∈ Q.closedSupBall s, ∀ x' ∈ Q.closedSupBall s,
    Torus.lOneNorm (Q.system.embed x - Q.system.embed x') = Torus.lOneNorm (x - x')
  supNorm_sub : ∀ s ∈ Q.thicken (5 / 6), ∀ x ∈ Q.closedSupBall s, ∀ x' ∈ Q.closedSupBall s,
    Torus.supNorm (Q.system.embed x - Q.system.embed x') = Torus.supNorm (x - x')
  embed_add : ∀ s ∈ Q.thicken (5 / 6), ∀ v : Fin 4 → ℝ, ‖v‖ ≤ 4 * S.scale (Q.level + 1) →
    Q.system.embed (s + Torus.torusProj 4 S.side v) =
      Q.system.embed s + Torus.torusProj 4 Q.system.setting.side v
  mapSite_eq : ∀ s ∈ Q.thicken (5 / 6), ∀ x : S.FineSite, (x : S.Point) ∈ Q.closedSupBall s →
    (Q.system.mapSite x : Q.system.setting.Point) = Q.system.embed (x : S.Point)
  mapSite_surj : ∀ s ∈ Q.thicken (5 / 6), ∀ c : Q.system.setting.FineSite,
    (c : Q.system.setting.Point) ∈ Q.torusSupBall (Q.system.embed s) →
      ∃ x : S.FineSite, (x : S.Point) ∈ Q.closedSupBall s ∧ Q.system.mapSite x = c
  mapSite_add_step : ∀ s ∈ Q.thicken (5 / 6), ∀ (ν : Fin 4) (x : S.FineSite),
    Torus.supNorm ((x : S.Point) - s) ≤ 3 * S.scale (Q.level + 1) →
      Q.system.mapSite (x + unitStep 4 S.side S.ξ ν) =
        Q.system.mapSite x + unitStep 4 Q.system.setting.side Q.system.setting.ξ ν
  mapSite_sub_step : ∀ s ∈ Q.thicken (5 / 6), ∀ (ν : Fin 4) (x : S.FineSite),
    Torus.supNorm ((x : S.Point) - s) ≤ 3 * S.scale (Q.level + 1) →
      Q.system.mapSite (x - unitStep 4 S.side S.ξ ν) =
        Q.system.mapSite x - unitStep 4 Q.system.setting.side Q.system.setting.ξ ν
  mapBond_shiftUp : ∀ s ∈ Q.thicken (5 / 6), ∀ (ν : Fin 4) (b : S.FineBond),
    Torus.supNorm ((b.source : S.Point) - s) ≤ 3 * S.scale (Q.level + 1) →
      Q.system.mapBond (shiftUp ν b) = shiftUp ν (Q.system.mapBond b)
  mapBond_shiftDown : ∀ s ∈ Q.thicken (5 / 6), ∀ (ν : Fin 4) (b : S.FineBond),
    Torus.supNorm ((b.source : S.Point) - s) ≤ 3 * S.scale (Q.level + 1) →
      Q.system.mapBond (shiftDown ν b) = shiftDown ν (Q.system.mapBond b)
structure BondFnReads (Q : LevelCube S M) (A : S.FineBond → ℝ) (B : Q.system.setting.FineBond → ℝ) :
    Prop where
  near : Q.BondFnNear A
  eq_zero_off : ∀ c : Q.system.setting.FineBond,
    (c.source : Q.system.setting.Point) ∉ Q.system.embed '' Q.thicken (5 / 6) → B c = 0
  eq_on : ∀ b : S.FineBond, (b.source : S.Point) ∈ Q.thicken (5 / 6) →
    A b = B (Q.system.mapBond b)
def TensorReads {r : ℕ} (Q : LevelCube S M) (J : S.Tensor r) (J' : Q.system.setting.Tensor r) :
    Prop :=
  ∀ ν, BondFnReads Q (J ν) (J' ν)
structure NormsPreserved (Q : LevelCube S M) : Prop where
  supSite_eq : ∀ (f : S.FineSite → ℝ) (g : Q.system.setting.FineSite → ℝ),
    PartitionCubes.CubeTorus.SiteFunctionsMatch Q f g → supSite g = supSite f
  ltwoSite_eq : ∀ (f : S.FineSite → ℝ) (g : Q.system.setting.FineSite → ℝ),
    PartitionCubes.CubeTorus.SiteFunctionsMatch Q f g → ltwoSite g = ltwoSite f
  holderSite_eq : ∀ (f : S.FineSite → ℝ) (g : Q.system.setting.FineSite → ℝ),
    PartitionCubes.CubeTorus.SiteFunctionsMatch Q f g → ∀ α t : ℝ, 0 ≤ α → α < 1 → 0 < t →
      t ≤ S.scale (Q.level + 1) → holderSite α t g = holderSite α t f
  vanishesOff_iff : ∀ (f : S.FineSite → ℝ) (g : Q.system.setting.FineSite → ℝ),
    PartitionCubes.CubeTorus.SiteFunctionsMatch Q f g → ∀ o ∈ Q.thicken (5 / 6), ∀ t : ℝ,
      t ≤ 4 * S.scale (Q.level + 1) →
      (VanishesOff (cubeHalfSide o t) f ↔
        VanishesOff (cubeHalfSide (Q.system.embed o) t) g)
  supBond_eq : ∀ (A : S.FineBond → ℝ) (B : Q.system.setting.FineBond → ℝ),
    BondFnReads Q A B → supBond B = supBond A
  ltwoBond_eq : ∀ (A : S.FineBond → ℝ) (B : Q.system.setting.FineBond → ℝ),
    BondFnReads Q A B → ltwoBond B = ltwoBond A
  holderBond_eq : ∀ (A : S.FineBond → ℝ) (B : Q.system.setting.FineBond → ℝ),
    BondFnReads Q A B → ∀ α t : ℝ, 0 ≤ α → α < 1 → 0 < t →
      t ≤ S.scale (Q.level + 1) → holderBond α t B = holderBond α t A
  anchorSupported_iff : ∀ (A : S.FineBond → ℝ) (B : Q.system.setting.FineBond → ℝ),
    BondFnReads Q A B → ∀ o ∈ Q.thicken (5 / 6), ∀ t : ℝ,
      t ≤ 4 * S.scale (Q.level + 1) →
      (AnchorSupported (cubeHalfSide o t) A ↔
        AnchorSupported (cubeHalfSide (Q.system.embed o) t) B)
  supTensor_eq : ∀ (r : ℕ) (J : S.Tensor r) (J' : Q.system.setting.Tensor r),
    TensorReads Q J J' → supTensor J' = supTensor J
  ltwoTensor_eq : ∀ (r : ℕ) (J : S.Tensor r) (J' : Q.system.setting.Tensor r),
    TensorReads Q J J' → ltwoTensor J' = ltwoTensor J
  holderTensor_eq : ∀ (r : ℕ) (J : S.Tensor r) (J' : Q.system.setting.Tensor r),
    TensorReads Q J J' → ∀ α t : ℝ, 0 ≤ α → α < 1 → 0 < t →
      t ≤ S.scale (Q.level + 1) → holderTensor α t J' = holderTensor α t J
  tensorAnchorSupported_iff : ∀ (r : ℕ) (J : S.Tensor r) (J' : Q.system.setting.Tensor r),
    TensorReads Q J J' → ∀ o ∈ Q.thicken (5 / 6), ∀ t : ℝ,
      t ≤ 4 * S.scale (Q.level + 1) →
      (YangMills.Construction.CubeTorus.TensorAnchorSupported (cubeHalfSide o t) J ↔
        YangMills.Construction.CubeTorus.TensorAnchorSupported
          (cubeHalfSide (Q.system.embed o) t) J')
end YangMills.Construction.CubeObservable
