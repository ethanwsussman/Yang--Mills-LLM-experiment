import YangMills.Construction.DirichletOperator.BoundsOnTheToriOfTheCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet RegionSequence RegionSequence.NestedRegions PartitionCubes
open CubeTorus (torusSetting levelSpacing tensorModulusAt TensorAnchorSupported)
namespace CubeOperators
structure RegularityConstants where
  δ : ℝ
  B : ℝ
  Bα : ℝ → ℝ
  Bε : ℝ → ℝ
  Bαε : ℝ → ℝ → ℝ
instance : Inhabited RegularityConstants := ⟨⟨0, 0, fun _ => 0, fun _ => 0, fun _ _ => 0⟩⟩
variable {𝒮 : NestedRegions} {M : ℕ}
open Classical in
def cubeDivOne (Q : LevelCube 𝒮 M) (J : (torusSetting Q).Tensor 1) :
    (torusSetting Q).FineBond → ℝ :=
  if Q.IsSecondType then
    adjointValue (Q.system.forms : Set ((torusSetting Q).FineBond → ℝ)) bondInner tensorInner
      nablaOne J
  else divOne J
open Classical in
def cubeDivTwo (Q : LevelCube 𝒮 M) (J : (torusSetting Q).Tensor 2) :
    (torusSetting Q).FineBond → ℝ :=
  if Q.IsSecondType then
    adjointValue (Q.system.forms : Set ((torusSetting Q).FineBond → ℝ)) bondInner tensorInner
      (fun A => nablaTwo (nablaOne A)) J
  else divTwo J
def IsCubeScale (Q : LevelCube 𝒮 M) (s : ℝ) : Prop :=
  s = levelSpacing Q ∨ s = 𝒮.scale (Q.level + 1)
def cutoffSize {𝒯 : NestedRegions} (α s : ℝ) (ζ : 𝒯.FineSite → ℝ) : ℝ :=
  holderSite α s ζ + supSite ζ
def sourceSize {𝒯 : NestedRegions} {r : ℕ} (ε s : ℝ) (J : 𝒯.Tensor r) : ℝ :=
  holderTensor ε s J + supTensor J
namespace RegularityConstants
variable (c : RegularityConstants) (Q : LevelCube 𝒮 M)
def expDecay (o o' : (torusSetting Q).Point) : ℝ := Real.exp (-c.δ * Q.torusDist o o')
structure KernelBounds (o o' : (torusSetting Q).Point) (s₁ s₂ : ℝ) : Prop where
  value : ∀ J ∈ Q.system.forms, AnchorSupported (cubeHalfSide o' s₂) J →
    ∀ x, AnchoredIn (cubeHalfSide o s₁) x →
      |Q.system.inv J x| ≤ c.B * levelSpacing Q ^ 2 * c.expDecay Q o o' * supBond J
  difference : ∀ J ∈ Q.system.forms, AnchorSupported (cubeHalfSide o' s₂) J →
    ∀ x, AnchoredIn (cubeHalfSide o s₁) x →
      tensorModulusAt (nablaOne (Q.system.inv J)) x ≤
        c.B * levelSpacing Q * c.expDecay Q o o' * supBond J
  source : ∀ J : (torusSetting Q).Tensor 1, TensorAnchorSupported (cubeHalfSide o' s₂) J →
    ∀ x, AnchoredIn (cubeHalfSide o s₁) x →
      |Q.system.inv (cubeDivOne Q J) x| ≤
        c.B * levelSpacing Q * c.expDecay Q o o' * supTensor J
  laplacian : ∀ J ∈ Q.system.forms, AnchorSupported (cubeHalfSide o' s₂) J →
    ∀ x, AnchoredIn (cubeHalfSide o s₁) x →
      |bondLap (Q.system.inv J) x| ≤ c.B * c.expDecay Q o o' * supBond J
  value_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o s₁) ζ → ∀ J ∈ Q.system.forms,
    AnchorSupported (cubeHalfSide o' s₂) J →
      (levelSpacing Q)⁻¹ * holderBond α s₁ (smulSiteBond ζ (Q.system.inv J)) ≤
        c.Bα α * levelSpacing Q * cutoffSize α s₁ ζ * c.expDecay Q o o' * supBond J
  difference_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o s₁) ζ → ∀ J ∈ Q.system.forms,
    AnchorSupported (cubeHalfSide o' s₂) J →
      holderTensor α s₁ (smulSiteTensor ζ (nablaOne (Q.system.inv J))) ≤
        c.Bα α * levelSpacing Q * cutoffSize α s₁ ζ * c.expDecay Q o o' * supBond J
  source_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o s₁) ζ → ∀ J : (torusSetting Q).Tensor 1,
    TensorAnchorSupported (cubeHalfSide o' s₂) J →
      holderBond α s₁ (smulSiteBond ζ (Q.system.inv (cubeDivOne Q J))) ≤
        c.Bα α * levelSpacing Q * cutoffSize α s₁ ζ * c.expDecay Q o o' * supTensor J
  source_difference : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ J : (torusSetting Q).Tensor 1,
    TensorAnchorSupported (cubeHalfSide o' s₂) J → ∀ x, AnchoredIn (cubeHalfSide o s₁) x →
      tensorModulusAt (nablaOne (Q.system.inv (cubeDivOne Q J))) x ≤
        c.Bε ε * c.expDecay Q o o' * sourceSize ε s₂ J
  source_difference_holder : ∀ α ε : ℝ, 0 ≤ α → α < 1 → 0 < ε → α + ε < 1 →
    ∀ ζ : (torusSetting Q).FineSite → ℝ, VanishesOff (cubeHalfSide o s₁) ζ →
    ∀ J : (torusSetting Q).Tensor 1, TensorAnchorSupported (cubeHalfSide o' s₂) J →
      holderTensor α s₁
          (smulSiteTensor ζ (nablaOne (Q.system.inv (cubeDivOne Q J)))) ≤
        c.Bαε α ε * cutoffSize α s₁ ζ * c.expDecay Q o o' * sourceSize (α + ε) s₂ J
  value_two : ∀ ζ : (torusSetting Q).FineSite → ℝ, VanishesOff (cubeHalfSide o s₁) ζ →
    ∀ J ∈ Q.system.forms, AnchorSupported (cubeHalfSide o' s₂) J →
      ltwoBond (smulSiteBond ζ (Q.system.inv J)) ≤
        c.B * levelSpacing Q ^ 2 * supSite ζ * c.expDecay Q o o' * ltwoBond J
  difference_two : ∀ ζ : (torusSetting Q).FineSite → ℝ, VanishesOff (cubeHalfSide o s₁) ζ →
    ∀ J ∈ Q.system.forms, AnchorSupported (cubeHalfSide o' s₂) J →
      ltwoTensor (smulSiteTensor ζ (nablaOne (Q.system.inv J))) ≤
        c.B * levelSpacing Q * supSite ζ * c.expDecay Q o o' * ltwoBond J
  source_two : ∀ ζ : (torusSetting Q).FineSite → ℝ, VanishesOff (cubeHalfSide o s₁) ζ →
    ∀ J : (torusSetting Q).Tensor 1, TensorAnchorSupported (cubeHalfSide o' s₂) J →
      ltwoBond (smulSiteBond ζ (Q.system.inv (cubeDivOne Q J))) ≤
        c.B * levelSpacing Q * supSite ζ * c.expDecay Q o o' * ltwoTensor J
  source_difference_two : ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o s₁) ζ → ∀ J : (torusSetting Q).Tensor 1,
    TensorAnchorSupported (cubeHalfSide o' s₂) J →
      ltwoTensor (smulSiteTensor ζ (nablaOne (Q.system.inv (cubeDivOne Q J)))) ≤
        c.B * supSite ζ * c.expDecay Q o o' * ltwoTensor J
  second_difference_two : ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o s₁) ζ → ∀ J ∈ Q.system.forms,
    AnchorSupported (cubeHalfSide o' s₂) J →
      ltwoTensor (smulSiteTensor ζ (nablaTwo (nablaOne (Q.system.inv J)))) ≤
        c.B * supSite ζ * c.expDecay Q o o' * ltwoBond J
  second_source_two : ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o s₁) ζ → ∀ J : (torusSetting Q).Tensor 2,
    TensorAnchorSupported (cubeHalfSide o' s₂) J →
      ltwoBond (smulSiteBond ζ (Q.system.inv (cubeDivTwo Q J))) ≤
        c.B * supSite ζ * c.expDecay Q o o' * ltwoTensor J
structure CubeHolds : Prop where
  invertible : BijOn Q.system.op (Q.system.forms : Set ((torusSetting Q).FineBond → ℝ))
    Q.system.forms
  symmetric : ∀ u ∈ Q.system.forms, ∀ v ∈ Q.system.forms,
    bondInner (Q.system.inv u) v = bondInner u (Q.system.inv v)
  bounds : ∀ s₁ s₂ : ℝ, IsCubeScale Q s₁ → IsCubeScale Q s₂ →
    ∀ o o' : (torusSetting Q).Point, c.KernelBounds Q o o' s₁ s₂
structure Valid (L : ℕ) : Prop where
  δ_pos : 0 < c.δ
  δ_le_one : c.δ ≤ 1
  one_le_B : 1 ≤ c.B
  holds : ∀ (K m M R₁ : ℕ) (𝒮 : NestedRegions), 𝒮.L = L → 𝒮.IsLevelUnitChain K m M R₁ →
    max ((L : ℝ) ^ 5) ((L : ℝ) * (CubeTorus.chosenConstants L).minBlock) ≤ (M : ℝ) →
    ∀ Q : LevelCube 𝒮 M, Q ∈ active 𝒮 M → c.CubeHolds Q
end RegularityConstants
def chosenConstants (L : ℕ) : RegularityConstants :=
  Classical.epsilon fun c : RegularityConstants => c.Valid L
def RegularityClaim : Prop := ∀ L : ℕ, Odd L → 13 ≤ L → (chosenConstants L).Valid L
end CubeOperators
end YangMills.Construction
