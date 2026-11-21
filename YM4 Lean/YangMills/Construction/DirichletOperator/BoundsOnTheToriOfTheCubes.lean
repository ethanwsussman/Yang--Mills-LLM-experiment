import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.LocalOperators
import YangMills.Construction.RegionSequence.FineLatticeNorms
import YangMills.Construction.RegionSequence.OperatorEstimates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
open DirichletGreen (fieldModulusAt)
open RegionSequence.OperatorEstimates (kernelOf avgGreenSqInv)
namespace CubeTorus
structure TorusConstants where
  δ : ℝ
  cornerδ : ℝ
  B : ℝ
  minBlock : ℝ
  Bα : ℝ → ℝ
  Bε : ℝ → ℝ
  Bαε : ℝ → ℝ → ℝ
instance : Inhabited TorusConstants := ⟨⟨0, 0, 0, 0, fun _ => 0, fun _ => 0, fun _ _ => 0⟩⟩
variable {𝒮 : NestedRegions} {M : ℕ}
abbrev torusSetting (Q : LevelCube 𝒮 M) : NestedRegions := Q.system.setting
def levelSpacing (Q : LevelCube 𝒮 M) : ℝ := 𝒮.scale Q.level
def corners (Q : LevelCube 𝒮 M) : Set (torusSetting Q).Point :=
  {w | ∃ o ∈ spacingLattice 4 (torusSetting Q).side (levelSpacing Q),
    IsCornerOf (torusSetting Q) o (levelSpacing Q) w}
def cornerBox (Q : LevelCube 𝒮 M) (w : (torusSetting Q).Point) : Set (torusSetting Q).Point :=
  cubeHalfSide w (levelSpacing Q)
def cornerBoxInterior (Q : LevelCube 𝒮 M) (w : (torusSetting Q).Point) :
    Set (torusSetting Q).Point :=
  {p | supNorm (p - w) < levelSpacing Q}
def tensorModulusAt {𝒯 : NestedRegions} {r : ℕ} (J : 𝒯.Tensor r) (x : 𝒯.FineBond) : ℝ :=
  ⨆ ν, |J ν x|
def TensorAnchorSupported {𝒯 : NestedRegions} {r : ℕ} (X : Set 𝒯.Point) (J : 𝒯.Tensor r) :
    Prop :=
  ∀ ν, AnchorSupported X (J ν)
def cutoffNorm (Q : LevelCube 𝒮 M) (α : ℝ) (ζ : (torusSetting Q).FineSite → ℝ) : ℝ :=
  holderSite α (levelSpacing Q) ζ + supSite ζ
namespace TorusConstants
variable (c : TorusConstants) (Q : LevelCube 𝒮 M)
def expDecay (w w' : (torusSetting Q).Point) : ℝ := Real.exp (-c.δ * Q.torusDist w w')
def cornerExpDecay (w w' : (torusSetting Q).Point) : ℝ :=
  Real.exp (-c.cornerδ * Q.torusDist w w')
structure GaugeGreenBounds (w w' : (torusSetting Q).Point) : Prop where
  value : ∀ f : (torusSetting Q).FineSite → ℝ, VanishesOff ((torusSetting Q).cellOf w') f →
    ∀ x : (torusSetting Q).FineSite, (x : (torusSetting Q).Point) ∈ (torusSetting Q).cellOf w →
      |gaugeGreenOp f x| ≤ c.B * levelSpacing Q ^ 2 * c.expDecay Q w w' * supSite f
  difference : ∀ f : (torusSetting Q).FineSite → ℝ, VanishesOff ((torusSetting Q).cellOf w') f →
    ∀ x : (torusSetting Q).FineSite, (x : (torusSetting Q).Point) ∈ (torusSetting Q).cellOf w →
      fieldModulusAt (grad (gaugeGreenOp f)) x ≤
        c.B * levelSpacing Q * c.expDecay Q w w' * supSite f
  source : ∀ F : BondField 4 (torusSetting Q).side (torusSetting Q).ξ,
    (∀ ν, VanishesOff ((torusSetting Q).cellOf w') (F ν)) →
    ∀ x : (torusSetting Q).FineSite, (x : (torusSetting Q).Point) ∈ (torusSetting Q).cellOf w →
      |gaugeGreenOp (latticeDiv F) x| ≤
        c.B * levelSpacing Q * c.expDecay Q w w' * fieldSupNorm F
structure CornerGreenBounds (w w' : (torusSetting Q).Point) : Prop where
  value : ∀ J : (torusSetting Q).FineBond → ℝ, AnchorSupported (cornerBox Q w') J →
    ∀ x, AnchoredIn (cornerBox Q w) x →
      |Q.system.inv J x| ≤ c.B * levelSpacing Q ^ 2 * c.cornerExpDecay Q w w' * supBond J
  difference : ∀ J : (torusSetting Q).FineBond → ℝ, AnchorSupported (cornerBox Q w') J →
    ∀ x, AnchoredIn (cornerBox Q w) x →
      tensorModulusAt (nablaOne (Q.system.inv J)) x ≤
        c.B * levelSpacing Q * c.cornerExpDecay Q w w' * supBond J
  source : ∀ J : (torusSetting Q).Tensor 1, TensorAnchorSupported (cornerBox Q w') J →
    ∀ x, AnchoredIn (cornerBox Q w) x →
      |Q.system.inv (divOne J) x| ≤
        c.B * levelSpacing Q * c.cornerExpDecay Q w w' * supTensor J
  laplacian : ∀ J : (torusSetting Q).FineBond → ℝ, AnchorSupported (cornerBox Q w') J →
    ∀ x, AnchoredIn (cornerBox Q w) x →
      |bondLap (Q.system.inv J) x| ≤ c.B * c.cornerExpDecay Q w w' * supBond J
  difference_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cornerBoxInterior Q w) ζ → ∀ J : (torusSetting Q).FineBond → ℝ,
    AnchorSupported (cornerBox Q w') J →
      holderTensor α (levelSpacing Q) (smulSiteTensor ζ (nablaOne (Q.system.inv J))) ≤
        c.Bα α * levelSpacing Q * c.cornerExpDecay Q w w' * cutoffNorm Q α ζ * supBond J
  source_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cornerBoxInterior Q w) ζ → ∀ J : (torusSetting Q).Tensor 1,
    TensorAnchorSupported (cornerBox Q w') J →
      holderBond α (levelSpacing Q) (smulSiteBond ζ (Q.system.inv (divOne J))) ≤
        c.Bα α * levelSpacing Q * c.cornerExpDecay Q w w' * cutoffNorm Q α ζ * supTensor J
  source_difference : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ J : (torusSetting Q).Tensor 1,
    TensorAnchorSupported (cornerBox Q w') J → ∀ x, AnchoredIn (cornerBox Q w) x →
      tensorModulusAt (nablaOne (Q.system.inv (divOne J))) x ≤
        c.Bε ε * c.cornerExpDecay Q w w' * (holderTensor ε (levelSpacing Q) J + supTensor J)
  source_difference_holder : ∀ α ε : ℝ, 0 ≤ α → α < 1 → 0 < ε → α + ε < 1 →
    ∀ ζ : (torusSetting Q).FineSite → ℝ, VanishesOff (cornerBoxInterior Q w) ζ →
    ∀ J : (torusSetting Q).Tensor 1, TensorAnchorSupported (cornerBox Q w') J →
      holderTensor α (levelSpacing Q)
          (smulSiteTensor ζ (nablaOne (Q.system.inv (divOne J)))) ≤
        c.Bαε α ε * c.cornerExpDecay Q w w' * cutoffNorm Q α ζ *
          (holderTensor (α + ε) (levelSpacing Q) J + supTensor J)
  value_two : ∀ ζ : (torusSetting Q).FineSite → ℝ, VanishesOff (cornerBoxInterior Q w) ζ →
    ∀ J : (torusSetting Q).FineBond → ℝ, AnchorSupported (cornerBox Q w') J →
      ltwoBond (smulSiteBond ζ (Q.system.inv J)) ≤
        c.B * levelSpacing Q ^ 2 * c.cornerExpDecay Q w w' * supSite ζ * ltwoBond J
  difference_two : ∀ ζ : (torusSetting Q).FineSite → ℝ, VanishesOff (cornerBoxInterior Q w) ζ →
    ∀ J : (torusSetting Q).FineBond → ℝ, AnchorSupported (cornerBox Q w') J →
      ltwoTensor (smulSiteTensor ζ (nablaOne (Q.system.inv J))) ≤
        c.B * levelSpacing Q * c.cornerExpDecay Q w w' * supSite ζ * ltwoBond J
  source_two : ∀ ζ : (torusSetting Q).FineSite → ℝ, VanishesOff (cornerBoxInterior Q w) ζ →
    ∀ J : (torusSetting Q).Tensor 1, TensorAnchorSupported (cornerBox Q w') J →
      ltwoBond (smulSiteBond ζ (Q.system.inv (divOne J))) ≤
        c.B * levelSpacing Q * c.cornerExpDecay Q w w' * supSite ζ * ltwoTensor J
  source_difference_two : ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cornerBoxInterior Q w) ζ → ∀ J : (torusSetting Q).Tensor 1,
    TensorAnchorSupported (cornerBox Q w') J →
      ltwoTensor (smulSiteTensor ζ (nablaOne (Q.system.inv (divOne J)))) ≤
        c.B * c.cornerExpDecay Q w w' * supSite ζ * ltwoTensor J
  second_difference_two : ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cornerBoxInterior Q w) ζ → ∀ J : (torusSetting Q).FineBond → ℝ,
    AnchorSupported (cornerBox Q w') J →
      ltwoTensor (smulSiteTensor ζ (nablaTwo (nablaOne (Q.system.inv J)))) ≤
        c.B * c.cornerExpDecay Q w w' * supSite ζ * ltwoBond J
  second_source_two : ∀ ζ : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cornerBoxInterior Q w) ζ → ∀ J : (torusSetting Q).Tensor 2,
    TensorAnchorSupported (cornerBox Q w') J →
      ltwoBond (smulSiteBond ζ (Q.system.inv (divTwo J))) ≤
        c.B * c.cornerExpDecay Q w w' * supSite ζ * ltwoTensor J
structure Holds : Prop where
  admissible : Q.IsAdmissible
  green : ∀ w ∈ (torusSetting Q).allCentres, ∀ w' ∈ (torusSetting Q).allCentres,
    c.GaugeGreenBounds Q w w'
  inverse : ∀ w w' : ↥(torusSetting Q).allCentres,
    |kernelOf (avgGreenSqInv (torusSetting Q)) w w'| ≤
      c.B * (levelSpacing Q ^ 4)⁻¹ * c.expDecay Q w w'
  longitudinal : ∀ w ∈ (torusSetting Q).allCentres, ∀ w' ∈ (torusSetting Q).allCentres,
    ∀ b b' : (torusSetting Q).FineBond,
      AnchoredIn ((torusSetting Q).cellOf w) b → AnchoredIn ((torusSetting Q).cellOf w') b' →
        |kernelOf Q.torusLongOp b b'| ≤
          c.B * ((torusSetting Q).ξ / (torusSetting Q).levelScale w') ^ 4 *
            (levelSpacing Q ^ 2)⁻¹ * c.expDecay Q w w'
  invertible : BijOn Q.system.op (Q.system.forms : Set ((torusSetting Q).FineBond → ℝ))
    Q.system.forms
  corner_bounds : ∀ w ∈ corners Q, ∀ w' ∈ corners Q, c.CornerGreenBounds Q w w'
structure Valid (L : ℕ) : Prop where
  δ_eq : c.δ = (OperatorEstimates.chosenConstants L).δ / (L : ℝ)
  minBlock_eq : c.minBlock = (OperatorEstimates.chosenConstants L).minBlock
  δ_pos : 0 < c.δ
  δ_le_one : c.δ ≤ 1
  cornerδ_pos : 0 < c.cornerδ
  cornerδ_le_one : c.cornerδ ≤ 1
  one_le_B : 1 ≤ c.B
  holds : ∀ (K m M R₁ : ℕ) (𝒮 : NestedRegions), 𝒮.L = L → 𝒮.IsLevelUnitChain K m M R₁ →
    max ((L : ℝ) ^ 5) ((L : ℝ) * c.minBlock) ≤ (M : ℝ) →
    ∀ Q : LevelCube 𝒮 M, Q.IsFirstType → c.Holds Q
end TorusConstants
def chosenConstants (L : ℕ) : TorusConstants :=
  Classical.epsilon fun c : TorusConstants => c.Valid L
end CubeTorus
end YangMills.Construction
