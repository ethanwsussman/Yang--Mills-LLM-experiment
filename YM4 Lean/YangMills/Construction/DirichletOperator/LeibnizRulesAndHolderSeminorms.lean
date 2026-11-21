import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.LocalOperators
import YangMills.Construction.RegionSequence.FineLatticeNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace LeibnizHolder
variable {𝒮 : NestedRegions}
def bondTranslateUp (ν : Fin 4) (f : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => f (shiftUp ν b)
def bondTranslateDown (ν : Fin 4) (f : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => f (shiftDown ν b)
def siteCommutator (φ f : 𝒮.FineSite → ℝ) : 𝒮.FineSite → ℝ :=
  φ * latticeLaplacian f - latticeLaplacian (φ * f)
def bondCommutator (φ : 𝒮.FineSite → ℝ) (f : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  smulSiteBond φ (bondLap f) - bondLap (smulSiteBond φ f)
structure SiteProductRules (φ f : 𝒮.FineSite → ℝ) : Prop where
  fwdDiff_mul : ∀ ν, forwardDiff ν (φ * f) =
    translateForward ν φ * forwardDiff ν f + forwardDiff ν φ * f
  mul_bwdDiff : ∀ ν, φ * backwardDiff ν f =
    backwardDiff ν (φ * f) + translateBackward ν (forwardDiff ν φ) * translateBackward ν f
  commutator_eq_sum : siteCommutator φ f =
    (∑ ν, (forwardDiff ν φ * forwardDiff ν f + backwardDiff ν φ * backwardDiff ν f)) -
      latticeLaplacian φ * f
  commutator_eq_div : siteCommutator φ f =
    -(∑ ν, backwardDiff ν (forwardDiff ν φ * (f + translateForward ν f))) +
      latticeLaplacian φ * f
  commutator_antisymm : ∀ g, innerSum (siteCommutator φ f) g = -innerSum f (siteCommutator φ g)
structure BondProductRules (φ : 𝒮.FineSite → ℝ) (f : 𝒮.FineBond → ℝ) : Prop where
  fwdDiff_mul : ∀ ν, fwdDiff ν (smulSiteBond φ f) =
    smulSiteBond (translateForward ν φ) (fwdDiff ν f) + smulSiteBond (forwardDiff ν φ) f
  mul_bwdDiff : ∀ ν, smulSiteBond φ (bwdDiff ν f) =
    bwdDiff ν (smulSiteBond φ f) +
      smulSiteBond (translateBackward ν (forwardDiff ν φ)) (bondTranslateDown ν f)
  commutator_eq_sum : bondCommutator φ f =
    (∑ ν, (smulSiteBond (forwardDiff ν φ) (fwdDiff ν f) +
      smulSiteBond (backwardDiff ν φ) (bwdDiff ν f))) - smulSiteBond (latticeLaplacian φ) f
  commutator_eq_div : bondCommutator φ f =
    -(∑ ν, bwdDiff ν (smulSiteBond (forwardDiff ν φ) (f + bondTranslateUp ν f))) +
      smulSiteBond (latticeLaplacian φ) f
  commutator_antisymm : ∀ g, bondInner (bondCommutator φ f) g = -bondInner f (bondCommutator φ g)
def supThickening (X : Set 𝒮.Point) (lam : ℝ) : Set 𝒮.Point :=
  {x | supSetDist {x} X ≤ ENNReal.ofReal lam}
def supBondOn (X : Set 𝒮.Point) (f : 𝒮.FineBond → ℝ) : ℝ :=
  sSup {r | ∃ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ X ∧ r = |f b|}
def supTensorOn {r : ℕ} (X : Set 𝒮.Point) (J : 𝒮.Tensor r) : ℝ := ⨆ ν, supBondOn X (J ν)
def holderSiteOn (α lam : ℝ) (X : Set 𝒮.Point) (f : 𝒮.FineSite → ℝ) : ℝ :=
  sSup {r | ∃ x x' : 𝒮.FineSite, (x : 𝒮.Point) ∈ X ∧ (x' : 𝒮.Point) ∈ X ∧
    0 < siteLOneDist x x' ∧ siteLOneDist x x' ≤ lam ∧
    r = (lam / siteLOneDist x x') ^ α * ‖f x' - f x‖}
def holderBondOn (α lam : ℝ) (X : Set 𝒮.Point) (f : 𝒮.FineBond → ℝ) : ℝ :=
  sSup {r | ∃ b b' : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ X ∧ (b'.source : 𝒮.Point) ∈ X ∧
    b.dir = b'.dir ∧
    0 < siteLOneDist b.source b'.source ∧ siteLOneDist b.source b'.source ≤ lam ∧
    r = (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖}
def holderTensorOn {r : ℕ} (α lam : ℝ) (X : Set 𝒮.Point) (J : 𝒮.Tensor r) : ℝ :=
  ⨆ ν, holderBondOn α lam X (J ν)
def IsTorusOrSmallCube (lam : ℝ) (X : Set 𝒮.Point) : Prop :=
  X = univ ∨ ∃ (c : 𝒮.Point) (σ : ℝ), 0 < σ ∧ σ + lam < 𝒮.side ∧ X = cubeAt c σ
structure SiteHolderBounds (α lam lam' : ℝ) (f : 𝒮.FineSite → ℝ) : Prop where
  mul_le : ∀ (φ : 𝒮.FineSite → ℝ) (X : Set 𝒮.Point), (∀ x, φ x ≠ 0 → (x : 𝒮.Point) ∈ X) →
    holderSite α lam (φ * f) ≤
      supNormOn (supThickening X lam) f * holderSite α lam φ +
        supSite φ * holderSiteOn α lam (supThickening X lam) f
  le_fwdDiff : ∀ X : Set 𝒮.Point, IsTorusOrSmallCube lam X →
    holderSiteOn α lam X f ≤ lam * ⨆ ν, supNormOn X (forwardDiff ν f)
  mono_scale : holderSite α lam' f ≤ holderSite α lam f
  le_rescale : holderSite α lam f ≤
    (lam / lam') ^ α * max (holderSite α lam' f) (2 * supSite f)
structure BondHolderBounds (α lam lam' : ℝ) (f : 𝒮.FineBond → ℝ) : Prop where
  mul_le : ∀ (φ : 𝒮.FineSite → ℝ) (X : Set 𝒮.Point), (∀ x, φ x ≠ 0 → (x : 𝒮.Point) ∈ X) →
    holderBond α lam (smulSiteBond φ f) ≤
      supBondOn (supThickening X lam) f * holderSite α lam φ +
        supSite φ * holderBondOn α lam (supThickening X lam) f
  le_fwdDiff : ∀ X : Set 𝒮.Point, IsTorusOrSmallCube lam X →
    holderBondOn α lam X f ≤ lam * ⨆ ν, supBondOn X (fwdDiff ν f)
  mono_scale : holderBond α lam' f ≤ holderBond α lam f
  le_rescale : holderBond α lam f ≤
    (lam / lam') ^ α * max (holderBond α lam' f) (2 * supBond f)
structure TensorHolderBounds {r : ℕ} (α lam lam' : ℝ) (J : 𝒮.Tensor r) : Prop where
  mul_le : ∀ (φ : 𝒮.FineSite → ℝ) (X : Set 𝒮.Point), (∀ x, φ x ≠ 0 → (x : 𝒮.Point) ∈ X) →
    holderTensor α lam (smulSiteTensor φ J) ≤
      supTensorOn (supThickening X lam) J * holderSite α lam φ +
        supSite φ * holderTensorOn α lam (supThickening X lam) J
  le_fwdDiff : ∀ X : Set 𝒮.Point, IsTorusOrSmallCube lam X →
    holderTensorOn α lam X J ≤ lam * ⨆ ρ, supTensorOn X fun ν => fwdDiff ρ (J ν)
  mono_scale : holderTensor α lam' J ≤ holderTensor α lam J
  le_rescale : holderTensor α lam J ≤
    (lam / lam') ^ α * max (holderTensor α lam' J) (2 * supTensor J)
def productRemainder (φ : 𝒮.FineSite → ℝ) (J : 𝒮.Tensor 1) : 𝒮.FineBond → ℝ :=
  ∑ ν, smulSiteBond (translateBackward ν (forwardDiff ν φ)) (bondTranslateDown ν (J (constIdx ν)))
def transferBonds (𝔏 : CubeSystem 𝒮) (g : 𝒮.FineBond → ℝ) :
    𝔏.setting.FineBond → ℝ :=
  fun c => ∑ᶠ b ∈ {b : 𝒮.FineBond | 𝔏.mapBond b = c}, g b
def localDiv (𝔏 : CubeSystem 𝒮) (w : 𝔏.setting.Tensor 1) :
    𝔏.setting.FineBond → ℝ :=
  adjointValue (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) bondInner tensorInner nablaOne w
variable {M : ℕ}
open Classical in
def transferredRemainder (Q : LevelCube 𝒮 M) (J : 𝒮.Tensor 1) :
    Q.system.setting.FineBond → ℝ :=
  transferBonds Q.system
    (if Q.IsSecondType then projBonds (productRemainder (fun x => Q.partitionFn x) J)
    else productRemainder (fun x => Q.partitionFn x) J)
def CubeProductRule (Q : LevelCube 𝒮 M) (J : 𝒮.Tensor 1) : Prop :=
  Q.system.pullBonds Q.partitionFn (divOne J) =
    localDiv Q.system (Q.system.pullTensor Q.partitionFn J) + transferredRemainder Q J
def Statement : Prop :=
  (∀ (𝒮 : NestedRegions) (φ f : 𝒮.FineSite → ℝ), SiteProductRules φ f) ∧
  (∀ (𝒮 : NestedRegions) (φ : 𝒮.FineSite → ℝ) (f : 𝒮.FineBond → ℝ), BondProductRules φ f) ∧
  (∀ (𝒮 : NestedRegions) (α lam lam' : ℝ), 0 ≤ α → α < 1 → 0 < lam' → lam' ≤ lam →
    (∀ f : 𝒮.FineSite → ℝ, SiteHolderBounds α lam lam' f) ∧
    (∀ f : 𝒮.FineBond → ℝ, BondHolderBounds α lam lam' f) ∧
    ∀ (r : ℕ) (J : 𝒮.Tensor r), TensorHolderBounds α lam lam' J) ∧
  ∀ (K m M R₁ : ℕ) (𝒮 : NestedRegions), 𝒮.IsLevelUnitChain K m M R₁ → 𝒮.L ^ 5 ≤ M →
    ∀ Q ∈ active 𝒮 M, ∀ J : 𝒮.Tensor 1, CubeProductRule Q J
end LeibnizHolder
end YangMills.Construction
