import YangMills.Construction.Torus.SeparatedChains
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction
namespace Dirichlet
variable {d : ℕ} {S ξ : ℝ}
abbrev LatticeSite (d : ℕ) (S ξ : ℝ) : Type := ↥(spacingLattice d S ξ)
def unitStep (d : ℕ) (S ξ : ℝ) (μ : Fin d) : LatticeSite d S ξ :=
  ⟨torusProj d S (Pi.single μ ξ), ⟨Pi.single μ 1, by
    funext ν
    by_cases h : ν = μ
    · subst h; simp [torusProj]
    · simp [torusProj, Pi.single_eq_of_ne h]⟩⟩
def IsNeighbor (x y : LatticeSite d S ξ) : Prop :=
  ∃ μ, y = x + unitStep d S ξ μ ∨ y = x - unitStep d S ξ μ
def restrictTo (X : Set (PeriodicTorus d S)) (f : LatticeSite d S ξ → ℝ) : LatticeSite d S ξ → ℝ :=
  indicator {x | (x : PeriodicTorus d S) ∈ X} f
def VanishesOff (X : Set (PeriodicTorus d S)) (f : LatticeSite d S ξ → ℝ) : Prop :=
  ∀ x : LatticeSite d S ξ, (x : PeriodicTorus d S) ∉ X → f x = 0
abbrev BondField (d : ℕ) (S ξ : ℝ) : Type := Fin d → LatticeSite d S ξ → ℝ
def translateForward (μ : Fin d) (f : LatticeSite d S ξ → ℝ) : LatticeSite d S ξ → ℝ :=
  fun x => f (x + unitStep d S ξ μ)
def translateBackward (μ : Fin d) (f : LatticeSite d S ξ → ℝ) : LatticeSite d S ξ → ℝ :=
  fun x => f (x - unitStep d S ξ μ)
def forwardDiff (μ : Fin d) (f : LatticeSite d S ξ → ℝ) : LatticeSite d S ξ → ℝ :=
  fun x => ξ⁻¹ * (f (x + unitStep d S ξ μ) - f x)
def backwardDiff (μ : Fin d) (f : LatticeSite d S ξ → ℝ) : LatticeSite d S ξ → ℝ :=
  fun x => ξ⁻¹ * (f (x - unitStep d S ξ μ) - f x)
def grad (f : LatticeSite d S ξ → ℝ) : BondField d S ξ := fun μ => forwardDiff μ f
def latticeDiv (F : BondField d S ξ) : LatticeSite d S ξ → ℝ :=
  fun x => ∑ μ, backwardDiff μ (F μ) x
def latticeLaplacian (f : LatticeSite d S ξ → ℝ) : LatticeSite d S ξ → ℝ := latticeDiv (grad f)
def innerSum (f g : LatticeSite d S ξ → ℝ) : ℝ := ξ ^ d * ∑ᶠ x, f x * g x
def fieldInnerSum (F G : BondField d S ξ) : ℝ := ∑ μ, innerSum (F μ) (G μ)
def siteNorm (f : LatticeSite d S ξ → ℝ) : ℝ := √(innerSum f f)
def fieldSiteNorm (F : BondField d S ξ) : ℝ := √(fieldInnerSum F F)
def siteNormOn (X : Set (PeriodicTorus d S)) (f : LatticeSite d S ξ → ℝ) : ℝ :=
  siteNorm (restrictTo X f)
def supNormOn (X : Set (PeriodicTorus d S)) (f : LatticeSite d S ξ → ℝ) : ℝ :=
  sSup {r | ∃ x : LatticeSite d S ξ, (x : PeriodicTorus d S) ∈ X ∧ r = |f x|}
def supNormAll (f : LatticeSite d S ξ → ℝ) : ℝ := supNormOn univ f
def fieldSupNorm (F : BondField d S ξ) : ℝ := ⨆ μ, supNormAll (F μ)
def blockWeights (L : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | n + 2 => blockWeights L (n + 1) / (((L : ℝ) ^ 2)⁻¹ + blockWeights L (n + 1))
structure BlockSetting (d L : ℕ) (aLow aHigh S : ℝ) where
  ξ : ℝ
  M : ℕ
  R₁ : ℕ
  t : ℕ
  Ω : ℕ → Set (PeriodicTorus d S)
  a : ℕ → ℝ
  isSeparatedChain : IsSeparatedChain L ξ M R₁ t Ω
  weight_mem : ∀ n ≤ t, aLow ≤ a n ∧ a n ≤ aHigh
namespace BlockSetting
variable {L : ℕ} {aLow aHigh : ℝ} (𝒮 : BlockSetting d L aLow aHigh S)
def scaleAt (n : ℤ) : ℝ := scaleSpacing L 𝒮.ξ n
def domainAt (n : ℤ) : Set (PeriodicTorus d S) := if n < 0 then univ else 𝒮.Ω n.toNat
def centres : Set (PeriodicTorus d S) := unionShellSites L 𝒮.ξ 𝒮.t 𝒮.Ω
def centreIndex (y : PeriodicTorus d S) : ℕ := shellIndex L 𝒮.ξ 𝒮.Ω y
def centreSpacing (y : PeriodicTorus d S) : ℝ := shellSpacing L 𝒮.ξ 𝒮.Ω y
def cell (y : PeriodicTorus d S) : Set (PeriodicTorus d S) := siteCube L 𝒮.ξ 𝒮.Ω y
def blockDist (p q : PeriodicTorus d S) : ℝ := chainWeightedDist L 𝒮.ξ 𝒮.t 𝒮.Ω p q
def centreOf (x : PeriodicTorus d S) : PeriodicTorus d S :=
  Classical.epsilon fun y => y ∈ 𝒮.centres ∧ x ∈ 𝒮.cell y
open Classical in
def localScale (x : LatticeSite d S 𝒮.ξ) : ℝ :=
  if (x : PeriodicTorus d S) ∈ 𝒮.Ω 0 then 𝒮.centreSpacing (𝒮.centreOf x) else 𝒮.ξ
def localWeight (x : LatticeSite d S 𝒮.ξ) : ℝ := (𝒮.localScale x ^ 2)⁻¹
def cellAverage (f : LatticeSite d S 𝒮.ξ → ℝ) (y : PeriodicTorus d S) : ℝ :=
  (𝒮.ξ / 𝒮.centreSpacing y) ^ d *
    ∑ᶠ x ∈ {x : LatticeSite d S 𝒮.ξ | (x : PeriodicTorus d S) ∈ 𝒮.cell y}, f x
def averagingOp (f : LatticeSite d S 𝒮.ξ → ℝ) : LatticeSite d S 𝒮.ξ → ℝ :=
  restrictTo (𝒮.Ω 0) fun x =>
    𝒮.a (𝒮.centreIndex (𝒮.centreOf x)) * (𝒮.centreSpacing (𝒮.centreOf x) ^ 2)⁻¹ *
      𝒮.cellAverage f (𝒮.centreOf x)
def IsCellUnion (W : Set (PeriodicTorus d S)) : Prop :=
  ∃ Y ⊆ 𝒮.centres, W = ⋃ y ∈ Y, 𝒮.cell y
end BlockSetting
structure LatticeBond (d : ℕ) (S ξ : ℝ) where
  source : LatticeSite d S ξ
  dir : Fin d
def LatticeBond.target (b : LatticeBond d S ξ) : LatticeSite d S ξ :=
  b.source + unitStep d S ξ b.dir
def IsBoundaryBond (W : Set (PeriodicTorus d S)) (b : LatticeBond d S ξ) : Prop :=
  Xor ((b.source : PeriodicTorus d S) ∈ W) ((b.target : PeriodicTorus d S) ∈ W)
open Classical in
def innerEnd (W : Set (PeriodicTorus d S)) (b : LatticeBond d S ξ) : LatticeSite d S ξ :=
  if (b.source : PeriodicTorus d S) ∈ W then b.source else b.target
open Classical in
def outerEnd (W : Set (PeriodicTorus d S)) (b : LatticeBond d S ξ) : LatticeSite d S ξ :=
  if (b.source : PeriodicTorus d S) ∈ W then b.target else b.source
def boundaryBonds (W : Set (PeriodicTorus d S)) : Set (LatticeBond d S ξ) :=
  {b | IsBoundaryBond W b}
def externalBoundaryBonds (Ω₀ W : Set (PeriodicTorus d S)) : Set (LatticeBond d S ξ) :=
  {b | IsBoundaryBond W b ∧ (outerEnd W b : PeriodicTorus d S) ∉ Ω₀}
def IsBoundaryRule (Ω₀ W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S ξ)) : Prop :=
  externalBoundaryBonds Ω₀ W ⊆ E ∧ E ⊆ boundaryBonds W
def dirichletForm (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S ξ))
    (f : LatticeSite d S ξ → ℝ) : ℝ :=
  ξ ^ ((d : ℤ) - 2) *
      ∑ᶠ b ∈ {b : LatticeBond d S ξ |
          (b.source : PeriodicTorus d S) ∈ W ∧ (b.target : PeriodicTorus d S) ∈ W},
        |f b.target - f b.source| ^ 2 +
    ξ ^ ((d : ℤ) - 2) * ∑ᶠ b ∈ E, |f (innerEnd W b)| ^ 2
def boundaryCount (E : Set (LatticeBond d S ξ)) (x : LatticeSite d S ξ) : ℕ :=
  Set.ncard {b ∈ E | b.source = x ∨ b.target = x}
def dirichletLaplacian (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S ξ))
    (f : LatticeSite d S ξ → ℝ) : LatticeSite d S ξ → ℝ :=
  restrictTo W fun x =>
    (ξ ^ 2)⁻¹ *
      ((∑ᶠ y ∈ {y : LatticeSite d S ξ | IsNeighbor x y ∧ (y : PeriodicTorus d S) ∈ W},
          (f x - f y)) +
        (boundaryCount E x : ℝ) * f x)
namespace BlockSetting
variable {L : ℕ} {aLow aHigh : ℝ} (𝒮 : BlockSetting d L aLow aHigh S)
def blockOperator (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S 𝒮.ξ))
    (f : LatticeSite d S 𝒮.ξ → ℝ) : LatticeSite d S 𝒮.ξ → ℝ :=
  dirichletLaplacian W E f + restrictTo W (𝒮.averagingOp (restrictTo W f))
def blockGreen (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S 𝒮.ξ))
    (f : LatticeSite d S 𝒮.ξ → ℝ) : LatticeSite d S 𝒮.ξ → ℝ :=
  Classical.epsilon fun g => VanishesOff W g ∧ 𝒮.blockOperator W E g = restrictTo W f
def fullOperator : (LatticeSite d S 𝒮.ξ → ℝ) → LatticeSite d S 𝒮.ξ → ℝ :=
  𝒮.blockOperator (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0))
def fullGreen : (LatticeSite d S 𝒮.ξ → ℝ) → LatticeSite d S 𝒮.ξ → ℝ :=
  𝒮.blockGreen (𝒮.Ω 0) (boundaryBonds (𝒮.Ω 0))
def collar (y : PeriodicTorus d S) : Set (PeriodicTorus d S) :=
  {z | supNorm (z - y) ≤ ((L : ℝ) + 9) * 𝒮.centreSpacing y}
def IsInteriorCentre (W : Set (PeriodicTorus d S)) (y : PeriodicTorus d S) : Prop :=
  y ∈ 𝒮.centres ∧ 𝒮.cell y ⊆ W ∧ (𝒮.centreIndex y = 0 ∨ 𝒮.collar y ⊆ W)
def cellNeighborhood (z : PeriodicTorus d S) : Set (LatticeSite d S 𝒮.ξ) :=
  {x | (x : PeriodicTorus d S) ∈ 𝒮.cell z ∨
    ∃ y : LatticeSite d S 𝒮.ξ, (y : PeriodicTorus d S) ∈ 𝒮.cell z ∧ IsNeighbor x y}
def IsSupportedNear (z : PeriodicTorus d S) (f : LatticeSite d S 𝒮.ξ → ℝ) : Prop :=
  ∀ x, x ∉ 𝒮.cellNeighborhood z → f x = 0
def IsFieldSupportedNear (z : PeriodicTorus d S) (F : BondField d S 𝒮.ξ) : Prop :=
  ∀ b : LatticeBond d S 𝒮.ξ, (b.source : PeriodicTorus d S) ∉ 𝒮.cell z →
    (b.target : PeriodicTorus d S) ∉ 𝒮.cell z → F b.dir b.source = 0
end BlockSetting
def siteLOneDist (x y : LatticeSite d S ξ) : ℝ :=
  lOneNorm ((x : PeriodicTorus d S) - (y : PeriodicTorus d S))
def holderSeminorm (α : ℝ) (D : LatticeSite d S ξ → ℝ) : ℝ :=
  sSup {r | ∃ x y : LatticeSite d S ξ, 0 < siteLOneDist x y ∧
    siteLOneDist x y ≤ 1 ∧
    r = |D x - D y| / siteLOneDist x y ^ α}
def scaledHolderSeminorm (α s : ℝ) (D : LatticeSite d S ξ → ℝ) : ℝ :=
  sSup {r | ∃ x y : LatticeSite d S ξ, 0 < siteLOneDist x y ∧
    siteLOneDist x y ≤ s ∧
    r = (s / siteLOneDist x y) ^ α * |D x - D y|}
def fieldHolderSeminorm (α : ℝ) (F : BondField d S ξ) : ℝ := ⨆ μ, holderSeminorm α (F μ)
end Dirichlet
end YangMills.Construction
