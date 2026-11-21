import YangMills.Construction.Lattice.TowersAndMinimalConfigurations
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice Matrices
namespace SeparatedSequences
variable {L m : ℕ}
structure ScaleData where
  levels : ℕ
  top : ℕ
  unitLevel : ℕ
  blockExp : ℕ
  top_le : top ≤ levels
  unitLevel_le : unitLevel ≤ levels
namespace ScaleData
variable (S : ScaleData)
def finestMesh (L : ℕ) : ℝ := finestMeshInLevelUnits L S.unitLevel
def levelMesh (L n : ℕ) : ℝ := (L : ℝ) ^ ((n : ℤ) - (S.unitLevel : ℤ))
def toUnits (L : ℕ) (r : ℝ) : ℝ := toLevelUnits L S.levels S.unitLevel r
def blockPartitionIndex (n : ℕ) : ℤ := scaledCubeIndex S.levels n S.blockExp
end ScaleData
abbrev FineBond (L m : ℕ) (S : ScaleData) : Type := BondAtLevel L m S.levels 0
variable (S : ScaleData)
def IsBlockUnion (n : ℕ) (X : Set (FourTorus L m)) : Prop :=
  X = ∅ ∨ (-(m : ℤ) ≤ S.blockPartitionIndex n ∧ IsPartitionRegion (S.blockPartitionIndex n) X)
def IsSeparatedSequence (R₁ : ℝ) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  (∀ n ≤ S.top, IsBlockUnion S n (Ω n)) ∧
    ∀ n < S.top, Ω (n + 1) ⊆ Ω n ∧
      ENNReal.ofReal (R₁ * (L : ℝ) ^ S.blockExp * S.levelMesh L n) <
        supDistInLevelUnits S.levels S.unitLevel
          (complementRegion (S.blockPartitionIndex n) (Ω n)) (Ω (n + 1))
def truncatedMember (Ω : ℕ → Set (FourTorus L m)) (n : ℕ) : Set (FourTorus L m) :=
  open Classical in if n ≤ S.top then Ω n else ∅
def layerSet (Ω : ℕ → Set (FourTorus L m)) (n : ℕ) : Set (FourTorus L m) :=
  open Classical in
  if n < S.top then closure (Ω n \ Ω (n + 1)) else if n = S.top then Ω S.top else ∅
def layerLatticeSites (Ω : ℕ → Set (FourTorus L m)) (n : ℕ) : Set (SiteAtLevel L m S.levels n) :=
  sitesIn (layerSet S Ω n)
def layerPoints (Ω : ℕ → Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃ n ∈ Iic S.top,
    (fun y : SiteAtLevel L m S.levels n => (y : FourTorus L m)) '' layerLatticeSites S Ω n
def closedSupCube (z : FourTorus L m) (a : ℝ) : Set (FourTorus L m) :=
  {x | torusSupNorm (x - z) ≤ a / 2}
def siteBlock {n : ℕ} (y : SiteAtLevel L m S.levels n) : Set (FourTorus L m) := cubeAround y
def doubledSiteBlock {n : ℕ} (y : SiteAtLevel L m S.levels n) : Set (FourTorus L m) :=
  closedSupCube (y : FourTorus L m) (2 * meshSize L (levelDepth S.levels n))
def layerWeightedLength (Ω : ℕ → Set (FourTorus L m)) (Γ : List LiftedSegment) : ℝ :=
  ∑ n ∈ Finset.Icc 1 S.top, (S.levelMesh L n)⁻¹ *
      S.toUnits L (pathLengthIn (torusSide L m) Γ (layerSet S Ω n)) +
    (S.levelMesh L 0)⁻¹ * S.toUnits L (pathLengthIn (torusSide L m) Γ (truncatedMember S Ω 1)ᶜ)
def layerWeightedDist (Ω : ℕ → Set (FourTorus L m)) (y y' : FourTorus L m) : ℝ≥0∞ :=
  ⨅ Γ ∈ {Γ : List LiftedSegment | IsTreeGraph (torusSide L m) Γ ∧
      y ∈ segmentsSupport (torusSide L m) Γ ∧ y' ∈ segmentsSupport (torusSide L m) Γ},
    ENNReal.ofReal (layerWeightedLength S Ω Γ)
abbrev LevelCube (L m : ℕ) : Type := ℕ × Set (FourTorus L m)
def IsLieOneFormOn {j : ℤ} (𝔥 : Set ComplexMatrix2) (ℬ : Set (Bond L m j))
    (A : Bond L m j → ComplexMatrix2) : Prop :=
  (∀ b ∈ ℬ, b.IsPositivelyOriented → A b ∈ 𝔥) ∧ ∀ b ∈ ℬ, A b.opposite = -A b
def unitL1Dist (x x' : FourTorus L m) : ℝ := S.toUnits L (torusL1Norm (x - x'))
def IsGeodesicPath (Γ : List (FineBond L m S)) (x x' : SiteAtLevel L m S.levels 0) : Prop :=
  IsBondPathFromTo Γ x x' ∧
    ∀ Γ' : List (FineBond L m S), IsBondPathFromTo Γ' x x' → Γ.length ≤ Γ'.length
def IsGeodesicChoice
    (path : SiteAtLevel L m S.levels 0 → SiteAtLevel L m S.levels 0 → List (FineBond L m S)) :
    Prop :=
  ∀ x x' : SiteAtLevel L m S.levels 0, 0 < unitL1Dist S (x : FourTorus L m) x' →
    unitL1Dist S (x : FourTorus L m) x' ≤ 1 → IsGeodesicPath S (path x x') x x'
def IsHolderPair (X : Set (FourTorus L m))
    (path : SiteAtLevel L m S.levels 0 → SiteAtLevel L m S.levels 0 → List (FineBond L m S))
    (x x' : SiteAtLevel L m S.levels 0) : Prop :=
  0 < unitL1Dist S (x : FourTorus L m) x' ∧ unitL1Dist S (x : FourTorus L m) x' ≤ 1 ∧
    ∀ b ∈ path x x', b ∈ (bondsInside X : Set (FineBond L m S))
def holderTerm (β : ℝ) (Uc : FineBond L m S → ComplexMatrix2) (Γ : List (FineBond L m S))
    (x x' : SiteAtLevel L m S.levels 0) (v v' : ComplexMatrix2) : ℝ≥0∞ :=
  ENNReal.ofReal (unitL1Dist S (x : FourTorus L m) x' ^ (-β) *
    ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy (pathHolonomy Uc Γ) v' - v))
def bondTransportHolderSeminorm (X : Set (FourTorus L m)) (ℬ : Set (FineBond L m S)) (β : ℝ)
    (Uc : FineBond L m S → ComplexMatrix2)
    (path : SiteAtLevel L m S.levels 0 → SiteAtLevel L m S.levels 0 → List (FineBond L m S))
    (f : FineBond L m S → ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ b ∈ ℬ, ⨆ b' ∈ ℬ,
    ⨆ _ : b.target - b.source = b'.target - b'.source ∧ IsHolderPair S X path b.source b'.source,
      holderTerm S β Uc (path b.source b'.source) b.source b'.source (f b) (f b')
def scaledHolderSeminorm (β lam : ℝ) (ζ : FourTorus L m → ℂ) : ℝ≥0∞ :=
  ⨆ x : FourTorus L m, ⨆ x' : FourTorus L m,
    ⨆ _ : 0 < unitL1Dist S x x' ∧ unitL1Dist S x x' ≤ lam,
      ENNReal.ofReal ((lam / unitL1Dist S x x') ^ β * ‖ζ x' - ζ x‖)
def complexSupNorm (ζ : FourTorus L m → ℂ) : ℝ≥0∞ := ⨆ x, ENNReal.ofReal ‖ζ x‖
end SeparatedSequences
end YangMills.Construction
