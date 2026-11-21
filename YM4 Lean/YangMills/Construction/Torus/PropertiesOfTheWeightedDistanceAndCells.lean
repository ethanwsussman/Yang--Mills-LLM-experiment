import YangMills.Construction.GeneralTorus.SeparatedChainDepth
import YangMills.Construction.SeparatedSequences.ExplicitConstants
import YangMills.Construction.Torus.ObjectsOfASequenceOfRegionsOnAGeneralTorus
import YangMills.Construction.Weighted.LengthDensity
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace GeneralTorus
theorem ScaleData.torusSide_pos (D : ScaleData) : 0 < D.torusSide := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.torusSide_pos <;> assumption
instance ScaleData.fact_torusSide_pos (D : ScaleData) : Fact (0 < D.torusSide) :=
  ⟨D.torusSide_pos⟩
namespace SeparatedChain
variable {D : ScaleData} (B : SeparatedChain D)
def augmentedShell : ℕ → Set D.Space
  | 0 => closedComplement (B.set 1)
  | n + 1 => B.shell (n + 1)
def AugmentedShellsSeparated : Prop :=
  ∀ n n' : ℕ, n ≤ D.lastLevel → n' ≤ D.lastLevel →
    ∀ y ∈ B.augmentedShell n, ∀ y' ∈ B.augmentedShell n',
    (D.gapCount : ℝ) * (D.blockCount : ℝ) * max (|(n : ℝ) - (n' : ℝ)| - 1) 0 ≤
        B.scaledDist y y' ∧
      ∀ s ε : ℝ, 0 < ε →
        |s| * Real.log (D.L : ℝ) ≤ ε * ((D.gapCount : ℝ) * (D.blockCount : ℝ)) →
        (D.L : ℝ) ^ (s * ((n' : ℝ) - (n : ℝ))) * Real.exp (-ε * B.scaledDist y y') ≤
          (D.L : ℝ) ^ |s|
def SupDistFunctionsLipschitzScaled : Prop :=
  ∀ n : ℕ, n ≤ D.lastLevel → ∀ (z : D.Space) (r κ : ℝ) (F : ℝ → ℝ), 0 < r →
    Disjoint {x : D.Space | torusSupNorm (x - z) ≤ r} (B.set (n + 2)) →
    (∀ s s' : ℝ, 0 ≤ s → 0 ≤ s' → |F s - F s'| ≤ κ * |s - s'|) →
    (∀ s : ℝ, r ≤ s → F s = F r) →
    ∀ x x' : D.Space, |F (torusSupNorm (x - z)) - F (torusSupNorm (x' - z))| ≤
      κ * D.levelSpacing (n + 1) * B.scaledDist x x'
def MeetingCellsAreClose : Prop :=
  (∀ n n' : ℕ, ∀ y ∈ B.shellSites n, ∀ y' ∈ B.shellSites n',
    (B.localCube y ∩ B.localCube y').Nonempty →
      |(n : ℤ) - (n' : ℤ)| ≤ 1 ∧ B.scaledDist y y' ≤ 4) ∧
  ∀ x ∈ D.baseLattice, ∀ x' ∈ D.baseLattice, x ∈ B.set 0 → x' ∈ B.set 0 →
    torusSupNorm (x - x') ≤ D.baseSpacing →
      ∃ y ∈ B.shellSitesUnion, ∃ y' ∈ B.shellSitesUnion, x ∈ B.localCube y ∧ x' ∈ B.localCube y' ∧
        (B.localCube y = B.localCube y' ∨ (B.localCube y ∩ B.localCube y').Nonempty)
def ScaledDistEqInfIntegral : Prop :=
  ∀ x x' : D.Space, ENNReal.ofReal (B.scaledDist x x') =
    ⨅ (Γ : List LiftedSegment)
      (_ : IsTreeGraph D.torusSide Γ ∧ x ∈ segmentsSupport D.torusSide Γ ∧
        x' ∈ segmentsSupport D.torusSide Γ),
      Weighted.setLIntegralL1 (segmentsSupport D.torusSide Γ)
        fun p => ENNReal.ofReal (D.levelSpacing (B.depthIndex p))⁻¹
end SeparatedChain
namespace GaugeSetting
variable (W : GaugeSetting)
def ExpSumsOfScaledDist : Prop :=
  ∀ α : ℝ, 0 < α →
    4 / α * (4 * Real.log (W.data.L : ℝ) + Real.log 2) ≤
      (W.data.gapCount : ℝ) * (W.data.blockCount : ℝ) →
    ∀ y ∈ W.chain.shellSitesUnion,
      ∑ᶠ y' : ↥W.chain.shellSitesUnion, Real.exp (-α * W.chain.scaledDist y y') ≤
          SeparatedSequences.expSumConstant 4 W.data.L α ∧
      ∑ᶠ c' : W.CoarseBond, Real.exp (-α * siteCoarseDist y c') ≤
          2 * 4 * SeparatedSequences.expSumConstant 4 W.data.L α
variable {W}
def coarseSupport (c : W.CoarseBond) : Set W.data.Space := ScaleData.bondSupport c.2.1
variable (W)
def CoarseSupportsAreCellUnions : Prop :=
  ∀ (c : W.CoarseBond) (k : ℕ), coarseLevel c = k + 1 →
    coarseSupport c ⊆ W.chain.set k ∧
    Disjoint (interior (coarseSupport c)) (W.chain.set (k + 2)) ∧
    (∀ y' : W.data.Space, y' = coarseSrc c ∨ y' = coarseTgt c → y' ∉ W.chain.set (k + 1) →
      W.data.cubeAt (k + 1) y' ⊆ W.chain.shell k ∧
      W.data.coarseBlock k y' ⊆ W.chain.shellSites k ∧
      W.data.cubeAt (k + 1) y' = ⋃ z ∈ W.data.coarseBlock k y', W.chain.localCube z ∧
      (W.chain.localCube '' W.data.coarseBlock k y').ncard = W.data.L ^ 4) ∧
    ∃ C : Finset W.data.Space, C.card ≤ 1 + W.data.L ^ 4 ∧
      (∀ y'' ∈ C, y'' ∈ W.chain.shellSites k ∪ W.chain.shellSites (k + 1)) ∧
      coarseSupport c = ⋃ y'' ∈ C, W.chain.localCube y'' ∧
      ∀ y'' ∈ C, W.chain.localSpacing y'' ≤ coarseSpacing c ∧
        siteCoarseDist y'' c ≤ SeparatedSequences.cellRadius 4 W.data.L
def CoarseEndpointsClose : Prop :=
  ∀ c : W.CoarseBond, W.chain.scaledDist (coarseSrc c) (coarseTgt c) ≤ 1 / 2 * ((W.data.L : ℝ) + 1)
end GaugeSetting
end GeneralTorus
end YangMills.Construction
end
