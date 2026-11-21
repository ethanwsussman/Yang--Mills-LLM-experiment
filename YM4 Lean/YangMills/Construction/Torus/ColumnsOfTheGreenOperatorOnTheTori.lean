import YangMills.Construction.SeparatedSequences.InverseGreenConstants
import YangMills.Construction.Torus.GreenOperatorBoundsOnTheTori
import YangMills.Construction.Torus.PropertiesOfTheWeightedDistanceAndCells
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.GeneralTorus
def ScaleData.IsPlaquetteBond {D : ScaleData} (p : D.BasePlaquette) (b : D.BaseBond) : Prop :=
  b.1 ∈ p.boundaryBonds ∨ b.1.flip ∈ p.boundaryBonds
namespace GaugeSetting
variable (W : GaugeSetting)
def coarseForm (c : W.CoarseBond) : ↥W.formSubspace := W.meanOpAdjoint (W.coarseDelta c)
def greenColumn (c : W.CoarseBond) : ↥W.formSubspace := W.greenOp (W.coarseForm c)
def normalizedCoarseEntry (c c' : W.CoarseBond) : ℝ :=
  (coarseSpacing c)⁻¹ * (coarseSpacing c')⁻¹ * W.matrixEntry W.coarseGreen c c'
def baseCoarseBond (b : W.data.BaseBond) (h : b ∈ W.coarseBondsAt 0) : W.CoarseBond :=
  ⟨⟨0, Nat.succ_pos _⟩, b, h⟩
def IsCellCoverOfSupport (c : W.CoarseBond) (k : ℕ) (C : Finset W.data.Space) : Prop :=
  C.card ≤ 1 + W.data.L ^ 4 ∧
    (∀ y'' ∈ C, y'' ∈ W.chain.shellSites k ∪ W.chain.shellSites (k + 1)) ∧
    coarseSupport c = ⋃ y'' ∈ C, W.chain.localCube y'' ∧
    ∀ y'' ∈ C, W.chain.localSpacing y'' ≤ coarseSpacing c ∧
      siteCoarseDist y'' c ≤ SeparatedSequences.cellRadius 4 W.data.L
open Classical in
structure CoarseFormsCellwise : Prop where
  unit_interval : ∀ (c : W.CoarseBond) (b : W.data.BaseBond),
    0 ≤ (W.coarseForm c).1 b ∧ (W.coarseForm c).1 b ≤ 1
  base_level : ∀ (b : W.data.BaseBond) (h : b ∈ W.coarseBondsAt 0),
    (W.coarseForm (W.baseCoarseBond b h)).1 = Pi.single b 1 ∧
      W.SupportedInCell (W.coarseForm (W.baseCoarseBond b h)).1
        (coarseAnchor (W.baseCoarseBond b h)) ∧
      ∀ A : ↥W.formSubspace, |W.meanOp A (W.baseCoarseBond b h)| ≤ |A.1 b|
  higher_level : ∀ (c : W.CoarseBond) (k : ℕ), coarseLevel c = k + 1 →
    (∀ b : W.data.BaseBond, (W.coarseForm c).1 b ≠ 0 →
      ScaleData.posBondDir b = ScaleData.posBondDir c.2.1 ∧
        (b.1.src : W.data.Space) ∈ coarseSupport c) ∧
    ∃ C : Finset W.data.Space, W.IsCellCoverOfSupport c k C ∧
      (∃ J : W.data.Space → ↥W.formSubspace, W.coarseForm c = ∑ y ∈ C, J y ∧
        ∀ y ∈ C, W.SupportedInCell (J y).1 y) ∧
      ∀ A : ↥W.formSubspace, ∃ b ∈ W.bondSet, (∃ y ∈ C, W.chain.LiesInCell b y) ∧
        |W.meanOp A c| ≤ |A.1 b|
end GaugeSetting
namespace GreenColumns
open SeparatedSequences GreenBounds
variable {L : ℕ}
def siteDecay (K : GreenConstants) (s : LevelUnitChain L) (y : s.setting.data.Space)
    (c : s.setting.CoarseBond) : ℝ :=
  Real.exp (-K.rate * GaugeSetting.siteCoarseDist y c)
structure ColumnEstimates (K : GreenConstants) (s : LevelUnitChain L)
    (c : s.setting.CoarseBond) : Prop where
  bond_le : ∀ y ∈ s.chain.shellSitesUnion, ∀ b ∈ s.setting.bondSet, s.chain.LiesInCell b y →
    |(s.setting.greenColumn c).1 b| ≤
      greenColumnConstant 4 L K.rate K.bound * s.chain.localSpacing y ^ 2 * siteDecay K s y c
  grad_le : ∀ y ∈ s.chain.shellSitesUnion, ∀ x : s.data.BaseSite,
    (x : s.data.Space) ∈ s.chain.localCube y → ∀ μ ν : Fin 4,
      |s.grad (s.setting.greenColumn c).1 x μ ν| ≤
        greenColumnConstant 4 L K.rate K.bound * s.chain.localSpacing y * siteDecay K s y c
  holder_le : ∀ y ∈ s.chain.shellSitesUnion, ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : s.data.Space → ℂ,
    s.IsSmoothSupportedInDoubleCube y ζ → ∀ path, IsGeodesicChoice s.scales path →
      s.cutoffGradSeminorm α ζ (s.setting.greenColumn c).1 path ≤
        ENNReal.ofReal ((1 + (L : ℝ) ^ 4) * Real.exp (K.rate * cellRadius 4 L) *
            K.holderBound α * s.chain.localSpacing y ^ (1 - α) * siteDecay K s y c) *
          s.cutoffSize α (s.chain.localSpacing y) ζ
structure PlaquetteEstimates (K : GreenConstants) (s : LevelUnitChain L)
    (c : s.setting.CoarseBond) : Prop where
  bond_le : ∀ (p : s.data.BasePlaquette), ∀ y ∈ s.chain.shellSitesUnion,
    (∃ x ∈ p.cornerSet, (x : s.data.Space) ∈ s.chain.localCube y) →
      ∀ b : s.data.BaseBond, ScaleData.IsPlaquetteBond p b →
        |(s.setting.greenColumn c).1 b| ≤
          plaquetteColumnConstant 4 L K.rate K.bound * s.chain.localSpacing y ^ 2 *
            siteDecay K s y c
  curl_le : ∀ (p : s.data.BasePlaquette), ∀ y ∈ s.chain.shellSitesUnion,
    (∃ x ∈ p.cornerSet, (x : s.data.Space) ∈ s.chain.localCube y) →
      |s.data.plaquetteCurl (s.setting.greenColumn c).1 p| ≤
        plaquetteColumnConstant 4 L K.rate K.bound * s.chain.localSpacing y *
          siteDecay K s y c
structure NormalizedMatrixEstimates (K : GreenConstants) (s : LevelUnitChain L) : Prop where
  symm : ∀ c c' : s.setting.CoarseBond,
    s.setting.normalizedCoarseEntry c c' = s.setting.normalizedCoarseEntry c' c
  kernel_le : ∀ c c' : s.setting.CoarseBond,
    |s.setting.kernelEntry s.setting.coarseGreen c c'| ≤
      compressedEntryConstant 4 L K.rate K.bound * GaugeSetting.coarseSpacing c ^ 2 *
        Real.exp (-K.rate * GaugeSetting.coarseDist c c')
  entry_le : ∀ c c' : s.setting.CoarseBond,
    |s.setting.normalizedCoarseEntry c c'| ≤
      compressedEntryConstant 4 L K.rate K.bound *
        Real.exp (-K.rate * GaugeSetting.coarseDist c c')
  quadratic_bounds : ∀ v : s.setting.CoarseField,
    compressedGreenLowerBound 4 1 * ∑ᶠ c, v c ^ 2 ≤
        ∑ᶠ c, ∑ᶠ c', v c * s.setting.normalizedCoarseEntry c c' * v c' ∧
      ∑ᶠ c, ∑ᶠ c', v c * s.setting.normalizedCoarseEntry c c' * v c' ≤ ∑ᶠ c, v c ^ 2
end GreenColumns
def GreenColumnsStatement : Prop :=
  ∀ (L : ℕ) (s : GreenBounds.LevelUnitChain L),
    (GreenBounds.chosen L).AboveLowerBounds s → L ≤ s.data.blockCount →
      s.setting.CoarseFormsCellwise ∧
        (∀ c : s.setting.CoarseBond,
          GreenColumns.ColumnEstimates (GreenBounds.chosen L) s c) ∧
        (∀ c : s.setting.CoarseBond,
          GreenColumns.PlaquetteEstimates (GreenBounds.chosen L) s c) ∧
        GreenColumns.NormalizedMatrixEstimates (GreenBounds.chosen L) s
end YangMills.Construction.GeneralTorus
