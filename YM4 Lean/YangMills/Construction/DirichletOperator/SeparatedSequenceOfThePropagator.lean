import YangMills.Construction.Dirichlet.RegionSequenceOperators
import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import YangMills.Construction.SeparatedSequences.LevelScaledParameters
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace Propagator
structure SeparatedRegionChain extends SeparatedSequences.LevelScaledParameters where
  blockExponent : ℕ
  gapExponent : ℕ
  le_gapNumber : L ≤ L ^ gapExponent
  Ω : ℕ → Set (FourTorus L m)
  separated : SeparatedSequences.IsSeparatedSequence (L := L) (m := m)
    ⟨K, level, level, blockExponent, level_le_K, level_le_K⟩ ((L ^ gapExponent : ℕ) : ℝ) Ω
  first_nonempty : (Ω 0).Nonempty
  empty_past : ∀ n, level < n → Ω n = ∅
namespace SeparatedRegionChain
variable (P : SeparatedRegionChain)
def blockCount : ℕ := P.L ^ P.blockExponent
def gapSize : ℕ := P.L ^ P.gapExponent
def scaleData : SeparatedSequences.ScaleData :=
  ⟨P.K, P.level, P.level, P.blockExponent, P.level_le_K, P.level_le_K⟩
def layerDist (y y' : FourTorus P.L P.m) : ENNReal :=
  SeparatedSequences.layerWeightedDist P.scaleData P.Ω y y'
def sideInUnits : ℝ := YangMills.Construction.Torus.unitSide P.L P.m P.K P.level
theorem L_pos : 0 < (P.L : ℝ) := by
  have h := P.isAdmissible.2
  exact_mod_cast (by omega : 0 < P.L)
theorem sideInUnits_pos : 0 < P.sideInUnits :=
  mul_pos two_pos (zpow_pos P.L_pos _)
theorem torusSide_ne_zero : torusSide P.L P.m ≠ 0 :=
  (mul_pos two_pos (pow_pos P.L_pos _)).ne'
def toUnits (x : FourTorus P.L P.m) :
    YangMills.Construction.Torus.PeriodicTorus 4 P.sideInUnits :=
  fun μ => AddCircle.equivAddCircle _ _ P.torusSide_ne_zero P.sideInUnits_pos.ne' (x μ)
def regionInUnits (n : ℕ) : Set (YangMills.Construction.Torus.PeriodicTorus 4 P.sideInUnits) :=
  P.toUnits '' P.Ω n
end SeparatedRegionChain
end Propagator
namespace RegionSequence.NestedRegions
structure IsLevelUnitChain (𝒮 : NestedRegions) (K m M R₁ : ℕ) : Prop where
  cutoff_pos : 0 < K
  exponent_pos : 0 < m
  level_le : 𝒮.s ≤ K
  spacing_eq : 𝒮.ξ = YangMills.Construction.Torus.unitSpacing 𝒮.L 𝒮.s
  side_eq : 𝒮.side = YangMills.Construction.Torus.unitSide 𝒮.L m K 𝒮.s
  separated : YangMills.Construction.Torus.IsSeparatedChain 𝒮.L 𝒮.ξ M R₁ 𝒮.s 𝒮.Ω
end RegionSequence.NestedRegions
end YangMills.Construction
end
