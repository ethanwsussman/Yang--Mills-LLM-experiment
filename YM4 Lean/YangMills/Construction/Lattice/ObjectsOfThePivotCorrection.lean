import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Lattice.ObjectsOfTheChartAtAConfiguration
import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open Matrices Coordinates
variable {L m K k : ℕ}
structure PathLengthBounds (L m K k : ℕ) : Prop where
  contour : ∀ (y : SiteAtLevel L m K (k + 1)) (x : SiteAtLevel L m K k),
    x ∈ sitesInBlock (levelDepth K k) y → ∀ σ : AxisOrdering y x,
      (orderedContour y x σ).length ≤ 2 * (L - 1)
  crossing : ∀ c : BondAtLevel L m K (k + 1), ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
    (crossingPath c x : List (BondAtLevel L m K k)).length = L
  average : ∀ a ∈ chartSpace L m K k, ∀ c : BondAtLevel L m K (k + 1),
    ComplexMatrix2.operatorNorm (linearBlockAverage (extendAntisymm a) c) ≤
        (L : ℝ) ^ (-5 : ℤ) * (L : ℝ) ^ 4 * (5 * (L : ℝ) - 4) * GroupLieProduct.supNorm a ∧
      (L : ℝ) ^ (-5 : ℤ) * (L : ℝ) ^ 4 * (5 * (L : ℝ) - 4) * GroupLieProduct.supNorm a ≤
        5 * GroupLieProduct.supNorm a
structure PivotPlacement (c : ↥(coarsePositiveBonds L m K k)) (μ : Fin 4) : Prop where
  mem : (pivot (c : BondAtLevel L m K (k + 1)) : BondAtLevel L m K k) ∈
    bondsInDoubleBlock (c : BondAtLevel L m K (k + 1))
  only_pivot : ∀ c' : BondAtLevel L m K (k + 1), c'.IsPositivelyOriented →
    (pivot c' : BondAtLevel L m K k) ∈ bondsInDoubleBlock (c : BondAtLevel L m K (k + 1)) →
      (pivot c' : BondAtLevel L m K k) = pivot (c : BondAtLevel L m K (k + 1))
  positive : ∀ c' : BondAtLevel L m K (k + 1), c'.IsPositivelyOriented →
    (pivot c' : BondAtLevel L m K k).IsPositivelyOriented
  injective : ∀ c' c'' : BondAtLevel L m K (k + 1), c'.IsPositivelyOriented →
    c''.IsPositivelyOriented → (pivot c' : BondAtLevel L m K k) = pivot c'' → c' = c''
  off_contours : ∀ (y : SiteAtLevel L m K (k + 1)) (x : SiteAtLevel L m K k),
    x ∈ sitesInBlock (levelDepth K k) y → ∀ σ : AxisOrdering y x,
      (pivot (c : BondAtLevel L m K (k + 1)) : BondAtLevel L m K k) ∉ orderedContour y x σ ∧
        (pivot (c : BondAtLevel L m K (k + 1)) : BondAtLevel L m K k).opposite ∉
          orderedContour y x σ
  opposite_off_crossing : ∀ x ∈ sitesInBlock (levelDepth K k) (c : BondAtLevel L m K (k + 1)).source,
    (pivot (c : BondAtLevel L m K (k + 1)) : BondAtLevel L m K k).opposite ∉
      crossingPath (c : BondAtLevel L m K (k + 1)) x
  on_crossing_iff : ∀ x ∈ sitesInBlock (levelDepth K k) (c : BondAtLevel L m K (k + 1)).source,
    (pivot (c : BondAtLevel L m K (k + 1)) : BondAtLevel L m K k) ∈
        crossingPath (c : BondAtLevel L m K (k + 1)) x ↔
      ∃ n : ℤ, 2 * |n| ≤ (L : ℤ) - 1 ∧
        x = (c : BondAtLevel L m K (k + 1)).source.toSublattice (levelDepth K k) +
          n • unitStep L m (levelDepth K k) μ
  crossing_sites : {x ∈ sitesInBlock (levelDepth K k) (c : BondAtLevel L m K (k + 1)).source |
    (pivot (c : BondAtLevel L m K (k + 1)) : BondAtLevel L m K k) ∈
      crossingPath (c : BondAtLevel L m K (k + 1)) x}.ncard = L
  crossed_once : ∀ x ∈ sitesInBlock (levelDepth K k) (c : BondAtLevel L m K (k + 1)).source,
    (pivot (c : BondAtLevel L m K (k + 1)) : BondAtLevel L m K k) ∈
        crossingPath (c : BondAtLevel L m K (k + 1)) x →
      ∃! i : Fin (crossingPath (c : BondAtLevel L m K (k + 1)) x : List (BondAtLevel L m K k)).length,
        (crossingPath (c : BondAtLevel L m K (k + 1)) x : List (BondAtLevel L m K k)).get i =
          pivot (c : BondAtLevel L m K (k + 1))
end PeriodicLattice
end YangMills.Construction
end
