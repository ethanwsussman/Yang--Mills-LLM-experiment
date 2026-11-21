import YangMills.Construction.ColdChainAtEveryLevel.PinOfAFramingOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PinnedGauge
structure HasPatchCellConditions (D : PinnedGaugeData) (r₀ n₁ C₃ n₀ : ℝ) : Prop where
  filledToward : LatticeFractionalIntegration.IsFilledToward D.scale D.corner D.region
  scale_pos : 1 ≤ D.scale
  cellSide_pos : 1 ≤ D.cellSide
  scale_le_mul : (D.scale : ℝ) ≤ r₀ * D.cellSide
  cellSites_sub : ∀ y ∈ D.cells, D.cellSites y ⊆ D.region
  cellSites_card : ∀ y ∈ D.cells, (D.cellSites y).card = D.cellSide ^ 4
  base_mem_cells : D.base ∈ D.cells
  cells_card_le : (D.cells.card : ℝ) ≤ n₁
  average_add : ∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' → ∀ f g,
    D.bondAverage y y' (f + g) = D.bondAverage y y' f + D.bondAverage y y' g
  average_congr : ∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' →
    ∀ f g : LatticeFractionalIntegration.Lattice4 → Fin 4 → ℍ[ℝ],
    (∀ b ∈ LatticeFractionalIntegration.bondsOf D.region, f b.1 b.2 = g b.1 b.2) →
      D.bondAverage y y' f = D.bondAverage y y' g
  average_difference : ∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' →
    ∀ φ : LatticeFractionalIntegration.Lattice4 → ℍ[ℝ],
    D.bondAverage y y' (LatticeFractionalIntegration.latticeDifference φ) = D.cellMean y' φ - D.cellMean y φ
  average_pow_le : ∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' →
    ∀ f : LatticeFractionalIntegration.Lattice4 → Fin 4 → ℍ[ℝ],
    ‖D.bondAverage y y' f‖ ^ 4 ≤ C₃ * ∑ b ∈ LatticeFractionalIntegration.bondsOf D.region, ‖f b.1 b.2‖ ^ 4
  joined : ∀ (κ : D.CellIndex → ℍ[ℝ]) (T : ℝ), 0 ≤ T →
    (∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' → ‖κ y - κ y'‖ ^ 4 ≤ T) → κ D.base = 0 →
      ∀ y ∈ D.cells, ‖κ y‖ ^ 4 ≤ n₀ * T
end PinnedGauge
namespace BlockAverages
def patchCellConditionsStatement : Prop :=
  ∃ C₃ n₀ : ℝ, 0 ≤ C₃ ∧ 0 ≤ n₀ ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
    ∀ (V : F.GaugeField F.top) (z : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain)
      (k : F.SiteGauge), z ∈ S →
      PinnedGauge.HasPatchCellConditions (pinnedGaugeDataOfPatch S V z W kW X k) 9 (47 ^ 4) C₃ n₀ ∧
        ∀ f g : F.Site 0 → Fin 4 → ℍ[ℝ], (∀ b ∈ patchInnerBonds S z 0, f b.1 b.2 = g b.1 b.2) →
          ∀ c ∈ patchInnerBonds S z F.top, iteratedBlockAverage f F.top c.1 c.2 = iteratedBlockAverage g F.top c.1 c.2
end BlockAverages
end YangMills.Construction
end
