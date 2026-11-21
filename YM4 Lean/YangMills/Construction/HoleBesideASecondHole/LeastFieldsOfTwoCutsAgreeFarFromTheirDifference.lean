import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import YangMills.Construction.HoleBesideASecondHole.CoordinatesOfAFieldNearATop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
variable {F : BlockAverages.BlockFrame}
def minimizingFieldsLocalStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ σ N : ℝ, 0 < σ ∧ 0 < N ∧
    ∀ (F : BlockAverages.BlockFrame) (m : ℕ) (S S' : Finset F.Cell), F.blockSide = L →
      HoleBounds.IsCubicTorus F 64 → 1024 ≤ m → BlockAverages.IsOrthantRegular S m →
      BlockAverages.IsOrthantRegular S' m → ∀ (s : ℝ) (V : F.GaugeField F.top) (W W' : F.GaugeField F.depth),
        0 < s → s ≤ σ → BlockAverages.IsCold S F.top s V →
        BlockAverages.IsCold S' F.top s V → IsMinimizingField a S V W → IsMinimizingField a S' V W' →
        (∀ b ∈ BlockAverages.innerBonds S F.depth, ‖(lexBondCoordinate V W b : ℍ[ℝ])‖ ≤ N * s) ∧
        ∀ (y : F.Cell) (r : ℕ), 1 ≤ r → 2 * r + 2 < F.extent 0 →
          (∀ h, BlockAverages.WithinRadius r h →
            (y + BlockAverages.siteOfCoords F.top h ∈ S ↔ y + BlockAverages.siteOfCoords F.top h ∈ S')) →
          ∀ b ∈ BlockAverages.innerBonds S F.depth, b ∈ BlockAverages.innerBonds S' F.depth →
            BlockAverages.cellSupDist y (BlockAverages.enclosingCell b.1) ≤ 1 →
            BlockAverages.cellSupDist y
              (BlockAverages.enclosingCell (b.1 + BlockAverages.unitStep F.depth b.2)) ≤ 1 →
            ‖(lexBondCoordinate V W b : ℍ[ℝ]) - lexBondCoordinate V W' b‖ ≤
              N * s * Real.exp (-δ * ((r : ℝ) - 1))
end YangMills.Construction.LumpContours
end
