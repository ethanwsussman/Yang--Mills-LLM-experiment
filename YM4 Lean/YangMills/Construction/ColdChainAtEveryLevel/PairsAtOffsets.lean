import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction
open BlockAverages
namespace BlockAverages.Offsets
variable {F F' : BlockFrame}
def siteAtOffset (j : ℕ) (Y : F.Cell) (p : Fin 4 → ℤ) : F.Site j := cellCentre j Y + siteOfCoords j p
def WithinCellRadius (L n ρ j : ℕ) (p : Fin 4 → ℤ) : Prop := ∀ i, (L : ℤ) ^ j * |p i| ≤ (ρ : ℤ) * (L : ℤ) ^ n
structure ChartsAgreeAtOffsets (Y : F.Cell) (Y' : F'.Cell) (ρ : ℕ) (A : ChainChart F) (A' : ChainChart F') :
    Prop where
  fine : ∀ (p : Fin 4 → ℤ) (i : Fin 4), WithinCellRadius F.blockSide F.top ρ 0 p →
    A.fine (siteAtOffset 0 Y p) i = A'.fine (siteAtOffset 0 Y' p) i
  coarse : ∀ (j : ℕ) (p : Fin 4 → ℤ) (i : Fin 4), j + 1 < F.top → WithinCellRadius F.blockSide F.top ρ (j + 1) p →
    A.coarse j (siteAtOffset (j + 1) Y p) i = A'.coarse j (siteAtOffset (j + 1) Y' p) i
structure SupportedNear (S : Finset F.Cell) (Y : F.Cell) (ρ : ℕ) (A : ChainChart F) : Prop where
  fine : ∀ b ∈ innerBonds S 0, ρ < cellSupDist (enclosingCell b.1) Y → A.fine b.1 b.2 = 0
  coarse : ∀ (j : ℕ), j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1), ρ < cellSupDist (enclosingCell b.1) Y →
    A.coarse j b.1 b.2 = 0
def chartSmul (χ : F.SiteWeights) (A : ChainChart F) : ChainChart F :=
  ⟨fun x i => χ 0 x • A.fine x i, fun j y i => χ (j + 1) y • A.coarse j y i⟩
def tentCutoff (F : BlockFrame) (Y : F.Cell) (ρ : ℝ) : F.SiteWeights :=
  fun _ x => max 0 (min 1 (ρ - (baseDistance x (cellCentre 0 Y) : ℝ) / (F.blockSide : ℝ) ^ F.top))
end BlockAverages.Offsets
end YangMills.Construction
end
