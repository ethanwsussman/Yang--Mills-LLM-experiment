import YangMills.Construction.ColdChainAtEveryLevel.PairsAtOffsets
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open Offsets
def gaugeMapAcrossFramesStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (F F' : BlockFrame) (m : ℕ) (S : Finset F.Cell) (S' : Finset F'.Cell) (s : ℝ)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r ρ : ℕ),
    F'.blockSide = F.blockSide → F'.depth = F.depth → Odd F.blockSide → IsAdmissibleAmbient F →
    IsAdmissibleAmbient F' → 1024 ≤ m → IsOrthantRegular S m → IsOrthantRegular S' m → 0 < s → s ≤ c →
    IsCold S F.top s V → IsCold S' F'.top s V' → AgreeOnBall S V S' V' Y Y' r → 30 ≤ ρ → ρ + 110 ≤ r →
    ∀ (u : F.Site 0 → Fin 4 → ℍ[ℝ]) (u' : F'.Site 0 → Fin 4 → ℍ[ℝ]),
      (∀ (p : Fin 4 → ℤ) (i : Fin 4), WithinCellRadius F.blockSide F.top ρ 0 p →
        u (siteAtOffset 0 Y p) i = u' (siteAtOffset 0 Y' p) i) →
      ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (ρ - 30) 0 q → siteAtOffset 0 Y q ∈ sitesOfCells S 0 →
        GaugeMap.gaugeMap S V (referenceFieldChain S V 0) u (siteAtOffset 0 Y q) =
          GaugeMap.gaugeMap S' V' (referenceFieldChain S' V' 0) u' (siteAtOffset 0 Y' q)
end YangMills.Construction.BlockAverages
end
