import YangMills.Construction.ColdChainAtEveryLevel.PairsAtOffsets
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import YangMills.Construction.ColdChainAtEveryLevel.TotalAtAComplexTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BlockAverages
open Offsets
def firstVariationAcrossFramesStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (F F' : BlockFrame) (a : ℝ) (m : ℕ) (S : Finset F.Cell) (S' : Finset F'.Cell) (s : ℝ)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r ρ : ℕ),
    F'.blockSide = F.blockSide → F'.depth = F.depth → Odd F.blockSide → 3 ≤ F.blockSide → IsAdmissibleAmbient F →
    IsAdmissibleAmbient F' → 1024 ≤ m → IsOrthantRegular S m → IsOrthantRegular S' m → 0 < s → s ≤ c →
    IsCold S F.top s V → IsCold S' F'.top s V' → AgreeOnBall S V S' V' Y Y' r → 10 ≤ ρ → ρ + 110 ≤ r →
    ∀ (W : ComplexChainChart F) (W' : ComplexChainChart F') (T : F.ComplexField F.top) (T' : F'.ComplexField F'.top)
      (B : ChainChart F) (B' : ChainChart F'),
      ChartsAgreeAtOffsets Y Y' ρ W.re W'.re → ChartsAgreeAtOffsets Y Y' ρ W.im W'.im →
      (∀ (p : Fin 4 → ℤ) (i : Fin 4), WithinCellRadius F.blockSide F.top ρ F.top p →
        T (siteAtOffset F.top Y p) i = T' (siteAtOffset F'.top Y' p) i) →
      ChartsAgreeAtOffsets Y Y' ρ B B' → SupportedNear S Y (ρ - 10) B → SupportedNear S' Y' (ρ - 10) B' →
      complexFirstVariation a S (referenceFieldChain S V) W T B =
        complexFirstVariation a S' (referenceFieldChain S' V') W' T' B'
end YangMills.Construction.BlockAverages
end
