import YangMills.Construction.ColdChainAtEveryLevel.TotalAtAComplexTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def firstVariationCellWeight (S : Finset F.Cell) (R : F.FieldChain) (s : ℝ) (W : ComplexChainChart F) {k : ℕ}
    (b : Fin k → F.Site F.top × Fin 4) (ζ : Fin k → ℂ) (z : F.Cell) : ℝ :=
  s + localNorm S R W.re (constOneWeights F) z + localNorm S R W.im (constOneWeights F) z +
    ∑ l, if cellSupDist z (b l).1 ≤ 1 then ‖ζ l‖ else 0
def localFirstVariationStatement : Prop :=
  ∀ a δ : ℝ, 0 < a → 0 < δ → δ ≤ 1 / 8 → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (k : ℕ) (b : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
          ∀ (W : ComplexChainChart F) (ζ : Fin k → ℂ) (B : ChainChart F),
            complexSupWeightedNorm S δ (referenceFieldChain S V) W ≤ c → ∑ l, ‖ζ l‖ ≤ c →
            ‖complexFirstVariation a S (referenceFieldChain S V) W (complexTwistedTop b X ζ V) B‖ ≤
              C * ∑ z ∈ S, firstVariationCellWeight S (referenceFieldChain S V) s W b ζ z *
                localNorm S (referenceFieldChain S V) B (constOneWeights F) z
end YangMills.Construction.BlockAverages
end
