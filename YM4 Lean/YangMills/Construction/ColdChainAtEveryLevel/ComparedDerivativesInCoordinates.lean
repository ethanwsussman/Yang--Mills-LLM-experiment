import YangMills.Construction.ColdChainAtEveryLevel.ComparedCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def comparisonConstant (Cm Dk : ℕ → ℝ) (M Gb : ℝ) (m : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition m, Cm c.length *
    (∏ i, (Dk (c.partSize i) + M) + ∑ l, ∏ i ∈ Finset.univ.erase l, (Dk (c.partSize i) + M + Gb))
def comparedMixedDerivStatement : Prop :=
  ∀ (F F' : BlockFrame) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Finset F.Cell) (S' : Finset F'.Cell) (R : F.FieldChain) (R' : F'.FieldChain) (Y : F.Cell) (Y' : F'.Cell)
    (B : Finset (F.Site F.top × Fin 4)) (B' : Finset (F'.Site F'.top × Fin 4)) (Ck Ck' Cm Dk : ℕ → ℝ)
    (U : ChainChart F) (U' : ChainChart F')
    (Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E)
    (Φ' : ChainChart F' → (F'.Site F'.top → Fin 4 → imaginaryQuaternions) → E) (del G Gb : ℝ) (r₀ k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (T : (Fin k → ℝ) → ChainChart F) (T' : (Fin k → ℝ) → ChainChart F'),
    0 ≤ del → 0 ≤ G → G ≤ Gb → (∀ m, 0 ≤ Ck m) → (∀ m, 0 ≤ Ck' m) → (∀ m, 0 ≤ Cm m) →
    (∀ m, 0 ≤ Dk m) → IsLocalRepresentation S R Y B Ck U Φ → IsLocalRepresentation S' R' Y' B' Ck' U' Φ' →
    AreComparedRepresentations S R Y Y' B Cm U U' Φ Φ' → AreUnitVectors X →
    (∀ b ∈ B, cellSupDist Y b.1 ≤ r₀) → (∀ b ∈ B', cellSupDist Y' b.1 ≤ r₀) →
    ChartEqOnBonds S (T 0) U → ChartEqOnBonds S' (T' 0) U' →
    (∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun ζ => (T ζ).fine b.1 b.2) 0) →
    (∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1), AnalyticAt ℝ (fun ζ => (T ζ).coarse j b.1 b.2) 0) →
    (∀ b ∈ innerBonds S' 0, AnalyticAt ℝ (fun ζ => (T' ζ).fine b.1 b.2) 0) →
    (∀ j, j + 1 < F'.top → ∀ b ∈ innerBonds S' (j + 1), AnalyticAt ℝ (fun ζ => (T' ζ).coarse j b.1 b.2) 0) →
    (∀ (m : ℕ) (e : Fin m ↪ Fin k), 1 ≤ m →
      localNorm S R (mixedDerivativeChart T e) (oneSiteWeights F) Y ≤
        Dk m * Real.exp (-del * bondListDistance Y (c ∘ e))) →
    (∀ (m : ℕ) (e : Fin m ↪ Fin k), 1 ≤ m →
      localNorm S' R' (mixedDerivativeChart T' e) (oneSiteWeights F') Y' ≤
        Dk m * Real.exp (-del * bondListDistance Y' (c' ∘ e))) →
    offsetChartGapNorm S R Y Y Y' U U' ≤ G →
    (∀ (m : ℕ) (e : Fin m ↪ Fin k), 1 ≤ m →
      offsetChartGapNorm S R Y Y Y' (mixedDerivativeChart T e) (mixedDerivativeChart T' e) ≤ G) →
    (∀ l, ∀ b ∈ B, c l = b ↔ c' l = (cellAtSameOffset Y Y' b.1, b.2)) →
    ∀ (m : ℕ) (e : Fin m ↪ Fin k), 1 ≤ m →
      ‖iteratedFDeriv ℝ m (fun ζ : Fin k → ℝ => Φ (T ζ) (bondSpread c X ζ)) 0 (fun l => Pi.single (e l) 1) -
        iteratedFDeriv ℝ m (fun ζ : Fin k → ℝ => Φ' (T' ζ) (bondSpread c' X ζ)) 0
          (fun l => Pi.single (e l) 1)‖ ≤
      comparisonConstant Cm Dk (Real.exp (del * r₀)) Gb m * G
end YangMills.Construction.BlockAverages
end
