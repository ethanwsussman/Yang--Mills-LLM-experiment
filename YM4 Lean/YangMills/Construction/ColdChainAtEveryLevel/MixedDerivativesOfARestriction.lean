import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ColdChainAtEveryLevel.LocalRestrictionsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def mixedDerivConstant (Ck Dk : ℕ → ℝ) (M : ℝ) (m : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition m, Ck c.length * ∏ i, (Dk (c.partSize i) + M)
def partEmbedding {k m : ℕ} (e : Fin m ↪ Fin k) (cP : OrderedFinpartition m) (i : Fin cP.length) :
    Fin (cP.partSize i) ↪ Fin k :=
  ⟨fun l => e (cP.emb i l), e.injective.comp (cP.emb_strictMono i).injective⟩
def partSpread {F : BlockFrame} {k p : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (e : Fin p ↪ Fin k) : F.Site F.top → Fin 4 → imaginaryQuaternions :=
  bondSpread c X (iteratedFDeriv ℝ p (fun ζ : Fin k → ℝ => ζ) 0 fun l => Pi.single (e l) 1)
def localMixedDerivStatement : Prop :=
  ∀ (F : BlockFrame) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (S : Finset F.Cell)
    (R : F.FieldChain) (z : F.Cell) (B : Finset (F.Site F.top × Fin 4)) (Ck Dk : ℕ → ℝ) (U : ChainChart F)
    (Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E) (δ : ℝ) (r₀ k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (T : (Fin k → ℝ) → ChainChart F),
    0 ≤ δ → (∀ m, 0 ≤ Ck m) → (∀ m, 0 ≤ Dk m) → IsLocalRepresentation S R z B Ck U Φ → AreUnitVectors X →
    (∀ b ∈ B, cellSupDist z b.1 ≤ r₀) → ChartEqOnBonds S (T 0) U →
    (∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun ζ => (T ζ).fine b.1 b.2) 0) →
    (∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1), AnalyticAt ℝ (fun ζ => (T ζ).coarse j b.1 b.2) 0) →
    (∀ (m : ℕ) (e : Fin m ↪ Fin k), 1 ≤ m →
      localNorm S R (mixedDerivativeChart T e) (oneSiteWeights F) z ≤
        Dk m * Real.exp (-δ * bondListDistance z (c ∘ e))) →
    AnalyticAt ℝ (fun ζ : Fin k → ℝ => Φ (T ζ) (bondSpread c X ζ)) 0 ∧
    (∀ (m : ℕ) (e : Fin m ↪ Fin k), 1 ≤ m →
      ∃ A : (cP : OrderedFinpartition m) → Fin cP.length → ChainChart F,
        (∀ cP i, ChartEqOnBonds S (A cP i) (mixedDerivativeChart T (partEmbedding e cP i))) ∧
        iteratedFDeriv ℝ m (fun ζ : Fin k → ℝ => Φ (T ζ) (bondSpread c X ζ)) 0 (fun l => Pi.single (e l) 1) =
          ∑ cP : OrderedFinpartition m,
            localIteratedDeriv Φ U (A cP) fun i => partSpread c X (partEmbedding e cP i)) ∧
    ∀ (m : ℕ) (e : Fin m ↪ Fin k), 1 ≤ m →
      ‖iteratedFDeriv ℝ m (fun ζ : Fin k → ℝ => Φ (T ζ) (bondSpread c X ζ)) 0 (fun l => Pi.single (e l) 1)‖ ≤
        mixedDerivConstant Ck Dk (Real.exp (δ * r₀)) m * Real.exp (-δ * bondListDistance z (c ∘ e))
end YangMills.Construction.BlockAverages
end
