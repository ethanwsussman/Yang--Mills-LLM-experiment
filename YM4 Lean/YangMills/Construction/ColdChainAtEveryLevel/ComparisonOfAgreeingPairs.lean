import YangMills.Construction.ColdChainAtEveryLevel.ChainsOfRotatedTopsForm
import YangMills.Construction.ColdChainAtEveryLevel.ComplexCriticalFamilies
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TwistedTops GaugeMap
namespace BlockAverages
structure IsSmallSliceCriticalPoint {F : BlockFrame} (a δ R : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (U : ChainChart F) : Prop where
  mem_slice : InGaugeSlice S V (referenceFieldChain S V 0) U.fine
  norm_le : supWeightedNorm S δ (referenceFieldChain S V) U ≤ R
  critical : ∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) V U A
def agreeingPairsComparisonStatement : Prop :=
  ∀ a θ δ K : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < K →
    ReferenceFormWeightedEstimateHolds a θ δ K →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ R : ℝ, 0 < R → R ≤ c₀ →
      ∃ (s₀ C : ℝ) (Ck : ℕ → ℝ), 0 < s₀ ∧ 0 < C ∧ (∀ k, 0 < Ck k) ∧
        ∀ (F F' : BlockFrame) (m : ℕ) (S : Finset F.Cell) (S' : Finset F'.Cell),
          F.blockSide = L → F'.blockSide = L → F'.depth = F.depth →
          IsAdmissibleAmbient F → IsAdmissibleAmbient F' → 1024 ≤ m → IsOrthantRegular S m → IsOrthantRegular S' m →
          ∀ (s : ℝ) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
            0 < s → s ≤ s₀ → IsCold S F.top s V → IsCold S' F'.top s V' → 108 ≤ r → AgreeOnBall S V S' V' Y Y' r →
            ∀ (U : ChainChart F) (U' : ChainChart F'),
              IsSmallSliceCriticalPoint a δ R S V U → IsSmallSliceCriticalPoint a δ R S' V' U' →
              (∀ z : F.Cell, cellSupDist z Y ≤ 3 →
                localNorm S (referenceFieldChain S V) (chartMove U (chartTranslate Y Y' U') (-1)) (oneSiteWeights F) z ≤
                  C * s * Real.exp (-δ * r / 4)) ∧
              ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions) (ρ : ℝ), 1 ≤ k → 0 < ρ →
                (∀ l, BondWithinRadius (r / 2) (h l)) → AreUnitVectors X →
                ∀ (T : (Fin k → ℝ) → ChainChart F) (T' : (Fin k → ℝ) → ChainChart F'),
                  IsTwistedCriticalFamily a δ R ρ S V (offsetBonds Y h) X T →
                  IsTwistedCriticalFamily a δ R ρ S' V' (offsetBonds Y' h) X T' →
                  ∀ (j : ℕ) (e : Fin j ↪ Fin k) (z : F.Cell), 1 ≤ j → cellSupDist z Y ≤ 3 →
                    localNorm S (referenceFieldChain S V)
                        (chartMove (chartMixedDeriv T e) (chartTranslate Y Y' (chartMixedDeriv T' e)) (-1))
                        (oneSiteWeights F) z ≤
                      Ck j * Real.exp (-δ * r / 4)
end BlockAverages
end YangMills.Construction
end
