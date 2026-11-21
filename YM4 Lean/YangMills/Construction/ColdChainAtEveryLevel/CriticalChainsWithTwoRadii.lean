import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfASplitCriticalPoint
import YangMills.Construction.ColdChainAtEveryLevel.ChainsOfRotatedTopsForm
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TwistedTops GaugeMap
namespace BlockAverages
def criticalChainsTwoRadiiStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ θ δ Ca : ℝ, 0 < θ ∧ θ ≤ 1 / 8 ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 < Ca ∧
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (R R' sL CL : ℝ) (Ck : ℕ → ℝ),
      0 < R ∧ 0 < R' ∧ R' ≤ R ∧ 0 < sL ∧ 0 < CL ∧ (∀ k, 0 < Ck k) ∧
      (∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
          IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ sL → IsCold S F.top s V →
          ∃ U : ChainChart F, IsSliceCriticalPoint a θ δ Ca R CL s S V U ∧
            SliceCriticalPointLocalBounds a θ CL s S V U ∧
            ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X →
              ∃ T : (Fin k → ℝ) → ChainChart F, IsTwistedCriticalChain a θ δ Ca R R' CL s Ck S V c X U T) ∧
      ∀ (F F' : BlockFrame) (m : ℕ) (S : Finset F.Cell) (S' : Finset F'.Cell),
        F.blockSide = L → F'.blockSide = L → F'.depth = F.depth →
        IsAdmissibleAmbient F → IsAdmissibleAmbient F' → 1024 ≤ m → IsOrthantRegular S m → IsOrthantRegular S' m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
          0 < s → s ≤ sL → IsCold S F.top s V → IsCold S' F'.top s V' → 108 ≤ r → AgreeOnBall S V S' V' Y Y' r →
          ∀ (U : ChainChart F) (U' : ChainChart F'),
            IsSliceCriticalPoint a θ δ Ca R CL s S V U →
            IsSliceCriticalPoint a θ δ Ca R CL s S' V' U' →
            (∀ z : F.Cell, cellSupDist z Y ≤ 3 →
              localNorm S (referenceFieldChain S V) (chartMove U (chartTranslate Y Y' U') (-1)) (oneSiteWeights F) z ≤
                CL * s * Real.exp (-δ * r / 4)) ∧
            ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
              (∀ l, BondWithinRadius (r / 2) (h l)) → AreUnitVectors X →
              ∀ (T : (Fin k → ℝ) → ChainChart F) (T' : (Fin k → ℝ) → ChainChart F'),
                IsTwistedCriticalChain a θ δ Ca R R' CL s Ck S V (offsetBonds Y h) X U T →
                IsTwistedCriticalChain a θ δ Ca R R' CL s Ck S' V' (offsetBonds Y' h) X U' T' →
                ∀ (j : ℕ) (e : Fin j ↪ Fin k) (z : F.Cell), 1 ≤ j → cellSupDist z Y ≤ 3 →
                  localNorm S (referenceFieldChain S V)
                      (chartMove (chartMixedDeriv T e) (chartTranslate Y Y' (chartMixedDeriv T' e)) (-1))
                      (oneSiteWeights F) z ≤
                    Ck j * Real.exp (-δ * r / 4)
end BlockAverages
end YangMills.Construction
end
