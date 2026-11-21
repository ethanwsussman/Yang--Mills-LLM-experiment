import YangMills.Construction.ColdChainAtEveryLevel.ChainsOfRotatedTopsForm
import YangMills.Construction.ColdChainAtEveryLevel.ComplexCriticalFamilies
import YangMills.Construction.ColdChainAtEveryLevel.CriticalPointOnTheSlice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TwistedTops GaugeMap
namespace BlockAverages
def coldTopTwistedChainsStatement : Prop :=
  ∀ a θ δ K : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < K →
    ReferenceFormWeightedEstimateHolds a θ δ K → ∃ Ca : ℝ, 0 < Ca ∧
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ R : ℝ, 0 < R → R ≤ c₀ →
      ∃ (R' sL CL : ℝ) (Ck : ℕ → ℝ), 0 < R' ∧ R' ≤ R ∧ 0 < sL ∧ 0 < CL ∧ (∀ k, 0 < Ck k) ∧
        ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
            IsOrthantRegular S m →
          ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ sL → IsCold S F.top s V →
            ∃ U : ChainChart F, IsSliceCriticalPoint a θ δ Ca R CL s S V U ∧
              ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
                AreUnitVectors X →
                ∃ T : (Fin k → ℝ) → ChainChart F, IsTwistedCriticalChain a θ δ Ca R R' CL s Ck S V c X U T
end BlockAverages
end YangMills.Construction
end
