import YangMills.Construction.ColdChainAtEveryLevel.ChainsOfRotatedTopsForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TwistedTops GaugeMap
namespace BlockAverages
def twistedTopLocalBoundsStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ R C₁ : ℝ, 0 < R → 0 < C₁ → ∃ s₂ C₂ : ℝ, 0 < s₂ ∧ 0 < C₂ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
          IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ s₂ →
          IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) → ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ R →
            (∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) (rotatedField v V) U A) →
            (∃ Ulin Urest : ChainChart F, ChartEqOnBonds S U (chartSum Ulin Urest) ∧
              ∀ (p : F.Site 0) (y₀ : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
                weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F δ θ' p y₀) ≤ Ca * s ∧
                weightedNorm S (referenceFieldChain S V) Urest (decayWeights F δ θ' p y₀) ≤ C₁ * s ^ 2) →
            HasTopLocalBounds θ C₂ s S V (rotatedField v V) U
end BlockAverages
end YangMills.Construction
end
