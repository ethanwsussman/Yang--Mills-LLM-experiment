import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def rotatedTopQuadraticForm (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : ℝ :=
  ∑ q ∈ plaquettesOver S S 0, ‖linearizedCurl (R 0) A.fine q‖ ^ 2 +
    a * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2 +
    a * ∑ c ∈ bondsOver S S F.top, ‖linearPart R A F.top c.1 c.2 - (v c.1 c.2 : ℍ[ℝ])‖ ^ 2
def rotatedTopActionStatement : Prop :=
  ∀ a δ : ℝ, 0 < a → 0 < δ → δ ≤ 1 / 8 → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ v : F.Site F.top → Fin 4 → imaginaryQuaternions, (∀ b, b ∉ innerBonds S F.top → v b.1 b.2 = 0) →
          (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (e₀ : E) (Q : E → ChainChart F),
            supWeightedNorm S δ (referenceFieldChain S V) (Q e₀) ≤ c →
            (∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun e => (Q e).fine b.1 b.2) e₀) →
            (∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1), AnalyticAt ℝ (fun e => (Q e).coarse j b.1 b.2) e₀) →
            AnalyticAt ℝ (fun x : E × ℝ => chartAction a S (referenceFieldChain S V) (Q x.1)
              (rotatedField (fun y i => x.2 • v y i) V)) (e₀, 0)) ∧
          ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
            (∀ A : ChainChart F,
              |deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ)
                  (rotatedField (fun y i => τ • v y i) V)) 0 -
                  rotatedTopQuadraticForm a S (referenceFieldChain S V) A v| ≤
                C * (s + supWeightedNorm S δ (referenceFieldChain S V) U) *
                  (weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2 +
                    ∑ b ∈ innerBonds S F.top, ‖v b.1 b.2‖ ^ 2)) ∧
            |deriv (fun τ : ℝ => chartAction a S (referenceFieldChain S V) U
                (rotatedField (fun y i => τ • v y i) V)) 0| ≤
              a * ∑ c ∈ innerBonds S F.top,
                normSubOne (chartBondMisfit (referenceFieldChain S V) U V F.depth c) * ‖v c.1 c.2‖
end YangMills.Construction.BlockAverages
end
