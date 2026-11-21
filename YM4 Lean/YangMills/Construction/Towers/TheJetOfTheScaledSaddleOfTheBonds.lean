import YangMills.Construction.PeriodicOperators.JetsOnADisjointSumAndOnTheUnionOfAPair
import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad (EqAsJet)
open RemainderJets
def rescaledEdgeSaddle (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (vectorIndices L k).Carrier → (vectorIndices L k).Carrier → ℂ :=
  fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).saddleX
def RescaledEdgeSaddleJet : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    IsLocalOpFun (remainderIndex L k)
        (PeriodicData.sigma (pairData (colourEdges L k 0) (colourEdges L k k)))
        (PeriodicData.sigma (pairData (colourEdges L k 0) (colourEdges L k k)))
        (readOnSigma (rescaledEdgeSaddle L k)) ∧
      ∀ (δ : ℝ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4), 0 < δ → p ∈ imStrip δ →
        EqAsJet δ p (jetAlongResponse L k (readOnSigma (rescaledEdgeSaddle L k)) p μPlus μMinus)
          (saddleJet p (subGramJet p (edgeMiddleJet L k p μPlus μMinus)
            (edgeSmoothingJet L k p μPlus μMinus)) (edgeSmoothingJet L k p μPlus μMinus))
end YangMills.Construction.Tower.FullSpace.BackgroundJets
end
