import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainIsLeast
import YangMills.Construction.ColdChainAtEveryLevel.CriticalValueIsTheLeastAction
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
theorem relativeEnergy_nonneg_of_nonneg (a : ℝ) (ha : 0 ≤ a) (S : Finset F.Cell) (z : F.Cell)
    (W : F.FieldChain) (gW : F.SiteGauge) (X : F.FieldChain) (g h : F.SiteGauge) :
    0 ≤ relativeEnergy a S z W gW X g h := by
  unfold relativeEnergy
  refine add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (mul_nonneg ha ?_)
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem chartChain_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V F.top = V := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_top <;> assumption
theorem criticalValueEqMinimalAction (hmin : criticalChainMinimalityStatement)
    (hexist : minimalChainExistenceStatement) (hlower : gaugedChainLowerBoundStatement) :
    criticalValueEqMinimalActionStatement := by
  intro a θ δ Ca ha hθ hθ8 hδ hδ8 hCa
  obtain ⟨L₀, h⟩ := hmin a θ δ Ca ha hθ hθ8 hδ hδ8 hCa
  refine ⟨L₀, fun L hL hge C₁ hC₁ => ?_⟩
  obtain ⟨ε₀, σ, C, c, hε₀, hσ, hC, hc, h'⟩ := h L hL hge C₁ hC₁
  refine ⟨σ, hσ, ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold hv U hU
  have hLpos : 0 < F.blockSide := by
    rw [hFL]
    exact hL.pos
  have key : ∀ (X : F.FieldChain) (g : F.SiteGauge), X F.top = rotatedField v V →
      chartAction a S (referenceFieldChain S V) U (rotatedField v V) ≤ gaugedChainAction a S X g := by
    intro X g hX
    obtain ⟨Γ, -, hex⟩ := h' F m S hFL hamb hm hreg s V v hs hsσ hcold hv U hU X g hX
    have h0 : 0 ≤ c * ((highEnergyCells a ε₀ S X g).card + ∑ z ∈ cellsFarFromHighEnergy a ε₀ S X g,
        relativeEnergy a S z (chartChain (referenceFieldChain S V) U (rotatedField v V))
          (chartGauge (referenceFieldChain S V) U) X g (Γ z)) := by
      refine mul_nonneg hc.le (add_nonneg (by positivity) (Finset.sum_nonneg fun z _ => ?_))
      exact relativeEnergy_nonneg_of_nonneg a ha.le S z _ _ X g _
    linarith
  refine ⟨le_antisymm ?_ ?_, key⟩
  · have := (hlower F a S ha.le hLpos).1 (chartChain (referenceFieldChain S V) U (rotatedField v V))
      (chartGauge (referenceFieldChain S V) U)
    rwa [chartChain_top] at this
  · obtain ⟨X, hX, htot⟩ := (hexist F a S ha.le).2.2.2 (rotatedField v V)
    have h1 := key X (fun _ _ => 1) hX.1
    rw [(hlower F a S ha.le hLpos).2 X, htot] at h1
    exact h1
end YangMills.Construction.BlockAverages
end
