import YangMills.Construction.Towers.CoefficientsOfTheResolventAsSumsOverBonds
import YangMills.Construction.Towers.DecayOfTheSecondDerivativesOfTheLogarithmicDensityProof
import YangMills.Construction.Towers.DifferenceOfTheLogarithmicDensitiesAsAnIntegral
import YangMills.Construction.Towers.ExpansionOfTheLogarithmicDensity
import YangMills.Construction.Towers.ResolventAlongAFieldToTheSecondOrder
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
namespace YangMills.Construction
open OperatorCalculus Tower.AbelianFieldDensity OneLoopNotation
namespace Tower.LocalFamilies
namespace LogTraceExpansionLemmas
private lemma integral_inv_add_sq {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun w : ℝ => (z / 4 + w)⁻¹ ^ 2) (Ioi 0) ∧
      ∫ w in Ioi (0 : ℝ), (z / 4 + w)⁻¹ ^ 2 = 4 / z := by apply _root_.YangMills.Construction.Tower.LocalFamilies.HessianDecay.integral_inv_sq_Ioi <;> assumption
private lemma integral_tsum_of_dominated {N : Type} [Countable N] (F : N → ℝ → ℂ) (g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioi 0)) (hF : ∀ n, IntegrableOn (F n) (Ioi 0))
    (hS : ∀ w : ℝ, 0 ≤ w → Summable (fun n => ‖F n w‖))
    (hB : ∀ w : ℝ, 0 ≤ w → ∑' n, ‖F n w‖ ≤ g w) :
    IntegrableOn (fun w => ∑' n, F n w) (Ioi 0) ∧
      HasSum (fun n => ∫ w in Ioi (0 : ℝ), F n w) (∫ w in Ioi (0 : ℝ), ∑' n, F n w) := by
  have hae : ∀ᵐ w ∂(volume.restrict (Ioi (0 : ℝ))),
      Summable (fun n => ‖F n w‖) ∧ ∑' n, ‖F n w‖ ≤ g w := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w hw => ?_)
    exact ⟨hS w (le_of_lt hw), hB w (le_of_lt hw)⟩
  have hlint : ∑' n, ∫⁻ w in Ioi (0 : ℝ), ‖F n w‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun n => (hF n).aestronglyMeasurable.aemeasurable.enorm]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae ?_) (Integrable.lintegral_lt_top hg))
    filter_upwards [hae] with w hw
    have h0 : ∀ n, 0 ≤ ‖F n w‖ := fun n => norm_nonneg _
    calc ∑' n, ‖F n w‖ₑ = ∑' n, ENNReal.ofReal ‖F n w‖ := by simp only [ofReal_norm]
      _ = ENNReal.ofReal (∑' n, ‖F n w‖) := (ENNReal.ofReal_tsum_of_nonneg h0 hw.1).symm
      _ ≤ ENNReal.ofReal (g w) := ENNReal.ofReal_le_ofReal hw.2
  have hsum : Summable fun n => ∫ w in Ioi (0 : ℝ), ‖F n w‖ := by
    have h := ENNReal.summable_toReal hlint
    refine h.congr fun n => ?_
    rw [integral_norm_eq_lintegral_enorm (hF n).aestronglyMeasurable]
  refine ⟨?_, hasSum_integral_of_summable_integral_norm (fun n => hF n) hsum⟩
  have hmeas : AEStronglyMeasurable (fun w => ∑' n, F n w) (volume.restrict (Ioi (0 : ℝ))) := by
    refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset N))
      (f := fun s w => ∑ n ∈ s, F n w)
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun n _ => (hF n).aestronglyMeasurable) ?_
    filter_upwards [hae] with w hw
    exact (hw.1.of_norm).hasSum
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [hae] with w hw
  exact (norm_tsum_le_tsum_norm hw.1).trans hw.2
private lemma countable_of_integerPlacement {B : Type} {src : B → InfiniteLattice.AmbientSpace} {m : ℕ}
    (h : IsIntegerPlacement src m) : Countable B := by
  have hu : (Set.univ : Set B) ⊆ ⋃ n : Fin 4 → ℤ, {b | src b = PeriodicOperators.castVec n} := by
    intro b _
    obtain ⟨n, hn⟩ := h.on_lattice b
    exact mem_iUnion.2 ⟨n, hn⟩
  have hc : (Set.univ : Set B).Countable :=
    (countable_iUnion fun n => (h.fibre_bounded _).1.countable).mono hu
  exact Set.countable_univ_iff.1 hc
end LogTraceExpansionLemmas
open LogTraceExpansionLemmas in
theorem logTraceQuadraticExpansion_holds
    (hHess : LogTraceSecondDerivative.IntegralFormula)
    (hRes : ResolventSecondOrderExpansion)
    (hCoef : ResolventCoeffSums.BondSumExpansion)
    (hInt : LogTraceDiffIntegral) :
    LogTraceQuadraticExpansion := by
  intro z C m m' hz hC
  obtain ⟨M, hM0, hM⟩ := hRes z C m m' hz hC
  obtain ⟨M', hM'0, hM'⟩ := hCoef z C m m' hz hC
  refine ⟨M * (4 / z), ?_⟩
  intro J B pos src T hset ξ hξ f₀ hf₀ hf₁ hlow
  have : Countable B := countable_of_integerPlacement hset.edges
  obtain ⟨hgi, hgv⟩ := integral_inv_add_sq hz
  have hcoef := hM' J B pos src T hset ξ hξ
  have hint := hInt J B pos src m m' z C T hz hC hset
  have hzero : PeriodicOperators.castVec (0 : Fin 4 → ℤ) = 0 := by
    funext μ
    simp [PeriodicOperators.castVec]
  set F₁ : B → ℝ → ℂ := fun b w => (ξ b : ℂ) * traceAt pos
    ((baseResolvent T z w).comp ((firstVar T b).comp (baseResolvent T z w))) 0 with hF₁
  have hF₁i : ∀ b, IntegrableOn (F₁ b) (Ioi 0) := fun b =>
    (hint.2 (firstVar T b)).const_mul _
  obtain ⟨hAi, hAs⟩ := integral_tsum_of_dominated F₁ (fun w => M' * (z / 4 + w)⁻¹ ^ 2)
    (hgi.const_mul M') hF₁i (fun w hw => (hcoef w hw).1.1) (fun w hw => (hcoef w hw).1.2.1)
  set F₂ : B × B → ℝ → ℂ := fun p w => (ξ p.1 : ℂ) * (ξ p.2 : ℂ) *
    traceAt pos (secondOrderResolvent T z p.1 p.2 w) 0 with hF₂
  have hhess : ∀ p : B × B,
      IntegrableOn (fun w => traceAt pos (secondOrderResolvent T z p.1 p.2 w) 0) (Ioi 0) ∧
      logTraceHessian pos T z 0 p.1 p.2 =
        ∫ w in Ioi (0 : ℝ), traceAt pos (secondOrderResolvent T z p.1 p.2 w) 0 := by
    intro p
    have h := hHess J B pos src m m' z C T hz hC hset 0 p.1 p.2
    rw [hzero] at h
    exact h.2
  have hF₂i : ∀ p, IntegrableOn (F₂ p) (Ioi 0) := fun p => (hhess p).1.const_mul _
  obtain ⟨hBi, hBs⟩ := integral_tsum_of_dominated F₂ (fun w => M' * (z / 4 + w)⁻¹ ^ 2)
    (hgi.const_mul M') hF₂i (fun w hw => (hcoef w hw).2.1) (fun w hw => (hcoef w hw).2.2.1)
  have hBs' : HasSum
      (fun p : B × B => logTraceHessian pos T z 0 p.1 p.2 * (ξ p.1 : ℂ) * (ξ p.2 : ℂ))
      (∫ w in Ioi (0 : ℝ), ∑' p, F₂ p w) := by
    have heq : (fun p : B × B =>
        logTraceHessian pos T z 0 p.1 p.2 * (ξ p.1 : ℂ) * (ξ p.2 : ℂ)) =
        fun p => ∫ w in Ioi (0 : ℝ), F₂ p w := by
      funext p
      simp only [hF₂]
      rw [integral_const_mul, ← (hhess p).2]
      ring
    rw [heq]
    exact hBs
  refine ⟨hBs'.summable, ∫ w in Ioi (0 : ℝ), ∑' b, F₁ b w, fun f hf => ?_⟩
  rw [hBs'.tsum_eq]
  have hf1 : |f| ≤ 1 := hf.trans hf₁
  have hlowf := hlow f hf
  obtain ⟨hDi, hDv⟩ := hint.1 (fun b => f * ξ b) hlowf
  rw [hDv]
  set D : ℝ → ℂ := fun w => traceAt pos (baseResolvent T z w) 0 -
    traceAt pos (inverseOp (addScalar (addScalar (T fun b => f * ξ b) z) w)) 0
    with hD
  have hcomb : (∫ w in Ioi (0 : ℝ), D w) - (∫ w in Ioi (0 : ℝ), ∑' b, F₁ b w) * (f : ℂ) -
      ((1 / 2 * f ^ 2 : ℝ) : ℂ) * ∫ w in Ioi (0 : ℝ), ∑' p, F₂ p w =
      ∫ w in Ioi (0 : ℝ), (D w - (f : ℂ) * ∑' b, F₁ b w -
        ((1 / 2 * f ^ 2 : ℝ) : ℂ) * ∑' p, F₂ p w) := by
    have h1 : IntegrableOn (fun w => (f : ℂ) * ∑' b, F₁ b w) (Ioi 0) := hAi.const_mul _
    have h2 : IntegrableOn (fun w => ((1 / 2 * f ^ 2 : ℝ) : ℂ) * ∑' p, F₂ p w) (Ioi 0) :=
      hBi.const_mul _
    have e1 := integral_sub (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun w => D w - (f : ℂ) * ∑' b, F₁ b w)
      (g := fun w => ((1 / 2 * f ^ 2 : ℝ) : ℂ) * ∑' p, F₂ p w) (hDi.sub h1) h2
    have e2 := integral_sub (μ := volume.restrict (Ioi (0 : ℝ))) (f := D)
      (g := fun w => (f : ℂ) * ∑' b, F₁ b w) hDi h1
    rw [e1, e2, integral_const_mul, integral_const_mul]
    ring
  rw [hcomb]
  have hbound : ∀ w ∈ Ioi (0 : ℝ), ‖D w - (f : ℂ) * ∑' b, F₁ b w -
      ((1 / 2 * f ^ 2 : ℝ) : ℂ) * ∑' p, F₂ p w‖ ≤ M * |f| ^ 3 * (z / 4 + w)⁻¹ ^ 2 := by
    intro w hw
    have hw0 : (0 : ℝ) ≤ w := le_of_lt hw
    have h := hM J B pos src T hset ξ hξ f hf1 hlowf w hw0
    have hc := hcoef w hw0
    rw [hc.1.2.2, hc.2.2.2] at h
    exact h
  calc ‖∫ w in Ioi (0 : ℝ), (D w - (f : ℂ) * ∑' b, F₁ b w -
        ((1 / 2 * f ^ 2 : ℝ) : ℂ) * ∑' p, F₂ p w)‖
      ≤ ∫ w in Ioi (0 : ℝ), M * |f| ^ 3 * (z / 4 + w)⁻¹ ^ 2 :=
        norm_integral_le_of_norm_le (hgi.const_mul _)
          ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hbound))
    _ = M * (4 / z) * |f| ^ 3 := by
        rw [integral_const_mul, hgv]
        ring
end Tower.LocalFamilies
end YangMills.Construction
end
