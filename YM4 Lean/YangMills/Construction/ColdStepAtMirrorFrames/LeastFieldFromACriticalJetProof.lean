import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import YangMills.Construction.ColdStepAtMirrorFrames.ChartFieldIsLeastAtACriticalPoint
import YangMills.Construction.ColdStepAtMirrorFrames.LeastFieldFromACriticalJet
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem minimalOfCriticalJet_holds (hCrit : ChartCriticalPointIsMinimal)
    (hLog : ConjugatedExpLogSmooth) (hMin : minimalChainExistenceStatement) :
    MinimalOfCriticalJet := by
  classical
  intro F a lam ρ σ S V u₀ u₁ ha hlam hAll hFloor hz₀ hz₁ hSeg hFits hJet
  refine hCrit F a lam ρ σ S V u₀ u₁ hlam hFloor hz₀ hz₁ hSeg ?_
  obtain ⟨Θ, U, C, hU, _, hDiag, hΘ, hExp, hΘzero, _⟩ := hLog
  set B := innerBonds S F.depth with hB
  set G₀ := chartedField u₀ V with hG₀
  set δ : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun x i => u₁ x i - u₀ x i with hδ
  set J := formComposition B (minimalAction a S F.depth) G₀ with hJ
  let curve : ↥B → ℝ → imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
    fun b s => (u₀ b.1.1 b.1.2 + s • δ b.1.1 b.1.2, 0, u₀ b.1.1 b.1.2)
  let X : ℝ → ↥B → imaginaryQuaternions := fun s b => Θ (curve b s)
  have hCurveZero : ∀ b, curve b 0 = diagonalTriple (u₀ b.1.1 b.1.2) := by
    intro b
    simp [curve, diagonalTriple]
  have hCurveDeriv : ∀ b, HasDerivAt (curve b)
      (δ b.1.1 b.1.2, (0 : imaginaryQuaternions), (0 : imaginaryQuaternions)) 0 := by
    intro b
    have hFirst : HasDerivAt (fun s : ℝ => u₀ b.1.1 b.1.2 + s • δ b.1.1 b.1.2) (δ b.1.1 b.1.2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (δ b.1.1 b.1.2)).const_add (u₀ b.1.1 b.1.2)
    exact hFirst.prodMk ((hasDerivAt_const (0 : ℝ) (0 : imaginaryQuaternions)).prodMk
      (hasDerivAt_const (0 : ℝ) (u₀ b.1.1 b.1.2)))
  have hXzero : X 0 = 0 := by
    funext b
    show Θ (curve b 0) = 0
    rw [hCurveZero, hΘzero]
  have hXderiv : HasDerivAt X (fun b => fderiv ℝ Θ (curve b 0)
      (δ b.1.1 b.1.2, (0 : imaginaryQuaternions), (0 : imaginaryQuaternions))) 0 := by
    rw [hasDerivAt_pi]
    intro b
    have hAt : ContDiffAt ℝ 3 Θ (curve b 0) := by
      apply hΘ.contDiffAt
      rw [hCurveZero]
      exact hU.mem_nhds (hDiag _)
    have hF : HasFDerivAt Θ (fderiv ℝ Θ (curve b 0)) (curve b 0) :=
      (hAt.differentiableAt (by norm_num)).hasFDerivAt
    exact hF.comp_hasDerivAt (0 : ℝ) (hCurveDeriv b)
  have hJX : HasDerivAt (fun s => J (X s)) 0 0 := by
    have hJ' : HasFDerivAt J (0 : (↥B → imaginaryQuaternions) →L[ℝ] ℝ) (X 0) := by
      rw [hXzero]; exact hJet
    have h := hJ'.comp_hasDerivAt (0 : ℝ) hXderiv
    simp only [ContinuousLinearMap.zero_apply] at h
    exact h
  have hNear : ∀ᶠ s : ℝ in 𝓝 0, ∀ b : ↥B, curve b s ∈ U := by
    rw [eventually_all]
    intro b
    have hc : ContinuousAt (curve b) 0 := (hCurveDeriv b).continuousAt
    apply hc.eventually_mem
    rw [hCurveZero]
    exact hU.mem_nhds (hDiag _)
  have hChart : ∀ s : ℝ, (∀ b : ↥B, curve b s ∈ U) →
      chartedField (fun x i => u₀ x i + s • δ x i) V = leftTranslate (extendByZero (X s)) G₀ := by
    intro s hs
    funext x i
    have hxi : (x, i) ∈ B := hAll _
    have hθ := hExp _ (hs ⟨(x, i), hxi⟩)
    have hStep : expUnit (u₀ x i + s • δ x i) = expUnit (X s ⟨(x, i), hxi⟩) * expUnit (u₀ x i) := by
      show _ = expUnit (Θ (curve ⟨(x, i), hxi⟩ s)) * _
      rw [hθ]
      simp [curve, expUnit_zero]
    unfold leftTranslate extendByZero
    rw [dif_pos hxi, hG₀]
    unfold chartedField
    by_cases hc : IsCrossingBond (x, i)
    · rw [if_pos hc, if_pos hc, hStep, mul_assoc]
    · rw [if_neg hc, if_neg hc]
      by_cases ht : IsAxialTreeBond (x, i)
      · rw [if_pos ht, if_pos ht]
        have hNot : (x, i) ∉ chordBonds S := by
          unfold chordBonds
          rw [Finset.mem_filter]
          exact fun h => h.2 ht
        have e₀ := hz₀ _ hNot
        have e₁ := hz₁ _ hNot
        have hX0 : X s ⟨(x, i), hxi⟩ = 0 := by
          show Θ (curve ⟨(x, i), hxi⟩ s) = 0
          have : curve ⟨(x, i), hxi⟩ s = diagonalTriple 0 := by
            simp only [curve, diagonalTriple, hδ]
            dsimp only at e₀ e₁
            rw [e₀, e₁]
            simp
          rw [this, hΘzero]
        rw [hX0, expUnit_zero, mul_one]
      · rw [if_neg ht, if_neg ht, hStep]
  intro ε hε
  have hLittle := (hasDerivAt_iff_isLittleO_nhds_zero.1 hJX)
  have hBound := hLittle.def (c := ε) hε
  have hBoth := hBound.and hNear
  rw [Metric.eventually_nhds_iff] at hBoth
  obtain ⟨r, hr, hBall⟩ := hBoth
  refine ⟨r, hr, fun s hs0 hsr => ?_⟩
  have hDist : dist s 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
    exact hsr
  obtain ⟨hb₁, hb₂⟩ := hBall hDist
  simp only [zero_add, smul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hs0] at hb₁
  have hb₃ : - (ε * s) ≤ J (X s) - J (X 0) := by
    have := (abs_le.1 hb₁).1
    simpa [zero_add] using this
  have hAtZero : chartEnergyOnSegment a S V u₀ δ 0 = J (X 0) := by
    rw [hXzero]
    have e₁ : J 0 = minimalAction a S F.depth G₀ := by
      show minimalAction a S F.depth (leftTranslate (extendByZero (0 : ↥B → imaginaryQuaternions)) G₀) = _
      congr 1
      funext x i
      unfold leftTranslate extendByZero
      rw [dif_pos (hAll (x, i))]
      show expUnit (0 : imaginaryQuaternions) * _ = _
      rw [expUnit_zero, one_mul]
    rw [e₁]
    unfold chartEnergyOnSegment blockEnergy
    simp only [zero_smul, add_zero]
    have : (fun x i => u₀ x i) = u₀ := rfl
    rw [this, ← hG₀, Finset.sum_eq_zero (fun c hc => hFits c hc), mul_zero, add_zero]
  have hAtS : J (X s) ≤ chartEnergyOnSegment a S V u₀ δ s := by
    unfold chartEnergyOnSegment blockEnergy
    rw [hChart s hb₂]
    show minimalAction a S F.depth (leftTranslate (extendByZero (X s)) G₀) ≤ _
    have hFitNonneg : 0 ≤ a * ∑ c ∈ innerBonds S (F.depth + 1),
        blockFit (leftTranslate (extendByZero (X s)) G₀) V c :=
      mul_nonneg ha (Finset.sum_nonneg fun c _ => (hMin F a S ha).1 _ _ _ c)
    linarith
  rw [hAtZero]
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
