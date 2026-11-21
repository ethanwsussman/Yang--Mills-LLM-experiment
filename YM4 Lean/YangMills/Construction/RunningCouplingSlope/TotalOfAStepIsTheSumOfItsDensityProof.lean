import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParametersProof
import YangMills.Construction.RunningCouplingSlope.HessianOfAStepIsPositive
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsTheSumOfItsDensity
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.RunningCouplingSlope
section Resolvent
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem trace_resolvent_eq_sum_eigenvalues {H : Matrix ι ι ℝ} (hH : H.PosDef) {lam : ℝ} (hl : 0 < lam) :
    ∃ μ : ι → ℝ, (∀ i, 0 < μ i) ∧ H.det = ∏ i, μ i ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      IsUnit (τ • H + (1 - τ) • lam • (1 : Matrix ι ι ℝ)).det ∧
      Matrix.trace ((H - lam • (1 : Matrix ι ι ℝ)) * (τ • H + (1 - τ) • lam • (1 : Matrix ι ι ℝ))⁻¹) =
        ∑ i, (μ i - lam) / (τ * μ i + (1 - τ) * lam) := by
  classical
  set μ : ι → ℝ := hH.1.eigenvalues with hμ
  have hpos : ∀ i, 0 < μ i := fun i => hH.eigenvalues_pos i
  set U : Matrix ι ι ℝ := (hH.1.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self hH.1.eigenvectorUnitary
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self hH.1.eigenvectorUnitary
  have hspec : H = U * Matrix.diagonal μ * star U := by
    have h := hH.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Function.comp_def, hμ, hUdef] using h
  have hdet : H.det = ∏ i, μ i := by
    have := hH.1.det_eq_prod_eigenvalues
    simpa using this
  refine ⟨μ, hpos, hdet, fun τ hτ => ?_⟩
  have hd : ∀ i, 0 < τ * μ i + (1 - τ) * lam := fun i => by
    rcases eq_or_lt_of_le hτ.1 with h0 | h0
    · rw [← h0]
      simpa using hl
    · have h1 := mul_pos h0 (hpos i)
      have h2 : 0 ≤ (1 - τ) * lam := mul_nonneg (by linarith [hτ.2]) hl.le
      linarith
  have hone : (1 : Matrix ι ι ℝ) = U * Matrix.diagonal (fun _ => (1 : ℝ)) * star U := by
    rw [Matrix.diagonal_one, Matrix.mul_one, hU2]
  have hM : τ • H + (1 - τ) • lam • (1 : Matrix ι ι ℝ) =
      U * Matrix.diagonal (fun i => τ * μ i + (1 - τ) * lam) * star U := by
    have e : Matrix.diagonal (fun i => τ * μ i + (1 - τ) * lam) =
        τ • Matrix.diagonal μ + ((1 - τ) * lam) • Matrix.diagonal (fun _ => (1 : ℝ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, ← hspec,
      ← hone, smul_smul]
  have hD : H - lam • (1 : Matrix ι ι ℝ) = U * Matrix.diagonal (fun i => μ i - lam) * star U := by
    have e : Matrix.diagonal (fun i => μ i - lam) = Matrix.diagonal μ - lam • Matrix.diagonal (fun _ => (1 : ℝ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← hspec, ← hone]
  set R : Matrix ι ι ℝ := U * Matrix.diagonal (fun i => (τ * μ i + (1 - τ) * lam)⁻¹) * star U with hR
  have hMR : (τ • H + (1 - τ) • lam • (1 : Matrix ι ι ℝ)) * R = 1 := by
    rw [hM, hR]
    calc U * Matrix.diagonal (fun i => τ * μ i + (1 - τ) * lam) * star U *
          (U * Matrix.diagonal (fun i => (τ * μ i + (1 - τ) * lam)⁻¹) * star U)
        = U * (Matrix.diagonal (fun i => τ * μ i + (1 - τ) * lam) * (star U * U) *
            Matrix.diagonal (fun i => (τ * μ i + (1 - τ) * lam)⁻¹)) * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * star U := by
          rw [hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          have : (fun i => (τ * μ i + (1 - τ) * lam) * (τ * μ i + (1 - τ) * lam)⁻¹) = fun _ => (1 : ℝ) := by
            funext i
            exact mul_inv_cancel₀ (hd i).ne'
          rw [this, Matrix.diagonal_one, Matrix.mul_one]
      _ = 1 := hU2
  refine ⟨Matrix.isUnit_det_of_right_inverse hMR, ?_⟩
  rw [Matrix.inv_eq_right_inv hMR, hD, hR]
  have e : U * Matrix.diagonal (fun i => μ i - lam) * star U *
      (U * Matrix.diagonal (fun i => (τ * μ i + (1 - τ) * lam)⁻¹) * star U) =
      U * (Matrix.diagonal (fun i => (μ i - lam) * (τ * μ i + (1 - τ) * lam)⁻¹) * star U) := by
    calc _ = U * (Matrix.diagonal (fun i => μ i - lam) * (star U * U) *
            Matrix.diagonal (fun i => (τ * μ i + (1 - τ) * lam)⁻¹)) * star U := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hU1, Matrix.mul_one, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
private theorem integral_log_segment {m lam : ℝ} (hm : 0 < m) (hl : 0 < lam) :
    ∫ τ in (0 : ℝ)..1, (m - lam) / (τ * m + (1 - τ) * lam) = Real.log m - Real.log lam := by
  have hd : ∀ τ ∈ Set.uIcc (0 : ℝ) 1, τ * m + (1 - τ) * lam ≠ 0 := fun τ hτ => by
    rw [Set.uIcc_of_le zero_le_one] at hτ
    have h3 : 0 < τ * m + (1 - τ) * lam := by
      rcases eq_or_lt_of_le hτ.1 with h0 | h0
      · rw [← h0]
        simpa using hl
      · have h1 := mul_pos h0 hm
        have h2 : 0 ≤ (1 - τ) * lam := mul_nonneg (by linarith [hτ.2]) hl.le
        linarith
    exact h3.ne'
  have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.log (s * m + (1 - s) * lam)) ((m - lam) / (τ * m + (1 - τ) * lam)) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun s : ℝ => s * m + (1 - s) * lam) (m - lam) τ := by
      have a := ((hasDerivAt_id' τ).mul_const m).add (((hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id' τ)).mul_const lam)
      have e : 1 * m + (0 - 1) * lam = m - lam := by ring
      rw [e] at a
      exact a
    exact h1.log (hd τ hτ)
  have hc : ContinuousOn (fun τ : ℝ => (m - lam) / (τ * m + (1 - τ) * lam)) (Set.uIcc 0 1) :=
    ContinuousOn.div continuousOn_const (by fun_prop) hd
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hc.intervalIntegrable]
  simp
private theorem integral_trace_resolvent {H : Matrix ι ι ℝ} (hH : H.PosDef) {lam : ℝ} (hl : 0 < lam) :
    ∫ τ in (0 : ℝ)..1, Matrix.trace ((H - lam • (1 : Matrix ι ι ℝ)) * (τ • H + (1 - τ) • lam • (1 : Matrix ι ι ℝ))⁻¹) =
      Real.log H.det - Fintype.card ι * Real.log lam := by
  obtain ⟨μ, hpos, hdet, hf⟩ := trace_resolvent_eq_sum_eigenvalues hH hl
  have e1 : ∫ τ in (0 : ℝ)..1, Matrix.trace ((H - lam • (1 : Matrix ι ι ℝ)) *
        (τ • H + (1 - τ) • lam • (1 : Matrix ι ι ℝ))⁻¹) =
      ∫ τ in (0 : ℝ)..1, ∑ i, (μ i - lam) / (τ * μ i + (1 - τ) * lam) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le zero_le_one] at hτ
    exact (hf τ hτ).2
  rw [e1, intervalIntegral.integral_finsetSum]
  · simp_rw [integral_log_segment (hpos _) hl]
    rw [Finset.sum_sub_distrib, hdet, Real.log_prod (fun i _ => (hpos i).ne')]
    simp
  · intro i _
    refine ContinuousOn.intervalIntegrable (ContinuousOn.div continuousOn_const (by fun_prop) fun τ hτ => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hτ
    have h3 : 0 < τ * μ i + (1 - τ) * lam := by
      rcases eq_or_lt_of_le hτ.1 with h0 | h0
      · rw [← h0]
        simpa using hl
      · have h1 := mul_pos h0 (hpos i)
        have h2 : 0 ≤ (1 - τ) * lam := mul_nonneg (by linarith [hτ.2]) hl.le
        linarith
    exact h3.ne'
private theorem continuousOn_entry_mul_resolvent {H : Matrix ι ι ℝ} (hH : H.PosDef) {lam : ℝ} (hl : 0 < lam)
    (A : Matrix ι ι ℝ) (i j : ι) :
    ContinuousOn (fun τ : ℝ => (A * (τ • H + (1 - τ) • lam • (1 : Matrix ι ι ℝ))⁻¹) i j) (Set.Icc 0 1) := by
  obtain ⟨μ, -, -, hf⟩ := trace_resolvent_eq_sum_eigenvalues hH hl
  have hM : Continuous fun τ : ℝ => τ • H + (1 - τ) • lam • (1 : Matrix ι ι ℝ) := by fun_prop
  have hinv : ContinuousOn (fun τ : ℝ => (τ • H + (1 - τ) • lam • (1 : Matrix ι ι ℝ))⁻¹) (Set.Icc 0 1) := by
    simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
    refine ContinuousOn.smul (ContinuousOn.inv₀ hM.matrix_det.continuousOn fun τ hτ => (hf τ hτ).1.ne_zero) ?_
    exact hM.matrix_adjugate.continuousOn
  have hc : Continuous fun X : Matrix ι ι ℝ => (A * X) i j :=
    Continuous.matrix_elem (continuous_const.matrix_mul continuous_id) i j
  exact hc.comp_continuousOn hinv
end Resolvent
section Sum
variable {L t n : ℕ} [NeZero n]
private theorem sum_finiteCells_eq_sum_sites (G : (TorusFields.torusFrame L t n).Cell → ℝ) :
    ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n), G Y =
      ∑ y : TorusFields.TorusSite n,
        G (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top y) := by
  classical
  have hn : ∀ i, (TorusFields.torusFrame L t n).extent i = n := fun _ => rfl
  rw [← TopLevelSites.cellsOfSites_univ hn]
  unfold TorusFields.cellsOfSites
  rw [Finset.sum_image]
  · rfl
  · intro y _ y' _ e
    have e' : StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top y =
        StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top y' := e
    have := congrArg (TorusLumps.toTorusSite n) e'
    rwa [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn),
      TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn)] at this
abbrev _root_.YangMills.SharedProofs.p21825 := @sum_finiteCells_eq_sum_sites
private theorem mem_finiteCells_torusFrame (Y : (TorusFields.torusFrame L t n).Cell) :
    Y ∈ ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n) :=
  TopLevelSites.mem_finiteCells (fun _ => Nat.pos_of_ne_zero (NeZero.ne n)) Y
end Sum
section Density
variable {F : BlockAverages.BlockFrame}
private theorem continuousOn_hessianCellShare {a ρ lam : ℝ} (hl : 0 < lam) {V : F.GaugeField F.top}
    (hH : (ReferenceDensity.chartedHessian a ρ V 0).PosDef) (Y : F.Cell) :
    ContinuousOn (fun τ => ReferenceDensity.hessianCellShare a ρ lam Y V τ) (Set.Icc 0 1) := by
  unfold ReferenceDensity.hessianCellShare
  refine continuousOn_finsetSum _ fun i _ => ?_
  split_ifs
  · exact continuousOn_entry_mul_resolvent hH hl _ i i
  · exact continuousOn_const
private theorem sum_stepDensity_eq_logAmplitude {a ρ lam : ℝ} (hl : 0 < lam)
    (hmem : ∀ Y : F.Cell, Y ∈ ColdStepAtMirrorFrames.finiteCells F) (V : F.GaugeField F.top)
    (hH : (ReferenceDensity.chartedHessian a ρ V 0).PosDef) :
    ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells F, ReferenceDensity.stepDensity a ρ lam Y V =
      SlopeCoefficient.stepLogAmplitude a ρ V +
        1 / 2 * (Fintype.card (ReferenceDensity.ChartCoord F) * Real.log lam) := by
  have hshare : ∀ Y : F.Cell, IntervalIntegrable (fun τ => ReferenceDensity.hessianCellShare a ρ lam Y V τ)
      MeasureTheory.volume 0 1 := by
    intro Y
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_hessianCellShare hl hH Y
  have h1 : ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells F,
      ∫ τ in (0 : ℝ)..1, ReferenceDensity.hessianCellShare a ρ lam Y V τ =
      Real.log (ReferenceDensity.chartedHessian a ρ V 0).det -
        Fintype.card (ReferenceDensity.ChartCoord F) * Real.log lam := by
    rw [← intervalIntegral.integral_finsetSum fun Y _ => hshare Y, ← integral_trace_resolvent hH hl]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    show ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells F, ReferenceDensity.hessianCellShare a ρ lam Y V τ = _
    unfold ReferenceDensity.hessianCellShare
    rw [Finset.sum_comm, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq (ColdStepAtMirrorFrames.finiteCells F) (BlockAverages.enclosingCell i.1.1.1),
      if_pos (hmem _)]
    rfl
  have h2 : ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells F,
      ∑ c ∈ (BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) F.top).filter (fun c => c.1 = Y),
        Real.log ‖BlockAverages.contourAverage (ColdStepAtMirrorFrames.fieldAboveFrame true a ρ 0 V 0) c‖ =
      ∑ c ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) F.top,
        Real.log ‖BlockAverages.contourAverage (ColdStepAtMirrorFrames.fieldAboveFrame true a ρ 0 V 0) c‖ :=
    Finset.sum_fiberwise_of_maps_to (fun c _ => hmem c.1) _
  have h3 : ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells F,
      ∑ b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)),
        (if BlockAverages.enclosingCell b.1.1 = Y then
          ColdStepAtMirrorFrames.haarLogRatio (ColdStepAtMirrorFrames.coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2)
        else 0) =
      ∑ b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)),
        ColdStepAtMirrorFrames.haarLogRatio (ColdStepAtMirrorFrames.coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_ite_eq (ColdStepAtMirrorFrames.finiteCells F) (BlockAverages.enclosingCell b.1.1), if_pos (hmem _)]
  unfold ReferenceDensity.stepDensity SlopeCoefficient.stepLogAmplitude
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2, h3]
  ring
end Density
private theorem isCold_trivialField {s : ℝ} (hs : 0 < s) (n : ℕ) : TorusFields.IsCold s (TorusFields.trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
theorem stepTotalEqDensitySum_of_stepHessianPosDef (hP : stepHessianPosDefStatement) :
    StepTotalEqDensitySum := by
  intro T hT t n _ V hn hV
  have hl : 0 < T.lam := hT.chain.2.2.1
  have hσ : 0 < 9 / 8 * T.threshold := by
    have := hT.σ_pos
    positivity
  have h1 := sum_stepDensity_eq_logAmplitude (F := TorusFields.torusFrame T.side t n) hl mem_finiteCells_torusFrame _
    (hP T hT t n V hn hV)
  have h2 := sum_stepDensity_eq_logAmplitude (F := TorusFields.torusFrame T.side t n) hl mem_finiteCells_torusFrame _
    (hP T hT t n (TorusFields.trivialField n) hn (isCold_trivialField hσ n))
  rw [sum_finiteCells_eq_sum_sites] at h1 h2
  unfold centeredDensityTotal
  rw [dif_neg (NeZero.ne n)]
  have e : ∀ y : TorusFields.TorusSite n, TorusLumps.centered (paramStepDensity T t) n y V =
      ReferenceDensity.stepDensity T.coupling T.ρA T.lam
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top y)
          (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V) -
        ReferenceDensity.stepDensity T.coupling T.ρA T.lam
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top y)
          (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top
            (TorusFields.trivialField n)) := fun y => rfl
  simp_rw [e]
  rw [Finset.sum_sub_distrib, h1, h2]
  show _ = SlopeCoefficient.stepLogAmplitude _ _ _ - SlopeCoefficient.stepLogAmplitude _ _ _
  ring
end YangMills.Construction.RunningCouplingSlope
end
