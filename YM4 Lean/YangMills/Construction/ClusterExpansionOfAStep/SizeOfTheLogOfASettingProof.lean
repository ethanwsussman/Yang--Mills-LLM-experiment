import YangMills.Construction.ClusterExpansionOfAStep.SizeOfADensityProof
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfJOfASettingProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts RenormalizationStepParameters
namespace LogJacobian
theorem coordNorm_toImaginary (z : EuclideanSpace ℝ (Fin 3)) : coordNorm z = ‖z‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
theorem norm_toCoords (w : imaginaryQuaternions) : ‖toCoords w‖ = ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianBound.norm_toCoords <;> assumption
theorem norm_contourMean_le {F : BlockFrame} (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth)))
    (b : F.Cell → F.Site F.depth) (W : F.GaugeField F.depth) (c : F.Cell × Fin 4) :
    ‖contourMean J₀ h b W c‖ ≤ 1 := by apply _root_.YangMills.Construction.WeightedResponses.norm_contourMean_le <;> assumption
theorem norm_minimizingCoordinates_le {F : BlockFrame} (a : ℝ) (S : Finset F.Cell)
    (V : F.GaugeField F.top) {ρ : ℝ} (hρ : 0 ≤ ρ) (x : F.Site F.depth) (i : Fin 4) :
    ‖minimizingCoordinates a S V ρ x i‖ ≤ ρ := by
  unfold minimizingCoordinates
  split_ifs with h
  · have hs := h.choose_spec
    by_cases hb : (x, i) ∈ chordBonds S
    · exact hs.2.1 (x, i) hb
    · have := hs.1 (x, i) hb
      simp only at this
      rw [this, norm_zero]
      exact hρ
  · simpa using hρ
theorem norm_bondFrameCoord_le {F : BlockFrame} (a : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    ‖bondFrameCoord a ρ m b V‖ ≤ ρ := by
  unfold bondFrameCoord reflectedBondCoord minimizingBondCoordinate
  split_ifs
  · exact norm_minimizingCoordinates_le _ _ _ hρ _ _
  · exact norm_minimizingCoordinates_le _ _ _ hρ _ _
theorem abs_log_haarLogDensity_le (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ ≤ 3 / 2) :
    |Real.log (haarLogDensity v)| ≤ -Real.log (2 / Real.pi ^ 4) := by
  have hpi := Real.pi_gt_three
  have hpos : 0 < Real.pi := Real.pi_pos
  have hlt : ‖v‖ < Real.pi := by linarith
  have hJ : haarLogDensity v = (Real.sinc ‖v‖) ^ 2 / (2 * Real.pi ^ 2) := by
    unfold haarLogDensity
    rw [if_pos hlt]
  have hs1 : 2 / Real.pi ≤ Real.sinc ‖v‖ := by
    by_cases h0 : ‖v‖ = 0
    · rw [h0, Real.sinc_zero, div_le_one hpos]
      linarith
    · have hn : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm h0)
      rw [Real.sinc_of_ne_zero h0, le_div_iff₀ hn]
      exact Real.mul_le_sin hn.le (by linarith)
  have hs0 : 0 < 2 / Real.pi := by positivity
  have hlow : 2 / Real.pi ^ 4 ≤ haarLogDensity v := by
    rw [hJ, le_div_iff₀ (by positivity)]
    have h1 : (2 / Real.pi) ^ 2 ≤ Real.sinc ‖v‖ ^ 2 := pow_le_pow_left₀ hs0.le hs1 2
    have h2 : 2 / Real.pi ^ 4 * (2 * Real.pi ^ 2) = (2 / Real.pi) ^ 2 := by
      field_simp
    rw [h2]
    exact h1
  have hup : haarLogDensity v ≤ 1 := by
    rw [hJ, div_le_one (by positivity)]
    have h1 : Real.sinc ‖v‖ ^ 2 ≤ 1 := by
      have := Real.abs_sinc_le_one ‖v‖
      exact sq_le_one_iff_abs_le_one _ |>.mpr this
    nlinarith [sq_nonneg Real.pi]
  have hlp : 0 < 2 / Real.pi ^ 4 := by positivity
  have hJp : 0 < haarLogDensity v := hlp.trans_le hlow
  have l1 := Real.log_le_log hlp hlow
  have l2 : Real.log (haarLogDensity v) ≤ 0 := Real.log_nonpos hJp.le hup
  rw [abs_of_nonpos l2]
  linarith
variable {n : ℕ}
theorem card_parentBlock_fiber_le [NeZero n] (L : ℕ) [NeZero L] (Y : TorusSite n) :
    ((Finset.univ : Finset (TorusSite (n * L))).filter fun x => parentBlock L x = Y).card ≤ L ^ 4 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DensityBound.card_parentBlock_fibre_le <;> assumption
theorem logJacobianBound_of_kernel (hk : BondKernelProperties)
    (ho : LogPartitionGapLogGrowth) : ClusterExpansionOfAStep.LogJacobianBound := by
  classical
  intro T hT
  obtain ⟨C₀, hC₀, hom⟩ := ho
  have ha : 0 < T.coupling := by linarith [hT.a_ge]
  have hK0 : 0 ≤ -Real.log (2 / Real.pi ^ 4) := by
    have h3 := Real.pi_gt_three
    have : 2 / Real.pi ^ 4 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3.le 4]
    have := Real.log_nonpos (by positivity) this
    linarith
  set K := -Real.log (2 / Real.pi ^ 4) with hK
  have hlogA : 0 ≤ Real.log (T.coupling + 2) := Real.log_nonneg (by linarith [hT.a_ge])
  refine ⟨4 * (C₀ * (Real.log (T.coupling + 2) + 1)) + 4 * (T.side : ℝ) ^ 4 * K + 1, Real.exp 1,
    by positivity, fun y R hR hρA hx n _ s Y η hη => ?_⟩
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have haR : R.params.coupling = T.coupling := by rw [hR]; rfl
  have hσR : R.params.threshold = T.threshold := by rw [hR]; rfl
  have hxpos : 0 < R.coupling := (Real.exp_pos 1).trans_le hx
  have hx1 : 1 ≤ R.coupling := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog1 : 1 ≤ Real.log R.coupling := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hρle : R.ballRadius ≤ 1 / 2 := by
    have h1 := hT.ρ_le
    have hN := hT.chain
    obtain ⟨_, _, _, hρ0, hρ1, _, _, hNp, _⟩ := hN
    have h2 := hNp 0
    have h3 := hT.σ_pos
    have h4 : R.ballRadius = T.ballRadius := by
      show R.params.threshold / 64 = T.threshold / 64
      rw [hσR]
    rw [h4]
    nlinarith [mul_pos h2 h3]
  have hρA0 : 0 ≤ R.anchorRadius ∧ R.anchorRadius ≤ 1 := by
    obtain ⟨_, _, _, hρ0, hρ1, _⟩ := hT.chain
    rw [hρA]
    exact ⟨hρ0.le, hρ1⟩
  have hbond : ∀ b : s.free,
      |Real.log (haarLogDensity (toCoords (s.frame b.1) + η b))| ≤ K := by
    intro b
    refine abs_log_haarLogDensity_le _ ?_
    have h1 : ‖toCoords (s.frame b.1)‖ ≤ 1 := by
      rw [norm_toCoords]
      have := norm_bondFrameCoord_le (F := torusFrame R.params.side R.depth n) R.params.coupling
        hρA0.1 R.frameReach
        (torusSiteInFrame (torusFrame R.params.side R.depth n)
          (torusFrame R.params.side R.depth n).depth b.1.1, b.1.2)
        (readAtLevel (torusFrame R.params.side R.depth n)
          (torusFrame R.params.side R.depth n).top s.coarse)
      exact this.trans hρA0.2
    have h2 : ‖η b‖ ≤ 1 / 2 := by
      have := hη b
      rw [coordNorm_toImaginary] at this
      linarith
    calc _ ≤ ‖toCoords (s.frame b.1)‖ + ‖η b‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by linarith
  have hcount : ((Finset.univ : Finset s.free).filter fun b => bondBlock (R := R) b.1 = Y).card ≤
      R.params.side ^ 4 * 4 := by
    have h1 := card_parentBlock_fiber_le (n := n) R.params.side Y
    have h2 : ((Finset.univ : Finset s.free).filter fun b => bondBlock (R := R) b.1 = Y).card ≤
        (((Finset.univ : Finset (TorusSite (n * R.params.side))).filter
          fun x => parentBlock R.params.side x = Y) ×ˢ (Finset.univ : Finset (Fin 4))).card := by
      refine Finset.card_le_card_of_injOn (fun b => b.1) ?_ ?_
      · intro b hb
        have hb' : bondBlock (R := R) b.1 = Y := by simpa using hb
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and, and_true]
        exact hb'
      · intro b _ b' _ h
        exact Subtype.ext h
    rw [Finset.card_product] at h2
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    exact h2.trans (Nat.mul_le_mul_right 4 h1)
  have hLr : (R.params.side : ℝ) = (T.side : ℝ) := by rw [hL]
  have hB : |∑ b : s.free, if bondBlock (R := R) b.1 = Y then
      Real.log (haarLogDensity (toCoords (s.frame b.1) + η b)) else 0| ≤
        4 * (T.side : ℝ) ^ 4 * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ b ∈ (Finset.univ : Finset s.free),
        |if bondBlock (R := R) b.1 = Y then
          Real.log (haarLogDensity (toCoords (s.frame b.1) + η b)) else 0| ≤
        if bondBlock (R := R) b.1 = Y then K else 0 := by
      intro b _
      split_ifs
      · exact hbond b
      · simp
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h2 : (((Finset.univ : Finset s.free).filter
        fun b => bondBlock (R := R) b.1 = Y).card : ℝ) ≤
        (R.params.side : ℝ) ^ 4 * 4 := by exact_mod_cast hcount
    rw [hLr] at h2
    nlinarith
  have hone : ∀ i : Fin 4,
      |logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i))| ≤
        C₀ * (Real.log (T.coupling + 2) + 1) * Real.log R.coupling := by
    intro i
    set m := meanNorm R.params (s.field η) s.bases (Y, i) with hm
    have hm0 : 0 ≤ m := norm_nonneg _
    have hm1 : m ≤ 1 := norm_contourMean_le _ _ _ _ _
    have hs0 : 0 ≤ R.params.coupling * R.coupling * m := by rw [haR]; positivity
    have hsle : R.params.coupling * R.coupling * m ≤ T.coupling * R.coupling := by
      rw [haR]
      have : 0 ≤ T.coupling * R.coupling := by positivity
      nlinarith
    rw [abs_of_nonneg (hk.1 _ hs0).2]
    refine (hom _ hs0).trans ?_
    have h2 : Real.log (2 + R.params.coupling * R.coupling * m) ≤
        Real.log ((T.coupling + 2) * R.coupling) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_mul (by linarith) hxpos.ne'] at h2
    have h3 : Real.log (T.coupling + 2) + Real.log R.coupling ≤
        (Real.log (T.coupling + 2) + 1) * Real.log R.coupling := by
      nlinarith
    calc _ ≤ C₀ * ((Real.log (T.coupling + 2) + 1) * Real.log R.coupling) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) hC₀.le
      _ = _ := by ring
  have hA : |∑ i : Fin 4,
      logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i))| ≤
        4 * (C₀ * (Real.log (T.coupling + 2) + 1)) * Real.log R.coupling := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hone i).trans ?_
    simp
    nlinarith
  unfold ChartSetting.logJacobianAt ChartSetting.logJacobian
  refine (abs_add_le _ _).trans ?_
  have hL4 : 0 ≤ 4 * (T.side : ℝ) ^ 4 * K := by positivity
  nlinarith
end LogJacobian
end YangMills.Construction
end
