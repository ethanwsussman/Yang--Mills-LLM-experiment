import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.OmGrowsLikeALogarithm
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheMeanOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusCounting RenormalizationStepParameters StepSettings StepCosts
  TorusLumps TorusFields
namespace LogJacobianBound
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖(toImaginary v : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
theorem norm_toCoords (w : imaginaryQuaternions) : ‖toCoords w‖ = ‖(w : ℍ[ℝ])‖ := by
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  have hsq : ‖toCoords w‖ ^ 2 = ‖(w : ℍ[ℝ])‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, sq ‖(w : ℍ[ℝ])‖, ← Quaternion.normSq_eq_norm_mul_self,
      Quaternion.normSq_def', hre]
    simp [toCoords, Fin.sum_univ_three]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
theorem norm_minimizingBondCoordinate_le {F : BlockFrame} (a ρ : ℝ) (hρ : 0 ≤ ρ) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4) :
    ‖(minimizingBondCoordinate a ρ S b V : ℍ[ℝ])‖ ≤ ρ := by
  classical
  unfold minimizingBondCoordinate minimizingCoordinates
  split_ifs with h
  · have hs := h.choose_spec
    by_cases hb : b ∈ chordBonds S
    · exact hs.2.1 b hb
    · rw [hs.1 b hb]
      simpa using hρ
  · simpa using hρ
theorem norm_frame_le {R : StepSetup} {n : ℕ} (hρ : 0 ≤ R.anchorRadius) (s : ChartSetting R n)
    (b : TorusBond (n * R.params.side)) : ‖(s.frame b : ℍ[ℝ])‖ ≤ R.anchorRadius := by
  unfold ChartSetting.frame frameCoord bondFrameCoord reflectedBondCoord
  split_ifs
  · exact norm_minimizingBondCoordinate_le _ _ hρ _ _ _
  · exact norm_minimizingBondCoordinate_le _ _ hρ _ _ _
theorem haarLogDensity_bounds {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ ≤ 3 / 2) :
    2 / Real.pi ^ 4 ≤ haarLogDensity v ∧ haarLogDensity v ≤ 1 := by
  have hπ := Real.pi_gt_three
  have hlt : ‖v‖ < Real.pi := by linarith
  unfold haarLogDensity
  rw [if_pos hlt]
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs1 : |Real.sinc ‖v‖| ≤ 1 := Real.abs_sinc_le_one _
  have hs2 : 2 / Real.pi ≤ Real.sinc ‖v‖ := by
    by_cases h0 : ‖v‖ = 0
    · rw [h0, Real.sinc_zero]
      rw [div_le_one hπ0]
      linarith
    · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm h0)
      rw [Real.sinc_of_ne_zero h0, le_div_iff₀ hp]
      exact Real.mul_le_sin hp.le (by linarith)
  have hs0 : 0 ≤ 2 / Real.pi := by positivity
  constructor
  · have h3 : (2 / Real.pi) ^ 2 ≤ Real.sinc ‖v‖ ^ 2 := pow_le_pow_left₀ hs0 hs2 2
    calc 2 / Real.pi ^ 4 = (2 / Real.pi) ^ 2 / (2 * Real.pi ^ 2) := by
          field_simp
      _ ≤ _ := by gcongr
  · have h3 : Real.sinc ‖v‖ ^ 2 ≤ 1 := by
      have := sq_abs (Real.sinc ‖v‖)
      rw [← this]
      exact pow_le_one₀ (abs_nonneg _) hs1
    rw [div_le_one (by positivity)]
    nlinarith
theorem abs_log_haarLogDensity_le {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ ≤ 3 / 2) :
    |Real.log (haarLogDensity v)| ≤ Real.log (Real.pi ^ 4 / 2) := by
  obtain ⟨h1, h2⟩ := haarLogDensity_bounds hv
  have ha : (0 : ℝ) < 2 / Real.pi ^ 4 := by positivity
  have hpos : 0 < haarLogDensity v := lt_of_lt_of_le ha h1
  have hn : Real.log (haarLogDensity v) ≤ 0 := Real.log_nonpos hpos.le h2
  rw [abs_of_nonpos hn]
  have h3 : Real.log (2 / Real.pi ^ 4) ≤ Real.log (haarLogDensity v) := Real.log_le_log ha h1
  have h4 : Real.log (Real.pi ^ 4 / 2) = -Real.log (2 / Real.pi ^ 4) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  linarith
theorem norm_contourMean_le {F : BlockFrame} (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth)))
    (b : F.Cell → F.Site F.depth) (W : F.GaugeField F.depth) (c : F.Cell × Fin 4) :
    ‖contourMean J₀ h b W c‖ ≤ 1 := by apply _root_.YangMills.Construction.WeightedResponses.norm_contourMean_le <;> assumption
end LogJacobianBound
open LogJacobianBound in
theorem logJacobianLeLog_holds (hGap : LogPartitionGapLogGrowth) (hKer : BondKernelProperties) :
    LogJacobianLeLog := by
  classical
  intro T hT
  obtain ⟨C₀, hC₀, hGap⟩ := hGap
  have hK0 := hKer.1
  set A := Real.log (Real.pi ^ 4 / 2) with hA
  have hA0 : 0 ≤ A := by
    apply Real.log_nonneg
    have := Real.pi_gt_three
    have h81 : (81 : ℝ) ≤ Real.pi ^ 4 := by
      have : (3 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) this.le 4
      linarith
    linarith
  have ha1 := hT.a_ge
  set B : ℝ := 4 * C₀ * (1 + Real.log (2 + T.coupling)) + (4 * (2 * (T.side : ℝ) + 1) ^ 4) * A with hB
  have hla : 0 ≤ Real.log (2 + T.coupling) := Real.log_nonneg (by linarith)
  refine ⟨B + 1, Real.exp 1, by positivity, fun y hy R hR n _ hn s hs η hη Y => ?_⟩
  have hx : Real.exp 1 ≤ R.coupling := hy.trans hR.le_coupling
  have hx1 : 1 ≤ R.coupling := (Real.one_le_exp (by norm_num)).trans hx
  have hlog : 1 ≤ Real.log R.coupling := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hx
  have haL : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hLL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hρAle : R.anchorRadius ≤ 1 := by
    rw [hR.anchorRadius_eq]
    exact hT.chain.2.2.2.2.1
  have hρA0 : 0 ≤ R.anchorRadius := by
    rw [hR.anchorRadius_eq]
    exact hT.chain.2.2.2.1.le
  have hρ : R.ballRadius ≤ 1 / 2 := by
    have e : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [hR.params_eq]
      rfl
    have h1 := hT.ρ_le
    have h2 := hT.chain.2.2.2.2.1
    have h3 := hT.chain.2.2.2.2.2.2.2.1 0
    have h4 := hT.σ_pos
    have h5 : 0 ≤ 2 * T.N 0 * T.threshold := by positivity
    rw [e]
    linarith
  have hgap1 : ∀ i : Fin 4,
      |logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i))| ≤
      C₀ * (1 + Real.log (2 + T.coupling)) * Real.log R.coupling := by
    intro i
    set m := meanNorm R.params (s.field η) s.bases (Y, i) with hm
    have hm0 : 0 ≤ m := norm_nonneg _
    have hm1 : m ≤ 1 := norm_contourMean_le _ _ _ _ _
    have hs0 : 0 ≤ R.params.coupling * R.coupling * m := by
      rw [haL]
      positivity
    have h1 := (hK0 _ hs0).2
    have h2 := hGap _ hs0
    rw [abs_of_nonneg h1]
    have h3 : R.params.coupling * R.coupling * m ≤ T.coupling * R.coupling := by
      rw [haL]
      have : 0 ≤ T.coupling * R.coupling := by positivity
      nlinarith
    have h4 : Real.log (2 + R.params.coupling * R.coupling * m) ≤
        Real.log ((2 + T.coupling) * R.coupling) := by
      apply Real.log_le_log (by linarith)
      nlinarith
    have h5 : Real.log ((2 + T.coupling) * R.coupling) = Real.log (2 + T.coupling) + Real.log R.coupling :=
      Real.log_mul (by linarith) (by linarith)
    calc _ ≤ C₀ * Real.log (2 + R.params.coupling * R.coupling * m) := h2
      _ ≤ C₀ * (Real.log (2 + T.coupling) + Real.log R.coupling) := by
          rw [← h5]
          exact mul_le_mul_of_nonneg_left h4 hC₀.le
      _ ≤ _ := by
          have : Real.log (2 + T.coupling) ≤ Real.log (2 + T.coupling) * Real.log R.coupling := by nlinarith
          have h6 : C₀ * (Real.log (2 + T.coupling) + Real.log R.coupling) ≤
              C₀ * (Real.log (2 + T.coupling) * Real.log R.coupling + Real.log R.coupling) := by
            apply mul_le_mul_of_nonneg_left _ hC₀.le
            linarith
          linarith
  have hhaar : ∀ b : s.free, ‖toCoords (s.frame b.1) + η b‖ ≤ 3 / 2 := by
    intro b
    have h1 := norm_add_le (toCoords (s.frame b.1)) (η b)
    rw [norm_toCoords] at h1
    have h2 := norm_frame_le hρA0 s b.1
    have h3 := hη b
    unfold coordNorm at h3
    rw [norm_toImaginary] at h3
    linarith
  have hcount : ((Finset.univ.filter fun b : s.free => bondBlock (R := R) b.1 = Y).card : ℝ) ≤
      4 * (2 * (T.side : ℝ) + 1) ^ 4 := by
    have hinj : ((Finset.univ.filter fun b : s.free => bondBlock (R := R) b.1 = Y).card) ≤
        ((sitesInBlocks R.params.side {Y}) ×ˢ (Finset.univ : Finset (Fin 4))).card := by
      refine Finset.card_le_card_of_injOn (fun b => b.1) ?_ ?_
      · intro b hb
        have hb2 : bondBlock (R := R) b.1 = Y := (Finset.mem_filter.mp hb).2
        refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
        simpa [sitesInBlocks, bondBlock] using hb2
      · intro a _ b _ h
        exact Subtype.ext h
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hinj
    have h2 := card_sitesInBlocks_singleton_le (L := R.params.side) Y
    have h3 : ((Finset.univ.filter fun b : s.free => bondBlock (R := R) b.1 = Y).card) ≤
        (2 * R.params.side + 1) ^ 4 * 4 := hinj.trans (Nat.mul_le_mul_right _ h2)
    have h4 : ((Finset.univ.filter fun b : s.free => bondBlock (R := R) b.1 = Y).card : ℝ) ≤
        (((2 * R.params.side + 1) ^ 4 * 4 : ℕ) : ℝ) := by exact_mod_cast h3
    have e : (((2 * R.params.side + 1) ^ 4 * 4 : ℕ) : ℝ) = 4 * (2 * (T.side : ℝ) + 1) ^ 4 := by
      push_cast
      rw [hLL]
      ring
    rw [e] at h4
    exact h4
  have hsum : |∑ b : s.free, if bondBlock (R := R) b.1 = Y then
      Real.log (haarLogDensity (toCoords (s.frame b.1) + η b)) else 0| ≤
      (4 * (2 * (T.side : ℝ) + 1) ^ 4) * A := by
    rw [← Finset.sum_filter]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _b ∈ Finset.univ.filter (fun b : s.free => bondBlock (R := R) b.1 = Y), A :=
          Finset.sum_le_sum fun b _ => abs_log_haarLogDensity_le (hhaar b)
      _ = ((Finset.univ.filter fun b : s.free => bondBlock (R := R) b.1 = Y).card : ℝ) * A := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount hA0
  have hfour : |∑ i : Fin 4,
      logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i))| ≤
      4 * (C₀ * (1 + Real.log (2 + T.coupling)) * Real.log R.coupling) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 4, C₀ * (1 + Real.log (2 + T.coupling)) * Real.log R.coupling :=
          Finset.sum_le_sum fun i _ => hgap1 i
      _ = _ := by simp
  have hmain : |s.logJacobian (s.field η) η Y| ≤
      4 * (C₀ * (1 + Real.log (2 + T.coupling)) * Real.log R.coupling) +
        (4 * (2 * (T.side : ℝ) + 1) ^ 4) * A := by
    unfold ChartSetting.logJacobian
    exact (abs_add_le _ _).trans (add_le_add hfour hsum)
  have hAc : 0 ≤ (4 * (2 * (T.side : ℝ) + 1) ^ 4) * A := by positivity
  calc _ ≤ _ := hmain
    _ ≤ (B + 1) * Real.log R.coupling := by
        have e : (B + 1) * Real.log R.coupling =
            4 * (C₀ * (1 + Real.log (2 + T.coupling)) * Real.log R.coupling) +
            (4 * (2 * (T.side : ℝ) + 1) ^ 4) * A * Real.log R.coupling + Real.log R.coupling := by
          rw [hB]
          ring
        rw [e]
        nlinarith
end YangMills.Construction.ClusterExpansionOfAStep
end
