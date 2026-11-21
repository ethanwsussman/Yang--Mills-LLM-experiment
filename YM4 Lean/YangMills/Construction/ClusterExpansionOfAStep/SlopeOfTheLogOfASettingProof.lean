import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfAContour
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfTheLogOfASettingProof
import YangMills.Construction.ClusterExpansionOfAStep.TheMeanReadsItsTwoBlocks
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfTheGroupGap
import YangMills.Construction.ColdStepAtMirrorFrames.WeylFormulaOfTheGroup
import YangMills.Construction.SummableBoundsOfTheFlow.ShortMovesOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusContours ContourOffsets TopLevelSites
open TorusFields TorusLumps StepSettings StepCosts RenormalizationStepParameters
namespace ClusterExpansionOfAStep
namespace LogJacobianSlope
theorem continuous_haarRealPartDensity : Continuous haarRealPartDensity := by
  unfold haarRealPartDensity
  fun_prop
theorem haarRealPartDensity_nonneg (v : ℝ) : 0 ≤ haarRealPartDensity v := by
  unfold haarRealPartDensity
  have := Real.pi_pos
  positivity
theorem haarRealPartDensity_le_sqrt {v : ℝ} :
    haarRealPartDensity v ≤ 2 * Real.sqrt (max 1 (2 * v - v ^ 2)) := by
  unfold haarRealPartDensity
  have hp := Real.pi_gt_three
  have h1 : 2 / Real.pi ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h2 : Real.sqrt (2 * v - v ^ 2) ≤ Real.sqrt (max 1 (2 * v - v ^ 2)) :=
    Real.sqrt_le_sqrt (le_max_right _ _)
  exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by norm_num)
theorem haarRealPartDensity_le_two {v : ℝ} : haarRealPartDensity v ≤ 2 := by
  refine haarRealPartDensity_le_sqrt.trans ?_
  have h : max 1 (2 * v - v ^ 2) ≤ 1 := max_le le_rfl (by nlinarith [sq_nonneg (v - 1)])
  have := Real.sqrt_le_one.mpr h
  linarith
theorem haarLaplace_pos (s : ℝ) : 0 < haarLaplace s := by
  unfold haarLaplace
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (((Real.continuous_exp.comp (by fun_prop)).mul continuous_haarRealPartDensity)).intervalIntegrable _ _
  · intro v hv
    have h1 : 0 < 2 * v - v ^ 2 := by nlinarith [hv.1, hv.2]
    have h2 : 0 < haarRealPartDensity v := by
      unfold haarRealPartDensity
      have := Real.pi_pos
      have := Real.sqrt_pos.mpr h1
      positivity
    have := Real.exp_pos (-(s * v))
    positivity
  · norm_num
theorem differentiableAt_haarLaplace (s : ℝ) : DifferentiableAt ℝ haarLaplace s := by
  have hc : ∀ x : ℝ, Continuous fun v : ℝ => Real.exp (-(x * v)) * haarRealPartDensity v := fun x =>
    (Real.continuous_exp.comp (by fun_prop)).mul continuous_haarRealPartDensity
  have hc' : ∀ x : ℝ, Continuous fun v : ℝ => -(v * Real.exp (-(x * v)) * haarRealPartDensity v) := fun x =>
    ((continuous_id.mul (Real.continuous_exp.comp (by fun_prop))).mul continuous_haarRealPartDensity).neg
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 2) (s := Metric.ball s 1)
    (F := fun (x v : ℝ) => Real.exp (-(x * v)) * haarRealPartDensity v)
    (F' := fun (x v : ℝ) => -(v * Real.exp (-(x * v)) * haarRealPartDensity v))
    (x₀ := s) (bound := fun _ => 2 * Real.exp (2 * (|s| + 1)) * 2)
    (Metric.ball_mem_nhds s one_pos)
    (Filter.Eventually.of_forall fun x => ((hc x).aestronglyMeasurable).restrict)
    ((hc s).intervalIntegrable _ _)
    ((hc' s).aestronglyMeasurable.restrict)
    ?_ (by exact intervalIntegrable_const) ?_
  · exact key.2.differentiableAt
  · refine Filter.Eventually.of_forall fun v hv x hx => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hv
    have hv0 : 0 ≤ v := hv.1.le
    have hv2 : v ≤ 2 := hv.2
    have hx' : |x| ≤ |s| + 1 := by
      have h1 : |x - s| < 1 := by simpa [Real.dist_eq] using hx
      have h2 := abs_sub_abs_le_abs_sub x s
      linarith
    have he : Real.exp (-(x * v)) ≤ Real.exp (2 * (|s| + 1)) := by
      apply Real.exp_le_exp.mpr
      have h3 : -(x * v) ≤ |x| * v := by
        have := neg_abs_le x
        nlinarith
      nlinarith [abs_nonneg x]
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by
      have := haarRealPartDensity_nonneg v
      positivity)]
    have h2 := haarRealPartDensity_le_two (v := v)
    have h3 := haarRealPartDensity_nonneg v
    exact show v * Real.exp (-(x * v)) * haarRealPartDensity v ≤ 2 * Real.exp (2 * (|s| + 1)) * 2 from by
      gcongr
  · refine Filter.Eventually.of_forall fun v _ x _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-(y * v))) (Real.exp (-(x * v)) * (-v)) x := by
      have : HasDerivAt (fun y : ℝ => -(y * v)) (-v) x :=
        HasDerivAt.congr_deriv ((hasDerivAt_id x).mul_const v).neg (by ring)
      exact this.exp
    refine HasDerivAt.congr_deriv (h1.mul_const (haarRealPartDensity v)) ?_
    ring
theorem differentiableAt_haarGap (s : ℝ) : DifferentiableAt ℝ haarGap s := by
  have hm : DifferentiableAt ℝ haarCharacterMean s := by
    unfold haarCharacterMean
    exact Real.differentiableAt_exp.mul (differentiableAt_haarLaplace s)
  have hne : haarCharacterMean s ≠ 0 := by
    unfold haarCharacterMean
    exact mul_ne_zero (Real.exp_pos s).ne' (haarLaplace_pos s).ne'
  unfold haarGap
  exact differentiableAt_id.sub (hm.log hne)
theorem logPartitionGap_lipschitz_above (hw : WeylIntegrationFormula) (hd : HaarGapDerivBound) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m s t : ℝ, 1 ≤ m → m ≤ s → m ≤ t →
      |logPartitionGap s - logPartitionGap t| ≤ K / m * |s - t| := by
  obtain ⟨C, hC⟩ := hd 1 le_rfl
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 1 le_rfl)
  refine ⟨C, hC0, fun m s t hm hs ht => ?_⟩
  have e : logPartitionGap = haarGap := funext hw.2.2
  rw [e]
  have hder : ∀ u ∈ Set.Ici m, ‖deriv haarGap u‖ ≤ C / m := by
    intro u hu
    have hu' : m ≤ u := hu
    have hu1 : 1 ≤ u := hm.trans hu'
    have h := hC u hu1
    rw [pow_one, iteratedDeriv_one, abs_mul, abs_of_pos (by linarith)] at h
    rw [Real.norm_eq_abs, le_div_iff₀ (by linarith)]
    nlinarith [abs_nonneg (deriv haarGap u)]
  have h := (convex_Ici m).norm_image_sub_le_of_norm_deriv_le (fun u _ => differentiableAt_haarGap u) hder
    (show t ∈ Set.Ici m from ht) (show s ∈ Set.Ici m from hs)
  simpa [Real.norm_eq_abs] using h
theorem sinc_eq_integral_cos (t : ℝ) : Real.sinc t = ∫ u in (0 : ℝ)..1, Real.cos (u * t) := by
  by_cases ht : t = 0
  · subst ht
    simp
  · rw [intervalIntegral.integral_comp_mul_right _ ht, integral_cos, Real.sinc_of_ne_zero ht]
    simp [div_eq_inv_mul]
theorem abs_sinc_sub_le (a b : ℝ) : |Real.sinc a - Real.sinc b| ≤ |a - b| := by
  have hc : ∀ t : ℝ, IntervalIntegrable (fun u : ℝ => Real.cos (u * t)) volume 0 1 := fun t =>
    (Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _
  rw [sinc_eq_integral_cos, sinc_eq_integral_cos, ← intervalIntegral.integral_sub (hc a) (hc b)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun u : ℝ => Real.cos (u * a) - Real.cos (u * b)) (C := |a - b|) (fun u hu => ?_)
  · simpa [Real.norm_eq_abs] using h
  · rw [Set.uIoc_of_le (by norm_num)] at hu
    rw [Real.norm_eq_abs]
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← mul_sub, abs_mul, abs_of_pos hu.1]
    have := abs_nonneg (a - b)
    nlinarith [hu.2]
theorem abs_log_sub_log_le {m A B : ℝ} (hm : 0 < m) (hA : m ≤ A) (hB : m ≤ B) :
    |Real.log A - Real.log B| ≤ |A - B| / m := by
  have key : ∀ {A B : ℝ}, m ≤ A → m ≤ B → Real.log A - Real.log B ≤ |A - B| / m := by
    intro A B hA hB
    have pA : 0 < A := hm.trans_le hA
    have pB : 0 < B := hm.trans_le hB
    have h := Real.log_le_sub_one_of_pos (div_pos pA pB)
    rw [Real.log_div pA.ne' pB.ne'] at h
    have e : A / B - 1 = (A - B) / B := by
      field_simp
    rw [e] at h
    calc _ ≤ (A - B) / B := h
      _ ≤ |A - B| / B := by gcongr; exact le_abs_self _
      _ ≤ |A - B| / m := by gcongr
  rw [abs_le]
  constructor
  · have := key hB hA
    rw [abs_sub_comm] at this
    linarith
  · exact key hA hB
theorem two_div_pi_le_sinc {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 3 / 2) : 2 / Real.pi ≤ Real.sinc a := by
  have hpi := Real.pi_gt_three
  have hpos : 0 < Real.pi := Real.pi_pos
  by_cases ha : a = 0
  · rw [ha, Real.sinc_zero, div_le_one hpos]
    linarith
  · have hn : 0 < a := lt_of_le_of_ne h0 (Ne.symm ha)
    rw [Real.sinc_of_ne_zero ha, le_div_iff₀ hn]
    exact Real.mul_le_sin hn.le (by linarith)
theorem abs_log_haarLogDensity_sub_le (v w : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ ≤ 3 / 2)
    (hw : ‖w‖ ≤ 3 / 2) :
    |Real.log (haarLogDensity v) - Real.log (haarLogDensity w)| ≤ Real.pi ^ 2 * ‖v - w‖ := by
  have hpi := Real.pi_gt_three
  have hform : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ ≤ 3 / 2 →
      haarLogDensity u = Real.sinc ‖u‖ ^ 2 / (2 * Real.pi ^ 2) := by
    intro u hu
    unfold haarLogDensity
    rw [if_pos (by linarith)]
  have hfl : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ ≤ 3 / 2 → 2 / Real.pi ^ 4 ≤ haarLogDensity u := by
    intro u hu
    rw [hform u hu, le_div_iff₀ (by positivity)]
    have h0 : 0 ≤ 2 / Real.pi := by positivity
    have h1 : (2 / Real.pi) ^ 2 ≤ Real.sinc ‖u‖ ^ 2 :=
      pow_le_pow_left₀ h0 (two_div_pi_le_sinc (norm_nonneg u) hu) 2
    have h2 : 2 / Real.pi ^ 4 * (2 * Real.pi ^ 2) = (2 / Real.pi) ^ 2 := by
      field_simp
    rw [h2]
    exact h1
  have hm : 0 < 2 / Real.pi ^ 4 := by positivity
  refine (abs_log_sub_log_le hm (hfl v hv) (hfl w hw)).trans ?_
  rw [hform v hv, hform w hw, ← sub_div]
  set a := Real.sinc ‖v‖ with ha
  set b := Real.sinc ‖w‖ with hb
  have ha1 : |a| ≤ 1 := Real.abs_sinc_le_one _
  have hb1 : |b| ≤ 1 := Real.abs_sinc_le_one _
  have hab : |a - b| ≤ ‖v - w‖ :=
    (abs_sinc_sub_le _ _).trans (abs_norm_sub_norm_le v w)
  have hsq : |a ^ 2 - b ^ 2| ≤ 2 * ‖v - w‖ := by
    have e : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [e, abs_mul]
    have h1 : |a + b| ≤ 2 := (abs_add_le a b).trans (by linarith)
    have h2 := abs_nonneg (a - b)
    nlinarith [norm_nonneg (v - w), abs_nonneg (a + b)]
  rw [abs_div, abs_of_pos (show 0 < 2 * Real.pi ^ 2 by positivity), div_div, div_le_iff₀ (by positivity)]
  have hnorm := norm_nonneg (v - w)
  have h3 : 2 * ‖v - w‖ ≤ Real.pi ^ 2 * ‖v - w‖ * (2 * Real.pi ^ 2 * (2 / Real.pi ^ 4)) := by
    have e2 : Real.pi ^ 2 * ‖v - w‖ * (2 * Real.pi ^ 2 * (2 / Real.pi ^ 4)) = 4 * ‖v - w‖ := by
      field_simp
      ring
    rw [e2]
    linarith
  exact hsq.trans h3
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := CStarRing.norm_coe_unitary g
theorem norm_pathHolonomy_sub_le {F : BlockFrame} {j : ℕ} {X X' : F.GaugeField j} {ε : ℝ}
    (h : ∀ x i, ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - ((X' x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε)
    (x : F.Site j) (l : List PathStep) :
    ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - ((pathHolonomy X' x l : UnitQuaternion) : ℍ[ℝ])‖ ≤
      l.length * ε := by
  induction l generalizing x with
  | nil => simp [pathHolonomy]
  | cons st r ih =>
    have hst : ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) -
        ((linkValue X' x st : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
      unfold linkValue
      split_ifs
      · exact h _ _
      · have e : (((X (x - BlockAverages.unitStep j st.1) st.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
              (((X' (x - BlockAverages.unitStep j st.1) st.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
            star (((X (x - BlockAverages.unitStep j st.1) st.1 : UnitQuaternion) : ℍ[ℝ]) -
              ((X' (x - BlockAverages.unitStep j st.1) st.1 : UnitQuaternion) : ℍ[ℝ])) := by
          rw [star_sub]
          rfl
        rw [e, norm_star]
        exact h _ _
    have e : ((pathHolonomy X x (st :: r) : UnitQuaternion) : ℍ[ℝ]) -
          ((pathHolonomy X' x (st :: r) : UnitQuaternion) : ℍ[ℝ]) =
        (((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) - ((linkValue X' x st : UnitQuaternion) : ℍ[ℝ])) *
            ((pathHolonomy X (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ]) +
          ((linkValue X' x st : UnitQuaternion) : ℍ[ℝ]) *
            (((pathHolonomy X (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ]) -
              ((pathHolonomy X' (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ])) := by
      show ((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) *
          ((pathHolonomy X (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ]) -
        ((linkValue X' x st : UnitQuaternion) : ℍ[ℝ]) *
          ((pathHolonomy X' (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ]) = _
      noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_unitQuaternion, norm_unitQuaternion, mul_one, one_mul, List.length_cons]
    have := ih (x + stepDisplacement j st)
    push_cast
    linarith
theorem length_axisPath_le (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) {M : ℕ} (hM : ∀ k, (h k).natAbs ≤ M) :
    (axisPath h π).length ≤ 4 * M := by apply _root_.YangMills.Construction.TorusContours.length_axisPath_le <;> assumption
theorem length_contourSteps_le {L : ℕ} {z₀ z₁ ξ : Fin 4 → ℤ} (h₀ : z₀ ∈ centredCube L)
    (h₁ : z₁ ∈ centredCube L) (hξ : ξ ∈ centredCube L) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (contourSteps L z₀ z₁ ξ π i).length ≤ 9 * L := by
  have hb : ∀ {z : Fin 4 → ℤ}, z ∈ centredCube L → ∀ k, ((ξ - z) k).natAbs ≤ L := by
    intro z hz k
    have h1 := _root_.YangMills.Construction.TorusContours.mem_centredCube_iff.mp hz k
    have h2 := _root_.YangMills.Construction.TorusContours.mem_centredCube_iff.mp hξ k
    simp only [Pi.sub_apply]
    omega
  have l₀ := length_axisPath_le (ξ - z₀) π (hb h₀)
  have l₁ := length_axisPath_le (ξ - z₁) π (hb h₁)
  unfold contourSteps
  simp only [List.length_append, List.length_replicate, reversePath, List.length_map, List.length_reverse]
  omega
theorem mem_centredCube_of_mem_usedContours {F : BlockFrame} {J₀ : ℕ}
    {h : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth}
    {c : F.Cell × Fin 4} {e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)} (he : e ∈ usedContours J₀ h b c) :
    e.1 ∈ centredCube F.blockSide := by
  classical
  have h1 : e ∈ allContours F := by
    unfold usedContours at he
    split_ifs at he
    · exact he
    · exact (Finset.mem_filter.mp he).1
  exact (Finset.mem_product.mp h1).1
theorem norm_contourMean_sub_le {L n J₀ : ℕ} [NeZero L] [NeZero n] (h16 : 16 ≤ n)
    {h : Finset (Finset ((stepBlockFrame L n).Site 0))}
    {b : (stepBlockFrame L n).Cell → (stepBlockFrame L n).Site 0}
    (hb : IsBaseChoice J₀ h b) {W W' : (stepBlockFrame L n).GaugeField 0} {ε : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - ((W' x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε)
    (c : (stepBlockFrame L n).Cell × Fin 4) :
    ‖contourMean J₀ h b W c - contourMean J₀ h b W' c‖ ≤ 9 * (L : ℝ) * ε := by
  obtain ⟨y, i⟩ := c
  have hL1 : 1 ≤ (stepBlockFrame L n).blockSide := Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨z₀, h₀, hz₀⟩ := exists_centredCube_of_isBaseChoice (F := stepBlockFrame L n) hL1 hb y
  obtain ⟨z₁, h₁, hz₁⟩ := exists_centredCube_of_isBaseChoice (F := stepBlockFrame L n) hL1 hb
    (y + BlockAverages.unitStep (stepBlockFrame L n).top i)
  have hbig : ∀ k, 2 * ((stepBlockFrame L n).blockSide : ℤ) ≤
      ((stepBlockFrame L n).period (stepBlockFrame L n).depth k : ℤ) := by
    intro k
    show 2 * (L : ℤ) ≤ ((stepBlockFrame L n).period 0 k : ℤ)
    rw [stepBlockFrame_period_zero]
    push_cast
    nlinarith
  have hone : ∀ e ∈ usedContours J₀ h b (y, i),
      ‖((pathHolonomy W (b y) (contourPath b (y, i) e.1 e.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy W' (b y) (contourPath b (y, i) e.1 e.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
        9 * (L : ℝ) * ε := by
    intro e he
    have hξ := mem_centredCube_of_mem_usedContours he
    have hs := contourPath_eq_contourSteps (F := stepBlockFrame L n) hbig (b := b) (y := y) (i := i)
      h₀ h₁ hξ hz₀ hz₁ e.2
    refine (norm_pathHolonomy_sub_le hW _ _).trans ?_
    rw [hs]
    have hl := length_contourSteps_le (L := L) h₀ h₁ hξ e.2 i
    have hl' : (((contourSteps L z₀ z₁ e.1 e.2 i).length : ℕ) : ℝ) ≤ 9 * (L : ℝ) := by exact_mod_cast hl
    exact mul_le_mul_of_nonneg_right hl' hε
  unfold contourMean
  simp only []
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul]
  set U := usedContours J₀ h b (y, i) with hU
  have hsum : ‖∑ e ∈ U, (((pathHolonomy W (b y) (contourPath b (y, i) e.1 e.2) : UnitQuaternion) : ℍ[ℝ]) -
      ((pathHolonomy W' (b y) (contourPath b (y, i) e.1 e.2) : UnitQuaternion) : ℍ[ℝ]))‖ ≤
      (U.card : ℝ) * (9 * (L : ℝ) * ε) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hone).trans ?_
    simp
  have h9 : 0 ≤ 9 * (L : ℝ) * ε := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos U.card with h0 | h0
  · simp [h0, h9]
  · have hc : (0 : ℝ) < U.card := by exact_mod_cast h0
    rw [one_div, inv_mul_le_iff₀ hc]
    exact hsum
open Classical in
theorem stepHotLumps_eq_of_torusHotLumps_eq {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {n : ℕ} [NeZero n]
    {W W' : TorusField (n * ℓ.side)} (h : torusHotLumps ℓ W = torusHotLumps ℓ W') :
    stepHotLumps ℓ W = stepHotLumps ℓ W' := by
  have e : n * ℓ.side / ℓ.side = n := Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne _))
  have key : ∀ m : ℕ, m = n →
      ((hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side m) 0)
          (readAtLevel (stepBlockFrame ℓ.side m) 0 W)).image
        fun l => l.image (toTorusSite (n * ℓ.side))) =
      ((hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side m) 0)
          (readAtLevel (stepBlockFrame ℓ.side m) 0 W')).image
        fun l => l.image (toTorusSite (n * ℓ.side))) →
      hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0)
          (readAtLevel (stepBlockFrame ℓ.side n) 0 W) =
        hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0)
          (readAtLevel (stepBlockFrame ℓ.side n) 0 W') := by
    intro m hmn hh
    subst hmn
    have hinj : Function.Injective
        (toTorusSite (m * ℓ.side) : (stepBlockFrame ℓ.side m).Site 0 → TorusSite (m * ℓ.side)) :=
      fun x y hxy => toTorusSite_injective (fun i => stepBlockFrame_period_zero i) hxy
    exact Finset.image_injective (Finset.image_injective hinj) hh
  exact key _ e h
theorem supDist_add_unitStep_le {n : ℕ} [NeZero n] (h16 : 16 ≤ n) (Y : TorusSite n) (i : Fin 4) :
    TorusFields.supDist (Y + TorusFields.unitStep n i) Y ≤ 16 := by
  unfold TorusFields.supDist
  refine Finset.sup_le fun k _ => ?_
  simp only [Pi.add_apply, add_sub_cancel_left]
  unfold TorusFields.unitStep
  by_cases hk : k = i
  · subst hk
    have h1 : (((1 : ℤ) : ZMod n)).valMinAbs = 1 := ContourOffsets.valMinAbs_intCast_of_small (by
      have : (16 : ℤ) ≤ n := by exact_mod_cast h16
      simp
      omega)
    simp only [Pi.single_eq_same]
    have h2 : ((1 : ZMod n)).valMinAbs = 1 := by simpa using h1
    rw [h2]
    norm_num
  · simp [hk]
theorem coordNorm_toImaginary (z : EuclideanSpace ℝ (Fin 3)) : coordNorm z = ‖z‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
theorem norm_toCoords (w : imaginaryQuaternions) : ‖toCoords w‖ = ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianBound.norm_toCoords <;> assumption
theorem norm_bondFrameCoord_le {F : BlockFrame} (a : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ)
    (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    ‖bondFrameCoord a ρ m b V‖ ≤ ρ := by apply _root_.YangMills.Construction.LogJacobian.norm_bondFrameCoord_le <;> assumption
theorem norm_mul_sub_mul_mul (A G G' B : UnitQuaternion) :
    ‖((A * G * B : UnitQuaternion) : ℍ[ℝ]) - ((A * G' * B : UnitQuaternion) : ℍ[ℝ])‖ =
      ‖(G : ℍ[ℝ]) - (G' : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.BondMeans.norm_mul_mul_sub_mul_mul <;> assumption
section ChartedSetting
variable {R : StepSetup} {n : ℕ}
theorem norm_chartLink_sub_le
    (hsh : ∀ u v : imaginaryQuaternions,
      ‖((expUnit u : UnitQuaternion) : ℍ[ℝ]) - ((expUnit v : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖u - v‖)
    (s : ChartSetting R n) (x : TorusSite (n * R.params.side)) (i : Fin 4) (w w' : imaginaryQuaternions) :
    ‖((chartLink s x i w : UnitQuaternion) : ℍ[ℝ]) - ((chartLink s x i w' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖w - w'‖ := by
  unfold chartLink
  rw [norm_mul_sub_mul_mul]
  split_ifs
  · have e : ((expUnit w * s.coarse (parentBlock R.params.side x) i : UnitQuaternion) : ℍ[ℝ]) -
          ((expUnit w' * s.coarse (parentBlock R.params.side x) i : UnitQuaternion) : ℍ[ℝ]) =
        (((expUnit w : UnitQuaternion) : ℍ[ℝ]) - ((expUnit w' : UnitQuaternion) : ℍ[ℝ])) *
          ((s.coarse (parentBlock R.params.side x) i : UnitQuaternion) : ℍ[ℝ]) := by
      show ((expUnit w : UnitQuaternion) : ℍ[ℝ]) *
          ((s.coarse (parentBlock R.params.side x) i : UnitQuaternion) : ℍ[ℝ]) -
        ((expUnit w' : UnitQuaternion) : ℍ[ℝ]) *
          ((s.coarse (parentBlock R.params.side x) i : UnitQuaternion) : ℍ[ℝ]) = _
      noncomm_ring
    rw [e, norm_mul, norm_unitQuaternion, mul_one]
    exact hsh w w'
  · exact hsh w w'
theorem field_apply_eq_of_ne (s : ChartSetting R n) {η η' : FreeCoords s.free} (b : s.free)
    (he : ∀ b', b' ≠ b → η b' = η' b')
    (x : TorusSite (n * R.params.side)) (i : Fin 4) (hne : (x, i) ≠ b.1) :
    s.field η x i = s.field η' x i := by
  unfold ChartSetting.field
  by_cases h : (x, i) ∈ s.free
  · rw [dif_pos h, dif_pos h, he ⟨(x, i), h⟩ (fun e => hne (congrArg Subtype.val e))]
  · rw [dif_neg h, dif_neg h]
theorem norm_toImaginary_sub (u v : EuclideanSpace ℝ (Fin 3)) :
    ‖toImaginary u - toImaginary v‖ = ‖u - v‖ := by
  have e : toImaginary u - toImaginary v = toImaginary (u - v) := by
    refine Subtype.ext (Quaternion.ext _ _ ?_ ?_ ?_ ?_) <;> simp [toImaginary] <;>
      first | exact sub_zero (0 : ℝ) | rfl
  rw [e, ← coordNorm_toImaginary]
  rfl
theorem norm_field_sub_le
    (hsh : ∀ u v : imaginaryQuaternions,
      ‖((expUnit u : UnitQuaternion) : ℍ[ℝ]) - ((expUnit v : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖u - v‖)
    (s : ChartSetting R n) {η η' : FreeCoords s.free} (b : s.free) (he : ∀ b', b' ≠ b → η b' = η' b')
    (x : TorusSite (n * R.params.side)) (i : Fin 4) :
    ‖((s.field η x i : UnitQuaternion) : ℍ[ℝ]) - ((s.field η' x i : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖η b - η' b‖ := by
  by_cases hne : (x, i) = b.1
  · have h : (x, i) ∈ s.free := hne ▸ b.2
    have hb : (⟨(x, i), h⟩ : s.free) = b := Subtype.ext hne
    unfold ChartSetting.field
    rw [dif_pos h, dif_pos h, hb]
    refine (norm_chartLink_sub_le hsh s x i _ _).trans (le_of_eq ?_)
    rw [add_sub_add_left_eq_sub]
    exact norm_toImaginary_sub _ _
  · rw [field_apply_eq_of_ne s b he x i hne, sub_self, norm_zero]
    exact norm_nonneg _
end ChartedSetting
end LogJacobianSlope
open LogJacobianSlope in
theorem logJacobianSlopeBound_holds (hm : ContourMeanReadsTwoBlocks)
    (hw : WeylIntegrationFormula) (hd : HaarGapDerivBound)
    (hshort : ChartLipschitz.ChartedFieldLipschitz) : LogJacobianSlopeBound := by
  classical
  intro T hT
  obtain ⟨K, hK0, hK⟩ := logPartitionGap_lipschitz_above hw hd
  have hsh := hshort.1
  have hB0 : 0 ≤ 2 * K * (9 * (T.side : ℝ)) := mul_nonneg (mul_nonneg (by norm_num) hK0) (by positivity)
  have hpi2 : 0 < Real.pi ^ 2 := by positivity
  have hCpos : 0 < 8 * (2 * K * (9 * (T.side : ℝ))) + Real.pi ^ 2 + 1 := by linarith
  refine ⟨8 * (2 * K * (9 * (T.side : ℝ))) + Real.pi ^ 2 + 1, 2, hCpos, fun y hy R hR n _ hn s hs b X hX => ?_⟩
  have hL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have haR : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hσR : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hLr : (R.params.side : ℝ) = (T.side : ℝ) := by rw [hL]
  have hx2 : 2 ≤ R.coupling := hy.trans hR.le_coupling
  have ha1 : 1 ≤ R.params.coupling := by rw [haR]; exact hT.a_ge
  have hodd : Odd R.params.side := by rw [hL]; exact hT.L_odd
  have h16 : 16 ≤ n := by
    have := hT.n₀_ge
    omega
  have hρ4 : R.ballRadius = T.ballRadius := by
    show R.params.threshold / 64 = T.threshold / 64
    rw [hσR]
  have hρ0 : 0 < R.ballRadius := by
    rw [hρ4]
    have := hT.σ_pos
    unfold ParameterAssignment.ballRadius
    positivity
  have hρA0 : 0 ≤ R.anchorRadius ∧ R.anchorRadius ≤ 1 := by
    obtain ⟨_, _, _, hρ0', hρ1, _⟩ := hT.chain
    rw [hR.anchorRadius_eq]
    exact ⟨hρ0'.le, hρ1⟩
  have hρle : R.ballRadius ≤ 1 / 2 := by
    have h1 := hT.ρ_le
    obtain ⟨_, _, _, _, hρ1, _, _, hNp, _⟩ := hT.chain
    have h2 := hNp 0
    have h3 := hT.σ_pos
    rw [hρ4]
    nlinarith [mul_pos h2 h3]
  have hline : ∀ τ : ℝ, |τ| ≤ R.ballRadius → s.InBalls (Function.update 0 b (τ • X)) := by
    intro τ hτ b'
    by_cases hb' : b' = b
    · subst hb'
      rw [Function.update_self, coordNorm_toImaginary, norm_smul, hX, mul_one, Real.norm_eq_abs]
      exact hτ
    · rw [Function.update_of_ne hb', coordNorm_toImaginary]
      simpa using hρ0.le
  have hnorm0 : s.InBalls (Function.update 0 b ((0 : ℝ) • X)) := hline 0 (by simpa using hρ0.le)
  have hbases := hs.isBaseChoice
  have hL1 : 1 ≤ (stepBlockFrame R.params.side n).blockSide := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  have hbelow : ∀ y : (stepBlockFrame R.params.side n).Cell, s.bases y ∈ sitesBelow 0 y := by
    intro y
    obtain ⟨z, hz, e⟩ := exists_centredCube_of_isBaseChoice (F := stepBlockFrame R.params.side n) hL1 hbases y
    exact (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff (F := stepBlockFrame R.params.side n) y _).mpr ⟨z, hz, e⟩
  set Bl : TorusSite n := parentBlock R.params.side b.1.1 with hBl
  have hfree : ∀ τ : ℝ, |τ| ≤ R.ballRadius →
      |∑ Y : TorusSite n, s.logJacobianAt Y (Function.update 0 b (τ • X)) -
        ∑ Y : TorusSite n, s.logJacobianAt Y (Function.update 0 b ((0 : ℝ) • X))| ≤
      (8 * (2 * K * (9 * (T.side : ℝ))) + Real.pi ^ 2) * |τ| := by
    intro τ hτ
    set η : FreeCoords s.free := Function.update 0 b (τ • X) with hη
    set η₀ : FreeCoords s.free := Function.update 0 b ((0 : ℝ) • X) with hη₀
    have hin : s.InBalls η := hline τ hτ
    have heq : ∀ b', b' ≠ b → η b' = η₀ b' := by
      intro b' hb'
      rw [hη, hη₀, Function.update_of_ne hb', Function.update_of_ne hb']
    have hdiff : ‖η b - η₀ b‖ = |τ| := by
      rw [hη, hη₀, Function.update_self, Function.update_self, zero_smul, sub_zero, norm_smul, hX, mul_one,
        Real.norm_eq_abs]
    have hotτ : stepHotLumps R.params (s.field η) = stepHotLumps R.params s.fine :=
      stepHotLumps_eq_of_torusHotLumps_eq (hs.hotLumps_eq η hin)
    have hot₀ : stepHotLumps R.params (s.field η₀) = stepHotLumps R.params s.fine :=
      stepHotLumps_eq_of_torusHotLumps_eq (hs.hotLumps_eq η₀ hnorm0)
    have hmove : ∀ c : TorusBond n,
        |meanNorm R.params (s.field η) s.bases c - meanNorm R.params (s.field η₀) s.bases c| ≤
          9 * (T.side : ℝ) * |τ| := by
      intro c
      unfold meanNorm
      rw [hotτ, hot₀, ← hLr]
      refine (abs_norm_sub_norm_le _ _).trans ?_
      refine norm_contourMean_sub_le h16 hbases (abs_nonneg τ) (fun x i => ?_) _
      rw [← hdiff]
      exact norm_field_sub_le hsh s b heq _ i
    have hfar : ∀ (Y : TorusSite n) (i : Fin 4), Y ≠ Bl → Y + TorusFields.unitStep n i ≠ Bl →
        meanNorm R.params (s.field η) s.bases (Y, i) = meanNorm R.params (s.field η₀) s.bases (Y, i) := by
      intro Y i h₁ h₂
      unfold meanNorm
      refine congrArg _ ?_
      refine hm R.params.side n R.params.baseDepth hodd h16 _ _ _ _ _ _ _ i (by rw [hotτ, hot₀])
        (by rw [hotτ, hot₀]) rfl (hbelow _) rfl (hbelow _) ?_
      intro x k hx _
      refine field_apply_eq_of_ne s b heq _ _ ?_
      intro e
      have e₁ : toTorusSite (n * R.params.side) x = b.1.1 := congrArg Prod.fst e
      rcases hx with hx | hx
      · obtain ⟨z, hz, rfl⟩ := (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff (F := stepBlockFrame R.params.side n) _ _).mp hx
        have h3 := parentBlock_siteAtOffset (L := R.params.side) (n := n)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y) hz
        rw [show toTorusSite (n * R.params.side)
          (siteAtOffset (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y) z :
            (stepBlockFrame R.params.side n).Site 0) = b.1.1 from e₁] at h3
        have h₄ : toTorusSite n (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y :
            (stepBlockFrame R.params.side n).Site 1) = Y :=
          toTorusSite_torusSiteInFrame (fun i => stepBlockFrame_period_one i) Y
        exact h₁ (h3.trans h₄).symm
      · obtain ⟨z, hz, rfl⟩ := (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff (F := stepBlockFrame R.params.side n) _ _).mp hx
        have h3 := parentBlock_siteAtOffset (L := R.params.side) (n := n)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y + BlockAverages.unitStep 1 i) hz
        rw [show toTorusSite (n * R.params.side)
          (siteAtOffset (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y + BlockAverages.unitStep 1 i) z :
            (stepBlockFrame R.params.side n).Site 0) = b.1.1 from e₁] at h3
        have h₄ : toTorusSite n ((torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y +
            BlockAverages.unitStep 1 i : (stepBlockFrame R.params.side n).Site 1)) =
            Y + TorusFields.unitStep n i := by
          rw [TopLevelSites.toTorusSite_add (fun i => stepBlockFrame_period_one i),
            toTorusSite_torusSiteInFrame (fun i => stepBlockFrame_period_one i),
            TopLevelSites.toTorusSite_unitStep (fun i => stepBlockFrame_period_one i)]
        exact h₂ (h3.trans h₄).symm
    have hnear : ∀ (Y : TorusSite n) (i : Fin 4), Y = Bl ∨ Y + TorusFields.unitStep n i = Bl →
        |logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i)) -
          logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η₀) s.bases (Y, i))| ≤
          2 * K * (9 * (T.side : ℝ)) * |τ| := by
      intro Y i hY
      have hd16 : TorusFields.supDist Bl Y ≤ 16 := by
        rcases hY with rfl | hY
        · simp [TorusFields.supDist]
        · rw [← hY]
          exact supDist_add_unitStep_le h16 Y i
      have r₁ := hs.half_le_meanNorm η hin b.1 b.2 (Y, i) hd16
      have r₀ := hs.half_le_meanNorm η₀ hnorm0 b.1 b.2 (Y, i) hd16
      have hax : 0 < R.params.coupling * R.coupling := by positivity
      have hm1 : 1 ≤ R.params.coupling * R.coupling / 2 := by nlinarith
      have h1 := hK (R.params.coupling * R.coupling / 2) _ _ hm1 (show R.params.coupling * R.coupling / 2 ≤
        R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i) by nlinarith)
        (show R.params.coupling * R.coupling / 2 ≤
          R.params.coupling * R.coupling * meanNorm R.params (s.field η₀) s.bases (Y, i) by nlinarith)
      refine h1.trans ?_
      rw [← mul_sub, abs_mul, abs_of_pos hax]
      have e : K / (R.params.coupling * R.coupling / 2) * (R.params.coupling * R.coupling *
          |meanNorm R.params (s.field η) s.bases (Y, i) - meanNorm R.params (s.field η₀) s.bases (Y, i)|) =
          2 * K * |meanNorm R.params (s.field η) s.bases (Y, i) -
            meanNorm R.params (s.field η₀) s.bases (Y, i)| := by
        field_simp
      rw [e]
      calc _ ≤ 2 * K * (9 * (T.side : ℝ) * |τ|) :=
            mul_le_mul_of_nonneg_left (hmove _) (mul_nonneg (by norm_num) hK0)
        _ = _ := by ring
    have hbonds : |(∑ Y : TorusSite n, ∑ i : Fin 4,
          logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i))) -
        ∑ Y : TorusSite n, ∑ i : Fin 4,
          logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η₀) s.bases (Y, i))| ≤
        8 * (2 * K * (9 * (T.side : ℝ))) * |τ| := by
      rw [← Finset.sum_sub_distrib]
      simp only [← Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      have hone : ∀ i : Fin 4, |∑ Y : TorusSite n,
          (logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i)) -
            logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η₀) s.bases (Y, i)))| ≤
          2 * (2 * K * (9 * (T.side : ℝ)) * |τ|) := by
        intro i
        have hsub : ∑ Y ∈ ({Bl, Bl - TorusFields.unitStep n i} : Finset (TorusSite n)),
            (logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i)) -
              logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η₀) s.bases (Y, i))) =
            ∑ Y : TorusSite n,
              (logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i)) -
                logPartitionGap (R.params.coupling * R.coupling *
                  meanNorm R.params (s.field η₀) s.bases (Y, i))) := by
          refine Finset.sum_subset (Finset.subset_univ _) fun Y _ hY => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hY
          rw [hfar Y i hY.1 (fun e => hY.2 (eq_sub_of_add_eq e)), sub_self]
        rw [← hsub]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hb : ∀ Y ∈ ({Bl, Bl - TorusFields.unitStep n i} : Finset (TorusSite n)),
            |logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i)) -
              logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η₀) s.bases (Y, i))| ≤
              2 * K * (9 * (T.side : ℝ)) * |τ| := by
          intro Y hY
          simp only [Finset.mem_insert, Finset.mem_singleton] at hY
          refine hnear Y i ?_
          rcases hY with hY | hY
          · exact Or.inl hY
          · exact Or.inr (by rw [hY]; simp)
        refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
        rw [nsmul_eq_mul]
        have hc : ((({Bl, Bl - TorusFields.unitStep n i} : Finset (TorusSite n))).card : ℝ) ≤ 2 := by
          exact_mod_cast Finset.card_le_two
        have h0 : 0 ≤ 2 * K * (9 * (T.side : ℝ)) * |τ| := mul_nonneg hB0 (abs_nonneg τ)
        exact mul_le_mul_of_nonneg_right hc h0
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hone i).trans (le_of_eq ?_)
      simp
      ring
    have hsumB : ∀ ξ : FreeCoords s.free, (∑ Y : TorusSite n, ∑ b' : s.free,
        if bondBlock (R := R) b'.1 = Y then
          Real.log (haarLogDensity (toCoords (s.frame b'.1) + ξ b')) else 0) =
        ∑ b' : s.free, Real.log (haarLogDensity (toCoords (s.frame b'.1) + ξ b')) := by
      intro ξ
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [Finset.sum_ite_eq]
      simp
    have hhaar : |(∑ b' : s.free, Real.log (haarLogDensity (toCoords (s.frame b'.1) + η b'))) -
        ∑ b' : s.free, Real.log (haarLogDensity (toCoords (s.frame b'.1) + η₀ b'))| ≤ Real.pi ^ 2 * |τ| := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single b]
      · have h1 : ‖toCoords (s.frame b.1)‖ ≤ 1 := by
          rw [norm_toCoords]
          have := norm_bondFrameCoord_le (F := torusFrame R.params.side R.depth n) R.params.coupling
            hρA0.1 R.frameReach
            (torusSiteInFrame (torusFrame R.params.side R.depth n)
              (torusFrame R.params.side R.depth n).depth b.1.1, b.1.2)
            (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top s.coarse)
          exact this.trans hρA0.2
        have hball : ∀ ξ : FreeCoords s.free, s.InBalls ξ → ‖toCoords (s.frame b.1) + ξ b‖ ≤ 3 / 2 := by
          intro ξ hξ
          have h2 : ‖ξ b‖ ≤ 1 / 2 := by
            have := hξ b
            rw [coordNorm_toImaginary] at this
            linarith
          calc _ ≤ ‖toCoords (s.frame b.1)‖ + ‖ξ b‖ := norm_add_le _ _
            _ ≤ 3 / 2 := by linarith
        refine (abs_log_haarLogDensity_sub_le _ _ (hball η hin) (hball η₀ hnorm0)).trans (le_of_eq ?_)
        rw [add_sub_add_left_eq_sub, hdiff]
      · intro b' _ hb'
        rw [heq b' hb', sub_self]
      · intro h
        exact absurd (Finset.mem_univ b) h
    have hsplit : ∀ ξ : FreeCoords s.free, ∑ Y : TorusSite n, s.logJacobianAt Y ξ =
        (∑ Y : TorusSite n, ∑ i : Fin 4,
          logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field ξ) s.bases (Y, i))) +
          ∑ b' : s.free, Real.log (haarLogDensity (toCoords (s.frame b'.1) + ξ b')) := by
      intro ξ
      rw [← hsumB ξ, ← Finset.sum_add_distrib]
      rfl
    rw [hsplit η, hsplit η₀]
    have e : ∀ a b c d : ℝ, a + b - (c + d) = (a - c) + (b - d) := fun a b c d => by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [add_mul]
    exact add_le_add hbonds hhaar
  have hlip : ∀ᶠ τ : ℝ in nhds 0,
      ‖(fun τ : ℝ => ∑ Y : TorusSite n, s.logJacobianAt Y (Function.update 0 b (τ • X))) τ -
        (fun τ : ℝ => ∑ Y : TorusSite n, s.logJacobianAt Y (Function.update 0 b (τ • X))) 0‖ ≤
      (8 * (2 * K * (9 * (T.side : ℝ))) + Real.pi ^ 2) * ‖τ - 0‖ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ0] with τ hτ
    have hτ' : |τ| ≤ R.ballRadius := by
      have : |τ| < R.ballRadius := by simpa [Real.dist_eq] using hτ
      exact this.le
    simpa [Real.norm_eq_abs] using hfree τ hτ'
  have hfin := norm_deriv_le_of_lip' (by linarith) hlip
  rw [Real.norm_eq_abs] at hfin
  linarith
end ClusterExpansionOfAStep
end YangMills.Construction
end
