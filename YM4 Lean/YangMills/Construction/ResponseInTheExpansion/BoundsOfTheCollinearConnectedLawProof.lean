import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.DirichletOperator.MapsOfACubeOfTheFirstKindProof
import YangMills.Construction.FourPointCondition.ConnectedLawOfACollinearQuadrupleProof
import YangMills.Construction.ResponseInTheExpansion.TraceOfTheFourPointKernel
import YangMills.Construction.Torus.CollinearQuadruples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open MeasureTheory Set Filter Topology TorusMetric TestFunctions QuadrupleClasses LinearResponse
private theorem sub_eq_intMul_of_torusProj_eq {ℓ : ℝ} {x y : Fin 4 → ℝ} (h : torusProj ℓ x = torusProj ℓ y)
    (j : Fin 4) : ∃ k : ℤ, x j - y j = k * ℓ := by apply _root_.YangMills.Construction.PartitionCubes.FirstTypeMaps.exists_int_mul_of_torusProj_eq <;> assumption
private theorem circleSub_eq_of_congr {ℓ a b a' b' : ℝ} (hℓ : 0 < ℓ) (ha : ∃ k : ℤ, a - a' = k * ℓ)
    (hb : ∃ k : ℤ, b - b' = k * ℓ) (hs : |a' - b'| < ℓ / 2) :
    circleSub ℓ a b = a' - b' := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  have e0 : a - b = (a' - b') + ((p - q : ℤ) : ℝ) * ℓ := by
    push_cast
    linarith
  have e : (a - b) / ℓ = (a' - b') / ℓ + ((p - q : ℤ) : ℝ) := by
    rw [e0]
    field_simp
  have hr : round ((a' - b') / ℓ) = 0 := by
    rw [round_eq_zero_iff]
    have h1 := abs_lt.1 hs
    constructor
    · rw [le_div_iff₀ hℓ]
      linarith
    · rw [div_lt_iff₀ hℓ]
      linarith
  unfold circleSub
  rw [e, round_add_intCast, hr, e0]
  push_cast
  ring
private theorem euclidNormVec_sq (v : Fin 4 → ℝ) : euclidNormVec v ^ 2 = sqNorm v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
private theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
private theorem euclidNormVec_sub_comm (a b : Fin 4 → ℝ) : euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
private theorem euclidNormVec_sub_le (a b c : Fin 4 → ℝ) :
    euclidNormVec (a - c) ≤ euclidNormVec (a - b) + euclidNormVec (b - c) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_le <;> assumption
private theorem euclidNormVec_sub_mem_Icc {A B : Set (Fin 4 → ℝ)} {d : ℝ} (hd : 0 < d)
    (hlow : ENNReal.ofReal d ≤ setDistR4 A B) (hup : setDistR4 A B ≤ ENNReal.ofReal (6 * d))
    {a b ca cb : Fin 4 → ℝ} (hA : A ⊆ closedBallR4 ca (d / 16)) (hB : B ⊆ closedBallR4 cb (d / 16))
    (ha : a ∈ A) (hb : b ∈ B) : d ≤ euclidNormVec (a - b) ∧ euclidNormVec (a - b) ≤ 25 / 4 * d := by
  constructor
  · have h1 : setDistR4 A B ≤ ENNReal.ofReal (euclidNormVec (a - b)) :=
      iInf₂_le_of_le a ha (iInf₂_le b hb)
    exact (ENNReal.ofReal_le_ofReal_iff (euclidNormVec_nonneg _)).1 (hlow.trans h1)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hlt : setDistR4 A B < ENNReal.ofReal (6 * d + ε) :=
      lt_of_le_of_lt hup ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
    unfold setDistR4 at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨a', ha', b', hb', hab⟩ := hlt
    have hab' : euclidNormVec (a' - b') < 6 * d + ε :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hab
    have h1 : euclidNormVec (a - ca) ≤ d / 16 := hA ha
    have h2 : euclidNormVec (a' - ca) ≤ d / 16 := hA ha'
    have h3 : euclidNormVec (b' - cb) ≤ d / 16 := hB hb'
    have h4 : euclidNormVec (b - cb) ≤ d / 16 := hB hb
    have t1 := euclidNormVec_sub_le a ca a'
    have t2 := euclidNormVec_sub_le a a' b
    have t3 := euclidNormVec_sub_le a' b' b
    have t4 := euclidNormVec_sub_le b' cb b
    rw [euclidNormVec_sub_comm ca a'] at t1
    rw [euclidNormVec_sub_comm cb b] at t4
    linarith
private theorem traceAlongCycle_eq_trace_four (ℓ : ℝ) (u : Fin 4 → Fin 4 → ℝ) (σ : Equiv.Perm (Fin 4)) :
    traceAlongCycle (q := 3) ℓ u σ =
      Matrix.trace (planeKernelMatrix (periodicDisplacement ℓ (u (σ (finRotate 4 0))) (u (σ 0))) *
        planeKernelMatrix (periodicDisplacement ℓ (u (σ (finRotate 4 1))) (u (σ 1))) *
        planeKernelMatrix (periodicDisplacement ℓ (u (σ (finRotate 4 2))) (u (σ 2))) *
        planeKernelMatrix (periodicDisplacement ℓ (u (σ (finRotate 4 3))) (u (σ 3)))) := by
  unfold traceAlongCycle
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Matrix.mul_assoc]
  rfl
private theorem traceAlongCycle_mem_bounds (hT : fourPointKernelTraceStatement) {ℓ d : ℝ} (hd : 0 < d)
    (hℓ : 40 * d ≤ ℓ) {e : Fin 4 → ℝ} (he : euclidNormVec e = 1) {u v : Fin 4 → Fin 4 → ℝ}
    (hcov : ∀ i, torusProj ℓ (u i) = torusProj ℓ (v i))
    (hdist : ∀ i j, i ≠ j → d ≤ euclidNormVec (v i - v j) ∧ euclidNormVec (v i - v j) ≤ 25 / 4 * d)
    (hsh : ∀ i j, i ≠ j → euclidNormVec ((v i - v j) - dotProduct (v i - v j) e • e) ≤
      1 / 8 * euclidNormVec (v i - v j))
    (σ : Equiv.Perm (Fin 4)) :
    3 / Real.pi ^ 8 * ((25 / 4 * d) ^ 16)⁻¹ ≤ traceAlongCycle (q := 3) ℓ u σ ∧
      traceAlongCycle (q := 3) ℓ u σ ≤ 6 / Real.pi ^ 8 * (d ^ 16)⁻¹ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hrot : ∀ i : Fin 4, i ≠ finRotate 4 i := by decide
  have hne : ∀ i : Fin 4, σ i ≠ σ (finRotate 4 i) := fun i h => hrot i (σ.injective h)
  set z : Fin 4 → Fin 4 → ℝ := fun i => periodicDisplacement ℓ (u (σ (finRotate 4 i))) (u (σ i)) with hz
  have hzv : ∀ i, z i = v (σ i) - v (σ (finRotate 4 i)) := by
    intro i
    funext j
    have hb := (hdist _ _ (hne i)).2
    have hj : |(v (σ i) - v (σ (finRotate 4 i))) j| ≤ _ := abs_apply_le_euclidNormVec _ j
    exact circleSub_eq_of_congr hℓ0 (sub_eq_intMul_of_torusProj_eq (hcov _) j)
      (sub_eq_intMul_of_torusProj_eq (hcov _) j)
      (by simp only [Pi.sub_apply] at hj; linarith)
  have hsum : ∑ i, z i = 0 := by
    have h1 : ∑ i, v (σ (finRotate 4 i)) = ∑ i, v (σ i) :=
      Equiv.sum_comp (finRotate 4) fun i => v (σ i)
    simp only [hzv, Finset.sum_sub_distrib, h1, sub_self]
  have hsq : ∀ i, d ^ 2 ≤ sqNorm (z i) ∧ sqNorm (z i) ≤ (25 / 4 * d) ^ 2 := by
    intro i
    rw [← euclidNormVec_sq, hzv]
    obtain ⟨h1, h2⟩ := hdist _ _ (hne i)
    exact ⟨pow_le_pow_left₀ hd.le h1 2, pow_le_pow_left₀ (euclidNormVec_nonneg _) h2 2⟩
  have hunit : sqNorm e = 1 := by
    rw [← euclidNormVec_sq, he]
    norm_num
  have hangle : ∀ i, (1 - (1 / 8 : ℝ) ^ 2) * sqNorm (z i) ≤ euclideanInner (z i) e ^ 2 := by
    intro i
    have h1 := hsh _ _ (hne i)
    rw [← hzv] at h1
    have h2 : sqNorm (z i - dotProduct (z i) e • e) ≤ (1 / 8) ^ 2 * sqNorm (z i) := by
      rw [← euclidNormVec_sq, ← euclidNormVec_sq, ← mul_pow]
      exact pow_le_pow_left₀ (euclidNormVec_nonneg _) h1 2
    have h3 : sqNorm (z i - dotProduct (z i) e • e) = sqNorm (z i) - euclideanInner (z i) e ^ 2 := by
      have hd' : dotProduct (z i) e = euclideanInner (z i) e := rfl
      rw [hd']
      set p := euclideanInner (z i) e with hp
      have hp' : ∑ μ, z i μ * e μ = p := rfl
      have hu' : ∑ μ, e μ ^ 2 = 1 := hunit
      unfold sqNorm
      have : ∀ μ, (z i - p • e) μ ^ 2 = z i μ ^ 2 - 2 * p * (z i μ * e μ) + p ^ 2 * e μ ^ 2 := by
        intro μ
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp', hu']
      ring
    rw [h3] at h2
    linarith
  have hpos : ∀ i, 0 < sqNorm (z i) := fun i =>
    lt_of_lt_of_le (by positivity) (hsq i).1
  obtain ⟨hlo, hhi⟩ := hT z e hunit hsum hpos hangle
  have hprodlo : ((25 / 4 * d) ^ 16)⁻¹ ≤ ∏ i, (sqNorm (z i) ^ 2)⁻¹ := by
    have hc : ((25 / 4 * d) ^ 16)⁻¹ = ∏ _i : Fin 4, ((25 / 4 * d) ^ 4)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, ← pow_mul]
    rw [hc]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_
    refine inv_anti₀ (pow_pos (hpos i) 2) ?_
    calc sqNorm (z i) ^ 2 ≤ ((25 / 4 * d) ^ 2) ^ 2 := pow_le_pow_left₀ (hpos i).le (hsq i).2 2
      _ = (25 / 4 * d) ^ 4 := by ring
  have hprodhi : ∏ i, (sqNorm (z i) ^ 2)⁻¹ ≤ (d ^ 16)⁻¹ := by
    have hc : (d ^ 16)⁻¹ = ∏ _i : Fin 4, (d ^ 4)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, ← pow_mul]
    rw [hc]
    refine Finset.prod_le_prod (fun i _ => inv_nonneg.2 (pow_nonneg (hpos i).le 2)) fun i _ => ?_
    refine inv_anti₀ (by positivity) ?_
    calc d ^ 4 = (d ^ 2) ^ 2 := by ring
      _ ≤ sqNorm (z i) ^ 2 := pow_le_pow_left₀ (by positivity) (hsq i).1 2
  rw [traceAlongCycle_eq_trace_four]
  constructor
  · exact (mul_le_mul_of_nonneg_left hprodlo (by positivity)).trans hlo
  · exact hhi.trans (mul_le_mul_of_nonneg_left hprodhi (by positivity))
private theorem continuous_comp_torusProj {ℓ : ℝ} {h : Torus4 ℓ → ℝ}
    (hh : IsLipschitzFor (euclidDistTorus (ℓ := ℓ)) h) : Continuous fun x => h (torusProj ℓ x) := by apply _root_.YangMills.SharedProofs.p11913 <;> assumption
private theorem closedBallR4_subset_closedBall (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    closedBallR4 c r ⊆ Metric.closedBall c r := by
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hr]
  intro j
  have h1 : |(x - c) j| ≤ euclidNormVec (x - c) := abs_apply_le_euclidNormVec _ j
  have h2 : euclidNormVec (x - c) ≤ r := hx
  rw [Real.dist_eq]
  simpa using h1.trans h2
abbrev _root_.YangMills.SharedProofs.p71595 := @closedBallR4_subset_closedBall
private theorem exists_bound_of_support_image_ball {ℓ r : ℝ} (hr : 0 ≤ r) {c : Fin 4 → ℝ}
    {h : Torus4 ℓ → ℝ} (hc : Continuous fun x => h (torusProj ℓ x))
    (hs : ∀ y, h y ≠ 0 → y ∈ torusProj ℓ '' closedBallR4 c r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖h y‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : h y = 0
  · rw [hy, norm_zero]
    exact le_max_right _ _
  · obtain ⟨v, hv, rfl⟩ := hs y hy
    exact (hC v (closedBallR4_subset_closedBall c hr hv)).trans (le_max_left _ _)
private theorem measurable_traceAlongCycle (ℓ : ℝ) (σ : Equiv.Perm (Fin 4)) :
    Measurable fun u : Fin 4 → Fin 4 → ℝ => traceAlongCycle (q := 3) ℓ u σ := by apply _root_.YangMills.SharedProofs.p77237 <;> assumption
private theorem setIntegral_prod_mul_mem_bounds {Q : Set (Fin 4 → ℝ)} (hQf : volume Q ≠ ⊤)
    {F : Fin 4 → (Fin 4 → ℝ) → ℝ} (hFm : ∀ i, Measurable (F i)) (hF0 : ∀ i x, 0 ≤ F i x)
    {M : Fin 4 → ℝ} (hFM : ∀ i x, F i x ≤ M i) {t : (Fin 4 → Fin 4 → ℝ) → ℝ} (ht : Measurable t)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hb : ∀ u, (∀ i, F i (u i) ≠ 0) → lo ≤ t u ∧ t u ≤ hi) :
    lo * ∏ i, ∫ x in Q, F i x ≤ ∫ u in Set.pi univ (fun _ : Fin 4 => Q), (∏ i, F i (u i)) * t u ∧
      ∫ u in Set.pi univ (fun _ : Fin 4 => Q), (∏ i, F i (u i)) * t u ≤ hi * ∏ i, ∫ x in Q, F i x := by
  set P : (Fin 4 → Fin 4 → ℝ) → ℝ := fun u => ∏ i, F i (u i) with hP
  have hP0 : ∀ u, 0 ≤ P u := fun u => Finset.prod_nonneg fun i _ => hF0 i _
  have hPm : Measurable P :=
    Finset.measurable_prod _ fun i _ => (hFm i).comp (measurable_pi_apply i)
  have hPb : ∀ u, P u ≤ ∏ i, M i := fun u =>
    Finset.prod_le_prod (fun i _ => hF0 i _) fun i _ => hFM i _
  have hbet : ∀ u, lo * P u ≤ P u * t u ∧ P u * t u ≤ hi * P u := by
    intro u
    by_cases hz : ∀ i, F i (u i) ≠ 0
    · obtain ⟨h1, h2⟩ := hb u hz
      constructor
      · rw [mul_comm]
        exact mul_le_mul_of_nonneg_left h1 (hP0 u)
      · rw [mul_comm hi]
        exact mul_le_mul_of_nonneg_left h2 (hP0 u)
    · obtain ⟨i, hi'⟩ := not_forall.1 hz
      have hi' := not_not.1 hi'
      have : P u = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi'
      simp [this]
  have hfin : volume (Set.pi univ fun _ : Fin 4 => Q) ≠ ⊤ := by
    rw [volume_pi_pi]
    exact ENNReal.prod_ne_top fun _ _ => hQf
  have hPi : IntegrableOn P (Set.pi univ fun _ : Fin 4 => Q) volume := by
    refine Measure.integrableOn_of_bounded (M := ∏ i, M i) hfin hPm.aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (hP0 u)]
    exact hPb u
  have hlop : IntegrableOn (fun u => lo * P u) (Set.pi univ fun _ : Fin 4 => Q) volume :=
    hPi.const_mul lo
  have hhip : IntegrableOn (fun u => hi * P u) (Set.pi univ fun _ : Fin 4 => Q) volume :=
    hPi.const_mul hi
  have hPt : IntegrableOn (fun u => P u * t u) (Set.pi univ fun _ : Fin 4 => Q) volume := by
    refine Integrable.mono' hhip (hPm.mul ht).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    have h0 : 0 ≤ P u * t u := (mul_nonneg hlo (hP0 u)).trans (hbet u).1
    rw [Real.norm_of_nonneg h0]
    exact (hbet u).2
  have hprod : ∫ u in Set.pi univ (fun _ : Fin 4 => Q), P u = ∏ i, ∫ x in Q, F i x := by
    rw [volume_pi, Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (fun i => F i)
  constructor
  · rw [← hprod, ← integral_const_mul]
    exact integral_mono hlop hPt fun u => (hbet u).1
  · rw [← hprod, ← integral_const_mul]
    exact integral_mono hPt hhip fun u => (hbet u).2
private theorem card_perm_fix_zero_of_decide :
    (Finset.univ.filter fun s : Equiv.Perm (Fin 4) => s 0 = 0).card = 6 := by
  decide
private theorem card_perm_fix_zero (inst : DecidablePred fun s : Equiv.Perm (Fin 4) => s 0 = 0) :
    (@Finset.filter _ (fun s : Equiv.Perm (Fin 4) => s 0 = 0) inst Finset.univ).card = 6 := by
  convert card_perm_fix_zero_of_decide
theorem collinearCumulantBounds_holds (hT : fourPointKernelTraceStatement)
    (hC : Collinear.CollinearQuadruplesStatement) : collinearCumulantBoundsStatement := by
  intro s d ϑ f hf
  obtain ⟨hQ, g, ⟨-, c, hsupp, hg⟩, ⟨hgQ, c', ⟨e, he⟩, hball⟩⟩ := hf
  obtain ⟨hsc, h40, hfL, hpairs⟩ := hQ
  have hd : 0 < d := hsc.1
  have hϑ : 0 < ϑ := hsc.2.1
  set ℓ : ℝ := PeriodicLattice.torusSide s.L s.m with hℓdef
  have hsh : IsShapeAxis e g := (hC.2.2 d ϑ hsc).1 g e c' hgQ he hball
  obtain ⟨-, -, -, -, -, hTor⟩ := hC.2.2 d ϑ hsc
  obtain ⟨-, hInt, -⟩ := hTor s h40
  obtain ⟨-, -, hgp⟩ := hgQ
  have hpt : ∀ i (w : Fin 4 → ℝ), f i (torusProj ℓ w) ≠ 0 →
      ∃ v, torusProj ℓ w = torusProj ℓ v ∧ v ∈ PlaquetteSupports.euclideanTSupport (g i) := by
    intro i w hw
    obtain ⟨v, hv, hvw⟩ := hsupp i (subset_tsupport _ hw)
    refine ⟨v, hvw.symm, subset_tsupport _ ?_⟩
    have hvw' : torusProj ℓ v = torusProj ℓ w := hvw
    have : g i v = f i (torusProj ℓ w) := by
      rw [hg i, ballLift, Set.indicator_of_mem hv, Function.comp_apply]
      exact congrArg (f i) hvw'
    rw [Function.mem_support, this]
    exact hw
  set F : Fin 4 → (Fin 4 → ℝ) → ℝ := fun i x => f i (torusProj ℓ x) with hF
  have hFc : ∀ i, Continuous (F i) := fun i => continuous_comp_torusProj (hfL i).1
  have hFm : ∀ i, Measurable (F i) := fun i => (hFc i).measurable
  have hF0 : ∀ i x, 0 ≤ F i x := fun i x => (hfL i).2 _
  have hbd : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖f i y‖ ≤ M := fun i =>
    exists_bound_of_support_image_ball (by positivity : (0 : ℝ) ≤ 9 * d) (hFc i)
      fun y hy => hsupp i (subset_tsupport _ hy)
  have hlesup : ∀ i y, f i y ≤ uniformNorm (f i) := by
    intro i y
    obtain ⟨M, -, hM⟩ := hbd i
    exact (le_abs_self _).trans (le_ciSup (f := fun y => ‖f i y‖) ⟨M, by rintro _ ⟨y, rfl⟩; exact hM y⟩ y)
  have hsup0 : ∀ i, 0 ≤ uniformNorm (f i) := fun i => Real.iSup_nonneg fun _ => norm_nonneg _
  set Qc : Set (Fin 4 → ℝ) := Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ with hQc
  set I : Fin 4 → ℝ := fun i => ∫ x in Qc, F i x with hI
  have hne : ∀ i : Fin 4, i ≠ i + 1 := by decide
  have hIlow : ∀ i, ϑ * uniformNorm (f i) * d ^ 4 ≤ I i := by
    intro i
    obtain ⟨x₁, x₂, hb₁, -, -, -⟩ := hpairs i (i + 1) (hne i)
    exact hb₁.2.2.2.2.1
  have hIup : ∀ i, I i ≤ TorusMeasure.omega4 * (d / 16) ^ 4 * uniformNorm (f i) := by
    intro i
    obtain ⟨M, -, hM⟩ := hbd i
    refine hInt (f i) (torusProj ℓ (c' i)) ⟨M, hM⟩ (hFm i).nullMeasurable fun u hu => ?_
    by_contra hne'
    obtain ⟨v, hv, rfl⟩ := hsupp i (subset_tsupport _ hne')
    obtain ⟨v₂, hv₂, hs₂⟩ := hpt i v hne'
    refine hu ?_
    have hvc : euclidNormVec (v₂ - c' i) ≤ d / 16 := hball i hs₂
    have e1 : TorusMeasure.proj s v - torusProj ℓ (c' i) = torusProj ℓ (v₂ - c' i) := by
      have : TorusMeasure.proj s v = torusProj ℓ v₂ := hv₂
      rw [this]
      funext μ
      simp [torusProj]
    change torusEuclidNorm (TorusMeasure.proj s v - torusProj ℓ (c' i)) ≤ d / 16
    rw [e1]
    exact (AmbientPoints.torusEuclidNorm_torusProj_le _).trans hvc
  have hI0 : ∀ i, 0 ≤ I i := fun i =>
    (by have := hsup0 i; positivity : 0 ≤ ϑ * uniformNorm (f i) * d ^ 4).trans (hIlow i)
  have hQf : volume Qc ≠ ⊤ := by
    rw [hQc, Real.volume_pi_Ico]
    exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  have hcycle : ∀ σ : Equiv.Perm (Fin 4),
      3 / Real.pi ^ 8 * ((25 / 4 * d) ^ 16)⁻¹ * ∏ i, I i ≤
        ∫ u in Set.pi univ (fun _ : Fin 4 => Qc), (∏ i, F i (u i)) * traceAlongCycle (q := 3) ℓ u σ ∧
      ∫ u in Set.pi univ (fun _ : Fin 4 => Qc), (∏ i, F i (u i)) * traceAlongCycle (q := 3) ℓ u σ ≤
        6 / Real.pi ^ 8 * (d ^ 16)⁻¹ * ∏ i, I i := by
    intro σ
    refine setIntegral_prod_mul_mem_bounds hQf hFm hF0 (M := fun i => uniformNorm (f i))
      (fun i x => hlesup i _) (measurable_traceAlongCycle ℓ σ) (by positivity) fun u hu => ?_
    choose v hv₁ hv₂ using fun i => hpt i (u i) (hu i)
    have hdist : ∀ i j, i ≠ j → d ≤ euclidNormVec (v i - v j) ∧ euclidNormVec (v i - v j) ≤ 25 / 4 * d := by
      intro i j hij
      obtain ⟨x₁, x₂, -, -, hl, hh⟩ := hgp i j hij
      exact euclidNormVec_sub_mem_Icc hd hl hh (hball i) (hball j) (hv₂ i) (hv₂ j)
    exact traceAlongCycle_mem_bounds hT hd h40 he.1 hv₁ hdist
      (fun i j hij => hsh.2 i j hij _ (hv₂ i) _ (hv₂ j)) σ
  have hcard := card_perm_fix_zero
  have hLaw : gaussianCumulantLimit (q := 3) ℓ f = (3 / 2) * ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))).filter
      (fun σ => σ 0 = 0),
      ∫ u in Set.pi univ (fun _ : Fin 4 => Qc), (∏ i, F i (u i)) * traceAlongCycle (q := 3) ℓ u σ := rfl
  have hπ : Real.pi ^ (-8 : ℤ) = (Real.pi ^ 8)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have h25 : (25 / 4 : ℝ) ^ (-16 : ℤ) = ((25 / 4 : ℝ) ^ 16)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have h16 : (16 : ℝ) ^ (-16 : ℤ) = ((16 : ℝ) ^ 16)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hprodlow : ϑ ^ 4 * (∏ i, uniformNorm (f i)) * d ^ 16 ≤ ∏ i, I i := by
    have e1 : ϑ ^ 4 * (∏ i, uniformNorm (f i)) * d ^ 16 = ∏ i, (ϑ * uniformNorm (f i) * d ^ 4) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    rw [e1]
    exact Finset.prod_le_prod (fun i _ => by have := hsup0 i; positivity) fun i _ => hIlow i
  have hprodup : ∏ i, I i ≤
      TorusMeasure.omega4 ^ 4 * (d ^ 16 * ((16 : ℝ) ^ 16)⁻¹) * ∏ i, uniformNorm (f i) := by
    have e1 : TorusMeasure.omega4 ^ 4 * (d ^ 16 * ((16 : ℝ) ^ 16)⁻¹) * ∏ i, uniformNorm (f i) =
        ∏ i, (TorusMeasure.omega4 * (d / 16) ^ 4 * uniformNorm (f i)) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      field_simp
    rw [e1]
    exact Finset.prod_le_prod (fun i _ => hI0 i) fun i _ => hIup i
  have hsum : ∀ σset : Finset (Equiv.Perm (Fin 4)), σset.card = 6 →
      6 * (3 / Real.pi ^ 8 * ((25 / 4 * d) ^ 16)⁻¹ * ∏ i, I i) ≤
        ∑ σ ∈ σset, ∫ u in Set.pi univ (fun _ : Fin 4 => Qc), (∏ i, F i (u i)) * traceAlongCycle (q := 3) ℓ u σ ∧
      ∑ σ ∈ σset, ∫ u in Set.pi univ (fun _ : Fin 4 => Qc), (∏ i, F i (u i)) * traceAlongCycle (q := 3) ℓ u σ ≤
        6 * (6 / Real.pi ^ 8 * (d ^ 16)⁻¹ * ∏ i, I i) := by
    intro σset hσ
    constructor
    · refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun σ _ => (hcycle σ).1)
      rw [Finset.sum_const, hσ, nsmul_eq_mul]
      try norm_num
    · refine le_trans (Finset.sum_le_sum fun σ _ => (hcycle σ).2) (le_of_eq ?_)
      rw [Finset.sum_const, hσ, nsmul_eq_mul]
      try norm_num
  obtain ⟨hs1, hs2⟩ := hsum _ (hcard _)
  rw [hLaw, hπ, h25, h16]
  constructor
  · have h1 : 27 * (Real.pi ^ 8)⁻¹ * ((25 / 4 : ℝ) ^ 16)⁻¹ * ϑ ^ 4 * ∏ i, uniformNorm (f i) =
        (3 / 2) * (6 * (3 / Real.pi ^ 8 * ((25 / 4 * d) ^ 16)⁻¹ *
          (ϑ ^ 4 * (∏ i, uniformNorm (f i)) * d ^ 16))) := by
      rw [mul_pow]
      field_simp
      ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hs1) (by norm_num)
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_left hprodlow (by positivity)
  · have h1 : 54 * (Real.pi ^ 8)⁻¹ * TorusMeasure.omega4 ^ 4 * ((16 : ℝ) ^ 16)⁻¹ * ∏ i, uniformNorm (f i) =
        (3 / 2) * (6 * (6 / Real.pi ^ 8 * (d ^ 16)⁻¹ *
          (TorusMeasure.omega4 ^ 4 * (d ^ 16 * ((16 : ℝ) ^ 16)⁻¹) * ∏ i, uniformNorm (f i)))) := by
      field_simp
      ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left (le_trans hs2 ?_) (by norm_num)
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_left hprodup (by positivity)
end YangMills.Construction.ResponseInTheExpansion
end
