import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.PassageToTheLimit.MovingAMirrorIsTranslatingTheImageProof
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
open Set YangMills.Construction.TorusMetric YangMills.Construction.MetricNotions YangMills.Construction.FamilyTopology
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
namespace AmbientMetric
theorem euclidNormVec_eq_norm (v : Fin 4 → ℝ) :
    euclidNormVec v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by
  simp only [euclidNormVec_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by
  simp [euclidNormVec]
theorem euclidNormVec_zero : euclidNormVec 0 = 0 := by
  simp [euclidNormVec]
theorem norm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
theorem eq_zero_of_euclidNormVec_eq_zero {v : Fin 4 → ℝ} (h : euclidNormVec v = 0) : v = 0 := by
  have := norm_le_euclidNormVec v
  rw [h] at this
  exact norm_le_zero_iff.mp this
theorem abs_inner_le_euclidNormVec_mul (u v : Fin 4 → ℝ) :
    |∑ i, u i * v i| ≤ euclidNormVec u * euclidNormVec v := by
  rw [abs_le]
  constructor
  · have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => -u i) v
    simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at h
    have : -(euclidNormVec u * euclidNormVec v) ≤ ∑ i, u i * v i := by
      simp only [euclidNormVec]
      linarith
    exact this
  · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v
theorem exists_minimal_lift_torus {L : ℝ} (x : Torus4 L) :
    ∃ b : Fin 4 → ℝ, torusProj L b = x ∧
      ∀ v, torusProj L v = x → euclidNormVec b ≤ euclidNormVec v := by
  choose b hb hb' using fun i => exists_coe_eq_abs_eq_norm (x i)
  refine ⟨b, funext hb, fun v hv => Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)⟩
  rw [← sq_abs (b i), ← sq_abs (v i), hb' i]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have : x i = ((v i : ℝ) : AddCircle L) := (congrFun hv i).symm
  rw [this]
  exact addCircle_norm_coe_le_abs _
variable (s : Conventions.StandingParameters) (E : Ambient)
theorem proj_eq_of_isLiftOf {x : E.Carrier s} {y : Fin 4 → ℝ} (h : E.IsLiftOf s x y) :
    E.proj s y = x := h
theorem exists_minimal_lift (x : E.Carrier s) :
    ∃ b : Fin 4 → ℝ, E.IsLiftOf s x b ∧ E.euclidLength s x = euclidNormVec b ∧
      ∀ v, E.IsLiftOf s x v → euclidNormVec b ≤ euclidNormVec v := by
  cases E with
  | euclidean =>
    refine ⟨x, rfl, rfl, fun v hv => ?_⟩
    have : v = x := hv
    rw [this]
  | periodic =>
    obtain ⟨b, hb, hmin⟩ := exists_minimal_lift_torus (L := s.side) x
    refine ⟨b, hb, ?_, hmin⟩
    have hl : IsLeast (euclidNormVec '' (torusProj s.side ⁻¹' {x})) (euclidNormVec b) :=
      ⟨⟨b, hb, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact hmin v hv⟩
    exact hl.csInf_eq
theorem euclidLength_le {x : E.Carrier s} {v : Fin 4 → ℝ} (hv : E.IsLiftOf s x v) :
    E.euclidLength s x ≤ euclidNormVec v := by
  obtain ⟨b, -, hb, hmin⟩ := exists_minimal_lift s E x
  rw [hb]
  exact hmin v hv
theorem proj_zero : E.proj s 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.MirrorTranslation.proj_zero_eq <;> assumption
theorem euclidLength_nonneg (x : E.Carrier s) : 0 ≤ E.euclidLength s x := by
  obtain ⟨b, -, hb, -⟩ := exists_minimal_lift s E x
  rw [hb]
  exact euclidNormVec_nonneg b
theorem euclidLength_zero : E.euclidLength s 0 = 0 :=
  le_antisymm (by simpa [euclidNormVec_zero] using euclidLength_le s E (proj_zero s E))
    (euclidLength_nonneg s E 0)
theorem eq_zero_of_euclidLength_eq_zero {x : E.Carrier s} (h : E.euclidLength s x = 0) :
    x = 0 := by
  obtain ⟨b, hl, hb, -⟩ := exists_minimal_lift s E x
  rw [h] at hb
  have : b = 0 := eq_zero_of_euclidNormVec_eq_zero hb.symm
  rw [← proj_eq_of_isLiftOf s E hl, this, proj_zero s E]
theorem euclidLength_neg_le (x : E.Carrier s) : E.euclidLength s (-x) ≤ E.euclidLength s x := by
  obtain ⟨b, hl, hb, -⟩ := exists_minimal_lift s E x
  have : E.IsLiftOf s (-x) (-b) := by
    rw [Ambient.IsLiftOf, E.proj_neg s, proj_eq_of_isLiftOf s E hl]
  rw [hb, ← euclidNormVec_neg]
  exact euclidLength_le s E this
theorem euclidLength_neg (x : E.Carrier s) : E.euclidLength s (-x) = E.euclidLength s x :=
  le_antisymm (euclidLength_neg_le s E x) (by simpa using euclidLength_neg_le s E (-x))
theorem euclidLength_add_le (x y : E.Carrier s) :
    E.euclidLength s (x + y) ≤ E.euclidLength s x + E.euclidLength s y := by
  obtain ⟨a, ha, ha', -⟩ := exists_minimal_lift s E x
  obtain ⟨b, hb, hb', -⟩ := exists_minimal_lift s E y
  have : E.IsLiftOf s (x + y) (a + b) := by
    rw [Ambient.IsLiftOf, E.proj_add s, proj_eq_of_isLiftOf s E ha, proj_eq_of_isLiftOf s E hb]
  rw [ha', hb']
  exact (euclidLength_le s E this).trans (euclidNormVec_add_le a b)
theorem pointDist_isMetricFunction : IsMetricFunction (E.pointDist s) where
  nonneg x y := euclidLength_nonneg s E _
  eq_zero_iff x y := by
    constructor
    · intro h
      exact sub_eq_zero.mp (eq_zero_of_euclidLength_eq_zero s E h)
    · rintro rfl
      simp [Ambient.pointDist, euclidLength_zero s E]
  symm x y := by
    rw [Ambient.pointDist, ← neg_sub, euclidLength_neg s E]
    rfl
  triangle x y z := by
    have := euclidLength_add_le s E (x - y) (y - z)
    simpa [Ambient.pointDist] using this
theorem pointDist_proj_le (x y : Fin 4 → ℝ) :
    E.pointDist s (E.proj s x) (E.proj s y) ≤ euclidNormVec (x - y) := by
  apply euclidLength_le s E
  rw [Ambient.IsLiftOf, sub_eq_add_neg, E.proj_add s, E.proj_neg s, sub_eq_add_neg]
theorem exists_lift_at_pointDist (x y : E.Carrier s) {u : Fin 4 → ℝ} (hu : E.IsLiftOf s x u) :
    ∃ w : Fin 4 → ℝ, E.IsLiftOf s y w ∧ euclidNormVec (u - w) = E.pointDist s x y := by
  obtain ⟨b, hb, hb', -⟩ := exists_minimal_lift s E (x - y)
  refine ⟨u - b, ?_, ?_⟩
  · rw [Ambient.IsLiftOf, sub_eq_add_neg, E.proj_add s, E.proj_neg s, proj_eq_of_isLiftOf s E hu,
      proj_eq_of_isLiftOf s E hb]
    abel
  · rw [Ambient.pointDist, hb']
    simp
theorem euclidDistFacts_holds :
    EuclidDistFacts s E := by
  refine ⟨fun x y => ⟨?_, pointDist_proj_le s E x y⟩, pointDist_isMetricFunction s E, ?_, ?_, ?_⟩
  · obtain ⟨w, hw, hw'⟩ := exists_lift_at_pointDist s E (E.proj s x) (E.proj s y)
      (u := x) rfl
    constructor
    · refine ⟨w - y, E.sub_mem_periodGroup s hw, ?_⟩
      have e : x - y - (w - y) = x - w := by abel
      simpa only [e] using hw'
    · rintro _ ⟨γ, hγ, rfl⟩
      have h0 := (E.mem_periodGroup_iff s γ).mp hγ
      have : E.proj s (y + γ) = E.proj s y := by
        rw [E.proj_add s, h0, add_zero]
      rw [← this]
      have h := pointDist_proj_le s E x (y + γ)
      have e : x - (y + γ) = x - y - γ := by abel
      rwa [e] at h
  · intro x y z
    simp [Ambient.pointDist]
  · intro x y u hu
    exact exists_lift_at_pointDist s E x y hu
  · intro x ε hε
    refine ⟨ε, hε, fun y hy => ?_⟩
    have h := pointDist_proj_le s E x y
    exact lt_of_le_of_lt h hy
section Generic
variable {X : Type*} {d : X → X → ℝ}
@[reducible] def metricSpaceOfMetricFunction (hd : IsMetricFunction d) : MetricSpace X where
  dist := d
  dist_self x := (hd.eq_zero_iff x x).mpr rfl
  dist_comm := hd.symm
  dist_triangle := hd.triangle
  eq_of_dist_eq_zero h := (hd.eq_zero_iff _ _).mp h
theorem isOpenWrt_iff_isOpen (hd : IsMetricFunction d) (U : Set X) :
    letI := metricSpaceOfMetricFunction hd
    IsOpenWrt d U ↔ IsOpen U := by
  let _ := metricSpaceOfMetricFunction hd
  rw [Metric.isOpen_iff]
  constructor
  · intro h x hx
    obtain ⟨r, hr, hy⟩ := h x hx
    refine ⟨r, hr, fun y hy' => hy y ?_⟩
    have h1 : d y x < r := hy'
    rwa [hd.symm]
  · intro h x hx
    obtain ⟨r, hr, hy⟩ := h x hx
    refine ⟨r, hr, fun y hy' => hy ?_⟩
    change d y x < r
    rwa [hd.symm]
theorem closureWrt_eq_closure (hd : IsMetricFunction d) (Z : Set X) :
    letI := metricSpaceOfMetricFunction hd
    closureWrt d Z = closure Z := by
  let _ := metricSpaceOfMetricFunction hd
  ext x
  rw [Metric.mem_closure_iff]
  rfl
theorem isCompactWrt_iff_isCompact (hd : IsMetricFunction d) (Z : Set X) :
    letI := metricSpaceOfMetricFunction hd
    IsCompactWrt d Z ↔ IsCompact Z := by
  let _ := metricSpaceOfMetricFunction hd
  constructor
  · intro h
    refine isCompact_of_finite_subcover fun {ι} U hU hZ => ?_
    obtain ⟨𝒰, h𝒰, hfin, hcov⟩ := h (range U)
      (by rintro _ ⟨i, rfl⟩; exact (isOpenWrt_iff_isOpen hd _).mpr (hU i))
      (by rwa [sUnion_range])
    obtain ⟨t, -, htfin, htcov⟩ := (exists_subset_image_finite_and (f := U) (s := univ)
      (p := fun 𝒱 => Z ⊆ ⋃₀ 𝒱)).mp ⟨𝒰, by rwa [image_univ], hfin, hcov⟩
    refine ⟨htfin.toFinset, ?_⟩
    simpa [sUnion_image] using htcov
  · intro h 𝒰 h𝒰 hZ
    obtain ⟨t, ht⟩ := h.elim_finite_subcover (fun u : 𝒰 => (u : Set X))
      (fun u => (isOpenWrt_iff_isOpen hd _).mp (h𝒰 u u.2)) (by rwa [← sUnion_eq_iUnion])
    refine ⟨(fun u : 𝒰 => (u : Set X)) '' (t : Set 𝒰), ?_, t.finite_toSet.image _, ?_⟩
    · rintro _ ⟨u, -, rfl⟩
      exact u.2
    · simpa [sUnion_image] using ht
theorem isContinuousWrt_iff_continuous (hd : IsMetricFunction d) {Y : Type*}
    [PseudoMetricSpace Y] (f : X → Y) :
    letI := metricSpaceOfMetricFunction hd
    IsContinuousWrt d dist f ↔ Continuous f := by
  let _ := metricSpaceOfMetricFunction hd
  rw [Metric.continuous_iff]
  constructor
  · intro h b ε hε
    obtain ⟨δ, hδ, hy⟩ := h b ε hε
    refine ⟨δ, hδ, fun a ha => ?_⟩
    rw [dist_comm]
    refine hy a ?_
    have h1 : d a b < δ := ha
    rwa [hd.symm]
  · intro h b ε hε
    obtain ⟨δ, hδ, hy⟩ := h b ε hε
    refine ⟨δ, hδ, fun a ha => ?_⟩
    rw [dist_comm]
    refine hy a ?_
    change d a b < δ
    rwa [hd.symm]
end Generic
theorem isContinuousWrt_of_continuous {Y : Type*} [PseudoMetricSpace Y]
    {F : (Fin 4 → ℝ) → Y} (hF : Continuous F) :
    IsContinuousWrt TestFunctions.euclidDistR4 dist F := by
  intro x ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hF x ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [dist_comm]
  refine h y ?_
  rw [dist_comm, dist_eq_norm]
  exact lt_of_le_of_lt (norm_le_euclidNormVec _) hy
theorem isContinuousWrt_of_comp_proj {Y : Type*} (d' : Y → Y → ℝ) (φ : E.Carrier s → Y)
    (h : IsContinuousWrt TestFunctions.euclidDistR4 d' (φ ∘ E.proj s)) :
    IsContinuousWrt (E.pointDist s) d' φ := by
  intro x ε hε
  obtain ⟨δ, hδ, hy⟩ := h (E.someLift s x) ε hε
  refine ⟨δ, hδ, fun y hxy => ?_⟩
  obtain ⟨w, hw, hw'⟩ := exists_lift_at_pointDist s E x y (u := E.someLift s x)
    (E.proj_someLift s x)
  have h1 := hy w (by
    change euclidNormVec (E.someLift s x - w) < δ
    rw [hw']
    exact hxy)
  simpa only [Function.comp_apply, E.proj_someLift s x, proj_eq_of_isLiftOf s E hw] using h1
theorem mem_closedSupport_iff {Z : Type*} [Zero Z] (f : E.Carrier s → Z) (x : E.Carrier s) :
    x ∈ E.closedSupport s f ↔ ∀ r : ℝ, 0 < r → ∃ y, f y ≠ 0 ∧ E.pointDist s x y < r := Iff.rfl
theorem eq_zero_of_notMem_closedSupport {Z : Type*} [Zero Z] {f : E.Carrier s → Z}
    {x : E.Carrier s} (hx : x ∉ E.closedSupport s f) : f x = 0 := by
  by_contra h
  refine hx fun r hr => ⟨x, h, ?_⟩
  rw [((pointDist_isMetricFunction s E).eq_zero_iff x x).mpr rfl]
  exact hr
theorem isDistPreserving_symm (t : E.Carrier s ≃ E.Carrier s) (ht : IsDistPreserving s E t) :
    IsDistPreserving s E t.symm := fun x y => by
  have h := ht (t.symm x) (t.symm y)
  simpa using h.symm
theorem isContinuousSelf_of_isDistPreserving {t : E.Carrier s → E.Carrier s}
    (ht : IsDistPreserving s E t) : E.IsContinuousSelf s t := fun _ ε hε =>
  ⟨ε, hε, fun y hy => by rw [ht]; exact hy⟩
theorem closedSupport_comp (t : E.Carrier s ≃ E.Carrier s) (ht : IsDistPreserving s E t)
    {Z : Type*} [Zero Z] (f : E.Carrier s → Z) :
    E.closedSupport s (f ∘ t) = t ⁻¹' E.closedSupport s f := by
  ext x
  rw [mem_preimage, mem_closedSupport_iff, mem_closedSupport_iff]
  constructor
  · intro h r hr
    obtain ⟨y, hy, hd⟩ := h r hr
    exact ⟨t y, hy, by rw [ht]; exact hd⟩
  · intro h r hr
    obtain ⟨y, hy, hd⟩ := h r hr
    refine ⟨t.symm y, by simpa using hy, ?_⟩
    have h1 := ht x (t.symm y)
    rw [t.apply_symm_apply] at h1
    rw [← h1]
    exact hd
theorem isCompactSubset_preimage (t : E.Carrier s ≃ E.Carrier s) (ht : IsDistPreserving s E t)
    {S : Set (E.Carrier s)} (hS : E.IsCompactSubset s S) : E.IsCompactSubset s (t ⁻¹' S) := by
  let _ := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E)
  have hc : Continuous t.symm :=
    (isContinuousWrt_iff_continuous (pointDist_isMetricFunction s E) t.symm).mp
      (isContinuousSelf_of_isDistPreserving s E (isDistPreserving_symm s E t ht))
  have h1 : IsCompact S := (isCompactWrt_iff_isCompact (pointDist_isMetricFunction s E) S).mp hS
  have h2 : IsCompact (t.symm '' S) := h1.image hc
  rw [Equiv.image_symm_eq_preimage] at h2
  exact (isCompactWrt_iff_isCompact (pointDist_isMetricFunction s E) _).mpr h2
theorem compactAndIsometryFacts_holds : CompactAndIsometryFacts s E := by
  refine ⟨fun S S' hS hS' hdis => ?_, fun t ht => ⟨isContinuousSelf_of_isDistPreserving s E ht,
    isContinuousSelf_of_isDistPreserving s E (isDistPreserving_symm s E t ht),
    fun Z _ f => closedSupport_comp s E t ht f⟩⟩
  let _ := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E)
  have h1 : IsCompact S := (isCompactWrt_iff_isCompact (pointDist_isMetricFunction s E) S).mp hS
  have h2 : IsCompact S' :=
    (isCompactWrt_iff_isCompact (pointDist_isMetricFunction s E) S').mp hS'
  obtain ⟨r, hr, hlt⟩ := Metric.exists_pos_forall_lt_edist h1 h2.isClosed hdis
  refine lt_of_lt_of_le (ENNReal.coe_pos.mpr hr) ?_
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  have h3 := (hlt x hx y hy).le
  rwa [edist_dist] at h3
section Calculus
variable {F G : (Fin 4 → ℝ) → ℝ}
theorem differentiableAt_of_contDiff_one (hF : ContDiff ℝ 1 F) (y : Fin 4 → ℝ) :
    DifferentiableAt ℝ F y :=
  (hF.differentiable (by norm_num)) y
theorem partialDerivR4_eq_fderiv (hF : ContDiff ℝ 1 F) (i : Fin 4) (y : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 i F y = fderiv ℝ F y (Pi.single i 1) := by
  have h1 : HasDerivAt (fun t : ℝ => y + t • (Pi.single i 1 : Fin 4 → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin 4 → ℝ)).const_add y
  have h2 : HasFDerivAt F (fderiv ℝ F y) (y + (0 : ℝ) • (Pi.single i 1 : Fin 4 → ℝ)) := by
    simpa using (differentiableAt_of_contDiff_one hF y).hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
theorem continuous_gradR4 (hF : ContDiff ℝ 1 F) : Continuous (Ambient.gradR4 F) := by
  refine continuous_pi fun i => ?_
  simp only [Ambient.gradR4, partialDerivR4_eq_fderiv hF]
  exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
theorem fderiv_apply_eq_sum_gradR4 (hF : ContDiff ℝ 1 F) (y v : Fin 4 → ℝ) :
    fderiv ℝ F y v = ∑ i, Ambient.gradR4 F y i * v i := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin 4 → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Ambient.gradR4, partialDerivR4_eq_fderiv hF, smul_eq_mul, mul_comm]
theorem abs_sub_le_of_gradR4_bound (hF : ContDiff ℝ 1 F) {C : ℝ}
    (hC : ∀ y, euclidNormVec (Ambient.gradR4 F y) ≤ C) (x y : Fin 4 → ℝ) :
    |F x - F y| ≤ C * euclidNormVec (x - y) := by
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => F (y + t • (x - y)))
      (fderiv ℝ F (y + t • (x - y)) (x - y)) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => y + t • (x - y)) (x - y) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
    exact (differentiableAt_of_contDiff_one hF _).hasFDerivAt.comp_hasDerivAt t h1
  have hbound : ∀ t ∈ (univ : Set ℝ),
      ‖fderiv ℝ F (y + t • (x - y)) (x - y)‖ ≤ C * euclidNormVec (x - y) := fun t _ => by
    rw [fderiv_apply_eq_sum_gradR4 hF, Real.norm_eq_abs]
    exact (abs_inner_le_euclidNormVec_mul _ _).trans
      (mul_le_mul_of_nonneg_right (hC _) (euclidNormVec_nonneg _))
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hder t).hasDerivWithinAt) hbound (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
  simpa using h
theorem gradR4_comp_sub (c y : Fin 4 → ℝ) :
    Ambient.gradR4 (fun z => F (z - c)) y = Ambient.gradR4 F (y - c) := by
  funext i
  simp only [Ambient.gradR4, TestFunctions.partialDerivR4]
  congr 1
  funext t
  congr 1
  abel
end Calculus
theorem continuous_proj :
    letI := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E)
    Continuous (E.proj s) := by
  let _ := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E)
  refine Metric.continuous_iff.mpr fun b ε hε => ⟨ε / 2, half_pos hε, fun a ha => ?_⟩
  rw [dist_eq_norm] at ha
  have h1 := pointDist_proj_le s E a b
  have h2 := euclidNormVec_le_two_mul_norm (a - b)
  change E.pointDist s (E.proj s a) (E.proj s b) < ε
  linarith
theorem grad_proj (f : E.Carrier s → ℝ) (y : Fin 4 → ℝ) :
    E.grad s f (E.proj s y) = Ambient.gradR4 (E.liftFun s f) y :=
  congrFun (E.grad_comp_proj s f) y
theorem grad_eq_zero_of_notMem_closedSupport {g : E.Carrier s → ℝ} {x : E.Carrier s}
    (hx : x ∉ E.closedSupport s g) : E.grad s g x = 0 := by
  let _ := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E)
  obtain ⟨y, rfl⟩ := E.proj_surjective s x
  rw [grad_proj]
  have hopen : IsOpen (E.closedSupport s g)ᶜ := by
    rw [Ambient.closedSupport, Ambient.closureSet,
      closureWrt_eq_closure (pointDist_isMetricFunction s E)]
    exact isClosed_closure.isOpen_compl
  have hcont : Continuous (E.proj s) := continuous_proj s E
  have hev : E.liftFun s g =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (hopen.mem_nhds hx)] with z hz
    exact eq_zero_of_notMem_closedSupport s E hz
  funext i
  simp only [Ambient.gradR4, TestFunctions.partialDerivR4]
  have h2 : (fun t : ℝ => E.liftFun s g (y + t • (Pi.single i 1 : Fin 4 → ℝ))) =ᶠ[𝓝 0]
      fun _ => 0 := by
    have hc : Filter.Tendsto (fun t : ℝ => y + t • (Pi.single i 1 : Fin 4 → ℝ)) (𝓝 0) (𝓝 y) := by
      have : Continuous fun t : ℝ => y + t • (Pi.single i 1 : Fin 4 → ℝ) := by fun_prop
      simpa using this.tendsto 0
    exact hc.eventually hev
  rw [h2.deriv_eq]
  simp
theorem isLip_iff (f : E.Carrier s → ℝ) :
    E.IsLip s f ↔ TestFunctions.IsLipschitzFor (E.pointDist s) f := by
  cases E <;> exact Iff.rfl
theorem lipConst_eq (f : E.Carrier s → ℝ) :
    E.lipConst s f = TestFunctions.bestLipschitzConstant (E.pointDist s) f := by
  cases E <;> rfl
theorem c1CompactFacts_holds : C1CompactFacts s E := by
  rintro g ⟨hg, hcpt⟩
  let _ := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E)
  have hF : ContDiff ℝ 1 (E.liftFun s g) := hg
  have hK : IsCompact (E.closedSupport s g) :=
    (isCompactWrt_iff_isCompact (pointDist_isMetricFunction s E) _).mp hcpt
  have hgc : E.IsContinuousInto s g :=
    isContinuousWrt_of_comp_proj s E dist g (isContinuousWrt_of_continuous hF.continuous)
  have hgc' : Continuous g :=
    (isContinuousWrt_iff_continuous (pointDist_isMetricFunction s E) g).mp hgc
  have hcomp : E.grad s g ∘ E.proj s = Ambient.gradR4 (E.liftFun s g) :=
    E.grad_comp_proj s g
  have hdc : Continuous (E.grad s g) := by
    refine (isContinuousWrt_iff_continuous (pointDist_isMetricFunction s E) _).mp
      (isContinuousWrt_of_comp_proj s E dist _ ?_)
    rw [hcomp]
    exact isContinuousWrt_of_continuous (continuous_gradR4 hF)
  have hdc' : IsContinuousWrt (E.pointDist s) TestFunctions.euclidDistR4 (E.grad s g) := by
    intro x ε hε
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hdc x (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have h1 : dist (E.grad s g y) (E.grad s g x) < ε / 2 := h y (by
      change E.pointDist s y x < δ
      rwa [(pointDist_isMetricFunction s E).symm])
    have h2 := euclidNormVec_le_two_mul_norm (E.grad s g x - E.grad s g y)
    rw [dist_comm, dist_eq_norm] at h1
    change euclidNormVec (E.grad s g x - E.grad s g y) < ε
    linarith
  have hoff : ∀ x, x ∉ E.closedSupport s g → E.grad s g x = 0 := fun x hx =>
    grad_eq_zero_of_notMem_closedSupport s E hx
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hgc'.continuousOn
  have hbdd : TestFunctions.IsBoundedFun g := by
    refine ⟨max C₀ 0, fun x => ?_⟩
    by_cases hx : x ∈ E.closedSupport s g
    · exact (hC₀ x hx).trans (le_max_left _ _)
    · rw [eq_zero_of_notMem_closedSupport s E hx]
      simp
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hdc.continuousOn
  have hgb : ∀ x, euclidNormVec (E.grad s g x) ≤ 2 * max C₁ 0 := fun x => by
    refine (euclidNormVec_le_two_mul_norm _).trans ?_
    by_cases hx : x ∈ E.closedSupport s g
    · linarith [hC₁ x hx, le_max_left C₁ 0]
    · rw [hoff x hx]
      simp
  have hcs : HasCompactSupport (E.grad s g) := by
    refine HasCompactSupport.of_support_subset_isCompact hK fun x hx => ?_
    by_contra h
    exact hx (hoff x h)
  have huc := hcs.uniformContinuous_of_continuous hdc
  have hunif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y, E.pointDist s x y ≤ δ →
      euclidNormVec (E.grad s g x - E.grad s g y) ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (half_pos hε)
    refine ⟨δ / 2, half_pos hδ, fun x y hxy => ?_⟩
    have h1 : dist (E.grad s g x) (E.grad s g y) < ε / 2 :=
      h (lt_of_le_of_lt hxy (half_lt_self hδ))
    rw [dist_eq_norm] at h1
    have h2 := euclidNormVec_le_two_mul_norm (E.grad s g x - E.grad s g y)
    linarith
  have hfin : E.gradSup s g < ∞ := by
    refine lt_of_le_of_lt (iSup_le fun x => ENNReal.ofReal_le_ofReal (hgb x)) ENNReal.ofReal_lt_top
  have hne : E.gradSup s g ≠ ∞ := hfin.ne
  have hsup : ∀ x, euclidNormVec (E.grad s g x) ≤ (E.gradSup s g).toReal := fun x =>
    (ENNReal.ofReal_le_iff_le_toReal hne).mp
      (le_iSup (fun x => ENNReal.ofReal (euclidNormVec (E.grad s g x))) x)
  have hlift : ∀ y, euclidNormVec (Ambient.gradR4 (E.liftFun s g) y) ≤
      (E.gradSup s g).toReal := fun y => by
    rw [← grad_proj]
    exact hsup _
  have hlip : ∀ x y, ‖g x - g y‖ ≤ (E.gradSup s g).toReal * E.pointDist s x y := by
    intro x y
    obtain ⟨u, hu⟩ := E.proj_surjective s x
    obtain ⟨w, hw, hw'⟩ := exists_lift_at_pointDist s E x y (u := u) hu
    have h1 := abs_sub_le_of_gradR4_bound hF hlift u w
    rw [hw'] at h1
    have e1 : E.liftFun s g u = g x := congrArg g hu
    have e2 : E.liftFun s g w = g y := congrArg g hw
    rwa [e1, e2] at h1
  refine ⟨hgc, hbdd, hdc', ⟨_, hgb⟩, hoff, hunif,
    (isLip_iff s E g).mpr ⟨_, ENNReal.toReal_nonneg, hlip⟩, ?_, hfin⟩
  rw [ENNReal.ofReal_le_iff_le_toReal hne, lipConst_eq]
  exact csInf_le ⟨0, fun C hC => hC.1⟩ ⟨ENNReal.toReal_nonneg, hlip⟩
theorem closedSupport_subset_of_isClosed {Z : Type*} [Zero Z] {f : E.Carrier s → Z}
    {C : Set (E.Carrier s)}
    (hC : letI := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E); IsClosed C)
    (hf : ∀ x, x ∉ C → f x = 0) :
    E.closedSupport s f ⊆ C := by
  let _ := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E)
  rw [Ambient.closedSupport, Ambient.closureSet,
    closureWrt_eq_closure (pointDist_isMetricFunction s E)]
  refine closure_minimal (fun x hx => ?_) hC
  by_contra h
  exact hx (hf x h)
theorem isClosed_closedSupport {Z : Type*} [Zero Z] (f : E.Carrier s → Z) :
    letI := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E)
    IsClosed (E.closedSupport s f) := by
  let _ := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E)
  rw [Ambient.closedSupport, Ambient.closureSet,
    closureWrt_eq_closure (pointDist_isMetricFunction s E)]
  exact isClosed_closure
theorem linearCombinationFacts_holds : LinearCombinationFacts s E := by
  rintro f ⟨hf, hfK⟩ g ⟨hg, hgK⟩ a b ψ hψ
  let _ := metricSpaceOfMetricFunction (pointDist_isMetricFunction s E)
  have hF : ContDiff ℝ 1 (E.liftFun s f) := hf
  have hG : ContDiff ℝ 1 (E.liftFun s g) := hg
  have hΨ : ContDiff ℝ 1 (E.liftFun s ψ) := hψ
  have hK : IsCompact (E.closedSupport s f) :=
    (isCompactWrt_iff_isCompact (pointDist_isMetricFunction s E) _).mp hfK
  have hK' : IsCompact (E.closedSupport s g) :=
    (isCompactWrt_iff_isCompact (pointDist_isMetricFunction s E) _).mp hgK
  have hsub : E.closedSupport s (fun x => a * f x + b * g x) ⊆
      E.closedSupport s f ∪ E.closedSupport s g := by
    refine closedSupport_subset_of_isClosed s E (hK.union hK').isClosed fun x hx => ?_
    rw [mem_union, not_or] at hx
    rw [eq_zero_of_notMem_closedSupport s E hx.1, eq_zero_of_notMem_closedSupport s E hx.2]
    simp
  have hsubψ : E.closedSupport s (fun x => ψ x * f x) ⊆
      E.closedSupport s ψ ∩ E.closedSupport s f := by
    refine closedSupport_subset_of_isClosed s E
      ((isClosed_closedSupport s E ψ).inter hK.isClosed) fun x hx => ?_
    rw [mem_inter_iff, not_and_or] at hx
    rcases hx with hx | hx
    · rw [eq_zero_of_notMem_closedSupport s E hx, zero_mul]
    · rw [eq_zero_of_notMem_closedSupport s E hx, mul_zero]
  refine ⟨⟨?_, ?_⟩, ?_, hsub, ⟨?_, ?_⟩, hsubψ⟩
  · exact (contDiff_const.mul hF).add (contDiff_const.mul hG)
  · exact (isCompactWrt_iff_isCompact (pointDist_isMetricFunction s E) _).mpr
      ((hK.union hK').of_isClosed_subset (isClosed_closedSupport s E _) hsub)
  · funext x
    obtain ⟨y, rfl⟩ := E.proj_surjective s x
    funext i
    have hC : ContDiff ℝ 1 (fun z => a * E.liftFun s f z + b * E.liftFun s g z) :=
      (contDiff_const.mul hF).add (contDiff_const.mul hG)
    have hfd := (((differentiableAt_of_contDiff_one hF y).hasFDerivAt.const_mul a).add
      ((differentiableAt_of_contDiff_one hG y).hasFDerivAt.const_mul b)).fderiv
    have e : E.liftFun s (fun x => a * f x + b * g x) =
        fun z => a * E.liftFun s f z + b * E.liftFun s g z := rfl
    simp only [Pi.add_apply, Pi.smul_apply, grad_proj, e, Ambient.gradR4,
      partialDerivR4_eq_fderiv hC, partialDerivR4_eq_fderiv hF, partialDerivR4_eq_fderiv hG,
      smul_eq_mul]
    have hfd' : fderiv ℝ (fun z => a * E.liftFun s f z + b * E.liftFun s g z) y =
        a • fderiv ℝ (E.liftFun s f) y + b • fderiv ℝ (E.liftFun s g) y := hfd
    rw [hfd']
    simp
  · exact hΨ.mul hF
  · exact (isCompactWrt_iff_isCompact (pointDist_isMetricFunction s E) _).mpr
      (hK.of_isClosed_subset (isClosed_closedSupport s E _) (hsubψ.trans inter_subset_right))
theorem isDistPreserving_sub (v : E.Carrier s) : IsDistPreserving s E (fun x => x - v) :=
  fun x y => by
  simp [Ambient.pointDist]
theorem isDistPreserving_add (v : E.Carrier s) : IsDistPreserving s E (fun x => x + v) :=
  fun x y => by
  simp [Ambient.pointDist]
theorem translationFacts_holds : TranslationFacts s E := by
  intro v
  have hts : IsDistPreserving s E (Equiv.subRight v) := isDistPreserving_sub s E v
  have hsupp : ∀ (Z : Type) [Zero Z] (f : E.Carrier s → Z),
      E.closedSupport s (E.translateFun s v f) = E.translateSet s (E.closedSupport s f) v := by
    intro Z _ f
    have h := closedSupport_comp s E (Equiv.subRight v) hts f
    have e : f ∘ (Equiv.subRight v) = E.translateFun s v f := rfl
    rw [e] at h
    rw [h]
    ext x
    constructor
    · intro hx
      exact ⟨x - v, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  refine ⟨(Equiv.addRight v).bijective, isDistPreserving_add s E v, hsupp, fun f hf => ?_⟩
  obtain ⟨hf, hK⟩ := hf
  have hlift : E.liftFun s (E.translateFun s v f) =
      fun y => E.liftFun s f (y - E.someLift s v) := by
    funext y
    change f (E.proj s y - v) = f (E.proj s (y - E.someLift s v))
    rw [sub_eq_add_neg y, E.proj_add s, E.proj_neg s, E.proj_someLift s v, sub_eq_add_neg]
  have hF : ContDiff ℝ 1 (E.liftFun s f) := hf
  refine ⟨⟨?_, ?_⟩, fun x => ?_⟩
  · change ContDiff ℝ 1 (E.liftFun s (E.translateFun s v f))
    rw [hlift]
    exact hF.comp (contDiff_id.sub contDiff_const)
  · have h := closedSupport_comp s E (Equiv.subRight v) hts f
    have e : f ∘ (Equiv.subRight v) = E.translateFun s v f := rfl
    rw [e] at h
    rw [h]
    exact isCompactSubset_preimage s E _ hts hK
  · obtain ⟨y, rfl⟩ := E.proj_surjective s x
    rw [grad_proj, hlift, gradR4_comp_sub, ← grad_proj]
    congr 1
    rw [sub_eq_add_neg y, E.proj_add s, E.proj_neg s, E.proj_someLift s v, sub_eq_add_neg]
section Lifted
variable (μ : Fin 4) (c : ℝ)
theorem reflectR4_apply (y : Fin 4 → ℝ) (ν : Fin 4) :
    reflectR4 μ c y ν = if ν = μ then 2 * c - y μ else y ν := by
  by_cases h : ν = μ
  · subst h
    simp [reflectR4, stdBasisVec]
    ring
  · simp [reflectR4, stdBasisVec, h]
theorem reflectR4_involutive : Function.Involutive (reflectR4 μ c) := fun y => by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [reflectR4_apply]
  · simp [reflectR4_apply, h]
theorem euclidNormVec_reflectR4_sub (x y : Fin 4 → ℝ) :
    euclidNormVec (reflectR4 μ c x - reflectR4 μ c y) = euclidNormVec (x - y) := by
  simp only [euclidNormVec]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : ν = μ
  · subst h
    simp only [Pi.sub_apply, reflectR4_apply, if_true]
    ring
  · simp [reflectR4_apply, h]
theorem contDiff_reflectR4 : ContDiff ℝ 1 (reflectR4 μ c) := by
  refine contDiff_pi.mpr fun ν => ?_
  simp only [reflectR4_apply]
  split_ifs
  · exact contDiff_const.sub (contDiff_apply ℝ ℝ μ)
  · exact contDiff_apply ℝ ℝ ν
theorem partialDerivR4_comp_reflectR4 {F : (Fin 4 → ℝ) → ℝ} (hF : ContDiff ℝ 1 F)
    (ν : Fin 4) (y : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 ν (F ∘ reflectR4 μ c) y =
      (if ν = μ then -1 else 1) * TestFunctions.partialDerivR4 ν F (reflectR4 μ c y) := by
  have e : ∀ t : ℝ, reflectR4 μ c (y + t • (Pi.single ν 1 : Fin 4 → ℝ)) =
      reflectR4 μ c y + ((if ν = μ then -1 else 1) * t) • (Pi.single ν 1 : Fin 4 → ℝ) := by
    intro t
    funext κ
    by_cases hκ : κ = ν
    · subst hκ
      by_cases h : κ = μ
      · subst h
        simp [reflectR4_apply]
        ring
      · simp [reflectR4_apply, h]
    · by_cases h : κ = μ
      · subst h
        have hν : ν ≠ κ := fun h' => hκ h'.symm
        simp [reflectR4_apply, hκ, hν]
      · have hz : (Pi.single ν (1 : ℝ) : Fin 4 → ℝ) κ = 0 := Pi.single_eq_of_ne hκ _
        simp only [reflectR4_apply, if_neg h, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz,
          mul_zero, add_zero]
  set σ : ℝ := if ν = μ then -1 else 1 with hσ
  have h1 : HasDerivAt (fun t : ℝ => reflectR4 μ c y + (σ * t) • (Pi.single ν 1 : Fin 4 → ℝ))
      (σ • (Pi.single ν 1 : Fin 4 → ℝ)) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => σ * t) σ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul σ
    exact (h0.smul_const (Pi.single ν 1 : Fin 4 → ℝ)).const_add _
  have h2 : HasFDerivAt F (fderiv ℝ F (reflectR4 μ c y))
      (reflectR4 μ c y + (σ * 0) • (Pi.single ν 1 : Fin 4 → ℝ)) := by
    simpa using (differentiableAt_of_contDiff_one hF _).hasFDerivAt
  have h3 := (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
  rw [partialDerivR4_eq_fderiv hF, ← smul_eq_mul, ← map_smul, ← h3]
  simp only [TestFunctions.partialDerivR4, Function.comp_def, e]
end Lifted
theorem reflect_proj (μ : Fin 4) (c : ℝ) (y : Fin 4 → ℝ) :
    E.reflect s μ c (E.proj s y) = E.proj s (reflectR4 μ c y) :=
  congrFun (E.reflect_comp_proj s μ c) y
theorem reflect_involutive (μ : Fin 4) (c : ℝ) : Function.Involutive (E.reflect s μ c) := by
  intro x
  obtain ⟨y, rfl⟩ := E.proj_surjective s x
  rw [reflect_proj, reflect_proj, reflectR4_involutive]
theorem pointDist_reflect_le (μ : Fin 4) (c : ℝ) (x y : E.Carrier s) :
    E.pointDist s (E.reflect s μ c x) (E.reflect s μ c y) ≤ E.pointDist s x y := by
  obtain ⟨u, rfl⟩ := E.proj_surjective s x
  obtain ⟨w, hw, hw'⟩ := exists_lift_at_pointDist s E (E.proj s u) y (u := u) rfl
  rw [← hw', ← proj_eq_of_isLiftOf s E hw, reflect_proj, reflect_proj,
    ← euclidNormVec_reflectR4_sub μ c u w]
  exact pointDist_proj_le s E _ _
theorem isDistPreserving_reflect (μ : Fin 4) (c : ℝ) :
    IsDistPreserving s E (E.reflect s μ c) := fun x y => by
  refine le_antisymm (pointDist_reflect_le s E μ c x y) ?_
  have h := pointDist_reflect_le s E μ c (E.reflect s μ c x) (E.reflect s μ c y)
  rwa [reflect_involutive s E μ c x, reflect_involutive s E μ c y] at h
theorem reflectionFacts_holds : ReflectionFacts s E := by
  intro μ c
  have hinv := reflect_involutive s E μ c
  have hpres := isDistPreserving_reflect s E μ c
  refine ⟨hinv.bijective, hpres, funext hinv, fun f hf => ?_⟩
  obtain ⟨hf, hK⟩ := hf
  have hF : ContDiff ℝ 1 (E.liftFun s f) := hf
  have hlift : E.liftFun s (E.reflectFun s μ c f) = E.liftFun s f ∘ reflectR4 μ c := by
    funext y
    change f (E.reflect s μ c (E.proj s y)) = f (E.proj s (reflectR4 μ c y))
    rw [reflect_proj]
  refine ⟨⟨?_, ?_⟩, fun x => ?_⟩
  · change ContDiff ℝ 1 (E.liftFun s (E.reflectFun s μ c f))
    rw [hlift]
    exact hF.comp (contDiff_reflectR4 μ c)
  · have hts : IsDistPreserving s E hinv.toPerm := hpres
    have h := closedSupport_comp s E hinv.toPerm hts f
    have e : f ∘ hinv.toPerm = E.reflectFun s μ c f := rfl
    rw [e] at h
    rw [h]
    exact isCompactSubset_preimage s E _ hts hK
  · obtain ⟨y, rfl⟩ := E.proj_surjective s x
    rw [grad_proj, hlift, reflect_proj, grad_proj]
    funext ν
    rw [coordFlipMatrix, Matrix.mulVec_diagonal]
    exact partialDerivR4_comp_reflectR4 μ c hF ν y
theorem periodicReflectHalfPeriod_holds : PeriodicReflectHalfPeriod s := by
  rintro μ c c' ⟨n, hn⟩
  funext x
  have hsplit : reflectR4 μ c' (Ambient.periodic.someLift s x) =
      reflectR4 μ c (Ambient.periodic.someLift s x) + (s.side * (n : ℝ)) • stdBasisVec μ := by
    funext ν
    by_cases h : ν = μ
    · subst h
      simp only [reflectR4_apply, if_true, Pi.add_apply, Pi.smul_apply, stdBasisVec,
        Pi.single_eq_same, smul_eq_mul]
      have : c' = c + s.side / 2 * (n : ℝ) := by linarith
      rw [this]
      ring
    · simp [reflectR4_apply, stdBasisVec, h]
  have h0 : Ambient.periodic.proj s ((s.side * (n : ℝ)) • stdBasisVec μ) = 0 := by
    funext ν
    refine (AddCircle.coe_eq_zero_iff _).mpr ?_
    by_cases h : ν = μ
    · subst h
      exact ⟨n, by simp [stdBasisVec, mul_comm]⟩
    · exact ⟨0, by simp [stdBasisVec, h]⟩
  simp only [Ambient.reflect]
  rw [hsplit, Ambient.proj_add, h0, add_zero]
theorem claim_holds : Claim := fun s E =>
  ⟨euclidDistFacts_holds s E, compactAndIsometryFacts_holds s E, c1CompactFacts_holds s E,
    linearCombinationFacts_holds s E, translationFacts_holds s E, reflectionFacts_holds s E,
    periodicReflectHalfPeriod_holds s⟩
end AmbientMetric
end LimitSpaces
end YangMills.Construction
end
