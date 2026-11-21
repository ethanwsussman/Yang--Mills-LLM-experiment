import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.Continuum.NeighbourhoodsAdmissibleFamiliesAndMembersOfTheClassesProof
import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBallsProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.QuotientCompactC1
open Set Filter YangMills.Construction.TorusMetric
private theorem normVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
private theorem normVec_add_le (a b : Fin 4 → ℝ) :
    euclidNormVec (a + b) ≤ euclidNormVec a + euclidNormVec b := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
private theorem normVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
private theorem normVec_zero : euclidNormVec 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
private theorem eq_zero_of_normVec_eq_zero {v : Fin 4 → ℝ} (hv : euclidNormVec v = 0) :
    v = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.eq_zero_of_euclidNormVec_eq_zero <;> assumption
private theorem supNorm_le_normVec (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
private theorem normVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
private theorem normVec_smul (t : ℝ) (v : Fin 4 → ℝ) :
    euclidNormVec (t • v) = |t| * euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
private theorem isOpenWrt_dist_iff {X : Type*} [MetricSpace X] (U : Set X) :
    MetricNotions.IsOpenWrt dist U ↔ IsOpen U := by
  rw [Metric.isOpen_iff]
  constructor
  · intro hU p hp
    obtain ⟨r, hr, hball⟩ := hU p hp
    exact ⟨r, hr, fun q hq => hball q (by rwa [dist_comm, ← Metric.mem_ball])⟩
  · intro hU p hp
    obtain ⟨r, hr, hball⟩ := hU p hp
    exact ⟨r, hr, fun q hq => hball (by rwa [Metric.mem_ball, dist_comm])⟩
private theorem isCompactWrt_dist_iff {X : Type*} [MetricSpace X] (K : Set X) :
    MetricNotions.IsCompactWrt dist K ↔ IsCompact K := by
  constructor
  · intro hK
    apply isCompact_of_finite_subcover
    intro ι U hU hcover
    obtain ⟨𝒱, hsub, hfin, hcov⟩ := hK (range U)
      (by rintro _ ⟨i, rfl⟩; exact (isOpenWrt_dist_iff _).2 (hU i)) (by rwa [sUnion_range])
    have hpre : ∀ W : 𝒱, ∃ i, U i = W := fun W => hsub W.2
    choose idx hidx using hpre
    have := hfin.fintype
    classical
    refine ⟨Finset.univ.image idx, fun p hp => ?_⟩
    obtain ⟨W, hW, hpW⟩ := hcov hp
    refine mem_iUnion₂.2 ⟨idx ⟨W, hW⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    rw [hidx ⟨W, hW⟩]
    exact hpW
  · intro hK 𝒰 hU hcover
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun W : 𝒰 => (W : Set X))
      (fun W => (isOpenWrt_dist_iff _).1 (hU W W.2)) (by rwa [← sUnion_eq_iUnion])
    refine ⟨(fun W : 𝒰 => (W : Set X)) '' (t : Set 𝒰), ?_, t.finite_toSet.image _, ?_⟩
    · rintro _ ⟨W, _, rfl⟩
      exact W.2
    · intro p hp
      obtain ⟨W, hW, hpW⟩ := mem_iUnion₂.1 (ht hp)
      exact ⟨W, ⟨W, hW, rfl⟩, hpW⟩
private theorem isContinuousWrt_dist_iff {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) : MetricNotions.IsContinuousWrt dist dist f ↔ Continuous f := by
  rw [Metric.continuous_iff]
  constructor
  · intro hf p ε hε
    obtain ⟨δ, hδ, hball⟩ := hf p ε hε
    exact ⟨δ, hδ, fun q hq => by
      rw [dist_comm]
      exact hball q (by rwa [dist_comm])⟩
  · intro hf p ε hε
    obtain ⟨δ, hδ, hball⟩ := hf p ε hε
    exact ⟨δ, hδ, fun q hq => by
      rw [dist_comm]
      exact hball q (by rwa [dist_comm])⟩
private theorem isContinuousWrt_euclidDistR4_iff {Y : Type*} [PseudoMetricSpace Y]
    (f : (Fin 4 → ℝ) → Y) :
    MetricNotions.IsContinuousWrt TestFunctions.euclidDistR4 dist f ↔ Continuous f := by
  rw [Metric.continuous_iff]
  constructor
  · intro hf p ε hε
    obtain ⟨δ, hδ, hball⟩ := hf p ε hε
    refine ⟨δ / 2, by positivity, fun q hq => ?_⟩
    rw [dist_comm]
    refine hball q ?_
    have ha : ‖p - q‖ < δ / 2 := by rwa [dist_comm, dist_eq_norm] at hq
    have hb := normVec_le_two_mul_norm (p - q)
    show euclidNormVec (p - q) < δ
    linarith
  · intro hf p ε hε
    obtain ⟨δ, hδ, hball⟩ := hf p ε hε
    refine ⟨δ, hδ, fun q hq => ?_⟩
    rw [dist_comm]
    refine hball q ?_
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (supNorm_le_normVec _) hq
variable (D : Params) (E : Kind)
private theorem quotDist_metric_lifts (hw : WellPosedness.WellPosed) :
    QuotDistIsMetricWithLifts D E := by
  obtain ⟨hhom, hlift, hdiff, -, -, -, hleast, -⟩ := hw D E
  have hnonneg : ∀ y y' : E.Pt D, 0 ≤ quotDist D E y y' := by
    intro y y'
    obtain ⟨p, rfl⟩ := hhom.2.1 y
    obtain ⟨p', rfl⟩ := hhom.2.1 y'
    obtain ⟨⟨k, -, hk⟩, -⟩ := hleast p p'
    rw [hk]
    exact normVec_nonneg _
  have hle : ∀ p p' : Fin 4 → ℝ, quotDist D E (E.quotMap D p) (E.quotMap D p') ≤
      euclidNormVec (p - p') := by
    intro p p'
    exact (hleast p p').2 ⟨0, (E.periodGroup D).zero_mem, by simp⟩
  have hsymm : ∀ y y' : E.Pt D, quotDist D E y y' ≤ quotDist D E y' y := by
    intro y y'
    obtain ⟨p, rfl⟩ := hhom.2.1 y
    obtain ⟨p', rfl⟩ := hhom.2.1 y'
    obtain ⟨⟨k, hk, hr⟩, -⟩ := hleast p' p
    rw [hr]
    refine (hleast p p').2 ⟨-k, (E.periodGroup D).neg_mem hk, ?_⟩
    rw [← normVec_neg (p' - p - k)]
    congr 1
    abel
  refine ⟨hnonneg, ?_, fun y y' => le_antisymm (hsymm y y') (hsymm y' y), ?_, hle, ?_⟩
  · intro y y'
    obtain ⟨p, rfl⟩ := hhom.2.1 y
    obtain ⟨p', rfl⟩ := hhom.2.1 y'
    constructor
    · intro hzero
      obtain ⟨⟨k, hk, hr⟩, -⟩ := hleast p p'
      rw [hzero] at hr
      have ha : p - p' - k = 0 := eq_zero_of_normVec_eq_zero hr.symm
      have hb : p - p' ∈ E.periodGroup D := by
        rw [sub_eq_zero.1 ha]
        exact hk
      obtain ⟨y, hy, hy'⟩ := (hdiff p p').2 hb
      exact hy.trans hy'.symm
    · intro heq
      have ha : p - p' ∈ E.periodGroup D := (hdiff p p').1 ⟨_, heq, rfl⟩
      refine le_antisymm ?_ (hnonneg _ _)
      have hb := (hleast p p').2 ⟨p - p', ha, rfl⟩
      simpa [normVec_zero] using hb
  · intro y y' y''
    obtain ⟨p, rfl⟩ := hhom.2.1 y
    obtain ⟨p', rfl⟩ := hhom.2.1 y'
    obtain ⟨p'', rfl⟩ := hhom.2.1 y''
    obtain ⟨⟨k, hk, hr⟩, -⟩ := hleast p p'
    obtain ⟨⟨k', hk', hr'⟩, -⟩ := hleast p' p''
    rw [hr, hr']
    have ha : quotDist D E (E.quotMap D p) (E.quotMap D p'') ≤
        euclidNormVec (p - p'' - (k + k')) :=
      (hleast p p'').2 ⟨k + k', (E.periodGroup D).add_mem hk hk', rfl⟩
    refine ha.trans (le_of_eq_of_le ?_ (normVec_add_le (p - p' - k) (p' - p'' - k')))
    congr 1
    abel
  · intro y y' p hp
    obtain ⟨p₀, rfl⟩ := hhom.2.1 y'
    subst hp
    obtain ⟨⟨k, hk, hr⟩, -⟩ := hleast p p₀
    refine ⟨p₀ + k, ?_, ?_⟩
    · show E.quotMap D (p₀ + k) = E.quotMap D p₀
      rw [hhom.1, (hhom.2.2 k).2 hk, add_zero]
    · rw [hr]
      congr 1
      abel
@[reducible] private def metricSpaceOf (hM : QuotDistIsMetricWithLifts D E) :
    MetricSpace (E.Pt D) where
  dist := quotDist D E
  dist_self y := (hM.2.1 y y).2 rfl
  dist_comm := hM.2.2.1
  dist_triangle := hM.2.2.2.1
  eq_of_dist_eq_zero h := (hM.2.1 _ _).1 h
private theorem quotMap_continuous_open (hw : WellPosedness.WellPosed) :
    QuotMapContinuousOpen D E := by
  obtain ⟨hhom, -⟩ := hw D E
  obtain ⟨-, -, -, -, hle, hl⟩ := quotDist_metric_lifts D E hw
  have hcont : MetricNotions.IsContinuousWrt TestFunctions.euclidDistR4 (quotDist D E)
      (E.quotMap D) := fun p ε hε =>
    ⟨ε, hε, fun q hq => lt_of_le_of_lt (hle p q) hq⟩
  refine ⟨hcont, ?_, fun f => ⟨?_, ?_⟩⟩
  · rintro U hU _ ⟨p, hp, rfl⟩
    obtain ⟨r, hr, hball⟩ := hU p hp
    refine ⟨r, hr, fun y' hy' => ?_⟩
    obtain ⟨p', hp', heq⟩ := hl _ y' p rfl
    exact ⟨p', hball p' (by
      show euclidNormVec (p - p') < r
      rwa [heq]), hp'⟩
  · intro hf p ε hε
    obtain ⟨δ, hδ, hball⟩ := hf (E.quotMap D p) ε hε
    obtain ⟨δ', hδ', hball'⟩ := hcont p δ hδ
    exact ⟨δ', hδ', fun q hq => hball _ (hball' q hq)⟩
  · intro hf y ε hε
    obtain ⟨p, rfl⟩ := hhom.2.1 y
    obtain ⟨δ, hδ, hball⟩ := hf p ε hε
    refine ⟨δ, hδ, fun y' hy' => ?_⟩
    obtain ⟨p', hp', heq⟩ := hl _ y' p rfl
    have ha := hball p' (by
      show euclidNormVec (p - p') < δ
      rwa [heq])
    rw [← show E.quotMap D p' = y' from hp']
    exact ha
private theorem params_side_pos : 0 < D.side := by apply _root_.YangMills.SharedProofs.p25685 <;> assumption
private theorem torus_isCompact (hw : WellPosedness.WellPosed) :
    TorusCompact D := by
  obtain ⟨hhom, -, hdiff, -⟩ := hw D Kind.torus
  have hM := quotDist_metric_lifts D Kind.torus hw
  have hQ := quotMap_continuous_open D Kind.torus hw
  let := metricSpaceOf D Kind.torus hM
  have hc : Continuous (Kind.torus.quotMap D) :=
    (isContinuousWrt_euclidDistR4_iff _).1 hQ.1
  have hℓ : 0 < D.side := params_side_pos D
  have hbox : IsCompact (Set.Icc (0 : Fin 4 → ℝ) (fun _ => D.side)) := isCompact_Icc
  have himg : Kind.torus.quotMap D '' Set.Icc (0 : Fin 4 → ℝ) (fun _ => D.side) =
      (Set.univ : Set (Kind.torus.Pt D)) := by
    rw [eq_univ_iff_forall]
    intro y
    obtain ⟨p, rfl⟩ := hhom.2.1 y
    let v : Fin 4 → ℝ := fun i => toIcoMod hℓ 0 (p i)
    refine ⟨v, ⟨fun i => (toIcoMod_mem_Ico hℓ 0 (p i)).1, fun i => ?_⟩, ?_⟩
    · have ha := (toIcoMod_mem_Ico hℓ 0 (p i)).2
      simp only [zero_add] at ha
      exact ha.le
    · have hm : v - p ∈ Kind.torus.periodGroup D := by
        show ∃ n : Fin 4 → ℤ, ∀ i, (v - p) i = (n i : ℝ) * D.side
        refine ⟨fun i => -toIcoDiv hℓ 0 (p i), fun i => ?_⟩
        simp only [Pi.sub_apply, v, toIcoMod, zsmul_eq_mul]
        push_cast
        ring
      obtain ⟨y, hy, hy'⟩ := (hdiff v p).2 hm
      exact hy.trans hy'.symm
  have hcpt : IsCompact (Set.univ : Set (Kind.torus.Pt D)) := himg ▸ hbox.image hc
  exact (isCompactWrt_dist_iff _).2 hcpt
private theorem infDistPt_lt_iff (y : E.Pt D) (S : Set (E.Pt D)) {η : ℝ} (hη : 0 < η) :
    infDistPt D E y S < ENNReal.ofReal η ↔ ∃ z ∈ S, quotDist D E y z < η := by
  have heq : infDistPt D E y S = ⨅ z' ∈ S, ENNReal.ofReal (quotDist D E y z') := by
    simp [infDistPt, setInfDist]
  rw [heq]
  simp only [iInf_lt_iff, ENNReal.ofReal_lt_ofReal_iff hη, exists_prop]
private theorem compact_thickenings (hw : WellPosedness.WellPosed) :
    CompactSetsThickenings D E := by
  have hM := quotDist_metric_lifts D E hw
  obtain ⟨hnn, h0, hs, ht, -, -⟩ := id hM
  let := metricSpaceOf D E hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S S' hS hS' hdisj
    have hSc : IsCompact S := (isCompactWrt_dist_iff S).1 hS
    have hSc' : IsCompact S' := (isCompactWrt_dist_iff S').1 hS'
    obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist hSc hSc'.isClosed hdisj
    refine lt_of_lt_of_le (ENNReal.coe_pos.2 hr)
      (le_iInf₂ fun z hz => le_iInf₂ fun z' hz' => ?_)
    have ha := hsep z hz z' hz'
    rw [edist_dist] at ha
    exact ha.le
  · intro S hS η hη
    constructor
    · intro y hy
      obtain ⟨z, hz, hd⟩ := (infDistPt_lt_iff D E y S hη).1 hy
      refine ⟨η - quotDist D E y z, by linarith, fun y' hy' =>
        (infDistPt_lt_iff D E y' S hη).2 ⟨z, hz, ?_⟩⟩
      have ha := ht y' y z
      have hb := hs y' y
      linarith
    · intro y hy
      exact (infDistPt_lt_iff D E y S hη).2 ⟨y, hy, by rw [(h0 y y).2 rfl]; exact hη⟩
  · refine ⟨fun 𝒰 _ _ => ⟨∅, empty_subset _, finite_empty, empty_subset _⟩, fun η hη => ?_⟩
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, -⟩ := (infDistPt_lt_iff D E y ∅ hη).1 hy
      exact hz.elim
    · intro hy
      exact hy.elim
  · intro S S' hS hS' η hη hd
    rw [eq_empty_iff_forall_notMem]
    rintro y ⟨hy, hy'⟩
    obtain ⟨z, hz, ha⟩ := (infDistPt_lt_iff D E y S hη).1 hy
    obtain ⟨z', hz', hb⟩ := (infDistPt_lt_iff D E y S' hη).1 hy'
    have hc : setInfDist D E S S' ≤ ENNReal.ofReal (quotDist D E z z') :=
      iInf₂_le_of_le z hz (iInf₂_le z' hz')
    have hlt : quotDist D E z z' < 2 * η := by
      have he := ht z y z'
      have hf := hs z y
      linarith
    exact absurd (hd.trans hc) (not_le.2 ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt))
private theorem hasDerivAt_along_line {F : (Fin 4 → ℝ) → ℝ} (hF : ContDiff ℝ 1 F)
    (p w : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (p + s • w)) (fderiv ℝ F (p + t • w) w) t := by apply _root_.YangMills.Construction.TorusTransport.SupportFacts.hasDerivAt_comp_line <;> assumption
private theorem partialDerivR4_eq_fderiv {F : (Fin 4 → ℝ) → ℝ} (hF : ContDiff ℝ 1 F)
    (i : Fin 4) (p : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 i F p = fderiv ℝ F p (Pi.single i 1) := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.partialDerivR4_eq_fderiv <;> assumption
private theorem clm_apply_eq_sum (A : (Fin 4 → ℝ) →L[ℝ] ℝ) (w : Fin 4 → ℝ) :
    A w = ∑ i, A (Pi.single i 1) * w i := by
  have hw : w = ∑ i, w i • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum, mul_comm]
private theorem abs_clm_apply_le (A : (Fin 4 → ℝ) →L[ℝ] ℝ) (w : Fin 4 → ℝ) :
    |A w| ≤ euclidNormVec (fun i => A (Pi.single i 1)) * euclidNormVec w := by
  rw [clm_apply_eq_sum A w, abs_le]
  have ha := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => A (Pi.single i 1)) w
  have hb := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => -A (Pi.single i 1)) w
  simp only [neg_mul, Finset.sum_neg_distrib, even_two, Even.neg_pow] at hb
  unfold euclidNormVec
  constructor <;> linarith
private theorem abs_sub_le_of_fderiv_bound {F : (Fin 4 → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) {G : ℝ}
    (hG : ∀ z, euclidNormVec (fun i => fderiv ℝ F z (Pi.single i 1)) ≤ G) (p p' : Fin 4 → ℝ) :
    |F p - F p'| ≤ G * euclidNormVec (p - p') := by
  have hbd : ∀ t : ℝ, ‖fderiv ℝ F (p' + t • (p - p')) (p - p')‖ ≤
      G * euclidNormVec (p - p') := by
    intro t
    rw [Real.norm_eq_abs]
    exact (abs_clm_apply_le _ _).trans (mul_le_mul_of_nonneg_right (hG _) (normVec_nonneg _))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => F (p' + s • (p - p')))
    (f' := fun t => fderiv ℝ F (p' + t • (p - p')) (p - p'))
    (fun t _ => (hasDerivAt_along_line hF p' (p - p') t).hasDerivWithinAt) (fun t _ => hbd t)
  simpa [Real.norm_eq_abs] using hmv
private theorem compactSupport_c1 (hw : WellPosedness.WellPosed) :
    CompactSupportC1Facts D E := by
  intro u hu hS
  obtain ⟨hhom, -, -, -, -, -, -, -, -, hpd, h40, hlipc⟩ := hw D E
  have hM := quotDist_metric_lifts D E hw
  have hQ := quotMap_continuous_open D E hw
  obtain ⟨hnn, h0, hs, ht, hle, hl⟩ := id hM
  let := metricSpaceOf D E hM
  have hF : ContDiff ℝ 1 (u ∘ E.quotMap D) := hu
  set F : (Fin 4 → ℝ) → ℝ := u ∘ E.quotMap D with hFdef
  have hSc : IsCompact (supportQ D E u) := (isCompactWrt_dist_iff _).1 hS
  have hpart : ∀ (i : Fin 4) (p : Fin 4 → ℝ),
      partialDeriv D E i u (E.quotMap D p) = fderiv ℝ F p (Pi.single i 1) := by
    intro i p
    have ha := congrFun ((hpd u hu).2 i).2.2 p
    rw [← partialDerivR4_eq_fderiv hF]
    exact ha
  have hgrad : ∀ p : Fin 4 → ℝ, gradVec D E u (E.quotMap D p) =
      fun i => fderiv ℝ F p (Pi.single i 1) := fun p => funext fun i => hpart i p
  have hdescend : ∀ v : E.Pt D → ℝ, Continuous (v ∘ E.quotMap D) → Continuous v :=
    fun v hv => (isContinuousWrt_dist_iff v).1
      ((hQ.2.2 v).2 ((isContinuousWrt_euclidDistR4_iff _).2 hv))
  have hucont : Continuous u := hdescend u hF.continuous
  have hpcont : ∀ i : Fin 4, Continuous (partialDeriv D E i u) := by
    intro i
    apply hdescend
    have ha : partialDeriv D E i u ∘ E.quotMap D =
        fun p => fderiv ℝ F p (Pi.single i 1) := funext fun p => hpart i p
    rw [ha]
    exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hpcont' : ∀ i : Fin 4, IsContinuousQ D E (partialDeriv D E i u) :=
    fun i => (isContinuousWrt_dist_iff _).2 (hpcont i)
  have hoff : ∀ y, y ∉ supportQ D E u → u y = 0 := by
    intro y hy
    by_contra hne
    refine hy (fun r hr => ⟨y, hne, ?_⟩)
    rw [(h0 y y).2 rfl]
    exact hr
  have hgoff : ∀ y, y ∉ supportQ D E u → gradVec D E u y = 0 := by
    intro y hy
    obtain ⟨p, rfl⟩ := hhom.2.1 y
    have hex : ∃ r : ℝ, 0 < r ∧ ∀ z, quotDist D E (E.quotMap D p) z < r → u z = 0 := by
      by_contra hcon
      push Not at hcon
      refine hy (fun r hr => ?_)
      obtain ⟨z, hz, hne⟩ := hcon r hr
      exact ⟨z, hne, hz⟩
    obtain ⟨r, hr, hvan⟩ := hex
    have hev : F =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds p (half_pos hr)] with z hz
      refine hvan _ (lt_of_le_of_lt (hle p z) ?_)
      have ha : ‖p - z‖ < r / 2 := by
        rwa [Metric.mem_ball, dist_comm, dist_eq_norm] at hz
      have hb := normVec_le_two_mul_norm (p - z)
      linarith
    funext i
    show partialDeriv D E i u (E.quotMap D p) = 0
    rw [hpart, hev.fderiv_eq]
    simp
  have hglen : Continuous fun y => euclidNormVec (gradVec D E u y) :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => (hpcont i).pow 2)
  obtain ⟨C₁, hC₁⟩ := hSc.exists_bound_of_continuousOn hucont.continuousOn
  obtain ⟨C₂, hC₂⟩ := hSc.exists_bound_of_continuousOn hglen.continuousOn
  have hsup : supNormQ D E u < ∞ := by
    refine lt_of_le_of_lt (iSup_le fun y => ENNReal.ofReal_le_ofReal (q := max C₁ 0) ?_)
      ENNReal.ofReal_lt_top
    by_cases hy : y ∈ supportQ D E u
    · exact le_max_of_le_left (hC₁ y hy)
    · simp [hoff y hy]
  have hgsup : vecSupNormQ D E (gradVec D E u) < ∞ := by
    refine lt_of_le_of_lt (iSup_le fun y => ENNReal.ofReal_le_ofReal (q := max C₂ 0) ?_)
      ENNReal.ofReal_lt_top
    by_cases hy : y ∈ supportQ D E u
    · exact le_max_of_le_left ((le_abs_self _).trans (hC₂ y hy))
    · simp [hgoff y hy, normVec_zero]
  set G : ℝ := (vecSupNormQ D E (gradVec D E u)).toReal with hGdef
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hGb : ∀ y, euclidNormVec (gradVec D E u y) ≤ G := by
    intro y
    have ha : ENNReal.ofReal (euclidNormVec (gradVec D E u y)) ≤
        vecSupNormQ D E (gradVec D E u) :=
      le_iSup (fun y => ENNReal.ofReal (euclidNormVec (gradVec D E u y))) y
    exact (ENNReal.ofReal_le_iff_le_toReal hgsup.ne).1 ha
  have hL : ∀ y y' : E.Pt D, |u y - u y'| ≤ G * quotDist D E y y' := by
    intro y y'
    obtain ⟨p, rfl⟩ := hhom.2.1 y
    obtain ⟨p', hp', heq⟩ := hl _ y' p rfl
    have ha := abs_sub_le_of_fderiv_bound hF (G := G)
      (fun z => by rw [← hgrad z]; exact hGb _) p p'
    rw [heq] at ha
    have hq : E.quotMap D p' = y' := hp'
    subst hq
    exact ha
  have hLip : IsLipschitzQ D E u := ⟨G, hG0, fun y y' => by
    rw [Real.norm_eq_abs]
    exact hL y y'⟩
  have hleast := (hlipc u hLip).2
  have hLipG : lipConstQ D E u ≤ G := hleast.2 ⟨hG0, hL⟩
  obtain ⟨hLip0, hLipb⟩ := hleast.1
  have hge : ∀ p : Fin 4 → ℝ,
      euclidNormVec (fun i => fderiv ℝ F p (Pi.single i 1)) ≤ lipConstQ D E u := by
    intro p
    set w : Fin 4 → ℝ := fun i => fderiv ℝ F p (Pi.single i 1) with hw
    have hder : HasDerivAt (fun s : ℝ => F (p + s • w)) (fderiv ℝ F p w) 0 := by
      simpa using hasDerivAt_along_line hF p w 0
    have hb : ‖fderiv ℝ F p w‖ ≤ lipConstQ D E u * euclidNormVec w := by
      refine hder.le_of_lip' (mul_nonneg hLip0 (normVec_nonneg w))
        (Eventually.of_forall fun t => ?_)
      have ha := hLipb (E.quotMap D (p + t • w)) (E.quotMap D p)
      have hc := hle (p + t • w) p
      have hd : p + t • w - p = t • w := by abel
      rw [hd, normVec_smul] at hc
      have he := ha.trans (mul_le_mul_of_nonneg_left hc hLip0)
      simp only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs]
      calc |F (p + t • w) - F p| ≤ lipConstQ D E u * (|t| * euclidNormVec w) := he
        _ = lipConstQ D E u * euclidNormVec w * |t| := by ring
    have hsq : fderiv ℝ F p w = euclidNormVec w ^ 2 := by
      rw [clm_apply_eq_sum, euclidNormVec,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      exact Finset.sum_congr rfl fun i _ => by rw [sq]
    rw [hsq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hb
    rcases (normVec_nonneg w).eq_or_lt with ha | ha
    · rw [← ha]
      exact hLip0
    · have hc : euclidNormVec w * euclidNormVec w ≤ lipConstQ D E u * euclidNormVec w := by
        rwa [← sq]
      exact le_of_mul_le_mul_right hc ha
  have hGle : vecSupNormQ D E (gradVec D E u) ≤ ENNReal.ofReal (lipConstQ D E u) := by
    refine iSup_le fun y => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨p, rfl⟩ := hhom.2.1 y
    rw [hgrad]
    exact hge p
  have hLipEq : ENNReal.ofReal (lipConstQ D E u) = vecSupNormQ D E (gradVec D E u) := by
    refine le_antisymm ?_ hGle
    calc ENNReal.ofReal (lipConstQ D E u) ≤ ENNReal.ofReal G :=
          ENNReal.ofReal_le_ofReal hLipG
      _ = vecSupNormQ D E (gradVec D E u) := ENNReal.ofReal_toReal hgsup.ne
  have h40' : (0 : ℝ) ≤ 40 * D.M := by linarith
  have hsharp : sharpNormQ D E u =
      max (supNormQ D E u) (ENNReal.ofReal (40 * D.M) * vecSupNormQ D E (gradVec D E u)) := by
    unfold sharpNormQ
    rw [ENNReal.ofReal_mul h40', hLipEq]
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (40 * D.M) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h40
  refine ⟨hpcont', fun y hy => hgoff y hy, max_lt hsup hgsup, hL, hLip, hLipEq, hsharp, ?_⟩
  rw [hsharp]
  refine max_le ?_ (mul_le_mul_right (le_max_right _ _) _)
  calc supNormQ D E u = 1 * supNormQ D E u := (one_mul _).symm
    _ ≤ ENNReal.ofReal (40 * D.M) * euclidC1Norm D E u :=
        mul_le_mul' hone (le_max_left _ _)
theorem claim_of_wellPosed (hw : WellPosedness.WellPosed) : Claim :=
  fun D E => ⟨quotDist_metric_lifts D E hw, quotMap_continuous_open D E hw, torus_isCompact D hw,
    compact_thickenings D E hw, compactSupport_c1 D E hw⟩
end YangMills.Construction.PeriodicSpace.Kind.QuotientCompactC1
