import YangMills.Construction.Continuum.SharpNormOfATestFunctionAndNeighbourhoodsOfDisjointCompactSetsProof
import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpacesProof
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNormProof
import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBallsProof
import YangMills.Construction.TorusOrFourSpace.StockOfSupportsAndTheCountableFamily
import YangMills.Construction.TorusOrFourSpace.TwoNormsOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
open Filter
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SupportStockProof
open YangMills.Construction.TorusMetric
open YangMills.Construction.PeriodicSpace.Kind
private theorem abs_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
private theorem euclidNormVec_le_two_mul (v : Fin 4 → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ μ, |v μ| ≤ c) :
    euclidNormVec v ≤ 2 * c := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
private theorem euclidNormVec_lt_two_mul (v : Fin 4 → ℝ) (c : ℝ) (hc : 0 < c) (h : ∀ μ, |v μ| < c) :
    euclidNormVec v < 2 * c := by
  unfold euclidNormVec
  refine (Real.sqrt_lt' (by positivity)).2 ?_
  have h1 : ∀ μ ∈ (Finset.univ : Finset (Fin 4)), v μ ^ 2 < c ^ 2 := fun μ _ =>
    sq_lt_sq' (by linarith [(abs_lt.1 (h μ)).1]) (abs_lt.1 (h μ)).2
  calc ∑ μ, v μ ^ 2 < ∑ _μ : Fin 4, c ^ 2 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty h1
    _ = (2 * c) ^ 2 := by simp; ring
private theorem eq_zero_of_euclidNormVec_eq_zero (v : Fin 4 → ℝ) (h : euclidNormVec v = 0) : v = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.eq_zero_of_euclidNormVec_eq_zero <;> assumption
private theorem isOpenWrt_of_isOpen {U : Set (Fin 4 → ℝ)} (hU : IsOpen U) :
    MetricNotions.IsOpenWrt TestFunctions.euclidDistR4 U := by
  intro x hx
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨ε, hε, fun y hy => hb ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
  intro μ
  have h1 := abs_le_euclidNormVec (x - y) μ
  have h2 : euclidNormVec (x - y) < ε := hy
  rw [Real.norm_eq_abs, Pi.sub_apply, abs_sub_comm]
  exact lt_of_le_of_lt h1 h2
private theorem isOpen_preimage_of_continuousWrt {P : Type*} {d : P → P → ℝ} {q : (Fin 4 → ℝ) → P}
    (hq : MetricNotions.IsContinuousWrt TestFunctions.euclidDistR4 d q) {U : Set P}
    (hU : MetricNotions.IsOpenWrt d U) : IsOpen (q ⁻¹' U) := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨r, hr, hb⟩ := hU (q x) hx
  obtain ⟨δ, hδ, hc⟩ := hq x r hr
  refine ⟨δ / 2, by positivity, fun y hy => hb _ (hc y ?_)⟩
  have h1 : ‖y - x‖ < δ / 2 := by simpa [dist_eq_norm] using hy
  have h2 := (pi_norm_lt_iff (by positivity)).1 h1
  have h3 : euclidNormVec (x - y) < 2 * (δ / 2) := by
    refine euclidNormVec_lt_two_mul _ _ (by positivity) fun μ => ?_
    have := h2 μ
    rw [Real.norm_eq_abs, Pi.sub_apply] at this
    rw [Pi.sub_apply, abs_sub_comm]
    exact this
  exact show euclidNormVec (x - y) < δ from by linarith
private theorem isCompactWrt_image {P : Type*} {d : P → P → ℝ} {q : (Fin 4 → ℝ) → P}
    (hq : MetricNotions.IsContinuousWrt TestFunctions.euclidDistR4 d q)
    {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) : MetricNotions.IsCompactWrt d (q '' K) := by
  intro 𝒰 h𝒰 hcov
  obtain ⟨𝒱, hV, hfin, hc⟩ := hK.elim_finite_subcover_image (b := 𝒰) (c := fun U => q ⁻¹' U)
    (fun U hU => isOpen_preimage_of_continuousWrt hq (h𝒰 U hU))
    (fun x hx => by
      obtain ⟨U, hU, hxU⟩ := hcov ⟨x, hx, rfl⟩
      exact Set.mem_biUnion hU hxU)
  refine ⟨𝒱, hV, hfin, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (hc hx)
  exact ⟨U, hU, hxU⟩
private theorem isCompactWrt_of_isClosedWrt_subset {P : Type*} {d : P → P → ℝ} {S C : Set P}
    (hS : MetricNotions.IsCompactWrt d S) (hC : MetricNotions.IsClosedWrt d C) (hCS : C ⊆ S) :
    MetricNotions.IsCompactWrt d C := by apply _root_.YangMills.SharedProofs.p5019 <;> assumption
private theorem partialDerivR4_eq_fderiv {G : (Fin 4 → ℝ) → ℝ} (hG : Differentiable ℝ G) (μ : Fin 4)
    (x : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 μ G x = fderiv ℝ G x (Pi.single μ (1 : ℝ)) := by apply _root_.YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings.partialDerivR4_eq_fderiv <;> assumption
private theorem norm_basisVec_le_one (μ : Fin 4) : ‖(Pi.single μ (1 : ℝ) : Fin 4 → ℝ)‖ ≤ 1 := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.C1Banach.norm_single_one_le <;> assumption
private theorem abs_apply_basisVec_le_opNorm (A : (Fin 4 → ℝ) →L[ℝ] ℝ) (μ : Fin 4) :
    |A (Pi.single μ (1 : ℝ))| ≤ ‖A‖ := by
  have h1 := A.le_opNorm (Pi.single μ (1 : ℝ))
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (mul_le_of_le_one_right (norm_nonneg _) (norm_basisVec_le_one μ))
private theorem opNorm_le_four_mul (A : (Fin 4 → ℝ) →L[ℝ] ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ μ, |A (Pi.single μ (1 : ℝ))| ≤ c) : ‖A‖ ≤ 4 * c := by
  refine A.opNorm_le_bound (by positivity) fun v => ?_
  have hv : v = ∑ μ, v μ • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) := by
    funext ν
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : ∀ μ ∈ (Finset.univ : Finset (Fin 4)),
      ‖A (v μ • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))‖ ≤ c * ‖v‖ := by
    intro μ _
    rw [map_smul, norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (h μ) (by simpa using norm_le_pi_norm v μ) (abs_nonneg _) hc
  calc ‖A v‖ = ‖∑ μ, A (v μ • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))‖ := by
        conv_lhs => rw [hv, map_sum]
    _ ≤ ∑ μ, ‖A (v μ • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _μ : Fin 4, c * ‖v‖ := Finset.sum_le_sum h1
    _ = 4 * c * ‖v‖ := by simp; ring
private theorem exists_c1_uniform_limit (F : ℕ → (Fin 4 → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (h0 : ∀ ε : ℝ, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, ∀ x, |F i x - F j x| < ε)
    (h1 : ∀ ε : ℝ, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, ∀ x,
      ‖fderiv ℝ (F i) x - fderiv ℝ (F j) x‖ < ε) :
    ∃ G : (Fin 4 → ℝ) → ℝ, ContDiff ℝ 1 G ∧
      (∀ x, Tendsto (fun j => F j x) atTop (𝓝 (G x))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ J, ∀ j ≥ J, ∀ x, |F j x - G x| < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ J, ∀ j ≥ J, ∀ x, ‖fderiv ℝ (F j) x - fderiv ℝ G x‖ < ε) := by
  have hu0 : UniformCauchySeqOn F atTop Set.univ :=
    Metric.uniformCauchySeqOn_iff.2 fun ε hε => by
      obtain ⟨J, hJ⟩ := h0 ε hε
      exact ⟨J, fun i hi j hj x _ => by simpa [Real.dist_eq] using hJ i hi j hj x⟩
  have hu1 : UniformCauchySeqOn (fun j => fderiv ℝ (F j)) atTop Set.univ :=
    Metric.uniformCauchySeqOn_iff.2 fun ε hε => by
      obtain ⟨J, hJ⟩ := h1 ε hε
      exact ⟨J, fun i hi j hj x _ => by simpa [dist_eq_norm] using hJ i hi j hj x⟩
  have hp0 : ∀ x, ∃ l, Tendsto (fun j => F j x) atTop (𝓝 l) := fun x =>
    cauchySeq_tendsto_of_complete (hu0.cauchy_map (Set.mem_univ x))
  have hp1 : ∀ x, ∃ l, Tendsto (fun j => fderiv ℝ (F j) x) atTop (𝓝 l) := fun x =>
    cauchySeq_tendsto_of_complete (hu1.cauchy_map (Set.mem_univ x))
  choose G hG using hp0
  choose A hA using hp1
  have t0 : TendstoUniformlyOn F G atTop Set.univ :=
    hu0.tendstoUniformlyOn_of_tendsto fun x _ => hG x
  have t1 : TendstoUniformlyOn (fun j => fderiv ℝ (F j)) A atTop Set.univ :=
    hu1.tendstoUniformlyOn_of_tendsto fun x _ => hA x
  have hder : ∀ x, HasFDerivAt G (A x) x := fun x =>
    hasFDerivAt_of_tendstoUniformlyOn isOpen_univ t1
      (fun n y _ => ((hF n).differentiable (by norm_num) y).hasFDerivAt)
      (fun y _ => hG y) (Set.mem_univ x)
  have hfd : fderiv ℝ G = A := funext fun x => (hder x).fderiv
  have hAc : Continuous A := by
    rw [← continuousOn_univ]
    refine t1.continuousOn (Frequently.of_forall fun n => ?_)
    exact ((hF n).continuous_fderiv (by norm_num)).continuousOn
  refine ⟨G, contDiff_one_iff_fderiv.2 ⟨fun x => (hder x).differentiableAt, hfd ▸ hAc⟩, hG, ?_, ?_⟩
  · intro ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 t0 ε hε)
    refine ⟨J, fun j hj x => ?_⟩
    have := hJ j hj x (Set.mem_univ x)
    rwa [Real.dist_eq, abs_sub_comm] at this
  · intro ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 t1 ε hε)
    refine ⟨J, fun j hj x => ?_⟩
    have := hJ j hj x (Set.mem_univ x)
    rwa [dist_eq_norm, norm_sub_rev, ← hfd] at this
section OnTheQuotient
variable (D : Params) (E : Kind)
private theorem side_pos : 0 < D.side := by apply _root_.YangMills.SharedProofs.p25685 <;> assumption
private theorem isCompact_box (b : RationalBox) : IsCompact b.toSet :=
  isCompact_univ_pi fun _ => isCompact_Icc
private theorem quotDist_eq_on_small_box
    (hw : WellPosedness.QuotDistEqMinTranslateNorm D torus) (b : RationalBox)
    (hb : b.diam < D.side / 2) {x x' : Fin 4 → ℝ} (hx : x ∈ b.toSet) (hx' : x' ∈ b.toSet) :
    quotDist D torus (quotMap D torus x) (quotMap D torus x') = euclidNormVec (x - x') := by
  have hdiam : euclidNormVec (x - x') ≤ b.diam := by
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
    have h1 := hx μ (Set.mem_univ μ)
    have h2 := hx' μ (Set.mem_univ μ)
    rw [Pi.sub_apply]
    exact sq_le_sq' (by linarith [h1.1, h1.2, h2.1, h2.2]) (by linarith [h1.1, h1.2, h2.1, h2.2])
  obtain ⟨⟨k, hk, hr⟩, hlow⟩ := hw x x'
  have h0 : quotDist D torus (quotMap D torus x) (quotMap D torus x') ≤
      euclidNormVec (x - x') := hlow ⟨0, (periodGroup D torus).zero_mem, by simp⟩
  by_cases hk0 : k = 0
  · subst hk0
    simpa using hr
  · exfalso
    obtain ⟨n, hn⟩ := hk
    have hex : ∃ μ, n μ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hk0 (funext fun μ => by simp [hn μ, hall μ])
    obtain ⟨μ, hμ⟩ := hex
    have hside := side_pos D
    have hk1 : D.side ≤ |k μ| := by
      rw [hn μ, abs_mul, abs_of_pos hside]
      have : (1 : ℝ) ≤ |(n μ : ℝ)| := by
        exact_mod_cast Int.one_le_abs hμ
      nlinarith
    have h1 := abs_le_euclidNormVec (x - x' - k) μ
    have h2 := abs_le_euclidNormVec (x - x') μ
    have h3 : |k μ| ≤ |(x - x' - k) μ| + |(x - x') μ| := by
      have : k μ = (x - x') μ - (x - x' - k) μ := by simp
      rw [this]
      exact (abs_sub _ _).trans (by rw [add_comm])
    rw [← hr] at h1
    linarith
private theorem supportStock_countable : (supportStock D E).Countable := by
  have : Countable RationalBox :=
    Function.Injective.countable (f := fun b : RationalBox => (b.lo, b.hi)) (by
      rintro ⟨a, b, h⟩ ⟨a', b', h'⟩ he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rfl)
  refine (Set.countable_range
    (fun p : (Σ r : ℕ, Fin r → RationalBox) => ⋃ i, E.quotMap D '' (p.2 i).toSet)).mono ?_
  rintro Q ⟨r, b, _, rfl⟩
  exact ⟨⟨r, b⟩, rfl⟩
private theorem isCompact_iUnion_boxes {r : ℕ} (b : Fin r → RationalBox) :
    IsCompact (⋃ i, (b i).toSet) :=
  isCompact_iUnion fun i => isCompact_box (b i)
private theorem isCompactQ_of_mem_supportStock
    (hc : MetricNotions.IsContinuousWrt TestFunctions.euclidDistR4 (quotDist D E)
      (E.quotMap D)) {Q : Set (E.Pt D)} (hQ : Q ∈ supportStock D E) :
    IsCompactQ D E Q := by
  obtain ⟨r, b, _, rfl⟩ := hQ
  rw [← Set.image_iUnion]
  exact isCompactWrt_image hc (isCompact_iUnion_boxes b)
private theorem isClosedQ_of_isCompactQ
    (h : QuotientCompactC1.CompactSetsThickenings D E)
    (hnn : ∀ y y' : E.Pt D, 0 ≤ quotDist D E y y')
    {S : Set (E.Pt D)} (hS : IsCompactQ D E S) : IsClosedQ D E S := by
  intro y hy
  have hsing : IsCompactQ D E ({y} : Set (E.Pt D)) := by
    intro 𝒰 _ hcov
    obtain ⟨U, hU, hyU⟩ := hcov (Set.mem_singleton y)
    exact ⟨{U}, by simpa using hU, Set.finite_singleton U, by simpa using hyU⟩
  have hpos := h.1 {y} S hsing hS (Set.disjoint_singleton_left.2 hy)
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
  refine ⟨r, by exact_mod_cast hr0, fun z hz hzS => ?_⟩
  have h1 : setInfDist D E {y} S ≤ ENNReal.ofReal (quotDist D E y z) :=
    iInf₂_le_of_le y rfl (iInf₂_le z hzS)
  have h2 : ENNReal.ofReal (r : ℝ) ≤ ENNReal.ofReal (quotDist D E y z) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hr.le.trans h1
  have h3 := (ENNReal.ofReal_le_ofReal_iff (hnn y z)).1 h2
  linarith
private theorem isClosedQ_closureQ
    (htri : ∀ y y' y'' : E.Pt D, quotDist D E y y'' ≤ quotDist D E y y' + quotDist D E y' y'')
    (Z : Set (E.Pt D)) : IsClosedQ D E (closureQ D E Z) := by
  intro y hy
  have hy' : ¬ ∀ r : ℝ, 0 < r → ∃ z ∈ Z, quotDist D E y z < r := hy
  push Not at hy'
  obtain ⟨r, hr, hb⟩ := hy'
  refine ⟨r / 2, by positivity, fun w hw hwc => ?_⟩
  obtain ⟨z, hz, hwz⟩ := hwc (r / 2) (by positivity)
  have := hb z hz
  have := htri y w z
  linarith
private theorem supportQ_subset {Q : Set (E.Pt D)} (hQ : IsClosedQ D E Q)
    {f : E.Pt D → ℝ} (hf : ∀ y, y ∉ Q → f y = 0) : supportQ D E f ⊆ Q := by
  intro y hy
  by_contra hyQ
  obtain ⟨r, hr, hb⟩ := hQ y hyQ
  obtain ⟨z, hz, hyz⟩ := hy r hr
  exact hz (hf z (hb z hyz))
private theorem eq_zero_of_not_mem_supportQ (h0 : ∀ y y' : E.Pt D, quotDist D E y y' = 0 ↔ y = y')
    {f : E.Pt D → ℝ} {y : E.Pt D} (hy : y ∉ supportQ D E f) : f y = 0 := by
  by_contra hne
  exact hy fun r hr => ⟨y, hne, by rw [(h0 y y).2 rfl]; exact hr⟩
private theorem c1VanishingOutside_eq_c1SupportedIn
    (hm : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    (hn : QuotientCompactC1.CompactSetsThickenings D E)
    {Q : Set (E.Pt D)} (hQ : IsCompactQ D E Q) :
    c1VanishingOutside D E Q = c1SupportedIn D E Q := by
  have hcl := isClosedQ_of_isCompactQ D E hn hm.1 hQ
  ext f
  constructor
  · rintro ⟨hf, h0⟩
    have hs := supportQ_subset D E hcl h0
    exact ⟨hf, isCompactWrt_of_isClosedWrt_subset hQ
      (isClosedQ_closureQ D E hm.2.2.2.1 _) hs, hs⟩
  · rintro ⟨hf, _, hs⟩
    exact ⟨hf, fun y hy => eq_zero_of_not_mem_supportQ D E hm.2.1 fun h => hy (hs h)⟩
private theorem contDiff_comp_quotMap {u : E.Pt D → ℝ} (hu : IsC1Fn D E u) :
    ContDiff ℝ 1 (u ∘ E.quotMap D) := hu
private theorem differentiable_comp_quotMap {u : E.Pt D → ℝ} (hu : IsC1Fn D E u) :
    Differentiable ℝ (u ∘ E.quotMap D) :=
  (contDiff_comp_quotMap D E hu).differentiable (by norm_num)
private theorem gradVec_quotMap_eq_fderiv
    (hw : WellPosedness.PartialDerivDescends D E)
    {u : E.Pt D → ℝ} (hu : IsC1Fn D E u) (x : Fin 4 → ℝ) (μ : Fin 4) :
    gradVec D E u (E.quotMap D x) μ =
      fderiv ℝ (u ∘ E.quotMap D) x (Pi.single μ (1 : ℝ)) := by
  have h1 := congrFun ((hw u hu).2 μ).2.2 x
  rw [partialDerivR4_eq_fderiv (differentiable_comp_quotMap D E hu)] at h1
  exact h1
private theorem isC1Fn_sub {u v : E.Pt D → ℝ} (hu : IsC1Fn D E u) (hv : IsC1Fn D E v) :
    IsC1Fn D E (u - v) :=
  (contDiff_comp_quotMap D E hu).sub (contDiff_comp_quotMap D E hv)
private theorem fderiv_sub_comp_quotMap {u v : E.Pt D → ℝ} (hu : IsC1Fn D E u)
    (hv : IsC1Fn D E v) (x : Fin 4 → ℝ) :
    fderiv ℝ ((u - v) ∘ E.quotMap D) x =
      fderiv ℝ (u ∘ E.quotMap D) x - fderiv ℝ (v ∘ E.quotMap D) x :=
  fderiv_sub (f := u ∘ E.quotMap D) (g := v ∘ E.quotMap D)
    (differentiable_comp_quotMap D E hu x) (differentiable_comp_quotMap D E hv x)
private theorem bounds_of_euclidC1Norm_lt {g : E.Pt D → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : euclidC1Norm D E g < ENNReal.ofReal ε) :
    (∀ y, |g y| < ε) ∧ ∀ y, euclidNormVec (gradVec D E g y) < ε := by
  obtain ⟨h1, h2⟩ := max_lt_iff.1 h
  refine ⟨fun y => ?_, fun y => ?_⟩
  · exact (ENNReal.ofReal_lt_ofReal_iff hε).1
      (lt_of_le_of_lt (le_iSup (fun y => ENNReal.ofReal |g y|) y) h1)
  · exact (ENNReal.ofReal_lt_ofReal_iff hε).1
      (lt_of_le_of_lt (le_iSup (fun y => ENNReal.ofReal (euclidNormVec (gradVec D E g y))) y) h2)
private theorem euclidC1Norm_le_of_bounds {g : E.Pt D → ℝ} {c : ℝ} (h1 : ∀ y, |g y| ≤ c)
    (h2 : ∀ y, euclidNormVec (gradVec D E g y) ≤ c) :
    euclidC1Norm D E g ≤ ENNReal.ofReal c :=
  max_le (iSup_le fun y => ENNReal.ofReal_le_ofReal (h1 y))
    (iSup_le fun y => ENNReal.ofReal_le_ofReal (h2 y))
private theorem norm_fderiv_sub_le_gradVec
    (hw : WellPosedness.PartialDerivDescends D E)
    {u v : E.Pt D → ℝ} (hu : IsC1Fn D E u) (hv : IsC1Fn D E v) (x : Fin 4 → ℝ) :
    ‖fderiv ℝ (u ∘ E.quotMap D) x - fderiv ℝ (v ∘ E.quotMap D) x‖ ≤
      4 * euclidNormVec (gradVec D E (u - v) (E.quotMap D x)) := by
  refine opNorm_le_four_mul _ _ (euclidNormVec_nonneg _) fun μ => ?_
  rw [← fderiv_sub_comp_quotMap D E hu hv, ← gradVec_quotMap_eq_fderiv D E hw (isC1Fn_sub D E hu hv)]
  exact abs_le_euclidNormVec _ μ
private theorem gradVec_le_norm_fderiv_sub
    (hw : WellPosedness.PartialDerivDescends D E)
    {u v : E.Pt D → ℝ} (hu : IsC1Fn D E u) (hv : IsC1Fn D E v) (x : Fin 4 → ℝ) :
    euclidNormVec (gradVec D E (u - v) (E.quotMap D x)) ≤
      2 * ‖fderiv ℝ (u ∘ E.quotMap D) x - fderiv ℝ (v ∘ E.quotMap D) x‖ := by
  refine euclidNormVec_le_two_mul _ _ (norm_nonneg _) fun μ => ?_
  rw [gradVec_quotMap_eq_fderiv D E hw (isC1Fn_sub D E hu hv), fderiv_sub_comp_quotMap D E hu hv]
  exact abs_apply_basisVec_le_opNorm _ μ
end OnTheQuotient
section FunctionSpaces
variable (D : Params) (E : Kind)
private theorem isFunctionSpaceNorm_euclidC1Norm {Q : Set (E.Pt D)}
    (hf : VectorClasses.ClassesLinear D E Q)
    (ht : ∀ V : Submodule ℝ (E.Pt D → ℝ),
      (∀ u ∈ V, u ∈ c1Set D E ∧ euclidC1Norm D E u < ⊤) →
        C1NormComparison.EquivalentNormsOn D E V)
    (hfin : ∀ u ∈ c1SupportedIn D E Q, euclidC1Norm D E u < ⊤)
    (heq : c1VanishingOutside D E Q = c1SupportedIn D E Q) :
    IsFunctionSpaceNorm D E (euclidC1Norm D E) (c1VanishingOutside D E Q) := by
  obtain ⟨W, hW⟩ := hf.2.1
  have hmem : ∀ f, f ∈ c1VanishingOutside D E Q ↔ f ∈ W := fun f => by
    rw [heq, ← hW]
    rfl
  have hmem' : ∀ f, f ∈ W ↔ f ∈ c1SupportedIn D E Q := fun f => by
    rw [← heq, hmem]
  have n := (ht W fun u hu => ⟨((hmem' u).1 hu).1, hfin u ((hmem' u).1 hu)⟩).1
  refine ⟨(hmem 0).2 W.zero_mem, fun f hf g hg a b => (hmem _).2 ?_, fun f hf => n.finite f ((hmem f).1 hf),
    fun f hf h => (n.eq_zero_iff f ((hmem f).1 hf)).1 h,
    fun f hf a => n.homogeneous a f ((hmem f).1 hf),
    fun f hf g hg => n.triangle f ((hmem f).1 hf) g ((hmem g).1 hg)⟩
  exact W.add_mem (W.smul_mem a ((hmem f).1 hf)) (W.smul_mem b ((hmem g).1 hg))
private theorem isCompleteWrt_euclidC1Norm {Q : Set (E.Pt D)}
    (hw : WellPosedness.PartialDerivDescends D E)
    (hs : Function.Surjective (E.quotMap D)) :
    IsCompleteWrt D E (euclidC1Norm D E) (c1VanishingOutside D E Q) := by
  intro u hu hc
  have hC : ∀ j, IsC1Fn D E (u j) := fun j => (hu j).1
  obtain ⟨G, hG, hpt, hu0, hu1⟩ := exists_c1_uniform_limit (fun j => u j ∘ E.quotMap D)
    (fun j => contDiff_comp_quotMap D E (hC j))
    (fun ε hε => by
      obtain ⟨J, hJ⟩ := hc ε hε
      exact ⟨J, fun i hi j hj x => (bounds_of_euclidC1Norm_lt D E hε (hJ i hi j hj)).1 (E.quotMap D x)⟩)
    (fun ε hε => by
      obtain ⟨J, hJ⟩ := hc (ε / 8) (by positivity)
      refine ⟨J, fun i hi j hj x => ?_⟩
      have h1 := norm_fderiv_sub_le_gradVec D E hw (hC i) (hC j) x
      have h2 := (bounds_of_euclidC1Norm_lt D E (by positivity) (hJ i hi j hj)).2 (E.quotMap D x)
      linarith)
  obtain ⟨s, hs'⟩ := hs.hasRightInverse
  have hfq : (G ∘ s) ∘ E.quotMap D = G := by
    funext x
    have h2 : (fun j => (u j ∘ E.quotMap D) (s (E.quotMap D x))) =
        fun j => (u j ∘ E.quotMap D) x :=
      funext fun j => by simp only [Function.comp, hs' (E.quotMap D x)]
    exact tendsto_nhds_unique (hpt (s (E.quotMap D x))) (h2 ▸ hpt x)
  have hfC : IsC1Fn D E (G ∘ s) := by
    unfold Kind.IsC1Fn TestFunctions.IsC1R4
    rw [hfq]
    exact hG
  have hfQ : ∀ y, y ∉ Q → (G ∘ s) y = 0 := by
    intro y hy
    have h2 : (fun j => (u j ∘ E.quotMap D) (s y)) = fun _ => (0 : ℝ) :=
      funext fun j => by simp only [Function.comp, hs' y, (hu j).2 y hy]
    exact tendsto_nhds_unique (hpt (s y)) (h2 ▸ tendsto_const_nhds)
  refine ⟨G ∘ s, ⟨hfC, hfQ⟩, fun ε hε => ?_⟩
  obtain ⟨J0, hJ0⟩ := hu0 (ε / 4) (by positivity)
  obtain ⟨J1, hJ1⟩ := hu1 (ε / 4) (by positivity)
  refine ⟨max J0 J1, fun j hj => lt_of_le_of_lt (euclidC1Norm_le_of_bounds D E (c := ε / 2) ?_ ?_)
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))⟩
  · intro y
    obtain ⟨x, rfl⟩ := hs y
    have h1 := hJ0 j (le_of_max_le_left hj) x
    have h2 : (G ∘ s) (E.quotMap D x) = G x := congrFun hfq x
    have h3 : |(u j - G ∘ s) (E.quotMap D x)| = |(u j ∘ E.quotMap D) x - G x| := by
      rw [Pi.sub_apply, h2]
      rfl
    rw [h3]
    linarith
  · intro y
    obtain ⟨x, rfl⟩ := hs y
    have h1 := hJ1 j (le_of_max_le_right hj) x
    have h2 := gradVec_le_norm_fderiv_sub D E hw (hC j) hfC x
    rw [hfq] at h2
    linarith
private theorem exists_countable_dense_euclidC1Norm {Q : Set (E.Pt D)} (hQ : Q ∈ supportStock D E)
    (hw : WellPosedness.PartialDerivDescends D E)
    (hvan : ∀ g ∈ c1VanishingOutside D E Q, ∀ y, y ∉ Q → gradVec D E g y = 0) :
    ∃ A, A ⊆ c1VanishingOutside D E Q ∧ A.Countable ∧
      IsDenseWrt D E (euclidC1Norm D E) (c1VanishingOutside D E Q) A := by
  obtain ⟨r, b, _, hQe⟩ := hQ
  have hK : IsCompact (⋃ i, (b i).toSet) := isCompact_iUnion_boxes b
  have hKQ : ∀ y ∈ Q, ∃ x ∈ ⋃ i, (b i).toSet, E.quotMap D x = y := by
    intro y hy
    rw [hQe] at hy
    obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.1 hy
    exact ⟨x, Set.mem_iUnion.2 ⟨i, hx⟩, rfl⟩
  generalize (⋃ i, (b i).toSet) = K at hK hKQ
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let lift : ∀ f : E.Pt D → ℝ, IsC1Fn D E f →
      C(K, ℝ × ((Fin 4 → ℝ) →L[ℝ] ℝ)) := fun f hf =>
    ⟨fun x => ((f ∘ E.quotMap D) x.1, fderiv ℝ (f ∘ E.quotMap D) x.1),
      ((contDiff_comp_quotMap D E hf).continuous.comp continuous_subtype_val).prodMk
        (((contDiff_comp_quotMap D E hf).continuous_fderiv (by norm_num)).comp continuous_subtype_val)⟩
  let S : Set C(K, ℝ × ((Fin 4 → ℝ) →L[ℝ] ℝ)) :=
    {ξ | ∃ f, ∃ hf : f ∈ c1VanishingOutside D E Q, ξ = lift f hf.1}
  have hsep : TopologicalSpace.IsSeparable S := .of_separableSpace S
  obtain ⟨T, hTS, hTc, hTd⟩ := hsep.exists_countable_dense_subset
  have hch : ∀ ξ : T, ∃ f, ∃ hf : f ∈ c1VanishingOutside D E Q, ξ.1 = lift f hf.1 :=
    fun ξ => hTS ξ.2
  choose p hp hpe using hch
  have : Countable T := hTc.to_subtype
  refine ⟨Set.range p, by rintro _ ⟨ξ, rfl⟩; exact hp ξ, Set.countable_range p, ?_⟩
  intro f hf ε hε
  have hcl := hTd (show lift f hf.1 ∈ S from ⟨f, hf, rfl⟩)
  obtain ⟨ξ, hξ, hd⟩ := (Metric.mem_closure_iff (α := C(K, ℝ × ((Fin 4 → ℝ) →L[ℝ] ℝ)))).1 hcl (ε / 4) (by positivity)
  obtain ⟨g, hgdef⟩ : ∃ g, p ⟨ξ, hξ⟩ = g := ⟨_, rfl⟩
  have hg : g ∈ c1VanishingOutside D E Q := hgdef ▸ hp ⟨ξ, hξ⟩
  have hxi : ξ = lift g hg.1 := by
    subst hgdef
    exact hpe ⟨ξ, hξ⟩
  have hnear : ∀ x ∈ K, |(f ∘ E.quotMap D) x - (g ∘ E.quotMap D) x| < ε / 4 ∧
      ‖fderiv ℝ (f ∘ E.quotMap D) x - fderiv ℝ (g ∘ E.quotMap D) x‖ < ε / 4 := by
    intro x hx
    have h1 := ContinuousMap.dist_apply_le_dist (f := lift f hf.1) (g := ξ) (⟨x, hx⟩ : K)
    have h2 := lt_of_le_of_lt h1 hd
    rw [hxi, Prod.dist_eq, max_lt_iff] at h2
    refine ⟨?_, ?_⟩
    · have := h2.1
      rwa [Real.dist_eq] at this
    · have := h2.2
      rwa [dist_eq_norm] at this
  have hfg : f - g ∈ c1VanishingOutside D E Q :=
    ⟨isC1Fn_sub D E hf.1 hg.1, fun y hy => by simp [hf.2 y hy, hg.2 y hy]⟩
  refine ⟨g, ⟨⟨ξ, hξ⟩, ?_⟩, lt_of_le_of_lt (euclidC1Norm_le_of_bounds D E (c := ε / 2) ?_ ?_)
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))⟩
  · exact hgdef
  · intro y
    by_cases hy : y ∈ Q
    · obtain ⟨x, hx, rfl⟩ := hKQ y hy
      have := (hnear x hx).1
      rw [Pi.sub_apply]
      exact le_of_lt (by simpa using this.trans (by linarith))
    · rw [hfg.2 y hy, abs_zero]
      positivity
  · intro y
    by_cases hy : y ∈ Q
    · obtain ⟨x, hx, rfl⟩ := hKQ y hy
      have h1 := (hnear x hx).2
      have h2 := gradVec_le_norm_fderiv_sub D E hw hf.1 hg.1 x
      linarith
    · rw [hvan _ hfg y hy]
      have : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [euclidNormVec]
      rw [this]
      positivity
private theorem isDenseWrt_sharpNormQ_of_euclidC1Norm {V : Set (E.Pt D → ℝ)}
    (hbd : ∀ g ∈ V, sharpNormQ D E g ≤ ENNReal.ofReal (40 * D.M) * euclidC1Norm D E g)
    (hsub : ∀ f ∈ V, ∀ g ∈ V, f - g ∈ V) {A : Set (E.Pt D → ℝ)} (hA : A ⊆ V)
    (hd : IsDenseWrt D E (euclidC1Norm D E) V A) : IsDenseWrt D E (sharpNormQ D E) V A := by
  intro f hf ε hε
  have hM : 0 < 40 * D.M := by linarith [D.one_le_M]
  have hM0 : 0 < D.M := by linarith [D.one_le_M]
  obtain ⟨g, hg, hlt⟩ := hd f hf (ε / (80 * D.M)) (by positivity)
  refine ⟨g, hg, lt_of_le_of_lt (hbd _ (hsub f hf g (hA hg))) ?_⟩
  calc ENNReal.ofReal (40 * D.M) * euclidC1Norm D E (f - g)
      ≤ ENNReal.ofReal (40 * D.M) * ENNReal.ofReal (ε / (80 * D.M)) := by
        gcongr
    _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_mul hM.le]
        congr 1
        field_simp
        ring
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
private theorem exists_box_nbhd (hs : Function.Surjective (E.quotMap D))
    (hq : QuotientCompactC1.QuotMapContinuousOpen D E)
    (hm : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    {W : Set (E.Pt D)} (hW : IsOpenQ D E W) {x : E.Pt D} (hx : x ∈ W) :
    ∃ b : RationalBox, E.AdmitsBox D b ∧ ∃ U, IsOpenQ D E U ∧ x ∈ U ∧
      U ⊆ E.quotMap D '' b.toSet ∧ E.quotMap D '' b.toSet ⊆ W := by
  obtain ⟨r, hr, hb⟩ := hW x hx
  obtain ⟨t, rfl⟩ := hs x
  have hside := side_pos D
  obtain ⟨ρ, hρ, hρr, hρs⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ρ ≤ D.side / 2 :=
    ⟨min r (D.side / 2), lt_min hr (by positivity), min_le_left _ _, min_le_right _ _⟩
  have ha : ∀ μ, ∃ a : ℚ, t μ - ρ / 8 < a ∧ (a : ℝ) < t μ := fun μ =>
    exists_rat_btwn (by linarith)
  have hc : ∀ μ, ∃ c : ℚ, t μ < c ∧ (c : ℝ) < t μ + ρ / 8 := fun μ =>
    exists_rat_btwn (by linarith)
  choose a ha1 ha2 using ha
  choose c hc1 hc2 using hc
  let B : RationalBox := ⟨a, c, fun μ => by exact_mod_cast (ha2 μ).trans (hc1 μ)⟩
  have hdiam : B.diam < D.side / 2 := by
    have h1 := euclidNormVec_lt_two_mul (fun μ => (c μ : ℝ) - a μ) (ρ / 4) (by positivity)
      (fun μ => abs_lt.2 ⟨by linarith [ha2 μ, hc1 μ], by linarith [ha1 μ, hc2 μ]⟩)
    have h2 : B.diam = euclidNormVec (fun μ => (c μ : ℝ) - a μ) := rfl
    rw [h2]
    linarith
  have hadm : ∀ E' : Kind, E'.AdmitsBox D B := fun E' => by
    cases E'
    · exact trivial
    · exact hdiam
  refine ⟨B, hadm E, E.quotMap D '' Set.pi Set.univ fun μ => Set.Ioo (a μ : ℝ) (c μ),
    hq.2.1 _ (isOpenWrt_of_isOpen (isOpen_set_pi Set.finite_univ fun μ _ => isOpen_Ioo)),
    ⟨t, fun μ _ => ⟨ha2 μ, hc1 μ⟩, rfl⟩,
    Set.image_mono fun z hz μ hμ => Set.Ioo_subset_Icc_self (hz μ hμ), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  refine hb _ (lt_of_le_of_lt (hm.2.2.2.2.1 t z) ?_)
  have h1 := euclidNormVec_lt_two_mul (t - z) (ρ / 4) (by positivity) fun μ => by
    have h2 := hz μ (Set.mem_univ μ)
    have h3 : (a μ : ℝ) ≤ z μ := h2.1
    have h4 : z μ ≤ (c μ : ℝ) := h2.2
    rw [Pi.sub_apply]
    exact abs_lt.2 ⟨by linarith [hc2 μ], by linarith [ha1 μ]⟩
  linarith
private theorem exists_mem_supportStock_between (hs : Function.Surjective (E.quotMap D))
    (hq : QuotientCompactC1.QuotMapContinuousOpen D E)
    (hm : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    (S W : Set (E.Pt D)) (hS : IsCompactQ D E S) (hW : IsOpenQ D E W) (hSW : S ⊆ W) :
    ∃ Q ∈ supportStock D E, S ⊆ Q ∧ Q ⊆ W := by
  obtain ⟨𝒱, hV, hfin, hc⟩ := hS
    {U | IsOpenQ D E U ∧ ∃ b : RationalBox, E.AdmitsBox D b ∧
      U ⊆ E.quotMap D '' b.toSet ∧ E.quotMap D '' b.toSet ⊆ W}
    (fun U hU => hU.1)
    (fun x hx => by
      obtain ⟨b, hb, U, hU, hxU, h1, h2⟩ := exists_box_nbhd D E hs hq hm hW (hSW hx)
      exact ⟨U, ⟨hU, b, hb, h1, h2⟩, hxU⟩)
  have hch : ∀ U : 𝒱, ∃ b : RationalBox, E.AdmitsBox D b ∧
      U.1 ⊆ E.quotMap D '' b.toSet ∧ E.quotMap D '' b.toSet ⊆ W :=
    fun U => (hV U.2).2
  choose bb hadm hsub hin using hch
  have : Finite 𝒱 := hfin.to_subtype
  let e := Finite.equivFin 𝒱
  refine ⟨⋃ i, E.quotMap D '' (bb (e.symm i)).toSet,
    ⟨_, fun i => bb (e.symm i), fun i => hadm _, rfl⟩, ?_, Set.iUnion_subset fun i => hin _⟩
  intro x hx
  obtain ⟨U, hU, hxU⟩ := hc hx
  refine Set.mem_iUnion.2 ⟨e ⟨U, hU⟩, ?_⟩
  rw [Equiv.symm_apply_apply]
  exact hsub ⟨U, hU⟩ hxU
private theorem tupleFamily_countable {F : supportStock D E → Set (E.Pt D → ℝ)}
    (hF : IsDenseFamily D E F) : (tupleFamily D E F).Countable := by
  have hcs : Countable (supportStock D E) := (supportStock_countable D E).to_subtype
  have hn : ∀ n : ℕ, (⋃ Q : Fin n → supportStock D E,
      Set.pi Set.univ fun i => F (Q i)).Countable := fun n =>
    Set.countable_iUnion fun Q => Set.countable_univ_pi fun i => (hF (Q i)).1
  refine (Set.countable_iUnion fun n => (hn n).image
    (fun φ => (⟨n, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ))).mono ?_
  rintro ⟨n, φ⟩ ⟨_, Q, hQ⟩
  exact Set.mem_iUnion.2 ⟨n, φ, Set.mem_iUnion.2 ⟨Q, fun i _ => hQ.2 i⟩, rfl⟩
private theorem setInfDist_anti {S S' T T' : Set (E.Pt D)} (h : S ⊆ T) (h' : S' ⊆ T') :
    setInfDist D E T T' ≤ setInfDist D E S S' :=
  le_iInf₂ fun z hz => le_iInf₂ fun z' hz' => iInf₂_le_of_le z (h hz) (iInf₂_le z' (h' hz'))
private theorem iInf_pos_of_finite {ι : Type*} [Finite ι] {g : ι → ℝ≥0∞} (h : ∀ i, 0 < g i) :
    0 < ⨅ i, g i := by
  by_cases hne : Nonempty ι
  · obtain ⟨i0, h0⟩ := Finite.exists_min g
    exact lt_of_lt_of_le (h i0) (le_iInf h0)
  · have hemp := not_nonempty_iff.1 hne
    rw [iInf_of_isEmpty, sInf_empty]
    exact ENNReal.zero_lt_top
private theorem minPairwiseDist_pos {n : ℕ} (Q : Fin n → Set (E.Pt D))
    (h : ∀ i k, i ≠ k → 0 < setInfDist D E (Q i) (Q k)) :
    0 < minPairwiseDist D E Q := by
  refine iInf_pos_of_finite fun i => iInf_pos_of_finite fun k => ?_
  by_cases hik : i = k
  · simp [hik]
  · rw [iInf_pos hik]
    exact h i k hik
end FunctionSpaces
theorem supportStockAndCountableFamily_holds (hlin : VectorClasses.Claim)
    (hcmp : C1NormComparison.statement) (hwell : WellPosedness.WellPosed)
    (hquot : QuotientCompactC1.Claim) :
    SupportStockAndCountableFamily := by
  intro D
  refine ⟨fun b hb => ?_, fun E => ?_⟩
  · obtain ⟨_, _, _, _, _, _, h7, _⟩ := hwell D torus
    obtain ⟨hm, _⟩ := hquot D torus
    have hk : ∀ x ∈ b.toSet, ∀ x' ∈ b.toSet,
        quotDist D torus (quotMap D torus x) (quotMap D torus x') =
          euclidNormVec (x - x') :=
      fun x hx x' hx' => quotDist_eq_on_small_box D h7 b hb hx hx'
    refine ⟨hk, fun x hx x' hx' he => ?_⟩
    have h1 := hk x hx x' hx'
    rw [he, (hm.2.1 _ _).2 rfl] at h1
    exact sub_eq_zero.1 (eq_zero_of_euclidNormVec_eq_zero _ h1.symm)
  · obtain ⟨h1, _, _, _, _, _, _, _, _, h10, _, _⟩ := hwell D E
    obtain ⟨hm, hq, _, hn, hcs⟩ := hquot D E
    have hsurj := h1.2.1
    have hcomp : ∀ Q ∈ supportStock D E, IsCompactQ D E Q :=
      fun Q hQ => isCompactQ_of_mem_supportStock D E hq.1 hQ
    have heq : ∀ Q ∈ supportStock D E, c1VanishingOutside D E Q = c1SupportedIn D E Q :=
      fun Q hQ => c1VanishingOutside_eq_c1SupportedIn D E hm hn (hcomp Q hQ)
    have hvan : ∀ Q ∈ supportStock D E, ∀ f ∈ c1VanishingOutside D E Q, ∀ y, y ∉ Q →
        gradVec D E f y = 0 := by
      intro Q hQ f hf y hy
      rw [heq Q hQ] at hf
      exact (hcs f hf.1 hf.2.1).2.1 y fun h => hy (hf.2.2 h)
    refine ⟨⟨supportStock_countable D E, hcomp⟩, fun Q hQ => ?_,
      exists_mem_supportStock_between D E hsurj hq hm, fun F hF => ⟨tupleFamily_countable D E hF, ?_⟩⟩
    · have hV := heq Q hQ
      refine ⟨hV, hvan Q hQ, ⟨?_, isCompleteWrt_euclidC1Norm D E h10 hsurj,
        exists_countable_dense_euclidC1Norm D E hQ h10 (hvan Q hQ)⟩, ?_⟩
      · refine isFunctionSpaceNorm_euclidC1Norm D E ((hlin D E).1 Q) (hcmp D E).2 (fun u hu => ?_) hV
        exact (hcs u hu.1 hu.2.1).2.2.1
      · intro A hA hd
        refine isDenseWrt_sharpNormQ_of_euclidC1Norm D E (fun g hg => ?_) (fun f hf g hg => ?_) hA hd
        · rw [hV] at hg
          exact (hcs g hg.1 hg.2.1).2.2.2.2.2.2.2
        · exact ⟨isC1Fn_sub D E hf.1 hg.1, fun y hy => by simp [hf.2 y hy, hg.2 y hy]⟩
    · intro n φ Q hmem hform
      have hcls : ∀ i, φ i ∈ c1SupportedIn D E (Q i : Set (E.Pt D)) := fun i => by
        rw [← heq _ (Q i).2]
        exact (hF (Q i)).2.1 (hform.2 i)
      refine ⟨⟨fun i => (hcls i).1, fun i => (hcls i).2.1, fun i k hik =>
        (hform.1 hik).mono (hcls i).2.2 (hcls k).2.2⟩, fun i => (hcls i).2.2, fun _ => ⟨?_, ?_⟩⟩
      · exact iInf_mono fun i => iInf_mono fun k => iInf_mono fun _ =>
          setInfDist_anti D E (hcls i).2.2 (hcls k).2.2
      · exact minPairwiseDist_pos D E _ fun i k hik =>
          hn.1 _ _ (hcomp _ (Q i).2) (hcomp _ (Q k).2) (hform.1 hik)
end YangMills.Construction.PeriodicSpace.SupportStockProof
