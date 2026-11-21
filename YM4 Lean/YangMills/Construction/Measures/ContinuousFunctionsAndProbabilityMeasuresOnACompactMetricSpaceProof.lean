import YangMills.Construction.Measures.ContinuousFunctionsAndProbabilityMeasuresOnACompactMetricSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.LatticePhases
open scoped Topology NNReal
noncomputable section
namespace YangMills.Construction.Measures.CompactMetricProbability
theorem exists_countable_dense_ball_basis_and_separable (X : Type) [MetricSpace X] [CompactSpace X] :
    (∃ D : Set X, D.Countable ∧ Dense D) ∧
      (∃ B : Set (Set X), B.Countable ∧
        (∀ b ∈ B, ∃ (x : X) (r : ℝ), 0 < r ∧ b = Metric.ball x r) ∧
        ∀ O : Set X, IsOpen O → O = ⋃₀ {b ∈ B | b ⊆ O}) ∧
      TopologicalSpace.SeparableSpace C(X, ℂ) := by
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense X
  refine ⟨⟨D, hDcount, hDdense⟩,
    ⟨(fun p : X × ℕ => Metric.ball p.1 (1 / ((p.2 : ℝ) + 1))) '' (D ×ˢ Set.univ), ?_, ?_, ?_⟩,
    inferInstance⟩
  · exact (hDcount.prod Set.countable_univ).image _
  · rintro _ ⟨⟨c, n⟩, -, rfl⟩
    exact ⟨c, _, by positivity, rfl⟩
  · intro O hO
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO x hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
      have hrad : 0 < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨c, hcD, hc⟩ := hDdense.exists_dist_lt x hrad
      refine ⟨Metric.ball c (1 / ((n : ℝ) + 1)), ⟨⟨(c, n), ⟨hcD, trivial⟩, rfl⟩, ?_⟩, ?_⟩
      · intro y hy
        apply hball
        rw [Metric.mem_ball] at hy ⊢
        have htri := dist_triangle y c x
        rw [dist_comm c x] at htri
        linarith
      · rw [Metric.mem_ball]
        exact hc
    · exact Set.sUnion_subset fun b hb => hb.2
theorem submodule_eq_bounded_measurable (X : Type) [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (H : Submodule ℂ (X → ℂ))
    (hH : ∀ f ∈ H, Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hcont : ∀ F : C(X, ℂ), (F : X → ℂ) ∈ H)
    (hlim : ∀ (u : ℕ → X → ℂ) (g : X → ℂ), (∀ n, u n ∈ H) → (∃ C : ℝ, ∀ n x, ‖u n x‖ ≤ C) →
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (g x))) → g ∈ H) :
    (H : Set (X → ℂ)) = {f | Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C} := by
  have hone : (fun _ : X => (1 : ℂ)) ∈ H := hcont (ContinuousMap.const X 1)
  have hindic : ∀ E : Set X, MeasurableSet E → E.indicator (fun _ => (1 : ℂ)) ∈ H := by
    intro E hE
    have hgen : (‹MeasurableSpace X›) = MeasurableSpace.generateFrom {s : Set X | IsClosed s} :=
      BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed
    have hpi : IsPiSystem {s : Set X | IsClosed s} := isPiSystem_isClosed
    induction E, hE using MeasurableSpace.induction_on_inter hgen hpi with
    | empty =>
      rw [Set.indicator_empty]
      exact H.zero_mem
    | basic t ht =>
      have hcl : IsClosed t := ht
      let u : ℕ → C(X, ℂ) := fun n => ⟨fun x => (((hcl.apprSeq n x : ℝ≥0) : ℝ) : ℂ),
        Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (hcl.apprSeq n).continuous)⟩
      refine hlim (fun n => u n) _ (fun n => hcont _) ⟨1, fun n x => ?_⟩ (fun x => ?_)
      · have hle : hcl.apprSeq n x ≤ 1 := HasOuterApproxClosed.apprSeq_apply_le_one hcl n x
        change ‖(((hcl.apprSeq n x : ℝ≥0) : ℝ) : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
        exact_mod_cast hle
      · have h1 := (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hcl)) x
        have h2 := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp h1
        have hval : (Complex.ofReal ∘ NNReal.toReal) (t.indicator (fun _ => (1 : ℝ≥0)) x) =
            t.indicator (fun _ => (1 : ℂ)) x := by
          by_cases hx : x ∈ t <;> simp [hx]
        rw [hval] at h2
        exact h2
    | compl t _ ih =>
      have heq : tᶜ.indicator (fun _ => (1 : ℂ)) =
          (fun _ => (1 : ℂ)) - t.indicator (fun _ => (1 : ℂ)) := by
        ext x
        by_cases hx : x ∈ t <;> simp [hx]
      rw [heq]
      exact H.sub_mem hone ih
    | iUnion f hdis _ ih =>
      let s : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, f i
      have hmono : Monotone s := fun a b hab =>
        Set.biUnion_subset_biUnion_left (fun i hi => by
          simp only [Finset.coe_range, Set.mem_Iio] at hi ⊢
          omega)
      have hU : ⋃ n, s n = ⋃ i, f i := by
        ext x
        simp only [s, Set.mem_iUnion, Finset.mem_range, exists_prop]
        constructor
        · rintro ⟨_, i, _, hi⟩
          exact ⟨i, hi⟩
        · rintro ⟨i, hi⟩
          exact ⟨i + 1, i, Nat.lt_succ_self i, hi⟩
      have hpartial : ∀ n, (s n).indicator (fun _ => (1 : ℂ)) ∈ H := by
        intro n
        have heq : (s n).indicator (fun _ => (1 : ℂ)) =
            ∑ i ∈ Finset.range n, (f i).indicator (fun _ => (1 : ℂ)) := by
          ext x
          rw [Finset.sum_apply]
          exact congrFun (Finset.indicator_biUnion (Finset.range n) f
            (fun i _ j _ hij => hdis hij)) x
        rw [heq]
        exact H.sum_mem fun i _ => ih i
      refine hlim (fun n => (s n).indicator (fun _ => (1 : ℂ))) _ hpartial ⟨1, fun n x => ?_⟩
        (fun x => ?_)
      · by_cases hx : x ∈ s n <;> simp [hx]
      · rw [← hU]
        exact (Monotone.tendsto_indicator s hmono _ x).mono_right (pure_le_nhds _)
  have hsimple : ∀ s : SimpleFunc X ℂ, (s : X → ℂ) ∈ H := by
    intro s
    induction s using SimpleFunc.induction with
    | const c hs =>
      rename_i E
      convert H.smul_mem c (hindic E hs) using 1
      ext x
      by_cases hx : x ∈ E <;> simp [hx]
    | add _ hf hg =>
      rw [SimpleFunc.coe_add]
      exact H.add_mem hf hg
  apply Set.Subset.antisymm
  · exact fun f hf => hH f hf
  · rintro f ⟨hm, C, hb⟩
    have hs : StronglyMeasurable f := hm.stronglyMeasurable
    have hb' : ∀ x, ‖f x‖ ≤ max C 0 := fun x => (hb x).trans (le_max_left _ _)
    exact hlim (fun n => hs.approxBounded (max C 0) n) f (fun n => hsimple _)
      ⟨max C 0, fun n x => hs.norm_approxBounded_le (le_max_right _ _) n x⟩
      (fun x => hs.tendsto_approxBounded_of_norm_le (hb' x))
section Integrals
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
theorem integrable_continuousMap (σ : ProbMeasure X) (F : C(X, ℂ)) :
    Integrable (F : X → ℂ) σ.toMeasure :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
theorem continuous_eval (σ : ProbMeasure X) : Continuous fun F : C(X, ℂ) => σ.eval F := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun F G => ?_).continuous
  have hsub : σ.eval F - σ.eval G = ∫ x, (F - G) x ∂σ.toMeasure :=
    (integral_sub (integrable_continuousMap σ F) (integrable_continuousMap σ G)).symm
  rw [dist_eq_norm, hsub, dist_eq_norm]
  have hbound := norm_integral_le_of_norm_le_const (μ := σ.toMeasure)
    (f := fun x => (F - G) x) (C := ‖F - G‖)
    (Eventually.of_forall fun x => (F - G).norm_coe_le_norm x)
  simpa using hbound
theorem ext_of_eval_eq_on_dense (S : Set C(X, ℂ)) (hS : Dense S) (ρ ρ' : ProbMeasure X)
    (h : ∀ F ∈ S, ρ.eval F = ρ'.eval F) : ρ = ρ' := by
  have hall : ∀ F : C(X, ℂ), ρ.eval F = ρ'.eval F := by
    intro F
    have hcl : IsClosed {F : C(X, ℂ) | ρ.eval F = ρ'.eval F} :=
      isClosed_eq (continuous_eval ρ) (continuous_eval ρ')
    exact closure_minimal (fun G hG => h G hG) hcl (hS F)
  have hmeas : ρ.toMeasure = ρ'.toMeasure := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    let G : C(X, ℂ) := ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    have hG := hall G
    have hval : ∀ σ : ProbMeasure X, σ.eval G = ((∫ x, f x ∂σ.toMeasure : ℝ) : ℂ) := fun σ =>
      integral_ofReal
    rw [hval, hval] at hG
    exact_mod_cast hG
  exact Subtype.ext hmeas
theorem compactSpace_probMeasure : CompactSpace (ProbMeasure X) := by
  let ι : ProbabilityMeasure X → ProbMeasure X := id
  have hcont : Continuous ι := by
    refine continuous_iInf_rng.2 fun F => continuous_induced_rng.2 ?_
    rw [continuous_iff_continuousAt]
    intro μ
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp tendsto_id
      (BoundedContinuousFunction.mkOfCompact F)
  exact Function.Surjective.compactSpace hcont Function.surjective_id
end Integrals
theorem topology_eq_of_compact_le_t2 {P : Type*} (t s : TopologicalSpace P) (hc : @CompactSpace P t)
    (h2 : @T2Space P s) (h : t ≤ s) : s = t := by
  have hcont : @Continuous P P t s id := (@continuous_id_iff_le P t s).mpr h
  obtain ⟨⟨⟨h3⟩, -⟩, -⟩ := @Continuous.isClosedEmbedding P P t s hc h2 id hcont
    Function.injective_id
  exact (h3.trans (@induced_id P s)).symm
theorem exists_metricSpace_of_separating {P : Type*} [t : TopologicalSpace P] [CompactSpace P]
    (e : ℕ+ → P → ℂ) (he : ∀ k, Continuous (e k))
    (hsep : ∀ p q, (∀ k, e k p = e k q) → p = q) :
    ∃ m : MetricSpace P,
      (∀ p q, @dist _ m.toDist p q = ∑' k : ℕ+, (2 : ℝ)⁻¹ ^ (k : ℕ) * min 1 ‖e k p - e k q‖) ∧
      m.toUniformSpace.toTopologicalSpace = t := by
  let w : ℕ+ → ℝ := fun k => (2 : ℝ)⁻¹ ^ (k : ℕ)
  have hw0 : ∀ k, 0 < w k := fun k => by positivity
  have hw : Summable w :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective PNat.coe_injective
  let term : P → P → ℕ+ → ℝ := fun p q k => w k * min 1 ‖e k p - e k q‖
  have hterm0 : ∀ p q k, 0 ≤ term p q k := fun p q k =>
    mul_nonneg (hw0 k).le (le_min zero_le_one (norm_nonneg _))
  have htermle : ∀ p q k, term p q k ≤ w k := fun p q k =>
    mul_le_of_le_one_right (hw0 k).le (min_le_left _ _)
  have hsum : ∀ p q, Summable (term p q) := fun p q =>
    Summable.of_nonneg_of_le (hterm0 p q) (htermle p q) hw
  let d : P → P → ℝ := fun p q => ∑' k, term p q k
  have hd_self : ∀ p, d p p = 0 := fun p => by simp [d, term]
  have hd_comm : ∀ p q, d p q = d q p := fun p q => by simp only [d, term, norm_sub_rev]
  have hd_tri : ∀ p q r, d p r ≤ d p q + d q r := by
    intro p q r
    simp only [d]
    rw [← (hsum p q).tsum_add (hsum q r)]
    refine (hsum p r).tsum_le_tsum (fun k => ?_) ((hsum p q).add (hsum q r))
    simp only [term]
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hw0 k).le
    have hn : ‖e k p - e k r‖ ≤ ‖e k p - e k q‖ + ‖e k q - e k r‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have ha := norm_nonneg (e k p - e k q)
    have hb := norm_nonneg (e k q - e k r)
    rcases le_total 1 ‖e k p - e k q‖ with h1 | h1 <;>
      rcases le_total 1 ‖e k q - e k r‖ with h2 | h2 <;>
      simp only [min_eq_left h1, min_eq_right h1, min_eq_left h2, min_eq_right h2] <;>
      first
        | linarith [min_le_left (1 : ℝ) ‖e k p - e k r‖]
        | linarith [min_le_right (1 : ℝ) ‖e k p - e k r‖]
  have hd_eq : ∀ p q, d p q = 0 → p = q := by
    intro p q h0
    refine hsep p q fun k => ?_
    have hs : HasSum (term p q) 0 := by
      have hs' := (hsum p q).hasSum
      rwa [show (∑' k, term p q k) = 0 from h0] at hs'
    have hk : term p q k = 0 := congrFun ((hasSum_zero_iff_of_nonneg (hterm0 p q)).mp hs) k
    have hmin : min 1 ‖e k p - e k q‖ = 0 := by
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd h (hw0 k).ne'
      · exact h
    have hnorm : ‖e k p - e k q‖ = 0 := by
      rcases min_choice (1 : ℝ) ‖e k p - e k q‖ with h | h
      · rw [h] at hmin
        exact absurd hmin one_ne_zero
      · rw [h] at hmin
        exact hmin
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  let m : MetricSpace P :=
    { dist := d
      dist_self := hd_self
      dist_comm := hd_comm
      dist_triangle := hd_tri
      eq_of_dist_eq_zero := fun {p q} => hd_eq p q }
  have hd_cont : ∀ q, Continuous fun p => d p q := by
    intro q
    refine continuous_tsum (fun k => ?_) hw (fun k p => ?_)
    · exact continuous_const.mul (continuous_const.min ((he k).sub continuous_const).norm)
    · rw [Real.norm_of_nonneg (hterm0 p q k)]
      exact htermle p q k
  have hle : t ≤ m.toUniformSpace.toTopologicalSpace := by
    rw [TopologicalSpace.le_def]
    intro U hU
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨ε, hε, hb⟩ := (@Metric.isOpen_iff P m.toPseudoMetricSpace U).mp hU x hx
    have hopen : IsOpen {y | d y x < ε} := isOpen_lt (hd_cont x) continuous_const
    have hmem : x ∈ {y | d y x < ε} := by
      change d x x < ε
      rw [hd_self]
      exact hε
    exact Filter.mem_of_superset (hopen.mem_nhds hmem) fun y hy => hb hy
  have h2 : @T2Space P m.toUniformSpace.toTopologicalSpace := by
    let _i := m
    infer_instance
  exact ⟨m, fun _ _ => rfl, topology_eq_of_compact_le_t2 _ _ inferInstance h2 hle⟩
theorem borel_eq_iSup_comap_of_separating {P : Type*} [t : TopologicalSpace P] [CompactSpace P]
    (e : ℕ+ → P → ℂ) (he : ∀ k, Continuous (e k))
    (hsep : ∀ p q, (∀ k, e k p = e k q) → p = q) :
    borel P = ⨆ k : ℕ+, MeasurableSpace.comap (e k) (borel ℂ) := by
  let Φ : P → (ℕ+ → ℂ) := fun p k => e k p
  have hΦ : Continuous Φ := continuous_pi he
  have hinj : Function.Injective Φ := fun p q h => hsep p q fun k => congrFun h k
  have hind : t = TopologicalSpace.induced Φ inferInstance :=
    (hΦ.isClosedEmbedding hinj).isEmbedding.eq_induced
  have hpi : borel (ℕ+ → ℂ) = MeasurableSpace.pi := (BorelSpace.measurable_eq).symm
  have hbor : (borel ℂ) = Complex.measurableSpace := (BorelSpace.measurable_eq).symm
  calc borel P = (borel (ℕ+ → ℂ)).comap Φ := by
        conv_lhs => rw [hind]
        exact borel_comap
    _ = ⨆ k : ℕ+, MeasurableSpace.comap (e k) (borel ℂ) := by
        rw [hpi, hbor, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
        refine iSup_congr fun k => ?_
        rw [MeasurableSpace.comap_comp]
        rfl
theorem compactMetricProbabilityFacts_holds : CompactMetricProbabilityFacts := by
  intro X _ _ _ _
  refine ⟨exists_countable_dense_ball_basis_and_separable X, fun ρ => ⟨?_, ?_⟩,
    submodule_eq_bounded_measurable X, ext_of_eval_eq_on_dense, fun F hF => ?_⟩
  · exact ContinuousMap.toLp_denseRange ℂ ρ.toMeasure ℂ ENNReal.one_ne_top
  · exact ContinuousMap.toLp_denseRange ℂ ρ.toMeasure ℂ ENNReal.ofNat_ne_top
  · let e : ℕ+ → ProbMeasure X → ℂ := fun k ρ => ρ.eval (F k)
    have hcomp : CompactSpace (ProbMeasure X) := compactSpace_probMeasure
    have he : ∀ k, Continuous (e k) := fun k =>
      continuous_iff_continuousAt.mpr fun ρ =>
        (ProbMeasure.tendsto_iff_eval (fun σ : ProbMeasure X => σ) ρ).mp tendsto_id (F k)
    have hsep : ∀ ρ ρ' : ProbMeasure X, (∀ k, e k ρ = e k ρ') → ρ = ρ' := by
      intro ρ ρ' h
      refine ext_of_eval_eq_on_dense (Set.range F) hF ρ ρ' ?_
      rintro _ ⟨k, rfl⟩
      exact h k
    obtain ⟨m, hm, hmt⟩ := exists_metricSpace_of_separating e he hsep
    exact ⟨⟨m, hm, hmt⟩, hcomp, borel_eq_iSup_comap_of_separating e he hsep⟩
end YangMills.Construction.Measures.CompactMetricProbability
