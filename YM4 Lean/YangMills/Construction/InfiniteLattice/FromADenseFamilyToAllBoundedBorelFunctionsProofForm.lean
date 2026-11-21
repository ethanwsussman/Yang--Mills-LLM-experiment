import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalMeasureIsAPeriodicGibbsStateProof
import YangMills.Construction.InfiniteLattice.FromADenseFamilyToAllBoundedBorelFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Filter Set
open InfiniteLattice GibbsAtFixedSpacing PeriodicGibbsStateSpace.DenseLocalFamily
open scoped Topology
namespace PeriodicGibbsStateSpace.DenseToBorel
section MonotoneClass
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X]
def unitIndicator (E : Set X) : X → ℝ := E.indicator fun _ => 1
omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
theorem abs_unitIndicator_le (E : Set X) (x : X) : |unitIndicator E x| ≤ 1 := by
  by_cases hx : x ∈ E <;> simp [unitIndicator, hx]
variable (N : Submodule ℝ (X → ℝ))
  (hcont : ∀ f : X → ℝ, Continuous f → (∃ c : ℝ, ∀ x, |f x| ≤ c) → f ∈ N)
  (hlim : ∀ (f : ℕ → X → ℝ) (g : X → ℝ), (∀ k, f k ∈ N) → (∃ c : ℝ, ∀ k x, |f k x| ≤ c) →
    (∀ x, Tendsto (fun k => f k x) atTop (𝓝 (g x))) → g ∈ N)
include hcont hlim in
theorem unitIndicator_mem_of_isClosed {E : Set X} (hE : IsClosed E) : unitIndicator E ∈ N := by
  refine hlim (fun k x => ((hE.apprSeq k x : NNReal) : ℝ)) _ (fun k => ?_) ⟨1, fun k x => ?_⟩
    (fun x => ?_)
  · refine hcont _ (NNReal.continuous_coe.comp (hE.apprSeq k).continuous) ⟨1, fun x => ?_⟩
    have hle := HasOuterApproxClosed.apprSeq_apply_le_one hE k x
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast hle
  · have hle := HasOuterApproxClosed.apprSeq_apply_le_one hE k x
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast hle
  · have h := tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hE) x
    have h2 := (NNReal.continuous_coe.tendsto _).comp h
    have h3 : unitIndicator E x = ((E.indicator (fun _ => (1 : NNReal)) x : NNReal) : ℝ) := by
      by_cases hx : x ∈ E <;> simp [unitIndicator, hx]
    rw [h3]
    exact h2
include hcont hlim in
theorem unitIndicator_mem_of_measurableSet {E : Set X} (hE : MeasurableSet E) :
    unitIndicator E ∈ N := by
  have hconst : (fun _ : X => (1 : ℝ)) ∈ N := hcont _ continuous_const ⟨1, fun x => by simp⟩
  refine MeasurableSpace.induction_on_inter (C := fun E _ => unitIndicator E ∈ N)
    (s := {s | IsClosed s}) (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed)
    isPiSystem_isClosed (unitIndicator_mem_of_isClosed N hcont hlim isClosed_empty)
    (fun t ht => unitIndicator_mem_of_isClosed N hcont hlim ht) ?_ ?_ E hE
  · intro t _ ih
    have h : unitIndicator tᶜ = (fun _ : X => (1 : ℝ)) - unitIndicator t := by
      funext x
      by_cases hx : x ∈ t <;> simp [unitIndicator, hx]
    rw [h]
    exact N.sub_mem hconst ih
  · intro f hd _ ih
    have hsum : ∀ x, HasSum (fun i => unitIndicator (f i) x) (unitIndicator (⋃ i, f i) x) := by
      intro x
      by_cases hx : ∃ i, x ∈ f i
      · obtain ⟨i, hi⟩ := hx
        have h1 : unitIndicator (⋃ i, f i) x = unitIndicator (f i) x := by
          simp [unitIndicator, hi, mem_iUnion.mpr ⟨i, hi⟩]
        rw [h1]
        refine hasSum_single i fun j hj => ?_
        have hxj' : x ∉ f j := fun hxj => (hd hj).le_bot ⟨hxj, hi⟩
        simp [unitIndicator, hxj']
      · have h1 : ∀ i, x ∉ f i := fun i hi => hx ⟨i, hi⟩
        have h2 : x ∉ ⋃ i, f i := by simpa using h1
        simp only [unitIndicator, h1, h2, not_false_eq_true, indicator_of_notMem]
        exact hasSum_zero
    refine hlim (fun n => ∑ i ∈ Finset.range n, unitIndicator (f i)) _
      (fun n => N.sum_mem fun i _ => ih i) ⟨1, fun n x => ?_⟩ (fun x => ?_)
    · rw [Finset.sum_apply, abs_of_nonneg
        (Finset.sum_nonneg fun i _ => by unfold unitIndicator; exact indicator_nonneg (by simp) x)]
      refine (sum_le_hasSum _ (fun i _ => ?_) (hsum x)).trans ?_
      · unfold unitIndicator; exact indicator_nonneg (by simp) x
      · exact (le_abs_self _).trans (abs_unitIndicator_le _ x)
    · simpa only [Finset.sum_apply] using (hsum x).tendsto_sum_nat
include hcont hlim in
theorem simpleFunc_mem_of_closure (s : SimpleFunc X ℝ) : (s : X → ℝ) ∈ N := by
  induction s using SimpleFunc.induction with
  | const c hs =>
    rename_i E
    have h : ((SimpleFunc.piecewise E hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0) :
        SimpleFunc X ℝ) : X → ℝ) = c • unitIndicator E := by
      funext x
      by_cases hx : x ∈ E <;> simp [unitIndicator, hx]
    rw [h]
    exact N.smul_mem c (unitIndicator_mem_of_measurableSet N hcont hlim hs)
  | add _ hf hg =>
    rw [SimpleFunc.coe_add]
    exact N.add_mem hf hg
include hcont hlim in
theorem mem_of_measurable_of_bounded {g : X → ℝ} (hg : Measurable g)
    (hb : ∃ c : ℝ, ∀ x, |g x| ≤ c) : g ∈ N := by
  obtain ⟨c, hc⟩ := hb
  have hc0 : ∀ x : X, 0 ≤ c := fun x => (abs_nonneg _).trans (hc x)
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    have hs : StronglyMeasurable g := hg.stronglyMeasurable
    refine hlim (fun n => hs.approxBounded c n) g
      (fun n => simpleFunc_mem_of_closure N hcont hlim _) ⟨c, fun n x => ?_⟩ (fun x => ?_)
    · simpa using hs.norm_approxBounded_le (hc0 x₀) n x
    · exact hs.tendsto_approxBounded_of_norm_le (by simpa using hc x)
  · have hz : g = 0 := by
      funext x
      exact (hX ⟨x⟩).elim
    rw [hz]
    exact N.zero_mem
end MonotoneClass
section OnTheFields
variable {a : ℝ}
def realRestriction (W : Submodule ℝ (GaugeField a → ℂ)) : Submodule ℝ (GaugeField a → ℝ) where
  carrier := {f | (fun U => (f U : ℂ)) ∈ W}
  add_mem' := by
    intro f g hf hg
    have h := W.add_mem hf hg
    change (fun U => (((f + g) U : ℝ) : ℂ)) ∈ W
    convert h using 1
    funext U
    simp
  zero_mem' := by
    change (fun U => (((0 : GaugeField a → ℝ) U : ℝ) : ℂ)) ∈ W
    convert W.zero_mem using 1
    funext U
    simp
  smul_mem' := by
    intro c f hf
    have h := W.smul_mem c hf
    change (fun U => (((c • f) U : ℝ) : ℂ)) ∈ W
    convert h using 1
    funext U
    simp
theorem ofReal_re_of_isRealValued {F : GaugeField a → ℂ} (hF : IsRealValued F) :
    (fun U => (((F U).re : ℝ) : ℂ)) = F := by
  funext U
  apply Complex.ext <;> simp [hF U]
theorem eq_boundedRealBorel [TopologicalSpace.PseudoMetrizableSpace (GaugeField a)]
    {𝒟 ℳ : Set (GaugeField a → ℂ)} (h𝒟 : IsCountableRealDense 𝒟)
    (hsub : ℳ ⊆ boundedRealBorel a) (hD : 𝒟 ⊆ ℳ) (hV : IsRealSubspace ℳ)
    (hL : IsClosedUnderBoundedPointwiseLimits ℳ) : ℳ = boundedRealBorel a := by
  obtain ⟨W, rfl⟩ := hV
  refine Subset.antisymm hsub fun F hF => ?_
  obtain ⟨⟨hFm, C, hC⟩, hFr⟩ := hF
  have hmem : (fun U => (F U).re) ∈ realRestriction W := by
    refine mem_of_measurable_of_bounded (realRestriction W) ?_ ?_ (Complex.measurable_re.comp hFm)
      ⟨C, fun U => (Complex.abs_re_le_norm _).trans (hC U)⟩
    · rintro f hf ⟨c, hc⟩
      have hfc : (fun U => (f U : ℂ)) ∈ continuousFns a :=
        Complex.continuous_ofReal.comp hf
      obtain ⟨H, hH, hu⟩ := h𝒟.2.2.2.2.2 _ hfc (fun U => by simp)
      obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hu 1 one_pos)
      refine hL (fun k => H (k + n₀)) _ (fun k => hD (hH _)) ⟨c + 1, fun k U => ?_⟩ (fun U => ?_)
      · have h1 := hn₀ (k + n₀) (by omega) U
        rw [dist_comm, dist_eq_norm] at h1
        have h2 : ‖(f U : ℂ)‖ ≤ c := by simpa using hc U
        have h3 := norm_sub_norm_le (H (k + n₀) U) (f U : ℂ)
        linarith
      · exact (tendsto_add_atTop_iff_nat n₀).2 (hu.tendsto_at U)
    · rintro f g hf ⟨c, hc⟩ hfg
      refine hL (fun k U => (f k U : ℂ)) (fun U => (g U : ℂ)) hf ⟨c, fun k U => ?_⟩ fun U => ?_
      · simpa using hc k U
      · exact (Complex.continuous_ofReal.tendsto _).comp (hfg U)
  have h2 : (fun U => (((F U).re : ℝ) : ℂ)) ∈ W := hmem
  rw [ofReal_re_of_isRealValued hFr] at h2
  exact h2
theorem meanAbs_eq_integral_norm (ν : BorelProb a) (A : GaugeField a → ℂ) :
    meanAbs ν A = ∫ U, ‖A U‖ ∂ν.1 := by
  unfold meanAbs BorelProb.integral GaugeFieldProbability.expect
  rw [integral_complex_ofReal]
  simp
theorem integrable_norm_of_isBoundedObservable (ν : BorelProb a) {A : GaugeField a → ℂ}
    (hA : IsBoundedObservable A) : Integrable (fun U => ‖A U‖) ν.1 := by
  obtain ⟨hm, C, hC⟩ := hA
  have : IsProbabilityMeasure ν.1 := ν.2
  exact Integrable.of_bound hm.norm.aestronglyMeasurable C
    (ae_of_all _ fun U => by simpa using hC U)
theorem isBoundedObservable_sub {A B : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable fun U => A U - B U := by apply _root_.YangMills.Construction.LatticePhases.ConditionalGibbsProof.isBoundedObservable_sub <;> assumption
def meanApproximable (𝒟 : Set (GaugeField a → ℂ)) (ν : BorelProb a) :
    Set (GaugeField a → ℂ) :=
  {F | F ∈ boundedRealBorel a ∧
    ∀ ε : ℝ, 0 < ε → ∃ H ∈ 𝒟, meanAbs ν (fun U => F U - H U) ≤ ε}
theorem mem_boundedRealBorel_of_mem {𝒟 : Set (GaugeField a → ℂ)}
    (h𝒟 : IsCountableRealDense 𝒟) {H : GaugeField a → ℂ} (hH : H ∈ 𝒟) :
    H ∈ boundedRealBorel a :=
  ⟨(h𝒟.2.1 hH).2.1, h𝒟.2.2.1 H hH⟩
theorem subset_meanApproximable {𝒟 : Set (GaugeField a → ℂ)}
    (h𝒟 : IsCountableRealDense 𝒟) (ν : BorelProb a) : 𝒟 ⊆ meanApproximable 𝒟 ν := by
  intro H hH
  refine ⟨mem_boundedRealBorel_of_mem h𝒟 hH, fun ε hε => ⟨H, hH, ?_⟩⟩
  rw [meanAbs_eq_integral_norm]
  simpa using hε.le
theorem add_real_smul_mem_meanApproximable {𝒟 : Set (GaugeField a → ℂ)}
    (h𝒟 : IsCountableRealDense 𝒟) (ν : BorelProb a) {F F' : GaugeField a → ℂ}
    (hF : F ∈ meanApproximable 𝒟 ν) (hF' : F' ∈ meanApproximable 𝒟 ν) (c : ℝ) :
    (fun U => F U + (c : ℂ) * F' U) ∈ meanApproximable 𝒟 ν := by
  have : IsProbabilityMeasure ν.1 := ν.2
  obtain ⟨⟨hFo, hFr⟩, hFa⟩ := hF
  obtain ⟨⟨hFo', hFr'⟩, hFa'⟩ := hF'
  obtain ⟨hFm, C, hC⟩ := id hFo
  obtain ⟨hFm', C', hC'⟩ := id hFo'
  refine ⟨⟨⟨hFm.add (measurable_const.mul hFm'), C + |c| * C', fun U => ?_⟩, fun U => ?_⟩,
    fun ε hε => ?_⟩
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact add_le_add (hC U) (mul_le_mul_of_nonneg_left (hC' U) (abs_nonneg c))
  · have h1 := hFr U
    have h2 := hFr' U
    simp [h1, h2]
  · have h2c : 0 < 2 + |c| := by positivity
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (2 + |c|) := ⟨_, rfl⟩
    have hδ : 0 < δ := by rw [hδdef]; positivity
    obtain ⟨H, hH, hHa⟩ := hFa δ hδ
    obtain ⟨H', hH', hHa'⟩ := hFa' δ hδ
    have hHo := (mem_boundedRealBorel_of_mem h𝒟 hH).1
    have hHo' := (mem_boundedRealBorel_of_mem h𝒟 hH').1
    obtain ⟨-, B', hB'⟩ := id hHo'
    have hB0 : 0 < |B'| + 1 := by positivity
    obtain ⟨q, hq⟩ := exists_rat_near c (div_pos hδ hB0)
    refine ⟨fun U => H U + (q : ℂ) * H' U, h𝒟.2.2.2.2.1 H hH H' hH' q, ?_⟩
    rw [meanAbs_eq_integral_norm] at hHa hHa' ⊢
    have hpt : ∀ U, ‖F U + (c : ℂ) * F' U - (H U + (q : ℂ) * H' U)‖ ≤
        ‖F U - H U‖ + |c| * ‖F' U - H' U‖ + δ := by
      intro U
      have hid : F U + (c : ℂ) * F' U - (H U + (q : ℂ) * H' U) =
          (F U - H U) + (c : ℂ) * (F' U - H' U) + ((c - q : ℝ) : ℂ) * H' U := by
        push_cast
        ring
      rw [hid]
      refine (norm_add₃_le).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have h3 : |c - (q : ℝ)| * ‖H' U‖ ≤ δ := by
        have h4 : ‖H' U‖ ≤ |B'| + 1 := by
          have hb1 := hB' U
          have hb2 := le_abs_self B'
          linarith
        calc |c - (q : ℝ)| * ‖H' U‖ ≤ (δ / (|B'| + 1)) * (|B'| + 1) :=
              mul_le_mul hq.le h4 (norm_nonneg _) (by positivity)
          _ = δ := by field_simp
      linarith
    have i1 := integrable_norm_of_isBoundedObservable ν (isBoundedObservable_sub hFo hHo)
    have i2 := integrable_norm_of_isBoundedObservable ν (isBoundedObservable_sub hFo' hHo')
    have i12 : Integrable (fun U => ‖F U - H U‖ + |c| * ‖F' U - H' U‖) ν.1 :=
      i1.add (i2.const_mul _)
    have i3 : Integrable (fun U => ‖F U - H U‖ + |c| * ‖F' U - H' U‖ + δ) ν.1 :=
      i12.add (integrable_const _)
    have hle : ∫ U, ‖F U + (c : ℂ) * F' U - (H U + (q : ℂ) * H' U)‖ ∂ν.1 ≤
        ∫ U, (‖F U - H U‖ + |c| * ‖F' U - H' U‖ + δ) ∂ν.1 :=
      integral_mono_of_nonneg (ae_of_all _ fun U => norm_nonneg _) i3 (ae_of_all _ hpt)
    have e1 : ∫ U, (‖F U - H U‖ + |c| * ‖F' U - H' U‖ + δ) ∂ν.1 =
        ∫ U, (‖F U - H U‖ + |c| * ‖F' U - H' U‖) ∂ν.1 + ∫ _, δ ∂ν.1 :=
      integral_add i12 (integrable_const _)
    have e2 : ∫ U, (‖F U - H U‖ + |c| * ‖F' U - H' U‖) ∂ν.1 =
        ∫ U, ‖F U - H U‖ ∂ν.1 + ∫ U, |c| * ‖F' U - H' U‖ ∂ν.1 :=
      integral_add i1 (i2.const_mul _)
    have e3 : ∫ U, |c| * ‖F' U - H' U‖ ∂ν.1 = |c| * ∫ U, ‖F' U - H' U‖ ∂ν.1 :=
      integral_const_mul _ _
    have e4 : ∫ _, δ ∂ν.1 = δ := by simp
    have h5 : |c| * ∫ U, ‖F' U - H' U‖ ∂ν.1 ≤ |c| * δ :=
      mul_le_mul_of_nonneg_left hHa' (abs_nonneg c)
    have h6 : δ + |c| * δ + δ = ε := by
      rw [hδdef]
      field_simp
      ring
    linarith
theorem meanApproximable_closed_under_limits {𝒟 : Set (GaugeField a → ℂ)}
    (h𝒟 : IsCountableRealDense 𝒟) (ν : BorelProb a) :
    IsClosedUnderBoundedPointwiseLimits (meanApproximable 𝒟 ν) := by
  rintro F G hF ⟨c, hc⟩ hlim
  have : IsProbabilityMeasure ν.1 := ν.2
  have hGm : Measurable G :=
    measurable_of_tendsto_metrizable (f := F) (fun k => (hF k).1.1.1) (tendsto_pi_nhds.mpr hlim)
  have hGb : ∀ U, ‖G U‖ ≤ c := fun U =>
    le_of_tendsto ((continuous_norm.tendsto _).comp (hlim U))
      (Eventually.of_forall fun k => hc k U)
  have hGr : IsRealValued G := fun U => by
    have h1 := (Complex.continuous_im.tendsto _).comp (hlim U)
    have h0 : (Complex.im ∘ fun k => F k U) = fun _ => 0 := funext fun k => (hF k).1.2 U
    rw [h0] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hGo : IsBoundedObservable G := ⟨hGm, c, hGb⟩
  refine ⟨⟨hGo, hGr⟩, fun ε hε => ?_⟩
  have hconv : Tendsto (fun k => ∫ U, ‖G U - F k U‖ ∂ν.1) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := ν.1)
      (F := fun k U => ‖G U - F k U‖) (f := fun _ => (0 : ℝ)) (fun _ => c + c)
      (fun k => (integrable_norm_of_isBoundedObservable ν
        (isBoundedObservable_sub hGo (hF k).1.1)).aestronglyMeasurable)
      (integrable_const _)
      (fun k => ae_of_all _ fun U => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hGb U) (hc k U)))
      (ae_of_all _ fun U => by
        have h1 : Tendsto (fun k => G U - F k U) atTop (𝓝 (G U - G U)) :=
          tendsto_const_nhds.sub (hlim U)
        have h2 := (continuous_norm.tendsto _).comp h1
        simpa [Function.comp_def] using h2)
    simpa using h
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hconv).2 (ε / 2) (half_pos hε)).exists
  obtain ⟨H, hH, hHa⟩ := (hF k).2 (ε / 2) (half_pos hε)
  refine ⟨H, hH, ?_⟩
  rw [meanAbs_eq_integral_norm] at hHa ⊢
  have hHo := (mem_boundedRealBorel_of_mem h𝒟 hH).1
  have i1 := integrable_norm_of_isBoundedObservable ν (isBoundedObservable_sub hGo (hF k).1.1)
  have i2 := integrable_norm_of_isBoundedObservable ν (isBoundedObservable_sub (hF k).1.1 hHo)
  have i3 : Integrable (fun U => ‖G U - F k U‖ + ‖F k U - H U‖) ν.1 := i1.add i2
  have hle : ∫ U, ‖G U - H U‖ ∂ν.1 ≤ ∫ U, (‖G U - F k U‖ + ‖F k U - H U‖) ∂ν.1 :=
    integral_mono_of_nonneg (ae_of_all _ fun U => norm_nonneg _) i3 (ae_of_all _ fun U => by
      have h1 := norm_add_le (G U - F k U) (F k U - H U)
      simpa using h1)
  have e : ∫ U, (‖G U - F k U‖ + ‖F k U - H U‖) ∂ν.1 =
      ∫ U, ‖G U - F k U‖ ∂ν.1 + ∫ U, ‖F k U - H U‖ ∂ν.1 := integral_add i1 i2
  linarith
theorem exists_complexSpan_meanAbs_le [TopologicalSpace.PseudoMetrizableSpace (GaugeField a)]
    {𝒟 : Set (GaugeField a → ℂ)} (h𝒟 : IsCountableRealDense 𝒟) (ν : BorelProb a)
    {h : GaugeField a → ℂ} (hh : IsBoundedObservable h) {ε : ℝ} (hε : 0 < ε) :
    ∃ H ∈ complexSpan 𝒟, meanAbs ν (fun U => h U - H U) ≤ ε := by
  have : IsProbabilityMeasure ν.1 := ν.2
  have hone : (fun _ => (1 : ℂ)) ∈ meanApproximable 𝒟 ν :=
    subset_meanApproximable h𝒟 ν h𝒟.2.2.2.1
  have hzero : (0 : GaugeField a → ℂ) ∈ meanApproximable 𝒟 ν := by
    have h0 := add_real_smul_mem_meanApproximable h𝒟 ν hone hone (-1)
    convert h0 using 1
    funext U
    simp
  have hV : IsRealSubspace (meanApproximable 𝒟 ν) := by
    refine ⟨{
      carrier := meanApproximable 𝒟 ν
      add_mem' := ?_
      zero_mem' := hzero
      smul_mem' := ?_ }, rfl⟩
    · intro f g hf hg
      have h0 := add_real_smul_mem_meanApproximable h𝒟 ν hf hg 1
      convert h0 using 1
      funext U
      simp
    · intro c f hf
      have h0 := add_real_smul_mem_meanApproximable h𝒟 ν hzero hf c
      convert h0 using 1
      funext U
      simp
  have heq := eq_boundedRealBorel h𝒟 (fun F hF => hF.1)
    (subset_meanApproximable h𝒟 ν) hV (meanApproximable_closed_under_limits h𝒟 ν)
  obtain ⟨hm, C, hC⟩ := id hh
  have hre : (fun U => (((h U).re : ℝ) : ℂ)) ∈ meanApproximable 𝒟 ν := by
    rw [heq]
    refine ⟨⟨Complex.measurable_ofReal.comp (Complex.measurable_re.comp hm), C, fun U => ?_⟩,
      fun U => by simp⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hC U)
  have him : (fun U => (((h U).im : ℝ) : ℂ)) ∈ meanApproximable 𝒟 ν := by
    rw [heq]
    refine ⟨⟨Complex.measurable_ofReal.comp (Complex.measurable_im.comp hm), C, fun U => ?_⟩,
      fun U => by simp⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hC U)
  obtain ⟨H₁, h₁, a₁⟩ := hre.2 (ε / 2) (half_pos hε)
  obtain ⟨H₂, h₂, a₂⟩ := him.2 (ε / 2) (half_pos hε)
  refine ⟨fun U => H₁ U + Complex.I * H₂ U, ⟨H₁, h₁, H₂, h₂, rfl⟩, ?_⟩
  rw [meanAbs_eq_integral_norm] at a₁ a₂ ⊢
  have i1 := integrable_norm_of_isBoundedObservable ν
    (isBoundedObservable_sub hre.1.1 (mem_boundedRealBorel_of_mem h𝒟 h₁).1)
  have i2 := integrable_norm_of_isBoundedObservable ν
    (isBoundedObservable_sub him.1.1 (mem_boundedRealBorel_of_mem h𝒟 h₂).1)
  have i3 : Integrable (fun U => ‖(((h U).re : ℝ) : ℂ) - H₁ U‖ +
      ‖(((h U).im : ℝ) : ℂ) - H₂ U‖) ν.1 := i1.add i2
  have hpt : ∀ U, ‖h U - (H₁ U + Complex.I * H₂ U)‖ ≤
      ‖(((h U).re : ℝ) : ℂ) - H₁ U‖ + ‖(((h U).im : ℝ) : ℂ) - H₂ U‖ := by
    intro U
    have hid : h U - (H₁ U + Complex.I * H₂ U) =
        ((((h U).re : ℝ) : ℂ) - H₁ U) + Complex.I * ((((h U).im : ℝ) : ℂ) - H₂ U) := by
      have h3 := Complex.re_add_im (h U)
      linear_combination -h3
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
  have hle : ∫ U, ‖h U - (H₁ U + Complex.I * H₂ U)‖ ∂ν.1 ≤
      ∫ U, (‖(((h U).re : ℝ) : ℂ) - H₁ U‖ + ‖(((h U).im : ℝ) : ℂ) - H₂ U‖) ∂ν.1 :=
    integral_mono_of_nonneg (ae_of_all _ fun U => norm_nonneg _) i3 (ae_of_all _ hpt)
  have e : ∫ U, (‖(((h U).re : ℝ) : ℂ) - H₁ U‖ + ‖(((h U).im : ℝ) : ℂ) - H₂ U‖) ∂ν.1 =
      ∫ U, ‖(((h U).re : ℝ) : ℂ) - H₁ U‖ ∂ν.1 + ∫ U, ‖(((h U).im : ℝ) : ℂ) - H₂ U‖ ∂ν.1 :=
    integral_add i1 i2
  linarith
end OnTheFields
theorem denseFamilyDeterminesBorel_holds
    (hS : GibbsAtFixedSpacing.SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties) :
    DenseFamilyDeterminesBorel := by
  intro D 𝒟 h𝒟
  have : TopologicalSpace.MetrizableSpace (GaugeField D.mesh) := (hS D.mesh D.mesh_pos).1.2.2
  exact ⟨fun ℳ h1 h2 h3 h4 => eq_boundedRealBorel h𝒟 h1 h2 h3 h4,
    fun ν h hh ε hε => exists_complexSpan_meanAbs_le h𝒟 ν hh hε⟩
end PeriodicGibbsStateSpace.DenseToBorel
end YangMills.Construction
