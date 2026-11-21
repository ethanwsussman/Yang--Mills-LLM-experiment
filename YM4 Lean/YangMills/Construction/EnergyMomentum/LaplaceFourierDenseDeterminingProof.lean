import YangMills.Construction.EnergyMomentum.LaplaceFourierDenseDetermining
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.EnergyMomentum.DenseDetermining
theorem laplaceFourierExp_mul (t t' : ℝ≥0) (y y' : Momentum3) (p : EnergyMomentumSpace) :
    laplaceFourierExp t y p * laplaceFourierExp t' y' p =
      laplaceFourierExp (t + t') (y + y') p := by
  simp only [laplaceFourierExp, spatialDot, ← Complex.exp_add]
  congr 1
  simp only [PiLp.add_apply, add_mul, Finset.sum_add_distrib, NNReal.coe_add]
  push_cast
  ring
theorem conj_laplaceFourierExp (t : ℝ≥0) (y : Momentum3) (p : EnergyMomentumSpace) :
    conj (laplaceFourierExp t y p) = laplaceFourierExp t (-y) p := by
  simp only [laplaceFourierExp, spatialDot, ← Complex.exp_conj]
  congr 1
  simp only [PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  push_cast
  ring
theorem laplaceFourierExp_zero (p : EnergyMomentumSpace) : laplaceFourierExp 0 0 p = 1 := by
  simp [laplaceFourierExp, spatialDot]
def bcfExp (s : ℝ≥0 × Momentum3) : BoundedContinuousFunction EnergyMomentumSpace ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (laplaceFourierExp s.1 s.2)
    (continuous_laplaceFourierExp s.1 s.2) 1 (norm_laplaceFourierExp_le_one s.1 s.2)
theorem bcfExp_apply (s : ℝ≥0 × Momentum3) (p : EnergyMomentumSpace) :
    bcfExp s p = laplaceFourierExp s.1 s.2 p := rfl
def bcfExpSpan : Submodule ℂ (BoundedContinuousFunction EnergyMomentumSpace ℂ) :=
  Submodule.span ℂ (range bcfExp)
theorem bcfExp_mem_span (s : ℝ≥0 × Momentum3) : bcfExp s ∈ bcfExpSpan :=
  Submodule.subset_span ⟨s, rfl⟩
theorem one_mem_bcfExpSpan : (1 : BoundedContinuousFunction EnergyMomentumSpace ℂ) ∈ bcfExpSpan := by
  have h : bcfExp (0, 0) = 1 := by
    ext p
    simpa [bcfExp_apply] using laplaceFourierExp_zero p
  exact h ▸ bcfExp_mem_span _
theorem mul_mem_bcfExpSpan (f g : BoundedContinuousFunction EnergyMomentumSpace ℂ)
    (hf : f ∈ bcfExpSpan) (hg : g ∈ bcfExpSpan) : f * g ∈ bcfExpSpan := by
  refine Submodule.span_induction (p := fun f _ => f * g ∈ bcfExpSpan) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨s, rfl⟩
    refine Submodule.span_induction (p := fun g _ => bcfExp s * g ∈ bcfExpSpan)
      ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨s', rfl⟩
      have h : bcfExp s * bcfExp s' = bcfExp (s.1 + s'.1, s.2 + s'.2) := by
        ext p
        exact laplaceFourierExp_mul _ _ _ _ p
      rw [h]
      exact bcfExp_mem_span _
    · simp
    · intro a b _ _ ha hb
      rw [mul_add]
      exact add_mem ha hb
    · intro c a _ ha
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ ha
  · simp
  · intro a b _ _ ha hb
    rw [add_mul]
    exact add_mem ha hb
  · intro c a _ ha
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ ha
theorem star_mem_bcfExpSpan (f : BoundedContinuousFunction EnergyMomentumSpace ℂ)
    (hf : f ∈ bcfExpSpan) : star f ∈ bcfExpSpan := by
  refine Submodule.span_induction (p := fun f _ => star f ∈ bcfExpSpan) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨s, rfl⟩
    have h : star (bcfExp s) = bcfExp (s.1, -s.2) := by
      ext p
      exact conj_laplaceFourierExp _ _ p
    rw [h]
    exact bcfExp_mem_span _
  · simp
  · intro a b _ _ ha hb
    rw [star_add]
    exact add_mem ha hb
  · intro c a _ ha
    rw [star_smul]
    exact Submodule.smul_mem _ _ ha
def bcfExpAlgebra : StarSubalgebra ℂ (BoundedContinuousFunction EnergyMomentumSpace ℂ) :=
  { Submodule.toSubalgebra bcfExpSpan one_mem_bcfExpSpan mul_mem_bcfExpSpan with
    star_mem' := fun {f} hf => star_mem_bcfExpSpan f hf }
theorem mem_bcfExpAlgebra_iff (f : BoundedContinuousFunction EnergyMomentumSpace ℂ) :
    f ∈ bcfExpAlgebra ↔ f ∈ bcfExpSpan := Iff.rfl
theorem exists_laplaceFourierExp_ne {p p' : EnergyMomentumSpace} (h : p ≠ p') :
    ∃ s : ℝ≥0 × Momentum3, laplaceFourierExp s.1 s.2 p ≠ laplaceFourierExp s.1 s.2 p' := by
  by_cases h₁ : p.1 = p'.1
  · have h₂ : p.2 ≠ p'.2 := fun h₂ => h (Prod.ext h₁ h₂)
    obtain ⟨i, hi⟩ : ∃ i, p.2 i ≠ p'.2 i := by
      by_contra hc
      exact h₂ (PiLp.ext fun i => by_contra fun hi => hc ⟨i, hi⟩)
    have hd : p.2 i - p'.2 i ≠ 0 := sub_ne_zero.mpr hi
    let c : ℝ := Real.pi / (p.2 i - p'.2 i)
    have hdot : ∀ q : Momentum3, spatialDot (EuclideanSpace.single i c) q = c * q i := by
      intro q
      simp [spatialDot]
    refine ⟨(0, EuclideanSpace.single i c), fun he => ?_⟩
    simp only [laplaceFourierExp, hdot, NNReal.coe_zero, neg_zero, zero_mul, Complex.ofReal_zero,
      zero_add] at he
    have hdiff : c * p.2 i - c * p'.2 i = Real.pi := by
      simp only [c]
      field_simp
    have hmul : Complex.exp (Complex.I * ((c * p.2 i - c * p'.2 i : ℝ) : ℂ)) = 1 := by
      have hne : Complex.exp (Complex.I * ((c * p'.2 i : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
      have hsplit : Complex.I * ((c * p.2 i - c * p'.2 i : ℝ) : ℂ) =
          Complex.I * ((c * p.2 i : ℝ) : ℂ) - Complex.I * ((c * p'.2 i : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hsplit, Complex.exp_sub, he, div_self hne]
    rw [hdiff, mul_comm, Complex.exp_pi_mul_I] at hmul
    norm_num at hmul
  · refine ⟨(1, 0), fun he => h₁ ?_⟩
    have hdot : ∀ q : Momentum3, spatialDot 0 q = 0 := fun q => by simp [spatialDot]
    simp only [laplaceFourierExp, hdot, NNReal.coe_one, Complex.ofReal_zero, mul_zero,
      add_zero] at he
    have he' : Real.exp (-1 * (p.1 : ℝ)) = Real.exp (-1 * (p'.1 : ℝ)) := by
      have h₂ : ((Real.exp (-1 * (p.1 : ℝ)) : ℝ) : ℂ) =
          ((Real.exp (-1 * (p'.1 : ℝ)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_exp, Complex.ofReal_exp]
        exact he
      exact Complex.ofReal_injective h₂
    have := Real.exp_injective he'
    exact NNReal.coe_injective (by linarith)
theorem measure_eq_of_integral_laplaceFourierExp_eq (M M' : Measure EnergyMomentumSpace)
    [IsFiniteMeasure M] [IsFiniteMeasure M']
    (h : ∀ (t : ℝ≥0) (y : Momentum3),
      ∫ x, laplaceFourierExp t y x ∂M' = ∫ x, laplaceFourierExp t y x ∂M) : M' = M := by
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable (𝕜 := ℂ)
    (A := bcfExpAlgebra) ?_ ?_
  · intro p p' hp
    obtain ⟨s, hs⟩ := exists_laplaceFourierExp_ne hp
    refine ⟨_, ⟨_, ⟨bcfExp s, bcfExp_mem_span s, rfl⟩, rfl⟩, hs⟩
  · intro g hg
    refine Submodule.span_induction
      (p := fun (g : BoundedContinuousFunction EnergyMomentumSpace ℂ) _ =>
        ∫ x, (g : EnergyMomentumSpace → ℂ) x ∂M' = ∫ x, (g : EnergyMomentumSpace → ℂ) x ∂M)
      ?_ ?_ ?_ ?_ ((mem_bcfExpAlgebra_iff g).mp hg)
    · rintro _ ⟨s, rfl⟩
      exact h s.1 s.2
    · simp
    · intro a b _ _ ha hb
      simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
      rw [integral_add (a.integrable M') (b.integrable M'),
        integral_add (a.integrable M) (b.integrable M), ha, hb]
    · intro c a _ ha
      simp only [BoundedContinuousFunction.coe_smul]
      rw [integral_smul, integral_smul, ha]
theorem integrable_laplaceFourierExp_mul (M : Measure EnergyMomentumSpace) (t : ℝ≥0)
    (y : Momentum3) {v : EnergyMomentumSpace → ℂ} (hv : Integrable v M) :
    Integrable (fun x => laplaceFourierExp t y x * v x) M := by
  refine hv.norm.mono' ((continuous_laplaceFourierExp t y).aestronglyMeasurable.mul
    hv.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_laplaceFourierExp_le_one t y x)
theorem ae_eq_zero_of_integral_laplaceFourierExp_mul_eq_zero (M : Measure EnergyMomentumSpace)
    [IsFiniteMeasure M] {u : EnergyMomentumSpace → ℝ} (hum : Measurable u) (hu : Integrable u M)
    (h : ∀ (t : ℝ≥0) (y : Momentum3), ∫ x, laplaceFourierExp t y x * (u x : ℂ) ∂M = 0) :
    u =ᵐ[M] 0 := by
  have hnu : Integrable (fun x => -u x) M := hu.neg
  have ha : Measurable fun x => ENNReal.ofReal (u x) := hum.ennreal_ofReal
  have hb : Measurable fun x => ENNReal.ofReal (-u x) := hum.neg.ennreal_ofReal
  have hfa : ∫⁻ x, ENNReal.ofReal (u x) ∂M ≠ ∞ := hu.lintegral_lt_top.ne
  have hfb : ∫⁻ x, ENNReal.ofReal (-u x) ∂M ≠ ∞ := hnu.lintegral_lt_top.ne
  have : IsFiniteMeasure (M.withDensity fun x => ENNReal.ofReal (u x)) :=
    isFiniteMeasure_withDensity hfa
  have : IsFiniteMeasure (M.withDensity fun x => ENNReal.ofReal (-u x)) :=
    isFiniteMeasure_withDensity hfb
  have key : M.withDensity (fun x => ENNReal.ofReal (u x)) =
      M.withDensity fun x => ENNReal.ofReal (-u x) := by
    refine measure_eq_of_integral_laplaceFourierExp_eq _ _ fun t y => ?_
    rw [integral_withDensity_eq_integral_toReal_smul ha
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul hb
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    have hA : Integrable (fun x => laplaceFourierExp t y x * ((max (u x) 0 : ℝ) : ℂ)) M :=
      integrable_laplaceFourierExp_mul M t y hu.pos_part.ofReal
    have hB : Integrable (fun x => laplaceFourierExp t y x * ((max (-u x) 0 : ℝ) : ℂ)) M :=
      integrable_laplaceFourierExp_mul M t y hnu.pos_part.ofReal
    have hsub := integral_sub hA hB
    have hcongr : (fun x => laplaceFourierExp t y x * ((max (u x) 0 : ℝ) : ℂ) -
        laplaceFourierExp t y x * ((max (-u x) 0 : ℝ) : ℂ)) =
        fun x => laplaceFourierExp t y x * (u x : ℂ) := by
      funext x
      rw [← mul_sub, ← Complex.ofReal_sub]
      congr 2
      rcases le_total (u x) 0 with h0 | h0
      · rw [max_eq_right h0, max_eq_left (by linarith)]
        ring
      · rw [max_eq_left h0, max_eq_right (by linarith)]
        ring
    rw [hcongr, h t y] at hsub
    have hleft : ∀ v : EnergyMomentumSpace → ℝ,
        (fun x => (ENNReal.ofReal (v x)).toReal • laplaceFourierExp t y x) =
          fun x => laplaceFourierExp t y x * ((max (v x) 0 : ℝ) : ℂ) := by
      intro v
      funext x
      rw [ENNReal.toReal_ofReal', Complex.real_smul, mul_comm]
    rw [hleft u, hleft fun x => -u x]
    exact sub_eq_zero.mp hsub.symm
  have hae := (withDensity_eq_iff ha.aemeasurable hb.aemeasurable hfa).mp key
  filter_upwards [hae] with x hx
  change u x = 0
  rcases le_total (u x) 0 with h0 | h0
  · rw [ENNReal.ofReal_of_nonpos h0] at hx
    have := ENNReal.ofReal_eq_zero.mp hx.symm
    exact le_antisymm h0 (by linarith)
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -u x ≤ 0)] at hx
    have := ENNReal.ofReal_eq_zero.mp hx
    exact le_antisymm this h0
theorem memLp_laplaceFourierExp (M : Measure EnergyMomentumSpace) [IsFiniteMeasure M] (t : ℝ≥0)
    (y : Momentum3) : MemLp (laplaceFourierExp t y) 2 M :=
  MemLp.of_bound (continuous_laplaceFourierExp t y).aestronglyMeasurable 1
    (ae_of_all _ (norm_laplaceFourierExp_le_one t y))
def laplaceFourierExpLp (M : Measure EnergyMomentumSpace) [IsFiniteMeasure M]
    (s : ℝ≥0 × Momentum3) : Lp ℂ 2 M :=
  (memLp_laplaceFourierExp M s.1 s.2).toLp _
theorem orthogonal_span_laplaceFourierExpLp (M : Measure EnergyMomentumSpace) [IsFiniteMeasure M] :
    (Submodule.span ℂ (range (laplaceFourierExpLp M)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  have hgi : Integrable (g : EnergyMomentumSpace → ℂ) M := (Lp.memLp g).integrable one_le_two
  have hgm : Measurable (g : EnergyMomentumSpace → ℂ) := (Lp.stronglyMeasurable g).measurable
  have h₀ : ∀ (t : ℝ≥0) (y : Momentum3), ∫ x, laplaceFourierExp t y x * g x ∂M = 0 := by
    intro t y
    have h := Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span ⟨(t, -y), rfl⟩ :
        laplaceFourierExpLp M (t, -y) ∈ Submodule.span ℂ (range (laplaceFourierExpLp M))) hg
    rw [L2.inner_def] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_laplaceFourierExp M t (-y))] with x hx
    have hx' : (laplaceFourierExpLp M (t, -y) : EnergyMomentumSpace → ℂ) x =
        laplaceFourierExp t (-y) x := hx
    rw [hx', RCLike.inner_apply, conj_laplaceFourierExp, neg_neg, mul_comm]
  have h₁ : ∀ (t : ℝ≥0) (y : Momentum3), ∫ x, laplaceFourierExp t y x * conj (g x) ∂M = 0 := by
    intro t y
    have h := congrArg (conj : ℂ → ℂ) (h₀ t (-y))
    rw [← integral_conj, map_zero] at h
    rw [← h]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [map_mul, conj_laplaceFourierExp, neg_neg]
  have hci : Integrable (fun x => conj (g x)) M := hgi.norm.mono'
    (Complex.continuous_conj.comp_aestronglyMeasurable hgi.aestronglyMeasurable)
    (ae_of_all _ fun x => by simp)
  have hre : (fun x => (g x).re) =ᵐ[M] 0 := by
    refine ae_eq_zero_of_integral_laplaceFourierExp_mul_eq_zero M
      (Complex.measurable_re.comp hgm) hgi.re fun t y => ?_
    have hs := integral_add (integrable_laplaceFourierExp_mul M t y hgi)
      (integrable_laplaceFourierExp_mul M t y hci)
    rw [h₀, h₁, add_zero] at hs
    have hc : (fun x => laplaceFourierExp t y x * g x + laplaceFourierExp t y x * conj (g x)) =
        fun x => (2 : ℂ) * (laplaceFourierExp t y x * ((g x).re : ℂ)) := by
      funext x
      rw [← mul_add, Complex.add_conj]
      push_cast
      ring
    rw [hc, integral_const_mul] at hs
    simpa using hs
  have him : (fun x => (g x).im) =ᵐ[M] 0 := by
    refine ae_eq_zero_of_integral_laplaceFourierExp_mul_eq_zero M
      (Complex.measurable_im.comp hgm) hgi.im fun t y => ?_
    have hs := integral_sub (integrable_laplaceFourierExp_mul M t y hgi)
      (integrable_laplaceFourierExp_mul M t y hci)
    rw [h₀, h₁, sub_zero] at hs
    have hc : (fun x => laplaceFourierExp t y x * g x - laplaceFourierExp t y x * conj (g x)) =
        fun x => ((2 : ℂ) * Complex.I) * (laplaceFourierExp t y x * ((g x).im : ℂ)) := by
      funext x
      rw [← mul_sub, Complex.sub_conj]
      push_cast
      ring
    rw [hc, integral_const_mul] at hs
    simpa using hs
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hre, him] with x h₂ h₃
  exact Complex.ext h₂ h₃
theorem exists_mem_laplaceFourierSpan_of_mem_span (M : Measure EnergyMomentumSpace)
    [IsFiniteMeasure M] (k : Lp ℂ 2 M)
    (hk : k ∈ Submodule.span ℂ (range (laplaceFourierExpLp M))) :
    ∃ p ∈ laplaceFourierSpan, (k : EnergyMomentumSpace → ℂ) =ᵐ[M] p := by
  refine Submodule.span_induction
    (p := fun (k : Lp ℂ 2 M) _ => ∃ p ∈ laplaceFourierSpan, (k : EnergyMomentumSpace → ℂ) =ᵐ[M] p)
    ?_ ?_ ?_ ?_ hk
  · rintro _ ⟨s, rfl⟩
    exact ⟨laplaceFourierExp s.1 s.2, Submodule.subset_span ⟨s, rfl⟩,
      MemLp.coeFn_toLp (memLp_laplaceFourierExp M s.1 s.2)⟩
  · exact ⟨0, zero_mem _, Lp.coeFn_zero _ _ _⟩
  · rintro a b _ _ ⟨p, hp, ha⟩ ⟨q, hq, hb⟩
    exact ⟨p + q, add_mem hp hq, (Lp.coeFn_add a b).trans (ha.add hb)⟩
  · rintro c a _ ⟨p, hp, ha⟩
    exact ⟨c • p, Submodule.smul_mem _ _ hp, (Lp.coeFn_smul c a).trans (ha.const_smul c)⟩
theorem eLpNorm_two_sq_eq_lintegral (M : Measure EnergyMomentumSpace)
    (f : EnergyMomentumSpace → ℂ) : eLpNorm f 2 M ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂M := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := M) (f := f) (p := 2) two_ne_zero
  simpa [ENNReal.rpow_two] using h
theorem dense_laplaceFourierSpan (M : Measure EnergyMomentumSpace) [IsFiniteMeasure M]
    (φ : EnergyMomentumSpace → ℂ) (hφ : EuclideanSpectral.MemSqIntegrable M φ) :
    ∃ p : ℕ → EnergyMomentumSpace → ℂ, (∀ n, p n ∈ laplaceFourierSpan) ∧
      EuclideanSpectral.TendstoSqMean M p φ := by
  have hmem : MemLp φ 2 M := by
    refine ⟨hφ.1.aestronglyMeasurable, ?_⟩
    have h : eLpNorm φ 2 M ^ 2 < ∞ := by
      rw [eLpNorm_two_sq_eq_lintegral]
      exact hφ.2
    exact (ENNReal.pow_lt_top_iff.mp h).resolve_right two_ne_zero
  have hK := (Submodule.topologicalClosure_eq_top_iff
    (K := Submodule.span ℂ (range (laplaceFourierExpLp M)))).mpr
      (orthogonal_span_laplaceFourierExpLp M)
  have hF : hmem.toLp φ ∈ closure
      ((Submodule.span ℂ (range (laplaceFourierExpLp M)) : Submodule ℂ (Lp ℂ 2 M)) :
        Set (Lp ℂ 2 M)) := by
    rw [← Submodule.topologicalClosure_coe, hK]
    trivial
  have hstep : ∀ n : ℕ, ∃ k ∈ Submodule.span ℂ (range (laplaceFourierExpLp M)),
      dist k (hmem.toLp φ) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨k, hk, hd⟩ := Metric.mem_closure_iff.mp hF (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨k, hk, by rwa [dist_comm]⟩
  choose k hk hd using hstep
  have hrep := fun n => exists_mem_laplaceFourierSpan_of_mem_span M (k n) (hk n)
  choose p hp hkp using hrep
  refine ⟨p, hp, ?_⟩
  have hlim : Tendsto k atTop (𝓝 (hmem.toLp φ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hed := (tendsto_iff_edist_tendsto_0.mp hlim)
  have hsq : Tendsto (fun n => edist (k n) (hmem.toLp φ) ^ 2) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.pow (n := 2) hed
  refine hsq.congr fun n => ?_
  rw [Lp.edist_def, ← eLpNorm_two_sq_eq_lintegral]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [hkp n, MemLp.coeFn_toLp hmem] with x h₁ h₂
  simp only [Pi.sub_apply, h₁, h₂]
theorem laplaceFourierDenseDetermining_holds : LaplaceFourierDenseDetermining := fun M _ =>
  ⟨dense_laplaceFourierSpan M,
    fun M' _ h => measure_eq_of_integral_laplaceFourierExp_eq M M' h⟩
end YangMills.Construction.EnergyMomentum.DenseDetermining
