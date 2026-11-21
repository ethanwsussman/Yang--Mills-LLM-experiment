import Mathlib

/-! Low-temperature concentration for a compact Gibbs model and minimum selection at a positive level. -/

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Formulation

/-- On a compact space with full-support probability measure, cooling towards a
nonnegative continuous action forces observables vanishing on its minima to zero. -/
theorem cold_gibbs_expectation {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] (s f : X → ℝ)
    (hs : Continuous s) (hf : Continuous f) (hs₀ : ∀ x, 0 ≤ s x)
    (x₀ : X) (hx₀ : s x₀ = 0) (hmin : ∀ x, s x = 0 → f x = 0) :
    Tendsto (fun b : ℝ =>
      (∫ x, f x * Real.exp (-b * s x) ∂μ) / (∫ x, Real.exp (-b * s x) ∂μ)) atTop (𝓝 0) := by
  have integ {F : X → ℝ} (h : Continuous F) : Integrable F μ :=
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  obtain ⟨z, _, hmax⟩ := isCompact_univ.exists_isMaxOn (⟨x₀, mem_univ _⟩ : (univ : Set X).Nonempty)
    hf.abs.continuousOn
  let M := |f z|
  have hM : 0 ≤ M := abs_nonneg _
  have hbound (x : X) : |f x| ≤ M := hmax (mem_univ x)
  let D : Set X := {x | ε / 2 ≤ |f x|}
  have hD : IsClosed D := isClosed_le continuous_const hf.abs
  have sep : ∃ d > (0 : ℝ), ∀ x ∈ D, d ≤ s x := by
    by_cases h : D.Nonempty
    · obtain ⟨y, hy, hlow⟩ := hD.isCompact.exists_isMinOn h hs.continuousOn
      refine ⟨s y, lt_of_le_of_ne (hs₀ y) ?_, fun x hx => hlow hx⟩
      intro hz
      have hfy := hmin y hz.symm
      change ε / 2 ≤ |f y| at hy
      simp [hfy] at hy
      linarith
    · exact ⟨1, zero_lt_one, fun x hx => (h ⟨x, hx⟩).elim⟩
  obtain ⟨d, hd, hsep⟩ := sep
  let U : Set X := {x | s x < d / 2}
  have hU : IsOpen U := isOpen_lt hs continuous_const
  let m := μ.real U
  have hm : 0 < m := ENNReal.toReal_pos (hU.measure_pos μ ⟨x₀, by
    change s x₀ < d / 2
    rw [hx₀]
    positivity⟩).ne' (measure_ne_top _ _)
  have hinfty : Tendsto (fun b : ℝ => -b * (d / 2)) atTop atBot :=
    tendsto_neg_atTop_atBot.atBot_mul_const (by positivity)
  have hind : Tendsto (fun b : ℝ => M / m * Real.exp (-b * (d/2))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hinfty).const_mul (M / m)
  filter_upwards [eventually_ge_atTop (0 : ℝ), hind.eventually_lt_const he] with b hb herr
  let w (x : X) := Real.exp (-b * s x)
  have hw : Continuous w := (continuous_const.mul hs).rexp
  have hw₀ (x : X) : 0 < w x := Real.exp_pos _
  let Z := ∫ x, w x ∂μ
  have hweight : m * Real.exp (-b*(d/2)) ≤ Z := calc
    _ = ∫ _ in U, Real.exp (-b*(d/2)) ∂μ := by simp [m, smul_eq_mul]
    _ ≤ ∫ x in U, w x ∂μ := setIntegral_mono_on (integrable_const _).integrableOn
      (integ hw).integrableOn hU.measurableSet fun x hx => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (le_of_lt hx) (neg_nonpos.mpr hb))
    _ ≤ Z := setIntegral_le_integral (integ hw) (Eventually.of_forall fun x => (hw₀ x).le)
  have hZ : 0 < Z := lt_of_lt_of_le (mul_pos hm (Real.exp_pos _)) hweight
  have hpoint (x : X) : |f x * w x| ≤ ε/2 * w x + M * Real.exp (-b*d) := by
    rw [abs_mul, abs_of_pos (hw₀ x)]
    by_cases hx : x ∈ D
    · have hwd : w x ≤ Real.exp (-b*d) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (hsep x hx) (neg_nonpos.mpr hb))
      exact (mul_le_mul (hbound x) hwd (hw₀ x).le hM).trans
        (le_add_of_nonneg_left (mul_nonneg he.le (hw₀ x).le))
    · have hsmall : |f x| ≤ ε/2 := le_of_lt (lt_of_not_ge hx)
      exact (mul_le_mul_of_nonneg_right hsmall (hw₀ x).le).trans
        (le_add_of_nonneg_right (mul_nonneg hM (Real.exp_pos _).le))
  have hnum : |∫ x, f x * w x ∂μ| ≤ ε/2 * Z + M * Real.exp (-b*d) := calc
    _ ≤ ∫ x, |f x * w x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ε/2 * w x + M * Real.exp (-b*d) ∂μ :=
      integral_mono (integ (hf.mul hw).abs) (integ ((continuous_const.mul hw).add continuous_const)) hpoint
    _ = _ := by rw [integral_add ((integ hw).const_mul _) (integrable_const _), integral_const_mul]; simp [Z]
  have htail : M * Real.exp (-b*d) ≤ (M / m * Real.exp (-b*(d/2))) * Z := calc
    _ = (M / m * Real.exp (-b*(d/2))) * (m * Real.exp (-b*(d/2))) := by
      have e : -b*d = -b*(d/2) + -b*(d/2) := by ring
      rw [e, Real.exp_add]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hZ]
  apply (div_lt_iff₀ hZ).mpr
  calc
    _ ≤ ε/2 * Z + M * Real.exp (-b*d) := hnum
    _ ≤ ε/2 * Z + (M / m * Real.exp (-b*(d/2))) * Z := add_le_add_right htail _
    _ < ε * Z := by nlinarith [mul_pos (sub_pos.mpr herr) hZ]

theorem isLeast_positive_level {F : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn F (Ioi 0)) (hz : Tendsto F (𝓝[>] 0) (𝓝 0))
    (ha : {g : ℝ | 0 < g ∧ F g = r}.Nonempty) :
    IsLeast {g : ℝ | 0 < g ∧ F g = r} (sInf {g : ℝ | 0 < g ∧ F g = r}) := by
  obtain ⟨ε, hε, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hz.eventually_lt_const hr)
  have hclosed : IsClosed (Ici ε ∩ F ⁻¹' {r}) :=
    (hc.mono (fun _ hx => hε.trans_le hx)).preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
  have heq : {g : ℝ | 0 < g ∧ F g = r} = Ici ε ∩ F ⁻¹' {r} := by
    ext g
    constructor
    · rintro ⟨hg, hg'⟩
      refine ⟨?_, hg'⟩
      change ε ≤ g
      by_contra! h
      exact (hsmall ⟨hg,h⟩).ne hg'
    · rintro ⟨hg, hg'⟩
      exact ⟨hε.trans_le hg, hg'⟩
  exact (heq ▸ hclosed : IsClosed {g : ℝ | 0 < g ∧ F g = r}).isLeast_csInf ha
    ⟨0, fun _ hg => hg.1.le⟩

/-- A single value above the level suffices for the smallest positive root,
even if the observable oscillates. -/
theorem isLeast_positive_level_of_le {F : ℝ → ℝ} {r b : ℝ}
    (hr : 0 < r) (hb : 0 < b) (hcross : r ≤ F b)
    (hc : ContinuousOn F (Ioi 0)) (hz : Tendsto F (𝓝[>] 0) (𝓝 0)) :
    IsLeast {g : ℝ | 0 < g ∧ F g = r} (sInf {g : ℝ | 0 < g ∧ F g = r}) ∧
      sInf {g : ℝ | 0 < g ∧ F g = r} ≤ b := by
  obtain ⟨ε, hε, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hz.eventually_lt_const hr)
  obtain ⟨a, ha, h⟩ := exists_between (lt_min (a := (0 : ℝ)) hε hb)
  have hab := le_of_lt (lt_of_lt_of_le h (min_le_right _ _))
  obtain ⟨g, hg, heq⟩ := intermediate_value_Icc hab
    (hc.mono ((Icc_subset_Ioi_iff hab).mpr ha))
    (show r ∈ Icc (F a) (F b) from ⟨(hsmall ⟨ha, h.trans_le (min_le_left _ _)⟩).le, hcross⟩)
  have hmem : g ∈ {v : ℝ | 0 < v ∧ F v = r} := ⟨ha.trans_le hg.1, heq⟩
  have hleast := isLeast_positive_level hr hc hz ⟨g, hmem⟩
  exact ⟨hleast, (hleast.2 hmem).trans hg.2⟩

end YangMills.Formulation
