import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayer
import YangMills.Construction.InfiniteLattice.FinitenessOfATorusNormalisersAndExtendedMeasures
import YangMills.Construction.InfiniteLattice.FoldedArrayAndTheMirrorsOfTheLadder
import YangMills.Construction.InfiniteLattice.LowerTangentUpperTangentAndTheInequalityInFiniteVolume
import YangMills.Construction.InfiniteLattice.LowerTangentsAtAConstantFunction
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusOfAnyShape
import YangMills.Construction.InfiniteLattice.PeriodsFoldCompactnessAndLimitsOfToriProof
import YangMills.Construction.InfiniteLattice.PropertiesOfThePeriodGroups
import YangMills.Construction.ReflectionPositivity.PullBacksOnASplitTorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
open YangMills.Construction.PeriodicLattice (coordVec)
namespace FiniteVolumeTangentBounds
namespace ExpTilt
variable {t : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] (m : Measure Ω) (X P : Ω → ℝ)
def density (t : ℝ) (U : Ω) : ℝ := Real.exp (t * X U - P U)
def normalizer (t : ℝ) : ℝ := ∫ U, density X P t U ∂m
def tilt (t : ℝ) : Measure Ω :=
  (ENNReal.ofReal (normalizer m X P t))⁻¹ •
    m.withDensity fun U => ENNReal.ofReal (density X P t U)
variable {X P}
theorem density_pos (t : ℝ) (U : Ω) : 0 < density X P t U := Real.exp_pos _
theorem measurable_density (hX : Measurable X) (hP : Measurable P) (t : ℝ) :
    Measurable (density X P t) :=
  Real.measurable_exp.comp ((measurable_const.mul hX).sub hP)
theorem density_le_exp {a b : ℝ} (hXb : ∀ U, |X U| ≤ a) (hPb : ∀ U, |P U| ≤ b) (t : ℝ) (U : Ω) :
    density X P t U ≤ Real.exp (|t| * a + b) := by
  refine Real.exp_le_exp.mpr ?_
  have h1 : t * X U ≤ |t| * a :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hXb U) (abs_nonneg t))
  have h2 : -P U ≤ b := (neg_le_abs _).trans (hPb U)
  linarith
variable [IsFiniteMeasure m]
theorem integrable_of_norm_le {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ U, ‖f U‖ ≤ C) : Integrable f m :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ h)
theorem integrable_density (hX : Measurable X) (hP : Measurable P) {a b : ℝ}
    (hXb : ∀ U, |X U| ≤ a) (hPb : ∀ U, |P U| ≤ b) (t : ℝ) : Integrable (density X P t) m :=
  integrable_of_norm_le m (measurable_density hX hP t) (C := Real.exp (|t| * a + b)) fun U => by
    rw [Real.norm_of_nonneg (density_pos t U).le]
    exact density_le_exp hXb hPb t U
theorem hasDerivAt_normalizer (hX : Measurable X) (hP : Measurable P) {a b : ℝ}
    (hXb : ∀ U, |X U| ≤ a) (hPb : ∀ U, |P U| ≤ b) (t : ℝ) :
    HasDerivAt (normalizer m X P) (∫ U, X U * density X P t U ∂m) t := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := m) (x₀ := t)
    (F := fun s U => density X P s U) (F' := fun s U => X U * density X P s U)
    (s := Metric.ball t 1) (bound := fun _ => |a| * Real.exp ((|t| + 1) * |a| + b))
    (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s => (measurable_density hX hP s).aestronglyMeasurable)
    (integrable_density m hX hP hXb hPb t)
    (hX.mul (measurable_density hX hP t)).aestronglyMeasurable
    (ae_of_all _ fun U s hs => ?_) (integrable_const _)
    (ae_of_all _ fun U s _ => ?_)
  · exact key.2
  · have hs' : |s| ≤ |t| + 1 := by
      have h1 : |s - t| < 1 := by simpa [Real.dist_eq] using hs
      have h2 : |s| ≤ |s - t| + |t| := by
        simpa using abs_add_le (s - t) t
      linarith
    have hXa : |X U| ≤ |a| := (hXb U).trans (le_abs_self a)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (density_pos s U)]
    refine mul_le_mul hXa ?_ (density_pos s U).le (abs_nonneg a)
    refine (density_le_exp (fun V => (hXb V).trans (le_abs_self a)) hPb s U).trans ?_
    exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg a])
  · have h1 : HasDerivAt (fun s : ℝ => s * X U - P U) (X U) s := by
      simpa using ((hasDerivAt_id s).mul_const (X U)).sub_const (P U)
    have h2 := h1.exp
    simpa [density, mul_comm] using h2
theorem normalizer_convexComb_le (hX : Measurable X) (hP : Measurable P) {a b : ℝ}
    (hXb : ∀ U, |X U| ≤ a) (hPb : ∀ U, |P U| ≤ b) {x y p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q = 1) :
    normalizer m X P (p * x + q * y) ≤ normalizer m X P x ^ p * normalizer m X P y ^ q := by
  have hconj : (1 / p).HolderConjugate (1 / q) := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hp]
      linarith
    · simp [hpq]
  have hfm : ∀ (s r : ℝ), Measurable fun U => density X P s U ^ r := fun s r =>
    (measurable_density hX hP s).pow_const r
  have hmem : ∀ (s r u : ℝ), 0 ≤ r →
      MemLp (fun U => density X P s U ^ r) (ENNReal.ofReal u) m := fun s r u hr =>
    MemLp.of_bound (hfm s r).aestronglyMeasurable (Real.exp (|s| * a + b) ^ r)
      (ae_of_all _ fun U => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (density_pos s U).le r)]
        exact Real.rpow_le_rpow (density_pos s U).le (density_le_exp hXb hPb s U) hr)
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := m) hconj
    (f := fun U => density X P x U ^ p) (g := fun U => density X P y U ^ q)
    (ae_of_all _ fun U => Real.rpow_nonneg (density_pos x U).le p)
    (ae_of_all _ fun U => Real.rpow_nonneg (density_pos y U).le q)
    (hmem x p _ hp.le) (hmem y q _ hq.le)
  have hroot : ∀ (s r : ℝ), 0 < r → ∀ U, (density X P s U ^ r) ^ (1 / r) = density X P s U :=
    fun s r hr U => by
      rw [← Real.rpow_mul (density_pos s U).le, mul_one_div_cancel hr.ne', Real.rpow_one]
  have hprod : ∀ U, density X P x U ^ p * density X P y U ^ q = density X P (p * x + q * y) U := by
    intro U
    rw [density, density, density, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    have : q = 1 - p := by linarith
    subst this
    ring
  simp only [hprod, hroot x p hp, hroot y q hq, one_div_one_div] at key
  exact key
theorem log_normalizer_convexComb_le (hZ : ∀ t, 0 < normalizer m X P t) (hX : Measurable X)
    (hP : Measurable P) {a b : ℝ} (hXb : ∀ U, |X U| ≤ a) (hPb : ∀ U, |P U| ≤ b) {x y p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1) :
    Real.log (normalizer m X P (p * x + q * y)) ≤
      p * Real.log (normalizer m X P x) + q * Real.log (normalizer m X P y) := by
  have h := Real.log_le_log (hZ _)
    (normalizer_convexComb_le m hX hP hXb hPb (x := x) (y := y) hp hq hpq)
  rwa [Real.log_mul (Real.rpow_pos_of_pos (hZ x) p).ne' (Real.rpow_pos_of_pos (hZ y) q).ne',
    Real.log_rpow (hZ x), Real.log_rpow (hZ y)] at h
theorem scaledLogRatio_props (hZ : ∀ t, 0 < normalizer m X P t) (hX : Measurable X)
    (hP : Measurable P) {a b : ℝ} (hXb : ∀ U, |X U| ≤ a) (hPb : ∀ U, |P U| ≤ b) {c : ℝ}
    (hc : 0 ≤ c) :
    let φ : ℝ → ℝ := fun t => c * Real.log (normalizer m X P t / normalizer m X P 0)
    ConvexOn ℝ Set.univ φ ∧ Differentiable ℝ φ ∧ φ 0 = 0 ∧ (∀ t, φ t ≤ t * deriv φ t) ∧
      ∀ t, deriv φ t = c * ((∫ U, X U * density X P t U ∂m) / normalizer m X P t) := by
  intro φ
  have hlog : ∀ t, φ t = c * (Real.log (normalizer m X P t) - Real.log (normalizer m X P 0)) :=
    fun t => by
      simp only [φ]
      rw [Real.log_div (hZ t).ne' (hZ 0).ne']
  have hder : ∀ t, HasDerivAt φ (c * ((∫ U, X U * density X P t U ∂m) / normalizer m X P t)) t := by
    intro t
    have h1 := hasDerivAt_normalizer m hX hP hXb hPb t
    have h2 := (h1.log (hZ t).ne').sub_const (Real.log (normalizer m X P 0))
    have h3 := h2.const_mul c
    exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall hlog)
  have hconv : ConvexOn ℝ Set.univ φ := by
    refine convexOn_iff_forall_pos.mpr ⟨convex_univ, ?_⟩
    intro x _ y _ p q hp hq hpq
    have h := log_normalizer_convexComb_le m hZ hX hP hXb hPb (x := x) (y := y) hp hq hpq
    simp only [smul_eq_mul]
    rw [hlog, hlog, hlog]
    have hz : Real.log (normalizer m X P 0) = (p + q) * Real.log (normalizer m X P 0) := by
      rw [hpq, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h hc]
  have hdiff : Differentiable ℝ φ := fun t => (hder t).differentiableAt
  have h0 : φ 0 = 0 := by
    rw [hlog]
    simp
  refine ⟨hconv, hdiff, h0, fun t => ?_, fun t => (hder t).deriv⟩
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h := hconv.deriv_le_slope (Set.mem_univ t) (Set.mem_univ 0) ht (hdiff t)
    rw [slope_def_field, h0] at h
    rw [le_div_iff₀ (by linarith)] at h
    nlinarith
  · simp [h0]
  · have h := hconv.slope_le_deriv (Set.mem_univ 0) (Set.mem_univ t) ht (hdiff t)
    rw [slope_def_field, h0, div_le_iff₀ (by linarith)] at h
    nlinarith
theorem integral_tilt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hZ : 0 < normalizer m X P t) (hX : Measurable X) (hP : Measurable P) (f : Ω → E) :
    ∫ U, f U ∂tilt m X P t = (normalizer m X P t)⁻¹ • ∫ U, density X P t U • f U ∂m := by
  rw [tilt, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul
    (measurable_density hX hP t).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) f]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only [ENNReal.toReal_ofReal (density_pos t U).le]
theorem isProbabilityMeasure_tilt (hZ : 0 < normalizer m X P t) (hX : Measurable X)
    (hP : Measurable P) {a b : ℝ} (hXb : ∀ U, |X U| ≤ a) (hPb : ∀ U, |P U| ≤ b) :
    IsProbabilityMeasure (tilt m X P t) := by
  refine ⟨?_⟩
  have hint := integrable_density m hX hP hXb hPb t
  have hl : ∫⁻ U, ENNReal.ofReal (density X P t U) ∂m = ENNReal.ofReal (normalizer m X P t) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun U => (density_pos t U).le)).symm
  rw [tilt, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hl,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top
theorem integral_comp_tilt (hZ : 0 < normalizer m X P t) (hX : Measurable X)
    (hP : Measurable P) {a b : ℝ} (hXb : ∀ U, |X U| ≤ a) (hPb : ∀ U, |P U| ≤ b) {T : Ω → Ω}
    (hm : ∀ F : Ω → ℂ, Measurable F → (∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) →
      ∫ U, F (T U) ∂m = ∫ U, F U ∂m)
    (hXT : ∀ U, X (T U) = X U) (hPT : ∀ U, P (T U) = P U) (F : Ω → ℂ) (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) : ∫ U, F (T U) ∂tilt m X P t = ∫ U, F U ∂tilt m X P t := by
  rw [integral_tilt m hZ hX hP, integral_tilt m hZ hX hP]
  congr 1
  have hw : ∀ U, density X P t (T U) = density X P t U := fun U => by
    simp only [density, hXT, hPT]
  obtain ⟨C, hC⟩ := hFb
  have := hm (fun U => density X P t U • F U) ((measurable_density hX hP t).smul hF)
    ⟨Real.exp (|t| * a + b) * C, fun U => by
      rw [norm_smul, Real.norm_of_nonneg (density_pos t U).le]
      exact mul_le_mul (density_le_exp hXb hPb t U) (hC U) (norm_nonneg _) (Real.exp_pos _).le⟩
  simp only [hw] at this
  exact this
end ExpTilt
section Arrays
variable (𝔸 : LocalObservableArray) (Γ : PeriodSublattice 1)
theorem continuous_shift_toFun (v : LatticePoint 1) : Continuous (shift v).toFun :=
  continuous_id.add continuous_const
theorem shift_actOn_mem {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1)
    (v : LatticePoint 1) : (shift v).actOn F ∈ continuousLocalFunctions 1 :=
  actOn_mem_continuousLocalFunctions _ (continuous_shift_toFun v) hF
theorem arrayTerm_mem (i : 𝔸.Label) : 𝔸.translate i ∈ continuousLocalFunctions 1 :=
  shift_actOn_mem (𝔸.gen_mem i.2) _
theorem exists_norm_bound_periodize {F : GaugeField 1 → ℂ}
    (hF : F ∈ continuousLocalFunctions 1) :
    ∃ C : ℝ, ∀ U : Γ.QuotientField, ‖Γ.periodize F U‖ ≤ C := by
  obtain ⟨⟨-, C, hC⟩, -, -⟩ := hF
  exact ⟨C, fun U => hC _⟩
variable {Γ}
theorem measurable_periodize (hE : Γ.QuotientLiftFacts) {F : GaugeField 1 → ℂ}
    (hF : F ∈ continuousLocalFunctions 1) : Measurable (Γ.periodize F) :=
  (hE.continuous_periodize F hF).measurable
theorem isBoundedBorelFn_periodize (hE : Γ.QuotientLiftFacts)
    {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) :
    Γ.IsBoundedBorelFn (Γ.periodize F) :=
  ⟨measurable_periodize hE hF, exists_norm_bound_periodize Γ hF⟩
theorem periodicSum_eq_finsetSum
    [Fintype (𝔸.Cosets Γ × Fin 𝔸.size)] :
    𝔸.periodicSum Γ = fun U => ∑ i : 𝔸.Cosets Γ × Fin 𝔸.size,
      (Γ.periodize (𝔸.translate (𝔸.cosetRep Γ i.1, i.2)) U).re := by
  funext U
  exact finsum_eq_sum_of_fintype _
theorem finite_cosetLabels (hQ : Γ.IsFiniteOver 𝔸.sublattice) :
    Finite (𝔸.Cosets Γ × Fin 𝔸.size) := by
  have : Finite (𝔸.Cosets Γ) := hQ.finite_cosets
  infer_instance
theorem measurable_periodicSum (hE : Γ.QuotientLiftFacts)
    (hQ : Γ.IsFiniteOver 𝔸.sublattice) : Measurable (𝔸.periodicSum Γ) := by
  have := finite_cosetLabels 𝔸 hQ
  have := Fintype.ofFinite (𝔸.Cosets Γ × Fin 𝔸.size)
  rw [periodicSum_eq_finsetSum 𝔸]
  exact Finset.measurable_fun_sum _ fun i _ =>
    Complex.measurable_re.comp (measurable_periodize hE (arrayTerm_mem 𝔸 _))
theorem exists_abs_bound_periodicSum (hQ : Γ.IsFiniteOver 𝔸.sublattice) :
    ∃ a : ℝ, ∀ U, |𝔸.periodicSum Γ U| ≤ a := by
  have := finite_cosetLabels 𝔸 hQ
  have := Fintype.ofFinite (𝔸.Cosets Γ × Fin 𝔸.size)
  choose C hC using fun i : 𝔸.Cosets Γ × Fin 𝔸.size =>
    exists_norm_bound_periodize Γ (arrayTerm_mem 𝔸 (𝔸.cosetRep Γ i.1, i.2))
  refine ⟨∑ i, C i, fun U => ?_⟩
  rw [periodicSum_eq_finsetSum 𝔸]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => (Complex.abs_re_le_norm _).trans (hC i U))
variable (Γ) in
def totalEnergy (β : ℝ) (U : Γ.QuotientField) : ℝ :=
  β * ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p
theorem measurable_totalEnergy (hE : Γ.QuotientLiftFacts) (β : ℝ) :
    Measurable (totalEnergy Γ β) := by
  have := hE.finite_quotientPlaquette
  have := Fintype.ofFinite Γ.QuotientPlaquette
  have : totalEnergy Γ β = fun U => β * ∑ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p := by
    funext U
    rw [totalEnergy, finsum_eq_sum_of_fintype]
  rw [this]
  exact (Finset.measurable_fun_sum _ fun p _ =>
    (hE.continuous_quotientFaceEnergy p).measurable).const_mul β
theorem exists_abs_bound_totalEnergy (hE : Γ.QuotientLiftFacts) (β : ℝ) :
    ∃ b : ℝ, ∀ U, |totalEnergy Γ β U| ≤ b := by
  have := hE.finite_quotientPlaquette
  have := Fintype.ofFinite Γ.QuotientPlaquette
  refine ⟨|β| * ∑ _p : Γ.QuotientPlaquette, 2, fun U => ?_⟩
  rw [totalEnergy, finsum_eq_sum_of_fintype, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_of_nonneg (hE.quotientFaceEnergy_mem_Icc p U).1]
  exact (hE.quotientFaceEnergy_mem_Icc p U).2
theorem tiltedMeasure_eq_tilt (β t : ℝ) :
    𝔸.tiltedMeasure Γ β t =
      ExpTilt.tilt Γ.quotientHaar (𝔸.periodicSum Γ) (totalEnergy Γ β) t := rfl
variable {n : AmbientSpace} {hn : n ∈ normalSet} {z : ℤ} {β : ℝ}
theorem periodize_actOn (hp : SplitTorusPullbacks) (hβ : 0 < β)
    (hs : Γ.SplitsAlongWithHalfPeriod n z) (hn : n ∈ normalSet) {r : LatticeSymmetry 1}
    (hr : IsClassIsometry n r.toFun) {F : GaugeField 1 → ℂ}
    (hF : F ∈ continuousLocalFunctions 1) :
    Γ.periodize (r.actOn F) = Γ.compPullback r (Γ.periodize F) := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := (hp β hβ Γ n hn z hs).2.1 r hr
  exact h6 F hF
theorem periodize_shift_add (hp : SplitTorusPullbacks) (hβ : 0 < β)
    (hs : Γ.SplitsAlongWithHalfPeriod n z) (hn : n ∈ normalSet)
    (hE : Γ.QuotientLiftFacts) (u v : LatticePoint 1) {F : GaugeField 1 → ℂ}
    (hF : F ∈ continuousLocalFunctions 1) :
    Γ.periodize ((shift (u + v)).actOn F) =
      Γ.compPullback (shift v) (Γ.periodize ((shift u).actOn F)) := by
  have iso := isClassIsometry_shift n
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := (hp β hβ Γ n hn z hs).2.1 (shift v) (iso v)
  rw [periodize_actOn hp hβ hs hn (iso (u + v)) hF, periodize_actOn hp hβ hs hn (iso u) hF]
  symm
  refine h9 (shift u) (shift (u + v)) (iso u) ?_ _ (isBoundedBorelFn_periodize hE hF)
  funext x
  change x + ((u + v : LatticePoint 1) : AmbientSpace) = x + (u : AmbientSpace) + (v : AmbientSpace)
  rw [AddSubgroup.coe_add, add_assoc]
theorem periodize_shift_add_period (hp : SplitTorusPullbacks) (hβ : 0 < β)
    (hs : Γ.SplitsAlongWithHalfPeriod n z) (hn : n ∈ normalSet)
    (hE : Γ.QuotientLiftFacts) (u : LatticePoint 1) {γ : LatticePoint 1} (hγ : γ ∈ Γ.periods)
    {F : GaugeField 1 → ℂ} (hF : F ∈ continuousLocalFunctions 1) :
    Γ.periodize ((shift (u + γ)).actOn F) =
      Γ.periodize ((shift u).actOn F) := by
  rw [periodize_shift_add hp hβ hs hn hE u γ hF,
    ← periodize_actOn hp hβ hs hn (isClassIsometry_shift n γ) (shift_actOn_mem hF u)]
  exact (hp β hβ Γ n hn z hs).2.2.1 γ hγ _ (shift_actOn_mem hF u)
theorem periodize_translate_eq (hp : SplitTorusPullbacks) (hβ : 0 < β)
    (hs : Γ.SplitsAlongWithHalfPeriod n z) (hn : n ∈ normalSet)
    (hE : Γ.QuotientLiftFacts) {i i' : 𝔸.Label} (h2 : i.2 = i'.2)
    (h1 : (i.1 : 𝔸.Cosets Γ) = i'.1) :
    Γ.periodize (𝔸.translate i) = Γ.periodize (𝔸.translate i') := by
  obtain ⟨u, ι⟩ := i
  obtain ⟨u', ι'⟩ := i'
  obtain rfl : ι = ι' := h2
  have hmem : ((-u + u' : 𝔸.sublattice) : LatticePoint 1) ∈ Γ.periods :=
    AddSubgroup.mem_addSubgroupOf.mp (QuotientAddGroup.eq.mp h1)
  have hu : (u' : LatticePoint 1) = (u : LatticePoint 1) + ((-u + u' : 𝔸.sublattice) : LatticePoint 1) := by
    simp
  change Γ.periodize ((shift (u : LatticePoint 1)).actOn _) =
    Γ.periodize ((shift (u' : LatticePoint 1)).actOn _)
  rw [hu, periodize_shift_add_period hp hβ hs hn hE _ hmem (𝔸.gen_mem ι)]
theorem periodicSum_pullbackField (hp : SplitTorusPullbacks) (hβ : 0 < β)
    (hs : Γ.SplitsAlongWithHalfPeriod n z) (hn : n ∈ normalSet)
    (hE : Γ.QuotientLiftFacts) (hQ : Γ.IsFiniteOver 𝔸.sublattice)
    (r : LatticeSymmetry 1) (e : 𝔸.Label → 𝔸.Label)
    (he : ∀ i, Γ.compPullback r (Γ.periodize (𝔸.translate i)) = Γ.periodize (𝔸.translate (e i)))
    (hinj : ∀ i i' : 𝔸.Label, (e i).2 = (e i').2 → ((e i).1 : 𝔸.Cosets Γ) = (e i').1 →
      i.2 = i'.2 ∧ (i.1 : 𝔸.Cosets Γ) = i'.1) (U : Γ.QuotientField) :
    𝔸.periodicSum Γ (Γ.pullbackField r U) = 𝔸.periodicSum Γ U := by
  have := finite_cosetLabels 𝔸 hQ
  let rep : 𝔸.Cosets Γ × Fin 𝔸.size → 𝔸.Label := fun c => (𝔸.cosetRep Γ c.1, c.2)
  have hrep : ∀ c, ((rep c).1 : 𝔸.Cosets Γ) = c.1 := fun c => QuotientAddGroup.out_eq' c.1
  let f : 𝔸.Cosets Γ × Fin 𝔸.size → 𝔸.Cosets Γ × Fin 𝔸.size :=
    fun c => (((e (rep c)).1 : 𝔸.Cosets Γ), (e (rep c)).2)
  have hf : Function.Injective f := by
    intro c c' h
    have h1 : ((e (rep c)).1 : 𝔸.Cosets Γ) = (e (rep c')).1 := congrArg Prod.fst h
    have h2 : (e (rep c)).2 = (e (rep c')).2 := (Prod.ext_iff.mp h).2
    obtain ⟨a, b⟩ := hinj (rep c) (rep c') h2 h1
    exact Prod.ext (by rw [← hrep c, ← hrep c', b]) a
  let E : 𝔸.Cosets Γ × Fin 𝔸.size ≃ 𝔸.Cosets Γ × Fin 𝔸.size :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  let g : 𝔸.Cosets Γ × Fin 𝔸.size → ℝ := fun c => (Γ.periodize (𝔸.translate (rep c)) U).re
  have step : ∀ c, (Γ.periodize (𝔸.translate (rep c)) (Γ.pullbackField r U)).re = g (E c) := by
    intro c
    have h := congrFun (he (rep c)) U
    have h' : Γ.periodize (𝔸.translate (rep c)) (Γ.pullbackField r U) =
        Γ.periodize (𝔸.translate (e (rep c))) U := h
    rw [h']
    change _ = (Γ.periodize (𝔸.translate (rep (f c))) U).re
    rw [periodize_translate_eq 𝔸 hp hβ hs hn hE (i := e (rep c)) (i' := rep (f c)) rfl
      (hrep (f c)).symm]
  change ∑ᶠ c, (Γ.periodize (𝔸.translate (rep c)) (Γ.pullbackField r U)).re = ∑ᶠ c, g c
  rw [← finsum_comp_equiv E (f := g)]
  exact finsum_congr step
theorem preservesFiniteMeasure_tiltedMeasure (hp : SplitTorusPullbacks) (hβ : 0 < β)
    (hs : Γ.SplitsAlongWithHalfPeriod n z) (hn : n ∈ normalSet)
    (hE : Γ.QuotientLiftFacts) (hQ : Γ.IsFiniteOver 𝔸.sublattice) {t : ℝ}
    (hZ : 0 < 𝔸.tiltedPartition Γ β t) {r : LatticeSymmetry 1}
    (hr : IsClassIsometry n r.toFun)
    (hX : ∀ U, 𝔸.periodicSum Γ (Γ.pullbackField r U) = 𝔸.periodicSum Γ U) :
    PeriodSublattice.PreservesFiniteMeasure (Γ.pullbackField r) (𝔸.tiltedMeasure Γ β t) := by
  obtain ⟨-, ⟨hm, hfin, hint⟩, -, -, -, -, -, -, -, -, h11, -⟩ :=
    (hp β hβ Γ n hn z hs).2.1 r hr
  obtain ⟨a, ha⟩ := exists_abs_bound_periodicSum 𝔸 hQ
  obtain ⟨b, hb⟩ := exists_abs_bound_totalEnergy hE β
  have hmX := measurable_periodicSum 𝔸 hE hQ
  have hmP := measurable_totalEnergy hE β
  have hZ' : 0 < ExpTilt.normalizer Γ.quotientHaar (𝔸.periodicSum Γ) (totalEnergy Γ β) t :=
    hZ
  have hprob := ExpTilt.isProbabilityMeasure_tilt Γ.quotientHaar hZ' hmX hmP ha hb
  refine ⟨hm, ?_, fun F hF hFb => ?_⟩
  · rw [tiltedMeasure_eq_tilt]
    refine ⟨?_⟩
    rw [hprob.measure_univ]
    exact ENNReal.one_lt_top
  · rw [tiltedMeasure_eq_tilt]
    refine ExpTilt.integral_comp_tilt Γ.quotientHaar hZ' hmX hmP ha hb hint hX
      (fun U => ?_) F hF hFb
    exact congrArg (fun x => β * x) (congrFun h11 U)
theorem integral_periodicSum (hE : Γ.QuotientLiftFacts)
    (hQ : Γ.IsFiniteOver 𝔸.sublattice) (μ : Measure Γ.QuotientField) [IsFiniteMeasure μ] (I : ℂ)
    (hI : ∀ i : 𝔸.Label, ∫ U, Γ.periodize (𝔸.translate i) U ∂μ = I) :
    ∫ U, 𝔸.periodicSum Γ U ∂μ = (Nat.card (𝔸.Cosets Γ) : ℝ) * (𝔸.size : ℝ) * I.re := by
  have := finite_cosetLabels 𝔸 hQ
  have := hQ.finite_cosets
  have := Fintype.ofFinite (𝔸.Cosets Γ × Fin 𝔸.size)
  have hint : ∀ i : 𝔸.Label, Integrable (Γ.periodize (𝔸.translate i)) μ := fun i => by
    obtain ⟨C, hC⟩ := exists_norm_bound_periodize Γ (arrayTerm_mem 𝔸 i)
    exact Integrable.of_bound (measurable_periodize hE (arrayTerm_mem 𝔸 i)).aestronglyMeasurable C
      (ae_of_all _ hC)
  rw [periodicSum_eq_finsetSum 𝔸, integral_finsetSum]
  · have h : ∀ c : 𝔸.Cosets Γ × Fin 𝔸.size,
        ∫ U, (Γ.periodize (𝔸.translate (𝔸.cosetRep Γ c.1, c.2)) U).re ∂μ = I.re := by
      intro c
      have := Complex.reCLM.integral_comp_comm (hint (𝔸.cosetRep Γ c.1, c.2))
      rw [hI] at this
      exact this
    simp only [h, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _),
      Fintype.card_fin]
    push_cast
    ring
  · intro c _
    exact Complex.reCLM.integrable_comp (hint _)
end Arrays
section Numbers
theorem one_le_normSq {n : AmbientSpace} (hn : n ∈ normalSet) : 1 ≤ normSq n := by
  rw [normSq_eq_dotProduct]
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, lam, hlt, rfl | rfl⟩
  · rw [coordVec_dot_coordVec_self]
  · simp only [add_dotProduct, dotProduct_add, coordVec_dot_coordVec_self,
      coordVec_dot_coordVec_of_ne hlt.ne, coordVec_dot_coordVec_of_ne hlt.ne']
    norm_num
  · simp only [sub_dotProduct, dotProduct_sub, coordVec_dot_coordVec_self,
      coordVec_dot_coordVec_of_ne hlt.ne, coordVec_dot_coordVec_of_ne hlt.ne']
    norm_num
theorem half_inv_add_sum_inv_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (q : Fin 3 → ℝ)
    (hq : ∀ i, 1 ≤ q i) :
    1 / (2 * x) + ∑ i, 1 / (y * q i) ≤ 3 * (1 / x + 1 / y) := by
  have h1 : 1 / (2 * x) ≤ 3 * (1 / x) := by
    have : 1 / (2 * x) = (1 / x) / 2 := by field_simp
    have hp : 0 < 1 / x := by positivity
    rw [this]
    linarith
  have h2 : ∀ i, 1 / (y * q i) ≤ 1 / y := fun i =>
    one_div_le_one_div_of_le hy (le_mul_of_one_le_right hy.le (hq i))
  rw [Fin.sum_univ_three]
  linarith [h2 0, h2 1, h2 2]
theorem sum_inv_adaptedSideLengths {n : AmbientSpace} {hn : IsNormalVector n} {h J w : ℤ}
    {s : Fin 4 → ℕ+} (hs : IsAdaptedSideTuple n hn h J w s) :
    ∑ i, (((s i : ℕ) : ℝ))⁻¹ = 1 / (2 * (J : ℝ) * (h : ℝ)) +
      ∑ i : Fin 3, 1 / ((w : ℝ) * (normalFrame n hn).lengthSq i.succ) := by
  rw [Fin.sum_univ_succ, hs.1]
  simp only [hs.2, one_div]
variable {L : MirrorLadder} (A : L.SlabZeroGenerator)
theorem tangentDefect_eq_sideDefect (ϱ : ℕ+) (β : ℝ) {t : ℝ} (ht : 0 ≤ t) (J : ℕ) (w : ℤ)
    {s : Fin 4 → ℕ+}
    (hs : IsAdaptedSideTuple L.normal L.normal_mem L.spacing (J : ℤ) w s) :
    A.tangentDefect ϱ β t J w = LocalObservableArray.sideDefect s ϱ A.toFun β t := by
  rw [LocalObservableArray.sideDefect, sum_inv_adaptedSideLengths hs, abs_of_nonneg ht,
    MirrorLadder.SlabZeroGenerator.tangentDefect]
  simp only [tangentLowerConst, Int.cast_natCast]
theorem tangentDefect_le {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) (ϱ : ℕ+) {J : ℕ} {w : ℤ}
    (hJ : 1 ≤ J) (hw : 0 < w) :
    A.tangentDefect ϱ β t J w ≤ 3 * (tangentLowerConst : ℝ) *
      (β + t * observableSupNorm A.toFun) * ((ϱ : ℕ) : ℝ) ^ 5 *
        (1 / ((J : ℝ) * (L.spacing : ℝ)) + 1 / (w : ℝ)) := by
  have hstep : (0 : ℝ) < (L.spacing : ℝ) := by
    have := L.two_le_spacing
    exact_mod_cast (by omega : 0 < L.spacing)
  have hJ' : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hw' : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hx : 0 < (J : ℝ) * (L.spacing : ℝ) := mul_pos hJ' hstep
  have hnorm : 0 ≤ observableSupNorm A.toFun := Real.iSup_nonneg fun _ => norm_nonneg _
  have hK : 0 ≤ (tangentLowerConst : ℝ) * (β + t * observableSupNorm A.toFun) *
      ((ϱ : ℕ) : ℝ) ^ 5 := by positivity
  have hsum := half_inv_add_sum_inv_le hx hw'
    (fun i : Fin 3 => (normalFrame L.normal L.normal_mem).lengthSq i.succ)
    (fun i => one_le_normSq ((normalFrame L.normal L.normal_mem).isNormal _))
  have h2 : 2 * (J : ℝ) * (L.spacing : ℝ) = 2 * ((J : ℝ) * (L.spacing : ℝ)) := by ring
  rw [MirrorLadder.SlabZeroGenerator.tangentDefect, h2]
  calc _ ≤ (tangentLowerConst : ℝ) * (β + t * observableSupNorm A.toFun) * ((ϱ : ℕ) : ℝ) ^ 5 *
        (3 * (1 / ((J : ℝ) * (L.spacing : ℝ)) + 1 / (w : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum hK
    _ = _ := by ring
end Numbers
section Ladder
variable {L : MirrorLadder} {w : ℤ} {S : SlabDecomposition}
theorem splits_of_isAdapted (hAd : AdaptedTorusProperties) (hS : L.IsAdaptedSlabDecomposition w S) :
    S.period.SplitsAlongWithHalfPeriod L.normal ((S.count : ℤ) * L.spacing) :=
  ((hAd L.normal L.normal_mem L.spacing S.count w hS.admissible).2.1 hS.three_le S.period
    hS.toAmbient_eq).1
theorem isAdaptedSideTuple_of_isAdapted (hAd : AdaptedTorusProperties)
    (hS : L.IsAdaptedSlabDecomposition w S) :
    IsAdaptedSideTuple L.normal L.normal_mem L.spacing S.count w
      (adaptedSideLengths L.normal L.normal_mem L.spacing S.count w) :=
  ((hAd L.normal L.normal_mem L.spacing S.count w hS.admissible).2.1 hS.three_le S.period
    hS.toAmbient_eq).2.2.1
theorem isBoxShaped_of_isAdapted (hAd : AdaptedTorusProperties)
    (hS : L.IsAdaptedSlabDecomposition w S) :
    S.period.IsBoxShaped (normalFrame L.normal L.normal_mem)
      (adaptedSideLengths L.normal L.normal_mem L.spacing S.count w) :=
  ((hAd L.normal L.normal_mem L.spacing S.count w hS.admissible).2.1 hS.three_le S.period
    hS.toAmbient_eq).2.2.2
theorem periods_le_normalSublattice (hAd : AdaptedTorusProperties)
    (hS : L.IsAdaptedSlabDecomposition w S) : S.period.periods ≤ L.normalSublattice := by
  intro γ hγ
  have h : (γ : AmbientSpace) ∈ S.period.toAmbient := ⟨γ, hγ, rfl⟩
  rw [hS.toAmbient_eq] at h
  exact AddSubgroup.mem_addSubgroupOf.mpr
    ((hAd L.normal L.normal_mem L.spacing S.count w hS.admissible).2.2.2.2.1 h)
theorem normalSublattice_le_axialSublattice (hAd : AdaptedTorusProperties)
    (hS : L.IsAdaptedSlabDecomposition w S) : L.normalSublattice ≤ L.axialSublattice := by
  intro γ hγ
  exact AddSubgroup.mem_addSubgroupOf.mpr
    ((hAd L.normal L.normal_mem L.spacing S.count w hS.admissible).2.2.2.2.2.1
      (AddSubgroup.mem_addSubgroupOf.mp hγ))
theorem axialPeriodDensity_facts (hPer : PeriodLatticeProperties) (L : MirrorLadder) :
    axialPeriodDensity L.normal L.spacing = (L.axialSublattice.index : ℝ)⁻¹ ∧
      0 < axialPeriodDensity L.normal L.spacing ∧
      (L.normalSublattice.index : ℝ) = 2 / axialPeriodDensity L.normal L.spacing := by
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, h9, -, h11, -⟩, ⟨-, -, -, -, -, h6⟩⟩ :=
    hPer.1 L.normal L.normal_mem L.spacing L.even_spacing L.two_le_spacing
  refine ⟨?_, h11, h6⟩
  rw [axialPeriodDensity, if_pos h9]
  rfl
theorem card_axial_cosets {Q : AddSubgroup (LatticePoint 1)} {Γ : PeriodSublattice 1}
    (hQ : Γ.IsFiniteOver Q) {ϰ : ℝ} (hϰ : ϰ = (Q.index : ℝ)⁻¹) {d : ℕ}
    (hd : d = Γ.periods.index) :
    (Nat.card (Q ⧸ Γ.periods.addSubgroupOf Q) : ℝ) = ϰ * (d : ℝ) := by
  have hne : (Q.index : ℝ) ≠ 0 := by
    exact_mod_cast hQ.finiteIndex_of_le.index_ne_zero
  rw [hd, hQ.index_mul, hϰ]
  push_cast
  rw [inv_mul_cancel_left₀ hne]
  rfl
theorem card_normal_cosets {Q : AddSubgroup (LatticePoint 1)} {Γ : PeriodSublattice 1}
    (hQ : Γ.IsFiniteOver Q) {ϰ : ℝ} (hpos : 0 < ϰ) (hϰ : (Q.index : ℝ) = 2 / ϰ) {d : ℕ}
    (hd : d = Γ.periods.index) :
    (Nat.card (Q ⧸ Γ.periods.addSubgroupOf Q) : ℝ) = 1 / 2 * ϰ * (d : ℝ) := by
  rw [hd, hQ.index_mul]
  push_cast
  rw [hϰ]
  have : (Nat.card (Q ⧸ Γ.periods.addSubgroupOf Q) : ℝ) =
      ((Γ.periods.addSubgroupOf Q).index : ℝ) := rfl
  rw [this]
  field_simp
end Ladder
section Folded
variable {L : MirrorLadder} {w : ℤ} {S : SlabDecomposition} (A : L.SlabZeroGenerator)
theorem normalLevelPair_ext {P Q : NormalLevelPair 1} (h1 : P.normal = Q.normal)
    (h2 : P.level = Q.level) : P = Q := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsFoldAndCompactness.normalLevelPair_ext <;> assumption
theorem reflectSym_one_eq (hS : L.IsAdaptedSlabDecomposition w S) :
    S.reflectSym 1 = L.upperWallOfSlabZero.reflectSymmetry := by
  have h : S.levelPair 1 = L.upperWallOfSlabZero := by
    refine normalLevelPair_ext hS.normal_eq ?_
    change S.baseLevel + ((1 : ℤ) : ℝ) * (S.width : ℝ) = L.offset + (L.spacing : ℝ)
    rw [hS.baseLevel_eq, hS.width_eq]
    push_cast
    ring
  exact congrArg NormalLevelPair.reflectSymmetry h
theorem linearReflect_neg_add (n x y : AmbientSpace) :
    linearReflect n (-x + y) = -linearReflect n x + linearReflect n y := by
  simp only [linearReflect_apply, dotProduct_add, dotProduct_neg]
  module
theorem linearReflect_linearReflect {n : AmbientSpace} (hn : n ∈ normalSet) (x : AmbientSpace) :
    linearReflect n (linearReflect n x) = x := by
  have h1 := dotProduct_dualVector hn
  simp only [linearReflect_apply, dotProduct_sub, dotProduct_smul, h1, smul_eq_mul]
  module
theorem periodicSum_pullbackField_shift (𝔸 : LocalObservableArray) {Γ : PeriodSublattice 1}
    {n : AmbientSpace} {z : ℤ} {β : ℝ} (hp : SplitTorusPullbacks) (hβ : 0 < β)
    (hs : Γ.SplitsAlongWithHalfPeriod n z) (hn : n ∈ normalSet)
    (hE : Γ.QuotientLiftFacts) (hQ : Γ.IsFiniteOver 𝔸.sublattice) {v : LatticePoint 1}
    (hv : v ∈ 𝔸.sublattice) (U : Γ.QuotientField) :
    𝔸.periodicSum Γ (Γ.pullbackField (shift v) U) = 𝔸.periodicSum Γ U := by
  let v' : 𝔸.sublattice := ⟨v, hv⟩
  refine periodicSum_pullbackField 𝔸 hp hβ hs hn hE hQ (shift v)
    (fun i => (i.1 + v', i.2))
    (fun i => (periodize_shift_add hp hβ hs hn hE i.1 v (𝔸.gen_mem i.2)).symm)
    (fun i i' h2 h1 => ⟨h2, ?_⟩) U
  simp only [QuotientAddGroup.mk_add] at h1
  exact add_right_cancel h1
theorem periodicSum_pullbackField_reflect (hp : SplitTorusPullbacks)
    (hDesc : SplitTorusDescent) (hFold : FoldedArrayMirrorProperties)
    {Γ : PeriodSublattice 1} {z : ℤ} {β : ℝ} (hβ : 0 < β) (hs : Γ.SplitsAlongWithHalfPeriod L.normal z)
    (hE : Γ.QuotientLiftFacts) (hQ : Γ.IsFiniteOver A.foldedArray.sublattice)
    (U : Γ.QuotientField) :
    A.foldedArray.periodicSum Γ
        (Γ.pullbackField L.upperWallOfSlabZero.reflectSymmetry U) =
      A.foldedArray.periodicSum Γ U := by
  have hn := L.normal_mem
  obtain ⟨-, -, -, -, -, -, ⟨e, he⟩, -⟩ := hFold L A
  obtain ⟨-, -, -, -, -, hlin, -⟩ := hDesc Γ L.normal hn z L.upperWallOfSlabZero.level
    L.upperWallOfSlabZero.allowed 0 hs
  have hr : IsClassIsometry L.normal L.upperWallOfSlabZero.reflectSymmetry.toFun :=
    isClassIsometry_reflectAcross L.upperWallOfSlabZero.allowed
  refine periodicSum_pullbackField A.foldedArray hp hβ hs hn hE hQ _ e (fun i => ?_)
    (fun i i' h2 h1 => ?_) U
  · rw [← periodize_actOn hp hβ hs hn hr (arrayTerm_mem _ i)]
    exact congrArg Γ.periodize (he i).2.2
  · obtain ⟨a1, a2, -⟩ := he i
    obtain ⟨b1, b2, -⟩ := he i'
    refine ⟨Fin.rev_injective (a2.symm.trans (h2.trans b2)), ?_⟩
    have hmem : ((-(e i).1 + (e i').1 : A.foldedArray.sublattice) : LatticePoint 1) ∈ Γ.periods :=
      AddSubgroup.mem_addSubgroupOf.mp (QuotientAddGroup.eq.mp h1)
    have hy : linearReflect L.normal
        (((-i.1 + i'.1 : A.foldedArray.sublattice) : LatticePoint 1) : AmbientSpace) ∈
          Γ.toAmbient := by
      refine ⟨_, hmem, ?_⟩
      simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, AddSubgroup.coe_subtype]
      rw [linearReflect_neg_add, a1, b1]
    have hy' : linearReflect L.normal
        (((-i.1 + i'.1 : A.foldedArray.sublattice) : LatticePoint 1) : AmbientSpace) ∈
          linearReflect L.normal '' (Γ.toAmbient : Set AmbientSpace) := by
      rw [hlin]
      exact hy
    obtain ⟨y, hyΓ, hyeq⟩ := hy'
    have hyy : y = (((-i.1 + i'.1 : A.foldedArray.sublattice) : LatticePoint 1) : AmbientSpace) := by
      have := congrArg (linearReflect L.normal) hyeq
      rwa [linearReflect_linearReflect hn, linearReflect_linearReflect hn] at this
    obtain ⟨γ, hγ, hγe⟩ := hyΓ
    have hγ' : γ = ((-i.1 + i'.1 : A.foldedArray.sublattice) : LatticePoint 1) :=
      Subtype.ext (hγe.trans hyy)
    exact QuotientAddGroup.eq.mpr (AddSubgroup.mem_addSubgroupOf.mpr (hγ' ▸ hγ))
theorem integral_periodize_foldedArray_translate (hp : SplitTorusPullbacks)
    {Γ : PeriodSublattice 1} {z : ℤ}
    {β : ℝ} (hβ : 0 < β) (hs : Γ.SplitsAlongWithHalfPeriod L.normal z)
    (hE : Γ.QuotientLiftFacts) (μ : Measure Γ.QuotientField)
    (hτ : ∀ v ∈ L.normalSublattice,
      PeriodSublattice.PreservesFiniteMeasure (Γ.pullbackField (shift v)) μ)
    (hθ : PeriodSublattice.PreservesFiniteMeasure
      (Γ.pullbackField L.upperWallOfSlabZero.reflectSymmetry) μ)
    (i : A.foldedArray.Label) :
    ∫ U, Γ.periodize (A.foldedArray.translate i) U ∂μ = ∫ U, Γ.periodize A.toFun U ∂μ := by
  have hn := L.normal_mem
  have hA := A.mem_continuousLocal
  have hgen : ∀ ι : Fin 2, ∫ U, Γ.periodize (A.foldedArray.gen ι) U ∂μ =
      ∫ U, Γ.periodize A.toFun U ∂μ := by
    intro ι
    fin_cases ι
    · rfl
    · have hr : IsClassIsometry L.normal
          L.upperWallOfSlabZero.reflectSymmetry.toFun :=
        isClassIsometry_reflectAcross L.upperWallOfSlabZero.allowed
      have h := periodize_actOn hp hβ hs hn hr hA
      have h' : Γ.periodize A.reflected =
          Γ.compPullback L.upperWallOfSlabZero.reflectSymmetry (Γ.periodize A.toFun) :=
        h
      change ∫ U, Γ.periodize A.reflected U ∂μ = _
      rw [h']
      exact hθ.2.2 _ (measurable_periodize hE hA) (exists_norm_bound_periodize Γ hA)
  obtain ⟨u, ι⟩ := i
  have hg := A.foldedArray.gen_mem ι
  have h := periodize_actOn hp hβ hs hn (isClassIsometry_shift L.normal (u : LatticePoint 1)) hg
  have h' : Γ.periodize (A.foldedArray.translate (u, ι)) =
      Γ.compPullback (shift (u : LatticePoint 1))
        (Γ.periodize (A.foldedArray.gen ι)) := h
  rw [h', ← hgen ι]
  exact (hτ u u.2).2.2 _ (measurable_periodize hE hg) (exists_norm_bound_periodize Γ hg)
theorem untiltedTorusPartition_eq (𝔸 𝔸' : LocalObservableArray) (Γ : PeriodSublattice 1) (β : ℝ) :
    𝔸.untiltedTorusPartition Γ β = 𝔸'.untiltedTorusPartition Γ β := by
  simp [LocalObservableArray.untiltedTorusPartition, LocalObservableArray.tiltedPartition,
    LocalObservableArray.tiltedWeight]
end Folded
section Main
variable {L : MirrorLadder} {w : ℤ} {S : SlabDecomposition} (A : L.SlabZeroGenerator)
theorem unfoldedArray_isLowerTangent (hAd : AdaptedTorusProperties)
    (hConst : ConstantTangents.ConstantLowerTangentClaim)
    (hTan : InvariantGibbsLowerTangent.InvariantGibbsLowerTangentClaim) {β : ℝ} (hβ : 0 < β)
    (hS : L.IsAdaptedSlabDecomposition w S) {ϱ : ℕ+} {x : LatticePoint 1}
    (hsupp : LinksLieIn (observableSupport A.toFun)
      ((fun y : LatticePoint 1 => (y : AmbientSpace)) '' siteCube x ϱ))
    (hmin : ((ϱ : ℕ) : ℤ) + 1 < min ((S.count : ℤ) * L.spacing) w)
    (hle : S.period.periods ≤ L.axialSublattice) {ν : Measure (GaugeField 1)}
    (hν : ν ∈ subgroupInvariantGibbsClass one_pos β L.axialSublattice) (t : ℝ) :
    A.unfoldedArray.IsLowerTangent S.period (normalFrame L.normal L.normal_mem)
      (adaptedSideLengths L.normal L.normal_mem L.spacing (S.count : ℤ) w) ϱ A.toFun ν β t := by
  have hrect := isBoxShaped_of_isAdapted hAd hS
  by_cases hc : ∃ c : ℂ, ∀ U, A.toFun U = c
  · obtain ⟨c, hc⟩ := hc
    have hfun : A.toFun = fun _ => ((c.re : ℝ) : ℂ) := by
      funext U
      have him := A.im_eq_zero U
      rw [hc U] at him ⊢
      exact Complex.ext (by simp) (by simpa using him)
    have h := hConst _ _ S.period hrect A.unfoldedArray hle c.re
      ⟨rfl, fun _ => hfun⟩ β hβ t
    have h' := h.2.2.2.2.1 ν ϱ hν.1.1
    rw [← hfun] at h'
    exact h'
  · have hshort : ∀ γ ∈ S.period.periods, γ ≠ 0 → ((ϱ : ℕ) : ℝ) + 1 < ‖(γ : AmbientSpace)‖ := by
      intro γ hγ h0
      have hmem : (γ : AmbientSpace) ∈ S.period.toAmbient := ⟨γ, hγ, rfl⟩
      rw [hS.toAmbient_eq] at hmem
      have h := ((hAd L.normal L.normal_mem L.spacing S.count w hS.admissible).1.2.2.2.2.2.2
        ((ϱ : ℕ) : ℤ) (by exact_mod_cast ϱ.pos) hmin).2 _ hmem
        (fun h => h0 (Subtype.ext h))
      simpa using h
    let d : BoxTorusComparisonData :=
      { obs := A.toFun
        obs_mem := A.mem_continuousLocal
        obs_im := A.im_eq_zero
        obs_nonconst := hc
        boxWidth := ϱ
        obsAnchor := x
        obs_support := hsupp
        normalFrame := normalFrame L.normal L.normal_mem
        sideLengths := adaptedSideLengths L.normal L.normal_mem L.spacing (S.count : ℤ) w
        periodSublattice := S.period
        periodSublattice_isBoxShaped := hrect
        no_short_period := hshort
        translationGroup := L.axialSublattice
        periods_le_translationGroup := hle
        translationGroup_finiteIndex := L.finiteIndex_axialSublattice }
    exact hTan d β hβ ν hν t
theorem holds (hAd : AdaptedTorusProperties) (hBox : FundamentalBox.RepresentsQuotientWithThinShell)
    (hChess : ChessboardFoldingEstimate)
    (hConst : ConstantTangents.ConstantLowerTangentClaim)
    (hDesc : SplitTorusDescent)
    (hExt : PeriodicQuotient.FinitenessClaim)
    (hFin : FiniteTorusPartitionsAndLifts)
    (hFold : FoldedArrayMirrorProperties)
    (hTan : InvariantGibbsLowerTangent.InvariantGibbsLowerTangentClaim)
    (hPer : PeriodLatticeProperties)
    (hPull : SplitTorusPullbacks) : Statement := by
  intro β hβ L A ϱ x hsupp w S hS hmin F s D ϰ e φ μ μ'
  have hs := splits_of_isAdapted hAd hS
  have hn := L.normal_mem
  have hsides : IsAdaptedSideTuple L.normal L.normal_mem L.spacing (S.count : ℤ) w s :=
    isAdaptedSideTuple_of_isAdapted hAd hS
  have hrect : S.period.IsBoxShaped F s := isBoxShaped_of_isAdapted hAd hS
  have hE := hExt.1 S.period
  have hlef := periods_le_normalSublattice hAd hS
  have hleu := hlef.trans (normalSublattice_le_axialSublattice hAd hS)
  have hQf : S.period.IsFiniteOver A.foldedArray.sublattice := (hFin β hβ S.period).1 _ hlef
  have hQu : S.period.IsFiniteOver A.unfoldedArray.sublattice := (hFin β hβ S.period).1 _ hleu
  obtain ⟨hϰ, hϰpos, hϰf⟩ := axialPeriodDensity_facts hPer L
  obtain ⟨hrep, henc, -, -⟩ := hBox F s S.period hrect
  have hncard : D.ncard = S.period.periods.index := by
    change (F.fundamentalBox s).ncard = _
    rw [Set.ncard_def, henc]
    simp
  have hDpos : (0 : ℝ) < (D.ncard : ℝ) := by
    rw [hncard]
    exact_mod_cast Nat.pos_of_ne_zero hE.periods_finiteIndex.index_ne_zero
  have hcardu : (Nat.card (A.unfoldedArray.Cosets S.period) : ℝ) = ϰ * (D.ncard : ℝ) :=
    card_axial_cosets hQu hϰ hncard
  have hcardf : (Nat.card (A.foldedArray.Cosets S.period) : ℝ) = 1 / 2 * ϰ * (D.ncard : ℝ) :=
    card_normal_cosets hQf hϰpos hϰf hncard
  have hZf : ∀ t, 0 < ExpTilt.normalizer S.period.quotientHaar
      (A.foldedArray.periodicSum S.period) (totalEnergy S.period β) t :=
    fun t => ((hFin β hβ S.period).2 A.foldedArray hlef t).1.tiltedPartition_pos
  obtain ⟨a, ha⟩ := exists_abs_bound_periodicSum A.foldedArray hQf
  obtain ⟨b, hb⟩ := exists_abs_bound_totalEnergy hE β
  have hmX := measurable_periodicSum A.foldedArray hE hQf
  have hmP := measurable_totalEnergy hE β
  have hfinH : IsFiniteMeasure S.period.quotientHaar := by
    obtain ⟨-, h, -⟩ := (hPull β hβ S.period L.normal hn _ hs).2.1 (shift 0)
      (isClassIsometry_shift L.normal 0)
    exact h.2.1
  have hc0 : (0 : ℝ) ≤ 1 / (D.ncard : ℝ) := by positivity
  obtain ⟨hconv, hdiff, h0, hφle, hderiv⟩ :=
    ExpTilt.scaledLogRatio_props S.period.quotientHaar hZf hmX hmP ha hb hc0
  have hφ : φ = fun t => 1 / (D.ncard : ℝ) * Real.log (ExpTilt.normalizer S.period.quotientHaar
      (A.foldedArray.periodicSum S.period) (totalEnergy S.period β) t /
      ExpTilt.normalizer S.period.quotientHaar
      (A.foldedArray.periodicSum S.period) (totalEnergy S.period β) 0) := rfl
  rw [← hφ] at hconv hdiff h0 hφle hderiv
  have hμ : ∀ t, μ t = ExpTilt.tilt S.period.quotientHaar
      (A.foldedArray.periodicSum S.period) (totalEnergy S.period β) t := fun _ => rfl
  have hprob : ∀ t, IsProbabilityMeasure (μ t) := fun t => by
    rw [hμ]
    exact ExpTilt.isProbabilityMeasure_tilt S.period.quotientHaar (hZf t) hmX hmP ha hb
  have hderiv' : ∀ t, deriv φ t = 1 / (D.ncard : ℝ) *
      ∫ U, A.foldedArray.periodicSum S.period U ∂(μ t) := by
    intro t
    have hI : ∫ U, A.foldedArray.periodicSum S.period U *
          ExpTilt.density (A.foldedArray.periodicSum S.period)
            (totalEnergy S.period β) t U ∂S.period.quotientHaar =
        ∫ U, ExpTilt.density (A.foldedArray.periodicSum S.period)
            (totalEnergy S.period β) t U • A.foldedArray.periodicSum S.period U
          ∂S.period.quotientHaar :=
      integral_congr_ae (ae_of_all _ fun U => mul_comm _ _)
    rw [hderiv t, hμ, ExpTilt.integral_tilt S.period.quotientHaar (hZf t) hmX hmP,
      smul_eq_mul, hI]
    ring
  have hτ : ∀ t, ∀ v ∈ L.normalSublattice, PeriodSublattice.PreservesFiniteMeasure
      (S.period.pullbackField (shift v)) (μ t) := fun t v hv =>
    preservesFiniteMeasure_tiltedMeasure A.foldedArray hPull hβ hs hn hE hQf (hZf t)
      (isClassIsometry_shift L.normal v)
      (periodicSum_pullbackField_shift A.foldedArray hPull hβ hs hn hE hQf hv)
  have hθ : ∀ t, PeriodSublattice.PreservesFiniteMeasure
      (S.period.pullbackField L.upperWallOfSlabZero.reflectSymmetry) (μ t) :=
    fun t => preservesFiniteMeasure_tiltedMeasure A.foldedArray hPull hβ hs hn hE hQf (hZf t)
      (isClassIsometry_reflectAcross L.upperWallOfSlabZero.allowed)
      (periodicSum_pullbackField_reflect A hPull hDesc hFold hβ hs hE hQf)
  have hθ' : ∀ t, PeriodSublattice.PreservesFiniteMeasure (S.reflectPullback 1) (μ t) := by
    intro t
    have hEq : S.reflectPullback 1 =
        S.period.pullbackField L.upperWallOfSlabZero.reflectSymmetry := by
      funext U
      change S.period.pullbackField (S.reflectSym 1) U = _
      rw [reflectSym_one_eq hS]
    rw [hEq]
    exact hθ t
  have hterm := fun t => integral_periodize_foldedArray_translate A hPull hβ hs hE (μ t) (hτ t) (hθ t)
  have hA := A.mem_continuousLocal
  have hsum : ∀ t, ∫ U, A.foldedArray.periodicSum S.period U ∂(μ t) =
      (Nat.card (A.foldedArray.Cosets S.period) : ℝ) * 2 *
        (∫ U, S.period.periodize A.toFun U ∂(μ t)).re := by
    intro t
    have := hprob t
    have h := integral_periodicSum A.foldedArray hE hQf (μ t) _ (hterm t)
    rw [h]
    rfl
  have hint : ∀ t, Integrable (S.period.periodize A.toFun) (μ t) := by
    intro t
    have := hprob t
    obtain ⟨C, hC⟩ := exists_norm_bound_periodize S.period hA
    exact Integrable.of_bound (measurable_periodize hE hA).aestronglyMeasurable C (ae_of_all _ hC)
  have him : ∀ t, (∫ U, S.period.periodize A.toFun U ∂(μ t)).im = 0 := by
    intro t
    have h := Complex.imCLM.integral_comp_comm (hint t)
    have h' : (∫ U, S.period.periodize A.toFun U ∂(μ t)).im =
        ∫ U, (S.period.periodize A.toFun U).im ∂(μ t) := h.symm
    rw [h']
    have hz : ∀ U, (S.period.periodize A.toFun U).im = 0 := fun U => A.im_eq_zero _
    simp [hz]
  have hderivϰ : ∀ t, deriv φ t =
      ϰ * (∫ U, S.period.periodize A.toFun U ∂(μ t)).re := by
    intro t
    rw [hderiv', hsum, hcardf]
    field_simp
  have hext : ∀ t, ∫ U, S.period.periodize A.toFun U ∂(μ t) =
      stateEval (μ' t) A.toFun := fun t =>
    (((hFin β hβ S.period).2 A.foldedArray hlef t).2.integral_tiltedLift _ hA).symm
  have hlower : ∀ ν ∈ subgroupInvariantGibbsClass one_pos β L.axialSublattice, ∀ t : ℝ, 0 ≤ t →
      t * ϰ * (stateEval ν A.toFun).re - e t ≤
        A.unfoldedArray.logTiltRatioPerSite S.period F s β t := by
    intro ν hν t ht
    have h := unfoldedArray_isLowerTangent A hAd hConst hTan hβ hS hsupp hmin hleu hν t
    have hinv : A.unfoldedArray.invIndex = ϰ := hϰ.symm
    have he : e t = LocalObservableArray.sideDefect s ϱ A.toFun β t :=
      tangentDefect_eq_sideDefect A ϱ β ht S.count w hsides
    rw [he, ← hinv]
    exact h.2.trans h.1
  refine ⟨fun t ht => tangentDefect_le A hβ ht ϱ S.one_le_count ?_, hrep, hncard, hcardu, hcardf,
    hlower, hconv, hdiff, h0, hφle, fun t => ?_, fun t => ⟨hτ t, hθ' t, ?_, ?_, ?_⟩, ?_⟩
  · have := hS.admissible.2.2.2.2
    omega
  · rw [hderiv' t]
  · have hr : IsClassIsometry L.normal
        L.upperWallOfSlabZero.reflectSymmetry.toFun :=
      isClassIsometry_reflectAcross L.upperWallOfSlabZero.allowed
    have h : S.period.periodize A.reflected =
        S.period.compPullback L.upperWallOfSlabZero.reflectSymmetry
          (S.period.periodize A.toFun) :=
      periodize_actOn hPull hβ hs hn hr hA
    rw [h]
    exact (hθ t).2.2 _ (measurable_periodize hE hA) (exists_norm_bound_periodize _ hA)
  · rw [hderivϰ t]
    refine Complex.ext ?_ ?_
    · simp
    · simp [him t]
  · rw [hext t]
  · intro ν hν t ht
    have h1 := hlower ν hν t ht.le
    obtain ⟨-, -, -, -, -, -, -, -, hZZ⟩ := (hChess β hβ L A w S hS).2.2 t ht.le
    have hZu : 0 < A.unfoldedArray.tiltedPartition S.period β t :=
      ((hFin β hβ S.period).2 A.unfoldedArray hleu t).1.tiltedPartition_pos
    have hZ0 : 0 < A.unfoldedArray.untiltedTorusPartition S.period β :=
      ((hFin β hβ S.period).2 A.unfoldedArray hleu 0).1.tiltedPartition_pos
    have h2 : A.unfoldedArray.logTiltRatioPerSite S.period F s β t ≤ φ t := by
      change 1 / (D.ncard : ℝ) * _ ≤
        1 / (D.ncard : ℝ) * Real.log (A.foldedArray.tiltedPartition S.period β t /
          A.foldedArray.untiltedTorusPartition S.period β)
      rw [untiltedTorusPartition_eq A.foldedArray A.unfoldedArray]
      refine mul_le_mul_of_nonneg_left ?_ hc0
      exact Real.log_le_log (div_pos hZu hZ0) (div_le_div_of_nonneg_right hZZ hZ0.le)
    have h3 := hφle t
    rw [hderivϰ t] at h3
    have hre : (stateEval (μ' t) A.toFun).re =
        (∫ U, S.period.periodize A.toFun U ∂(μ t)).re := by rw [hext t]
    rw [hre]
    have hpos : 0 < t * ϰ := mul_pos ht hϰpos
    have h4 : t * ϰ * (stateEval ν A.toFun).re ≤
        t * ϰ * (∫ U, S.period.periodize A.toFun U ∂(μ t)).re + e t := by
      nlinarith
    have h5 : (∫ U, S.period.periodize A.toFun U ∂(μ t)).re + e t / (t * ϰ) =
        (t * ϰ * (∫ U, S.period.periodize A.toFun U ∂(μ t)).re + e t) / (t * ϰ) := by
      rw [add_div, mul_div_cancel_left₀ _ hpos.ne']
    rw [h5, le_div_iff₀ hpos]
    linarith
end Main
end FiniteVolumeTangentBounds
end YangMills.Construction.NormalFamilies
