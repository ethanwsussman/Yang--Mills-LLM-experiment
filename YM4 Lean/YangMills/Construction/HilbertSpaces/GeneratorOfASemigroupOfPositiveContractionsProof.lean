import YangMills.Construction.HilbertSpaces.EnergyMomentumMeasureOfACommutingRepresentationProof
import YangMills.Construction.HilbertSpaces.GeneratorOfASemigroupOfPositiveContractions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexOrder InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.PositiveContractionGenerator
open YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (TendstoStrongly IsContractive IsOrthProjOnto IsPositiveBounded
  IsNonneg IsSelfAdj IsC0Semigroup ker ofCLM)
open YangMills.Construction.SpectralTheory (UnboundedOp)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem mem_domain_ofCLM (S : H →L[ℂ] H) (ψ : H) : ψ ∈ (ofCLM S).domain :=
  Submodule.mem_top
theorem apply_congr_of_eq {A A' : UnboundedOp H} (h : A = A') (x : H) (hx : x ∈ A.domain)
    (hx' : x ∈ A'.domain) : A ⟨x, hx⟩ = A' ⟨x, hx'⟩ := by
  subst h
  rfl
theorem ofCLM_injective {S S' : H →L[ℂ] H} (h : ofCLM S = ofCLM S') : S = S' :=
  ContinuousLinearMap.ext fun ψ =>
    apply_congr_of_eq h ψ (mem_domain_ofCLM S ψ) (mem_domain_ofCLM S' ψ)
theorem inner_map_symm_of_isSelfAdj {S : H →L[ℂ] H} (h : IsSelfAdj (ofCLM S)) (φ ψ : H) :
    ⟪φ, S ψ⟫_ℂ = ⟪S φ, ψ⟫_ℂ := by
  obtain ⟨hd, ha⟩ := h
  have hφ : φ ∈ (YangMills.Construction.FormsOperators.adj (ofCLM S) hd).domain := by
    rw [ha]
    exact mem_domain_ofCLM S φ
  have h₁ := YangMills.Construction.FormsOperators.adj_spec (ofCLM S) hd ⟨φ, hφ⟩
    ⟨ψ, mem_domain_ofCLM S ψ⟩
  rw [apply_congr_of_eq ha φ hφ (mem_domain_ofCLM S φ)] at h₁
  exact h₁
section Maps
variable {d : ℕ} {E E' : BorelSubset d → H →L[ℂ] H} {f f' : Space d → ℂ} {A A' : UnboundedOp H}
theorem eq_of_isSpectralIntegralOp (h : IsSpectralIntegralOp A E f)
    (h' : IsSpectralIntegralOp A' E f) : A = A' := by
  obtain ⟨hd, hv⟩ := h
  obtain ⟨hd', hv'⟩ := h'
  exact LinearPMap.ext (SetLike.coe_injective (hd.trans hd'.symm)) fun x hx hy =>
    (hv ⟨x, hx⟩).trans (hv' ⟨x, hy⟩).symm
theorem isSpectralIntegralOp_of_isOp (h : RealizesSpectralIntegral E f A) :
    IsSpectralIntegralOp A E f := by
  refine ⟨h.1, fun χ => ?_⟩
  obtain ⟨_, hv⟩ := h.2 χ
  exact hv.symm
theorem isSpectralIntegralOp_ofCLM {B : H →L[ℂ] H} (h : SpectralIntegralIs E f B) :
    IsSpectralIntegralOp (ofCLM B) E f := by apply _root_.YangMills.Construction.PositiveFormReconstruction.CommutingJointSpectrum.isSpectralIntegralOp_ofCLM <;> assumption
theorem isSpectralIntegralOp_of_partialMapEq
    (h : PartialMapEq (spectralIntegral E f) (spectralIntegral E' f'))
    (hA : IsSpectralIntegralOp A E' f') : IsSpectralIntegralOp A E f := by
  obtain ⟨hS, hv⟩ := h
  obtain ⟨hd, hw⟩ := hA
  exact ⟨hd.trans hS.symm, fun χ => (hw χ).trans (hv ⟨χ, (hd.trans hS.symm) ▸ χ.2⟩)⟩
end Maps
omit [CompleteSpace H] in
theorem orthoProjection_eq_of_range_eq {P Q : H →L[ℂ] H} (hP : IsOrthoProjection P)
    (hQ : IsOrthoProjection Q) (h : range P = range Q) : P = Q := by
  have fix : ∀ {R : H →L[ℂ] H}, IsOrthoProjection R → ∀ x ∈ range R, R x = x := by
    rintro R hR _ ⟨z, rfl⟩
    exact congrArg (fun T : H →L[ℂ] H => T z) hR.1
  have hQP : ∀ ψ, Q (P ψ) = P ψ := fun ψ => fix hQ _ (h ▸ mem_range_self ψ)
  have hPQ : ∀ ψ, P (Q ψ) = Q ψ := fun ψ => fix hP _ (h ▸ mem_range_self ψ)
  refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
  rw [← hQP ψ, hQ.2 φ, hP.2 (Q φ) ψ, hPQ φ, hQ.2 φ ψ]
theorem measurable_firstCoord : Measurable fun y : Space 1 => y 0 := by
  fun_prop
def negLogReal (x : ℝ) : ℝ := if 0 < x then -Real.log x else 0
theorem measurable_negLogReal : Measurable negLogReal :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id) Real.measurable_log.neg
    measurable_const
def negLogFn : Space 1 → ℂ := zeroExtend openPosRay negLogOnPosRay
theorem negLogFn_apply (y : Space 1) : negLogFn y = ((negLogReal (y 0) : ℝ) : ℂ) := by
  unfold negLogFn zeroExtend negLogReal negLogOnPosRay
  by_cases h : 0 < y 0
  · have h' : y ∈ openPosRay.1 := h
    rw [dif_pos h', if_pos h]
  · have h' : y ∉ openPosRay.1 := h
    rw [dif_neg h', if_neg h]
    simp
theorem measurable_negLogFn : Measurable negLogFn := by
  have : negLogFn = fun y => ((negLogReal (y 0) : ℝ) : ℂ) := funext negLogFn_apply
  rw [this]
  exact Complex.measurable_ofReal.comp (measurable_negLogReal.comp measurable_firstCoord)
def unitIoc : BorelSubset 1 :=
  ⟨{y | y 0 ∈ Ioc (0 : ℝ) 1}, measurable_firstCoord measurableSet_Ioc⟩
theorem negLogReal_nonneg {y : Space 1} (hy : y ∈ unitIoc.1) : 0 ≤ negLogReal (y 0) := by
  have h : 0 < y 0 ∧ y 0 ≤ 1 := hy
  unfold negLogReal
  rw [if_pos h.1]
  exact neg_nonneg.mpr (Real.log_nonpos h.1.le h.2)
def powReal (t : ℝ≥0) (y : Space 1) : ℝ :=
  unitIoc.1.indicator (fun y => Real.exp (-(t : ℝ) * negLogReal (y 0))) y
def powFn (t : ℝ≥0) (y : Space 1) : ℂ := ((powReal t y : ℝ) : ℂ)
theorem powReal_of_mem (t : ℝ≥0) {y : Space 1} (hy : y ∈ unitIoc.1) :
    powReal t y = Real.exp (-(t : ℝ) * negLogReal (y 0)) :=
  Set.indicator_of_mem hy _
theorem powReal_of_notMem (t : ℝ≥0) {y : Space 1} (hy : y ∉ unitIoc.1) :
    powReal t y = 0 := by
  simp [powReal, hy]
theorem measurable_powFn (t : ℝ≥0) : Measurable (powFn t) := by
  refine Complex.measurable_ofReal.comp (Measurable.indicator ?_ unitIoc.2)
  exact Real.measurable_exp.comp
    (measurable_const.mul (measurable_negLogReal.comp measurable_firstCoord))
theorem powReal_nonneg (t : ℝ≥0) (y : Space 1) : 0 ≤ powReal t y := by
  by_cases hy : y ∈ unitIoc.1
  · rw [powReal_of_mem t hy]
    exact (Real.exp_pos _).le
  · rw [powReal_of_notMem t hy]
theorem powReal_le_one (t : ℝ≥0) (y : Space 1) : powReal t y ≤ 1 := by
  by_cases hy : y ∈ unitIoc.1
  · rw [powReal_of_mem t hy, Real.exp_le_one_iff]
    have := mul_nonneg t.2 (negLogReal_nonneg hy)
    simp only [NNReal.val_eq_coe] at this
    linarith
  · rw [powReal_of_notMem t hy]
    exact zero_le_one
theorem norm_powFn_le (t : ℝ≥0) (y : Space 1) : ‖powFn t y‖ ≤ 1 := by
  unfold powFn
  rw [Complex.norm_real, Real.norm_of_nonneg (powReal_nonneg t y)]
  exact powReal_le_one t y
theorem isBoundedMeasurable_powFn (t : ℝ≥0) : IsBoundedMeasurableFn (powFn t) :=
  ⟨measurable_powFn t, 1, norm_powFn_le t⟩
theorem powFn_add (s t : ℝ≥0) : powFn (s + t) = fun y => powFn s y * powFn t y := by
  funext y
  unfold powFn
  by_cases hy : y ∈ unitIoc.1
  · rw [powReal_of_mem _ hy, powReal_of_mem _ hy, powReal_of_mem _ hy, ← Complex.ofReal_mul,
      ← Real.exp_add]
    congr 2
    push_cast
    ring
  · rw [powReal_of_notMem _ hy, powReal_of_notMem _ hy, powReal_of_notMem _ hy]
    simp
theorem powFn_one {y : Space 1} (hy : y ∈ unitIoc.1) : powFn 1 y = lineCoord y := by
  have h : 0 < y 0 ∧ y 0 ≤ 1 := hy
  unfold powFn
  rw [powReal_of_mem _ hy]
  unfold negLogReal
  rw [if_pos h.1]
  simp [Real.exp_log h.1, lineCoord, coordFn]
theorem tendsto_powFn {τ : ℕ → ℝ≥0} {t : ℝ≥0} (h : Tendsto τ atTop (𝓝 t)) (y : Space 1) :
    Tendsto (fun j => powFn (τ j) y) atTop (𝓝 (powFn t y)) := by
  by_cases hy : y ∈ unitIoc.1
  · have hc : Continuous fun s : ℝ≥0 => ((Real.exp (-(s : ℝ) * negLogReal (y 0)) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (NNReal.continuous_coe.neg.mul continuous_const))
    have := (hc.tendsto t).comp h
    simpa only [powFn, powReal_of_mem _ hy, Function.comp_def] using this
  · simp only [powFn, powReal_of_notMem _ hy]
    exact tendsto_const_nhds
def negLogZeroLocus : BorelSubset 1 := zeroLocus measurable_negLogFn
def negLogZeroIndicator : Space 1 → ℂ := negLogZeroLocus.1.indicator fun _ => (1 : ℂ)
theorem isBoundedMeasurable_negLogZeroIndicator : IsBoundedMeasurableFn negLogZeroIndicator := by
  refine ⟨measurable_const.indicator negLogZeroLocus.2, 1, fun y => ?_⟩
  unfold negLogZeroIndicator
  by_cases h : y ∈ negLogZeroLocus.1 <;> simp [h]
theorem tendsto_powFn_atTop {τ : ℕ → ℝ≥0} (h : Tendsto τ atTop atTop) {y : Space 1}
    (hy : y ∈ unitIoc.1) : Tendsto (fun j => powFn (τ j) y) atTop (𝓝 (negLogZeroIndicator y)) := by
  have hl := negLogReal_nonneg hy
  rcases hl.eq_or_lt with h0 | h0
  · have hz : y ∈ negLogZeroLocus.1 := by
      show negLogFn y = 0
      rw [negLogFn_apply, ← h0]
      simp
    have hone : ∀ j, powFn (τ j) y = 1 := fun j => by
      unfold powFn
      rw [powReal_of_mem _ hy, ← h0]
      simp
    simp only [hone, negLogZeroIndicator, Set.indicator_of_mem hz]
    exact tendsto_const_nhds
  · have hz : y ∉ negLogZeroLocus.1 := by
      intro hz
      have : negLogFn y = 0 := hz
      rw [negLogFn_apply] at this
      exact h0.ne' (by exact_mod_cast this)
    have hτ : Tendsto (fun j => ((τ j : ℝ≥0) : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.mpr h
    have h₁ : Tendsto (fun j => -(τ j : ℝ) * negLogReal (y 0)) atTop atBot := by
      have := tendsto_neg_atTop_atBot.comp (hτ.atTop_mul_const h0)
      simpa only [Function.comp_def, neg_mul] using this
    have h₂ := Real.tendsto_exp_atBot.comp h₁
    have h₃ := (Complex.continuous_ofReal.tendsto 0).comp h₂
    simpa only [powFn, powReal_of_mem _ hy, negLogZeroIndicator, Set.indicator_of_notMem hz,
      Function.comp_def, Complex.ofReal_zero] using h₃
section Calculus
variable (hC : FunctionalCalculus.Statement) (hI : BoundedBorelCalculusTheorem)
  {E : BorelSubset 1 → H →L[ℂ] H} (hE : IsPVM E) (hN : E unitIocᶜ = 0)
include hI hE in
theorem spectralIntegralIs_boundedCalculus {f : Space 1 → ℂ} (hf : IsBoundedMeasurableFn f) :
    SpectralIntegralIs E f (boundedCalculus E f) := by
  have hT := (hI 1 le_rfl H E hE).2.2.2.2.2
  exact ⟨(hT.2 f hf).1, fun ψ => spectralIntegral_eq_boundedCalculus hT hf ψ⟩
include hC hE in
theorem isSpectralIntegralOp_spectralOp {f : Space 1 → ℂ} (hf : Measurable f) :
    IsSpectralIntegralOp (spectralOp E f) E f :=
  isSpectralIntegralOp_of_isOp (hC 1 1 H E hE f f hf hf 0).1.isOp
include hC hI hE in
theorem spectralOp_eq_ofCLM {f : Space 1 → ℂ} (hf : IsBoundedMeasurableFn f) :
    spectralOp E f = ofCLM (boundedCalculus E f) :=
  eq_of_isSpectralIntegralOp (isSpectralIntegralOp_spectralOp hC hE hf.1)
    (isSpectralIntegralOp_ofCLM (spectralIntegralIs_boundedCalculus hI hE hf))
include hN in
theorem holdsOffNull_of_unitIoc {p : Space 1 → Prop} (h : ∀ y ∈ unitIoc.1, p y) :
    HoldsOffNull E p :=
  ⟨unitIocᶜ, hN, fun y hy => h y (by simpa using hy)⟩
include hC hI hE hN in
theorem spectralOp_congr {f g : Space 1 → ℂ} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ y ∈ unitIoc.1, f y = g y) : spectralOp E f = spectralOp E g := by
  refine (hC 1 1 H E hE f g hf hg 0).2.2.2.2.1.eq_of_null ?_
  refine (hI 1 le_rfl H E hE).2.1.2.1 unitIocᶜ _ (fun y hy hc => hy (h y ?_)) hN
  simpa using hc
include hC hI hE hN in
theorem tendsto_boundedCalculus_apply {fs : ℕ → Space 1 → ℂ} {f : Space 1 → ℂ}
    (hfs : ∀ j, IsBoundedMeasurableFn (fs j)) (hf : IsBoundedMeasurableFn f)
    (hb : ∀ j y, ‖fs j y‖ ≤ 1) (hl : ∀ y ∈ unitIoc.1, Tendsto (fun j => fs j y) atTop (𝓝 (f y)))
    (ψ : H) : Tendsto (fun j => boundedCalculus E (fs j) ψ) atTop (𝓝 (boundedCalculus E f ψ)) := by
  have hT := (hI 1 le_rfl H E hE).2.2.2.2.2
  obtain ⟨h, hs, ht⟩ := (hC 1 1 H E hE f f hf.1 hf.1 0).2.2.2.2.2.2.1 fs 1 (fun j => (hfs j).1)
    zero_le_one (holdsOffNull_of_unitIoc hN fun y hy => ⟨fun j => hb j y, hl y hy⟩) ψ
  rw [spectralIntegral_eq_boundedCalculus hT hf] at ht
  simpa only [spectralIntegral_eq_boundedCalculus hT (hfs _)] using ht
include hI hE in
theorem boundedCalculus_powFn_add (s t : ℝ≥0) :
    boundedCalculus E (powFn (s + t)) = boundedCalculus E (powFn s) * boundedCalculus E (powFn t) := by
  rw [powFn_add]
  exact (((hI 1 le_rfl H E hE).2.2.2.2.1.1 _ _ 0 (isBoundedMeasurable_powFn s)
    (isBoundedMeasurable_powFn t))).2
include hC hI hE in
theorem isSelfAdj_powFn (t : ℝ≥0) :
    IsSelfAdj (ofCLM (boundedCalculus E (powFn t))) := by
  rw [← spectralOp_eq_ofCLM hC hI hE (isBoundedMeasurable_powFn t)]
  exact (hC 1 1 H E hE _ _ (measurable_powFn t) (measurable_powFn t) 0).2.2.1.2
    fun y => Complex.ofReal_im _
include hC hI hE hN in
theorem isPositiveBounded_powFn (t : ℝ≥0) : IsPositiveBounded (boundedCalculus E (powFn t)) := by
  intro ψ
  have hT := (hI 1 le_rfl H E hE).2.2.2.2.2
  have hb := isBoundedMeasurable_powFn t
  have h := (hC 1 1 H E hE _ _ hb.1 hb.1 0).2.2.2.2.1.nonneg
    (holdsOffNull_of_unitIoc hN fun y _ => Complex.zero_le_real.mpr (powReal_nonneg t y))
    ⟨ψ, by rw [(hT.2 _ hb).1]; trivial⟩
  rwa [spectralIntegral_eq_boundedCalculus hT hb] at h
end Calculus
section Semigroup
variable {B : ℝ≥0 → H →L[ℂ] H}
theorem sqrt_unique (hR : SpectralRules.AllRules) {T S S' : H →L[ℂ] H}
    (hT : IsSelfAdj (ofCLM T)) (hTp : IsPositiveBounded T)
    (hS : IsSelfAdj (ofCLM S)) (hSp : IsPositiveBounded S) (hSS : S * S = T)
    (hS' : IsSelfAdj (ofCLM S')) (hSp' : IsPositiveBounded S')
    (hSS' : S' * S' = T) : S = S' :=
  ofCLM_injective (eq_of_isSpectralIntegralOp
    ((hR H).2.2.2.2 T S hT hTp hS hSp hSS) ((hR H).2.2.2.2 T S' hT hTp hS' hSp' hSS'))
theorem half_pow_succ_add_self (k : ℕ) :
    (1 / 2 : ℝ≥0) ^ (k + 1) + (1 / 2 : ℝ≥0) ^ (k + 1) = (1 / 2 : ℝ≥0) ^ k := by
  rw [pow_succ, ← mul_add, add_halves, mul_one]
theorem tendsto_half_pow_zero : Tendsto (fun k : ℕ => (1 / 2 : ℝ≥0) ^ k) atTop (𝓝 0) :=
  NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.half_lt_self one_ne_zero)
theorem eq_zero_of_semigroup_apply_eq_zero (hB : IsC0Semigroup B)
    (hsa : ∀ t, IsSelfAdj (ofCLM (B t))) (t : ℝ≥0) {ψ : H} (h : B t ψ = 0) :
    ψ = 0 := by
  have step : ∀ k : ℕ, B (t * (1 / 2 : ℝ≥0) ^ k) ψ = 0 := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have hss : t * (1 / 2 : ℝ≥0) ^ (k + 1) + t * (1 / 2 : ℝ≥0) ^ (k + 1) =
          t * (1 / 2 : ℝ≥0) ^ k := by
        rw [← mul_add, half_pow_succ_add_self]
      generalize t * (1 / 2 : ℝ≥0) ^ (k + 1) = s at hss
      have h₁ : B s (B s ψ) = 0 := by
        have : B s (B s ψ) = (B s * B s) ψ := rfl
        rw [this, hB.map_add, hss, ih]
      have h₂ : ⟪B s ψ, B s ψ⟫_ℂ = 0 := by
        rw [← inner_map_symm_of_isSelfAdj (hsa s) ψ (B s ψ), h₁, inner_zero_right]
      exact inner_self_eq_zero.mp h₂
  have hl : Tendsto (fun k : ℕ => t * (1 / 2 : ℝ≥0) ^ k) atTop (𝓝 0) := by
    simpa using tendsto_half_pow_zero.const_mul t
  have hc := ((hB.continuous_apply ψ).tendsto 0).comp hl
  have hz : B 0 ψ = 0 := by
    refine tendsto_nhds_unique hc ?_
    simp only [Function.comp_def, step]
    exact tendsto_const_nhds
  rw [hB.map_zero] at hz
  simpa using hz
theorem semigroup_eq_boundedCalculus_powFn (hC : FunctionalCalculus.Statement)
    (hI : BoundedBorelCalculusTheorem) (hR : SpectralRules.AllRules)
    {E : BorelSubset 1 → H →L[ℂ] H} (hE : IsPVM E) (hN : E unitIocᶜ = 0)
    (hB : IsC0Semigroup B)
    (hsa : ∀ t, IsSelfAdj (ofCLM (B t))) (hpos : ∀ t, IsPositiveBounded (B t))
    (hone : B 1 = boundedCalculus E (powFn 1)) (t : ℝ≥0) :
    B t = boundedCalculus E (powFn t) := by
  have hd : ∀ k : ℕ, B ((1 / 2 : ℝ≥0) ^ k) = boundedCalculus E (powFn ((1 / 2 : ℝ≥0) ^ k)) := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih =>
      refine sqrt_unique hR (T := B ((1 / 2 : ℝ≥0) ^ k)) (hsa _) (hpos _) (hsa _) (hpos _) ?_
        (isSelfAdj_powFn hC hI hE _) (isPositiveBounded_powFn hC hI hE hN _) ?_
      · rw [hB.map_add, half_pow_succ_add_self]
      · rw [← boundedCalculus_powFn_add hI hE, half_pow_succ_add_self, ih]
  have hm : ∀ (k m : ℕ), B (((m + 1 : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ k) =
      boundedCalculus E (powFn (((m + 1 : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ k)) := by
    intro k m
    induction m with
    | zero => simpa using hd k
    | succ m ih =>
      have e : ((m + 1 + 1 : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ k =
          ((m + 1 : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ k + (1 / 2 : ℝ≥0) ^ k := by
        push_cast
        ring
      rw [e, ← hB.map_add, boundedCalculus_powFn_add hI hE, ih, hd]
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ → ℝ≥0, ∀ j, τ j =
      ((⌊t / (1 / 2 : ℝ≥0) ^ j⌋₊ + 1 : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ j := ⟨_, fun _ => rfl⟩
  have hpos' : ∀ j : ℕ, (0 : ℝ≥0) < (1 / 2 : ℝ≥0) ^ j := fun j => by positivity
  have lo : ∀ j, t ≤ τ j := fun j => by
    have h₁ := Nat.lt_floor_add_one (t / (1 / 2 : ℝ≥0) ^ j)
    have h₂ := (div_lt_iff₀ (hpos' j)).mp h₁
    rw [hτ]
    push_cast
    exact h₂.le
  have hi : ∀ j, τ j ≤ t + (1 / 2 : ℝ≥0) ^ j := fun j => by
    have h₁ := Nat.floor_le (a := t / (1 / 2 : ℝ≥0) ^ j) zero_le
    have h₂ := (le_div_iff₀ (hpos' j)).mp h₁
    rw [hτ]
    push_cast
    rw [add_mul, one_mul]
    exact add_le_add_left h₂ _
  have hlim : Tendsto (fun j : ℕ => t + (1 / 2 : ℝ≥0) ^ j) atTop (𝓝 t) := by
    simpa using tendsto_half_pow_zero.const_add t
  have hτt : Tendsto τ atTop (𝓝 t) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim lo hi
  refine ContinuousLinearMap.ext fun ψ => ?_
  have h₁ := ((hB.continuous_apply ψ).tendsto t).comp hτt
  have h₂ := tendsto_boundedCalculus_apply hC hI hE hN (fs := fun j => powFn (τ j)) (f := powFn t)
    (fun j => isBoundedMeasurable_powFn _) (isBoundedMeasurable_powFn t)
    (fun j y => norm_powFn_le _ y) (fun y _ => tendsto_powFn hτt y) ψ
  refine tendsto_nhds_unique h₁ (Tendsto.congr (fun j => ?_) h₂)
  simp only [Function.comp_def]
  rw [hτ, hm]
end Semigroup
theorem statement_holds (hS : SelfAdjoint.SpectralTheorem) (hR : SpectralRules.AllRules)
    (hC : FunctionalCalculus.Statement) (hI : BoundedBorelCalculusTheorem) :
    Statement := by
  intro H _ _ _ B hB hP
  have hsa := fun t => (hP t).2.1
  have hpos := fun t => (hP t).1
  have hker : ∀ t, ker (ofCLM (B t)) = {0} := by
    intro t
    ext ψ
    constructor
    · rintro ⟨hψ, hv⟩
      exact eq_zero_of_semigroup_apply_eq_zero hB hsa t hv
    · intro hψ
      rw [mem_singleton_iff.mp hψ]
      exact ⟨mem_domain_ofCLM _ 0, map_zero _⟩
  set E := spectralResolution (ofCLM (B 1)) with hEdef
  have hspec : IsSpectralResolution (ofCLM (B 1)) E := (hS H _ (hsa 1)).2.2.2.2.2.2.2.2.1
  have hE := hspec.1
  have hlin : Measurable lineCoord :=
    Complex.measurable_ofReal.comp measurable_firstCoord
  have hasO : spectralOp E lineCoord = ofCLM (B 1) :=
    eq_of_isSpectralIntegralOp (isSpectralIntegralOp_spectralOp hC hE hlin) hspec.2
  have hzero : E (zeroLocus hlin) = 0 := by
    have hk : ker (spectralOp E lineCoord) = range (E (zeroLocus hlin)) :=
      (hC 1 1 H E hE _ _ hlin hlin 0).2.2.2.2.2.1
    rw [hasO, hker 1] at hk
    refine ContinuousLinearMap.ext fun ψ => ?_
    have : E (zeroLocus hlin) ψ ∈ ({0} : Set H) := hk ▸ mem_range_self ψ
    simpa using this
  have hseg : IsSupportedOnPVM E unitIntervalSet :=
    (hR H).1.2.2 (B 1) (hsa 1) (hpos 1) (hP 1).2.2
  have hN : E unitIocᶜ = 0 := by
    refine (hI 1 le_rfl H E hE).2.1.2.2 {unitIntervalSetᶜ, zeroLocus hlin} unitIocᶜ
      ((countable_singleton _).insert _) ?_ ?_
    · rintro Δ (rfl | h)
      · exact hseg
      · rw [mem_singleton_iff.mp h]
        exact hzero
    · rw [Set.biUnion_insert, Set.biUnion_singleton]
      ext y
      change ¬ (y 0 ∈ Ioc (0 : ℝ) 1) ↔ (¬ (y 0 ∈ Icc (0 : ℝ) 1)) ∨ lineCoord y = 0
      have e : lineCoord y = 0 ↔ y 0 = 0 := by
        simp [lineCoord, coordFn]
      rw [e]
      by_cases h0 : y 0 = 0
      · simp [h0]
      · have e' : 0 < y 0 ↔ 0 ≤ y 0 :=
          ⟨le_of_lt, fun h => lt_of_le_of_ne h (Ne.symm h0)⟩
        simp [h0, e']
  have hone : B 1 = boundedCalculus E (powFn 1) := by
    apply ofCLM_injective
    rw [← spectralOp_eq_ofCLM hC hI hE (isBoundedMeasurable_powFn 1), ← hasO]
    exact spectralOp_congr hC hI hE hN hlin (measurable_powFn 1)
      fun y hy => (powFn_one hy).symm
  have hBC := semigroup_eq_boundedCalculus_powFn hC hI hR hE hN hB hsa hpos hone
  have hL := measurable_negLogFn
  have hf : Measurable fun y : Space 1 => negLogReal (y 0) :=
    measurable_negLogReal.comp measurable_firstCoord
  obtain ⟨A, hAint, hAsa, -, hAh⟩ := (hR H).2.1 1 le_rfl E hE _ hf
  have hAL : IsSpectralIntegralOp A E negLogFn := by
    rwa [show negLogFn = fun y => ((negLogReal (y 0) : ℝ) : ℂ) from funext negLogFn_apply]
  have hgen : IsSemigroupGenerator B A := by
    refine ⟨hAsa, ?_, fun t => ?_⟩
    · intro χ
      obtain ⟨hd, hv⟩ := hAL
      rw [hv χ]
      exact (hC 1 1 H E hE _ _ hL hL 0).2.2.2.2.1.nonneg
        (holdsOffNull_of_unitIoc hN fun y hy => by
          rw [negLogFn_apply]
          exact Complex.zero_le_real.mpr (negLogReal_nonneg hy)) ⟨χ, hd ▸ χ.2⟩
    · have hh : Measurable fun x : ℝ => Complex.exp (-((t : ℝ) : ℂ) * (x : ℂ)) :=
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).measurable
      obtain ⟨hS', hv⟩ := hAh _ hh
      have hg : Measurable fun y : Space 1 =>
          Complex.exp (-((t : ℝ) : ℂ) * ((negLogReal (y 0) : ℝ) : ℂ)) := hh.comp hf
      have hcong := spectralOp_congr hC hI hE hN hg (measurable_powFn t) (fun y hy => by
        unfold powFn
        rw [powReal_of_mem t hy]
        push_cast
        rfl)
      have hI₁ := isSpectralIntegralOp_spectralOp hC hE hg
      rw [hcong, spectralOp_eq_ofCLM hC hI hE (isBoundedMeasurable_powFn t), ← hBC t] at hI₁
      obtain ⟨hd₁, hv₁⟩ := hI₁
      refine ⟨hS'.trans hd₁.symm, fun ψ => ?_⟩
      exact (hv ψ).symm.trans (hv₁ ⟨ψ.1, mem_domain_ofCLM _ _⟩).symm
  have hlog : ∀ A', IsSemigroupGenerator B A' → IsSpectralIntegralOp A' E negLogFn := by
    intro A' hA'
    obtain ⟨hsa', -, hexp⟩ := hA'
    have hspec' : IsSpectralResolution A' (spectralResolution A') :=
      (hS H _ hsa').2.2.2.2.2.2.2.2.1
    have hφ : Measurable fun y : Space 1 => Real.exp (-(y 0)) :=
      Real.measurable_exp.comp measurable_firstCoord.neg
    obtain ⟨Cc, hCint, -, -, hCh⟩ := (hR H).2.1 1 le_rfl (spectralResolution A') hspec'.1 _ hφ
    have hCB : Cc = ofCLM (B 1) := by
      obtain ⟨hd, hv⟩ := hexp 1
      have e : liftFromLine (fun x : ℝ => Complex.exp (-(((1 : ℝ≥0) : ℝ) : ℂ) * (x : ℂ))) =
          fun y : Space 1 => ((Real.exp (-(y 0)) : ℝ) : ℂ) := by
        funext y
        simp [liftFromLine]
      have hI₂ : SpectralIntegralIs (spectralResolution A')
          (liftFromLine fun x : ℝ => Complex.exp (-(((1 : ℝ≥0) : ℝ) : ℂ) * (x : ℂ))) (B 1) :=
        ⟨hd, hv⟩
      rw [e] at hI₂
      exact eq_of_isSpectralIntegralOp hCint (isSpectralIntegralOp_ofCLM hI₂)
    subst hCB
    have hm : Measurable fun x : ℝ => ((negLogReal x : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp measurable_negLogReal
    have hmaps := hCh _ hm
    have e₁ : liftFromLine (fun x : ℝ => ((negLogReal x : ℝ) : ℂ)) = negLogFn :=
      funext fun y => (negLogFn_apply y).symm
    have e₂ : (fun y : Space 1 => ((negLogReal (Real.exp (-(y 0))) : ℝ) : ℂ)) =
        lineCoord := by
      funext y
      simp [negLogReal, Real.exp_pos, lineCoord, coordFn]
    unfold borelCalculus at hmaps
    rw [e₁, e₂] at hmaps
    exact isSpectralIntegralOp_of_partialMapEq hmaps hspec'.2
  have huniq : ∀ A', IsSemigroupGenerator B A' → A' = A := fun A' h =>
    eq_of_isSpectralIntegralOp (hlog A' h) hAL
  have hgenA : semigroupGenerator B = A := huniq _ (Classical.epsilon_spec ⟨A, hgen⟩)
  have hcar : IsSupportedOnPVM E openPosRay :=
    (hI 1 le_rfl H E hE).2.1.2.1 unitIocᶜ _ (fun y hy hc => hy hc.1) hN
  have hkerA : ker A = range (E negLogZeroLocus) := by
    have hk : ker (spectralOp E negLogFn) = range (E (zeroLocus hL)) :=
      (hC 1 1 H E hE _ _ hL hL 0).2.2.2.2.2.1
    rwa [eq_of_isSpectralIntegralOp (isSpectralIntegralOp_spectralOp hC hE hL) hAL]
      at hk
  have hPproj : IsOrthProjOnto (E negLogZeroLocus) (ker A) :=
    ⟨hE.isOrthoProjection _, hkerA.symm⟩
  have hproj : kerProjection A = E negLogZeroLocus := by
    have hsp : IsOrthProjOnto (kerProjection A) (ker A) :=
      Classical.epsilon_spec (p := fun P => IsOrthProjOnto P (ker A)) ⟨_, hPproj⟩
    exact orthoProjection_eq_of_range_eq hsp.1 hPproj.1 (hsp.2.trans hPproj.2.symm)
  have hrules := (hI 1 le_rfl H E hE).2.2.2.2.1
  have hfix : ∀ ψ, B 1 ψ = ψ → ψ ∈ ker A := by
    intro ψ hψ
    obtain ⟨u, hudef⟩ : ∃ u : Space 1 → ℂ, ∀ y, u y =
        ((Real.exp (-negLogReal (y 0)) : ℝ) : ℂ) - 1 := ⟨_, fun _ => rfl⟩
    have hu : Measurable u := by
      rw [show u = fun y => ((Real.exp (-negLogReal (y 0)) : ℝ) : ℂ) - 1 from funext hudef]
      exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp hf.neg)).sub
        measurable_const
    have hb1 := isBoundedMeasurable_powFn 1
    have hb0 := isBoundedMeasurable_powFn 0
    have hvb : IsBoundedMeasurableFn fun y => powFn 1 y + (-1 : ℂ) * powFn 0 y := by
      refine ⟨hb1.1.add (measurable_const.mul hb0.1), 2, fun y => ?_⟩
      calc ‖powFn 1 y + (-1 : ℂ) * powFn 0 y‖ ≤ ‖powFn 1 y‖ + ‖(-1 : ℂ) * powFn 0 y‖ :=
            norm_add_le _ _
        _ ≤ 1 + 1 := by
            refine add_le_add (norm_powFn_le 1 y) ?_
            rw [norm_mul, norm_neg, norm_one, one_mul]
            exact norm_powFn_le 0 y
        _ = 2 := by norm_num
    have huv := spectralOp_congr hC hI hE hN hu hvb.1 (fun y hy => by
      rw [hudef]
      unfold powFn
      rw [powReal_of_mem _ hy, powReal_of_mem _ hy]
      simp
      ring)
    have hbs := (hrules.1 _ _ (-1) hb1 hb0).1
    have hz : zeroLocus hu = negLogZeroLocus := by
      refine Subtype.ext (Set.ext fun y => ?_)
      change u y = 0 ↔ negLogFn y = 0
      rw [hudef, negLogFn_apply, sub_eq_zero]
      have e : ((Real.exp (-negLogReal (y 0)) : ℝ) : ℂ) = 1 ↔ Real.exp (-negLogReal (y 0)) = 1 := by
        exact_mod_cast Iff.rfl
      rw [e, Real.exp_eq_one_iff, neg_eq_zero, Complex.ofReal_eq_zero]
    have hk : ker (spectralOp E u) = range (E (zeroLocus hu)) :=
      (hC 1 1 H E hE _ _ hu hu 0).2.2.2.2.2.1
    rw [huv, spectralOp_eq_ofCLM hC hI hE hvb, hbs, hz, ← hkerA, ← hBC 1, ← hBC 0,
      hB.map_zero] at hk
    rw [← hk]
    refine ⟨mem_domain_ofCLM _ ψ, ?_⟩
    change (B 1 + (-1 : ℂ) • (1 : H →L[ℂ] H)) ψ = 0
    simp [hψ]
  have hlim : TendstoStrongly atTop B (E negLogZeroLocus) := by
    intro ψ
    have hEZ : boundedCalculus E negLogZeroIndicator = E negLogZeroLocus := hrules.2.2.1 negLogZeroLocus
    have ht : Tendsto (fun t => B t ψ) atTop (𝓝 (E negLogZeroLocus ψ)) := by
      refine tendsto_of_seq_tendsto fun τ hτ => ?_
      have h₁ := tendsto_boundedCalculus_apply hC hI hE hN (fs := fun j => powFn (τ j))
        (f := negLogZeroIndicator) (fun j => isBoundedMeasurable_powFn _)
        isBoundedMeasurable_negLogZeroIndicator
        (fun j y => norm_powFn_le _ y) (fun y hy => tendsto_powFn_atTop hτ hy) ψ
      rw [hEZ] at h₁
      refine Tendsto.congr (fun j => ?_) h₁
      simp only [Function.comp_def]
      rw [hBC]
    exact tendsto_iff_norm_sub_tendsto_zero.mp ht
  rw [hgenA, hproj]
  exact ⟨hker, ⟨A, hgen, huniq⟩, hgen, ⟨hcar, hAL⟩, hfix, hPproj, hlim⟩
end YangMills.Construction.PositiveFormReconstruction.PositiveContractionGenerator
