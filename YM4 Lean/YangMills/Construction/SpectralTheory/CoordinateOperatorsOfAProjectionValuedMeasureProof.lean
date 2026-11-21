import YangMills.Construction.HilbertSpace.BasicFacts
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusTheorem
import YangMills.Construction.SpectralTheory.CoordinateOperatorsOfAProjectionValuedMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.CoordOps
open YangMills.Construction.BorelSpectral YangMills.Construction.HilbertSpaceBasics YangMills.Construction.SpectralTheorem YangMills.Construction.SelfAdjointFunctions YangMills.Construction.BorelCalculus
section Lemmas
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
  {Y : Set (Fin n → ℝ)}
theorem measurable_coordEval (l : Fin n) : Measurable fun y : FullSpace n => y.1 l :=
  (measurable_pi_apply l).comp measurable_subtype_coe
theorem measurable_coordEval_complex (l : Fin n) :
    Measurable fun y : FullSpace n => ((y.1 l : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (measurable_coordEval l)
theorem hasDomainAndAction_of_isSpectralIntegralOf {A : UnboundedOp H} {E : SpectralMeasure Y H}
    {g : Y → ℂ} (h : IsSpectralIntegralOf A E g) :
    HasDomainAndAction A (E.integralDom g) (E.integralApply g) :=
  ⟨Set.ext fun ψ => h.1 ψ, h.2⟩
theorem isSpectralIntegralOf_of_hasDomainAndAction {A : UnboundedOp H} {E : SpectralMeasure Y H}
    {g : Y → ℂ} (h : HasDomainAndAction A (E.integralDom g) (E.integralApply g)) :
    IsSpectralIntegralOf A E g :=
  ⟨fun ψ => by rw [← h.1]; rfl, h.2⟩
theorem unboundedCalc (hC : BorelCalculusTheorem)
    (E : SpectralMeasure Y H) : UnboundedFunctionalCalculus E :=
  ((hC H n).1 Y E).2.2.2.1
theorem isSpectralIntegralOf_spectralIntegralOp (hC : BorelCalculusTheorem)
    (E : SpectralMeasure Y H) {g : Y → ℂ} (hg : Measurable g) :
    IsSpectralIntegralOf (spectralIntegralOp E g) E g := by
  obtain ⟨A, -, hA⟩ := (unboundedCalc hC E).exists_op g hg
  exact Classical.epsilon_spec (p := fun A => IsSpectralIntegralOf A E g)
    ⟨A, isSpectralIntegralOf_of_hasDomainAndAction hA⟩
theorem isSelfAdjointOp_of_coord (hC : BorelCalculusTheorem)
    {E : SpectralMeasure (FullSpace n) H} {A : UnboundedOp H} {l : Fin n}
    (h : IsSpectralIntegralOf A E fun y => ((y.1 l : ℝ) : ℂ)) : IsSelfAdjointOp A :=
  (unboundedCalc hC E).isSelfAdjoint _ (measurable_coordEval_complex l)
    (fun _ => Complex.ofReal_im _) A (hasDomainAndAction_of_isSpectralIntegralOf h)
theorem spectralMeasure_eq_coordMarginal (hS : SpectralTheoremHolds)
    (hC : BorelCalculusTheorem)
    {E : SpectralMeasure (FullSpace n) H} {A : UnboundedOp H} {l : Fin n}
    (h : IsSpectralIntegralOf A E fun y => ((y.1 l : ℝ) : ℂ)) :
    spectralMeasure A = E.coordMarginal l := by
  obtain ⟨-, -, -, -, -, -, h₇, -, -⟩ := hS H A (isSelfAdjointOp_of_coord hC h)
  exact (h₇ n univ E (fun y => y.1 l) (measurable_coordEval l) h).1
theorem isSpectralIntegralOf_fnCalc (hS : SpectralTheoremHolds)
    (hC : BorelCalculusTheorem)
    {E : SpectralMeasure (FullSpace n) H} {A : UnboundedOp H} {l : Fin n}
    (h : IsSpectralIntegralOf A E fun y => ((y.1 l : ℝ) : ℂ)) {f : ℝ → ℂ} (hf : Measurable f) :
    IsSpectralIntegralOf (fnCalc A f) E fun y => f (y.1 l) := by
  obtain ⟨-, -, -, -, -, -, h₇, -, -⟩ := hS H A (isSelfAdjointOp_of_coord hC h)
  have h₂ := (h₇ n univ E (fun y => y.1 l) (measurable_coordEval l) h).2 f hf
  have h₁ : IsSpectralIntegralOf (fnCalc A f) (spectralMeasure A) fun y => f (y.1 0) :=
    isSpectralIntegralOf_spectralIntegralOp hC _ (hf.comp (measurable_coordEval 0))
  refine ⟨fun ψ => (h₁.1 ψ).trans (by rw [h₂.1]), fun ψ => (h₁.2 ψ).trans ?_⟩
  exact h₂.2 ψ ((h₁.1 ψ).1 ψ.2)
theorem eq_of_hasCoordOps (hS : SpectralTheoremHolds)
    (hC : BorelCalculusTheorem)
    {E E' : SpectralMeasure (FullSpace n) H} {A : Fin n → UnboundedOp H}
    (h : HasCoordOps E A) (h' : HasCoordOps E' A) : E' = E :=
  ((hC H n).2 E).eq_of_coordMarginal_eq E' fun l =>
    (spectralMeasure_eq_coordMarginal hS hC (h' l)).symm.trans
      (spectralMeasure_eq_coordMarginal hS hC (h l))
theorem isSelfAdjoint_of_isSelfAdjointOp_ofBounded {B : H →L[ℂ] H}
    (h : IsSelfAdjointOp (ofBounded B)) : IsSelfAdjoint B :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y =>
    (h.2.2 ⟨x, Submodule.mem_top⟩ ⟨y, Submodule.mem_top⟩).symm
def outsideIcc (c : ℝ) (l : Fin n) : BorelSubsets (FullSpace n) :=
  ⟨{y | y.1 l ∉ Icc (-c) c}, (measurable_coordEval l measurableSet_Icc).compl⟩
def coordBox (c : ℝ) (i k : Fin n) : BorelSubsets (FullSpace n) :=
  ⟨{y | y.1 i ∈ Icc (-c) c ∧ y.1 k ∈ Icc (-c) c},
    (measurable_coordEval i measurableSet_Icc).inter (measurable_coordEval k measurableSet_Icc)⟩
theorem apply_outsideIcc_eq_zero (hS : SpectralTheoremHolds)
    (hC : BorelCalculusTheorem)
    (hF : HilbertSpaceFacts.Facts) {E : SpectralMeasure (FullSpace n) H} {l : Fin n}
    {B : H →L[ℂ] H} (h : IsSpectralIntegralOf (ofBounded B) E fun y => ((y.1 l : ℝ) : ℂ)) {c : ℝ}
    (hc : 0 < c) (hBc : ‖B‖ ≤ c) : E (outsideIcc c l) = 0 := by
  have hsa := isSelfAdjointOp_of_coord hC h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hN, -⟩ := hF
  obtain ⟨hlo, hhi⟩ := hN H B c (isSelfAdjoint_of_isSelfAdjointOp_ofBounded hsa) hBc
  obtain ⟨-, -, -, -, -, -, -, -, h₉⟩ := hS H _ hsa
  have hcar := (h₉ B (-c) c rfl (by linarith) hlo hhi).2
  rw [spectralMeasure_eq_coordMarginal hS hC h] at hcar
  exact hcar
theorem isCarriedBy_coordBox (hS : SpectralTheoremHolds)
    (hC : BorelCalculusTheorem)
    (hF : HilbertSpaceFacts.Facts) {E : SpectralMeasure (FullSpace n) H} {i k : Fin n}
    {B B' : H →L[ℂ] H} (h : IsSpectralIntegralOf (ofBounded B) E fun y => ((y.1 i : ℝ) : ℂ))
    (h' : IsSpectralIntegralOf (ofBounded B') E fun y => ((y.1 k : ℝ) : ℂ)) {c : ℝ} (hc : 0 < c)
    (hBc : ‖B‖ ≤ c) (hBc' : ‖B'‖ ≤ c) : E.IsCarriedBy (coordBox c i k) := by
  have bc : BoundedFunctionalCalculus E := ((hC H n).1 univ E).1
  have hU := bc.apply_iUnion Bool (fun b => cond b (outsideIcc c i) (outsideIcc c k))
    (fun b => by
      cases b
      · exact apply_outsideIcc_eq_zero hS hC hF h' hc hBc'
      · exact apply_outsideIcc_eq_zero hS hC hF h hc hBc)
  refine bc.apply_subset _ _ hU ?_
  intro y hy
  by_cases hi : y.1 i ∈ Icc (-c) c
  · have hk : y.1 k ∉ Icc (-c) c := fun hk => hy ⟨hi, hk⟩
    exact mem_iUnion.mpr ⟨false, hk⟩
  · exact mem_iUnion.mpr ⟨true, hi⟩
theorem integralDom_eq_univ_of_isCarriedBy (hC : BorelCalculusTheorem)
    {E : SpectralMeasure Y H} {g : Y → ℂ} (hg : Measurable g) {Δ₀ : BorelSubsets Y}
    (hΔ : E.IsCarriedBy Δ₀) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ y ∈ Δ₀.1, ‖g y‖ ≤ c) :
    E.integralDom g = univ ∧
      ∀ ψ, E.integralApply g ψ = E.integralOp (Δ₀.1.indicator g) ψ := by
  have hb : Measurable (Δ₀.1.indicator g) := hg.indicator Δ₀.2
  have hbound : ∀ y, ‖Δ₀.1.indicator g y‖ ≤ c := fun y => by
    by_cases hy : y ∈ Δ₀.1
    · rw [indicator_of_mem hy]
      exact hc y hy
    · rw [indicator_of_notMem hy, norm_zero]
      exact hc0
  obtain ⟨hd, hv⟩ := (unboundedCalc hC E).congr g _ hg hb Δ₀ hΔ
    fun y hy => (indicator_of_mem hy g).symm
  have hdom : E.integralDom g = univ := hd.trans (E.integralDom_eq_univ hbound)
  refine ⟨hdom, fun ψ => ?_⟩
  rw [hv ψ (hdom ▸ mem_univ ψ), E.integralApply_eq_integralOp hbound]
theorem eq_ofBounded_of_isSpectralIntegralOf {A : UnboundedOp H} {E : SpectralMeasure Y H}
    {g : Y → ℂ} (h : IsSpectralIntegralOf A E g) (hd : E.integralDom g = univ) {T : H →L[ℂ] H}
    (hv : ∀ ψ, E.integralApply g ψ = T ψ) : A = ofBounded T := by
  have hdom : A.domain = ⊤ := (Submodule.eq_top_iff').mpr fun ψ => (h.1 ψ).2 (hd ▸ mem_univ ψ)
  exact LinearPMap.ext hdom fun x hx _ => (h.2 ⟨x, hx⟩).trans (hv x)
theorem absOp_coord_spec (hS : SpectralTheoremHolds)
    (hC : BorelCalculusTheorem)
    (hF : HilbertSpaceFacts.Facts) {E : SpectralMeasure (FullSpace n) H} {i k : Fin n}
    {B B' : H →L[ℂ] H} {A' : UnboundedOp H}
    (h : IsSpectralIntegralOf (ofBounded B) E fun y => ((y.1 i : ℝ) : ℂ))
    (h' : IsSpectralIntegralOf (ofBounded B') E fun y => ((y.1 k : ℝ) : ℂ))
    (hA' : A' = ofBounded B') :
    ∃ C : H →L[ℂ] H, absOp A' = ofBounded C ∧ IsSelfAdjoint C ∧
      (E (setLtAbs i k) = 0 ↔ IsPositiveOp (B - C)) := by
  subst hA'
  obtain ⟨c, hc, hBc, hBc'⟩ : ∃ c : ℝ, 0 < c ∧ ‖B‖ ≤ c ∧ ‖B'‖ ≤ c :=
    ⟨max ‖B‖ ‖B'‖ + 1, by positivity, (le_max_left _ _).trans (by linarith),
      (le_max_right _ _).trans (by linarith)⟩
  have hcar := isCarriedBy_coordBox hS hC hF h h' hc hBc hBc'
  have bc : BoundedFunctionalCalculus E := ((hC H n).1 univ E).1
  have hyi := measurable_coordEval i
  have hyk := measurable_coordEval k
  set u : FullSpace n → ℂ := fun y => ((y.1 i : ℝ) : ℂ) with hu
  set v : FullSpace n → ℂ := fun y => ((|y.1 k| : ℝ) : ℂ) with hv'
  set w : FullSpace n → ℂ := fun y => ((y.1 i - |y.1 k| : ℝ) : ℂ) with hw
  have hmu : Measurable u := measurable_coordEval_complex i
  have hmv : Measurable v := Complex.measurable_ofReal.comp hyk.abs
  have hmw : Measurable w := Complex.measurable_ofReal.comp (hyi.sub hyk.abs)
  have hbu : ∀ y ∈ (coordBox c i k).1, ‖u y‖ ≤ c := fun y hy => by
    simpa [hu, Real.norm_eq_abs, abs_le] using hy.1
  have hbv : ∀ y ∈ (coordBox c i k).1, ‖v y‖ ≤ c := fun y hy => by
    simpa [hv', Real.norm_eq_abs, abs_le] using hy.2
  have hbw : ∀ y ∈ (coordBox c i k).1, ‖w y‖ ≤ 2 * c := fun y hy => by
    have h₂ := abs_le.mpr hy.2
    have h₃ := abs_nonneg (y.1 k)
    have h₄ : ‖w y‖ = abs (y.1 i - abs (y.1 k)) :=
      (Complex.norm_real _).trans (Real.norm_eq_abs _)
    rw [h₄, abs_le]
    constructor <;> linarith [hy.1.1, hy.1.2]
  obtain ⟨-, hvalu⟩ := integralDom_eq_univ_of_isCarriedBy hC hmu hcar hc.le hbu
  obtain ⟨hdv, hvalv⟩ := integralDom_eq_univ_of_isCarriedBy hC hmv hcar hc.le hbv
  obtain ⟨hdw, hvalw⟩ := integralDom_eq_univ_of_isCarriedBy hC hmw hcar (by positivity) hbw
  set bu := (coordBox c i k).1.indicator u with hbu'
  set bv := (coordBox c i k).1.indicator v with hbv'
  have hB : ∀ ψ, B ψ = E.integralOp bu ψ := fun ψ =>
    (h.2 ⟨ψ, Submodule.mem_top⟩).trans (hvalu ψ)
  have hmbu : Measurable bu := hmu.indicator (coordBox c i k).2
  have hmbv : Measurable bv := hmv.indicator (coordBox c i k).2
  have hbd : ∀ (g : FullSpace n → ℂ) (c' : ℝ), 0 ≤ c' → (∀ y ∈ (coordBox c i k).1, ‖g y‖ ≤ c') →
      IsBoundedFn ((coordBox c i k).1.indicator g) := fun g c' h0 hg => ⟨c', fun y => by
    by_cases hy : y ∈ (coordBox c i k).1
    · rw [indicator_of_mem hy]
      exact hg y hy
    · rw [indicator_of_notMem hy, norm_zero]
      exact h0⟩
  have hbdu : IsBoundedFn bu := hbd _ _ hc.le hbu
  have hbdv : IsBoundedFn bv := hbd _ _ hc.le hbv
  have hrealv : IsRealValued bv := fun y => by
    by_cases hy : y ∈ (coordBox c i k).1
    · rw [hbv', indicator_of_mem hy]
      exact Complex.ofReal_im _
    · rw [hbv', indicator_of_notMem hy]
      rfl
  have hCsa : IsSelfAdjoint (E.integralOp bv) := bc.isSelfAdjoint bv hmbv hbdv hrealv
  have hBsa : IsSelfAdjoint B :=
    isSelfAdjoint_of_isSelfAdjointOp_ofBounded (isSelfAdjointOp_of_coord hC h)
  have hsplit : (coordBox c i k).1.indicator w = bu + (-1 : ℂ) • bv := by
    funext y
    by_cases hy : y ∈ (coordBox c i k).1
    · simp [hbu', hbv', indicator_of_mem hy, hw, hu, hv', sub_eq_add_neg]
    · simp [hbu', hbv', indicator_of_notMem hy]
  have hdiff : ∀ ψ, E.integralApply w ψ = (B - E.integralOp bv) ψ := fun ψ => by
    have hneg : Measurable ((-1 : ℂ) • bv) := hmbv.const_smul _
    have hnegb : IsBoundedFn ((-1 : ℂ) • bv) := by
      obtain ⟨c', hc'⟩ := hbdv
      exact ⟨c', fun y => by simpa using hc' y⟩
    rw [hvalw, hsplit, bc.add _ _ hmbu hbdu hneg hnegb, bc.smul _ _ hmbv hbdv]
    simp [hB, sub_eq_add_neg]
  have hnn := ((hC H n).1 univ E).2.2.2.2.1.nonneg_iff w hmw fun y => Complex.ofReal_im _
  have hset : E (negativeLocus hmw) = E (setLtAbs i k) := by
    refine congrArg E.toFun (Subtype.ext ?_)
    ext y
    simp [negativeLocus, setLtAbs, hw]
  refine ⟨E.integralOp bv, ?_, hCsa, ?_⟩
  · have habs : IsSpectralIntegralOf (absOp (ofBounded B')) E v :=
      isSpectralIntegralOf_fnCalc hS hC h' (f := fun x => ((|x| : ℝ) : ℂ))
        (Complex.measurable_ofReal.comp measurable_id.abs)
    exact eq_ofBounded_of_isSpectralIntegralOf habs hdv hvalv
  · rw [hset] at hnn
    constructor
    · intro h₀
      refine ⟨hBsa.sub hCsa, fun ψ => ?_⟩
      rw [← hdiff]
      exact hnn.mpr h₀ ψ (hdw ▸ mem_univ ψ)
    · rintro ⟨-, hpos⟩
      refine hnn.mp fun ψ _ => ?_
      rw [hdiff]
      exact hpos ψ
end Lemmas
theorem coordOpsTheorem_holds (hS : SpectralTheoremHolds)
    (hC : BorelCalculusTheorem)
    (hF : HilbertSpaceFacts.Facts) : CoordOpsTheorem := by
  intro H _ _ _ n E
  have hI : HasCoordOps E (coordOperator E) := fun l =>
    isSpectralIntegralOf_spectralIntegralOp hC E (measurable_coordEval_complex l)
  have hM : ∀ l, spectralMeasure (coordOperator E l) = E.coordMarginal l := fun l =>
    spectralMeasure_eq_coordMarginal hS hC (hI l)
  refine ⟨fun l => ⟨isSelfAdjointOp_of_coord hC (hI l), hM l, fun f hf =>
      isSpectralIntegralOf_fnCalc hS hC (hI l) hf⟩, ?_, hI,
    fun E' h => eq_of_hasCoordOps hS hC hI h, fun i k _ => ?_⟩
  · intro i j Δ Δ'
    rw [hM i, hM j]
    exact ((hC H n).2 E).commute i j _ _
  · have hP : HasCoordOps (pairPushforward E i k)
        ![coordOperator E i, coordOperator E k] := by
      intro l
      obtain ⟨hd, hv⟩ := ((hC H n).1 univ E).2.2.2.2.2.1.integral_pushforward (m := 2)
        (Y' := FullSpace 2) (by norm_num) MeasurableSet.univ (coordPair i k)
        (measurable_coordPair i k) (fun y => ((y.1 l : ℝ) : ℂ)) (measurable_coordEval_complex l)
      have hcomp : (fun y : FullSpace 2 => ((y.1 l : ℝ) : ℂ)) ∘ coordPair i k =
          fun y => ((y.1 (![i, k] l) : ℝ) : ℂ) := by
        funext y
        fin_cases l <;> rfl
      have hop : (![coordOperator E i, coordOperator E k] : Fin 2 → UnboundedOp H) l =
          coordOperator E (![i, k] l) := by
        fin_cases l <;> rfl
      rw [hcomp] at hd hv
      rw [hop]
      have hl := hI (![i, k] l)
      exact ⟨fun ψ => (hl.1 ψ).trans (by
        rw [show (pairPushforward E i k).integralDom _ = _ from hd]),
        fun ψ => (hl.2 ψ).trans (hv ψ ((hl.1 ψ).1 ψ.2)).symm⟩
    refine ⟨hP, fun F h => eq_of_hasCoordOps hS hC hP h, rfl, ?_⟩
    intro B B' hB hB'
    exact absOp_coord_spec hS hC hF (hB ▸ hI i) (hB' ▸ hI k) hB'
end YangMills.Construction.CoordOps
