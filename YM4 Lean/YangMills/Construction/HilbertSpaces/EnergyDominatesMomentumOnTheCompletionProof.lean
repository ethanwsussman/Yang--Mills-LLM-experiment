import YangMills.Construction.HilbertSpaces.EnergyDominatesMomentumOnTheCompletion
import YangMills.Construction.HilbertSpaces.EnergyMomentumMeasureOfACommutingRepresentation
import YangMills.Construction.HilbertSpaces.FormAndItsCompletion
import YangMills.Construction.HilbertSpaces.GeneratorOfASemigroupOfPositiveContractions
import YangMills.Construction.HilbertSpaces.SemigroupOnTheCompletion
import YangMills.Construction.HilbertSpaces.UnitaryOperatorsOnTheCompletion
import YangMills.Construction.SpectralMeasures.CalculusOfBorelFunctionsOnEuclideanSpace
import Mathlib
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped NNReal ComplexOrder InnerProductSpace ComplexConjugate
open YangMills.Construction.EuclideanBorel (Space BorelSubset IsBoundedMeasurableFn IsPVM
  SpectralIntegralIs IsNull NullProperties DiagonalMeasureProperties BoundedCalculusUnique
  BoundedCalculusProperties CutoffsConverge boundedCalculus spectralIntegral
  spectralIntegral_eq_boundedCalculus diagonalMeasure sqIntegrableDomain momentumVec
  momentumExpChar expMomentumOp pvmSupport maxOpenNull
  IsMaximalOpenNull RealizesSpectralIntegral spectralOp disagreementSet
  coordLtAbs CoordOpGeAbs)
open YangMills.Construction.FormsOperators (IsHilbertCompletion IsLoewnerGE
  IsStronglyContUnitaryRep UnitaryMap formRadical formOnQuotient)
open YangMills.Construction.SpectralTheory (UnboundedOp)
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.CompletionEnergyBound
section FormToOperator
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : PreHilbertData V) (h : S.IsAdmissible)
  (j : (V ⧸ formRadical S.form h.hermitian.toIsSesquilinear) →ₗ[ℂ] H)
theorem secondDifferenceBound_of_form_nonneg
    (hj : IsHilbertCompletion (formOnQuotient S.form h.hermitian.toIsSesquilinear) j)
    (hmk : ∀ F F' : V, formOnQuotient S.form h.hermitian.toIsSesquilinear (Submodule.Quotient.mk F)
      (Submodule.Quotient.mk F') = S.form F F')
    (hT : ∀ t, CLMExtends S h.hermitian.toIsSesquilinear j (S.semigroupMap t)
      (transferOp S h.hermitian.toIsSesquilinear j t))
    (hU : ∀ a, UnitaryExtends S h.hermitian.toIsSesquilinear j (S.translationMap a)
      (translationOp S h.hermitian.toIsSesquilinear j a))
    (i : Fin 3) (t : ℝ≥0) (hF : ∀ F, 0 ≤ S.form F (secondDifferenceMap S i t F)) :
    SecondDifferenceBound S h.hermitian.toIsSesquilinear j i t := by
  have cdef : ∀ F, embed S h.hermitian.toIsSesquilinear j F = j (Submodule.Quotient.mk F) :=
    fun _ => rfl
  obtain ⟨c, hc⟩ : ∃ c : V → H, c = embed S h.hermitian.toIsSesquilinear j := ⟨_, rfl⟩
  have cadd : ∀ F G, c (F + G) = c F + c G := fun F G => by
    simp [hc, cdef, Submodule.Quotient.mk_add]
  have csub : ∀ F G, c (F - G) = c F - c G := fun F G => by
    simp [hc, cdef, Submodule.Quotient.mk_sub]
  have csmul : ∀ (z : ℂ) F, c (z • F) = z • c F := fun z F => by
    simp [hc, cdef, Submodule.Quotient.mk_smul]
  obtain ⟨T, hTdef⟩ : ∃ T, T = transferOp S h.hermitian.toIsSesquilinear j t := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Space 3, a = (t : ℝ) • spatialBasis i := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : Space 3, a' = (-(t : ℝ)) • spatialBasis i := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U, U = translationOp S h.hermitian.toIsSesquilinear j a := ⟨_, rfl⟩
  have hTc : ∀ F, T (c F) = c (S.semigroupMap t F) := fun F => by
    rw [hTdef, hc]; exact hT t F
  have hUc : ∀ F, U (c F) = c (S.translationMap a F) := fun F => by
    rw [hUdef, hc]; exact hU a F
  have hsum : a + a' = 0 := by simp [ha, ha', neg_smul]
  have hUs : ∀ F, U.symm (c F) = c (S.translationMap a' F) := fun F => by
    rw [LinearIsometryEquiv.symm_apply_eq, hUc]
    have e : S.translationMap a (S.translationMap a' F) = F := by
      have e₁ := LinearMap.congr_fun (h.translationMap_comp a a') F
      simpa [hsum, h.translationMap_zero] using e₁
    rw [e]
  have hTT : ∀ F, S.semigroupMap t (S.semigroupMap t F) = S.semigroupMap (2 * t) F := fun F => by
    have e₁ := LinearMap.congr_fun (h.semigroupMap_comp t t) F
    rw [two_mul]
    simpa using e₁
  obtain ⟨B, hB⟩ : ∃ B : H →L[ℂ] H, B = (1 - T) ^ 2 -
      T * ((2 : ℂ) • 1 - toCLM U - unitaryStar U) := ⟨_, rfl⟩
  have hBx : ∀ x, B x = x - (4 : ℂ) • T x + T (T x) + T (U x) + T (U.symm x) := fun x => by
    have e₁ : toCLM U x = U x := rfl
    have e₂ : unitaryStar U x = U.symm x := rfl
    rw [hB, pow_two]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, map_sub, map_smul, e₁, e₂]
    module
  have hBc : ∀ F, B (c F) = c (secondDifferenceMap S i t F) := fun F => by
    rw [hBx]
    simp only [secondDifferenceMap, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearMap.comp_apply, cadd, csub, csmul, hTc, hUc, hUs, hTT, ha, ha']
  have hnn : ∀ ψ, 0 ≤ ⟪ψ, B ψ⟫_ℂ := by
    have hd : DenseRange j :=
      (YangMills.Construction.FormsOperators.isDenseSet_iff_dense _).1 hj.dense_range
    intro ψ
    refine hd.induction_on ψ (isClosed_le continuous_const (by fun_prop)) fun x => ?_
    obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e₁ : j (Submodule.Quotient.mk F) = c F := by rw [hc, cdef]
    rw [e₁, hBc]
    have e₂ : ∀ G, c G = j (Submodule.Quotient.mk G) := fun G => by rw [hc, cdef]
    rw [e₂, e₂, hj.inner_map, hmk]
    exact hF F
  intro ψ
  have e₃ := hnn ψ
  rw [hB, ContinuousLinearMap.sub_apply, inner_sub_right, sub_nonneg] at e₃
  rw [← hTdef, ← ha, ← hUdef]
  exact e₃
end FormToOperator
section BoundedCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {m : ℕ}
def HasBoundedCalculus (E : BorelSubset m → H →L[ℂ] H) (f : Space m → ℂ) (B : H →L[ℂ] H) : Prop :=
  IsBoundedMeasurableFn f ∧ boundedCalculus E f = B
theorem isBoundedMeasurableFn_add_mul {f g : Space m → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) (z : ℂ) : IsBoundedMeasurableFn fun y => f y + z * g y := by
  obtain ⟨mf, C, hC⟩ := hf
  obtain ⟨mg, D, hD⟩ := hg
  refine ⟨mf.add (measurable_const.mul mg), C + ‖z‖ * D, fun y => ?_⟩
  calc ‖f y + z * g y‖ ≤ ‖f y‖ + ‖z * g y‖ := norm_add_le _ _
    _ ≤ C + ‖z‖ * D := by
      rw [norm_mul]
      exact add_le_add (hC y) (mul_le_mul_of_nonneg_left (hD y) (norm_nonneg _))
theorem isBoundedMeasurableFn_mul {f g : Space m → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) : IsBoundedMeasurableFn fun y => f y * g y := by
  obtain ⟨mf, C, hC⟩ := hf
  obtain ⟨mg, D, hD⟩ := hg
  refine ⟨mf.mul mg, C * D, fun y => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC y) (hD y) (norm_nonneg _) ((norm_nonneg _).trans (hC y))
theorem HasBoundedCalculus.add_mul {E : BorelSubset m → H →L[ℂ] H} (hR : BoundedCalculusProperties E)
    {f g : Space m → ℂ} {B C : H →L[ℂ] H} (hf : HasBoundedCalculus E f B)
    (hg : HasBoundedCalculus E g C) (z : ℂ) :
    HasBoundedCalculus E (fun y => f y + z * g y) (B + z • C) :=
  ⟨isBoundedMeasurableFn_add_mul hf.1 hg.1 z, by
    rw [(hR.1 f g z hf.1 hg.1).1, hf.2, hg.2]⟩
theorem HasBoundedCalculus.mul {E : BorelSubset m → H →L[ℂ] H} (hR : BoundedCalculusProperties E)
    {f g : Space m → ℂ} {B C : H →L[ℂ] H} (hf : HasBoundedCalculus E f B)
    (hg : HasBoundedCalculus E g C) :
    HasBoundedCalculus E (fun y => f y * g y) (B * C) :=
  ⟨isBoundedMeasurableFn_mul hf.1 hg.1, by
    rw [(hR.1 f g 0 hf.1 hg.1).2, hf.2, hg.2]⟩
theorem hasBoundedCalculus_one {E : BorelSubset m → H →L[ℂ] H} (hE : IsPVM E)
    (hR : BoundedCalculusProperties E) : HasBoundedCalculus E (fun _ => (1 : ℂ)) 1 := by
  refine ⟨⟨measurable_const, 1, fun _ => by simp⟩, ?_⟩
  have e : (⊤ : BorelSubset m).1.indicator (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ) :=
    funext fun y => Set.indicator_of_mem (Set.mem_univ y) _
  have e₁ := hR.2.2.1 ⊤
  rw [e, hE.map_top] at e₁
  exact e₁
theorem pvm_negSet_eq_zero {E : BorelSubset m → H →L[ℂ] H} (hS : DiagonalMeasureProperties E)
    (hU : BoundedCalculusUnique E) {r : Space m → ℝ} {B : H →L[ℂ] H}
    (hB : HasBoundedCalculus E (fun y => (r y : ℂ)) B) (hnn : ∀ ψ, 0 ≤ ⟪ψ, B ψ⟫_ℂ)
    (hr : Measurable r) : E ⟨{y | r y < 0}, measurableSet_lt hr measurable_const⟩ = 0 := by
  obtain ⟨_, h₂, h₃, _, _, h₆⟩ := hS
  obtain ⟨hb, hBeq⟩ := hB
  obtain ⟨_, C, hC⟩ := hb
  set D : BorelSubset m := ⟨{y | r y < 0}, measurableSet_lt hr measurable_const⟩ with hD
  ext ψ
  have hfin : IsFiniteMeasure (diagonalMeasure E ψ) :=
    ⟨by rw [h₃ ψ]; exact ENNReal.ofReal_lt_top⟩
  have hint : Integrable r (diagonalMeasure E ψ) := by
    refine Integrable.of_bound hr.aestronglyMeasurable C (ae_of_all _ fun y => ?_)
    simpa using hC y
  have hrestrict : diagonalMeasure E (E D ψ) = (diagonalMeasure E ψ).restrict D.1 := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.restrict_apply hs]
    exact h₆ ψ ⟨s, hs⟩ D
  have hpos : 0 ≤ ∫ y in D.1, r y ∂(diagonalMeasure E ψ) := by
    have e₁ := hnn (E D ψ)
    rw [← hBeq, (hU _ ⟨‹_›, C, hC⟩).2.2.1 (E D ψ), hrestrict] at e₁
    have e₂ : ∫ y in D.1, ((r y : ℝ) : ℂ) ∂(diagonalMeasure E ψ) =
        ((∫ y in D.1, r y ∂(diagonalMeasure E ψ) : ℝ) : ℂ) := integral_ofReal
    exact Complex.zero_le_real.1 (e₂ ▸ e₁)
  have hzero : diagonalMeasure E ψ D.1 = 0 := by
    by_contra hne
    have hsupp : Function.support (fun y => -r y) ∩ D.1 = D.1 := by
      refine inter_eq_right.2 fun y hy => ?_
      have hy' : r y < 0 := hy
      simpa using hy'.ne
    have e₂ : 0 < ∫ y in D.1, -r y ∂(diagonalMeasure E ψ) := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae, hsupp]
      · exact pos_iff_ne_zero.2 hne
      · refine (ae_restrict_iff' D.2).2 (ae_of_all _ fun y hy => ?_)
        have hy' : r y < 0 := hy
        simpa using hy'.le
      · exact hint.neg.integrableOn
    rw [integral_neg] at e₂
    linarith
  have e₃ := h₂ ψ D
  rw [hzero] at e₃
  have e₄ : ‖E D ψ‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 e₃.symm
  have e₅ : ‖E D ψ‖ = 0 := by nlinarith [norm_nonneg (E D ψ)]
  simpa using e₅
theorem spectralIntegral_eq_of_same_op {E : BorelSubset m → H →L[ℂ] H} {f g : Space m → ℂ}
    {A : UnboundedOp H} (hf : RealizesSpectralIntegral E f A) (hg : RealizesSpectralIntegral E g A)
    {ψ : H} (h₁ : ψ ∈ sqIntegrableDomain E f) (h₂ : ψ ∈ sqIntegrableDomain E g) :
    spectralIntegral E f ⟨ψ, h₁⟩ = spectralIntegral E g ⟨ψ, h₂⟩ := by
  have hA : ψ ∈ A.domain := by
    change ψ ∈ (A.domain : Set H)
    rw [hf.1]
    exact h₁
  obtain ⟨_, e₁⟩ := hf.2 ⟨ψ, hA⟩
  obtain ⟨_, e₂⟩ := hg.2 ⟨ψ, hA⟩
  exact e₁.trans e₂.symm
end BoundedCalculus
def negEnergySet : BorelSubset (1 + 3) :=
  ⟨{y | y energyCoordIndex < 0}, (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet⟩
def truncExpNegEnergy (t : ℝ≥0) (y : Space (1 + 3)) : ℝ :=
  Real.exp (-(t : ℝ) * max (y energyCoordIndex) 0)
def secondDifferenceSymbol (i : Fin 3) (t : ℝ≥0) (y : Space (1 + 3)) : ℝ :=
  (1 - truncExpNegEnergy t y) ^ 2 -
    truncExpNegEnergy t y * (2 - 2 * Real.cos ((t : ℝ) * y (momentumCoordIndex i)))
theorem continuous_truncExpNegEnergy (t : ℝ≥0) : Continuous (truncExpNegEnergy t) := by
  unfold truncExpNegEnergy
  fun_prop
theorem continuous_secondDifferenceSymbol (i : Fin 3) (t : ℝ≥0) :
    Continuous (secondDifferenceSymbol i t) := by
  have := continuous_truncExpNegEnergy t
  unfold secondDifferenceSymbol
  fun_prop
theorem truncExpNegEnergy_le_one (t : ℝ≥0) (y : Space (1 + 3)) : truncExpNegEnergy t y ≤ 1 := by
  refine Real.exp_le_one_iff.2 ?_
  have h₁ : (0 : ℝ) ≤ t := t.2
  have h₂ : (0 : ℝ) ≤ max (y energyCoordIndex) 0 := le_max_right _ _
  nlinarith [mul_nonneg h₁ h₂]
theorem inner_momentumVec (s : ℝ) (i : Fin 3) (y : Space (1 + 3)) :
    inner ℝ (s • spatialBasis i) (momentumVec y) = s * y (momentumCoordIndex i) := by
  have e : spatialBasis i = EuclideanSpace.single i (1 : ℝ) := rfl
  rw [inner_smul_left, e, EuclideanSpace.inner_single_left]
  simp [momentumVec, momentumCoordIndex]
theorem isBoundedMeasurableFn_momentumExpChar (a : Space 3) :
    IsBoundedMeasurableFn (momentumExpChar a) := by
  refine ⟨?_, 1, fun y => ?_⟩
  · have h₁ : Measurable fun y => inner ℝ a (momentumVec y) :=
      (continuous_const.inner continuous_id).measurable.comp measurable_momentumVec
    exact Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp h₁))
  · simp only [momentumExpChar]
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem pvm_negEnergySet_eq_zero {E : BorelSubset (1 + 3) → H →L[ℂ] H} (hN : NullProperties E)
    (hlarge : ∃ U, IsMaximalOpenNull E U)
    (hsupp : pvmSupport E ⊆ {y | 0 ≤ y energyCoordIndex}) : E negEnergySet = 0 := by
  have spec : IsMaximalOpenNull E (maxOpenNull E) := Classical.epsilon_spec hlarge
  obtain ⟨ho, hn⟩ := spec.1
  refine hN.2.1 ⟨_, ho.measurableSet⟩ negEnergySet (fun y hy => ?_) hn
  by_contra hyn
  exact absurd (show 0 ≤ y energyCoordIndex from hsupp hyn) (not_le.2 hy)
theorem hasBoundedCalculus_truncExpNegEnergy
    (hC : YangMills.Construction.EuclideanBorel.FunctionalCalculus.Statement)
    {E : BorelSubset (1 + 3) → H →L[ℂ] H} (hE : IsPVM E)
    (hN : NullProperties E) (hTr : CutoffsConverge E) (hL : E negEnergySet = 0)
    (t : ℝ≥0) {T : H →L[ℂ] H} (hT : SpectralIntegralIs E (expNegEnergy t) T) :
    HasBoundedCalculus E (fun y => (truncExpNegEnergy t y : ℂ)) T := by
  have hb : IsBoundedMeasurableFn fun y => (truncExpNegEnergy t y : ℂ) := by
    refine ⟨Complex.measurable_ofReal.comp (continuous_truncExpNegEnergy t).measurable, 1,
      fun y => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < truncExpNegEnergy t y from Real.exp_pos _)]
    exact truncExpNegEnergy_le_one t y
  have hdm : Measurable (expNegEnergy t) := by
    have : Continuous (expNegEnergy t) := by
      unfold expNegEnergy
      fun_prop
    exact this.measurable
  have c₁ := hC (1 + 3) 1 H E hE _ _ hdm hb.1 0
  have c₂ := hC (1 + 3) 1 H E hE _ _ hb.1 hb.1 0
  have hnull : IsNull E (disagreementSet hdm hb.1) := by
    refine hN.2.1 negEnergySet _ (fun y hy => ?_) hL
    by_contra hneg
    have h₀ : 0 ≤ y energyCoordIndex := not_lt.1 hneg
    refine hy ?_
    simp only [expNegEnergy, truncExpNegEnergy, max_eq_left h₀]
    push_cast
    rfl
  have heq := c₁.2.2.2.2.1.eq_of_null hnull
  have hop₂ : RealizesSpectralIntegral E (fun y => (truncExpNegEnergy t y : ℂ))
      (spectralOp E (expNegEnergy t)) := by
    rw [heq]
    exact c₂.1.isOp
  refine ⟨hb, ?_⟩
  ext ψ
  have hψ₁ : ψ ∈ sqIntegrableDomain E (expNegEnergy t) := by
    rw [hT.1]
    exact mem_univ ψ
  have hψ₂ : ψ ∈ sqIntegrableDomain E fun y => (truncExpNegEnergy t y : ℂ) := by
    rw [(hTr.2 _ hb).1]
    exact mem_univ ψ
  rw [← hT.2 ⟨ψ, hψ₁⟩]
  have e₁ := spectralIntegral_eq_boundedCalculus hTr hb ⟨ψ, hψ₂⟩
  exact e₁.symm.trans (spectralIntegral_eq_of_same_op hop₂ c₁.1.isOp hψ₂ hψ₁)
theorem hasBoundedCalculus_momentumExpChar {E : BorelSubset (1 + 3) → H →L[ℂ] H}
    (hTr : CutoffsConverge E) {a : Space 3} {W : UnitaryMap H H}
    (hW : sqIntegrableDomain E (momentumExpChar a) = univ ∧
      ∀ ψ, expMomentumOp E a ψ = W ψ.1) :
    HasBoundedCalculus E (momentumExpChar a) (toCLM W) := by
  have hb := isBoundedMeasurableFn_momentumExpChar a
  refine ⟨hb, ?_⟩
  ext ψ
  have hψ : ψ ∈ sqIntegrableDomain E (momentumExpChar a) := by
    rw [hW.1]
    exact mem_univ ψ
  exact (spectralIntegral_eq_boundedCalculus hTr hb ⟨ψ, hψ⟩).symm.trans (hW.2 ⟨ψ, hψ⟩)
theorem unitaryStar_eq_neg {W : Space 3 → UnitaryMap H H}
    (hW : IsStronglyContUnitaryRep W) (a : Space 3) :
    unitaryStar (W a) = toCLM (W (-a)) := by
  ext ψ
  change (W a).symm ψ = W (-a) ψ
  rw [LinearIsometryEquiv.symm_apply_eq]
  have e₁ := hW.map_add a (-a)
  rw [add_neg_cancel, hW.map_zero] at e₁
  exact (DFunLike.congr_fun e₁ ψ).symm
theorem hasBoundedCalculus_secondDifferenceSymbol {E : BorelSubset (1 + 3) → H →L[ℂ] H}
    (hE : IsPVM E) (hR : BoundedCalculusProperties E) (i : Fin 3) (t : ℝ≥0)
    {T : H →L[ℂ] H} {W W' : H →L[ℂ] H}
    (hT : HasBoundedCalculus E (fun y => (truncExpNegEnergy t y : ℂ)) T)
    (hW : HasBoundedCalculus E (momentumExpChar ((t : ℝ) • spatialBasis i)) W)
    (hW' : HasBoundedCalculus E (momentumExpChar (-((t : ℝ) • spatialBasis i))) W') :
    HasBoundedCalculus E (fun y => (secondDifferenceSymbol i t y : ℂ))
      ((1 - T) ^ 2 - T * ((2 : ℂ) • 1 - W - W')) := by
  have one := hasBoundedCalculus_one hE hR
  have a₁ := one.add_mul hR hT (-1)
  have two := one.add_mul hR one 1
  have b₁ := (two.add_mul hR hW (-1)).add_mul hR hW' (-1)
  have d₁ := (a₁.mul hR a₁).add_mul hR (hT.mul hR b₁) (-1)
  have eop : (1 + (-1 : ℂ) • T) * (1 + (-1 : ℂ) • T) +
      (-1 : ℂ) • (T * (1 + (1 : ℂ) • 1 + (-1 : ℂ) • W + (-1 : ℂ) • W')) =
      (1 - T) ^ 2 - T * ((2 : ℂ) • 1 - W - W') := by
    have e₂ : (2 : ℂ) • (1 : H →L[ℂ] H) = 1 + 1 := two_smul _ _
    rw [e₂]
    simp only [neg_smul, one_smul]
    noncomm_ring
  rw [eop] at d₁
  have efun : (fun y => (secondDifferenceSymbol i t y : ℂ)) = fun y =>
      (1 + (-1) * (truncExpNegEnergy t y : ℂ)) * (1 + (-1) * (truncExpNegEnergy t y : ℂ)) +
      (-1) * ((truncExpNegEnergy t y : ℂ) * (1 + 1 * 1 +
        (-1) * momentumExpChar ((t : ℝ) • spatialBasis i) y +
        (-1) * momentumExpChar (-((t : ℝ) • spatialBasis i)) y)) := by
    funext y
    have e₃ : momentumExpChar ((t : ℝ) • spatialBasis i) y +
        momentumExpChar (-((t : ℝ) • spatialBasis i)) y =
        2 * Complex.cos (((t : ℝ) * y (momentumCoordIndex i) : ℝ) : ℂ) := by
      simp only [momentumExpChar, inner_neg_left, inner_momentumVec]
      rw [Complex.two_cos]
      push_cast
      ring_nf
    simp only [secondDifferenceSymbol]
    push_cast
    push_cast at e₃
    linear_combination (-(truncExpNegEnergy t y : ℂ)) * e₃
  rw [efun]
  exact d₁
end Operators
theorem abs_le_of_secondDifference_nonneg {l p : ℝ} {τ : ℕ → ℝ} (hτ : ∀ k, 0 < τ k)
    (hlim : Tendsto τ atTop (𝓝 0)) (hl : 0 ≤ l)
    (hk : ∀ k, 0 ≤ (1 - Real.exp (-τ k * l)) ^ 2 -
      Real.exp (-τ k * l) * (2 - 2 * Real.cos (τ k * p))) : |p| ≤ l := by
  have step : ∀ k, 4 * Real.exp (-τ k * l) * (Real.sin (τ k * p / 2) / τ k) ^ 2 ≤ l ^ 2 := by
    intro k
    have ht := hτ k
    have hcos : 2 - 2 * Real.cos (τ k * p) = 4 * Real.sin (τ k * p / 2) ^ 2 := by
      have e₁ : τ k * p = 2 * (τ k * p / 2) := by ring
      rw [e₁, Real.cos_two_mul]
      have e₂ := Real.sin_sq_add_cos_sq (2 * (τ k * p / 2) / 2)
      have e₃ : 2 * (τ k * p / 2) / 2 = τ k * p / 2 := by ring
      rw [e₃] at e₂ ⊢
      nlinarith
    have hx : 0 ≤ τ k * l := mul_nonneg ht.le hl
    have hexp : 1 - Real.exp (-τ k * l) ≤ τ k * l := by
      have := Real.add_one_le_exp (-τ k * l)
      linarith
    have hexp₀ : 0 ≤ 1 - Real.exp (-τ k * l) := by
      have : Real.exp (-τ k * l) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      linarith
    have hsq : (1 - Real.exp (-τ k * l)) ^ 2 ≤ (τ k * l) ^ 2 :=
      pow_le_pow_left₀ hexp₀ hexp 2
    have hmain : Real.exp (-τ k * l) * (4 * Real.sin (τ k * p / 2) ^ 2) ≤ (τ k * l) ^ 2 := by
      have := hk k
      rw [hcos] at this
      linarith
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hne : Tendsto τ atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => (hτ k).ne'⟩
  have hd : HasDerivAt (fun u : ℝ => Real.sin (u * p / 2)) (p / 2) 0 := by
    have h₁ : HasDerivAt (fun u : ℝ => u * p / 2) (p / 2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const p).div_const 2
    simpa using h₁.sin
  have hs : Tendsto (fun k => Real.sin (τ k * p / 2) / τ k) atTop (𝓝 (p / 2)) := by
    have h₂ := (hasDerivAt_iff_tendsto_slope_zero.1 hd).comp hne
    refine h₂.congr fun k => ?_
    simp [div_eq_inv_mul]
  have he : Tendsto (fun k => Real.exp (-τ k * l)) atTop (𝓝 1) := by
    have h₃ : Tendsto (fun k => -τ k * l) atTop (𝓝 (-0 * l)) := (hlim.neg).mul_const l
    have h₄ := (Real.continuous_exp.tendsto _).comp h₃
    simpa [Function.comp_def] using h₄
  have hfin : Tendsto (fun k => 4 * Real.exp (-τ k * l) * (Real.sin (τ k * p / 2) / τ k) ^ 2)
      atTop (𝓝 (4 * 1 * (p / 2) ^ 2)) := (he.const_mul 4).mul (hs.pow 2)
  have hle := le_of_tendsto' hfin step
  exact abs_le_of_sq_le_sq (by nlinarith) hl
theorem holds (h₁ : QuotientCompletion.Statement)
    (h₂ : SemigroupOnCompletion.TransferSemigroupSpec)
    (h₃ : UnitaryOpsOnCompletion.UnitaryActionSpec)
    (h₄ : PositiveContractionGenerator.Statement)
    (h₅ : CommutingJointSpectrum.Statement)
    (h₆ : YangMills.Construction.EuclideanBorel.FunctionalCalculus.Statement)
    (h₇ : YangMills.Construction.EuclideanBorel.BoundedBorelCalculusTheorem) : Statement := by
  intro V _ _ S h H _ _ _ j hj
  obtain ⟨⟨_, hmk, _⟩, _⟩ := h₁ V S h
  obtain ⟨s₁, s₂, s₃, _⟩ := h₂ V S h H j hj
  obtain ⟨u₁, u₂, _, u₄, _⟩ := h₃ V S h H j hj
  obtain ⟨_, _, g₃, g₄, _⟩ := h₄ H _ s₂ s₃
  obtain ⟨_, p₀, _, p₂, _, _, _, p₆, _, _, p₉⟩ := h₅ H _ _ _ s₂ g₃ g₄ u₂ u₄
  refine ⟨fun i t _ hF => secondDifferenceBound_of_form_nonneg S h j hj hmk s₁ u₁ i t hF,
    fun i τ hpos _ hlim hineq => ?_⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = jointMeasure S h.hermitian.toIsSesquilinear j := ⟨_, rfl⟩
  have hE : IsPVM E := by rw [hEdef]; exact p₀.1
  obtain ⟨r₁, r₂, _, r₄, r₅, r₆⟩ := h₇ (1 + 3) (by norm_num) H E hE
  have hlarge : ∃ U, IsMaximalOpenNull E U := by
    have c₀ := h₆ (1 + 3) 1 H E hE (fun _ => 0) (fun _ => 0) measurable_const measurable_const 0
    exact c₀.2.2.2.2.2.2.2.2.2.2.1
  have hL : E negEnergySet = 0 :=
    pvm_negEnergySet_eq_zero r₂ hlarge (by rw [hEdef]; exact p₉)
  have hnull : ∀ k, E ⟨{y | secondDifferenceSymbol i (τ k) y < 0}, measurableSet_lt
      (continuous_secondDifferenceSymbol i (τ k)).measurable measurable_const⟩ = 0 := by
    intro k
    have hT := hasBoundedCalculus_truncExpNegEnergy h₆ hE r₂ r₆ hL (τ k)
      (T := transferOp S h.hermitian.toIsSesquilinear j (τ k)) (by rw [hEdef]; exact p₂ (τ k))
    have hW := hasBoundedCalculus_momentumExpChar (E := E) r₆
      (a := ((τ k : ℝ≥0) : ℝ) • spatialBasis i)
      (W := translationOp S h.hermitian.toIsSesquilinear j (((τ k : ℝ≥0) : ℝ) • spatialBasis i))
      (by rw [hEdef]; exact p₆ _)
    have hW' := hasBoundedCalculus_momentumExpChar (E := E) r₆
      (a := -(((τ k : ℝ≥0) : ℝ) • spatialBasis i))
      (W := translationOp S h.hermitian.toIsSesquilinear j (-(((τ k : ℝ≥0) : ℝ) • spatialBasis i)))
      (by rw [hEdef]; exact p₆ _)
    have hB := hasBoundedCalculus_secondDifferenceSymbol hE r₅ i (τ k) hT hW hW'
    rw [← unitaryStar_eq_neg u₂] at hB
    refine pvm_negSet_eq_zero r₁ r₄ hB (fun ψ => ?_)
      (continuous_secondDifferenceSymbol i (τ k)).measurable
    have e₁ := hineq k ψ
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, sub_nonneg]
    exact e₁
  obtain ⟨D, hD⟩ : ∃ D : ℕ → BorelSubset (1 + 3), D = fun k =>
      ⟨{y | secondDifferenceSymbol i (τ k) y < 0}, measurableSet_lt
        (continuous_secondDifferenceSymbol i (τ k)).measurable measurable_const⟩ := ⟨_, rfl⟩
  have hcount : (insert negEnergySet (range D)).Countable :=
    (countable_range D).insert _
  have hunion := r₂.2.2 (insert negEnergySet (range D))
    ⟨⋃ Δ ∈ insert negEnergySet (range D), Δ.1,
      MeasurableSet.biUnion hcount fun Δ _ => Δ.2⟩ hcount (by
      rintro Δ (rfl | ⟨k, rfl⟩)
      · exact hL
      · rw [hD]
        exact hnull k) rfl
  rw [← hEdef]
  refine r₂.2.1 _ _ (fun y hy => ?_) hunion
  by_contra hout
  have hy₀ : y energyCoordIndex < |y (momentumCoordIndex i)| := hy
  have hnot : ∀ Δ ∈ insert negEnergySet (range D), y ∉ Δ.1 := fun Δ hΔ hyΔ =>
    hout (mem_iUnion₂.2 ⟨Δ, hΔ, hyΔ⟩)
  have hl : 0 ≤ y energyCoordIndex := not_lt.1 (hnot _ (mem_insert _ _))
  have hk : ∀ k, 0 ≤ secondDifferenceSymbol i (τ k) y := fun k => by
    have := hnot (D k) (mem_insert_of_mem _ (mem_range_self k))
    rw [hD] at this
    exact not_lt.1 this
  refine absurd (abs_le_of_secondDifference_nonneg (τ := fun k => ((τ k : ℝ≥0) : ℝ)) hpos ?_ hl
    fun k => ?_) (not_le.2 hy₀)
  · simpa using NNReal.tendsto_coe.2 hlim
  · have := hk k
    simpa only [secondDifferenceSymbol, truncExpNegEnergy, max_eq_left hl] using this
end YangMills.Construction.PositiveFormReconstruction.CompletionEnergyBound
