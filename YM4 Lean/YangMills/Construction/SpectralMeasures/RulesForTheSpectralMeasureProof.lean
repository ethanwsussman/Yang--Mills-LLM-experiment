import YangMills.Construction.HilbertSpaces.GeneratorOfASemigroupOfPositiveContractionsProof
import YangMills.Construction.LinearAlgebra.TraceSixFoldProductProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanBorel.SpectralRules
open FormsOperators (IsContractive IsNonneg IsPositiveBounded IsSelfAdj Commutes UnitaryMap ofCLM)
open SpectralTheory (UnboundedOp)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
section PartialMaps
variable {n n' : ℕ} {E : BorelSubset n → H →L[ℂ] H} {E' : BorelSubset n' → H →L[ℂ] H}
  {f : Space n → ℂ} {f' : Space n' → ℂ} {A B : UnboundedOp H}
theorem integralOp_of_op (h : RealizesSpectralIntegral E f A) :
    IsSpectralIntegralOp A E f := by apply _root_.YangMills.Construction.PositiveFormReconstruction.PositiveContractionGenerator.isSpectralIntegralOp_of_isOp <;> assumption
theorem op_of_integralOp (h : IsSpectralIntegralOp A E f) :
    RealizesSpectralIntegral E f A := by
  obtain ⟨hd, hv⟩ := h
  exact ⟨hd, fun χ => ⟨hd ▸ χ.2, (hv χ).symm⟩⟩
theorem eq_of_isSpectralIntegralOp (hA : RealizesSpectralIntegral E f A)
    (hB : RealizesSpectralIntegral E f B) : A = B := by
  refine LinearPMap.ext (SetLike.coe_injective (hA.1.trans hB.1.symm)) fun x hx hy => ?_
  obtain ⟨_, h₁⟩ := hA.2 ⟨x, hx⟩
  obtain ⟨_, h₂⟩ := hB.2 ⟨x, hy⟩
  exact h₁.symm.trans h₂
theorem partialMapEq_of_isSpectralIntegralOp (h₁ : RealizesSpectralIntegral E f A)
    (h₂ : RealizesSpectralIntegral E' f' A) :
    PartialMapEq (spectralIntegral E f) (spectralIntegral E' f') := by
  refine ⟨h₁.1.symm.trans h₂.1, fun χ => ?_⟩
  have hχ : (χ : H) ∈ A.domain := by
    show (χ : H) ∈ (A.domain : Set H)
    rw [h₁.1]
    exact χ.2
  obtain ⟨_, v₁⟩ := h₁.2 ⟨χ, hχ⟩
  obtain ⟨_, v₂⟩ := h₂.2 ⟨χ, hχ⟩
  exact v₂.trans v₁.symm
theorem partialMapEq_symm {S T : Set H} {u : S → H} {v : T → H} (h : PartialMapEq u v) :
    PartialMapEq v u := by
  obtain ⟨rfl, hv⟩ := h
  exact ⟨rfl, fun χ => (hv χ).symm⟩
theorem conjPartialMap_apply (U : UnitaryMap H H) {S : Set H} (u : S → H) {φ : H} (hφ : φ ∈ S)
    (h : U φ ∈ U '' S) : conjPartialMap U u ⟨U φ, h⟩ = U (u ⟨φ, hφ⟩) := by
  simp only [conjPartialMap, LinearIsometryEquiv.symm_apply_apply]
end PartialMaps
theorem measurable_lineCoord : Measurable lineCoord :=
  (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun y : Space 1 => y 0)).measurable
theorem measurable_liftFromLine {h : ℝ → ℂ} (hh : Measurable h) :
    Measurable (liftFromLine h) :=
  hh.comp (by fun_prop : Continuous fun y : Space 1 => y 0).measurable
theorem spectralResolution_eq (hS : SelfAdjoint.SpectralTheorem) {A : UnboundedOp H}
    (hA : IsSelfAdj A) {E : BorelSubset 1 → H →L[ℂ] H} (h : IsSpectralResolution A E) :
    spectralResolution A = E := by
  obtain ⟨-, -, -, -, -, -, -, hu, hs, -, -⟩ := hS H A hA
  exact hu.unique hs h
theorem isSpectralResolution_self (hS : SelfAdjoint.SpectralTheorem) {A : UnboundedOp H}
    (hA : IsSelfAdj A) : IsSpectralResolution A (spectralResolution A) := by
  obtain ⟨-, -, -, -, -, -, -, -, hs, -, -⟩ := hS H A hA
  exact hs
section Pushforward
variable {n : ℕ} [NeZero n] {E : BorelSubset n → H →L[ℂ] H}
theorem measurable_ofReal_comp {f : Space n → ℝ} (hf : Measurable f) :
    Measurable fun y => ((f y : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp hf
theorem isSelfAdj_spectralOp (hC : FunctionalCalculus.Statement)
    (hE : IsPVM E) {g : Space n → ℂ} (hg : Measurable g)
    (him : ∀ y, (g y).im = 0) : IsSelfAdj (spectralOp E g) := by
  obtain ⟨-, -, a, -⟩ := hC n 1 H E hE g g hg hg 0
  exact a.2 him
theorem isSpectralIntegralOp_spectralOp (hC : FunctionalCalculus.Statement)
    (hE : IsPVM E) {g : Space n → ℂ} (hg : Measurable g) :
    RealizesSpectralIntegral E g (spectralOp E g) :=
  (hC n 1 H E hE g g hg hg 0).1.isOp
theorem isPVM_pushforward (hC : FunctionalCalculus.Statement)
    (hE : IsPVM E) {κ : Space n → Space 1} (hκ : Measurable κ) :
    IsPVM (pushforward E κ hκ) := by
  obtain ⟨-, -, -, -, -, -, -, im, -⟩ := hC n 1 H E hE 0 0 measurable_const measurable_const 0
  exact (im κ hκ).1
theorem spectralOp_pushforward (hC : FunctionalCalculus.Statement)
    (hE : IsPVM E) {κ : Space n → Space 1} (hκ : Measurable κ)
    {h : Space 1 → ℂ} (hh : Measurable h) :
    spectralOp (pushforward E κ hκ) h = spectralOp E (h ∘ κ) := by
  obtain ⟨-, -, -, -, -, -, -, im, -⟩ := hC n 1 H E hE 0 0 measurable_const measurable_const 0
  exact (im κ hκ).2 h hh
theorem isSpectralIntegralOp_pushforward (hC : FunctionalCalculus.Statement)
    (hE : IsPVM E) {κ : Space n → Space 1} (hκ : Measurable κ)
    {h : Space 1 → ℂ} (hh : Measurable h) :
    RealizesSpectralIntegral (pushforward E κ hκ) h (spectralOp E (h ∘ κ)) := by
  rw [← spectralOp_pushforward hC hE hκ hh]
  exact isSpectralIntegralOp_spectralOp hC (isPVM_pushforward hC hE hκ) hh
theorem isSpectralResolution_pushforward (hC : FunctionalCalculus.Statement)
    (hE : IsPVM E) {f : Space n → ℝ} (hf : Measurable f) :
    IsSpectralResolution (spectralOp E fun y => ((f y : ℝ) : ℂ))
      (pushforward E (liftToLine f) (measurable_liftToLine hf)) :=
  ⟨isPVM_pushforward hC hE _, integralOp_of_op
    (isSpectralIntegralOp_pushforward hC hE (measurable_liftToLine hf) measurable_lineCoord)⟩
theorem spectralResolution_spectralOp (hC : FunctionalCalculus.Statement)
    (hS : SelfAdjoint.SpectralTheorem) (hE : IsPVM E) {f : Space n → ℝ}
    (hf : Measurable f) :
    spectralResolution (spectralOp E fun y => ((f y : ℝ) : ℂ)) =
      pushforward E (liftToLine f) (measurable_liftToLine hf) :=
  spectralResolution_eq hS
    (isSelfAdj_spectralOp hC hE (measurable_ofReal_comp hf) fun _ => Complex.ofReal_im _)
    (isSpectralResolution_pushforward hC hE hf)
theorem borelCalculus_spectralOp (hC : FunctionalCalculus.Statement)
    (hS : SelfAdjoint.SpectralTheorem) (hE : IsPVM E) {f : Space n → ℝ}
    (hf : Measurable f) {h : ℝ → ℂ} (hh : Measurable h) :
    PartialMapEq (borelCalculus (spectralOp E fun y => ((f y : ℝ) : ℂ)) h)
      (spectralIntegral E fun y => h (f y)) := by
  unfold borelCalculus
  rw [spectralResolution_spectralOp hC hS hE hf]
  have hm : Measurable fun y => h (f y) := hh.comp hf
  exact partialMapEq_of_isSpectralIntegralOp
    (isSpectralIntegralOp_pushforward hC hE (measurable_liftToLine hf) (measurable_liftFromLine hh))
    (isSpectralIntegralOp_spectralOp hC hE hm)
end Pushforward
theorem pushforward_rule (hC : FunctionalCalculus.Statement) (hS : SelfAdjoint.SpectralTheorem) :
    Pushforward H := by
  intro n hn E hE f hf
  have : NeZero n := ⟨by omega⟩
  have hm := measurable_ofReal_comp hf
  exact ⟨_, integralOp_of_op (isSpectralIntegralOp_spectralOp hC hE hm),
    isSelfAdj_spectralOp hC hE hm fun _ => Complex.ofReal_im _,
    spectralResolution_spectralOp hC hS hE hf, fun h hh => borelCalculus_spectralOp hC hS hE hf hh⟩
theorem coordinates_rule (hC : FunctionalCalculus.Statement)
    (hS : SelfAdjoint.SpectralTheorem) : Coordinates H := by
  intro n hn E hE
  have : NeZero n := ⟨by omega⟩
  have hm : ∀ i : Fin n, Measurable fun y => ((realCoord i y : ℝ) : ℂ) := fun i =>
    measurable_ofReal_comp (measurable_realCoord i)
  have hsa : ∀ i : Fin n, IsSelfAdj
      (spectralOp E fun y => ((realCoord i y : ℝ) : ℂ)) := fun i =>
    isSelfAdj_spectralOp hC hE (hm i) fun _ => Complex.ofReal_im _
  have hsp := fun i : Fin n => spectralResolution_spectralOp hC hS hE (measurable_realCoord i)
  refine ⟨fun i => spectralOp E fun y => ((realCoord i y : ℝ) : ℂ),
    fun i => integralOp_of_op (isSpectralIntegralOp_spectralOp hC hE (hm i)), hsa, hsp,
    hsa, fun i k Δ Δ' => ?_⟩
  rw [hsp i, hsp k]
  show pushforward E _ _ Δ * pushforward E _ _ Δ' = pushforward E _ _ Δ' * pushforward E _ _ Δ
  simp only [pushforward]
  rw [← hE.map_inter, ← hE.map_inter]
  exact congrArg E (Subtype.ext (Set.inter_comm _ _))
section Conjugation
variable {n : ℕ} [NeZero n] {E : BorelSubset n → H →L[ℂ] H}
theorem conj_partialMapEq {C B : UnboundedOp H} {E' : BorelSubset n → H →L[ℂ] H} {f : Space n → ℂ}
    (U : UnitaryMap H H) (hB : B = FormsOperators.unitaryConjugate U C)
    (h₁ : RealizesSpectralIntegral E f C) (h₂ : RealizesSpectralIntegral E' f B) :
    PartialMapEq (spectralIntegral E' f) (conjPartialMap U (spectralIntegral E f)) := by
  subst hB
  have hdom : sqIntegrableDomain E' f = U '' sqIntegrableDomain E f := by
    rw [← h₂.1, ← h₁.1]
    ext x
    simp [FormsOperators.unitaryConjugate]
  refine ⟨hdom, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨φ, hφ, rfl⟩ := hdom ▸ hx
  rw [conjPartialMap_apply U _ hφ]
  have hφ' : φ ∈ C.domain := by
    show φ ∈ (C.domain : Set H)
    rw [h₁.1]
    exact hφ
  obtain ⟨_, v₁⟩ := h₁.2 ⟨φ, hφ'⟩
  obtain ⟨_, v₂⟩ := h₂.2 ⟨U φ, Submodule.mem_map_of_mem hφ'⟩
  have v₃ := FormsOperators.unitaryConjugate_apply U C ⟨φ, hφ'⟩
  exact (congrArg U v₁).trans (v₃.symm.trans v₂.symm)
end Conjugation
theorem unitaryConjugation_rule (hC : FunctionalCalculus.Statement)
    (hS : SelfAdjoint.SpectralTheorem) : UnitaryConjugation H := by
  intro A hA U
  obtain ⟨hE, hI⟩ := isSpectralResolution_self hS hA
  have hop := op_of_integralOp hI
  have hrule : ∀ {f : Space 1 → ℂ}, Measurable f →
      IsPVM (unitaryConj U (spectralResolution A)) ∧
      spectralOp (unitaryConj U (spectralResolution A)) f =
        FormsOperators.unitaryConjugate U (spectralOp (spectralResolution A) f) := by
    intro f hf
    obtain ⟨-, -, -, -, -, -, -, -, cj, -⟩ := hC 1 1 H _ hE f f hf hf 0
    exact cj U
  have hpvm := (hrule measurable_lineCoord).1
  have hAeq : spectralOp (spectralResolution A) lineCoord = A :=
    eq_of_isSpectralIntegralOp (isSpectralIntegralOp_spectralOp hC hE measurable_lineCoord) hop
  have hB : spectralOp (unitaryConj U (spectralResolution A)) lineCoord =
      FormsOperators.unitaryConjugate U A := by
    rw [(hrule measurable_lineCoord).2, hAeq]
  have hBop : RealizesSpectralIntegral (unitaryConj U (spectralResolution A)) lineCoord
      (FormsOperators.unitaryConjugate U A) := by
    rw [← hB]
    exact isSpectralIntegralOp_spectralOp hC hpvm measurable_lineCoord
  have hsa : IsSelfAdj (FormsOperators.unitaryConjugate U A) := by
    rw [← hB]
    exact isSelfAdj_spectralOp hC hpvm measurable_lineCoord fun _ => Complex.ofReal_im _
  have hsp : spectralResolution (FormsOperators.unitaryConjugate U A) =
      unitaryConj U (spectralResolution A) :=
    spectralResolution_eq hS hsa ⟨hpvm, integralOp_of_op hBop⟩
  have hmaps : ∀ h : ℝ → ℂ, Measurable h →
      PartialMapEq (spectralIntegral (unitaryConj U (spectralResolution A)) (liftFromLine h))
        (conjPartialMap U (spectralIntegral (spectralResolution A) (liftFromLine h))) := by
    intro h hh
    have hl := measurable_liftFromLine hh
    exact conj_partialMapEq U (hrule hl).2 (isSpectralIntegralOp_spectralOp hC hE hl)
      (isSpectralIntegralOp_spectralOp hC hpvm hl)
  refine ⟨hsa, hsp, fun h hh => ?_, fun T hT hcom => ?_⟩
  · unfold borelCalculus
    rw [hsp]
    exact hmaps h hh
  · have hfix : unitaryConj U (spectralResolution A) = spectralResolution A := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hb⟩ := hS H A hA
      funext Δ
      have hc : (U.toContinuousLinearEquiv : H →L[ℂ] H) * spectralResolution A Δ =
          spectralResolution A Δ * (U.toContinuousLinearEquiv : H →L[ℂ] H) := hb T hT _ hcom Δ
      show (U.toContinuousLinearEquiv : H →L[ℂ] H) * spectralResolution A Δ *
        (U.symm.toContinuousLinearEquiv : H →L[ℂ] H) = spectralResolution A Δ
      rw [hc]
      ext ψ
      simp
    refine ⟨hfix, fun h hh => ?_⟩
    have hm := hmaps h hh
    rw [hfix] at hm
    exact partialMapEq_symm hm
section Bounds
variable {E : BorelSubset 1 → H →L[ℂ] H} {A : UnboundedOp H}
theorem isFiniteMeasure_diagonalMeasure (hI : BoundedBorelCalculusTheorem)
    (hE : IsPVM E) (ψ : H) : IsFiniteMeasure (diagonalMeasure E ψ) := by
  refine ⟨?_⟩
  rw [(hI 1 le_rfl H E hE).1.2.2.1 ψ]
  exact ENNReal.ofReal_lt_top
theorem diagonalMeasure_real_univ (hI : BoundedBorelCalculusTheorem)
    (hE : IsPVM E) (ψ : H) :
    (diagonalMeasure E ψ).real Set.univ = ‖ψ‖ ^ 2 := by
  rw [measureReal_def, (hI 1 le_rfl H E hE).1.2.2.1 ψ, ENNReal.toReal_ofReal (sq_nonneg _)]
theorem ae_mem_diagonalMeasure (hI : BoundedBorelCalculusTheorem)
    (hE : IsPVM E) (Δ : BorelSubset 1) (ψ : H) :
    ∀ᵐ y ∂(diagonalMeasure E (E Δ ψ)), y ∈ Δ.1 := by
  have h := (hI 1 le_rfl H E hE).1.2.2.2.2.2 ψ ⟨Δ.1ᶜ, Δ.2.compl⟩ Δ
  have h₀ : ((⟨Δ.1ᶜ, Δ.2.compl⟩ : BorelSubset 1) ∩ Δ).1 = ∅ := Set.compl_inter_self _
  rw [h₀, measure_empty] at h
  rw [ae_iff]
  exact h
theorem mem_domain_of_bounded (hC : FunctionalCalculus.Statement)
    (hI : BoundedBorelCalculusTheorem) (hE : IsPVM E)
    (hop : RealizesSpectralIntegral E lineCoord A) (Δ : BorelSubset 1) {M : ℝ}
    (hM : ∀ y ∈ Δ.1, |y 0| ≤ M) (ψ : H) :
    ∃ hχ : E Δ ψ ∈ A.domain, ⟪E Δ ψ, A ⟨E Δ ψ, hχ⟩⟫_ℂ =
      ((∫ y, y 0 ∂(diagonalMeasure E (E Δ ψ)) : ℝ) : ℂ) := by
  have := isFiniteMeasure_diagonalMeasure hI hE (E Δ ψ)
  have hae := ae_mem_diagonalMeasure hI hE Δ ψ
  have hd : E Δ ψ ∈ sqIntegrableDomain E lineCoord := by
    show ∫⁻ y, ‖lineCoord y‖ₑ ^ 2 ∂(diagonalMeasure E (E Δ ψ)) < ∞
    calc ∫⁻ y, ‖lineCoord y‖ₑ ^ 2 ∂(diagonalMeasure E (E Δ ψ))
        ≤ ∫⁻ _, ENNReal.ofReal M ^ 2 ∂(diagonalMeasure E (E Δ ψ)) := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          have h₁ : ‖lineCoord y‖ₑ ≤ ENNReal.ofReal M := by
            rw [← ofReal_norm_eq_enorm]
            refine ENNReal.ofReal_le_ofReal ?_
            show ‖((y 0 : ℝ) : ℂ)‖ ≤ M
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact hM y hy
          gcongr
      _ < ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top (by finiteness) (measure_lt_top _ _)
  have hχ : E Δ ψ ∈ A.domain := by
    show E Δ ψ ∈ (A.domain : Set H)
    rw [hop.1]
    exact hd
  refine ⟨hχ, ?_⟩
  obtain ⟨-, s, -⟩ := hC 1 1 H E hE lineCoord lineCoord measurable_lineCoord
    measurable_lineCoord 0
  obtain ⟨_, hv⟩ := hop.2 ⟨E Δ ψ, hχ⟩
  rw [← hv, (s _ hd hd).2.2.2]
  exact integral_complex_ofReal
theorem integrable_coord_of_bounded (hI : BoundedBorelCalculusTheorem)
    (hE : IsPVM E) (Δ : BorelSubset 1) {M : ℝ}
    (hM : ∀ y ∈ Δ.1, |y 0| ≤ M) (ψ : H) :
    Integrable (fun y : Space 1 => y 0) (diagonalMeasure E (E Δ ψ)) := by
  have := isFiniteMeasure_diagonalMeasure hI hE (E Δ ψ)
  refine Integrable.of_bound (by fun_prop) M ?_
  exact (ae_mem_diagonalMeasure hI hE Δ ψ).mono fun y hy => hM y hy
theorem eq_zero_of_form_le (hC : FunctionalCalculus.Statement)
    (hI : BoundedBorelCalculusTheorem) (hE : IsPVM E)
    (hop : RealizesSpectralIntegral E lineCoord A) {c ε : ℝ} (hε : 0 < ε)
    (hb : ∀ χ : A.domain, ⟪(χ : H), A χ⟫_ℂ ≤ ((c * ‖(χ : H)‖ ^ 2 : ℝ) : ℂ))
    (Δ : BorelSubset 1) {M : ℝ} (hM : ∀ y ∈ Δ.1, |y 0| ≤ M) (hΔ : ∀ y ∈ Δ.1, c + ε ≤ y 0) :
    E Δ = 0 := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  have := isFiniteMeasure_diagonalMeasure hI hE (E Δ ψ)
  obtain ⟨hχ, hexp⟩ := mem_domain_of_bounded hC hI hE hop Δ hM ψ
  have h₁ := hb ⟨E Δ ψ, hχ⟩
  simp only at h₁
  rw [hexp, Complex.real_le_real] at h₁
  have h₂ : ∫ _, (c + ε) ∂(diagonalMeasure E (E Δ ψ)) ≤ ∫ y, y 0 ∂(diagonalMeasure E (E Δ ψ)) :=
    integral_mono_ae (integrable_const _) (integrable_coord_of_bounded hI hE Δ hM ψ)
      ((ae_mem_diagonalMeasure hI hE Δ ψ).mono fun y hy => hΔ y hy)
  rw [integral_const, diagonalMeasure_real_univ hI hE, smul_eq_mul] at h₂
  have h₃ : ‖E Δ ψ‖ ^ 2 * ε ≤ 0 := by nlinarith
  have h₄ : ‖E Δ ψ‖ ^ 2 ≤ 0 := by
    by_contra hn
    exact absurd h₃ (not_le.mpr (mul_pos (not_le.mp hn) hε))
  have h₅ : ‖E Δ ψ‖ = 0 := by nlinarith [norm_nonneg (E Δ ψ)]
  simpa using h₅
theorem eq_zero_of_le_form (hC : FunctionalCalculus.Statement)
    (hI : BoundedBorelCalculusTheorem) (hE : IsPVM E)
    (hop : RealizesSpectralIntegral E lineCoord A) {c ε : ℝ} (hε : 0 < ε)
    (hb : ∀ χ : A.domain, ((c * ‖(χ : H)‖ ^ 2 : ℝ) : ℂ) ≤ ⟪(χ : H), A χ⟫_ℂ)
    (Δ : BorelSubset 1) {M : ℝ} (hM : ∀ y ∈ Δ.1, |y 0| ≤ M) (hΔ : ∀ y ∈ Δ.1, y 0 ≤ c - ε) :
    E Δ = 0 := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  have := isFiniteMeasure_diagonalMeasure hI hE (E Δ ψ)
  obtain ⟨hχ, hexp⟩ := mem_domain_of_bounded hC hI hE hop Δ hM ψ
  have h₁ := hb ⟨E Δ ψ, hχ⟩
  simp only at h₁
  rw [hexp, Complex.real_le_real] at h₁
  have h₂ : ∫ y, y 0 ∂(diagonalMeasure E (E Δ ψ)) ≤ ∫ _, (c - ε) ∂(diagonalMeasure E (E Δ ψ)) :=
    integral_mono_ae (integrable_coord_of_bounded hI hE Δ hM ψ) (integrable_const _)
      ((ae_mem_diagonalMeasure hI hE Δ ψ).mono fun y hy => hΔ y hy)
  rw [integral_const, diagonalMeasure_real_univ hI hE, smul_eq_mul] at h₂
  have h₃ : ‖E Δ ψ‖ ^ 2 * ε ≤ 0 := by nlinarith
  have h₄ : ‖E Δ ψ‖ ^ 2 ≤ 0 := by
    by_contra hn
    exact absurd h₃ (not_le.mpr (mul_pos (not_le.mp hn) hε))
  have h₅ : ‖E Δ ψ‖ = 0 := by nlinarith [norm_nonneg (E Δ ψ)]
  simpa using h₅
end Bounds
def iccSet (a b : ℝ) : BorelSubset 1 :=
  ⟨{y | y 0 ∈ Set.Icc a b},
    (isClosed_Icc.preimage (f := fun y : Space 1 => y 0) (by fun_prop)).measurableSet⟩
theorem abs_le_of_mem_iccSet {a b : ℝ} {y : Space 1} (hy : y ∈ (iccSet a b).1) :
    |y 0| ≤ max |a| |b| :=
  abs_le_max_abs_abs hy.1 hy.2
section Rays
variable {E : BorelSubset 1 → H →L[ℂ] H}
theorem eq_zero_of_iUnion (hI : BoundedBorelCalculusTheorem)
    (hE : IsPVM E) (Δ : BorelSubset 1) (s : ℕ → BorelSubset 1)
    (hs : ∀ k, E (s k) = 0) (hc : Δ.1 = ⋃ k, (s k).1) : E Δ = 0 := by
  refine (hI 1 le_rfl H E hE).2.1.2.2 (Set.range s) Δ (Set.countable_range s) ?_ ?_
  · rintro _ ⟨k, rfl⟩
    exact hs k
  · rw [hc]
    ext y
    simp
theorem exists_mem_Icc_of_lt {c x : ℝ} (h : c < x) :
    ∃ k : ℕ, x ∈ Set.Icc (c + 1 / ((k : ℝ) + 1)) (c + (k + 1)) := by
  have hd : 0 < x - c := sub_pos.mpr h
  obtain ⟨k₁, hk₁⟩ := exists_nat_ge (1 / (x - c))
  obtain ⟨k₂, hk₂⟩ := exists_nat_ge (x - c)
  refine ⟨max k₁ k₂, ?_, ?_⟩
  · have hk : (k₁ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_left _ _
    have hp : (0 : ℝ) < ((max k₁ k₂ : ℕ) : ℝ) + 1 := by positivity
    have : 1 / (((max k₁ k₂ : ℕ) : ℝ) + 1) ≤ x - c := by
      rw [div_le_iff₀ hp]
      rw [div_le_iff₀ hd] at hk₁
      nlinarith
    linarith
  · have hk : (k₂ : ℝ) ≤ (max k₁ k₂ : ℕ) := by exact_mod_cast le_max_right _ _
    linarith
theorem ioiSet_eq_zero (hC : FunctionalCalculus.Statement)
    (hI : BoundedBorelCalculusTheorem) {A : UnboundedOp H}
    (hE : IsPVM E) (hop : RealizesSpectralIntegral E lineCoord A) {c : ℝ}
    (hb : ∀ χ : A.domain, ⟪(χ : H), A χ⟫_ℂ ≤ ((c * ‖(χ : H)‖ ^ 2 : ℝ) : ℂ)) :
    E (ioiSet c) = 0 := by
  refine eq_zero_of_iUnion hI hE _
    (fun k => iccSet (c + 1 / ((k : ℝ) + 1)) (c + (k + 1))) (fun k => ?_) ?_
  · exact eq_zero_of_form_le hC hI hE hop (ε := 1 / ((k : ℝ) + 1)) (by positivity) hb _
      (fun y hy => abs_le_of_mem_iccSet hy) fun y hy => hy.1
  · ext y
    simp only [Set.mem_iUnion]
    constructor
    · intro hy
      exact exists_mem_Icc_of_lt hy
    · rintro ⟨k, hk⟩
      have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      exact lt_of_lt_of_le (by linarith) hk.1
theorem iioSet_eq_zero (hC : FunctionalCalculus.Statement)
    (hI : BoundedBorelCalculusTheorem) {A : UnboundedOp H}
    (hE : IsPVM E) (hop : RealizesSpectralIntegral E lineCoord A) {c : ℝ}
    (hb : ∀ χ : A.domain, ((c * ‖(χ : H)‖ ^ 2 : ℝ) : ℂ) ≤ ⟪(χ : H), A χ⟫_ℂ) :
    E (iioSet c) = 0 := by
  refine eq_zero_of_iUnion hI hE _
    (fun k => iccSet (c - (k + 1)) (c - 1 / ((k : ℝ) + 1))) (fun k => ?_) ?_
  · exact eq_zero_of_le_form hC hI hE hop (ε := 1 / ((k : ℝ) + 1)) (by positivity) hb _
      (fun y hy => abs_le_of_mem_iccSet hy) fun y hy => hy.2
  · ext y
    simp only [Set.mem_iUnion]
    constructor
    · intro hy
      have hy' : y 0 < c := hy
      obtain ⟨k, hk⟩ := exists_mem_Icc_of_lt (neg_lt_neg hy')
      refine ⟨k, ?_, ?_⟩
      · have := hk.2
        linarith
      · have := hk.1
        linarith
    · rintro ⟨k, hk⟩
      have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      exact lt_of_le_of_lt hk.2 (by linarith)
theorem eq_zero_of_subset_rays (hI : BoundedBorelCalculusTheorem)
    (hE : IsPVM E) {a b : ℝ} (ha : E (iioSet a) = 0)
    (hb : E (ioiSet b) = 0) (N : BorelSubset 1) (hN : ∀ y ∈ N.1, y 0 < a ∨ b < y 0) :
    E N = 0 := by
  have hU : E ⟨(iioSet a).1 ∪ (ioiSet b).1,
      (iioSet a).2.union (ioiSet b).2⟩ = 0 := by
    refine eq_zero_of_iUnion hI hE _ (fun k => if k = 0 then iioSet a else ioiSet b)
      (fun k => ?_) ?_
    · by_cases hk : k = 0
      · simpa [hk] using ha
      · simpa [hk] using hb
    · ext y
      simp only [Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro (h | h)
        · exact ⟨0, by simpa using h⟩
        · exact ⟨1, by simpa using h⟩
      · rintro ⟨k, hk⟩
        by_cases h0 : k = 0
        · left
          simpa [h0] using hk
        · right
          simpa [h0] using hk
  exact (hI 1 le_rfl H E hE).2.1.2.1 ⟨(iioSet a).1 ∪ (ioiSet b).1,
    (iioSet a).2.union (ioiSet b).2⟩ N (fun y hy => hN y hy) hU
end Rays
theorem ofCLM_apply (T : H →L[ℂ] H) (χ : (ofCLM T).domain) :
    ofCLM T χ = T χ := rfl
theorem inner_le_of_isPositiveBounded {T : H →L[ℂ] H} (hT : IsPositiveBounded T) {C : ℝ}
    (hC : ∀ ψ, ‖T ψ‖ ≤ C * ‖ψ‖) (ψ : H) : ⟪ψ, T ψ⟫_ℂ ≤ ((C * ‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  have h₀ := hT ψ
  rw [Complex.le_def] at h₀ ⊢
  refine ⟨?_, by
    rw [Complex.ofReal_im]
    exact h₀.2.symm⟩
  have h₁ : (⟪ψ, T ψ⟫_ℂ).re ≤ ‖ψ‖ * ‖T ψ‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h₂ : ‖ψ‖ * ‖T ψ‖ ≤ ‖ψ‖ * (C * ‖ψ‖) := mul_le_mul_of_nonneg_left (hC ψ) (norm_nonneg _)
  simp only [Complex.ofReal_re]
  nlinarith
theorem formBounds_rule (hC : FunctionalCalculus.Statement)
    (hS : SelfAdjoint.SpectralTheorem) (hI : BoundedBorelCalculusTheorem) :
    FormBounds H := by
  have hspec : ∀ {A : UnboundedOp H}, IsSelfAdj A →
      IsPVM (spectralResolution A) ∧
        RealizesSpectralIntegral (spectralResolution A) lineCoord A := fun hA =>
    ⟨(isSpectralResolution_self hS hA).1,
      op_of_integralOp (isSpectralResolution_self hS hA).2⟩
  refine ⟨fun A hA c => ?_, fun A hA => ?_, fun T hsa hpos hcon => ?_⟩
  · obtain ⟨hE, hop⟩ := hspec hA
    exact ⟨fun hb => ioiSet_eq_zero hC hI hE hop hb, fun hb => iioSet_eq_zero hC hI hE hop hb⟩
  · obtain ⟨hE, hop⟩ := hspec hA
    constructor
    · intro hn
      have h₀ : spectralResolution A (iioSet 0) = 0 := iioSet_eq_zero hC hI hE hop fun χ => by
        simpa using hn χ
      have hc : iciZeroSetᶜ = iioSet 0 := Subtype.ext (by
        ext y
        exact not_le (a := (0 : ℝ)) (b := y 0))
      show spectralResolution A iciZeroSetᶜ = 0
      rw [hc]
      exact h₀
    · intro hcar χ
      obtain ⟨-, -, -, -, o, -⟩ := hC 1 1 H _ hE lineCoord lineCoord
        measurable_lineCoord measurable_lineCoord 0
      have hnn := o.nonneg ⟨iciZeroSetᶜ, hcar, fun y hy => by
        have hy' : 0 ≤ y 0 := not_not.mp hy
        exact Complex.zero_le_real.mpr hy'⟩
      obtain ⟨hχ, hv⟩ := hop.2 χ
      rw [← hv]
      exact hnn ⟨χ, hχ⟩
  · obtain ⟨hE, hop⟩ := hspec hsa
    have h₁ : spectralResolution (ofCLM T) (ioiSet 1) = 0 :=
      ioiSet_eq_zero hC hI hE hop fun χ =>
        inner_le_of_isPositiveBounded hpos (C := 1) (fun ψ => by simpa using hcon ψ) χ
    have h₀ : spectralResolution (ofCLM T) (iioSet 0) = 0 :=
      iioSet_eq_zero hC hI hE hop fun χ => by
        rw [ofCLM_apply]
        simpa using hpos χ
    refine eq_zero_of_subset_rays hI hE h₀ h₁ _ fun y hy => ?_
    have hy' : ¬ (0 ≤ y 0 ∧ y 0 ≤ 1) := hy
    by_contra hn
    push_neg at hn
    exact hy' hn
theorem sqrtOf_eq_sqrt {x : ℝ} (hx : 0 ≤ x) : RealPower.sqrtOf x = Real.sqrt x := by apply _root_.YangMills.Construction.TraceBound.sqrtOf_eq_sqrt <;> assumption
theorem zeroExtend_sqrtOnNonneg :
    zeroExtend iciZeroSet sqrtOnNonneg =
      fun y => ((Real.sqrt (y 0) : ℝ) : ℂ) := by
  funext y
  unfold zeroExtend sqrtOnNonneg
  by_cases h : y ∈ iciZeroSet.1
  · rw [dif_pos h, sqrtOf_eq_sqrt h]
  · have h' : y 0 < 0 := not_le.mp h
    rw [dif_neg h, Real.sqrt_eq_zero_of_nonpos h'.le]
    simp
def coordSq (y : Space 1) : ℝ := y 0 * y 0
theorem measurable_coordSq : Measurable coordSq := by
  unfold coordSq
  fun_prop
def coordSqrt (y : Space 1) : ℂ := ((Real.sqrt (y 0) : ℝ) : ℂ)
theorem measurable_coordSqrt : Measurable coordSqrt :=
  (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
    (by fun_prop : Continuous fun y : Space 1 => y 0))).measurable
theorem squareRoot_rule (hC : FunctionalCalculus.Statement)
    (hS : SelfAdjoint.SpectralTheorem) (hI : BoundedBorelCalculusTheorem) :
    SquareRoot H := by
  intro T B hTsa _ hBsa hBpos hsq
  obtain ⟨hE, hIop⟩ := isSpectralResolution_self hS hBsa
  have hop := op_of_integralOp hIop
  have hlc := measurable_lineCoord
  have h₀ : spectralResolution (ofCLM B) (iioSet 0) = 0 :=
    iioSet_eq_zero hC hI hE hop fun χ => by
      rw [ofCLM_apply]
      simpa using hBpos χ
  have h₁ : spectralResolution (ofCLM B) (ioiSet ‖B‖) = 0 :=
    ioiSet_eq_zero hC hI hE hop fun χ => inner_le_of_isPositiveBounded hBpos (fun ψ => B.le_opNorm ψ) χ
  have hnull : spectralResolution (ofCLM B) ⟨{y | y 0 < 0 ∨ ‖B‖ < y 0},
      (iioSet 0).2.union (ioiSet ‖B‖).2⟩ = 0 :=
    eq_zero_of_subset_rays hI hE h₀ h₁ _ fun y hy => hy
  have hbd : EssBounded (spectralResolution (ofCLM B)) lineCoord :=
    ⟨‖B‖, _, hnull, fun y hy => by
      have hy' : ¬ (y 0 < 0 ∨ ‖B‖ < y 0) := hy
      push_neg at hy'
      show ‖((y 0 : ℝ) : ℂ)‖ ≤ ‖B‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy'.1]
      exact hy'.2⟩
  obtain ⟨-, -, -, -, o, -⟩ := hC 1 1 H _ hE lineCoord lineCoord hlc hlc 0
  obtain ⟨B₁, B₂, e₁, e₂, e₃, -⟩ := o.mul hbd hbd
  have hB : ∀ {B' : H →L[ℂ] H},
      SpectralIntegralIs (spectralResolution (ofCLM B)) lineCoord B' → B' = B := by
    intro B' he
    refine ContinuousLinearMap.ext fun ψ => ?_
    obtain ⟨hd, hv⟩ := hop.2 ⟨ψ, Submodule.mem_top⟩
    have h₂ := he.2 ⟨ψ, hd⟩
    exact h₂.symm.trans hv
  rw [hB e₁, hB e₂, hsq] at e₃
  have hsqm := measurable_coordSq
  have hg : (fun y => ((coordSq y : ℝ) : ℂ)) =
      fun y => lineCoord y * lineCoord y := by
    funext y
    simp [coordSq, lineCoord, coordFn]
  have hTop : RealizesSpectralIntegral (spectralResolution (ofCLM B))
      (fun y => ((coordSq y : ℝ) : ℂ)) (ofCLM T) := by
    rw [hg]
    refine ⟨by rw [e₃.1]; exact Submodule.top_coe, fun χ => ?_⟩
    have hd : (χ : H) ∈ sqIntegrableDomain (spectralResolution (ofCLM B))
        (fun y => lineCoord y * lineCoord y) := by
      rw [e₃.1]
      trivial
    exact ⟨hd, e₃.2 ⟨χ, hd⟩⟩
  have hTeq := eq_of_isSpectralIntegralOp
    (isSpectralIntegralOp_spectralOp hC hE (measurable_ofReal_comp hsqm)) hTop
  have hspT := spectralResolution_spectralOp hC hS hE hsqm
  rw [hTeq] at hspT
  rw [hspT, zeroExtend_sqrtOnNonneg]
  refine integralOp_of_op ?_
  have hκ := measurable_liftToLine hsqm
  have hrm := measurable_coordSqrt
  have h₂ := isSpectralIntegralOp_pushforward hC hE hκ hrm
  have hcm : Measurable (coordSqrt ∘ liftToLine coordSq) := hrm.comp hκ
  obtain ⟨-, -, -, -, o', -⟩ := hC 1 1 H _ hE _ lineCoord hcm hlc 0
  have hdiff : IsNull (spectralResolution (ofCLM B)) (disagreementSet hcm hlc) := by
    refine (hI 1 le_rfl H _ hE).2.1.2.1 (iioSet 0) _ (fun y hy => ?_) h₀
    by_contra hn
    have hn' : 0 ≤ y 0 := not_lt.mp hn
    refine hy ?_
    show ((Real.sqrt (y 0 * y 0) : ℝ) : ℂ) = ((y 0 : ℝ) : ℂ)
    rw [Real.sqrt_mul_self hn']
  have heq : spectralOp (spectralResolution (ofCLM B))
      (coordSqrt ∘ liftToLine coordSq) = ofCLM B :=
    (o'.eq_of_null hdiff).trans
      (eq_of_isSpectralIntegralOp (isSpectralIntegralOp_spectralOp hC hE hlc) hop)
  rw [heq] at h₂
  exact h₂
theorem allRules_holds (hC : FunctionalCalculus.Statement) (hS : SelfAdjoint.SpectralTheorem)
    (hI : BoundedBorelCalculusTheorem) : AllRules :=
  fun _ _ _ _ => ⟨formBounds_rule hC hS hI, pushforward_rule hC hS, coordinates_rule hC hS,
    unitaryConjugation_rule hC hS, squareRoot_rule hC hS hI⟩
end YangMills.Construction.EuclideanBorel.SpectralRules
