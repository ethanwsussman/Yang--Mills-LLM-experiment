import YangMills.Construction.SpectralCalculus.FormCompletionAndExtension
import YangMills.Construction.SpectralMeasures.UniquenessOfComplexMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanBorel.BoundedCalculusProof
variable {n : ℕ}
theorem isBoundedMeasurableFn_indicator (c : ℂ) (Δ : BorelSubset n) :
    IsBoundedMeasurableFn (Δ.1.indicator fun _ => c) := by
  refine ⟨measurable_const.indicator Δ.2, ‖c‖, fun y => ?_⟩
  by_cases h : y ∈ Δ.1
  · simp [h]
  · simp [h]
theorem isBoundedMeasurableFn_add {f g : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) : IsBoundedMeasurableFn fun y => f y + g y := by apply _root_.YangMills.Construction.EuclideanBorel.FunctionalCalculus.boundedFn_add <;> assumption
theorem isBoundedMeasurableFn_mul {f g : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) : IsBoundedMeasurableFn fun y => f y * g y := by apply _root_.YangMills.Construction.PositiveFormReconstruction.CompletionEnergyBound.isBoundedMeasurableFn_mul <;> assumption
theorem isBoundedMeasurableFn_const (c : ℂ) : IsBoundedMeasurableFn fun _ : Space n => c :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩
theorem isBoundedMeasurableFn_conj {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f) :
    IsBoundedMeasurableFn fun y => conj (f y) := by apply _root_.YangMills.Construction.EuclideanBorel.FunctionalCalculus.boundedFn_conj <;> assumption
theorem isBoundedMeasurableFn_cutoff {f : Space n → ℂ} (hf : Measurable f) (k : ℕ) :
    IsBoundedMeasurableFn (cutoff f k) := by apply _root_.YangMills.Construction.EuclideanBorel.FunctionalCalculus.isBoundedMeasurableFn_cutoff <;> assumption
theorem isBoundedMeasurableFn_induction (P : (Space n → ℂ) → Prop)
    (hind : ∀ (c : ℂ) (Δ : BorelSubset n), P (Δ.1.indicator fun _ => c))
    (hadd : ∀ f g : Space n → ℂ, IsBoundedMeasurableFn f → IsBoundedMeasurableFn g →
      P f → P g → P fun y => f y + g y)
    (hlim : ∀ (f : Space n → ℂ) (u : ℕ → Space n → ℂ) (C : ℝ),
      IsBoundedMeasurableFn f → (∀ k, IsBoundedMeasurableFn (u k)) → (∀ k y, ‖u k y‖ ≤ C) →
      (∀ y, Tendsto (fun k => u k y) atTop (𝓝 (f y))) → (∀ k, P (u k)) → P f)
    (f : Space n → ℂ) (hf : IsBoundedMeasurableFn f) : P f := by
  have hs : ∀ s : SimpleFunc (Space n) ℂ, IsBoundedMeasurableFn s := fun s => by
    obtain ⟨C, hC⟩ := s.exists_forall_norm_le
    exact ⟨s.measurable, C, hC⟩
  have hsimple : ∀ s : SimpleFunc (Space n) ℂ, P s := by
    intro s
    induction s using SimpleFunc.induction with
    | @const c S hm =>
      have h := hind c ⟨S, hm⟩
      convert h using 1
      ext y
      by_cases hy : y ∈ S <;> simp [hy]
    | add hd h1 h2 =>
      rename_i s t
      exact hadd s t (hs s) (hs t) h1 h2
  obtain ⟨hm, C, hC⟩ := id hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hst := hm.stronglyMeasurable
  exact hlim f (fun k => hst.approxBounded C k) C hf (fun k => hs _)
    (fun k y => hst.norm_approxBounded_le hC0 k y)
    (fun y => hst.tendsto_approxBounded_of_norm_le (hC y)) (fun k => hsimple _)
theorem combination_integral_add (p : MeasureCombination n) {f g : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (hg : IsBoundedMeasurableFn g) :
    p.integral (fun y => f y + g y) = p.integral f + p.integral g := by apply _root_.YangMills.Construction.EuclideanBorel.MeasureUniqueness.combination_integral_add <;> assumption
theorem combination_integral_const_mul (p : MeasureCombination n) (c : ℂ) (f : Space n → ℂ) :
    p.integral (fun y => c * f y) = c * p.integral f := by apply _root_.YangMills.Construction.EuclideanBorel.MeasureUniqueness.combination_integral_const_mul <;> assumption
theorem combination_integral_indicator (p : MeasureCombination n) (c : ℂ) (Δ : BorelSubset n) :
    p.integral (Δ.1.indicator fun _ => c) = c * p.toSetFunction Δ := by
  simp only [MeasureCombination.integral, MeasureCombination.toSetFunction]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_indicator_const c Δ.2, Complex.real_smul]
  ring
theorem combination_integral_tendsto (p : MeasureCombination n) {f : Space n → ℂ}
    {u : ℕ → Space n → ℂ} {C : ℝ} (hu : ∀ k, IsBoundedMeasurableFn (u k))
    (hC : ∀ k y, ‖u k y‖ ≤ C) (hl : ∀ y, Tendsto (fun k => u k y) atTop (𝓝 (f y))) :
    Tendsto (fun k => p.integral (u k)) atTop (𝓝 (p.integral f)) := by
  simp only [MeasureCombination.integral]
  refine tendsto_finsetSum _ fun j _ => Tendsto.const_mul _ ?_
  have := p.isFinite j
  exact tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun k => (hu k).1.aestronglyMeasurable) (integrable_const C)
    (fun k => Eventually.of_forall (hC k)) (Eventually.of_forall hl)
theorem combination_integral_unique (p p' : MeasureCombination n)
    (h : p.toSetFunction = p'.toSetFunction)
    {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f) : p.integral f = p'.integral f := by
  refine isBoundedMeasurableFn_induction (fun f => p.integral f = p'.integral f) ?_ ?_ ?_ f hf
  · intro c Δ
    rw [combination_integral_indicator, combination_integral_indicator, h]
  · intro f g hf hg h1 h2
    rw [combination_integral_add p hf hg, combination_integral_add p' hf hg, h1, h2]
  · intro f u C _ hu hC hl hP
    exact tendsto_nhds_unique (combination_integral_tendsto p hu hC hl)
      ((combination_integral_tendsto p' hu hC hl).congr fun k => (hP k).symm)
theorem complexIntegral_eq_combination {ν : BorelSubset n → ℂ} (p : MeasureCombination n)
    (h : p.toSetFunction = ν) {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f) :
    complexIntegral ν f = p.integral f := by
  have hν : IsFiniteCombinationMeasure ν := ⟨p, h⟩
  rw [complexIntegral, dif_pos hν]
  exact combination_integral_unique _ _ ((Classical.choose_spec hν).trans h.symm) hf
theorem sum_fourthRoots_eq (F : ℂ → ℂ) :
    ∑ α ∈ ({1, Complex.I, -1, -Complex.I} : Finset ℂ), F α =
      F 1 + F Complex.I + F (-1) + F (-Complex.I) := by apply _root_.YangMills.Construction.SpectralCalculus.FormCompletionAndExtension.sum_fourthRootsOfUnity <;> assumption
def powersOfI : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]
theorem norm_quarterTurn (j : Fin 4) : ‖powersOfI j‖ = 1 := by
  fin_cases j <;> simp [powersOfI]
section HilbertSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem inner_polarization_sum (A : H →L[ℂ] H) (φ ψ : H) :
    ⟪φ, A ψ⟫_ℂ = (1 / 4 : ℂ) * ∑ α ∈ ({1, Complex.I, -1, -Complex.I} : Finset ℂ),
      conj α * ⟪φ + α • ψ, A (φ + α • ψ)⟫_ℂ := by
  have key : ∀ α : ℂ, ⟪φ + α • ψ, A (φ + α • ψ)⟫_ℂ =
      ⟪φ, A φ⟫_ℂ + α * ⟪φ, A ψ⟫_ℂ + conj α * ⟪ψ, A φ⟫_ℂ + conj α * α * ⟪ψ, A ψ⟫_ℂ := by
    intro α
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right]
    ring
  rw [sum_fourthRoots_eq]
  simp only [key, map_one, map_neg, Complex.conj_I]
  linear_combination ((⟪φ, A ψ⟫_ℂ - ⟪ψ, A φ⟫_ℂ) / 2) * Complex.I_sq
variable {E : BorelSubset n → H →L[ℂ] H}
theorem pvm_apply_apply (hE : IsPVM E) (Δ : BorelSubset n) (ψ : H) :
    E Δ (E Δ ψ) = E Δ ψ := by
  have h := congrArg (fun T : H →L[ℂ] H => T ψ) (hE.isOrthoProjection Δ).1
  simpa using h
theorem pvm_inner_symm (hE : IsPVM E) (Δ : BorelSubset n) (φ ψ : H) :
    ⟪φ, E Δ ψ⟫_ℂ = ⟪E Δ φ, ψ⟫_ℂ :=
  (hE.isOrthoProjection Δ).2 φ ψ
theorem diagonalForm_eq_norm_sq (hE : IsPVM E) (ψ : H) (Δ : BorelSubset n) :
    diagonalForm E ψ Δ = ((‖E Δ ψ‖ ^ 2 : ℝ) : ℂ) := by
  have h : ⟪ψ, E Δ ψ⟫_ℂ = ⟪E Δ ψ, E Δ ψ⟫_ℂ := by
    conv_lhs => rw [← pvm_apply_apply hE Δ ψ]
    exact pvm_inner_symm hE Δ ψ (E Δ ψ)
  rw [diagonalForm, h, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem diagonalMeasure_real (hE : IsPVM E) (ψ : H) (Δ : BorelSubset n) :
    (diagonalMeasure E ψ).real Δ.1 = ‖E Δ ψ‖ ^ 2 := by
  have h := (toMeasure_spec (hE.isPositiveMeasure ψ) Δ).2
  rw [diagonalForm_eq_norm_sq hE] at h
  exact (Complex.ofReal_injective h).symm
theorem diagonalMeasure_ne_top (hE : IsPVM E) (ψ : H) (Δ : BorelSubset n) :
    diagonalMeasure E ψ Δ.1 ≠ ∞ :=
  (toMeasure_spec (hE.isPositiveMeasure ψ) Δ).1
theorem diagonalMeasure_apply (hE : IsPVM E) (ψ : H) (Δ : BorelSubset n) :
    diagonalMeasure E ψ Δ.1 = ENNReal.ofReal (‖E Δ ψ‖ ^ 2) := by
  rw [← diagonalMeasure_real hE ψ Δ, Measure.real,
    ENNReal.ofReal_toReal (diagonalMeasure_ne_top hE ψ Δ)]
theorem diagonalMeasure_univ (hE : IsPVM E) (ψ : H) :
    diagonalMeasure E ψ Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  have h := diagonalMeasure_apply hE ψ ⊤
  rw [hE.map_top] at h
  simpa using h
theorem diagonalMeasure_isFinite (hE : IsPVM E) (ψ : H) :
    IsFiniteMeasure (diagonalMeasure E ψ) :=
  ⟨by rw [diagonalMeasure_univ hE]; exact ENNReal.ofReal_lt_top⟩
theorem diagonalMeasure_real_univ (hE : IsPVM E) (ψ : H) :
    (diagonalMeasure E ψ).real Set.univ = ‖ψ‖ ^ 2 := by
  rw [Measure.real, diagonalMeasure_univ hE, ENNReal.toReal_ofReal (by positivity)]
def polarizationCombination (hE : IsPVM E) (φ ψ : H) : MeasureCombination n where
  numTerms := 4
  one_le_numTerms := by norm_num
  coeff j := (1 / 4 : ℂ) * conj (powersOfI j)
  component j := diagonalMeasure E (φ + powersOfI j • ψ)
  isFinite _ := diagonalMeasure_isFinite hE _
theorem crossForm_eq_polarization (hE : IsPVM E) (φ ψ : H) (Δ : BorelSubset n) :
    crossForm E φ ψ Δ = (1 / 4 : ℂ) * ∑ α ∈ ({1, Complex.I, -1, -Complex.I} : Finset ℂ),
      conj α * diagonalForm E (φ + α • ψ) Δ :=
  inner_polarization_sum (E Δ) φ ψ
theorem polarizationCombination_toSetFunction (hE : IsPVM E) (φ ψ : H) :
    (polarizationCombination hE φ ψ).toSetFunction = crossForm E φ ψ := by
  funext Δ
  have hr : ∀ χ : H, (((diagonalMeasure E χ).real Δ.1 : ℝ) : ℂ) = diagonalForm E χ Δ :=
    fun χ => by rw [diagonalMeasure_real hE, diagonalForm_eq_norm_sq hE]
  have h0 : powersOfI 0 = 1 := rfl
  have h1 : powersOfI 1 = Complex.I := rfl
  have h2 : powersOfI 2 = -1 := rfl
  have h3 : powersOfI 3 = -Complex.I := rfl
  rw [crossForm_eq_polarization hE, sum_fourthRoots_eq]
  show ∑ j : Fin 4, (1 / 4 : ℂ) * conj (powersOfI j) *
    (((diagonalMeasure E (φ + powersOfI j • ψ)).real Δ.1 : ℝ) : ℂ) = _
  rw [Fin.sum_univ_four]
  simp only [hr, h0, h1, h2, h3]
  ring
def crossIntegral (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) (φ ψ : H) : ℂ :=
  complexIntegral (crossForm E φ ψ) f
theorem crossIntegral_eq (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (φ ψ : H) :
    crossIntegral E f φ ψ = (polarizationCombination hE φ ψ).integral f :=
  complexIntegral_eq_combination _ (polarizationCombination_toSetFunction hE φ ψ) hf
theorem crossIntegral_add (hE : IsPVM E) {f g : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (hg : IsBoundedMeasurableFn g) (φ ψ : H) :
    crossIntegral E (fun y => f y + g y) φ ψ = crossIntegral E f φ ψ + crossIntegral E g φ ψ := by
  rw [crossIntegral_eq hE (isBoundedMeasurableFn_add hf hg), crossIntegral_eq hE hf,
    crossIntegral_eq hE hg, combination_integral_add _ hf hg]
theorem crossIntegral_const_mul (hE : IsPVM E) (c : ℂ) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (φ ψ : H) :
    crossIntegral E (fun y => c * f y) φ ψ = c * crossIntegral E f φ ψ := by
  rw [crossIntegral_eq hE (isBoundedMeasurableFn_mul (isBoundedMeasurableFn_const c) hf),
    crossIntegral_eq hE hf, combination_integral_const_mul]
theorem crossIntegral_indicator (hE : IsPVM E) (c : ℂ) (Δ : BorelSubset n) (φ ψ : H) :
    crossIntegral E (Δ.1.indicator fun _ => c) φ ψ = c * ⟪φ, E Δ ψ⟫_ℂ := by
  rw [crossIntegral_eq hE (isBoundedMeasurableFn_indicator c Δ), combination_integral_indicator,
    polarizationCombination_toSetFunction]
  rfl
theorem crossIntegral_tendsto (hE : IsPVM E) {f : Space n → ℂ}
    {u : ℕ → Space n → ℂ} {C : ℝ} (hf : IsBoundedMeasurableFn f)
    (hu : ∀ k, IsBoundedMeasurableFn (u k)) (hC : ∀ k y, ‖u k y‖ ≤ C)
    (hl : ∀ y, Tendsto (fun k => u k y) atTop (𝓝 (f y))) (φ ψ : H) :
    Tendsto (fun k => crossIntegral E (u k) φ ψ) atTop (𝓝 (crossIntegral E f φ ψ)) := by
  simp only [crossIntegral_eq hE hf, crossIntegral_eq hE (hu _)]
  exact combination_integral_tendsto _ hu hC hl
def diagonalCombination (hE : IsPVM E) (ψ : H) : MeasureCombination n where
  numTerms := 1
  one_le_numTerms := le_rfl
  coeff _ := 1
  component _ := diagonalMeasure E ψ
  isFinite _ := diagonalMeasure_isFinite hE ψ
theorem crossIntegral_self (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (ψ : H) :
    crossIntegral E f ψ ψ = ∫ y, f y ∂(diagonalMeasure E ψ) := by
  have h : (diagonalCombination hE ψ).toSetFunction = crossForm E ψ ψ := by
    funext Δ
    have hr : (((diagonalMeasure E ψ).real Δ.1 : ℝ) : ℂ) = diagonalForm E ψ Δ := by
      rw [diagonalMeasure_real hE, diagonalForm_eq_norm_sq hE]
    show ∑ _j : Fin 1, (1 : ℂ) * (((diagonalMeasure E ψ).real Δ.1 : ℝ) : ℂ) = _
    rw [Fin.sum_univ_one, one_mul, hr]
    rfl
  rw [crossIntegral, complexIntegral_eq_combination _ h hf]
  show ∑ _j : Fin 1, (1 : ℂ) * ∫ y, f y ∂(diagonalMeasure E ψ) = _
  rw [Fin.sum_univ_one, one_mul]
theorem norm_integral_diagonalMeasure_le (hE : IsPVM E) {f : Space n → ℂ} {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) (χ : H) :
    ‖∫ y, f y ∂(diagonalMeasure E χ)‖ ≤ C * ‖χ‖ ^ 2 := by
  have := diagonalMeasure_isFinite hE χ
  have h := norm_integral_le_of_norm_le_const (μ := diagonalMeasure E χ) (Eventually.of_forall hC)
  rwa [diagonalMeasure_real_univ hE] at h
theorem norm_crossIntegral_le_sq (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖f y‖ ≤ C) (φ ψ : H) :
    ‖crossIntegral E f φ ψ‖ ≤ C * (2 * ‖φ‖ ^ 2 + 2 * ‖ψ‖ ^ 2) := by
  have hterm : ∀ j : Fin 4, ‖(1 / 4 : ℂ) * conj (powersOfI j) *
      ∫ y, f y ∂(diagonalMeasure E (φ + powersOfI j • ψ))‖ ≤
        (1 / 4) * (C * (2 * ‖φ‖ ^ 2 + 2 * ‖ψ‖ ^ 2)) := by
    intro j
    have h1 : ‖φ + powersOfI j • ψ‖ ^ 2 ≤ 2 * ‖φ‖ ^ 2 + 2 * ‖ψ‖ ^ 2 := by
      have h2 : ‖φ + powersOfI j • ψ‖ ≤ ‖φ‖ + ‖ψ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_quarterTurn, one_mul]
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      nlinarith [sq_nonneg (‖φ‖ - ‖ψ‖)]
    have h4 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
    rw [norm_mul, norm_mul, RCLike.norm_conj, norm_quarterTurn, mul_one, h4]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact (norm_integral_diagonalMeasure_le hE hC _).trans (mul_le_mul_of_nonneg_left h1 hC0)
  rw [crossIntegral_eq hE hf]
  show ‖∑ j : Fin 4, (1 / 4 : ℂ) * conj (powersOfI j) *
    ∫ y, f y ∂(diagonalMeasure E (φ + powersOfI j • ψ))‖ ≤ _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => hterm j).trans (le_of_eq ?_))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
theorem crossIntegral_sesquilinear (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) :
    (∀ φ φ' ψ : H, crossIntegral E f (φ + φ') ψ = crossIntegral E f φ ψ + crossIntegral E f φ' ψ) ∧
    (∀ (c : ℂ) (φ ψ : H), crossIntegral E f (c • φ) ψ = conj c * crossIntegral E f φ ψ) ∧
    (∀ φ ψ ψ' : H, crossIntegral E f φ (ψ + ψ') = crossIntegral E f φ ψ + crossIntegral E f φ ψ') ∧
    (∀ (c : ℂ) (φ ψ : H), crossIntegral E f φ (c • ψ) = c * crossIntegral E f φ ψ) := by
  refine isBoundedMeasurableFn_induction (fun f =>
    (∀ φ φ' ψ : H, crossIntegral E f (φ + φ') ψ =
      crossIntegral E f φ ψ + crossIntegral E f φ' ψ) ∧
    (∀ (c : ℂ) (φ ψ : H), crossIntegral E f (c • φ) ψ = conj c * crossIntegral E f φ ψ) ∧
    (∀ φ ψ ψ' : H, crossIntegral E f φ (ψ + ψ') =
      crossIntegral E f φ ψ + crossIntegral E f φ ψ') ∧
    (∀ (c : ℂ) (φ ψ : H), crossIntegral E f φ (c • ψ) = c * crossIntegral E f φ ψ)) ?_ ?_ ?_ f hf
  · intro c Δ
    refine ⟨fun φ φ' ψ => ?_, fun a φ ψ => ?_, fun φ ψ ψ' => ?_, fun a φ ψ => ?_⟩ <;>
      simp only [crossIntegral_indicator hE, map_add, map_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right] <;> ring
  · rintro f g hf hg ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨fun φ φ' ψ => ?_, fun a φ ψ => ?_, fun φ ψ ψ' => ?_, fun a φ ψ => ?_⟩ <;>
      simp only [crossIntegral_add hE hf hg, a1, a2, a3, a4, b1, b2, b3, b4] <;> ring
  · intro f u C hf hu hC hl hP
    have T := fun φ ψ : H => crossIntegral_tendsto hE hf hu hC hl φ ψ
    refine ⟨fun φ φ' ψ => ?_, fun a φ ψ => ?_, fun φ ψ ψ' => ?_, fun a φ ψ => ?_⟩
    · exact tendsto_nhds_unique (T _ _)
        (((T φ ψ).add (T φ' ψ)).congr fun k => ((hP k).1 φ φ' ψ).symm)
    · exact tendsto_nhds_unique (T _ _)
        (((T φ ψ).const_mul (conj a)).congr fun k => ((hP k).2.1 a φ ψ).symm)
    · exact tendsto_nhds_unique (T _ _)
        (((T φ ψ).add (T φ ψ')).congr fun k => ((hP k).2.2.1 φ ψ ψ').symm)
    · exact tendsto_nhds_unique (T _ _)
        (((T φ ψ).const_mul a).congr fun k => ((hP k).2.2.2 a φ ψ).symm)
theorem norm_crossIntegral_le_mul (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖f y‖ ≤ C) (φ ψ : H) :
    ‖crossIntegral E f φ ψ‖ ≤ 4 * C * ‖φ‖ * ‖ψ‖ := by
  obtain ⟨-, a2, -, a4⟩ := crossIntegral_sesquilinear hE hf
  by_cases hφ : φ = 0
  · have h := a2 0 φ ψ
    rw [zero_smul, map_zero, zero_mul] at h
    simp [hφ, h]
  by_cases hψ : ψ = 0
  · have h := a4 0 φ ψ
    rw [zero_smul, zero_mul] at h
    simp [hψ, h]
  have hr : (‖φ‖ : ℂ) ≠ 0 := by simpa using hφ
  have hs : (‖ψ‖ : ℂ) ≠ 0 := by simpa using hψ
  have h1 : ‖((‖φ‖⁻¹ : ℝ) : ℂ) • φ‖ = 1 := by
    rw [Complex.ofReal_inv]
    exact norm_smul_inv_norm hφ
  have h2 : ‖((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ‖ = 1 := by
    rw [Complex.ofReal_inv]
    exact norm_smul_inv_norm hψ
  have h3 := norm_crossIntegral_le_sq hE hf hC0 hC (((‖φ‖⁻¹ : ℝ) : ℂ) • φ)
    (((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ)
  rw [h1, h2, a2, a4, Complex.conj_ofReal] at h3
  have h4 : crossIntegral E f φ ψ = (‖φ‖ : ℂ) * (‖ψ‖ : ℂ) *
      (((‖φ‖⁻¹ : ℝ) : ℂ) * (((‖ψ‖⁻¹ : ℝ) : ℂ) * crossIntegral E f φ ψ)) := by
    push_cast
    field_simp
  rw [h4, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, norm_norm, norm_norm]
  have h5 : 0 ≤ ‖φ‖ * ‖ψ‖ := by positivity
  calc ‖φ‖ * ‖ψ‖ * _ ≤ ‖φ‖ * ‖ψ‖ * (C * (2 * 1 ^ 2 + 2 * 1 ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 h5
    _ = 4 * C * ‖φ‖ * ‖ψ‖ := by ring
theorem exists_crossIntegralOperator (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) : ∃ B : H →L[ℂ] H, IsCrossIntegralOperator E f B := by
  obtain ⟨a1, a2, a3, a4⟩ := crossIntegral_sesquilinear (H := H) hE hf
  obtain ⟨-, C, hC⟩ := id hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let b : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (crossIntegral E f) a1 a2 a3 a4
  let bc : H →L⋆[ℂ] H →L[ℂ] ℂ :=
    b.mkContinuous₂ (4 * C) (fun x y => norm_crossIntegral_le_mul hE hf hC0 hC x y)
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin bc),
    fun φ ψ => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl
theorem inner_boundedCalculus (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (φ ψ : H) :
    ⟪φ, boundedCalculus E f ψ⟫_ℂ = crossIntegral E f φ ψ :=
  Classical.epsilon_spec (exists_crossIntegralOperator hE hf) φ ψ
theorem eq_boundedCalculus (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) {B : H →L[ℂ] H}
    (hB : ∀ φ ψ, ⟪φ, B ψ⟫_ℂ = crossIntegral E f φ ψ) :
    B = boundedCalculus E f :=
  ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => by
    rw [hB, inner_boundedCalculus hE hf]
theorem boundedCalculus_add_smul (hE : IsPVM E) {f g : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (hg : IsBoundedMeasurableFn g) (c : ℂ) :
    boundedCalculus E (fun y => f y + c * g y) =
      boundedCalculus E f + c • boundedCalculus E g := by
  have hcg := isBoundedMeasurableFn_mul (isBoundedMeasurableFn_const c) hg
  refine (eq_boundedCalculus hE (isBoundedMeasurableFn_add hf hcg) fun φ ψ => ?_).symm
  rw [crossIntegral_add hE hf hcg, crossIntegral_const_mul hE c hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inner_add_right, inner_smul_right,
    inner_boundedCalculus hE hf, inner_boundedCalculus hE hg]
theorem crossIntegral_mul_indicator (hE : IsPVM E) (c : ℂ) (Δ : BorelSubset n)
    {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f) (φ ψ : H) :
    crossIntegral E (fun y => f y * Δ.1.indicator (fun _ => c) y) φ ψ =
      c * crossIntegral E f φ (E Δ ψ) := by
  have hi := isBoundedMeasurableFn_indicator c Δ
  refine isBoundedMeasurableFn_induction (fun f => ∀ φ ψ : H,
    crossIntegral E (fun y => f y * Δ.1.indicator (fun _ => c) y) φ ψ =
      c * crossIntegral E f φ (E Δ ψ)) ?_ ?_ ?_ f hf φ ψ
  · intro c' Δ' φ ψ
    have h : (fun y => Δ'.1.indicator (fun _ => c') y * Δ.1.indicator (fun _ => c) y) =
        (Δ' ∩ Δ).1.indicator (fun _ => c' * c) := by
      funext y
      have hm : y ∈ (Δ' ∩ Δ).1 ↔ y ∈ Δ'.1 ∧ y ∈ Δ.1 := Iff.rfl
      by_cases h1 : y ∈ Δ'.1 <;> by_cases h2 : y ∈ Δ.1 <;> simp [Set.indicator, hm, h1, h2]
    rw [h, crossIntegral_indicator hE, crossIntegral_indicator hE, hE.map_inter,
      ContinuousLinearMap.mul_apply]
    ring
  · intro f g hf hg h1 h2 φ ψ
    have h : (fun y => (f y + g y) * Δ.1.indicator (fun _ => c) y) =
        fun y => f y * Δ.1.indicator (fun _ => c) y + g y * Δ.1.indicator (fun _ => c) y := by
      funext y
      ring
    rw [h, crossIntegral_add hE (isBoundedMeasurableFn_mul hf hi) (isBoundedMeasurableFn_mul hg hi),
      h1, h2, crossIntegral_add hE hf hg]
    ring
  · intro f u C hf hu hC hl hP φ ψ
    obtain ⟨-, D, hD⟩ := id hi
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0)
    exact tendsto_nhds_unique
      (crossIntegral_tendsto hE (isBoundedMeasurableFn_mul hf hi)
        (fun k => isBoundedMeasurableFn_mul (hu k) hi) (C := C * D)
        (fun k y => by
          rw [norm_mul]
          exact mul_le_mul (hC k y) (hD y) (norm_nonneg _) hC0)
        (fun y => (hl y).mul_const _) φ ψ)
      (((crossIntegral_tendsto hE hf hu hC hl φ (E Δ ψ)).const_mul c).congr
        fun k => (hP k φ ψ).symm)
theorem crossIntegral_mul (hE : IsPVM E) {f g : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (hg : IsBoundedMeasurableFn g) (φ ψ : H) :
    crossIntegral E (fun y => g y * f y) φ ψ =
      crossIntegral E g (ContinuousLinearMap.adjoint (boundedCalculus E f) φ) ψ := by
  refine isBoundedMeasurableFn_induction (fun g => ∀ φ ψ : H,
    crossIntegral E (fun y => g y * f y) φ ψ =
      crossIntegral E g (ContinuousLinearMap.adjoint (boundedCalculus E f) φ) ψ) ?_ ?_ ?_
    g hg φ ψ
  · intro c Δ φ ψ
    have h : (fun y => Δ.1.indicator (fun _ => c) y * f y) =
        fun y => f y * Δ.1.indicator (fun _ => c) y := by
      funext y
      ring
    rw [h, crossIntegral_mul_indicator hE c Δ hf, crossIntegral_indicator hE,
      ContinuousLinearMap.adjoint_inner_left, inner_boundedCalculus hE hf]
  · intro g₁ g₂ hg₁ hg₂ h1 h2 φ ψ
    have h : (fun y => (g₁ y + g₂ y) * f y) = fun y => g₁ y * f y + g₂ y * f y := by
      funext y
      ring
    rw [h, crossIntegral_add hE (isBoundedMeasurableFn_mul hg₁ hf)
      (isBoundedMeasurableFn_mul hg₂ hf), h1, h2, crossIntegral_add hE hg₁ hg₂]
  · intro g u C hg hu hC hl hP φ ψ
    obtain ⟨-, D, hD⟩ := id hf
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0)
    exact tendsto_nhds_unique
      (crossIntegral_tendsto hE (isBoundedMeasurableFn_mul hg hf)
        (fun k => isBoundedMeasurableFn_mul (hu k) hf) (C := C * D)
        (fun k y => by
          rw [norm_mul]
          exact mul_le_mul (hC k y) (hD y) (norm_nonneg _) hC0)
        (fun y => (hl y).mul_const _) φ ψ)
      ((crossIntegral_tendsto hE hg hu hC hl _ ψ).congr fun k => (hP k φ ψ).symm)
theorem boundedCalculus_mul (hE : IsPVM E) {f g : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (hg : IsBoundedMeasurableFn g) :
    boundedCalculus E (fun y => f y * g y) = boundedCalculus E f * boundedCalculus E g := by
  have h : (fun y => f y * g y) = fun y => g y * f y := by
    funext y
    ring
  rw [h]
  refine (eq_boundedCalculus hE (isBoundedMeasurableFn_mul hg hf) fun φ ψ => ?_).symm
  rw [crossIntegral_mul hE hf hg, ContinuousLinearMap.mul_apply, ← inner_boundedCalculus hE hg,
    ContinuousLinearMap.adjoint_inner_left]
theorem conj_crossIntegral_conj (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (φ ψ : H) :
    conj (crossIntegral E (fun y => conj (f y)) ψ φ) = crossIntegral E f φ ψ := by
  refine isBoundedMeasurableFn_induction (fun f => ∀ φ ψ : H,
    conj (crossIntegral E (fun y => conj (f y)) ψ φ) = crossIntegral E f φ ψ) ?_ ?_ ?_ f hf φ ψ
  · intro c Δ φ ψ
    have h : (fun y => conj (Δ.1.indicator (fun _ => c) y)) =
        Δ.1.indicator (fun _ => conj c) := by
      funext y
      by_cases h1 : y ∈ Δ.1 <;> simp [Set.indicator, h1]
    rw [h, crossIntegral_indicator hE, crossIntegral_indicator hE, map_mul, Complex.conj_conj,
      inner_conj_symm, pvm_inner_symm hE Δ φ ψ]
  · intro f g hf hg h1 h2 φ ψ
    have h : (fun y => conj (f y + g y)) = fun y => conj (f y) + conj (g y) := by
      funext y
      simp
    rw [h, crossIntegral_add hE (isBoundedMeasurableFn_conj hf) (isBoundedMeasurableFn_conj hg),
      map_add, h1, h2, crossIntegral_add hE hf hg]
  · intro f u C hf hu hC hl hP φ ψ
    have hT := crossIntegral_tendsto (u := fun k y => conj (u k y)) (C := C) hE
      (isBoundedMeasurableFn_conj hf)
      (fun k => isBoundedMeasurableFn_conj (hu k))
      (fun k y => by
        rw [RCLike.norm_conj]
        exact hC k y)
      (fun y => (Complex.continuous_conj.tendsto _).comp (hl y)) ψ φ
    exact tendsto_nhds_unique ((Complex.continuous_conj.tendsto _).comp hT)
      ((crossIntegral_tendsto hE hf hu hC hl φ ψ).congr fun k => (hP k φ ψ).symm)
theorem inner_boundedCalculus_conj (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (φ ψ : H) :
    ⟪φ, boundedCalculus E f ψ⟫_ℂ = ⟪boundedCalculus E (fun y => conj (f y)) φ, ψ⟫_ℂ := by
  rw [inner_boundedCalculus hE hf, ← conj_crossIntegral_conj hE hf,
    ← inner_boundedCalculus hE (isBoundedMeasurableFn_conj hf), inner_conj_symm]
theorem boundedCalculus_indicator_one (hE : IsPVM E) (Δ : BorelSubset n) :
    boundedCalculus E (Δ.1.indicator fun _ => (1 : ℂ)) = E Δ := by
  refine (eq_boundedCalculus hE (isBoundedMeasurableFn_indicator 1 Δ) fun φ ψ => ?_).symm
  rw [crossIntegral_indicator hE, one_mul]
theorem norm_boundedCalculus_apply_sq (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) (ψ : H) :
    ‖boundedCalculus E f ψ‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂(diagonalMeasure E ψ) := by
  have hc := isBoundedMeasurableFn_conj hf
  have h1 : ⟪boundedCalculus E f ψ, boundedCalculus E f ψ⟫_ℂ =
      ⟪ψ, boundedCalculus E (fun y => conj (f y) * f y) ψ⟫_ℂ := by
    rw [boundedCalculus_mul hE hc hf, ContinuousLinearMap.mul_apply,
      inner_boundedCalculus_conj hE hc ψ]
    simp only [Complex.conj_conj]
  have h2 : (fun y => conj (f y) * f y) = fun y => ((‖f y‖ ^ 2 : ℝ) : ℂ) := by
    funext y
    rw [Complex.conj_mul']
    push_cast
    rfl
  have h3 : ((‖boundedCalculus E f ψ‖ ^ 2 : ℝ) : ℂ) =
      ((∫ y, ‖f y‖ ^ 2 ∂(diagonalMeasure E ψ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← h2, ← crossIntegral_self hE (isBoundedMeasurableFn_mul hc hf),
      ← inner_boundedCalculus hE (isBoundedMeasurableFn_mul hc hf), ← h1,
      inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  exact Complex.ofReal_injective h3
theorem lintegral_enorm_sq_lt_top_iff {f : Space n → ℂ} (hf : Measurable f)
    (μ : Measure (Space n)) :
    ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ < ∞ ↔ Integrable (fun y => ‖f y‖ ^ 2) μ := by
  have h : ∀ y, ‖‖f y‖ ^ 2‖ₑ = ‖f y‖ₑ ^ 2 := fun y => by rw [enorm_pow, enorm_norm]
  constructor
  · intro hlt
    refine ⟨(hf.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa only [h] using hlt
  · intro hi
    have := hi.2
    rw [hasFiniteIntegral_iff_enorm] at this
    simpa only [h] using this
theorem exists_tendsto_boundedCalculus_cutoff (hE : IsPVM E) {f : Space n → ℂ}
    (hf : Measurable f) {ψ : H} (hψ : ψ ∈ sqIntegrableDomain E f) :
    ∃ v : H, Tendsto (fun k : ℕ => boundedCalculus E (cutoff f k) ψ) atTop (𝓝 v) := by
  have hint : Integrable (fun y => ‖f y‖ ^ 2) (diagonalMeasure E ψ) :=
    (lintegral_enorm_sq_lt_top_iff hf _).1 hψ
  let g : ℕ → Space n → ℝ := fun N => {y | (N : ℝ) < ‖f y‖}.indicator fun y => ‖f y‖ ^ 2
  have hgm : ∀ N : ℕ, MeasurableSet {y | (N : ℝ) < ‖f y‖} := fun N =>
    measurableSet_lt measurable_const hf.norm
  have hgi : ∀ N, Integrable (g N) (diagonalMeasure E ψ) := fun N => hint.indicator (hgm N)
  have hp : ∀ (N a b : ℕ), N ≤ a → N ≤ b → ∀ y,
      ‖cutoff f a y + (-1) * cutoff f b y‖ ^ 2 ≤ g N y := by
    intro N a b ha hb y
    by_cases h : ‖f y‖ ≤ N
    · have ha' : ‖f y‖ ≤ a := h.trans (by exact_mod_cast ha)
      have hb' : ‖f y‖ ≤ b := h.trans (by exact_mod_cast hb)
      simp [cutoff, g, Set.indicator, ha', hb', not_lt.2 h]
    · have hg : g N y = ‖f y‖ ^ 2 := by simp [g, Set.indicator, not_le.1 h]
      rw [hg]
      by_cases ha' : ‖f y‖ ≤ a <;> by_cases hb' : ‖f y‖ ≤ b <;>
        simp [cutoff, Set.indicator, ha', hb']
  have hdist : ∀ N a b : ℕ, N ≤ a → N ≤ b →
      dist (boundedCalculus E (cutoff f a) ψ) (boundedCalculus E (cutoff f b) ψ) ≤
        Real.sqrt (∫ y, g N y ∂(diagonalMeasure E ψ)) := by
    intro N a b ha hb
    have hu := isBoundedMeasurableFn_cutoff hf a
    have hv := isBoundedMeasurableFn_cutoff hf b
    have hd := isBoundedMeasurableFn_add hu
      (isBoundedMeasurableFn_mul (isBoundedMeasurableFn_const (-1)) hv)
    have hn := norm_boundedCalculus_apply_sq hE hd ψ
    rw [boundedCalculus_add_smul hE hu hv (-1)] at hn
    have he : boundedCalculus E (cutoff f a) ψ - boundedCalculus E (cutoff f b) ψ =
        (boundedCalculus E (cutoff f a) + (-1 : ℂ) • boundedCalculus E (cutoff f b)) ψ := by
      simp [sub_eq_add_neg]
    rw [dist_eq_norm, he]
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [hn]
    exact integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) (hgi N)
      (Eventually.of_forall (hp N a b ha hb))
  have h0 : Tendsto (fun N => ∫ y, g N y ∂(diagonalMeasure E ψ)) atTop
      (𝓝 (∫ _, (0 : ℝ) ∂(diagonalMeasure E ψ))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖f y‖ ^ 2)
      (fun N => (hgi N).aestronglyMeasurable) hint
      (fun N => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · by_cases h : (N : ℝ) < ‖f y‖ <;> simp [g, Set.indicator, h]
    · obtain ⟨K, hK⟩ := exists_nat_ge ‖f y‖
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop K] with N hN
      have h : ¬ (N : ℝ) < ‖f y‖ := not_lt.2 (hK.trans (by exact_mod_cast hN))
      simp [g, Set.indicator, h]
  have h1 : Tendsto (fun N => Real.sqrt (∫ y, g N y ∂(diagonalMeasure E ψ))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto _).comp h0
    rw [integral_zero, Real.sqrt_zero] at h
    exact h
  exact cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_tendsto_0 _ (fun a b N ha hb => hdist N a b ha hb) h1)
theorem cutoff_of_isBoundedMeasurableFn (hE : IsPVM E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) :
    sqIntegrableDomain E f = Set.univ ∧
    ∀ ψ : H, Tendsto (fun k : ℕ => boundedCalculus E (cutoff f k) ψ) atTop
      (𝓝 (boundedCalculus E f ψ)) := by
  obtain ⟨hm, C, hC⟩ := id hf
  refine ⟨Set.eq_univ_of_forall fun ψ => ?_, fun ψ => ?_⟩
  · have hfin := diagonalMeasure_isFinite hE ψ
    refine (lintegral_enorm_sq_lt_top_iff hm _).2 ?_
    refine Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
      (Eventually.of_forall fun y => ?_)
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC y) 2
  · obtain ⟨K, hK⟩ := exists_nat_ge C
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop K] with k hk
    have h : cutoff f k = f := by
      funext y
      have hy : ‖f y‖ ≤ k := (hC y).trans (hK.trans (by exact_mod_cast hk))
      simp [cutoff, Set.indicator, hy]
    rw [h]
theorem diagonalMeasureProperties_holds (hE : IsPVM E) : DiagonalMeasureProperties E := by
  refine ⟨fun ψ Δ => diagonalForm_eq_norm_sq hE ψ Δ, fun ψ Δ => diagonalMeasure_apply hE ψ Δ,
    fun ψ => diagonalMeasure_univ hE ψ, fun c ψ => ?_, fun φ ψ Δ => ?_, fun ψ Δ Δ' => ?_⟩
  · refine Measure.ext fun s hs => ?_
    have h := diagonalMeasure_apply hE (c • ψ) ⟨s, hs⟩
    have h' := diagonalMeasure_apply hE ψ ⟨s, hs⟩
    simp only at h h'
    rw [h, Measure.smul_apply, h', smul_eq_mul, ← ENNReal.ofReal_mul (by positivity), map_smul,
      norm_smul, mul_pow]
  · rw [diagonalMeasure_apply hE, diagonalMeasure_apply hE, diagonalMeasure_apply hE, map_add]
    have h1 : ‖E Δ φ + E Δ ψ‖ ≤ ‖E Δ φ‖ + ‖E Δ ψ‖ := norm_add_le _ _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ENNReal.ofReal (‖E Δ φ + E Δ ψ‖ ^ 2)
        ≤ ENNReal.ofReal (2 * ‖E Δ φ‖ ^ 2 + 2 * ‖E Δ ψ‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (‖E Δ φ‖ - ‖E Δ ψ‖)])
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          norm_num
  · rw [diagonalMeasure_apply hE, diagonalMeasure_apply hE, hE.map_inter,
      ContinuousLinearMap.mul_apply]
theorem isNull_iff (hE : IsPVM E) (Δ : BorelSubset n) :
    IsNull E Δ ↔ ∀ ψ : H, diagonalMeasure E ψ Δ.1 = 0 := by
  constructor
  · intro h ψ
    rw [diagonalMeasure_apply hE, show E Δ = 0 from h]
    simp
  · intro h
    refine ContinuousLinearMap.ext fun ψ => ?_
    have h1 := h ψ
    rw [diagonalMeasure_apply hE, ENNReal.ofReal_eq_zero] at h1
    have h2 : ‖E Δ ψ‖ ^ 2 = 0 := le_antisymm h1 (by positivity)
    simpa using h2
theorem nullProperties_holds (hE : IsPVM E) : NullProperties E := by
  refine ⟨isNull_iff hE, fun Δ Δ' hs h => ?_, fun S U hS h hU => ?_⟩
  · rw [isNull_iff hE] at h ⊢
    exact fun ψ => measure_mono_null hs (h ψ)
  · rw [isNull_iff hE]
    intro ψ
    rw [hU, measure_biUnion_null_iff hS]
    exact fun Δ hΔ => (isNull_iff hE Δ).1 (h Δ hΔ) ψ
theorem crossFormProperties_holds (hE : IsPVM E) : CrossFormProperties E := by
  refine ⟨fun φ ψ => ⟨polarizationCombination hE φ ψ, polarizationCombination_toSetFunction hE φ ψ⟩,
    fun φ ψ Δ => crossForm_eq_polarization hE φ ψ Δ, fun φ ψ Δ => ?_⟩
  simp only [crossForm]
  rw [inner_conj_symm, pvm_inner_symm hE Δ ψ φ]
theorem boundedCalculusUnique_holds (hE : IsPVM E) :
    BoundedCalculusUnique (H := H) E := by
  intro f hf
  refine ⟨inner_boundedCalculus hE hf, fun B hB => eq_boundedCalculus hE hf hB,
    fun ψ => ?_, fun B hB => ?_⟩
  · rw [inner_boundedCalculus hE hf, crossIntegral_self hE hf]
  · have h : (B : H →ₗ[ℂ] H) = (boundedCalculus E f : H →ₗ[ℂ] H) := by
      refine (ext_inner_map _ _).1 fun ψ => ?_
      have h1 : ⟪ψ, B ψ⟫_ℂ = ⟪ψ, boundedCalculus E f ψ⟫_ℂ := by
        rw [hB ψ, inner_boundedCalculus hE hf, crossIntegral_self hE hf]
      have h2 := congrArg conj h1
      rwa [inner_conj_symm, inner_conj_symm] at h2
    exact ContinuousLinearMap.coe_injective h
theorem boundedCalculusProperties_holds (hE : IsPVM E) :
    BoundedCalculusProperties (H := H) E :=
  ⟨fun _ _ c hf hg => ⟨boundedCalculus_add_smul hE hf hg c, boundedCalculus_mul hE hf hg⟩,
    fun _ hf φ ψ => inner_boundedCalculus_conj hE hf φ ψ,
    fun Δ => boundedCalculus_indicator_one hE Δ,
    fun _ hf ψ => norm_boundedCalculus_apply_sq hE hf ψ⟩
theorem cutoffsConverge_holds (hE : IsPVM E) :
    CutoffsConverge (H := H) E :=
  ⟨fun _ hf _ hψ => exists_tendsto_boundedCalculus_cutoff hE hf hψ,
    fun _ hf => cutoff_of_isBoundedMeasurableFn hE hf⟩
end HilbertSpace
theorem boundedBorelCalculusTheorem_proof : BoundedBorelCalculusTheorem := by
  intro n _ H _ _ _ E hE
  exact ⟨diagonalMeasureProperties_holds hE, nullProperties_holds hE, crossFormProperties_holds hE,
    boundedCalculusUnique_holds hE, boundedCalculusProperties_holds hE, cutoffsConverge_holds hE⟩
end YangMills.Construction.EuclideanBorel.BoundedCalculusProof
