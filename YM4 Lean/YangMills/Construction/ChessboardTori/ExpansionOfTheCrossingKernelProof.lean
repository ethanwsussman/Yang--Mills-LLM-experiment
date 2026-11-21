import YangMills.Construction.ChessboardTori.TraceFormulaProof
import YangMills.Construction.ChessboardTori.ExpansionOfTheCrossingKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori.KernelExpansion
open TransferSetup
open YangMills.Construction.Conventions YangMills.Construction.Matrices
local instance instSecondCountableGaugeGroup :
    SecondCountableTopology StandingParameters.gaugeGroup :=
  haveI : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
def wordProduct (w : Fin 2 × Fin 2 → ℂ) (γ : MatrixWord) : ℂ := (γ.map w).prod
theorem wordProduct_ofFn (w : Fin 2 × Fin 2 → ℂ) {n : ℕ} (p : Fin n → Fin 2 × Fin 2) :
    wordProduct w (List.ofFn p) = ∏ i, w (p i) := by
  simp [wordProduct, List.map_ofFn, List.prod_ofFn]
theorem sum_prod_tuples_eq_pow (w : Fin 2 × Fin 2 → ℂ) (n : ℕ) :
    ∑ p : Fin n → Fin 2 × Fin 2, ∏ i, w (p i) = (∑ q, w q) ^ n := by
  rw [Finset.sum_pow', Fintype.piFinset_univ]
theorem sum_prod_tuples_eq_pow_real (w : Fin 2 × Fin 2 → ℝ) (n : ℕ) :
    ∑ p : Fin n → Fin 2 × Fin 2, ∏ i, w (p i) = (∑ q, w q) ^ n := by
  rw [Finset.sum_pow', Fintype.piFinset_univ]
theorem poissonWeight_mul_pow (D : ChessboardSetup) (n : ℕ) (x : ℝ) :
    poissonWeight D n * x ^ n = Real.exp (-D.β) * ((D.β / 2 * x) ^ n / (n.factorial : ℝ)) := by
  unfold poissonWeight
  rw [mul_pow]
  ring
theorem hasSum_wordProduct_series (D : ChessboardSetup) (w : Fin 2 × Fin 2 → ℂ) :
    Summable (fun γ : MatrixWord => ‖(poissonWeight D γ.length : ℂ) * wordProduct w γ‖) ∧
    HasSum (fun γ : MatrixWord => (poissonWeight D γ.length : ℂ) * wordProduct w γ)
      (Complex.exp (-(D.β : ℂ)) * Complex.exp ((D.β : ℂ) / 2 * ∑ q, w q)) := by
  have hc : ∀ n, 0 ≤ poissonWeight D n := fun n => (poissonWeight_pos D n).le
  set g : (Σ n, Fin n → Fin 2 × Fin 2) → ℂ :=
    fun x => (poissonWeight D x.1 : ℂ) * ∏ i, w (x.2 i) with hg
  have hcomp : (fun γ : MatrixWord => (poissonWeight D γ.length : ℂ) * wordProduct w γ) ∘
      (List.equivSigmaTuple (α := Fin 2 × Fin 2)).symm = g := by
    funext x
    obtain ⟨n, p⟩ := x
    simp [hg, List.equivSigmaTuple, wordProduct_ofFn]
  have hnorm : ∀ x, ‖g x‖ = poissonWeight D x.1 * ∏ i, ‖w (x.2 i)‖ := by
    intro x
    simp only [hg, norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc _)]
  have hfib : ∀ n, ∑' p : Fin n → Fin 2 × Fin 2, ‖g ⟨n, p⟩‖ =
      poissonWeight D n * (∑ q, ‖w q‖) ^ n := by
    intro n
    rw [tsum_fintype, ← sum_prod_tuples_eq_pow_real, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => hnorm ⟨n, p⟩
  have hsum : Summable fun x => ‖g x‖ := by
    refine (summable_sigma_of_nonneg fun _ => norm_nonneg _).2
      ⟨fun n => Summable.of_finite, ?_⟩
    simp only [hfib, poissonWeight_mul_pow]
    exact (Real.summable_pow_div_factorial _).mul_left _
  have hg' : HasSum g (Complex.exp (-(D.β : ℂ)) * Complex.exp ((D.β : ℂ) / 2 * ∑ q, w q)) := by
    refine HasSum.sigma_of_hasSum (g := fun n => (poissonWeight D n : ℂ) * (∑ q, w q) ^ n)
      ?_ ?_ hsum.of_norm
    · have h := (NormedSpace.expSeries_div_hasSum_exp ((D.β : ℂ) / 2 * ∑ q, w q)).mul_left
        (Complex.exp (-(D.β : ℂ)))
      rw [← Complex.exp_eq_exp_ℂ] at h
      refine h.congr_fun ?_
      intro n
      simp only [poissonWeight, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_natCast, mul_pow]
      push_cast
      ring
    · intro n
      have h := hasSum_fintype (fun p : Fin n → Fin 2 × Fin 2 => g ⟨n, p⟩)
      simp only [hg] at h ⊢
      rw [← Finset.mul_sum, sum_prod_tuples_eq_pow] at h
      exact h
  constructor
  · rw [← (List.equivSigmaTuple (α := Fin 2 × Fin 2)).symm.summable_iff]
    have : (fun γ : MatrixWord => ‖(poissonWeight D γ.length : ℂ) * wordProduct w γ‖) ∘
        (List.equivSigmaTuple (α := Fin 2 × Fin 2)).symm = fun x => ‖g x‖ := by
      rw [← hcomp]
      rfl
    rw [this]
    exact hsum
  · rw [← (List.equivSigmaTuple (α := Fin 2 × Fin 2)).symm.hasSum_iff, hcomp]
    exact hg'
def conjEntryProd (u u' : StandingParameters.gaugeGroup) (p : Fin 2 × Fin 2) : ℂ :=
  starRingEnd ℂ ((u : ComplexMatrix2) p.1 p.2) * (u' : ComplexMatrix2) p.1 p.2
theorem conj_wordMonomial_mul (u u' : StandingParameters.gaugeGroup) (γ : MatrixWord) :
    starRingEnd ℂ (wordMonomial γ u) * wordMonomial γ u' =
      wordProduct (conjEntryProd u u') γ := by
  induction γ with
  | nil => simp [wordMonomial, wordProduct]
  | cons p γ ih =>
    simp only [wordMonomial, wordProduct, List.map_cons, List.prod_cons, map_mul,
      conjEntryProd] at ih ⊢
    rw [← ih]
    ring
theorem wordSeriesTerm_eq (D : ChessboardSetup) (u u' : StandingParameters.gaugeGroup)
    (γ : MatrixWord) :
    wordSeriesTerm D u u' γ =
      (poissonWeight D γ.length : ℂ) * wordProduct (conjEntryProd u u') γ := by
  rw [← conj_wordMonomial_mul, wordSeriesTerm, mul_assoc]
theorem sum_conjEntryProd (u u' : StandingParameters.gaugeGroup) :
    ∑ q, conjEntryProd u u' q =
      ComplexMatrix2.fullTrace ((u⁻¹ * u' : StandingParameters.gaugeGroup) : ComplexMatrix2) := by
  have hinv : ((u⁻¹ : StandingParameters.gaugeGroup) : ComplexMatrix2) =
      star (u : ComplexMatrix2) := rfl
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, conjEntryProd, ComplexMatrix2.fullTrace,
    Matrix.trace, Matrix.diag_apply, Submonoid.coe_mul, hinv, Matrix.mul_apply, Matrix.star_apply,
    RCLike.star_def]
  ring
theorem exp_mul_exp_eq_boltzmannFactor (D : ChessboardSetup) (u : StandingParameters.gaugeGroup) :
    Complex.exp (-(D.β : ℂ)) *
        Complex.exp ((D.β : ℂ) / 2 * ComplexMatrix2.fullTrace (u : ComplexMatrix2)) =
      boltzmannFactor D u := by
  rw [boltzmannFactor, ← Complex.exp_add]
  congr 1
  ring
theorem wordSeriesTerm_hasSum (D : ChessboardSetup) (u u' : StandingParameters.gaugeGroup) :
    Summable (fun γ : MatrixWord => ‖wordSeriesTerm D u u' γ‖) ∧
      HasSum (wordSeriesTerm D u u') (boltzmannFactor D (u⁻¹ * u')) := by
  have h := hasSum_wordProduct_series D (conjEntryProd u u')
  rw [sum_conjEntryProd, exp_mul_exp_eq_boltzmannFactor] at h
  have he : wordSeriesTerm D u u' = fun γ : MatrixWord =>
      (poissonWeight D γ.length : ℂ) * wordProduct (conjEntryProd u u') γ :=
    funext (wordSeriesTerm_eq D u u')
  rw [he]
  exact h
theorem boltzmannFactor_one (D : ChessboardSetup) : boltzmannFactor D 1 = 1 := by
  simp [boltzmannFactor, ComplexMatrix2.fullTrace, Matrix.trace_one]
theorem norm_entry_le_one (u : StandingParameters.gaugeGroup) (i j : Fin 2) :
    ‖(u : ComplexMatrix2) i j‖ ≤ 1 :=
  entry_norm_bound_of_unitary (Matrix.mem_specialUnitaryGroup_iff.mp u.2).1 i j
theorem norm_wordMonomial_le_one (γ : MatrixWord) (u : StandingParameters.gaugeGroup) :
    ‖wordMonomial γ u‖ ≤ 1 := by
  induction γ with
  | nil => simp [wordMonomial]
  | cons p γ ih =>
    simp only [wordMonomial, List.map_cons, List.prod_cons, norm_mul] at ih ⊢
    exact mul_le_one₀ (norm_entry_le_one u _ _) (norm_nonneg _) ih
theorem wordSeriesTerm_diag (D : ChessboardSetup) (u : StandingParameters.gaugeGroup)
    (γ : MatrixWord) :
    wordSeriesTerm D u u γ = ((poissonWeight D γ.length * ‖wordMonomial γ u‖ ^ 2 : ℝ) : ℂ) := by
  rw [wordSeriesTerm, mul_assoc, Complex.conj_mul']
  push_cast
  rfl
theorem hasSum_poissonWeight_norm_sq (D : ChessboardSetup) (u : StandingParameters.gaugeGroup) :
    HasSum (fun γ : MatrixWord => poissonWeight D γ.length * ‖wordMonomial γ u‖ ^ 2) 1 := by
  have h := (wordSeriesTerm_hasSum D u u).2
  rw [inv_mul_cancel, boltzmannFactor_one, funext (wordSeriesTerm_diag D u)] at h
  exact_mod_cast Complex.hasSum_ofReal.mp (by simpa using h)
theorem hasSum_prod_fin {W : Type} (n : ℕ) (f : Fin n → W → ℂ) (a : Fin n → ℂ)
    (hs : ∀ i, Summable fun x => ‖f i x‖) (hf : ∀ i, HasSum (f i) (a i)) :
    Summable (fun α : Fin n → W => ‖∏ i, f i (α i)‖) ∧
      HasSum (fun α : Fin n → W => ∏ i, f i (α i)) (∏ i, a i) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact ⟨Summable.of_finite, hasSum_unique (fun _ : Fin 0 → W => (1 : ℂ))⟩
  | succ n ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (fun i => f i.succ) (fun i => a i.succ) (fun i => hs i.succ)
      (fun i => hf i.succ)
    let e : (W × (Fin n → W)) ≃ (Fin (n + 1) → W) := Fin.consEquiv (fun _ => W)
    have hmul : ∀ x : W × (Fin n → W),
        ∏ i, f i (e x i) = f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i) := by
      intro x
      rw [Fin.prod_univ_succ]
      rfl
    have hsummable := (hs 0).mul_norm ih₁
    constructor
    · rw [← e.summable_iff]
      refine hsummable.congr fun x => ?_
      simp only [Function.comp_apply, hmul]
    · rw [← e.hasSum_iff, Fin.prod_univ_succ]
      have h := (hf 0).mul ih₂ hsummable.of_norm
      refine h.congr_fun fun x => ?_
      simp only [Function.comp_apply, hmul]
theorem hasSum_prod_fintype {W ι : Type} [Fintype ι] (f : ι → W → ℂ) (a : ι → ℂ)
    (hs : ∀ i, Summable fun x => ‖f i x‖) (hf : ∀ i, HasSum (f i) (a i)) :
    Summable (fun α : ι → W => ‖∏ i, f i (α i)‖) ∧
      HasSum (fun α : ι → W => ∏ i, f i (α i)) (∏ i, a i) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨h₁, h₂⟩ := hasSum_prod_fin (Fintype.card ι) (fun j => f (e.symm j))
    (fun j => a (e.symm j)) (fun j => hs _) (fun j => hf _)
  let E : (Fin (Fintype.card ι) → W) ≃ (ι → W) := e.symm.arrowCongr (Equiv.refl W)
  have hprod : ∀ β : Fin (Fintype.card ι) → W,
      ∏ i, f i (E β i) = ∏ j, f (e.symm j) (β j) := by
    intro β
    rw [← e.symm.prod_comp (fun i => f i (E β i))]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [E, Equiv.arrowCongr]
  constructor
  · rw [← E.summable_iff]
    refine h₁.congr fun β => ?_
    simp only [Function.comp_apply, hprod]
  · rw [← E.hasSum_iff, ← e.symm.prod_comp a]
    refine h₂.congr_fun fun β => ?_
    simp only [Function.comp_apply, hprod]
section Index
variable {D : ChessboardSetup} (T : TransferSetup D)
theorem indexSeriesTerm_eq_prod (ξ ξ' : T.EdgeField) (α : T.WordIndex) :
    indexSeriesTerm T ξ ξ' α = ∏ b, wordSeriesTerm D (ξ b) (ξ' b) (α b) := by
  simp only [indexSeriesTerm, wordSeriesTerm, TransferSetup.indexWeight,
    TransferSetup.indexMonomial, Finset.prod_mul_distrib, map_prod, Complex.ofReal_prod]
theorem indexSeriesTerm_hasSum (ξ ξ' : T.EdgeField) :
    Summable (fun α : T.WordIndex => ‖indexSeriesTerm T ξ ξ' α‖) ∧
      HasSum (indexSeriesTerm T ξ ξ')
        (∏ b : T.PositiveTransverseEdge, boltzmannFactor D ((ξ b)⁻¹ * ξ' b)) := by
  have h := hasSum_prod_fintype
    (fun b : T.PositiveTransverseEdge => wordSeriesTerm D (ξ b) (ξ' b))
    (fun b => boltzmannFactor D ((ξ b)⁻¹ * ξ' b))
    (fun b => (wordSeriesTerm_hasSum D (ξ b) (ξ' b)).1)
    (fun b => (wordSeriesTerm_hasSum D (ξ b) (ξ' b)).2)
  have he : indexSeriesTerm T ξ ξ' = fun α : T.WordIndex =>
      ∏ b, wordSeriesTerm D (ξ b) (ξ' b) (α b) := funext (indexSeriesTerm_eq_prod T ξ ξ')
  rw [he]
  exact h
theorem indexSeriesTerm_diag (ξ : T.EdgeField) (α : T.WordIndex) :
    indexSeriesTerm T ξ ξ α = ((T.indexWeight α * ‖T.indexMonomial α ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [indexSeriesTerm, mul_assoc, Complex.conj_mul']
  push_cast
  rfl
theorem hasSum_indexWeight_norm_sq (ξ : T.EdgeField) :
    HasSum (fun α : T.WordIndex => T.indexWeight α * ‖T.indexMonomial α ξ‖ ^ 2) 1 := by
  have h := (indexSeriesTerm_hasSum T ξ ξ).2
  simp only [inv_mul_cancel, boltzmannFactor_one, Finset.prod_const_one] at h
  rw [funext (indexSeriesTerm_diag T ξ)] at h
  exact_mod_cast Complex.hasSum_ofReal.mp (by simpa using h)
end Index
theorem continuous_wordMonomial (γ : MatrixWord) :
    Continuous fun u : StandingParameters.gaugeGroup => wordMonomial γ u := by
  induction γ with
  | nil => simpa [wordMonomial] using continuous_const
  | cons p γ ih =>
    simp only [wordMonomial, List.map_cons, List.prod_cons] at ih ⊢
    exact (continuous_subtype_val.matrix_elem p.1 p.2).mul ih
theorem continuous_boltzmannFactor (D : ChessboardSetup) :
    Continuous fun u : StandingParameters.gaugeGroup => boltzmannFactor D u := by apply _root_.YangMills.Construction.ChessboardTori.CyclicTraceFormula.continuous_boltzmannFactor <;> assumption
theorem boltzmannFactor_mul_comm (D : ChessboardSetup) (x y : StandingParameters.gaugeGroup) :
    boltzmannFactor D (x * y) = boltzmannFactor D (y * x) := by
  simp only [boltzmannFactor, Submonoid.coe_mul, ComplexMatrix2.fullTrace]
  rw [Matrix.trace_mul_comm]
theorem sq_norm_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℂ) (hg : AEStronglyMeasurable g μ)
    (hb : ∀ x, ‖g x‖ ≤ 1) :
    ‖∫ x, g x ∂μ‖ ^ 2 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have h₁ : Integrable (fun x => ‖g x‖) μ :=
    Integrable.of_bound hg.norm 1 (Filter.Eventually.of_forall fun x => by simpa using hb x)
  have h₂ : Integrable (fun x => ‖g x‖ ^ 2) μ :=
    Integrable.of_bound (hg.norm.pow 2) 1 (Filter.Eventually.of_forall fun x => by
      have := hb x
      have h0 := norm_nonneg (g x)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith)
  set m := ∫ x, ‖g x‖ ∂μ with hm
  have h₃ : 0 ≤ ∫ x, (‖g x‖ - m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have h₄ : ∫ x, (‖g x‖ - m) ^ 2 ∂μ = (∫ x, ‖g x‖ ^ 2 ∂μ) - m ^ 2 := by
    have he : (fun x => (‖g x‖ - m) ^ 2) =
        fun x => ‖g x‖ ^ 2 - 2 * m * ‖g x‖ + m ^ 2 := by
      funext x
      ring
    have hA : Integrable (fun x => ‖g x‖ ^ 2 - 2 * m * ‖g x‖) μ := h₂.sub (h₁.const_mul _)
    rw [he, integral_add hA (integrable_const _),
      integral_sub h₂ (h₁.const_mul _), integral_const_mul, ← hm, integral_const]
    simp only [probReal_univ, one_smul]
    ring
  have h₅ : ‖∫ x, g x ∂μ‖ ≤ m := norm_integral_le_integral_norm g
  calc ‖∫ x, g x ∂μ‖ ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₅ 2
    _ ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := by linarith
section Expansion
variable {D : ChessboardSetup} (T : TransferSetup D)
theorem continuous_indexMonomial_comp {X : Type*} [TopologicalSpace X] (α : T.WordIndex)
    {Ψ : X → T.EdgeField} (hΨ : Continuous Ψ) :
    Continuous fun x => T.indexMonomial α (Ψ x) := by
  unfold TransferSetup.indexMonomial
  exact continuous_finsetProd _ fun b _ =>
    (continuous_wordMonomial (α b)).comp ((continuous_apply b).comp hΨ)
theorem continuous_gaugeAct {X : Type*} [TopologicalSpace X] {Φ : X → T.SiteField}
    {Ψ : X → T.EdgeField} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) :
    Continuous fun x => T.gaugeAct (Φ x) (Ψ x) := by
  unfold TransferSetup.gaugeAct
  refine continuous_pi fun b => ?_
  have h₁ : Continuous fun x => Φ x b.1.source := (continuous_apply _).comp hΦ
  have h₂ : Continuous fun x => Ψ x b := (continuous_apply _).comp hΨ
  have h₃ : Continuous fun x => Φ x b.1.target := (continuous_apply _).comp hΦ
  exact (h₁.mul h₂).mul h₃.inv
theorem norm_indexMonomial_le_one (α : T.WordIndex) (ξ : T.EdgeField) :
    ‖T.indexMonomial α ξ‖ ≤ 1 := by
  unfold TransferSetup.indexMonomial
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    fun b _ => norm_wordMonomial_le_one _ _
theorem continuous_indexMonomial_gaugeAct (α : T.WordIndex) (ξ : T.EdgeField) :
    Continuous fun V : T.SiteField => T.indexMonomial α (T.gaugeAct V ξ) :=
  continuous_indexMonomial_comp T α (continuous_gaugeAct T continuous_id continuous_const)
theorem continuous_normalizedMonomial (α : T.WordIndex) :
    Continuous (T.normalizedMonomial α) := by
  unfold TransferSetup.normalizedMonomial TransferSetup.averagedMonomial
  refine continuous_const.mul ?_
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (fun ξ => (continuous_indexMonomial_gaugeAct T α ξ).aestronglyMeasurable)
    (fun ξ => Filter.Eventually.of_forall fun V => norm_indexMonomial_le_one T α _)
    (integrable_const _) (Filter.Eventually.of_forall fun V => ?_)
  exact continuous_indexMonomial_comp T α (continuous_gaugeAct T continuous_const continuous_id)
def averagedSquare (α : T.WordIndex) (ξ : T.EdgeField) : ℝ :=
  ∫ V, T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct V ξ)‖ ^ 2 ∂T.siteHaar
theorem aestronglyMeasurable_weightedSquare (α : T.WordIndex) (ξ : T.EdgeField) :
    AEStronglyMeasurable (fun V : T.SiteField =>
      T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct V ξ)‖ ^ 2) T.siteHaar :=
  (continuous_const.mul ((continuous_indexMonomial_gaugeAct T α ξ).norm.pow 2)).aestronglyMeasurable
theorem weightedSquare_nonneg (α : T.WordIndex) (ξ : T.EdgeField) :
    0 ≤ T.indexWeight α * ‖T.indexMonomial α ξ‖ ^ 2 :=
  mul_nonneg (T.indexWeight_pos α).le (sq_nonneg _)
theorem hasSum_averagedSquare (ξ : T.EdgeField) :
    HasSum (fun α : T.WordIndex => averagedSquare T α ξ) 1 := by
  have h := hasSum_integral_of_dominated_convergence (μ := T.siteHaar)
    (F := fun (α : T.WordIndex) (V : T.SiteField) =>
      T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct V ξ)‖ ^ 2)
    (f := fun _ => (1 : ℝ))
    (fun α V => T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct V ξ)‖ ^ 2)
    (fun α => aestronglyMeasurable_weightedSquare T α ξ)
    (fun α => Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs, abs_of_nonneg (weightedSquare_nonneg T α _)])
    (Filter.Eventually.of_forall fun V => (hasSum_indexWeight_norm_sq T _).summable)
    (by
      have : (fun V : T.SiteField => ∑' α : T.WordIndex,
          T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct V ξ)‖ ^ 2) =
          fun _ => (1 : ℝ) := funext fun V => (hasSum_indexWeight_norm_sq T _).tsum_eq
      rw [this]
      exact integrable_const _)
    (Filter.Eventually.of_forall fun V => hasSum_indexWeight_norm_sq T _)
  simpa [averagedSquare] using h
theorem sq_norm_normalizedMonomial_le (α : T.WordIndex) (ξ : T.EdgeField) :
    ‖T.normalizedMonomial α ξ‖ ^ 2 ≤ averagedSquare T α ξ := by
  have hc := (T.indexWeight_pos α).le
  have h := sq_norm_integral_le_integral_sq T.siteHaar _
    (continuous_indexMonomial_gaugeAct T α ξ).aestronglyMeasurable
    fun V => norm_indexMonomial_le_one T α _
  rw [averagedSquare, integral_const_mul]
  unfold TransferSetup.normalizedMonomial TransferSetup.averagedMonomial
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hc]
  exact mul_le_mul_of_nonneg_left h hc
theorem summable_sq_norm_normalizedMonomial (ξ : T.EdgeField) :
    Summable fun α : T.WordIndex => ‖T.normalizedMonomial α ξ‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun α => sq_norm_normalizedMonomial_le T α ξ) (hasSum_averagedSquare T ξ).summable
theorem tsum_sq_norm_normalizedMonomial_le (ξ : T.EdgeField) :
    ∑' α : T.WordIndex, ‖T.normalizedMonomial α ξ‖ ^ 2 ≤ 1 := by
  rw [← (hasSum_averagedSquare T ξ).tsum_eq]
  exact (summable_sq_norm_normalizedMonomial T ξ).tsum_le_tsum
    (fun α => sq_norm_normalizedMonomial_le T α ξ) (hasSum_averagedSquare T ξ).summable
theorem norm_mul_norm_le_half_sq (α : T.WordIndex) (ξ ξ' : T.EdgeField) :
    ‖T.normalizedMonomial α ξ‖ * ‖T.normalizedMonomial α ξ'‖ ≤
      (‖T.normalizedMonomial α ξ‖ ^ 2 + ‖T.normalizedMonomial α ξ'‖ ^ 2) / 2 := by
  nlinarith [sq_nonneg (‖T.normalizedMonomial α ξ‖ - ‖T.normalizedMonomial α ξ'‖)]
theorem summable_norm_mul_norm_normalizedMonomial (ξ ξ' : T.EdgeField) :
    Summable fun α : T.WordIndex =>
      ‖T.normalizedMonomial α ξ‖ * ‖T.normalizedMonomial α ξ'‖ :=
  Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun α => norm_mul_norm_le_half_sq T α ξ ξ')
    (((summable_sq_norm_normalizedMonomial T ξ).add
      (summable_sq_norm_normalizedMonomial T ξ')).div_const 2)
theorem tsum_norm_mul_norm_normalizedMonomial_le (ξ ξ' : T.EdgeField) :
    ∑' α : T.WordIndex, ‖T.normalizedMonomial α ξ‖ * ‖T.normalizedMonomial α ξ'‖ ≤ 1 := by
  have hs := ((summable_sq_norm_normalizedMonomial T ξ).add
    (summable_sq_norm_normalizedMonomial T ξ')).div_const 2
  calc ∑' α : T.WordIndex, ‖T.normalizedMonomial α ξ‖ * ‖T.normalizedMonomial α ξ'‖
      ≤ ∑' α : T.WordIndex,
          (‖T.normalizedMonomial α ξ‖ ^ 2 + ‖T.normalizedMonomial α ξ'‖ ^ 2) / 2 :=
        (summable_norm_mul_norm_normalizedMonomial T ξ ξ').tsum_le_tsum
          (fun α => norm_mul_norm_le_half_sq T α ξ ξ') hs
    _ = ((∑' α : T.WordIndex, ‖T.normalizedMonomial α ξ‖ ^ 2) +
          ∑' α : T.WordIndex, ‖T.normalizedMonomial α ξ'‖ ^ 2) / 2 := by
        rw [tsum_div_const, (summable_sq_norm_normalizedMonomial T ξ).tsum_add
          (summable_sq_norm_normalizedMonomial T ξ')]
    _ ≤ 1 := by
        have h₁ := tsum_sq_norm_normalizedMonomial_le T ξ
        have h₂ := tsum_sq_norm_normalizedMonomial_le T ξ'
        linarith
end Expansion
section Kernel
variable {D : ChessboardSetup} (T : TransferSetup D)
theorem map_leftMul_siteHaar (W : T.SiteField) :
    Measure.map (fun (V : T.SiteField) y => W y * V y) T.siteHaar = T.siteHaar := by
  unfold TransferSetup.siteHaar ComplexMatrix2.haarPi
  have hmeas : ∀ y : T.TransverseSite, Measurable fun u : StandingParameters.gaugeGroup => W y * u :=
    fun y => (continuous_const.mul continuous_id).measurable
  rw [Measure.infinitePi_map_pi (fun _ : T.TransverseSite => ComplexMatrix2.haarProb) hmeas]
  congr 1
  funext y
  exact map_mul_left_eq_self (Measure.haarMeasure ⊤) (W y)
theorem boltzmannFactor_gaugeAct_eq (ξ ξ' : T.EdgeField) (V₁ V₂ : T.SiteField)
    (b : T.PositiveTransverseEdge) :
    boltzmannFactor D ((T.gaugeAct V₁ ξ b)⁻¹ * T.gaugeAct V₂ ξ' b) =
      boltzmannFactor D (T.axialHolonomy ξ ξ' (fun y => (V₁ y)⁻¹ * V₂ y) b) := by
  unfold TransferSetup.gaugeAct TransferSetup.axialHolonomy
  have h₁ : (V₁ b.1.source * ξ b * (V₁ b.1.target)⁻¹)⁻¹ *
        (V₂ b.1.source * ξ' b * (V₂ b.1.target)⁻¹) =
      (V₁ b.1.target * (ξ b)⁻¹) *
        ((V₁ b.1.source)⁻¹ * V₂ b.1.source * ξ' b * (V₂ b.1.target)⁻¹) := by
    group
  have h₂ : (V₁ b.1.source)⁻¹ * V₂ b.1.source * ξ' b *
        ((V₁ b.1.target)⁻¹ * V₂ b.1.target)⁻¹ * (ξ b)⁻¹ =
      ((V₁ b.1.source)⁻¹ * V₂ b.1.source * ξ' b * (V₂ b.1.target)⁻¹) *
        (V₁ b.1.target * (ξ b)⁻¹) := by
    group
  rw [h₁, h₂]
  exact boltzmannFactor_mul_comm D _ _
theorem continuous_prod_boltzmannFactor_axialHolonomy (ξ ξ' : T.EdgeField) :
    Continuous fun V : T.SiteField =>
      ∏ b : T.PositiveTransverseEdge, boltzmannFactor D (T.axialHolonomy ξ ξ' V b) := by
  refine continuous_finsetProd _ fun b _ => (continuous_boltzmannFactor D).comp ?_
  unfold TransferSetup.axialHolonomy
  have h₁ : Continuous fun V : T.SiteField => V b.1.source := continuous_apply _
  have h₂ : Continuous fun V : T.SiteField => V b.1.target := continuous_apply _
  exact ((h₁.mul continuous_const).mul h₂.inv).mul continuous_const
theorem integral_prod_boltzmannFactor_gaugeAct (ξ ξ' : T.EdgeField) (V₁ : T.SiteField) :
    ∫ V₂, ∏ b : T.PositiveTransverseEdge,
        boltzmannFactor D ((T.gaugeAct V₁ ξ b)⁻¹ * T.gaugeAct V₂ ξ' b) ∂T.siteHaar =
      T.transferKernel ξ ξ' := by
  have hφ : Continuous fun (V : T.SiteField) (y : T.TransverseSite) => (V₁ y)⁻¹ * V y :=
    continuous_pi fun y => continuous_const.mul (continuous_apply y)
  calc ∫ V₂, ∏ b : T.PositiveTransverseEdge,
        boltzmannFactor D ((T.gaugeAct V₁ ξ b)⁻¹ * T.gaugeAct V₂ ξ' b) ∂T.siteHaar
      = ∫ V₂, (fun V : T.SiteField => ∏ b : T.PositiveTransverseEdge,
          boltzmannFactor D (T.axialHolonomy ξ ξ' V b)) (fun y => (V₁ y)⁻¹ * V₂ y)
            ∂T.siteHaar :=
        integral_congr_ae (Filter.Eventually.of_forall fun V₂ =>
          Finset.prod_congr rfl fun b _ => boltzmannFactor_gaugeAct_eq T ξ ξ' V₁ V₂ b)
    _ = ∫ V, ∏ b : T.PositiveTransverseEdge, boltzmannFactor D (T.axialHolonomy ξ ξ' V b)
          ∂(Measure.map (fun (V : T.SiteField) y => (V₁ y)⁻¹ * V y) T.siteHaar) :=
        (integral_map hφ.measurable.aemeasurable
          (continuous_prod_boltzmannFactor_axialHolonomy T ξ ξ').aestronglyMeasurable).symm
    _ = T.transferKernel ξ ξ' := by
        rw [map_leftMul_siteHaar T fun y => (V₁ y)⁻¹]
        rfl
theorem integral_indexSeriesTerm (ξ ξ' : T.EdgeField) (α : T.WordIndex) :
    ∫ p : T.SiteField × T.SiteField,
        indexSeriesTerm T (T.gaugeAct p.1 ξ) (T.gaugeAct p.2 ξ') α
          ∂T.siteHaar.prod T.siteHaar =
      starRingEnd ℂ (T.normalizedMonomial α ξ) * T.normalizedMonomial α ξ' := by
  have hc := (T.indexWeight_pos α).le
  have hs : ((Real.sqrt (T.indexWeight α) : ℝ) : ℂ) * (Real.sqrt (T.indexWeight α) : ℝ) =
      (T.indexWeight α : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have h := integral_prod_mul (μ := T.siteHaar) (ν := T.siteHaar)
    (fun V : T.SiteField =>
      (T.indexWeight α : ℂ) * starRingEnd ℂ (T.indexMonomial α (T.gaugeAct V ξ)))
    (fun V : T.SiteField => T.indexMonomial α (T.gaugeAct V ξ'))
  simp only [integral_const_mul, integral_conj] at h
  unfold indexSeriesTerm
  rw [h]
  unfold TransferSetup.normalizedMonomial TransferSetup.averagedMonomial
  rw [map_mul, Complex.conj_ofReal, ← hs]
  ring
theorem hasSum_transferKernel (ξ ξ' : T.EdgeField) :
    HasSum (fun α : T.WordIndex =>
        starRingEnd ℂ (T.normalizedMonomial α ξ) * T.normalizedMonomial α ξ')
      (T.transferKernel ξ ξ') := by
  have hA : Continuous fun p : T.SiteField × T.SiteField => T.gaugeAct p.1 ξ :=
    continuous_gaugeAct T continuous_fst continuous_const
  have hB : Continuous fun p : T.SiteField × T.SiteField => T.gaugeAct p.2 ξ' :=
    continuous_gaugeAct T continuous_snd continuous_const
  have hG : Continuous fun p : T.SiteField × T.SiteField =>
      ∏ b : T.PositiveTransverseEdge,
        boltzmannFactor D ((T.gaugeAct p.1 ξ b)⁻¹ * T.gaugeAct p.2 ξ' b) :=
    continuous_finsetProd _ fun b _ => (continuous_boltzmannFactor D).comp
      (((continuous_apply b).comp hA).inv.mul ((continuous_apply b).comp hB))
  have hbound : ∀ p : T.SiteField × T.SiteField,
      HasSum (fun α : T.WordIndex =>
        (T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct p.1 ξ)‖ ^ 2 +
          T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct p.2 ξ')‖ ^ 2) / 2)
        ((1 + 1) / 2) := fun p =>
    ((hasSum_indexWeight_norm_sq T _).add (hasSum_indexWeight_norm_sq T _)).div_const 2
  have h := hasSum_integral_of_dominated_convergence (μ := T.siteHaar.prod T.siteHaar)
    (F := fun (α : T.WordIndex) (p : T.SiteField × T.SiteField) =>
      indexSeriesTerm T (T.gaugeAct p.1 ξ) (T.gaugeAct p.2 ξ') α)
    (f := fun p => ∏ b : T.PositiveTransverseEdge,
      boltzmannFactor D ((T.gaugeAct p.1 ξ b)⁻¹ * T.gaugeAct p.2 ξ' b))
    (fun α p => (T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct p.1 ξ)‖ ^ 2 +
      T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct p.2 ξ')‖ ^ 2) / 2)
    (fun α => by
      unfold indexSeriesTerm
      exact ((continuous_const.mul (Complex.continuous_conj.comp
        (continuous_indexMonomial_comp T α hA))).mul
          (continuous_indexMonomial_comp T α hB)).aestronglyMeasurable)
    (fun α => Filter.Eventually.of_forall fun p => by
      have hc := (T.indexWeight_pos α).le
      unfold indexSeriesTerm
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc,
        RCLike.norm_conj]
      nlinarith [mul_nonneg hc (sq_nonneg (‖T.indexMonomial α (T.gaugeAct p.1 ξ)‖ -
        ‖T.indexMonomial α (T.gaugeAct p.2 ξ')‖))])
    (Filter.Eventually.of_forall fun p => (hbound p).summable)
    (by
      have : (fun p : T.SiteField × T.SiteField => ∑' α : T.WordIndex,
          (T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct p.1 ξ)‖ ^ 2 +
            T.indexWeight α * ‖T.indexMonomial α (T.gaugeAct p.2 ξ')‖ ^ 2) / 2) =
          fun _ => ((1 + 1) / 2 : ℝ) := funext fun p => (hbound p).tsum_eq
      rw [this]
      exact integrable_const _)
    (Filter.Eventually.of_forall fun p => (indexSeriesTerm_hasSum T _ _).2)
  have hint : Integrable (fun p : T.SiteField × T.SiteField =>
      ∏ b : T.PositiveTransverseEdge,
        boltzmannFactor D ((T.gaugeAct p.1 ξ b)⁻¹ * T.gaugeAct p.2 ξ' b))
      (T.siteHaar.prod T.siteHaar) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
    exact Integrable.of_bound hG.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hC p (Set.mem_univ p))
  have hK : ∫ p : T.SiteField × T.SiteField, ∏ b : T.PositiveTransverseEdge,
        boltzmannFactor D ((T.gaugeAct p.1 ξ b)⁻¹ * T.gaugeAct p.2 ξ' b)
        ∂T.siteHaar.prod T.siteHaar = T.transferKernel ξ ξ' := by
    rw [integral_prod _ hint]
    simp only [integral_prod_boltzmannFactor_gaugeAct, integral_const, probReal_univ, one_smul]
  rw [hK] at h
  exact h.congr_fun fun α => (integral_indexSeriesTerm T ξ ξ' α).symm
end Kernel
theorem statement_holds : Statement := by
  intro D T
  exact ⟨fun u u' => ⟨fun γ => norm_wordMonomial_le_one γ u, hasSum_poissonWeight_norm_sq D u,
      (wordSeriesTerm_hasSum D u u').1, (wordSeriesTerm_hasSum D u u').2⟩,
    fun ξ ξ' => ⟨hasSum_indexWeight_norm_sq T ξ, (indexSeriesTerm_hasSum T ξ ξ').1,
      (indexSeriesTerm_hasSum T ξ ξ').2⟩,
    fun α => continuous_normalizedMonomial T α,
    fun ξ ξ' => ⟨summable_sq_norm_normalizedMonomial T ξ,
      tsum_sq_norm_normalizedMonomial_le T ξ, summable_norm_mul_norm_normalizedMonomial T ξ ξ',
      tsum_norm_mul_norm_normalizedMonomial_le T ξ ξ', hasSum_transferKernel T ξ ξ'⟩⟩
end YangMills.Construction.ChessboardTori.KernelExpansion
end
