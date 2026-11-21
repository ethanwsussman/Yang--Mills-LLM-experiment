import YangMills.Construction.Analysis.CyclicTraceProducts
import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPicture
import YangMills.Construction.ChessboardTori.ExpansionOfTheCrossingKernel
import YangMills.Construction.ChessboardTori.TraceFormula
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori.CyclicTraceFormula
open SquareSummable TransferSetup
section AbsolutelySummableProducts
variable {𝕜 A : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
theorem hasSum_pi_prod_fin (n : ℕ) (g : Fin n → A → 𝕜) (hg : ∀ k, Summable fun a => ‖g k a‖) :
    Summable (fun α : Fin n → A => ‖∏ k, g k (α k)‖) ∧
      HasSum (fun α : Fin n → A => ∏ k, g k (α k)) (∏ k, ∑' a, g k a) := by
  induction n with
  | zero =>
    refine ⟨(hasSum_unique _).summable, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact hasSum_unique (fun _ : Fin 0 → A => (1 : 𝕜))
  | succ n ih =>
    obtain ⟨hnorm, hval⟩ := ih (fun k => g k.succ) (fun k => hg k.succ)
    let e : A × (Fin n → A) ≃ (Fin (n + 1) → A) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun α => (α 0, Fin.tail α)
        left_inv := fun p => by simp
        right_inv := fun α => by simp }
    have hsplit : ∀ p : A × (Fin n → A), ∏ k, g k (e p k) = g 0 p.1 * ∏ k, g k.succ (p.2 k) := by
      intro p
      simp [e, Fin.prod_univ_succ]
    have hprod : Summable fun p : A × (Fin n → A) => ‖g 0 p.1 * ∏ k, g k.succ (p.2 k)‖ :=
      (Summable.mul_of_nonneg (hg 0) hnorm (fun _ => norm_nonneg _)
        (fun _ => norm_nonneg _)).congr fun p => (norm_mul _ _).symm
    constructor
    · refine (e.summable_iff (f := fun α : Fin (n + 1) → A => ‖∏ k, g k (α k)‖)).mp ?_
      have hcomp : ((fun α : Fin (n + 1) → A => ‖∏ k, g k (α k)‖) ∘ e) =
          fun p : A × (Fin n → A) => ‖g 0 p.1 * ∏ k, g k.succ (p.2 k)‖ := by
        funext p
        simp only [Function.comp]
        rw [hsplit]
      rw [hcomp]
      exact hprod
    · refine (e.hasSum_iff (f := fun α : Fin (n + 1) → A => ∏ k, g k (α k))).mp ?_
      have hmul : HasSum (fun p : A × (Fin n → A) => g 0 p.1 * ∏ k, g k.succ (p.2 k))
          ((∑' a, g 0 a) * ∑' β : Fin n → A, ∏ k, g k.succ (β k)) := by
        rw [tsum_mul_tsum_of_summable_norm (R := 𝕜) (f := g 0) (g := fun β : Fin n → A => ∏ k : Fin n, g k.succ (β k)) (hg 0) hnorm]
        exact (summable_mul_of_summable_norm (R := 𝕜) (f := g 0) (g := fun β : Fin n → A => ∏ k : Fin n, g k.succ (β k)) (hg 0) hnorm).hasSum
      rw [hval.tsum_eq, ← Fin.prod_univ_succ (fun k => ∑' a, g k a)] at hmul
      have hcomp : ((fun α : Fin (n + 1) → A => ∏ k, g k (α k)) ∘ e) =
          fun p : A × (Fin n → A) => g 0 p.1 * ∏ k, g k.succ (p.2 k) := by
        funext p
        exact hsplit p
      rw [hcomp]
      exact hmul
theorem hasSum_pi_prod_fintype {ι : Type*} [Fintype ι] (g : ι → A → 𝕜)
    (hg : ∀ k, Summable fun a => ‖g k a‖) :
    Summable (fun α : ι → A => ‖∏ k, g k (α k)‖) ∧
      HasSum (fun α : ι → A => ∏ k, g k (α k)) (∏ k, ∑' a, g k a) := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨hnorm, hval⟩ := hasSum_pi_prod_fin (Fintype.card ι) (fun k => g (e.symm k)) (fun k => hg _)
  let E : (Fin (Fintype.card ι) → A) ≃ (ι → A) := e.symm.arrowCongr (Equiv.refl A)
  have hreindex : ∀ β, ∏ k, g k (E β k) = ∏ k, g (e.symm k) (β k) := by
    intro β
    rw [← e.symm.prod_comp]
    simp [E]
  constructor
  · refine (E.summable_iff (f := fun α : ι → A => ‖∏ k, g k (α k)‖)).mp ?_
    have hcomp : ((fun α : ι → A => ‖∏ k, g k (α k)‖) ∘ E) =
        fun β : Fin (Fintype.card ι) → A => ‖∏ k, g (e.symm k) (β k)‖ := by
      funext β
      simp only [Function.comp]
      rw [hreindex]
    rw [hcomp]
    exact hnorm
  · refine (E.hasSum_iff (f := fun α : ι → A => ∏ k, g k (α k))).mp ?_
    rw [← e.symm.prod_comp (fun k => ∑' a, g k a)]
    have hcomp : ((fun α : ι → A => ∏ k, g k (α k)) ∘ E) =
        fun β : Fin (Fintype.card ι) → A => ∏ k, g (e.symm k) (β k) := by
      funext β
      exact hreindex β
    rw [hcomp]
    exact hval
theorem sum_pi_prod_le {ι B : Type*} [Fintype ι] (g : ι → B → ℝ) (C : ι → ℝ)
    (hg0 : ∀ k a, 0 ≤ g k a) (hs : ∀ k, Summable (g k)) (hle : ∀ k, ∑' a, g k a ≤ C k)
    (s : Finset (ι → B)) : ∑ α ∈ s, ∏ k, g k (α k) ≤ ∏ k, C k := by
  have hn : ∀ k, Summable fun a => ‖g k a‖ := fun k =>
    (hs k).congr fun a => (Real.norm_of_nonneg (hg0 k a)).symm
  obtain ⟨-, hsum⟩ := hasSum_pi_prod_fintype g hn
  have h0 : ∀ α : ι → B, 0 ≤ ∏ k, g k (α k) := fun α => Finset.prod_nonneg fun k _ => hg0 k _
  calc ∑ α ∈ s, ∏ k, g k (α k) ≤ ∑' α : ι → B, ∏ k, g k (α k) :=
        hsum.summable.sum_le_tsum s fun α _ => h0 α
    _ = ∏ k, ∑' a, g k a := hsum.tsum_eq
    _ ≤ ∏ k, C k := Finset.prod_le_prod (fun k _ => tsum_nonneg fun a => hg0 k a) fun k _ => hle k
end AbsolutelySummableProducts
section BoundedIntegrals
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
theorem integrable_of_norm_le [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {h : X → E} (hm : Measurable h)
    (C : ℝ) (hb : ∀ x, ‖h x‖ ≤ C) : Integrable h μ :=
  Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hb)
theorem sq_integral_le_integral_sq [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Integrable g μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) : (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  set c := ∫ x, g x ∂μ with hc
  have h0 : 0 ≤ ∫ x, (g x - c) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hexp : ∀ x, (g x - c) ^ 2 = g x ^ 2 - 2 * c * g x + c ^ 2 := fun x => by ring
  simp only [hexp] at h0
  have hlin : ∫ x, (g x ^ 2 - 2 * c * g x + c ^ 2) ∂μ = (∫ x, g x ^ 2 ∂μ) - 2 * c * c + c ^ 2 := by
    rw [integral_add (f := fun x => g x ^ 2 - 2 * c * g x) (g := fun _ => c ^ 2)
      (hg2.sub (hg.const_mul _)) (integrable_const _),
      integral_sub hg2 (hg.const_mul _), integral_const_mul, ← hc]
    simp
  rw [hlin] at h0
  nlinarith [h0]
end BoundedIntegrals
instance instSecondCountableTopologyGaugeGroup :
    SecondCountableTopology Conventions.StandingParameters.gaugeGroup := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology _
variable {D : ChessboardSetup} (T : TransferSetup D)
theorem measurable_slabFirst : Measurable T.slabFirst :=
  (measurable_pi_apply _).comp measurable_fst
theorem measurable_slabLast : Measurable T.slabLast :=
  (measurable_pi_apply _).comp measurable_fst
theorem continuous_boltzmannFactor : Continuous (boltzmannFactor D) := by
  have h : Continuous fun u : Conventions.StandingParameters.gaugeGroup =>
      Matrices.ComplexMatrix2.fullTrace (u : Matrices.ComplexMatrix2) :=
    Continuous.matrix_trace continuous_subtype_val
  unfold boltzmannFactor
  exact Complex.continuous_exp.comp (continuous_const.mul (continuous_const.sub
    (continuous_const.mul h)))
theorem norm_boltzmannFactor_le_one (hTr : GaugeGroupTraceFacts)
    (u : Conventions.StandingParameters.gaugeGroup) : ‖boltzmannFactor D u‖ ≤ 1 := by
  obtain ⟨-, hn, -⟩ := hTr u
  have hre : (Matrices.ComplexMatrix2.fullTrace (u : Matrices.ComplexMatrix2)).re ≤ 2 :=
    (Complex.re_le_norm _).trans hn
  have hβ := D.beta_pos
  rw [boltzmannFactor, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.sub_re, Complex.one_re,
    Complex.neg_im, Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im]
  norm_num
  nlinarith
def edgeWeight (T : TransferSetup D) (ξ ξ' : T.EdgeField) (V : T.SiteField) : ℂ :=
  ∏ b : T.PositiveTransverseEdge, boltzmannFactor D (T.axialHolonomy ξ ξ' V b)
theorem continuous_edgeWeight :
    Continuous fun p : T.EdgeField × T.EdgeField × T.SiteField =>
      edgeWeight T p.1 p.2.1 p.2.2 := by
  refine continuous_finsetProd _ fun b _ => (continuous_boltzmannFactor (D := D)).comp ?_
  unfold axialHolonomy
  fun_prop
theorem measurable_edgeWeight :
    Measurable fun p : T.EdgeField × T.EdgeField × T.SiteField =>
      edgeWeight T p.1 p.2.1 p.2.2 :=
  (continuous_edgeWeight T).measurable
theorem measurable_comp_triple {Ω X Y Z W : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W] {F : X → Y → Z → W}
    (hF : Measurable fun p : X × Y × Z => F p.1 p.2.1 p.2.2) {a : Ω → X} {b : Ω → Y} {c : Ω → Z}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable fun ω => F (a ω) (b ω) (c ω) :=
  hF.comp (ha.prodMk (hb.prodMk hc))
theorem measurable_edgeWeight_comp {Ω : Type*} [MeasurableSpace Ω] {a b : Ω → T.EdgeField}
    {c : Ω → T.SiteField} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable fun ω => edgeWeight T (a ω) (b ω) (c ω) :=
  measurable_comp_triple (F := edgeWeight T) (measurable_edgeWeight T) ha hb hc
theorem norm_edgeWeight_le_one (hTr : GaugeGroupTraceFacts) (ξ ξ' : T.EdgeField)
    (V : T.SiteField) : ‖edgeWeight T ξ ξ' V‖ ≤ 1 := by
  rw [edgeWeight, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_boltzmannFactor_le_one hTr _
def ExpansionBounds : Prop :=
  (∀ α : T.WordIndex, Continuous (T.normalizedMonomial α)) ∧
    ∀ ξ ξ' : T.EdgeField,
      Summable (fun α : T.WordIndex => ‖T.normalizedMonomial α ξ‖ ^ 2) ∧
      ∑' α : T.WordIndex, ‖T.normalizedMonomial α ξ‖ ^ 2 ≤ 1 ∧
      Summable (fun α : T.WordIndex => ‖T.normalizedMonomial α ξ‖ * ‖T.normalizedMonomial α ξ'‖) ∧
      ∑' α : T.WordIndex, ‖T.normalizedMonomial α ξ‖ * ‖T.normalizedMonomial α ξ'‖ ≤ 1 ∧
      HasSum (fun α : T.WordIndex =>
          starRingEnd ℂ (T.normalizedMonomial α ξ) * T.normalizedMonomial α ξ')
        (T.transferKernel ξ ξ')
variable {T}
theorem ExpansionBounds.norm_le_one (hK : ExpansionBounds T) (α : T.WordIndex)
    (ξ : T.EdgeField) : ‖T.normalizedMonomial α ξ‖ ≤ 1 := by
  obtain ⟨hs, hle, -⟩ := hK.2 ξ ξ
  have hterm := hs.le_tsum α fun _ _ => by positivity
  have hnn := norm_nonneg (T.normalizedMonomial α ξ)
  nlinarith
theorem ExpansionBounds.measurable (hK : ExpansionBounds T) (α : T.WordIndex) :
    Measurable (T.normalizedMonomial α) :=
  (hK.1 α).measurable
theorem sq_norm_slabKernelMatrix_le (hK : ExpansionBounds T) {Φ : T.SlabConfig → ℂ}
    (hΦ : Measurable Φ) {S : ℝ} (hS : ∀ η, ‖Φ η‖ ≤ S) (α α' : T.WordIndex) :
    ‖T.slabKernelMatrix Φ α α'‖ ^ 2 ≤ S ^ 2 * ∫ η, ‖T.normalizedMonomial α (T.slabFirst η)‖ ^ 2 *
      ‖T.normalizedMonomial α' (T.slabLast η)‖ ^ 2 ∂T.slabHaar := by
  set f : T.SlabConfig → ℝ := fun η => ‖T.normalizedMonomial α (T.slabFirst η)‖ with hf
  set f' : T.SlabConfig → ℝ := fun η => ‖T.normalizedMonomial α' (T.slabLast η)‖ with hf'
  have hfm : Measurable f :=
    ((hK.measurable α).comp (measurable_slabFirst T)).norm
  have hfm' : Measurable f' :=
    ((hK.measurable α').comp (measurable_slabLast T)).norm
  have hf1 : ∀ η, f η ≤ 1 := fun η => hK.norm_le_one _ _
  have hf1' : ∀ η, f' η ≤ 1 := fun η => hK.norm_le_one _ _
  have hf0 : ∀ η, 0 ≤ f η := fun η => norm_nonneg _
  have hf0' : ∀ η, 0 ≤ f' η := fun η => norm_nonneg _
  set h : T.SlabConfig → ℂ := fun η => T.normalizedMonomial α (T.slabFirst η) * Φ η *
    starRingEnd ℂ (T.normalizedMonomial α' (T.slabLast η)) with hh
  have hhm : Measurable h :=
    (((hK.measurable α).comp (measurable_slabFirst T)).mul hΦ).mul
      (continuous_star.measurable.comp ((hK.measurable α').comp (measurable_slabLast T)))
  have hg : Measurable fun η => ‖h η‖ := hhm.norm
  have hbound : ∀ η, ‖h η‖ ≤ f η * ‖Φ η‖ * f' η := fun η => by
    simp only [hh, norm_mul, RCLike.norm_conj, hf, hf']
    exact le_rfl
  have hS0 : ∀ η, 0 ≤ ‖Φ η‖ := fun η => norm_nonneg _
  have hbound' : ∀ η, ‖h η‖ ≤ S := fun η => (hbound η).trans (by
    have : f η * f' η ≤ 1 := mul_le_one₀ (hf1 η) (hf0' η) (hf1' η)
    nlinarith [hS η, hS0 η, mul_nonneg (hf0 η) (hf0' η)])
  have hint : Integrable (fun η => ‖h η‖) T.slabHaar :=
    integrable_of_norm_le hg S fun η => by simpa using hbound' η
  have hint2 : Integrable (fun η => ‖h η‖ ^ 2) T.slabHaar :=
    integrable_of_norm_le (hg.pow_const 2) (S ^ 2) fun η => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound' η) 2
  have hq : Integrable (fun η => f η ^ 2 * f' η ^ 2) T.slabHaar :=
    integrable_of_norm_le ((hfm.pow_const 2).mul (hfm'.pow_const 2)) 1 fun η => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := hf0 η; have := hf0' η; positivity)]
      have h1 : f η ^ 2 ≤ 1 := pow_le_one₀ (hf0 η) (hf1 η)
      have h2 : f' η ^ 2 ≤ 1 := pow_le_one₀ (hf0' η) (hf1' η)
      exact mul_le_one₀ h1 (sq_nonneg _) h2
  calc ‖T.slabKernelMatrix Φ α α'‖ ^ 2 ≤ (∫ η, ‖h η‖ ∂T.slabHaar) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2
    _ ≤ ∫ η, ‖h η‖ ^ 2 ∂T.slabHaar := sq_integral_le_integral_sq hint hint2
    _ ≤ ∫ η, S ^ 2 * (f η ^ 2 * f' η ^ 2) ∂T.slabHaar := by
        refine integral_mono hint2 (hq.const_mul _) fun η => ?_
        have h3 : ‖h η‖ ≤ f η * f' η * S := (hbound η).trans (by
          nlinarith [hS η, mul_nonneg (hf0 η) (hf0' η)])
        have h4 : ‖h η‖ ^ 2 ≤ (f η * f' η * S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        calc ‖h η‖ ^ 2 ≤ (f η * f' η * S) ^ 2 := h4
          _ = S ^ 2 * (f η ^ 2 * f' η ^ 2) := by ring
    _ = S ^ 2 * ∫ η, f η ^ 2 * f' η ^ 2 ∂T.slabHaar := integral_const_mul _ _
theorem sum_sq_norm_slabKernelMatrix_le (hK : ExpansionBounds T) {Φ : T.SlabConfig → ℂ}
    (hΦ : Measurable Φ) {S : ℝ} (hS : ∀ η, ‖Φ η‖ ≤ S) (t : Finset (T.WordIndex × T.WordIndex)) :
    ∑ p ∈ t, ‖T.slabKernelMatrix Φ p.1 p.2‖ ^ 2 ≤ S ^ 2 := by
  set q : T.WordIndex × T.WordIndex → T.SlabConfig → ℝ := fun p η =>
    ‖T.normalizedMonomial p.1 (T.slabFirst η)‖ ^ 2 *
      ‖T.normalizedMonomial p.2 (T.slabLast η)‖ ^ 2 with hq
  have hqint : ∀ p, Integrable (q p) T.slabHaar := fun p =>
    integrable_of_norm_le
      ((((hK.measurable p.1).comp (measurable_slabFirst T)).norm.pow_const 2).mul
        (((hK.measurable p.2).comp (measurable_slabLast T)).norm.pow_const 2)) 1 fun η => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hq]; positivity)]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (hK.norm_le_one _ _)) (sq_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (hK.norm_le_one _ _))
  have hpoint : ∀ η, ∑ p ∈ t, q p η ≤ 1 := fun η => by
    obtain ⟨ha, ha1, -⟩ := hK.2 (T.slabFirst η) (T.slabFirst η)
    obtain ⟨hb, hb1, -⟩ := hK.2 (T.slabLast η) (T.slabLast η)
    have hab := Summable.mul_of_nonneg ha hb (fun _ => by positivity) (fun _ => by positivity)
    have h1 := hab.sum_le_tsum t fun _ _ => by positivity
    rw [← ha.tsum_mul_tsum hb hab] at h1
    have h2 : 0 ≤ ∑' α : T.WordIndex, ‖T.normalizedMonomial α (T.slabLast η)‖ ^ 2 :=
      tsum_nonneg fun _ => by positivity
    exact h1.trans (mul_le_one₀ ha1 h2 hb1)
  have hint : ∫ η, ∑ p ∈ t, q p η ∂T.slabHaar ≤ 1 := by
    have h1 := integral_mono (μ := T.slabHaar) (integrable_finsetSum t fun p _ => hqint p)
      (integrable_const (1 : ℝ)) hpoint
    simpa using h1
  calc ∑ p ∈ t, ‖T.slabKernelMatrix Φ p.1 p.2‖ ^ 2 ≤ ∑ p ∈ t, S ^ 2 * ∫ η, q p η ∂T.slabHaar :=
        Finset.sum_le_sum fun p _ => sq_norm_slabKernelMatrix_le hK hΦ hS p.1 p.2
    _ = S ^ 2 * ∫ η, ∑ p ∈ t, q p η ∂T.slabHaar := by
        rw [integral_finsetSum t fun p _ => hqint p, Finset.mul_sum]
    _ ≤ S ^ 2 * 1 := mul_le_mul_of_nonneg_left hint (sq_nonneg _)
    _ = S ^ 2 := mul_one _
theorem isSqSummable_slabKernelMatrix (hK : ExpansionBounds T) {Φ : T.SlabConfig → ℂ}
    (hΦ : T.IsBoundedMeasurable Φ) :
    IsSqSummable (T.slabKernelMatrix Φ) ∧ hsNorm (T.slabKernelMatrix Φ) ≤ ⨆ η, ‖Φ η‖ := by
  obtain ⟨hm, C, hC⟩ := hΦ
  have hbdd : BddAbove (Set.range fun η => ‖Φ η‖) := ⟨C, by rintro _ ⟨η, rfl⟩; exact hC η⟩
  set S := ⨆ η, ‖Φ η‖ with hSdef
  have hS : ∀ η, ‖Φ η‖ ≤ S := fun η => le_ciSup hbdd η
  have hS0 : 0 ≤ S := Real.iSup_nonneg fun _ => norm_nonneg _
  have hsum := sum_sq_norm_slabKernelMatrix_le hK hm hS
  have h0 : (0 : T.WordIndex × T.WordIndex → ℝ) ≤
      fun p => ‖T.slabKernelMatrix Φ p.1 p.2‖ ^ 2 := fun _ => by positivity
  refine ⟨summable_of_sum_le h0 hsum, ?_⟩
  have h1 := Real.tsum_le_of_sum_le h0 hsum
  rw [hsNorm, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_iff.mpr ⟨hS0, h1⟩
theorem slabFirst_slabReverse (η : T.SlabConfig) :
    T.slabFirst (T.slabReverse η) = T.slabLast η := by
  simp only [slabFirst, slabLast, slabReverse]
  exact congrArg η.1 (Fin.ext (by simp only [Fin.val_rev]))
theorem slabLast_slabReverse (η : T.SlabConfig) :
    T.slabLast (T.slabReverse η) = T.slabFirst η := by
  have h2 := T.two_le_ratioNat
  simp only [slabFirst, slabLast, slabReverse]
  exact congrArg η.1 (Fin.ext (by simp only [Fin.val_rev]; omega))
theorem adjointKernel_slabKernelMatrix (hK : ExpansionBounds T) (hRev : T.SlabReversalProperties)
    {Φ : T.SlabConfig → ℂ} (hΦ : T.IsBoundedMeasurable Φ) :
    adjointKernel (T.slabKernelMatrix Φ) = T.slabKernelMatrix (T.reflectConj Φ) := by
  obtain ⟨-, hinv, hmp, hfun⟩ := hRev
  have hΦ' := (hfun Φ Φ hΦ hΦ).1.1
  funext α α'
  simp only [adjointKernel, slabKernelMatrix]
  rw [← integral_conj]
  set H : T.SlabConfig → ℂ := fun η => T.normalizedMonomial α (T.slabFirst η) * T.reflectConj Φ η *
    starRingEnd ℂ (T.normalizedMonomial α' (T.slabLast η)) with hH
  have hHm : Measurable H :=
    (((hK.measurable α).comp (measurable_slabFirst T)).mul hΦ').mul
      (continuous_star.measurable.comp ((hK.measurable α').comp (measurable_slabLast T)))
  have h1 := integral_map (μ := T.slabHaar) hmp.measurable.aemeasurable
    (f := H) hHm.aestronglyMeasurable
  rw [hmp.map_eq] at h1
  rw [h1]
  refine integral_congr_ae (ae_of_all _ fun η => ?_)
  simp only [hH, slabFirst_slabReverse, slabLast_slabReverse, reflectConj, hinv η, map_mul,
    Complex.conj_conj]
  ring
section CyclicIndices
def finZModEquiv (m : SlabCount) : Fin (m : ℕ) ≃ ZMod (m : ℕ) :=
  Equiv.ofBijective (fun k => ((k : ℕ) : ZMod (m : ℕ))) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => ?_, by simp [ZMod.card]⟩
    have h' := congrArg ZMod.val h
    simp only [ZMod.val_natCast_of_lt a.2, ZMod.val_natCast_of_lt b.2] at h'
    exact Fin.ext h'
theorem finZModEquiv_finRotate (m : SlabCount) (k : Fin (m : ℕ)) :
    finZModEquiv m (finRotate (m : ℕ) k) = finZModEquiv m k + 1 := by
  obtain ⟨m, hm⟩ := m
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  change ((finRotate (n + 1) k : ℕ) : ZMod (n + 1)) = ((k : ℕ) : ZMod (n + 1)) + 1
  by_cases hk : k = Fin.last n
  · subst hk
    have h : ((n : ZMod (n + 1))) + 1 = 0 := by exact_mod_cast ZMod.natCast_self (n + 1)
    rw [finRotate_last]
    simp [h]
  · rw [coe_finRotate_of_ne_last hk]
    push_cast
    rfl
theorem tsum_prod_cyclic_eq_cyclicTrace {𝔸 : Type*} [Countable 𝔸] [Nonempty 𝔸] (m : SlabCount)
    (M : ZMod (m : ℕ) → 𝔸 → 𝔸 → ℂ) :
    ∑' α : ZMod (m : ℕ) → 𝔸, ∏ k, M k (α k) (α (k + 1)) =
      cyclicTrace (fun k : Fin (m : ℕ) => M (((k : ℕ) : ZMod (m : ℕ)))) := by
  let e := finZModEquiv m
  let E : (Fin (m : ℕ) → 𝔸) ≃ (ZMod (m : ℕ) → 𝔸) := e.arrowCongr (Equiv.refl 𝔸)
  rw [cyclicTrace, ← E.tsum_eq]
  refine tsum_congr fun β => ?_
  rw [cyclicTraceTerm, ← e.prod_comp]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h : e.symm (e k + 1) = finRotate (m : ℕ) k := by
    rw [← finZModEquiv_finRotate]
    exact e.symm_apply_apply _
  simp only [E, Equiv.arrowCongr_apply, Function.comp, Equiv.coe_refl, id, e.symm_apply_apply, h]
  rfl
end CyclicIndices
section SlabVariables
variable (T) (m : SlabCount)
theorem slabSliceIndex_sub_one_ratio (k : ZMod (m : ℕ)) :
    T.slabSliceIndex m (k - 1) (T.ratioNat : ℤ) = T.slabSliceIndex m k 0 := by
  have h : ((m : ℕ) : ℤ) ∣ (k.cast : ℤ) - (((k - 1).cast : ℤ) + 1) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simp
  obtain ⟨z, hz⟩ := h
  unfold slabSliceIndex
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨z, ?_⟩
  push_cast
  linear_combination (T.ratioNat : ℤ) * hz
theorem slabLast_slabRestriction (k : ZMod (m : ℕ)) (U : (T.torusPeriods m).GaugeConfig) :
    T.slabLast (T.slabRestriction m k U) =
      T.sliceField m U (T.slabSliceIndex m k (T.ratioNat : ℤ)) := by
  have h : (((T.ratioNat - 1 : ℕ) : ℤ) + 1) = (T.ratioNat : ℤ) := by
    have := T.two_le_ratioNat
    omega
  simp only [slabLast, slabRestriction]
  rw [h]
theorem slabFirst_slabRestriction (k : ZMod (m : ℕ)) (U : (T.torusPeriods m).GaugeConfig) :
    T.slabFirst (T.slabRestriction m k U) = T.sliceField m U (T.slabSliceIndex m k 1) := by
  simp [slabFirst, slabRestriction]
def periodIntegrand (Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ)
    (p : (ZMod (m : ℕ) → T.SlabConfig) × (ZMod (m : ℕ) → T.SiteField)) : ℂ :=
  ∏ k, (Φ k (p.1 k) * edgeWeight T (T.slabLast (p.1 (k - 1))) (T.slabFirst (p.1 k)) (p.2 k))
theorem periodIntegrand_slabDecomposition (Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ)
    (U : (T.torusPeriods m).GaugeConfig) :
    periodIntegrand T m Φ (T.slabDecomposition m U) =
      ∏ k : ZMod (m : ℕ), (Φ k (T.slabRestriction m k U) * ∏ b : T.PositiveTransverseEdge,
        boltzmannFactor D (T.axialHolonomy (T.sliceField m U (T.slabSliceIndex m k 0))
          (T.sliceField m U (T.slabSliceIndex m k 1)) (T.axialField m U (T.slabSliceIndex m k 0))
          b)) := by
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [slabDecomposition, edgeWeight, slabLast_slabRestriction, slabFirst_slabRestriction,
    slabSliceIndex_sub_one_ratio]
theorem measurable_periodIntegrand {Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ}
    (hΦ : ∀ k, Measurable (Φ k)) : Measurable (periodIntegrand T m Φ) := by
  have hfst : ∀ k : ZMod (m : ℕ), Measurable fun p :
      (ZMod (m : ℕ) → T.SlabConfig) × (ZMod (m : ℕ) → T.SiteField) => p.1 k :=
    fun k => (measurable_pi_apply k).comp measurable_fst
  have hsnd : ∀ k : ZMod (m : ℕ), Measurable fun p :
      (ZMod (m : ℕ) → T.SlabConfig) × (ZMod (m : ℕ) → T.SiteField) => p.2 k :=
    fun k => (measurable_pi_apply k).comp measurable_snd
  have hk : ∀ k : ZMod (m : ℕ), Measurable fun p :
      (ZMod (m : ℕ) → T.SlabConfig) × (ZMod (m : ℕ) → T.SiteField) =>
      Φ k (p.1 k) * edgeWeight T (T.slabLast (p.1 (k - 1))) (T.slabFirst (p.1 k))
        (p.2 k) := fun k => by
    have h1 : Measurable fun p :
        (ZMod (m : ℕ) → T.SlabConfig) × (ZMod (m : ℕ) → T.SiteField) => Φ k (p.1 k) :=
      (hΦ k).comp (hfst k)
    have h2 : Measurable fun p :
        (ZMod (m : ℕ) → T.SlabConfig) × (ZMod (m : ℕ) → T.SiteField) =>
        edgeWeight T (T.slabLast (p.1 (k - 1))) (T.slabFirst (p.1 k)) (p.2 k) :=
      measurable_edgeWeight_comp T ((measurable_slabLast T).comp (hfst (k - 1)))
        ((measurable_slabFirst T).comp (hfst k)) (hsnd k)
    exact h1.mul h2
  have h3 : periodIntegrand T m Φ = fun p => ∏ k ∈ Finset.univ, (Φ k (p.1 k) * edgeWeight T
      (T.slabLast (p.1 (k - 1))) (T.slabFirst (p.1 k)) (p.2 k)) := rfl
  rw [h3]
  exact Finset.measurable_fun_prod _ fun k _ => hk k
variable {T m}
theorem norm_periodIntegrand_le (hTr : GaugeGroupTraceFacts)
    {Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ} {C : ZMod (m : ℕ) → ℝ} (hC : ∀ k η, ‖Φ k η‖ ≤ C k)
    (p : (ZMod (m : ℕ) → T.SlabConfig) × (ZMod (m : ℕ) → T.SiteField)) :
    ‖periodIntegrand T m Φ p‖ ≤ ∏ k, C k := by
  rw [periodIntegrand, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => ?_
  rw [norm_mul]
  have h1 := norm_edgeWeight_le_one T hTr (T.slabLast (p.1 (k - 1)))
    (T.slabFirst (p.1 k)) (p.2 k)
  have h2 := hC k (p.1 k)
  nlinarith [norm_nonneg (Φ k (p.1 k)), norm_nonneg (edgeWeight T (T.slabLast (p.1 (k - 1)))
    (T.slabFirst (p.1 k)) (p.2 k))]
theorem slabProductIntegral_eq_integral_transferKernel (hTr : GaugeGroupTraceFacts)
    (hMap : Measure.map (T.slabDecomposition m) (T.torusPeriods m).haarMeasure =
      (Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar).prod
        (Measure.pi fun _ : ZMod (m : ℕ) => T.siteHaar))
    {Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ} (hΦ : ∀ k, Measurable (Φ k))
    {C : ZMod (m : ℕ) → ℝ} (hC : ∀ k η, ‖Φ k η‖ ≤ C k) :
    T.slabProductIntegral m Φ = ∫ ζ, ∏ k, (Φ k (ζ k) * T.transferKernel (T.slabLast (ζ (k - 1)))
      (T.slabFirst (ζ k))) ∂(Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar) := by
  have hne : Measure.map (T.slabDecomposition m) (T.torusPeriods m).haarMeasure ≠ 0 := by
    rw [hMap]
    exact IsProbabilityMeasure.ne_zero _
  have hae := AEMeasurable.of_map_ne_zero hne
  have hmeas := measurable_periodIntegrand T m hΦ
  have h1 : T.slabProductIntegral m Φ = ∫ p, periodIntegrand T m Φ p
      ∂(Measure.map (T.slabDecomposition m) (T.torusPeriods m).haarMeasure) := by
    rw [integral_map hae hmeas.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun U => (periodIntegrand_slabDecomposition T m Φ U).symm)
  have hint : Integrable (periodIntegrand T m Φ)
      ((Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar).prod
        (Measure.pi fun _ : ZMod (m : ℕ) => T.siteHaar)) :=
    integrable_of_norm_le hmeas _ (norm_periodIntegrand_le hTr hC)
  rw [h1, hMap, integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  have h2 := integral_fintype_prod_eq_prod (E := fun _ : ZMod (m : ℕ) => T.SiteField)
    (μ := fun _ => T.siteHaar)
    (fun (k : ZMod (m : ℕ)) (w : T.SiteField) => Φ k (ζ k) * edgeWeight T
      (T.slabLast (ζ (k - 1))) (T.slabFirst (ζ k)) w)
  simp only [periodIntegrand]
  rw [h2]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  rfl
end SlabVariables
section KernelSeries
variable {m : SlabCount}
def expansionSummand (Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ) (α : ZMod (m : ℕ) → T.WordIndex)
    (ζ : ZMod (m : ℕ) → T.SlabConfig) : ℂ :=
  ∏ k, (Φ k (ζ k) * (starRingEnd ℂ (T.normalizedMonomial (α k) (T.slabLast (ζ (k - 1)))) *
    T.normalizedMonomial (α k) (T.slabFirst (ζ k))))
theorem hasSum_expansionSummand (hK : ExpansionBounds T) (Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ)
    (ζ : ZMod (m : ℕ) → T.SlabConfig) :
    HasSum (fun α => expansionSummand Φ α ζ)
      (∏ k, (Φ k (ζ k) * T.transferKernel (T.slabLast (ζ (k - 1)))
        (T.slabFirst (ζ k)))) := by
  set g : ZMod (m : ℕ) → T.WordIndex → ℂ := fun k a => Φ k (ζ k) *
    (starRingEnd ℂ (T.normalizedMonomial a (T.slabLast (ζ (k - 1)))) *
      T.normalizedMonomial a (T.slabFirst (ζ k))) with hg
  have hs : ∀ k, HasSum (g k) (Φ k (ζ k) * T.transferKernel (T.slabLast (ζ (k - 1)))
      (T.slabFirst (ζ k))) := fun k =>
    ((hK.2 _ _).2.2.2.2).mul_left _
  have hn : ∀ k, Summable fun a => ‖g k a‖ := fun k => by
    have h := ((hK.2 (T.slabLast (ζ (k - 1))) (T.slabFirst (ζ k))).2.2.1).mul_left
      ‖Φ k (ζ k)‖
    refine h.congr fun a => ?_
    simp only [hg, norm_mul, RCLike.norm_conj]
  have h := (hasSum_pi_prod_fintype g hn).2
  have he : ∀ k, ∑' a, g k a = Φ k (ζ k) * T.transferKernel (T.slabLast (ζ (k - 1)))
      (T.slabFirst (ζ k)) := fun k => (hs k).tsum_eq
  simp only [he] at h
  exact h
theorem sum_norm_expansionSummand_le (hK : ExpansionBounds T)
    {Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ} {C : ZMod (m : ℕ) → ℝ} (hC0 : ∀ k, 0 ≤ C k)
    (hC : ∀ k η, ‖Φ k η‖ ≤ C k) (s : Finset (ZMod (m : ℕ) → T.WordIndex))
    (ζ : ZMod (m : ℕ) → T.SlabConfig) :
    ∑ α ∈ s, ‖expansionSummand Φ α ζ‖ ≤ ∏ k, C k := by
  have hle : ∀ α : ZMod (m : ℕ) → T.WordIndex, ‖expansionSummand Φ α ζ‖ ≤
      ∏ k, C k * (‖T.normalizedMonomial (α k) (T.slabLast (ζ (k - 1)))‖ *
        ‖T.normalizedMonomial (α k) (T.slabFirst (ζ k))‖) := fun α => by
    rw [expansionSummand, norm_prod]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hC k _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine (Finset.sum_le_sum fun α _ => hle α).trans ?_
  refine sum_pi_prod_le (fun k a => C k * (‖T.normalizedMonomial a (T.slabLast (ζ (k - 1)))‖ *
    ‖T.normalizedMonomial a (T.slabFirst (ζ k))‖)) C
    (fun k a => mul_nonneg (hC0 k) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun k => ((hK.2 (T.slabLast (ζ (k - 1))) (T.slabFirst (ζ k))).2.2.1).mul_left (C k))
    (fun k => ?_) s
  rw [tsum_mul_left]
  exact mul_le_of_le_one_right (hC0 k)
    (hK.2 (T.slabLast (ζ (k - 1))) (T.slabFirst (ζ k))).2.2.2.1
theorem measurable_expansionSummand (hK : ExpansionBounds T)
    {Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ} (hΦ : ∀ k, Measurable (Φ k))
    (α : ZMod (m : ℕ) → T.WordIndex) : Measurable (expansionSummand Φ α) := by
  have hpi : ∀ k : ZMod (m : ℕ), Measurable fun ζ : ZMod (m : ℕ) → T.SlabConfig => ζ k :=
    fun k => measurable_pi_apply k
  have hk : ∀ k : ZMod (m : ℕ), Measurable fun ζ : ZMod (m : ℕ) → T.SlabConfig =>
      Φ k (ζ k) * (starRingEnd ℂ (T.normalizedMonomial (α k) (T.slabLast (ζ (k - 1)))) *
        T.normalizedMonomial (α k) (T.slabFirst (ζ k))) := fun k => by
    have h1 : Measurable fun ζ : ZMod (m : ℕ) → T.SlabConfig => Φ k (ζ k) := (hΦ k).comp (hpi k)
    have h2 : Measurable fun ζ : ZMod (m : ℕ) → T.SlabConfig =>
        T.normalizedMonomial (α k) (T.slabLast (ζ (k - 1))) :=
      (hK.measurable (α k)).comp ((measurable_slabLast T).comp (hpi (k - 1)))
    have h3 : Measurable fun ζ : ZMod (m : ℕ) → T.SlabConfig =>
        T.normalizedMonomial (α k) (T.slabFirst (ζ k)) :=
      (hK.measurable (α k)).comp ((measurable_slabFirst T).comp (hpi k))
    have h4 : Measurable fun ζ : ZMod (m : ℕ) → T.SlabConfig =>
        starRingEnd ℂ (T.normalizedMonomial (α k) (T.slabLast (ζ (k - 1)))) :=
      continuous_star.measurable.comp h2
    exact h1.mul (h4.mul h3)
  have h3 : expansionSummand Φ α = fun ζ => ∏ k ∈ Finset.univ, (Φ k (ζ k) *
      (starRingEnd ℂ (T.normalizedMonomial (α k) (T.slabLast (ζ (k - 1)))) *
        T.normalizedMonomial (α k) (T.slabFirst (ζ k)))) := rfl
  rw [h3]
  exact Finset.measurable_fun_prod _ fun k _ => hk k
theorem integral_expansionSummand (Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ)
    (α : ZMod (m : ℕ) → T.WordIndex) :
    ∫ ζ, expansionSummand Φ α ζ ∂(Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar) =
      ∏ k, T.slabKernelMatrix (Φ k) (α k) (α (k + 1)) := by
  have h1 : ∀ ζ, expansionSummand Φ α ζ = ∏ k, (T.normalizedMonomial (α k) (T.slabFirst (ζ k)) *
      Φ k (ζ k) * starRingEnd ℂ (T.normalizedMonomial (α (k + 1)) (T.slabLast (ζ k)))) := by
    intro ζ
    have h2 : ∏ k, starRingEnd ℂ (T.normalizedMonomial (α k) (T.slabLast (ζ (k - 1)))) =
        ∏ k, starRingEnd ℂ (T.normalizedMonomial (α (k + 1)) (T.slabLast (ζ k))) := by
      rw [← Equiv.prod_comp (Equiv.addRight (1 : ZMod (m : ℕ)))
        (fun k => starRingEnd ℂ (T.normalizedMonomial (α k) (T.slabLast (ζ (k - 1)))))]
      simp
    simp only [expansionSummand, Finset.prod_mul_distrib]
    rw [h2]
    ring
  simp only [h1]
  exact integral_fintype_prod_eq_prod (E := fun _ : ZMod (m : ℕ) => T.SlabConfig)
    (μ := fun _ => T.slabHaar)
    (fun (k : ZMod (m : ℕ)) (η : T.SlabConfig) => T.normalizedMonomial (α k) (T.slabFirst η) *
      Φ k η * starRingEnd ℂ (T.normalizedMonomial (α (k + 1)) (T.slabLast η)))
theorem hasSum_slabProductIntegral (hK : ExpansionBounds T) (hTr : GaugeGroupTraceFacts)
    (hMap : Measure.map (T.slabDecomposition m) (T.torusPeriods m).haarMeasure =
      (Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar).prod
        (Measure.pi fun _ : ZMod (m : ℕ) => T.siteHaar))
    {Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ} (hΦ : ∀ k, T.IsBoundedMeasurable (Φ k)) :
    HasSum (fun α : ZMod (m : ℕ) → T.WordIndex =>
      ∏ k, T.slabKernelMatrix (Φ k) (α k) (α (k + 1))) (T.slabProductIntegral m Φ) := by
  have hm : ∀ k, Measurable (Φ k) := fun k => (hΦ k).1
  choose c hc using fun k => (hΦ k).2
  set C : ZMod (m : ℕ) → ℝ := fun k => |c k| with hCdef
  have hC0 : ∀ k, 0 ≤ C k := fun k => abs_nonneg _
  have hC : ∀ k η, ‖Φ k η‖ ≤ C k := fun k η => (hc k η).trans (le_abs_self _)
  have hint : ∀ α, Integrable (expansionSummand Φ α)
      (Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar) := fun α =>
    integrable_of_norm_le (measurable_expansionSummand hK hm α) (∏ k, C k) fun ζ => by
      simpa using sum_norm_expansionSummand_le hK hC0 hC {α} ζ
  have hsum : Summable fun α => ∫ ζ, ‖expansionSummand Φ α ζ‖
      ∂(Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar) := by
    refine summable_of_sum_le (c := ∏ k, C k) (fun α => integral_nonneg fun _ => norm_nonneg _)
      fun s => ?_
    rw [← integral_finsetSum s fun α _ => (hint α).norm]
    have h1 := integral_mono (μ := Measure.pi fun _ : ZMod (m : ℕ) => T.slabHaar)
      (integrable_finsetSum s fun α _ => (hint α).norm) (integrable_const (∏ k, C k))
      (fun ζ => sum_norm_expansionSummand_le hK hC0 hC s ζ)
    simpa using h1
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  simp only [integral_expansionSummand] at h
  rw [slabProductIntegral_eq_integral_transferKernel hTr hMap hm hC]
  have he : (fun ζ : ZMod (m : ℕ) → T.SlabConfig => ∏ k, (Φ k (ζ k) * T.transferKernel
      (T.slabLast (ζ (k - 1))) (T.slabFirst (ζ k)))) =
      fun ζ => ∑' α, expansionSummand Φ α ζ :=
    funext fun ζ => (hasSum_expansionSummand hK Φ ζ).tsum_eq.symm
  rw [he]
  exact h
end KernelSeries
theorem statement_holds (hExp : ChessboardTori.KernelExpansion.Statement)
    (hPic : ChessboardTori.TransferAssertions.Statement) (hTrace : CyclicTraceProductBounds) :
    CyclicTraceFormula.Statement := by
  intro D T
  obtain ⟨-, -, hcont, hsum⟩ := hExp D T
  have hK : ExpansionBounds T := ⟨hcont, hsum⟩
  obtain ⟨-, -, hTr, -, -, hRev, -, -, -⟩ := hPic D T ⟨2, le_rfl⟩
  have hsq : ∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ →
      IsSqSummable (T.slabKernelMatrix Φ) ∧ hsNorm (T.slabKernelMatrix Φ) ≤ ⨆ η, ‖Φ η‖ :=
    fun Φ hΦ => isSqSummable_slabKernelMatrix hK hΦ
  have hadj : ∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ →
      adjointKernel (T.slabKernelMatrix Φ) = T.slabKernelMatrix (T.reflectConj Φ) :=
    fun Φ hΦ => adjointKernel_slabKernelMatrix hK hRev hΦ
  have hrevb : ∀ Φ : T.SlabConfig → ℂ, T.IsBoundedMeasurable Φ →
      T.IsBoundedMeasurable (T.reflectConj Φ) :=
    fun Φ hΦ => (hRev.2.2.2 Φ Φ hΦ hΦ).1
  have hform : ∀ (m : SlabCount) (Φ : ZMod (m : ℕ) → T.SlabConfig → ℂ),
      (∀ k, T.IsBoundedMeasurable (Φ k)) →
      CyclicTraceConverges (T.slabKernels m Φ) ∧
        T.slabProductIntegral m Φ = cyclicTrace (T.slabKernels m Φ) := by
    intro m Φ hΦ
    have hB : ∀ k : Fin (m : ℕ), IsSqSummable (T.slabKernels m Φ k) :=
      fun k => (hsq _ (hΦ _)).1
    obtain ⟨⟨-, -, hf, -⟩, -⟩ := hTrace T.WordIndex (m : ℕ) m.2 (T.slabKernelMatrix (Φ 0))
      (T.slabKernels m Φ) (hsq _ (hΦ 0)).1 hB
    refine ⟨hf, ?_⟩
    obtain ⟨-, hMap, -⟩ := (hPic D T m).2.2.2.2.2.2.1
    have h := hasSum_slabProductIntegral hK hTr hMap hΦ
    rw [← h.tsum_eq, tsum_prod_cyclic_eq_cyclicTrace]
    rfl
  have halt : ∀ (m : SlabCount) (hm : Even (m : ℕ)) (Φ : T.SlabConfig → ℂ),
      T.IsBoundedMeasurable Φ →
      CyclicTraceConverges (alternatingKernels (T.slabKernelMatrix Φ) (m : ℕ)) ∧
        T.alternatingSlabIntegral m hm Φ =
          alternatingCyclicTrace (T.slabKernelMatrix Φ) (m : ℕ) := by
    intro m hm Φ hΦ
    have hb : ∀ k : ZMod (m : ℕ),
        T.IsBoundedMeasurable (if Even k.val then Φ else T.reflectConj Φ) := by
      intro k
      split_ifs
      · exact hΦ
      · exact hrevb Φ hΦ
    obtain ⟨h1, h2⟩ := hform m _ hb
    have hfac : T.slabKernels m (fun k => if Even k.val then Φ else T.reflectConj Φ) =
        alternatingKernels (T.slabKernelMatrix Φ) (m : ℕ) := by
      funext k
      simp only [slabKernels, alternatingKernels, ZMod.val_natCast_of_lt k.2]
      split_ifs with h
      · rfl
      · exact (hadj Φ hΦ).symm
    rw [hfac] at h1 h2
    exact ⟨h1, h2⟩
  have hschatten : ∀ (m : SlabCount) (hm : Even (m : ℕ)) (Φ : T.SlabConfig → ℂ),
      T.IsBoundedMeasurable Φ →
      T.alternatingSlabIntegral m hm Φ =
        ((schattenEvenNorm (T.slabKernelMatrix Φ) (m : ℕ) ^ (m : ℕ) : ℝ) : ℂ) := by
    intro m hm Φ hΦ
    obtain ⟨-, -, hE⟩ := hTrace T.WordIndex (m : ℕ) m.2 (T.slabKernelMatrix Φ)
      (fun _ => T.slabKernelMatrix Φ) (hsq Φ hΦ).1 (fun _ => (hsq Φ hΦ).1)
    rw [(halt m hm Φ hΦ).2]
    exact (hE hm).1.2.2.1
  have hnn : ∀ (A : T.WordIndex → T.WordIndex → ℂ) (n : ℕ), 0 ≤ schattenEvenNorm A n :=
    fun A n => Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨fun Φ hΦ => ⟨(hsq Φ hΦ).1, (hsq Φ hΦ).2, hadj Φ hΦ⟩, fun m Φ hΦ => hform m Φ hΦ, ?_⟩
  intro m hm
  refine ⟨fun Φ hΦ => ⟨(halt m hm Φ hΦ).1, (halt m hm Φ hΦ).2, hschatten m hm Φ hΦ,
    pow_nonneg (hnn _ _) _, ?_⟩, fun Φ hΦ => ?_, fun Φ hΦ j hj => ?_⟩
  · obtain ⟨-, -, hE⟩ := hTrace T.WordIndex (m : ℕ) m.2 (T.slabKernelMatrix Φ)
      (fun _ => T.slabKernelMatrix Φ) (hsq Φ hΦ).1 (fun _ => (hsq Φ hΦ).1)
    rw [hschatten m hm _ (hrevb Φ hΦ), hschatten m hm Φ hΦ, ← hadj Φ hΦ, (hE hm).1.2.2.2]
  · obtain ⟨-, -, hE⟩ := hTrace T.WordIndex (m : ℕ) m.2 (T.slabKernelMatrix (Φ 0))
      (T.slabKernels m Φ) (hsq _ (hΦ 0)).1 (fun _ => (hsq _ (hΦ _)).1)
    rw [(hform m Φ hΦ).2]
    refine (hE hm).2.1.trans (le_of_eq ?_)
    rw [← (finZModEquiv m).prod_comp (fun k : ZMod (m : ℕ) =>
      (T.alternatingSlabIntegral m hm (Φ k)).re ^ (1 / ((m : ℕ) : ℝ)))]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hschatten m hm _ (hΦ _), Complex.ofReal_re, one_div,
      Real.pow_rpow_inv_natCast (hnn _ _) (by have := m.2; omega)]
    rfl
  · obtain ⟨-, -, hE⟩ := hTrace T.WordIndex (m : ℕ) m.2 (T.slabKernelMatrix Φ)
      (fun _ => T.slabKernelMatrix Φ) (hsq Φ hΦ).1 (fun _ => (hsq Φ hΦ).1)
    have h1 : T.alternatingSlabIntegral (SlabCount.scale j hj m) (SlabCount.even_scale j hj hm) Φ =
        ((schattenEvenNorm (T.slabKernelMatrix Φ) (j * (m : ℕ)) ^ (j * (m : ℕ)) : ℝ) : ℂ) :=
      hschatten _ _ Φ hΦ
    rw [h1, hschatten m hm Φ hΦ]
    simp only [Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨trivial, pow_nonneg (hnn _ _) _, (hE hm).2.2 j hj⟩
end YangMills.Construction.ChessboardTori.CyclicTraceFormula
end
