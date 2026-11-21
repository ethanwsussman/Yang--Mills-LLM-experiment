import YangMills.Construction.TransferOperators.AverageOfATwistedActionOnAPowerOfG
import YangMills.Construction.TransferOperators.OperatorsOfATwistedActionOnAPowerOfG
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators
open MeasureTheory
open SpinHarmonics (HaarL2)
open Matrices.ComplexMatrix2 (specialUnitary haarPi)
open GibbsHaarKernels (HaarPiInvariance invertAt)
namespace TwistedAverage
section General
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [IsProbabilityMeasure ν]
theorem sq_norm_integral_le_integral_sq {F : Y → ℂ} (hF : Integrable F ν)
    (hF2 : Integrable (fun y => ‖F y‖ ^ 2) ν) :
    ‖∫ y, F y ∂ν‖ ^ 2 ≤ ∫ y, ‖F y‖ ^ 2 ∂ν := by
  set m : ℝ := ∫ y, ‖F y‖ ∂ν with hm
  have hm0 : 0 ≤ m := integral_nonneg fun _ => norm_nonneg _
  have hle : ‖∫ y, F y ∂ν‖ ≤ m := norm_integral_le_integral_norm F
  have hnn : 0 ≤ ∫ y, (‖F y‖ - m) ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  have hexp : ∫ y, (‖F y‖ - m) ^ 2 ∂ν = (∫ y, ‖F y‖ ^ 2 ∂ν) - m ^ 2 := by
    have e₀ : ∀ y, (‖F y‖ - m) ^ 2 = ‖F y‖ ^ 2 - (2 * m) * ‖F y‖ + m ^ 2 := fun y => by ring
    have e₁ : Integrable (fun y => (2 * m) * ‖F y‖) ν := hF.norm.const_mul _
    have e₂ : Integrable (fun y => ‖F y‖ ^ 2 - (2 * m) * ‖F y‖) ν := hF2.sub e₁
    simp only [e₀]
    rw [integral_add e₂ (integrable_const _), integral_sub hF2 e₁, integral_const_mul,
      integral_const]
    simp only [probReal_univ, one_smul, ← hm]
    ring
  nlinarith [norm_nonneg (∫ y, F y ∂ν)]
theorem memLp_fiberIntegral [IsProbabilityMeasure μ] {F : X × Y → ℂ} (hF : MemLp F 2 (μ.prod ν)) :
    MemLp (fun x => ∫ y, F (x, y) ∂ν) 2 μ ∧
      ∫ x, ‖∫ y, F (x, y) ∂ν‖ ^ 2 ∂μ ≤ ∫ p, ‖F p‖ ^ 2 ∂μ.prod ν := by
  have hF2 : Integrable (fun p => ‖F p‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm hF.1).1 hF
  have hF1 : Integrable F (μ.prod ν) := hF.integrable one_le_two
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, F (x, y) ∂ν) μ := hF.1.integral_prod_right'
  have hB : Integrable (fun x => ∫ y, ‖F (x, y)‖ ^ 2 ∂ν) μ := hF2.integral_prod_left
  have hpt : ∀ᵐ x ∂μ, ‖∫ y, F (x, y) ∂ν‖ ^ 2 ≤ ∫ y, ‖F (x, y)‖ ^ 2 ∂ν := by
    filter_upwards [hF1.prod_right_ae, hF2.prod_right_ae] with x ha hb
    exact sq_norm_integral_le_integral_sq ha hb
  have hA : Integrable (fun x => ‖∫ y, F (x, y) ∂ν‖ ^ 2) μ := by
    refine hB.mono' (hmeas.norm.pow 2) ?_
    filter_upwards [hpt] with x hx
    rwa [Real.norm_of_nonneg (by positivity)]
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).2 hA, ?_⟩
  rw [integral_prod _ hF2]
  exact integral_mono_ae hA hB hpt
theorem fiberIntegral_congr_ae [SFinite μ] {F F' : X × Y → ℂ} (hFF : F =ᵐ[μ.prod ν] F') :
    (fun x => ∫ y, F (x, y) ∂ν) =ᵐ[μ] fun x => ∫ y, F' (x, y) ∂ν := by
  filter_upwards [Measure.ae_ae_of_ae_prod hFF] with x hx
  exact integral_congr_ae hx
theorem norm_sq_eq_integral_norm_sq (f : Lp ℂ 2 ν) :
    ‖f‖ ^ 2 = ∫ y, ‖(f : Y → ℂ) y‖ ^ 2 ∂ν := by
  have e := @inner_self_eq_norm_sq_to_K ℂ _ _ _ _ f
  rw [L2.inner_def] at e
  have e' : ∀ y, inner ℂ ((f : Y → ℂ) y) ((f : Y → ℂ) y) = ((‖(f : Y → ℂ) y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp only [e'] at e
  rw [integral_complex_ofReal] at e
  have e₂ : ((∫ y, ‖(f : Y → ℂ) y‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [e]
    push_cast
    rfl
  exact (Complex.ofReal_injective e₂).symm
end General
section Invariance
variable {V : Type} [Finite V]
def inverseOn (s : Finset V) (g : V → specialUnitary) : V → specialUnitary :=
  open Classical in fun b => if b ∈ s then (g b)⁻¹ else g b
theorem inverseOn_measurePreserving (hH : HaarPiInvariance V) (s : Finset V) :
    MeasurePreserving (inverseOn s) (haarPi V) (haarPi V) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : inverseOn (∅ : Finset V) = id := by
      funext g b
      simp [inverseOn]
    rw [this]
    exact MeasurePreserving.id _
  | insert c s hc ih =>
    have : inverseOn (insert c s) = invertAt c ∘ inverseOn s := by
      funext g b
      by_cases hb : b = c
      · subst hb
        simp [inverseOn, invertAt, hc]
      · simp [inverseOn, invertAt, hb]
    rw [this]
    exact (hH.2.1 c).comp ih
theorem inv_measurePreserving (hH : HaarPiInvariance V) :
    MeasurePreserving (fun g : V → specialUnitary => g⁻¹) (haarPi V) (haarPi V) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  have : (fun g : V → specialUnitary => g⁻¹) = inverseOn Finset.univ := by
    funext g b
    simp [inverseOn]
  rw [this]
  exact inverseOn_measurePreserving hH _
theorem mulLeft_measurePreserving (hH : HaarPiInvariance V) (k : V → specialUnitary) :
    MeasurePreserving (fun g : V → specialUnitary => k * g) (haarPi V) (haarPi V) := by
  have : (fun g : V → specialUnitary => k * g) = fun (g : V → specialUnitary) (b : V) => k b * g b * 1 := by
    funext g b
    simp
  rw [this]
  exact hH.1 k 1
theorem integral_inv_haarPi (hH : HaarPiInvariance V) (F : (V → specialUnitary) → ℂ) :
    ∫ g, F g⁻¹ ∂haarPi V = ∫ g, F g ∂haarPi V :=
  (inv_measurePreserving hH).integral_comp (Homeomorph.inv (V → specialUnitary)).measurableEmbedding F
theorem integral_mulLeft_haarPi (hH : HaarPiInvariance V) (k : V → specialUnitary)
    (F : (V → specialUnitary) → ℂ) :
    ∫ g, F (k * g) ∂haarPi V = ∫ g, F g ∂haarPi V :=
  (mulLeft_measurePreserving hH k).integral_comp (Homeomorph.mulLeft k).measurableEmbedding F
end Invariance
section Average
variable {J V : Type} [Finite J] [Finite V] (t h : J → V)
def actInv (p : (J → specialUnitary) × (V → specialUnitary)) : J → specialUnitary :=
  twistedConjAction t h p.2⁻¹ p.1
theorem continuous_actInv : Continuous (actInv t h) := by
  refine continuous_pi fun b => ?_
  show Continuous fun p : (J → specialUnitary) × (V → specialUnitary) =>
    (p.2 (t b))⁻¹ * p.1 b * ((p.2 (h b))⁻¹)⁻¹
  fun_prop
variable {t h}
theorem twisted_measurePreserving (hH : HaarPiInvariance J) (g : V → specialUnitary) :
    MeasurePreserving (twistedConjAction t h g) (haarPi J) (haarPi J) :=
  hH.1 (fun b => g (t b)) fun b => (g (h b))⁻¹
theorem skew_measurePreserving (hH : HaarPiInvariance J) :
    MeasurePreserving (fun p : (V → specialUnitary) × (J → specialUnitary) =>
        (p.1, twistedConjAction t h p.1⁻¹ p.2))
      ((haarPi V).prod (haarPi J))
      ((haarPi V).prod (haarPi J)) := by
  have hm : Measurable fun p : (V → specialUnitary) × (J → specialUnitary) =>
      twistedConjAction t h p.1⁻¹ p.2 := by
    have hc := (continuous_actInv t h).measurable
    have hs : Measurable (Prod.swap : (V → specialUnitary) × (J → specialUnitary) → _) := measurable_swap
    have hcs := hc.comp hs
    exact hcs
  exact MeasurePreserving.skew_product (MeasurePreserving.id (haarPi V)) hm
    (Filter.Eventually.of_forall fun g => (twisted_measurePreserving hH g⁻¹).map_eq)
theorem actInv_measurePreserving (hH : HaarPiInvariance J) :
    MeasurePreserving (actInv t h) ((haarPi J).prod (haarPi V)) (haarPi J) := by
  have e₁ : MeasurePreserving (fun p : (V → specialUnitary) × (J → specialUnitary) =>
      twistedConjAction t h p.1⁻¹ p.2) ((haarPi V).prod (haarPi J)) (haarPi J) :=
    measurePreserving_snd.comp (skew_measurePreserving hH)
  have e₂ : MeasurePreserving (Prod.swap : (J → specialUnitary) × (V → specialUnitary) → _)
      ((haarPi J).prod (haarPi V)) ((haarPi V).prod (haarPi J)) := Measure.measurePreserving_swap
  have e₃ := e₁.comp e₂
  exact e₃
theorem memLp_comp_actInv (hH : HaarPiInvariance J) (f : HaarL2 J) :
    MemLp (fun p => (f : (J → specialUnitary) → ℂ) (actInv t h p)) 2
      ((haarPi J).prod (haarPi V)) :=
  (Lp.memLp f).comp_measurePreserving (actInv_measurePreserving hH)
def averageFun (t h : J → V) (f : HaarL2 J) (u : J → specialUnitary) : ℂ :=
  ∫ g, (f : (J → specialUnitary) → ℂ) (actInv t h (u, g)) ∂haarPi V
theorem memLp_averageFun (hH : HaarPiInvariance J) (f : HaarL2 J) :
    MemLp (averageFun t h f) 2 (haarPi J) :=
  (memLp_fiberIntegral (memLp_comp_actInv hH f)).1
def averageLinear (t h : J → V) (hH : HaarPiInvariance J) :
    HaarL2 J →ₗ[ℂ] HaarL2 J where
  toFun f := (memLp_averageFun hH f).toLp _
  map_add' f f' := by
    have hq := (actInv_measurePreserving (t := t) (h := h) (V := V) hH).quasiMeasurePreserving
    refine Lp.ext ?_
    refine (MemLp.coeFn_toLp _).trans ?_
    refine Filter.EventuallyEq.trans ?_ (Filter.EventuallyEq.add (MemLp.coeFn_toLp _)
      (MemLp.coeFn_toLp _)).symm |>.trans (Lp.coeFn_add _ _).symm
    refine (fiberIntegral_congr_ae (hq.ae_eq_comp (Lp.coeFn_add f f'))).trans ?_
    have hf := (memLp_comp_actInv (t := t) (h := h) (V := V) hH f).integrable one_le_two
    have hf' := (memLp_comp_actInv (t := t) (h := h) (V := V) hH f').integrable one_le_two
    filter_upwards [hf.prod_right_ae, hf'.prod_right_ae] with u ha hb
    exact integral_add ha hb
  map_smul' c f := by
    have hq := (actInv_measurePreserving (t := t) (h := h) (V := V) hH).quasiMeasurePreserving
    refine Lp.ext ?_
    refine (MemLp.coeFn_toLp _).trans ?_
    refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul c _).symm
    refine (fiberIntegral_congr_ae (hq.ae_eq_comp (Lp.coeFn_smul c f))).trans ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_averageFun (t := t) (h := h) hH f)] with u hu
    simp only [Pi.smul_apply, hu]
    exact integral_smul c _
theorem norm_averageLinear_le (hH : HaarPiInvariance J) (f : HaarL2 J) :
    ‖averageLinear t h hH f‖ ≤ 1 * ‖f‖ := by
  have hmp := actInv_measurePreserving (t := t) (h := h) (V := V) hH
  rw [one_mul]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_sq_eq_integral_norm_sq, norm_sq_eq_integral_norm_sq]
  have e₁ : ∫ u, ‖(averageLinear t h hH f : (J → specialUnitary) → ℂ) u‖ ^ 2 ∂haarPi J =
      ∫ u, ‖averageFun t h f u‖ ^ 2 ∂haarPi J := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_averageFun (t := t) (h := h) hH f)] with u hu
    show ‖(((memLp_averageFun (t := t) (h := h) hH f).toLp _ :
      HaarL2 J) : (J → specialUnitary) → ℂ) u‖ ^ 2 = _
    rw [hu]
  have e₂ : ∫ p, ‖(f : (J → specialUnitary) → ℂ) (actInv t h p)‖ ^ 2
      ∂(haarPi J).prod (haarPi V) =
      ∫ u, ‖(f : (J → specialUnitary) → ℂ) u‖ ^ 2 ∂haarPi J := by
    have hm : AEStronglyMeasurable (fun u => ‖(f : (J → specialUnitary) → ℂ) u‖ ^ 2)
        (Measure.map (actInv t h) ((haarPi J).prod (haarPi V))) := by
      rw [hmp.map_eq]
      exact (Lp.aestronglyMeasurable f).norm.pow 2
    have hmap := integral_map hmp.aemeasurable hm
    rw [hmp.map_eq] at hmap
    exact hmap.symm
  rw [e₁, ← e₂]
  exact (memLp_fiberIntegral (memLp_comp_actInv hH f)).2
def averageOp (t h : J → V) (hH : HaarPiInvariance J) : HaarL2 J →L[ℂ] HaarL2 J :=
  (averageLinear t h hH).mkContinuous 1 (norm_averageLinear_le hH)
theorem isTwistedAverage_averageOp (hH : HaarPiInvariance J) :
    IsTwistedAverage t h (averageOp t h hH) :=
  fun f => MemLp.coeFn_toLp (memLp_averageFun (t := t) (h := h) hH f)
theorem integrable_inner_comp_actInv (hH : HaarPiInvariance J) (f₁ f₂ : HaarL2 J) :
    Integrable (fun p : (J → specialUnitary) × (V → specialUnitary) =>
        inner ℂ ((f₁ : (J → specialUnitary) → ℂ) p.1) ((f₂ : (J → specialUnitary) → ℂ) (actInv t h p)))
      ((haarPi J).prod (haarPi V)) := by
  have h₁ : MemLp (fun p : (J → specialUnitary) × (V → specialUnitary) => (f₁ : (J → specialUnitary) → ℂ) p.1) 2
      ((haarPi J).prod (haarPi V)) :=
    (Lp.memLp f₁).comp_measurePreserving measurePreserving_fst
  have h₂ := memLp_comp_actInv (t := t) (h := h) (V := V) hH f₂
  refine (L2.integrable_inner (𝕜 := ℂ) (h₁.toLp _) (h₂.toLp _)).congr ?_
  filter_upwards [h₁.coeFn_toLp, h₂.coeFn_toLp] with p ha hb
  rw [ha, hb]
theorem inner_eq_integral_of_isTwistedTranslation {g : V → specialUnitary}
    {T : HaarL2 J →L[ℂ] HaarL2 J} (hT : IsTwistedTranslation t h g T)
    (ψ φ : HaarL2 J) :
    inner ℂ ψ (T φ) = ∫ u, inner ℂ ((ψ : (J → specialUnitary) → ℂ) u)
      ((φ : (J → specialUnitary) → ℂ) (actInv t h (u, g))) ∂haarPi J := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hT φ] with u hu
  rw [hu]
  rfl
theorem integrable_inner_of_isTwistedTranslation (hH : HaarPiInvariance J)
    {ρ : (V → specialUnitary) → HaarL2 J →L[ℂ] HaarL2 J}
    (hρ : ∀ g, IsTwistedTranslation t h g (ρ g)) (ψ φ : HaarL2 J) :
    Integrable (fun g => inner ℂ ψ (ρ g φ)) (haarPi V) := by
  simp only [fun g => inner_eq_integral_of_isTwistedTranslation (hρ g) ψ φ]
  exact (integrable_inner_comp_actInv hH ψ φ).integral_prod_right
theorem inner_average_eq_integral (hH : HaarPiInvariance J)
    {ρ : (V → specialUnitary) → HaarL2 J →L[ℂ] HaarL2 J}
    (hρ : ∀ g, IsTwistedTranslation t h g (ρ g))
    {P : HaarL2 J →L[ℂ] HaarL2 J} (hP : IsTwistedAverage t h P)
    (ψ φ : HaarL2 J) :
    inner ℂ ψ (P φ) = ∫ g, inner ℂ ψ (ρ g φ) ∂haarPi V := by
  have hint := integrable_inner_comp_actInv (t := t) (h := h) (V := V) hH ψ φ
  have hφ := (memLp_comp_actInv (t := t) (h := h) (V := V) hH φ).integrable one_le_two
  calc inner ℂ ψ (P φ)
      = ∫ u, ∫ g, inner ℂ ((ψ : (J → specialUnitary) → ℂ) u)
          ((φ : (J → specialUnitary) → ℂ) (actInv t h (u, g))) ∂haarPi V
          ∂haarPi J := by
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [hP φ, hφ.prod_right_ae] with u hu hi
        rw [hu]
        exact (integral_inner hi _).symm
    _ = ∫ g, ∫ u, inner ℂ ((ψ : (J → specialUnitary) → ℂ) u)
          ((φ : (J → specialUnitary) → ℂ) (actInv t h (u, g))) ∂haarPi J
          ∂haarPi V :=
        integral_integral_swap (f := fun u g => inner ℂ ((ψ : (J → specialUnitary) → ℂ) u)
          ((φ : (J → specialUnitary) → ℂ) (actInv t h (u, g)))) hint
    _ = ∫ g, inner ℂ ψ (ρ g φ) ∂haarPi V := by
        simp only [fun g => inner_eq_integral_of_isTwistedTranslation (hρ g) ψ φ]
end Average
theorem twistedAverage_holds (hO : TwistedActionOperators.Statement)
    (hS : GibbsHaarKernels.Statement) :
    TwistedAverageStatement := by
  intro J V _ _ _ _ t h
  have hHJ : HaarPiInvariance J := hS.2.1 J
  have hHV : HaarPiInvariance V := hS.2.1 V
  refine ⟨⟨averageOp t h hHJ, isTwistedAverage_averageOp hHJ⟩, fun ρ P hρ hP => ?_⟩
  obtain ⟨-, hunit, hmul, hone, -⟩ := (hO J V t h).2 ρ hρ
  have hform : ∀ ψ φ : HaarL2 J,
      inner ℂ ψ (P φ) = ∫ g, inner ℂ ψ (ρ g φ) ∂haarPi V :=
    inner_average_eq_integral hHJ hρ hP
  have hadj : ∀ (g : V → specialUnitary) (ψ φ : HaarL2 J),
      inner ℂ ψ (ρ g φ) = inner ℂ (ρ g⁻¹ ψ) φ := by
    intro g ψ φ
    have e₁ : ρ g (ρ g⁻¹ ψ) = ψ := by
      have e₂ := hmul g g⁻¹
      rw [mul_inv_cancel, hone] at e₂
      exact DFunLike.congr_fun e₂ ψ
    rw [← hunit g (ρ g⁻¹ ψ) φ, e₁]
  have hsym : IsSymmetricOp P := by
    intro φ ψ
    rw [hform φ ψ, ← inner_conj_symm (P φ) ψ, hform ψ φ, ← integral_conj,
      ← integral_inv_haarPi hHV fun g => (starRingEnd ℂ) (inner ℂ ψ (ρ g φ))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show inner ℂ φ (ρ g ψ) = (starRingEnd ℂ) (inner ℂ ψ (ρ g⁻¹ φ))
    rw [inner_conj_symm, hadj g φ ψ]
  have hfix : ∀ φ : HaarL2 J, (∀ g, ρ g φ = φ) → P φ = φ := by
    intro φ hφ
    refine ext_inner_left ℂ fun ψ => ?_
    rw [hform]
    simp [hφ]
  have hinv : ∀ (k : V → specialUnitary) (φ : HaarL2 J), ρ k (P φ) = P φ := by
    intro k φ
    refine ext_inner_left ℂ fun ψ => ?_
    rw [hadj k ψ (P φ), hform, hform,
      ← integral_mulLeft_haarPi hHV k fun g => inner ℂ ψ (ρ g φ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show inner ℂ (ρ k⁻¹ ψ) (ρ g φ) = inner ℂ ψ (ρ (k * g) φ)
    rw [← hmul k g]
    show _ = inner ℂ ψ (ρ k (ρ g φ))
    rw [hadj k ψ]
  refine ⟨integrable_inner_of_isTwistedTranslation hHJ hρ, hform, hsym, ?_, ?_, ?_⟩
  · exact ContinuousLinearMap.ext fun φ => hfix (P φ) fun g => hinv g φ
  · ext φ
    constructor
    · rintro ⟨φ, rfl⟩ g
      exact hinv g φ
    · intro hφ
      exact ⟨φ, hfix φ hφ⟩
  · intro A hA hcomm
    refine ContinuousLinearMap.ext fun φ => ext_inner_left ℂ fun ψ => ?_
    show inner ℂ ψ (A (P φ)) = inner ℂ ψ (P (A φ))
    rw [hA ψ (P φ), hform, hform]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show inner ℂ (A ψ) (ρ g φ) = inner ℂ ψ (ρ g (A φ))
    rw [← hA ψ (ρ g φ)]
    exact congrArg (inner ℂ ψ) (DFunLike.congr_fun (hcomm g) φ)
end TwistedAverage
end YangMills.Construction.TransferOperators
end
