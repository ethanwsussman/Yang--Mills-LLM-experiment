import YangMills.Construction.LinearAlgebra.TraceSixFoldProductProof
import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.CyclicityAndTransposeOfTheTraceNumberProof
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.OrderOfHermitianMatricesUnderARootProof
import YangMills.Construction.PeriodicOperators.TraceOfAProductOfSixJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SixJetTraceProof
open JetQuad
open YangMills.Construction.TraceBound (schattenThreeNorm IsHermitianForm formNorm)
open YangMills.Construction.RealPower (rpowPos sqrtOf)
theorem sqrtOf_eq_sqrt {x : ℝ} (hx : 0 ≤ x) : sqrtOf x = √x := by apply _root_.YangMills.Construction.TraceBound.sqrtOf_eq_sqrt <;> assumption
theorem rpowPos_nonneg (x t : ℝ) : 0 ≤ rpowPos x t := by
  unfold rpowPos
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl
theorem quotWeight_pos {I : PeriodicData} (hI : IsPeriodic I) (c : I.UnitQuot) :
    0 < I.quotWeight 1 c := by apply _root_.YangMills.SharedProofs.p9241 <;> assumption
section Weighted
variable {J : Type} [Fintype J] (w : J → ℝ)
theorem wInner_eq_sum (v u : J → ℂ) :
    wInner w v u = ∑ i, (w i : ℂ) * (starRingEnd ℂ (v i) * u i) := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.wInner_eq_sum <;> assumption
theorem wInner_self (v : J → ℂ) :
    wInner w v v = ((∑ i, w i * ‖v i‖ ^ 2 : ℝ) : ℂ) := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.wInner_self_eq <;> assumption
variable {w}
theorem wInner_isHermitianForm (hw : ∀ i, 0 < w i) : IsHermitianForm (wInner w) where
  linear_right v :=
    { map_add := fun u u' => by
        simp only [wInner_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul := fun a u => by
        simp only [wInner_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring }
  conj_symm v u := by
    simp only [wInner_eq_sum, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  pos v hv := by
    rw [wInner_self]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    have : 0 < ∑ i, w i * ‖v i‖ ^ 2 :=
      Finset.sum_pos' (fun j _ => mul_nonneg (hw j).le (sq_nonneg _))
        ⟨i, Finset.mem_univ _, mul_pos (hw i) (pow_pos (norm_pos_iff.2 (by simpa using hi)) 2)⟩
    exact_mod_cast this
theorem formNorm_wInner (hw : ∀ i, 0 < w i) (v : J → ℂ) :
    formNorm (wInner w) v = wNorm w v := by
  unfold formNorm wNorm
  rw [wInner_self, Complex.ofReal_re, tsum_fintype,
    sqrtOf_eq_sqrt (Finset.sum_nonneg fun j _ => mul_nonneg (hw j).le (sq_nonneg _))]
theorem opNormE_le_of_wOpNorm_le (hw : ∀ i, 0 < w i) (M : Module.End ℂ (J → ℂ)) {n : ℝ}
    (hn : 0 ≤ n) (h : wOpNorm w w univ (fun f => M f) ≤ ENNReal.ofReal n) :
    YangMills.Construction.TraceBound.opNormE (wInner w) M ≤ (n : EReal) := by
  unfold YangMills.Construction.TraceBound.opNormE
  refine sSup_le ?_
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v ∈ wUnitBall w univ :=
    ⟨mem_univ _, (hasSum_fintype _).summable, by
      rw [← formNorm_wInner hw]
      exact hv⟩
  have h1 : ENNReal.ofReal (wNorm w (M v)) ≤ wOpNorm w w univ (fun f => M f) :=
    le_iSup₂ (f := fun f (_ : f ∈ wUnitBall w univ) => ENNReal.ofReal (wNorm w (M f))) v hv'
  have h2 := (ENNReal.ofReal_le_ofReal_iff hn).1 (h1.trans h)
  change ((formNorm (wInner w) (M v) : ℝ) : EReal) ≤ (n : EReal)
  rw [formNorm_wInner hw]
  exact EReal.coe_le_coe_iff.2 h2
theorem opNormE_nonneg (hw : ∀ i, 0 < w i) (M : Module.End ℂ (J → ℂ)) :
    0 ≤ YangMills.Construction.TraceBound.opNormE (wInner w) M := by
  have hz : formNorm (wInner w) (0 : J → ℂ) = 0 := by
    rw [formNorm_wInner hw]
    simp [wNorm]
  unfold YangMills.Construction.TraceBound.opNormE
  refine le_sSup ⟨0, ?_, ?_⟩
  · simp [hz]
  · simp [hz]
def schattenCube (w : J → ℝ) (M : (J → ℂ) →ₗ[ℂ] (J → ℂ)) : ℝ :=
  rpowPos (schattenThreeNorm (wInner w) M) 3
theorem norm_trace_sixFold_le (six : YangMills.Construction.TraceBound.TraceSixFoldProductBound)
    [Nonempty J] (hw : ∀ i, 0 < w i) (A₁ A₂ A₃ B₁ B₂ B₃ : (J → ℂ) →ₗ[ℂ] (J → ℂ))
    {n₁ n₂ n₃ : ℝ} (h₁ : 0 ≤ n₁) (h₂ : 0 ≤ n₂) (h₃ : 0 ≤ n₃)
    (hB₁ : wOpNorm w w univ (fun f => B₁ f) ≤ ENNReal.ofReal n₁)
    (hB₂ : wOpNorm w w univ (fun f => B₂ f) ≤ ENNReal.ofReal n₂)
    (hB₃ : wOpNorm w w univ (fun f => B₃ f) ≤ ENNReal.ofReal n₃) :
    ‖LinearMap.trace ℂ (J → ℂ) (A₁.comp (B₁.comp (A₂.comp (B₂.comp (A₃.comp B₃)))))‖ ≤
      1 / 3 * (schattenCube w A₁ + schattenCube w A₂ + schattenCube w A₃) * (n₁ * n₂ * n₃) := by
  obtain ⟨hall, -, htr⟩ := six (Fintype.card J) Fintype.card_pos (J → ℂ)
    (Module.finrank_fintype_fun_eq_card ℂ) (wInner w) (wInner_isHermitianForm hw)
  obtain ⟨r₁, hr₁⟩ := (hall B₁).2.1
  obtain ⟨r₂, hr₂⟩ := (hall B₂).2.1
  obtain ⟨r₃, hr₃⟩ := (hall B₃).2.1
  have hle : ∀ (B : Module.End ℂ (J → ℂ)) (r n : ℝ),
      YangMills.Construction.TraceBound.opNormE (wInner w) B = r → 0 ≤ n →
      wOpNorm w w univ (fun f => B f) ≤ ENNReal.ofReal n → 0 ≤ r ∧ r ≤ n := by
    intro B r n hr hn hB
    have a := opNormE_nonneg hw B
    have b := opNormE_le_of_wOpNorm_le hw B hn hB
    rw [hr] at a b
    exact ⟨by exact_mod_cast a, EReal.coe_le_coe_iff.1 b⟩
  obtain ⟨p₁, q₁⟩ := hle B₁ r₁ n₁ hr₁ h₁ hB₁
  obtain ⟨p₂, q₂⟩ := hle B₂ r₂ n₂ hr₂ h₂ hB₂
  obtain ⟨p₃, q₃⟩ := hle B₃ r₃ n₃ hr₃ h₃ hB₃
  have h := htr A₁ A₂ A₃ B₁ B₂ B₃
  have h' := h.1.trans h.2
  rw [hr₁, hr₂, hr₃] at h'
  have h'' : ‖LinearMap.trace ℂ (J → ℂ) (A₁ * B₁ * A₂ * B₂ * A₃ * B₃)‖ ≤
      1 / 3 * (schattenCube w A₁ + schattenCube w A₂ + schattenCube w A₃) * r₁ * r₂ * r₃ := by
    exact_mod_cast h'
  have hc : 0 ≤ 1 / 3 * (schattenCube w A₁ + schattenCube w A₂ + schattenCube w A₃) := by
    have := rpowPos_nonneg (schattenThreeNorm (wInner w) A₁) 3
    have := rpowPos_nonneg (schattenThreeNorm (wInner w) A₂) 3
    have := rpowPos_nonneg (schattenThreeNorm (wInner w) A₃) 3
    unfold schattenCube
    positivity
  have hm : r₁ * r₂ * r₃ ≤ n₁ * n₂ * n₃ :=
    mul_le_mul (mul_le_mul q₁ q₂ p₂ h₁) q₃ p₃ (mul_nonneg h₁ h₂)
  calc ‖LinearMap.trace ℂ (J → ℂ) (A₁.comp (B₁.comp (A₂.comp (B₂.comp (A₃.comp B₃)))))‖
      = ‖LinearMap.trace ℂ (J → ℂ) (A₁ * B₁ * A₂ * B₂ * A₃ * B₃)‖ := rfl
    _ ≤ 1 / 3 * (schattenCube w A₁ + schattenCube w A₂ + schattenCube w A₃) * r₁ * r₂ * r₃ := h''
    _ = 1 / 3 * (schattenCube w A₁ + schattenCube w A₂ + schattenCube w A₃) * (r₁ * r₂ * r₃) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm hc
end Weighted
section Means
def torusMean (f : (Fin 4 → ℝ) → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 4)⁻¹ * ∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), f κ
def MeanLE (γ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  Continuous f ∧ torusMean f ≤ γ
theorem integrableOn_torusBox {f : (Fin 4 → ℝ) → ℝ} (hf : Continuous f) :
    MeasureTheory.IntegrableOn f (Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)) :=
  hf.continuousOn.integrableOn_compact isCompact_Icc
theorem MeanLE.add {γ γ' : ℝ} {f g : (Fin 4 → ℝ) → ℝ} (hf : MeanLE γ f)
    (hg : MeanLE γ' g) : MeanLE (γ + γ') fun κ => f κ + g κ := by
  refine ⟨hf.1.add hg.1, ?_⟩
  have e : torusMean (fun κ => f κ + g κ) = torusMean f + torusMean g := by
    unfold torusMean
    rw [MeasureTheory.integral_add (integrableOn_torusBox hf.1) (integrableOn_torusBox hg.1),
      mul_add]
  rw [e]
  exact add_le_add hf.2 hg.2
theorem MeanLE.third_mul {γ n : ℝ} {f g h : (Fin 4 → ℝ) → ℝ} (hf : MeanLE γ f)
    (hg : MeanLE γ g) (hh : MeanLE γ h) (hn : 0 ≤ n) :
    MeanLE (γ * n) fun κ => 1 / 3 * (f κ + g κ + h κ) * n := by
  refine ⟨by have := hf.1; have := hg.1; have := hh.1; fun_prop, ?_⟩
  have hs := (hf.add hg).add hh
  have e : torusMean (fun κ => 1 / 3 * (f κ + g κ + h κ) * n) =
      1 / 3 * torusMean (fun κ => f κ + g κ + h κ) * n := by
    unfold torusMean
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
    ring
  rw [e]
  have := hs.2
  have h3 : 1 / 3 * torusMean (fun κ => f κ + g κ + h κ) ≤ γ := by linarith
  exact mul_le_mul_of_nonneg_right h3 hn
end Means
section Expansion
variable {I : PeriodicData}
theorem f11_mul_alternating (p z : Fin 4 → ℂ) (A : (Fin 4 → ℂ) → QuotHom I I)
    (B₁ B₂ B₃ : JetQuad I I) :
    (mul p (⟨A, 0, 0, 0⟩ : JetQuad I I) (mul p B₁ (mul p (⟨A, 0, 0, 0⟩ : JetQuad I I)
      (mul p B₂ (mul p (⟨A, 0, 0, 0⟩ : JetQuad I I) B₃))))).f11 z =
      (A z).comp ((B₁.f11 z).comp ((A z).comp ((B₂.f00 z).comp ((A z).comp (B₃.f00 z))))) +
      (A z).comp ((B₁.f00 z).comp ((A z).comp ((B₂.f11 z).comp ((A z).comp (B₃.f00 z))))) +
      (A z).comp ((B₁.f00 z).comp ((A z).comp ((B₂.f00 z).comp ((A z).comp (B₃.f11 z))))) +
      (A z).comp ((B₁.f00 z).comp ((A z).comp ((B₂.f10 (z - p)).comp
        ((A (z - p)).comp (B₃.f01 z))))) +
      (A z).comp ((B₁.f00 z).comp ((A z).comp ((B₂.f01 (z + p)).comp
        ((A (z + p)).comp (B₃.f10 z))))) +
      (A z).comp ((B₁.f10 (z - p)).comp ((A (z - p)).comp ((B₂.f01 z).comp
        ((A z).comp (B₃.f00 z))))) +
      (A z).comp ((B₁.f10 (z - p)).comp ((A (z - p)).comp ((B₂.f00 (z - p)).comp
        ((A (z - p)).comp (B₃.f01 z))))) +
      (A z).comp ((B₁.f01 (z + p)).comp ((A (z + p)).comp ((B₂.f10 z).comp
        ((A z).comp (B₃.f00 z))))) +
      (A z).comp ((B₁.f01 (z + p)).comp ((A (z + p)).comp ((B₂.f00 (z + p)).comp
        ((A (z + p)).comp (B₃.f10 z))))) := by
  simp only [JetQuad.mul, LinearMap.comp_add, LinearMap.zero_comp, Pi.zero_apply, add_zero,
    zero_add]
  abel
end Expansion
section Assembly
theorem norm_torusAverage_le {g : (Fin 4 → ℝ) → ℂ} {H : (Fin 4 → ℝ) → ℝ} {s : ℝ}
    (hH : MeanLE s H) (h : ∀ κ, ‖g κ‖ ≤ H κ) : ‖torusAverage g‖ ≤ s := by
  have hc : 0 ≤ ((2 * Real.pi) ^ 4)⁻¹ := by positivity
  unfold torusAverage
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  have hi : ‖∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), g κ‖ ≤
      ∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), H κ :=
    (MeasureTheory.norm_integral_le_integral_norm _).trans
      (MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (integrableOn_torusBox hH.1) (Filter.Eventually.of_forall h))
  exact (mul_le_mul_of_nonneg_left hi hc).trans hH.2
theorem norm_sum_nine_le (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : ℂ) (y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (h₁ : ‖x₁‖ ≤ y₁) (h₂ : ‖x₂‖ ≤ y₂) (h₃ : ‖x₃‖ ≤ y₃) (h₄ : ‖x₄‖ ≤ y₄) (h₅ : ‖x₅‖ ≤ y₅)
    (h₆ : ‖x₆‖ ≤ y₆) (h₇ : ‖x₇‖ ≤ y₇) (h₈ : ‖x₈‖ ≤ y₈) (h₉ : ‖x₉‖ ≤ y₉) :
    ‖x₁ + x₂ + x₃ + x₄ + x₅ + x₆ + x₇ + x₈ + x₉‖ ≤ y₁ + y₂ + y₃ + y₄ + y₅ + y₆ + y₇ + y₈ + y₉ := by
  have e₂ := norm_add_le x₁ x₂
  have e₃ := norm_add_le (x₁ + x₂) x₃
  have e₄ := norm_add_le (x₁ + x₂ + x₃) x₄
  have e₅ := norm_add_le (x₁ + x₂ + x₃ + x₄) x₅
  have e₆ := norm_add_le (x₁ + x₂ + x₃ + x₄ + x₅) x₆
  have e₇ := norm_add_le (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) x₇
  have e₈ := norm_add_le (x₁ + x₂ + x₃ + x₄ + x₅ + x₆ + x₇) x₈
  have e₉ := norm_add_le (x₁ + x₂ + x₃ + x₄ + x₅ + x₆ + x₇ + x₈) x₉
  linarith
theorem nine_products_le_prod_sums {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ a₃ b₃ c₃ d₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁) (hc₁ : 0 ≤ c₁) (hd₁ : 0 ≤ d₁)
    (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) (hc₂ : 0 ≤ c₂) (hd₂ : 0 ≤ d₂)
    (ha₃ : 0 ≤ a₃) (hb₃ : 0 ≤ b₃) (hc₃ : 0 ≤ c₃) (hd₃ : 0 ≤ d₃) :
    d₁ * a₂ * a₃ + a₁ * d₂ * a₃ + a₁ * a₂ * d₃ + a₁ * b₂ * c₃ + a₁ * c₂ * b₃ + b₁ * c₂ * a₃ +
        b₁ * a₂ * c₃ + c₁ * b₂ * a₃ + c₁ * a₂ * b₃ ≤
      (a₁ + b₁ + c₁ + d₁) * (a₂ + b₂ + c₂ + d₂) * (a₃ + b₃ + c₃ + d₃) := by
  rw [← sub_nonneg]
  ring_nf
  positivity
variable {I : PeriodicData}
structure ComponentSup (δ : ℝ) (p : Fin 4 → ℂ) (T : JetQuad I I) (a b c d : ℝ) : Prop where
  nonneg_a : 0 ≤ a
  nonneg_b : 0 ≤ b
  nonneg_c : 0 ≤ c
  nonneg_d : 0 ≤ d
  le_a : ∀ κ ∈ imStrip (2 * δ), quotHomNorm (T.f00 κ) ≤ ENNReal.ofReal a
  le_b : ∀ κ ∈ stripAddShift δ p, quotHomNorm (T.f10 κ) ≤ ENNReal.ofReal b
  le_c : ∀ κ ∈ stripSubShift δ p, quotHomNorm (T.f01 κ) ≤ ENNReal.ofReal c
  le_d : ∀ κ ∈ realDualPoints, quotHomNorm (T.f11 κ) ≤ ENNReal.ofReal d
  jetNorm_eq : jetNorm δ p T = ENNReal.ofReal (a + b + c + d)
theorem exists_componentSup {δ : ℝ} {p : Fin 4 → ℂ} {T : JetQuad I I}
    (h : JetDomains.SupsFinite δ p T) : ∃ a b c d, ComponentSup δ p T a b c d := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  have t₀ := ENNReal.toReal_nonneg (a := ⨆ κ ∈ imStrip (2 * δ), quotHomNorm (T.f00 κ))
  have t₁ := ENNReal.toReal_nonneg (a := ⨆ κ ∈ stripAddShift δ p, quotHomNorm (T.f10 κ))
  have t₂ := ENNReal.toReal_nonneg (a := ⨆ κ ∈ stripSubShift δ p, quotHomNorm (T.f01 κ))
  have t₃ := ENNReal.toReal_nonneg (a := ⨆ κ ∈ realDualPoints, quotHomNorm (T.f11 κ))
  refine ⟨_, _, _, _, t₀, t₁, t₂, t₃, fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_,
    fun κ hκ => ?_, ?_⟩
  · rw [ENNReal.ofReal_toReal h₀.ne]
    exact le_iSup₂ (f := fun κ (_ : κ ∈ imStrip (2 * δ)) => quotHomNorm (T.f00 κ)) κ hκ
  · rw [ENNReal.ofReal_toReal h₁.ne]
    exact le_iSup₂ (f := fun κ (_ : κ ∈ stripAddShift δ p) => quotHomNorm (T.f10 κ)) κ hκ
  · rw [ENNReal.ofReal_toReal h₂.ne]
    exact le_iSup₂ (f := fun κ (_ : κ ∈ stripSubShift δ p) => quotHomNorm (T.f01 κ)) κ hκ
  · rw [ENNReal.ofReal_toReal h₃.ne]
    exact le_iSup₂ (f := fun κ (_ : κ ∈ realDualPoints) => quotHomNorm (T.f11 κ)) κ hκ
  · rw [ENNReal.ofReal_add (add_nonneg (add_nonneg t₀ t₁) t₂) t₃,
      ENNReal.ofReal_add (add_nonneg t₀ t₁) t₂, ENNReal.ofReal_add t₀ t₁,
      ENNReal.ofReal_toReal h₀.ne, ENNReal.ofReal_toReal h₁.ne, ENNReal.ofReal_toReal h₂.ne,
      ENNReal.ofReal_toReal h₃.ne]
    rfl
theorem norm_trace_f11_le (six : YangMills.Construction.TraceBound.TraceSixFoldProductBound)
    [Fintype I.UnitQuot] [Nonempty I.UnitQuot] (hw : ∀ c, 0 < I.quotWeight 1 c) {δ : ℝ}
    {p : Fin 4 → ℂ} (hs : JetDomainSymmetries δ p) (A : (Fin 4 → ℂ) → QuotHom I I)
    {B₁ B₂ B₃ : JetQuad I I} {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ a₃ b₃ c₃ d₃ : ℝ}
    (k₁ : ComponentSup δ p B₁ a₁ b₁ c₁ d₁) (k₂ : ComponentSup δ p B₂ a₂ b₂ c₂ d₂)
    (k₃ : ComponentSup δ p B₃ a₃ b₃ c₃ d₃) {z : Fin 4 → ℂ} (hz : z ∈ realDualPoints) :
    ‖LinearMap.trace ℂ (I.UnitQuot → ℂ)
      ((mul p (⟨A, 0, 0, 0⟩ : JetQuad I I) (mul p B₁ (mul p (⟨A, 0, 0, 0⟩ : JetQuad I I)
        (mul p B₂ (mul p (⟨A, 0, 0, 0⟩ : JetQuad I I) B₃))))).f11 z)‖ ≤
      1 / 3 * (schattenCube (I.quotWeight 1) (A z) + schattenCube (I.quotWeight 1) (A z) +
          schattenCube (I.quotWeight 1) (A z)) * (d₁ * a₂ * a₃) +
        1 / 3 * (schattenCube (I.quotWeight 1) (A z) + schattenCube (I.quotWeight 1) (A z) +
          schattenCube (I.quotWeight 1) (A z)) * (a₁ * d₂ * a₃) +
        1 / 3 * (schattenCube (I.quotWeight 1) (A z) + schattenCube (I.quotWeight 1) (A z) +
          schattenCube (I.quotWeight 1) (A z)) * (a₁ * a₂ * d₃) +
        1 / 3 * (schattenCube (I.quotWeight 1) (A z) + schattenCube (I.quotWeight 1) (A z) +
          schattenCube (I.quotWeight 1) (A (z - p))) * (a₁ * b₂ * c₃) +
        1 / 3 * (schattenCube (I.quotWeight 1) (A z) + schattenCube (I.quotWeight 1) (A z) +
          schattenCube (I.quotWeight 1) (A (z + p))) * (a₁ * c₂ * b₃) +
        1 / 3 * (schattenCube (I.quotWeight 1) (A z) + schattenCube (I.quotWeight 1) (A (z - p)) +
          schattenCube (I.quotWeight 1) (A z)) * (b₁ * c₂ * a₃) +
        1 / 3 * (schattenCube (I.quotWeight 1) (A z) + schattenCube (I.quotWeight 1) (A (z - p)) +
          schattenCube (I.quotWeight 1) (A (z - p))) * (b₁ * a₂ * c₃) +
        1 / 3 * (schattenCube (I.quotWeight 1) (A z) + schattenCube (I.quotWeight 1) (A (z + p)) +
          schattenCube (I.quotWeight 1) (A z)) * (c₁ * b₂ * a₃) +
        1 / 3 * (schattenCube (I.quotWeight 1) (A z) + schattenCube (I.quotWeight 1) (A (z + p)) +
          schattenCube (I.quotWeight 1) (A (z + p))) * (c₁ * a₂ * b₃) := by
  obtain ⟨⟨⟨hz₀, hzP⟩, hzM⟩, hmP, hpM⟩ := hs.mem_real z hz
  have hp₀ := (hs.mem_addShift z hzP).2.1
  have hm₀ := (hs.mem_subShift z hzM).2.1
  have tb := fun (X₁ X₂ X₃ Y₁ Y₂ Y₃ : QuotHom I I) (n₁ n₂ n₃ : ℝ) (h₁ : 0 ≤ n₁) (h₂ : 0 ≤ n₂)
      (h₃ : 0 ≤ n₃) (g₁ : quotHomNorm Y₁ ≤ ENNReal.ofReal n₁)
      (g₂ : quotHomNorm Y₂ ≤ ENNReal.ofReal n₂) (g₃ : quotHomNorm Y₃ ≤ ENNReal.ofReal n₃) =>
    norm_trace_sixFold_le six hw X₁ X₂ X₃ Y₁ Y₂ Y₃ h₁ h₂ h₃ g₁ g₂ g₃
  rw [f11_mul_alternating]
  simp only [map_add]
  exact norm_sum_nine_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (tb (A z) (A z) (A z) (B₁.f11 z) (B₂.f00 z) (B₃.f00 z) _ _ _ k₁.nonneg_d k₂.nonneg_a
      k₃.nonneg_a (k₁.le_d z hz) (k₂.le_a z hz₀) (k₃.le_a z hz₀))
    (tb (A z) (A z) (A z) (B₁.f00 z) (B₂.f11 z) (B₃.f00 z) _ _ _ k₁.nonneg_a k₂.nonneg_d
      k₃.nonneg_a (k₁.le_a z hz₀) (k₂.le_d z hz) (k₃.le_a z hz₀))
    (tb (A z) (A z) (A z) (B₁.f00 z) (B₂.f00 z) (B₃.f11 z) _ _ _ k₁.nonneg_a k₂.nonneg_a
      k₃.nonneg_d (k₁.le_a z hz₀) (k₂.le_a z hz₀) (k₃.le_d z hz))
    (tb (A z) (A z) (A (z - p)) (B₁.f00 z) (B₂.f10 (z - p)) (B₃.f01 z) _ _ _ k₁.nonneg_a
      k₂.nonneg_b k₃.nonneg_c (k₁.le_a z hz₀) (k₂.le_b _ hmP) (k₃.le_c z hzM))
    (tb (A z) (A z) (A (z + p)) (B₁.f00 z) (B₂.f01 (z + p)) (B₃.f10 z) _ _ _ k₁.nonneg_a
      k₂.nonneg_c k₃.nonneg_b (k₁.le_a z hz₀) (k₂.le_c _ hpM) (k₃.le_b z hzP))
    (tb (A z) (A (z - p)) (A z) (B₁.f10 (z - p)) (B₂.f01 z) (B₃.f00 z) _ _ _ k₁.nonneg_b
      k₂.nonneg_c k₃.nonneg_a (k₁.le_b _ hmP) (k₂.le_c z hzM) (k₃.le_a z hz₀))
    (tb (A z) (A (z - p)) (A (z - p)) (B₁.f10 (z - p)) (B₂.f00 (z - p)) (B₃.f01 z) _ _ _
      k₁.nonneg_b k₂.nonneg_a k₃.nonneg_c (k₁.le_b _ hmP) (k₂.le_a _ hm₀) (k₃.le_c z hzM))
    (tb (A z) (A (z + p)) (A z) (B₁.f01 (z + p)) (B₂.f10 z) (B₃.f00 z) _ _ _ k₁.nonneg_c
      k₂.nonneg_b k₃.nonneg_a (k₁.le_c _ hpM) (k₂.le_b z hzP) (k₃.le_a z hz₀))
    (tb (A z) (A (z + p)) (A (z + p)) (B₁.f01 (z + p)) (B₂.f00 (z + p)) (B₃.f10 z) _ _ _
      k₁.nonneg_c k₂.nonneg_a k₃.nonneg_b (k₁.le_c _ hpM) (k₂.le_a _ hp₀) (k₃.le_b z hzP))
end Assembly
theorem sixJetTrace_bound (six : YangMills.Construction.TraceBound.TraceSixFoldProductBound)
    (facts : JetDomains.OpFunJetTheory) (args : JetArgumentsAndEqualJets) : SixJetTrace.Bound := by
  intro I hI _ hne δ p A γ hδ hp hA hγ hint B₁ B₂ B₃ j₁ j₂ j₃
  let _ := Fintype.ofFinite I.UnitQuot
  have _ := hne
  have hw := quotWeight_pos hI
  have hs := (args.1 δ p hδ hp).1
  have hf := facts.2.2 I I I hI hI hI δ p hδ hp
  obtain ⟨a₁, b₁, c₁, d₁, k₁⟩ := exists_componentSup (hf.sups_finite B₁ j₁)
  obtain ⟨a₂, b₂, c₂, d₂, k₂⟩ := exists_componentSup (hf.sups_finite B₂ j₂)
  obtain ⟨a₃, b₃, c₃, d₃, k₃⟩ := exists_componentSup (hf.sups_finite B₃ j₃)
  have G₀ : MeanLE γ fun κ => schattenCube (I.quotWeight 1) (A (toComplexVec κ)) := by
    have h := hint 0 (by simp)
    simp only [add_zero] at h
    exact h
  have Gp : MeanLE γ fun κ => schattenCube (I.quotWeight 1) (A (toComplexVec κ + p)) :=
    hint p (by simp)
  have Gm : MeanLE γ fun κ => schattenCube (I.quotWeight 1) (A (toComplexVec κ - p)) := by
    have h := hint (-p) (by simp)
    simp only [← sub_eq_add_neg] at h
    exact h
  have n₁ := mul_nonneg (mul_nonneg k₁.nonneg_d k₂.nonneg_a) k₃.nonneg_a
  have n₂ := mul_nonneg (mul_nonneg k₁.nonneg_a k₂.nonneg_d) k₃.nonneg_a
  have n₃ := mul_nonneg (mul_nonneg k₁.nonneg_a k₂.nonneg_a) k₃.nonneg_d
  have n₄ := mul_nonneg (mul_nonneg k₁.nonneg_a k₂.nonneg_b) k₃.nonneg_c
  have n₅ := mul_nonneg (mul_nonneg k₁.nonneg_a k₂.nonneg_c) k₃.nonneg_b
  have n₆ := mul_nonneg (mul_nonneg k₁.nonneg_b k₂.nonneg_c) k₃.nonneg_a
  have n₇ := mul_nonneg (mul_nonneg k₁.nonneg_b k₂.nonneg_a) k₃.nonneg_c
  have n₈ := mul_nonneg (mul_nonneg k₁.nonneg_c k₂.nonneg_b) k₃.nonneg_a
  have n₉ := mul_nonneg (mul_nonneg k₁.nonneg_c k₂.nonneg_a) k₃.nonneg_b
  have H := (((((((((G₀.third_mul G₀ G₀ n₁).add (G₀.third_mul G₀ G₀ n₂)).add
    (G₀.third_mul G₀ G₀ n₃)).add (G₀.third_mul G₀ Gm n₄)).add (G₀.third_mul G₀ Gp n₅)).add
    (G₀.third_mul Gm G₀ n₆)).add (G₀.third_mul Gm Gm n₇)).add (G₀.third_mul Gp G₀ n₈)).add
    (G₀.third_mul Gp Gp n₉))
  have hb := norm_torusAverage_le
    (g := fun κ => LinearMap.trace ℂ (I.UnitQuot → ℂ)
      ((mul p (⟨A, 0, 0, 0⟩ : JetQuad I I) (mul p B₁ (mul p (⟨A, 0, 0, 0⟩ : JetQuad I I)
        (mul p B₂ (mul p (⟨A, 0, 0, 0⟩ : JetQuad I I) B₃))))).f11 (toComplexVec κ))) H
    (fun κ => norm_trace_f11_le six hw hs A k₁ k₂ k₃ (z := toComplexVec κ)
      (fun j => Complex.ofReal_im _))
  have hnine := nine_products_le_prod_sums k₁.nonneg_a k₁.nonneg_b k₁.nonneg_c k₁.nonneg_d
    k₂.nonneg_a k₂.nonneg_b k₂.nonneg_c k₂.nonneg_d k₃.nonneg_a k₃.nonneg_b k₃.nonneg_c
    k₃.nonneg_d
  have hP₁ := add_nonneg (add_nonneg (add_nonneg k₁.nonneg_a k₁.nonneg_b) k₁.nonneg_c) k₁.nonneg_d
  have hP₂ := add_nonneg (add_nonneg (add_nonneg k₂.nonneg_a k₂.nonneg_b) k₂.nonneg_c) k₂.nonneg_d
  rw [k₁.jetNorm_eq, k₂.jetNorm_eq, k₃.jetNorm_eq, ← ENNReal.ofReal_mul hγ,
    ← ENNReal.ofReal_mul (mul_nonneg hγ hP₁),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hγ hP₁) hP₂)]
  refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
  have := mul_le_mul_of_nonneg_left hnine hγ
  linarith
end YangMills.Construction.PeriodicOperators.SixJetTraceProof
end
