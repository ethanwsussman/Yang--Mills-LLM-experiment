import YangMills.Construction.LawByMomentsOfTheFlow.CopiesGivenAField
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction
namespace MomentMethod
variable {Ω : Type} {G : MeasurableSpace Ω} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
private theorem integral_sq_sub_condExp_le [IsProbabilityMeasure μ] (hm : G ≤ m₀)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    ∫ x, (Y x - (μ[Y | G]) x) ^ 2 ∂μ ≤ ∫ x, Y x ^ 2 ∂μ := by
  have h1 : ∫ x, (ProbabilityTheory.condVar G Y μ) x ∂μ = ∫ x, ((Y - μ[Y | G]) ^ 2) x ∂μ :=
    integral_condExp hm
  have h2 : ∫ x, (μ[Y ^ 2 | G]) x ∂μ = ∫ x, (Y ^ 2) x ∂μ := integral_condExp hm
  have h3 : ∫ x, (ProbabilityTheory.condVar G Y μ) x ∂μ ≤ ∫ x, (μ[Y ^ 2 | G]) x ∂μ :=
    integral_mono_ae ProbabilityTheory.integrable_condVar integrable_condExp
      (ProbabilityTheory.condVar_ae_le_condExp_sq hm hY)
  simpa [h1, h2] using h3
private theorem condExp_comp_of_measurePreserving_inverse [IsProbabilityMeasure μ] (hm : G ≤ m₀)
    {τ τ' : Ω → Ω}
    (hτ : MeasurePreserving τ μ μ) (hτ' : MeasurePreserving τ' μ μ) (h1 : ∀ x, τ' (τ x) = x)
    (h2 : ∀ x, τ (τ' x) = x) (hG : @Measurable _ _ G G τ) (hG' : @Measurable _ _ G G τ')
    {Y : Ω → ℝ} (hY : Integrable Y μ) :
    (fun x => (μ[Y | G]) (τ x)) =ᵐ[μ] μ[Y ∘ τ | G] := by
  let e : Ω ≃ᵐ Ω :=
    { toFun := τ, invFun := τ', left_inv := h1, right_inv := h2,
      measurable_toFun := hτ.measurable, measurable_invFun := hτ'.measurable }
  have he : MeasurableEmbedding τ := e.measurableEmbedding
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (hτ.integrable_comp_of_integrable hY) ?_ ?_ ?_
  · intro s _ _
    exact (hτ.integrable_comp_of_integrable (integrable_condExp (m := G) (f := Y))).integrableOn
  · intro s hs _
    have hS : MeasurableSet[G] (τ' ⁻¹' s) := hG' hs
    have hpre : τ ⁻¹' (τ' ⁻¹' s) = s := by
      ext x
      simp [h1]
    calc ∫ x in s, (μ[Y | G]) (τ x) ∂μ = ∫ y in τ' ⁻¹' s, (μ[Y | G]) y ∂μ := by
          conv_lhs => rw [← hpre]
          exact hτ.setIntegral_preimage_emb he _ _
      _ = ∫ y in τ' ⁻¹' s, Y y ∂μ := setIntegral_condExp hm hY hS
      _ = ∫ x in s, (Y ∘ τ) x ∂μ := by
          conv_rhs => rw [← hpre]
          exact (hτ.setIntegral_preimage_emb he _ _).symm
  · exact ((stronglyMeasurable_condExp (m := G) (f := Y) (μ := μ)).comp_measurable hG).aestronglyMeasurable
private theorem integral_abs_mul_le_of_integral_sq_le {f g : Ω → ℝ} {p q : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (h1 : ∫ x, f x ^ 2 ∂μ ≤ p ^ 2) (h2 : ∫ x, g x ^ 2 ∂μ ≤ q ^ 2) :
    ∫ x, |f x * g x| ∂μ ≤ p * q := by
  have hs := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  have e1 : ∀ h : Ω → ℝ, (∫ a, ‖h a‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ a, h a ^ 2 ∂μ) := by
    intro h
    rw [Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [e1 f, e1 g] at hs
  have hl : ∫ x, |f x * g x| ∂μ = ∫ a, ‖f a‖ * ‖g a‖ ∂μ :=
    integral_congr_ae (Eventually.of_forall fun a => by simp [abs_mul])
  rw [hl]
  refine hs.trans (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) hp)
  · exact (Real.sqrt_le_sqrt h1).trans (Real.sqrt_sq hp).le
  · exact (Real.sqrt_le_sqrt h2).trans (Real.sqrt_sq hq).le
private theorem integrable_bounded_mul {W f : Ω → ℝ} {D : ℝ} (hW : AEStronglyMeasurable W μ)
    (hb : ∀ x, |W x| ≤ D) (hf : Integrable f μ) : Integrable (fun x => W x * f x) μ := by
  refine Integrable.mono' (hf.abs.const_mul D) (hW.mul hf.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)
private theorem abs_integral_bounded_mul_le {W f : Ω → ℝ} {D : ℝ} (hb : ∀ x, |W x| ≤ D)
    (hf : Integrable f μ) :
    |∫ x, W x * f x ∂μ| ≤ D * ∫ x, |f x| ∂μ := by
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) (hf.abs.const_mul D)
    (Eventually.of_forall fun x => ?_)
  simp only [abs_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)
private theorem integral_mul_eq_integral_mul_condExp [IsProbabilityMeasure μ] (hm : G ≤ m₀)
    {H Y : Ω → ℝ} (hH : StronglyMeasurable[G] H) (hHY : Integrable (fun x => H x * Y x) μ)
    (hY : Integrable Y μ) :
    ∫ x, H x * Y x ∂μ = ∫ x, H x * (μ[Y | G]) x ∂μ := by
  have hp : μ[H * Y | G] =ᵐ[μ] H * μ[Y | G] := condExp_mul_of_stronglyMeasurable_left hH hHY hY
  calc ∫ x, H x * Y x ∂μ = ∫ x, (H * Y) x ∂μ := rfl
    _ = ∫ x, (μ[H * Y | G]) x ∂μ := (integral_condExp hm).symm
    _ = ∫ x, H x * (μ[Y | G]) x ∂μ := integral_congr_ae hp
private theorem abs_integral_weighted_centred_copy_le [IsProbabilityMeasure μ] {τ τ' : Ω → Ω}
    (hm : G ≤ m₀)
    (hτ : MeasurePreserving τ μ μ) (hτ' : MeasurePreserving τ' μ μ) (h1 : ∀ x, τ' (τ x) = x)
    (h2 : ∀ x, τ (τ' x) = x) (hG : @Measurable _ _ G G τ) (hG' : @Measurable _ _ G G τ')
    {R R' X Xb : Ω → ℝ} {C δ A e : ℝ} (hR : StronglyMeasurable[G] R) (hR' : StronglyMeasurable[G] R')
    (hRC : ∀ x, |R x| ≤ C) (hRC' : ∀ x, |R' x| ≤ C) (hX : MemLp X 2 μ) (hXb : MemLp Xb 2 μ)
    (hA : 0 ≤ A) (he : 0 ≤ e) (hX2 : ∫ x, X x ^ 2 ∂μ ≤ A ^ 2) (hXb2 : ∫ x, Xb x ^ 2 ∂μ ≤ A ^ 2)
    (hXe : ∫ x, (X x - Xb x) ^ 2 ∂μ ≤ e ^ 2)
    (hcov : ∀ᵐ x ∂μ, |(μ[fun z => Xb z * Xb (τ z) | G]) x - (μ[Xb | G]) x * (μ[Xb ∘ τ | G]) x| ≤ δ) :
    |∫ x, R x * R' x * ((X x - (μ[X | G]) x) * (X (τ x) - (μ[X | G]) (τ x))) ∂μ| ≤
      C ^ 2 * (δ + 8 * A * e) := by
  have hemb : MeasurableEmbedding τ :=
    (({ toFun := τ, invFun := τ', left_inv := h1, right_inv := h2,
        measurable_toFun := hτ.measurable, measurable_invFun := hτ'.measurable } : Ω ≃ᵐ Ω)).measurableEmbedding
  obtain ⟨a, ha⟩ : ∃ a, a = μ[X | G] := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = μ[Xb | G] := ⟨_, rfl⟩
  obtain ⟨bt, hbt⟩ : ∃ bt, bt = μ[Xb ∘ τ | G] := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = μ[fun z => Xb z * Xb (τ z) | G] := ⟨_, rfl⟩
  rw [← ha]
  rw [← hb, ← hbt, ← hc] at hcov
  obtain ⟨W, hWdef⟩ : ∃ W : Ω → ℝ, W = fun x => R x * R' x := ⟨_, rfl⟩
  have hWs : StronglyMeasurable[G] W := by
    rw [hWdef]
    exact hR.mul hR'
  have hWa : AEStronglyMeasurable W μ := (hWs.mono hm).aestronglyMeasurable
  have hWb : ∀ x, |W x| ≤ C ^ 2 := by
    intro x
    rw [hWdef, sq]
    simp only [abs_mul]
    exact mul_le_mul (hRC x) (hRC' x) (abs_nonneg _) ((abs_nonneg _).trans (hRC x))
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have haL : MemLp a 2 μ := ha ▸ hX.condExp one_le_two
  have hbL : MemLp b 2 μ := hb ▸ hXb.condExp one_le_two
  have hXt : MemLp (Xb ∘ τ) 2 μ := hXb.comp_measurePreserving hτ
  have hbtL : MemLp bt 2 μ := hbt ▸ hXt.condExp one_le_two
  have hbs : StronglyMeasurable[G] b := hb ▸ stronglyMeasurable_condExp
  have hbts : StronglyMeasurable[G] bt := hbt ▸ stronglyMeasurable_condExp
  have hW2 : ∀ u : Ω → ℝ, MemLp u 2 μ → MemLp (fun x => W x * u x) 2 μ := by
    intro u hu
    refine MemLp.of_le_mul (c := C ^ 2) hu (hWa.mul hu.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hWb x) (abs_nonneg _)
  obtain ⟨De, hDe⟩ : ∃ De : Ω → ℝ, De = fun x => X x - a x := ⟨_, rfl⟩
  obtain ⟨Db, hDb⟩ : ∃ Db : Ω → ℝ, Db = fun x => Xb x - b x := ⟨_, rfl⟩
  obtain ⟨Dd, hDd⟩ : ∃ Dd : Ω → ℝ, Dd = fun x => De x - Db x := ⟨_, rfl⟩
  have hDeL : MemLp De 2 μ := by
    rw [hDe]
    exact hX.sub haL
  have hDbL : MemLp Db 2 μ := by
    rw [hDb]
    exact hXb.sub hbL
  have hDdL : MemLp Dd 2 μ := by
    rw [hDd]
    exact hDeL.sub hDbL
  have hDe2 : ∫ x, De x ^ 2 ∂μ ≤ A ^ 2 := by
    rw [hDe, ha]
    exact (integral_sq_sub_condExp_le hm hX).trans hX2
  have hDb2 : ∫ x, Db x ^ 2 ∂μ ≤ A ^ 2 := by
    rw [hDb, hb]
    exact (integral_sq_sub_condExp_le hm hXb).trans hXb2
  have hDd2 : ∫ x, Dd x ^ 2 ∂μ ≤ e ^ 2 := by
    have hsub : μ[X - Xb | G] =ᵐ[μ] μ[X | G] - μ[Xb | G] :=
      condExp_sub (hX.integrable one_le_two) (hXb.integrable one_le_two) G
    have hcg : ∫ x, Dd x ^ 2 ∂μ = ∫ x, ((X - Xb) x - (μ[X - Xb | G]) x) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hsub] with x hx
      simp only [hDd, hDe, hDb, ha, hb, hx, Pi.sub_apply]
      ring
    rw [hcg]
    exact (integral_sq_sub_condExp_le hm (hX.sub hXb)).trans hXe
  have hcopy : ∀ f : Ω → ℝ, ∫ x, f (τ x) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ := fun f =>
    hτ.integral_comp hemb (fun y => f y ^ 2)
  have hDeτ : MemLp (De ∘ τ) 2 μ := hDeL.comp_measurePreserving hτ
  have hDbτ : MemLp (Db ∘ τ) 2 μ := hDbL.comp_measurePreserving hτ
  have hDdτ : MemLp (Dd ∘ τ) 2 μ := hDdL.comp_measurePreserving hτ
  have hf0 : Integrable (fun x => Db x * (Db ∘ τ) x) μ := hDbL.integrable_mul hDbτ
  have hf1 : Integrable (fun x => Dd x * (De ∘ τ) x) μ := hDdL.integrable_mul hDeτ
  have hf2 : Integrable (fun x => Db x * (Dd ∘ τ) x) μ := hDbL.integrable_mul hDdτ
  have hsplit : ∫ x, R x * R' x * ((X x - a x) * (X (τ x) - a (τ x))) ∂μ =
      ∫ x, W x * (Db x * (Db ∘ τ) x) ∂μ + ∫ x, W x * (Dd x * (De ∘ τ) x) ∂μ
        + ∫ x, W x * (Db x * (Dd ∘ τ) x) ∂μ := by
    have j0 := integrable_bounded_mul hWa hWb hf0
    have j1 := integrable_bounded_mul hWa hWb hf1
    have j2 := integrable_bounded_mul hWa hWb hf2
    have j01 : Integrable (fun x => W x * (Db x * (Db ∘ τ) x) + W x * (Dd x * (De ∘ τ) x)) μ :=
      j0.add j1
    rw [← integral_add j0 j1, ← integral_add j01 j2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hDd, hDe, hDb, hWdef, Function.comp_apply]
    ring
  have hT1 : |∫ x, W x * (Dd x * (De ∘ τ) x) ∂μ| ≤ C ^ 2 * (e * A) :=
    (abs_integral_bounded_mul_le hWb hf1).trans (mul_le_mul_of_nonneg_left
      (integral_abs_mul_le_of_integral_sq_le hDdL hDeτ he hA hDd2 (by
        simpa only [Function.comp_apply, hcopy De] using hDe2)) hC2)
  have hT2 : |∫ x, W x * (Db x * (Dd ∘ τ) x) ∂μ| ≤ C ^ 2 * (A * e) :=
    (abs_integral_bounded_mul_le hWb hf2).trans (mul_le_mul_of_nonneg_left
      (integral_abs_mul_le_of_integral_sq_le hDbL hDdτ hA he hDb2 (by
        simpa only [Function.comp_apply, hcopy Dd] using hDd2)) hC2)
  have hmove : (fun x => b (τ x)) =ᵐ[μ] bt := by
    rw [hb, hbt]
    exact condExp_comp_of_measurePreserving_inverse hm hτ hτ' h1 h2 hG hG' (hXb.integrable one_le_two)
  have hXX : Integrable (fun x => Xb x * Xb (τ x)) μ := hXb.integrable_mul hXt
  have hc1 : Integrable c μ := hc ▸ integrable_condExp
  have p1 : ∫ x, W x * (Xb x * Xb (τ x)) ∂μ = ∫ x, W x * c x ∂μ := by
    rw [hc]
    exact integral_mul_eq_integral_mul_condExp hm hWs (integrable_bounded_mul hWa hWb hXX) hXX
  have i2 : Integrable (fun x => (W x * b x) * (Xb ∘ τ) x) μ := (hW2 b hbL).integrable_mul hXt
  have p2 : ∫ x, (W x * b x) * (Xb ∘ τ) x ∂μ = ∫ x, (W x * b x) * bt x ∂μ := by
    rw [hbt]
    exact integral_mul_eq_integral_mul_condExp hm (hWs.mul hbs) i2 (hXt.integrable one_le_two)
  have i3 : Integrable (fun x => (W x * bt x) * Xb x) μ := (hW2 bt hbtL).integrable_mul hXb
  have p3 : ∫ x, (W x * bt x) * Xb x ∂μ = ∫ x, (W x * bt x) * b x ∂μ := by
    rw [hb]
    exact integral_mul_eq_integral_mul_condExp hm (hWs.mul hbts) i3 (hXb.integrable one_le_two)
  have i1 : Integrable (fun x => W x * (Xb x * Xb (τ x))) μ := integrable_bounded_mul hWa hWb hXX
  have i4 : Integrable (fun x => (W x * b x) * bt x) μ := (hW2 b hbL).integrable_mul hbtL
  have i5 : Integrable (fun x => W x * c x) μ := integrable_bounded_mul hWa hWb hc1
  have hT0 : ∫ x, W x * (Db x * (Db ∘ τ) x) ∂μ = ∫ x, W x * (c x - b x * bt x) ∂μ := by
    have hfour : ∫ x, W x * (Db x * (Db ∘ τ) x) ∂μ =
        ∫ x, ((W x * (Xb x * Xb (τ x)) - (W x * b x) * (Xb ∘ τ) x) - (W x * bt x) * Xb x
          + (W x * b x) * bt x) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hmove] with x hx
      simp only [hDb, Function.comp_apply, hx]
      ring
    have hlast : ∫ x, W x * (c x - b x * bt x) ∂μ = ∫ x, W x * c x ∂μ - ∫ x, (W x * b x) * bt x ∂μ := by
      rw [← integral_sub i5 i4]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    have hsw : ∫ x, (W x * bt x) * b x ∂μ = ∫ x, (W x * b x) * bt x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    have j12 : Integrable (fun x => W x * (Xb x * Xb (τ x)) - (W x * b x) * (Xb ∘ τ) x) μ := i1.sub i2
    have j123 : Integrable (fun x => W x * (Xb x * Xb (τ x)) - (W x * b x) * (Xb ∘ τ) x
        - (W x * bt x) * Xb x) μ := j12.sub i3
    rw [hfour, integral_add j123 i4, integral_sub j12 i3, integral_sub i1 i2, p1, p2, p3, hsw, hlast]
    ring
  have hB0 : |∫ x, W x * (c x - b x * bt x) ∂μ| ≤ C ^ 2 * δ := by
    have hn := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => W x * (c x - b x * bt x))
      (C := C ^ 2 * δ) (by
        filter_upwards [hcov] with x hx
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hWb x) hx (abs_nonneg _) hC2)
    simpa using hn
  rw [hsplit, hT0]
  have hAe : 0 ≤ A * e := mul_nonneg hA he
  have htri := abs_add_three (∫ x, W x * (c x - b x * bt x) ∂μ) (∫ x, W x * (Dd x * (De ∘ τ) x) ∂μ)
    (∫ x, W x * (Db x * (Dd ∘ τ) x) ∂μ)
  have hfin : C ^ 2 * δ + C ^ 2 * (e * A) + C ^ 2 * (A * e) ≤ C ^ 2 * (δ + 8 * A * e) := by
    nlinarith [mul_nonneg hC2 hAe]
  linarith
theorem conditionalCopyCovariance : conditionalCopyCovarianceStatement := by
  intro Ω m₀ μ _ G τ τ' hm hτ hτ' h1 h2 hG hG' R R' X Xb C δ A e hR hR' hRC hRC' hX hXb _ _ hA he
    hX2 hXb2 hXe hcov
  exact abs_integral_weighted_centred_copy_le (G := G) (m₀ := m₀) hm hτ hτ' h1 h2 hG hG' hR hR' hRC hRC'
    hX hXb hA he hX2 hXb2 hXe hcov
end MomentMethod
end YangMills.Construction
end
