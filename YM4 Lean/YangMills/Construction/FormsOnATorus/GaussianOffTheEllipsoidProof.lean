import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawOnABoxOfTheFlow.GaussianOffTheEllipsoid
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped Quaternion ENNReal
namespace YangMills.Construction.BoxGaussian
open TorusFields ResponseInTheExpansion BlockAverages
private theorem exp_neg_mul_sq_le_one_add_rpow (c : ℝ) (hc : 0 < c) (N : ℕ) (hN : 0 < N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → Real.exp (-(c * t ^ 2)) ≤ K * (1 + t) ^ (-(2 * (N : ℝ))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set e : ℝ := min 1 (c / N) with he
  have he1 : e ≤ 1 := min_le_left _ _
  have he2 : e ≤ c / N := min_le_right _ _
  refine ⟨(2 / e) ^ N, by positivity, fun t ht => ?_⟩
  have h1t : 0 < 1 + t := by linarith
  have hA : e / 2 * (1 + t) ^ 2 ≤ 1 + c / N * t ^ 2 := by
    have : e * (1 + t ^ 2) ≤ 1 + c / N * t ^ 2 := by
      have h3 : e * t ^ 2 ≤ c / N * t ^ 2 := mul_le_mul_of_nonneg_right he2 (by positivity)
      nlinarith
    have h4 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (1 - t)]
    have h5 : e / 2 * (1 + t) ^ 2 ≤ e / 2 * (2 * (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith
  have hB : 1 + c / N * t ^ 2 ≤ Real.exp (c / N * t ^ 2) := by
    have := Real.add_one_le_exp (c / N * t ^ 2)
    linarith
  have hC : (e / 2 * (1 + t) ^ 2) ^ N ≤ Real.exp (c * t ^ 2) := by
    have h6 : (e / 2 * (1 + t) ^ 2) ^ N ≤ (Real.exp (c / N * t ^ 2)) ^ N :=
      pow_le_pow_left₀ (by positivity) (hA.trans hB) N
    have h7 : (Real.exp (c / N * t ^ 2)) ^ N = Real.exp (c * t ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    rwa [h7] at h6
  have hD : (1 + t) ^ (-(2 * (N : ℝ))) = (((1 + t) ^ 2) ^ N)⁻¹ := by
    rw [Real.rpow_neg h1t.le, ← pow_mul]
    congr 1
    have : (2 * (N : ℝ)) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  rw [hD, Real.exp_neg]
  have hpos : 0 < (e / 2 * (1 + t) ^ 2) ^ N := by positivity
  calc (Real.exp (c * t ^ 2))⁻¹ ≤ ((e / 2 * (1 + t) ^ 2) ^ N)⁻¹ := inv_anti₀ hpos hC
    _ = (2 / e) ^ N * (((1 + t) ^ 2) ^ N)⁻¹ := by
      rw [mul_pow, mul_inv, ← inv_pow (e / 2), inv_div]
section GaussianTails
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
private theorem integrable_exp_neg_of_coercive (μ : Measure E) [μ.IsAddHaarMeasure] (q : E → ℝ)
    (hq : Continuous q) (c : ℝ) (hc : 0 < c) (hcq : ∀ z, c * ‖z‖ ^ 2 ≤ q z) :
    Integrable (fun z => Real.exp (-q z)) μ := by
  obtain ⟨K, _, hb⟩ := exp_neg_mul_sq_le_one_add_rpow c hc (finrank ℝ E + 1) (Nat.succ_pos _)
  have hi : Integrable (fun z : E => (1 + ‖z‖) ^ (-(2 * ((finrank ℝ E + 1 : ℕ) : ℝ)))) μ := by
    refine integrable_one_add_norm ?_
    push_cast
    have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    linarith
  refine (hi.const_mul K).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-q z) ≤ Real.exp (-(c * ‖z‖ ^ 2)) := Real.exp_le_exp.2 (by linarith [hcq z])
    _ ≤ _ := hb _ (norm_nonneg _)
omit [MeasurableSpace E] [BorelSpace E] in
private theorem exists_bilin_representative (q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
    (hcq : ∀ z, c * ‖z‖ ^ 2 ≤ q z z) (l : E →ₗ[ℝ] ℝ) : ∃ z₀, ∀ η, q z₀ η = l η := by
  have hinj : Function.Injective q := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have h := hcq z
    rw [hz] at h
    simp only [LinearMap.zero_apply] at h
    have h0 : ‖z‖ ^ 2 ≤ 0 := by
      by_contra hne
      have : 0 < c * ‖z‖ ^ 2 := mul_pos hc (not_le.1 hne)
      linarith
    have : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
    exact norm_eq_zero.1 this
  have hsurj : Function.Surjective q :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm).1 hinj
  obtain ⟨z₀, h⟩ := hsurj l
  exact ⟨z₀, fun η => by rw [h]⟩
private theorem gaussian_tail_core (μ : Measure E) [μ.IsAddHaarMeasure]
    (q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsym : ∀ u v, q u v = q v u) (c : ℝ) (hc : 0 < c)
    (hcq : ∀ z, c * ‖z‖ ^ 2 ≤ q z z) (l : E →ₗ[ℝ] ℝ) (c₀ x cc : ℝ) (hx : 0 < x) (h2 : 2 * c₀ ≤ cc)
    (F : E → ℝ) (hFdef : ∀ z, F z = q z z + 2 * l z + c₀) :
    Integrable (fun z => Real.exp (-(x / 2) * F z)) μ ∧ 0 < ∫ z, Real.exp (-(x / 2) * F z) ∂μ ∧
    ∫ z, Set.indicator {z | cc < F z} (fun z => Real.exp (-(x / 2) * F z)) z ∂μ ≤
      (Real.sqrt 2) ^ finrank ℝ E * Real.exp (-(x * cc / 8)) * ∫ z, Real.exp (-(x / 2) * F z) ∂μ := by
  obtain ⟨z₀, hz₀⟩ := exists_bilin_representative q c hc hcq l
  set P : E → ℝ := fun u => q u u with hP
  have hPc : Continuous P := by
    have : P = fun u => q.toContinuousBilinearMap u u := rfl
    rw [this]
    fun_prop
  set m : ℝ := c₀ - q z₀ z₀ with hm
  have hF : ∀ z, F z = P (z + z₀) + m := by
    intro z
    have h1 : q z z₀ = l z := by rw [hsym, hz₀]
    have h2' : q z₀ z = l z := hz₀ z
    simp only [hFdef, hP, hm, map_add, LinearMap.add_apply, h1, h2']
    ring
  have hPpos : ∀ u, 0 ≤ P u := fun u => le_trans (by positivity) (hcq u)
  have hmle : m ≤ cc / 2 := by
    have := hPpos z₀
    simp only [hP] at this
    linarith
  have hFc : Continuous F := by
    have : F = fun z => P (z + z₀) + m := funext hF
    rw [this]
    fun_prop
  have hG : ∀ y : ℝ, 0 < y → Integrable (fun u => Real.exp (-(y * P u))) μ := fun y hy =>
    integrable_exp_neg_of_coercive μ (fun u => y * P u) (by fun_prop) (y * c) (mul_pos hy hc)
      (fun z => by
        have := mul_le_mul_of_nonneg_left (hcq z) hy.le
        simpa [hP, mul_assoc] using this)
  have hsplit : ∀ z, Real.exp (-(x / 2) * F z) =
      Real.exp (-(x / 2) * m) * Real.exp (-((x / 2) * P (z + z₀))) := by
    intro z
    rw [← Real.exp_add, hF]
    congr 1
    ring
  have hx2 : 0 < x / 2 := by positivity
  have hx4 : 0 < x / 4 := by positivity
  have hint : Integrable (fun z => Real.exp (-(x / 2) * F z)) μ := by
    simp only [hsplit]
    exact ((hG _ hx2).comp_add_right z₀).const_mul _
  have hZ : ∫ z, Real.exp (-(x / 2) * F z) ∂μ =
      Real.exp (-(x / 2) * m) * ∫ u, Real.exp (-((x / 2) * P u)) ∂μ := by
    simp only [hsplit]
    rw [integral_const_mul, integral_add_right_eq_self (fun u => Real.exp (-((x / 2) * P u))) z₀]
  have hZ0 : 0 < ∫ u, Real.exp (-((x / 2) * P u)) ∂μ := integral_exp_pos (hG _ hx2)
  have hscale : ∫ u, Real.exp (-((x / 4) * P u)) ∂μ =
      (Real.sqrt 2) ^ finrank ℝ E * ∫ u, Real.exp (-((x / 2) * P u)) ∂μ := by
    have h := Measure.integral_comp_smul μ (fun u => Real.exp (-((x / 2) * P u))) (Real.sqrt 2)⁻¹
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 < Real.sqrt 2 := by positivity
    have e1 : ∀ u, Real.exp (-((x / 2) * P ((Real.sqrt 2)⁻¹ • u))) = Real.exp (-((x / 4) * P u)) := by
      intro u
      congr 2
      simp only [hP, map_smul, LinearMap.smul_apply, smul_eq_mul]
      have : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
        rw [← mul_inv, ← sq, hs]
        norm_num
      calc x / 2 * ((Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * q u u))
          = x / 2 * (((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * q u u) := by ring
        _ = x / 4 * q u u := by rw [this]; ring
    simp only [e1] at h
    rw [h, smul_eq_mul, inv_pow, inv_inv, abs_of_pos (by positivity)]
  have hind : Integrable (Set.indicator {z | cc < F z} (fun z => Real.exp (-(x / 2) * F z))) μ :=
    hint.indicator (isOpen_lt continuous_const hFc).measurableSet
  have hb : Integrable (fun z => Real.exp (-(x / 2) * m) * Real.exp (-(x * cc / 8)) *
      Real.exp (-((x / 4) * P (z + z₀)))) μ := ((hG _ hx4).comp_add_right z₀).const_mul _
  have hpt : ∀ z, Set.indicator {z | cc < F z} (fun z => Real.exp (-(x / 2) * F z)) z ≤
      Real.exp (-(x / 2) * m) * Real.exp (-(x * cc / 8)) * Real.exp (-((x / 4) * P (z + z₀))) := by
    intro z
    by_cases hz : cc < F z
    · rw [Set.indicator_of_mem (show z ∈ {z | cc < F z} from hz), hsplit, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hPz : cc / 2 ≤ P (z + z₀) := by
        have := hF z
        linarith
      nlinarith
    · rw [Set.indicator_of_notMem (show z ∉ {z | cc < F z} from hz)]
      positivity
  refine ⟨hint, ?_, ?_⟩
  · rw [hZ]
    exact mul_pos (Real.exp_pos _) hZ0
  · calc ∫ z, Set.indicator {z | cc < F z} (fun z => Real.exp (-(x / 2) * F z)) z ∂μ
        ≤ ∫ z, Real.exp (-(x / 2) * m) * Real.exp (-(x * cc / 8)) * Real.exp (-((x / 4) * P (z + z₀))) ∂μ :=
          integral_mono hind hb hpt
      _ = Real.exp (-(x / 2) * m) * Real.exp (-(x * cc / 8)) * ∫ u, Real.exp (-((x / 4) * P u)) ∂μ := by
          rw [integral_const_mul, integral_add_right_eq_self (fun u => Real.exp (-((x / 4) * P u))) z₀]
      _ = _ := by
          rw [hscale, hZ]
          ring
end GaussianTails
section Restriction
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
private theorem gaussian_tail_on_subspace (𝒮 : Submodule ℝ V) (Qb : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsym : ∀ u v, Qb u v = Qb v u)
    (c : ℝ) (hc : 0 < c) (hcq : ∀ z ∈ 𝒮, c * ‖z‖ ^ 2 ≤ Qb z z) (A : V) (x cc : ℝ) (hx : 0 < x)
    (h2 : 2 * Qb A A ≤ cc) :
    IsProbabilityMeasure (BoxGaussian.normalize (((Measure.addHaar : Measure 𝒮).map Subtype.val).withDensity
      fun ζ => ENNReal.ofReal (Real.exp (-(x / 2) * Qb (A + ζ) (A + ζ))))) ∧
    (BoxGaussian.normalize (((Measure.addHaar : Measure 𝒮).map Subtype.val).withDensity
      fun ζ => ENNReal.ofReal (Real.exp (-(x / 2) * Qb (A + ζ) (A + ζ))))).real
        {ζ : V | ζ ∈ 𝒮 ∧ Qb (A + ζ) (A + ζ) ≤ cc}ᶜ ≤
      Real.sqrt 2 ^ finrank ℝ 𝒮 * Real.exp (-(x * cc / 8)) := by
  set μ : Measure 𝒮 := Measure.addHaar with hμ
  set f : V → ℝ≥0∞ := fun ζ => ENNReal.ofReal (Real.exp (-(x / 2) * Qb (A + ζ) (A + ζ))) with hf
  set ν := (μ.map Subtype.val).withDensity f with hν
  have hQc : Continuous fun ζ : V => Qb (A + ζ) (A + ζ) := by
    have : (fun ζ : V => Qb (A + ζ) (A + ζ)) =
        fun ζ => Qb.toContinuousBilinearMap (A + ζ) (A + ζ) := rfl
    rw [this]
    fun_prop
  have hfm : Measurable f :=
    ((Real.continuous_exp.comp (continuous_const.mul hQc)).measurable).ennreal_ofReal
  have hvm : Measurable (Subtype.val : 𝒮 → V) := measurable_subtype_coe
  let q : 𝒮 →ₗ[ℝ] 𝒮 →ₗ[ℝ] ℝ := Qb.domRestrict₁₂ 𝒮 𝒮
  let l : 𝒮 →ₗ[ℝ] ℝ := (Qb A).domRestrict 𝒮
  let F : 𝒮 → ℝ := fun z => Qb (A + z) (A + z)
  have hFdef : ∀ z : 𝒮, F z = q z z + 2 * l z + Qb A A := by
    intro z
    simp only [F, q, l, map_add, LinearMap.add_apply, LinearMap.domRestrict₁₂_apply,
      LinearMap.domRestrict_apply]
    rw [hsym z.1 A]
    ring
  obtain ⟨hint, hpos, hoff⟩ := gaussian_tail_core μ q (fun u v => hsym u.1 v.1) c hc
    (fun z => hcq z.1 z.2) l (Qb A A) x cc hx h2 F hFdef
  have hνapply : ∀ T : Set V, MeasurableSet T →
      ν T = ∫⁻ z in Subtype.val ⁻¹' T, ENNReal.ofReal (Real.exp (-(x / 2) * F z)) ∂μ := by
    intro T hT
    rw [hν, withDensity_apply f hT, setLIntegral_map hT hfm hvm]
  have hnn : ∀ z, 0 ≤ Real.exp (-(x / 2) * F z) := fun _ => (Real.exp_pos _).le
  have hmass : ν Set.univ = ENNReal.ofReal (∫ z, Real.exp (-(x / 2) * F z) ∂μ) := by
    rw [hνapply _ MeasurableSet.univ, Set.preimage_univ, Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)).symm
  have hne0 : ν Set.univ ≠ 0 := by
    rw [hmass]
    exact (ENNReal.ofReal_pos.2 hpos).ne'
  have hnetop : ν Set.univ ≠ ∞ := by
    rw [hmass]
    exact ENNReal.ofReal_ne_top
  refine ⟨⟨?_⟩, ?_⟩
  · show (BoxGaussian.normalize ν) Set.univ = 1
    simp only [BoxGaussian.normalize, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hne0 hnetop
  · set T : Set V := {ζ : V | ζ ∈ 𝒮 ∧ Qb (A + ζ) (A + ζ) ≤ cc}ᶜ with hTdef
    have hT : MeasurableSet T := by
      refine MeasurableSet.compl (IsClosed.measurableSet ?_)
      exact (Submodule.closed_of_finiteDimensional 𝒮).inter (isClosed_le hQc continuous_const)
    have hs : MeasurableSet {z : 𝒮 | cc < F z} :=
      (isOpen_lt continuous_const (hQc.comp continuous_subtype_val)).measurableSet
    have hpre : (Subtype.val : 𝒮 → V) ⁻¹' T = {z : 𝒮 | cc < F z} := by
      ext z
      simp [hTdef, F]
    have hνT : ν T = ENNReal.ofReal (∫ z in {z : 𝒮 | cc < F z}, Real.exp (-(x / 2) * F z) ∂μ) := by
      rw [hνapply T hT, hpre]
      exact (ofReal_integral_eq_lintegral_ofReal hint.integrableOn
        (Filter.Eventually.of_forall hnn)).symm
    rw [integral_indicator hs] at hoff
    have hO : 0 ≤ ∫ z in {z : 𝒮 | cc < F z}, Real.exp (-(x / 2) * F z) ∂μ :=
      integral_nonneg hnn
    have hreal : (BoxGaussian.normalize ν).real T =
        (∫ z, Real.exp (-(x / 2) * F z) ∂μ)⁻¹ *
          ∫ z in {z : 𝒮 | cc < F z}, Real.exp (-(x / 2) * F z) ∂μ := by
      simp only [Measure.real, BoxGaussian.normalize, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_inv]
      rw [hmass, hνT, ENNReal.toReal_ofReal hpos.le, ENNReal.toReal_ofReal hO]
    rw [hreal, inv_mul_le_iff₀ hpos]
    calc _ ≤ _ := hoff
      _ = _ := by ring
end Restriction
section LatticeCounting
variable {n : ℕ} [NeZero n]
private theorem card_supBall_le (o : TorusSite n) (r : ℕ) : (supBall o (r : ℝ)).card ≤ (2 * r + 1) ^ 4 := by apply _root_.YangMills.SharedProofs.p9908 <;> assumption
private theorem natAbs_valMinAbs_unitStep_le (i j : Fin 4) :
    ((TorusFields.unitStep n i j).valMinAbs).natAbs ≤ 1 := by
  by_cases h : j = i
  · subst h
    have : TorusFields.unitStep n j j = 1 := by simp [TorusFields.unitStep]
    rw [this, ZMod.valMinAbs_natAbs_eq_min]
    refine (min_le_left _ _).trans ?_
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_le _ _
  · have : TorusFields.unitStep n i j = 0 := by simp [TorusFields.unitStep, h]
    simp [this]
private theorem supDist_add_unitStep_le (u o : TorusSite n) (i : Fin 4) :
    supDist (u + TorusFields.unitStep n i) o ≤ supDist u o + 1 := by apply _root_.YangMills.SharedProofs.p13239 <;> assumption
private theorem supDist_sub_unitStep_le (u o : TorusSite n) (i : Fin 4) :
    supDist (u - TorusFields.unitStep n i) o ≤ supDist u o + 1 := by
  refine Finset.sup_le fun j _ => ?_
  have h1 : (u - TorusFields.unitStep n i) j - o j = (u j - o j) + -(TorusFields.unitStep n i j) := by
    simp only [Pi.sub_apply]
    ring
  rw [h1]
  refine ((ZMod.natAbs_valMinAbs_add_le _ _).trans (Int.natAbs_add_le _ _)).trans (Nat.add_le_add ?_ ?_)
  · exact Finset.le_sup (f := fun i => ((u i - o i).valMinAbs).natAbs) (Finset.mem_univ j)
  · rw [ZMod.natAbs_valMinAbs_neg]
    exact natAbs_valMinAbs_unitStep_le i j
private theorem card_bondsTouching_le (o : TorusSite n) (R : ℕ) :
    (bondsTouching o R).card ≤ 8 * (2 * R + 1) ^ 4 := by
  classical
  set Bx : Finset (TorusBond n) := (supBall o (R : ℝ)) ×ˢ Finset.univ with hBx
  have hsub : bondsTouching o R ⊆
      Bx ∪ Bx.image fun p : TorusBond n => (p.1 - TorusFields.unitStep n p.2, p.2) := by
    intro b hb
    simp only [bondsTouching, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rcases hb with hb | hb
    · exact Finset.mem_union_left _ (by simp [hBx, hb])
    · refine Finset.mem_union_right _
        (Finset.mem_image.2 ⟨(b.1 + TorusFields.unitStep n b.2, b.2), by simp [hBx, hb], ?_⟩)
      simp
  have hc : Bx.card ≤ 4 * (2 * R + 1) ^ 4 := by
    rw [hBx, Finset.card_product]
    simp only [Finset.card_univ, Fintype.card_fin]
    have := card_supBall_le o R
    omega
  calc (bondsTouching o R).card ≤ _ := Finset.card_le_card hsub
    _ ≤ Bx.card + (Bx.image _).card := Finset.card_union_le _ _
    _ ≤ Bx.card + Bx.card := Nat.add_le_add_left Finset.card_image_le _
    _ ≤ _ := by omega
abbrev _root_.YangMills.SharedProofs.p9498 := @card_bondsTouching_le
private theorem finrank_gaugeSlice_le (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions) :
    finrank ℝ (gaugeSlice o R A) ≤ 4 * (bondsTouching o R).card := by
  classical
  let f : gaugeSlice o R A →ₗ[ℝ] (TouchingBond o R → imaginaryQuaternions) :=
    { toFun := fun ζ b => ζ.1 b.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro ζ hζ
    refine Subtype.ext (funext fun b => ?_)
    by_cases hb : b ∈ bondsTouching o R
    · exact congrFun hζ ⟨b, hb⟩
    · exact ζ.2.1 b hb
  have hlie : finrank ℝ imaginaryQuaternions ≤ 4 := by
    have := Submodule.finrank_le imaginaryQuaternions
    rwa [Quaternion.finrank_eq_four] at this
  calc finrank ℝ (gaugeSlice o R A) ≤ finrank ℝ (TouchingBond o R → imaginaryQuaternions) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = Fintype.card (TouchingBond o R) * finrank ℝ imaginaryQuaternions := by
        rw [Module.finrank_pi_fintype]
        simp
    _ ≤ 4 * (bondsTouching o R).card := by
        rw [Fintype.card_coe, mul_comm]
        exact Nat.mul_le_mul_right _ hlie
private theorem bondsTouching_subset_bondsWithin (o : TorusSite n) (R : ℕ) (hR : 1 ≤ R) :
    bondsTouching o R ⊆ bondsWithin (supBall o (2 * (R : ℝ))) := by
  classical
  have hmem : ∀ z : TorusSite n, supDist z o ≤ R + 1 → z ∈ supBall o (2 * (R : ℝ)) := by
    intro z hz
    have h1 : (supDist z o : ℝ) ≤ R + 1 := by exact_mod_cast hz
    have h2 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    linarith
  have hle : ∀ z : TorusSite n, z ∈ supBall o (R : ℝ) → supDist z o ≤ R := by
    intro z hz
    have : (supDist z o : ℝ) ≤ R := by simpa [supBall] using hz
    exact_mod_cast this
  intro b hb
  simp only [bondsTouching, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  simp only [bondsWithin, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hb with hb | hb
  · have := hle _ hb
    exact ⟨hmem _ (by omega), hmem _ ((supDist_add_unitStep_le _ _ _).trans (by omega))⟩
  · have := hle _ hb
    refine ⟨hmem _ ?_, hmem _ (by omega)⟩
    have h3 := supDist_sub_unitStep_le (b.1 + TorusFields.unitStep n b.2) o b.2
    rw [add_sub_cancel_right] at h3
    omega
end LatticeCounting
private def hessianBilin {n : ℕ} [NeZero n] (a : ℝ) (L k : ℕ) (S : Finset (TorusSite n))
    (hsym : ∀ u v : TorusBond n → imaginaryQuaternions, hessianForm a L k S u v = hessianForm a L k S v u)
    (hlin : ∀ (c : ℝ) (u u' v : TorusBond n → imaginaryQuaternions), hessianForm a L k S (c • u + u') v =
      c * hessianForm a L k S u v + hessianForm a L k S u' v) :
    (TorusBond n → imaginaryQuaternions) →ₗ[ℝ] (TorusBond n → imaginaryQuaternions) →ₗ[ℝ] ℝ :=
  have hadd : ∀ u u' v : TorusBond n → imaginaryQuaternions, hessianForm a L k S (u + u') v =
      hessianForm a L k S u v + hessianForm a L k S u' v := fun u u' v => by
    simpa using hlin 1 u u' v
  have hzero : ∀ v : TorusBond n → imaginaryQuaternions, hessianForm a L k S 0 v = 0 := fun v => by
    have := hadd 0 0 v
    simp only [add_zero] at this
    linarith
  have hsmul : ∀ (c : ℝ) (u v : TorusBond n → imaginaryQuaternions),
      hessianForm a L k S (c • u) v = c * hessianForm a L k S u v :=
    fun c u v => by simpa [hzero] using hlin c u 0 v
  LinearMap.mk₂ ℝ (hessianForm a L k S) hadd hsmul
    (fun u v v' => by rw [hsym u, hsym u v, hsym u v', hadd])
    (fun c u v => by rw [hsym u, hsym u v, hsmul, smul_eq_mul])
theorem gaussianTailOffEllipsoid_holds (hForm : cubeHessianStatement)
    (hBounds : ellipsoidBoundsStatement) : gaussianTailOffEllipsoidStatement := by
  intro Tb hTb κ₀ hκ₁ hκ₂ C₀ hC₀
  obtain ⟨CQ, R₀, _, hform⟩ := hForm Tb hTb
  obtain ⟨K, xb, _, hbd⟩ := hBounds Tb hTb κ₀ hκ₁ hκ₂ C₀ hC₀
  refine ⟨max xb (max (((R₀ : ℝ) + 1) ^ 27) (Real.exp (2594 / C₀ + 1))), ?_⟩
  intro x R k n _ o A hxs hR hn hAx hQ
  have hxb : xb ≤ x := (le_max_left _ _).trans hxs
  have hxR : ((R₀ : ℝ) + 1) ^ 27 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hxs
  have hxe : Real.exp (2594 / C₀ + 1) ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hxs
  have hR1 : (1 : ℝ) ≤ (R₀ : ℝ) + 1 := by
    have : (0 : ℝ) ≤ R₀ := Nat.cast_nonneg _
    linarith
  have hx1 : 1 ≤ x := (one_le_pow₀ hR1).trans hxR
  have hx0 : 0 < x := by linarith
  have hRr : (R₀ : ℝ) + 1 ≤ R := by
    have h1 : (((R₀ : ℝ) + 1) ^ 27) ^ ((27 : ℕ) : ℝ)⁻¹ ≤ x ^ ((27 : ℕ) : ℝ)⁻¹ :=
      Real.rpow_le_rpow (by positivity) hxR (by positivity)
    rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at h1
    have h2 : x ^ ((27 : ℕ) : ℝ)⁻¹ ≤ x ^ κ₀ :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; norm_num at hκ₁; linarith)
    have h3 : x ^ κ₀ ≤ R := by
      rw [hR]
      exact Nat.le_ceil _
    linarith
  have hRR₀ : R₀ ≤ R := by
    have : (R₀ : ℝ) ≤ R := by linarith
    exact_mod_cast this
  have hRpos : 1 ≤ R := by
    have : (1 : ℝ) ≤ R := by linarith
    exact_mod_cast this
  have hRr0 : (0 : ℝ) < R := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hRpos
    linarith
  obtain ⟨-, -, hsym, hlin, -, -, -⟩ := hform k n o R hRR₀ hn
  obtain ⟨hlow, -⟩ := hbd x R k n o A hxb hR hn hAx
  set S := supBall o (2 * (R : ℝ)) with hS
  set cc : ℝ := C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2 with hcc
  set Qb := hessianBilin Tb.coupling Tb.side k S hsym hlin with hQb
  have hQapply : ∀ u v, Qb u v = hessianForm Tb.coupling Tb.side k S u v := fun _ _ => rfl
  have hcK : 0 < Tb.coercivity := hTb.cK_pos
  have hc : 0 < 2 * Tb.coercivity * ((R : ℝ) ^ 2)⁻¹ := by positivity
  have hnorm : ∀ ζ ∈ gaugeSlice o R A, ‖ζ‖ ^ 2 ≤ bondNormSq S ζ := by
    intro ζ hζ
    have hnn : 0 ≤ bondNormSq S ζ := Finset.sum_nonneg fun _ _ => by positivity
    have hle : ‖ζ‖ ≤ Real.sqrt (bondNormSq S ζ) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
      by_cases hb : b ∈ bondsTouching o R
      · refine Real.le_sqrt_of_sq_le ?_
        exact Finset.single_le_sum (f := fun b => ‖ζ b‖ ^ 2) (fun _ _ => by positivity)
          (bondsTouching_subset_bondsWithin o R hRpos hb)
      · rw [hζ.1 b hb, norm_zero]
        exact Real.sqrt_nonneg _
    calc ‖ζ‖ ^ 2 ≤ Real.sqrt (bondNormSq S ζ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = bondNormSq S ζ := Real.sq_sqrt hnn
  have hcq : ∀ z ∈ gaugeSlice o R A, 2 * Tb.coercivity * ((R : ℝ) ^ 2)⁻¹ * ‖z‖ ^ 2 ≤ Qb z z :=
    fun z hz => (mul_le_mul_of_nonneg_left (hnorm z hz) hc.le).trans (hlow z hz)
  obtain ⟨hprob, hoff⟩ :=
    gaussian_tail_on_subspace (gaugeSlice o R A) Qb (fun u v => hsym u v) _ hc hcq A x cc hx0 hQ
  refine ⟨hprob, hoff.trans ?_⟩
  have hdim : finrank ℝ (gaugeSlice o R A) ≤ 2592 * R ^ 4 := by
    have h1 := finrank_gaugeSlice_le o R A
    have h2 := card_bondsTouching_le o R
    have h3 : (2 * R + 1) ^ 4 ≤ (3 * R) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h4 : (3 * R) ^ 4 = 81 * R ^ 4 := by ring
    omega
  have hsq : Real.sqrt 2 ≤ Real.exp (1 / 2) := by
    have h1 : (1 / 2 : ℝ) + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
    have h2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    linarith
  have hpow : Real.sqrt 2 ^ finrank ℝ (gaugeSlice o R A) ≤ Real.exp (1296 * (R : ℝ) ^ 4) := by
    have h1 : Real.sqrt 2 ^ finrank ℝ (gaugeSlice o R A) ≤ Real.sqrt 2 ^ (2592 * R ^ 4) :=
      pow_le_pow_right₀ (by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)) hdim
    have h2 : Real.sqrt 2 ^ (2592 * R ^ 4) ≤ Real.exp (1 / 2) ^ (2592 * R ^ 4) :=
      pow_le_pow_left₀ (by positivity) hsq _
    have h3 : Real.exp (1 / 2) ^ (2592 * R ^ 4) = Real.exp (1296 * (R : ℝ) ^ 4) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    linarith
  have hδ : x * boxScale x ^ 2 = 4 * Real.log x ^ 2 := by
    have h1 : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num [Real.rpow_neg_one]
    simp only [boxScale]
    have : x * (2 * x ^ (-(1 / 2 : ℝ)) * Real.log x) ^ 2 =
        4 * (x * (x ^ (-(1 / 2 : ℝ))) ^ 2) * Real.log x ^ 2 := by ring
    rw [this, h1, mul_inv_cancel₀ hx0.ne']
    ring
  have hlog : 2594 / C₀ + 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact hxe
  have hlog2 : 2594 / C₀ ≤ Real.log x ^ 2 := by
    have hd : 0 < 2594 / C₀ := by positivity
    nlinarith
  have hC : 2594 ≤ C₀ * Real.log x ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlog2 hC₀.le
    rwa [mul_div_cancel₀ _ hC₀.ne'] at this
  have hxc : x * cc / 8 = C₀ * (R : ℝ) ^ 4 * Real.log x ^ 2 / 2 := by
    have : x * cc = C₀ * (R : ℝ) ^ 4 * (x * boxScale x ^ 2) := by
      rw [hcc]
      ring
    rw [this, hδ]
    ring
  calc Real.sqrt 2 ^ finrank ℝ (gaugeSlice o R A) * Real.exp (-(x * cc / 8))
      ≤ Real.exp (1296 * (R : ℝ) ^ 4) * Real.exp (-(x * cc / 8)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (1296 * (R : ℝ) ^ 4 - x * cc / 8) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-((R : ℝ) ^ 4)) := by
        refine Real.exp_le_exp.2 ?_
        rw [hxc]
        have hR4 : (0 : ℝ) < (R : ℝ) ^ 4 := by positivity
        nlinarith
end YangMills.Construction.BoxGaussian
end
