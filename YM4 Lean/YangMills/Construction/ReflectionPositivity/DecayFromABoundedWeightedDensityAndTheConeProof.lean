import YangMills.Construction.ReflectionPositivity.BoundedMomentumDensityWithReflectionSizesProof
import YangMills.Construction.ReflectionPositivity.DecayFromABoundedWeightedDensityAndTheCone
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Real
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.ConeDecay
open EnergyMomentum DirectionPictures
theorem one_le_tanh_mul_one_add_inv {v : ℝ} (hv : 0 < v) : 1 ≤ Real.tanh v * (1 + 1 / v) := by
  have hneg : 0 < Real.exp (-v) := Real.exp_pos _
  have hprod : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
  have hsq : 2 * v + 1 ≤ Real.exp v * Real.exp v := by
    rw [← Real.exp_add]
    have := Real.add_one_le_exp (v + v)
    linarith
  have hlin : (2 * v + 1) * Real.exp (-v) ≤ Real.exp v := by
    calc (2 * v + 1) * Real.exp (-v) ≤ (Real.exp v * Real.exp v) * Real.exp (-v) :=
          mul_le_mul_of_nonneg_right hsq hneg.le
      _ = Real.exp v * (Real.exp v * Real.exp (-v)) := by ring
      _ = Real.exp v := by rw [hprod, mul_one]
  have htanh : Real.tanh v * (1 + 1 / v) =
      ((Real.exp v - Real.exp (-v)) * (v + 1)) / ((Real.exp v + Real.exp (-v)) * v) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have : Real.exp v + Real.exp (-v) ≠ 0 := by positivity
    field_simp
  rw [htanh, one_le_div (by positivity)]
  nlinarith [hlin]
theorem lintegral_exp_density_Ioi {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ∫⁻ s in Ioi y, ENNReal.ofReal (t * Real.exp (-(t * s))) =
      ENNReal.ofReal (Real.exp (-(t * y))) := by
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-t * s)) (Ioi y) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ht) y
  have hrw : ∫⁻ s in Ioi y, ENNReal.ofReal (t * Real.exp (-(t * s))) =
      ∫⁻ s in Ioi y, ENNReal.ofReal (t * Real.exp (-t * s)) := by
    simp only [neg_mul]
  rw [hrw, ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul t)
    (Filter.Eventually.of_forall fun s => by positivity)]
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr ht) y]
  congr 1
  rw [neg_mul]
  field_simp
theorem lintegral_exp_neg_mul_Ioi_param {a y : ℝ} (hy : 0 < y) :
    ∫⁻ t in Ioi a, ENNReal.ofReal (Real.exp (-(t * y))) =
      ENNReal.ofReal (Real.exp (-(a * y)) / y) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-y * t)) (Ioi a) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hy) a
  have hrw : ∫⁻ t in Ioi a, ENNReal.ofReal (Real.exp (-(t * y))) =
      ∫⁻ t in Ioi a, ENNReal.ofReal (Real.exp (-y * t)) := by
    refine lintegral_congr fun t => ?_
    rw [neg_mul, mul_comm]
  rw [hrw, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun s => by positivity)]
  rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hy) a]
  congr 1
  rw [neg_mul, mul_comm y a]
  field_simp
theorem lintegral_inv_cube_Ioi {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioi a, ENNReal.ofReal (48 / t ^ 3) = ENNReal.ofReal (24 / a ^ 2) := by
  have hint : IntegrableOn (fun t : ℝ => 48 * t ^ (-3 : ℝ)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ha).const_mul 48
  have hcongr : ∫⁻ t in Ioi a, ENNReal.ofReal (48 / t ^ 3) =
      ∫⁻ t in Ioi a, ENNReal.ofReal (48 * t ^ (-3 : ℝ)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ha.trans ht
    have e : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by
      rw [Real.rpow_neg ht0.le]
      norm_num
    simp only [e, div_eq_mul_inv]
  rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => by
      have ht0 : 0 < t := ha.trans ht
      positivity))]
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha]
  congr 1
  have e : a ^ ((-3 : ℝ) + 1) = (a ^ 2)⁻¹ := by
    rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg ha.le]
    norm_num
  rw [e]
  field_simp
  norm_num
variable (μ : Fin 4)
theorem angleSupNorm_nonneg (η : TransverseAxis μ → ℝ) : 0 ≤ angleSupNorm μ η := by
  obtain ⟨l⟩ : Nonempty (TransverseAxis μ) := Finset.univ_nonempty.to_subtype.map Subtype.val
  exact (abs_nonneg (η l)).trans
    (Finset.le_sup' (fun l => |η l|) (Finset.mem_univ l))
theorem measurable_angleSupNorm : Measurable (angleSupNorm μ) := by
  have : Continuous (angleSupNorm μ) := by
    unfold angleSupNorm
    exact Continuous.finset_sup'_apply _ fun l _ => (continuous_apply l).abs
  exact this.measurable
theorem volume_angleSupNorm_lt_le (s : ℝ) :
    volume {η : TransverseAxis μ → ℝ | angleSupNorm μ η < s} ≤ ENNReal.ofReal (2 * s) ^ 3 := by
  have hsub : {η : TransverseAxis μ → ℝ | angleSupNorm μ η < s} ⊆
      Set.pi univ fun _ => Ioo (-s) s := by
    intro η hη l _
    have h := (Finset.sup'_lt_iff (f := fun l => |η l|) Finset.univ_nonempty).mp hη l
      (Finset.mem_univ l)
    exact abs_lt.mp h
  refine (measure_mono hsub).trans ?_
  rw [Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, card_transverseAxis]
  have e : s - -s = 2 * s := by ring
  rw [e]
theorem lintegral_exp_neg_angleSupNorm_le {t : ℝ} (ht : 0 < t) :
    ∫⁻ η : TransverseAxis μ → ℝ, ENNReal.ofReal (Real.exp (-(t * angleSupNorm μ η))) ≤
      ENNReal.ofReal (48 / t ^ 3) := by
  set g : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (t * Real.exp (-(t * s))) with hg
  have hgm : Measurable g := by
    simp only [hg]
    fun_prop
  have hnorm := measurable_angleSupNorm μ
  have hset : MeasurableSet {q : (TransverseAxis μ → ℝ) × ℝ | angleSupNorm μ q.1 < q.2} :=
    measurableSet_lt (hnorm.comp measurable_fst) measurable_snd
  set K : (TransverseAxis μ → ℝ) → ℝ → ℝ≥0∞ :=
    fun η s => indicator {q : (TransverseAxis μ → ℝ) × ℝ | angleSupNorm μ q.1 < q.2}
      (fun q => g q.2) (η, s) with hK
  have hKm : Measurable (Function.uncurry K) :=
    (hgm.comp measurable_snd).indicator hset
  have hlayer : ∀ η : TransverseAxis μ → ℝ,
      ENNReal.ofReal (Real.exp (-(t * angleSupNorm μ η))) = ∫⁻ s, K η s := by
    intro η
    rw [← lintegral_exp_density_Ioi ht, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun s => ?_
    by_cases h : angleSupNorm μ η < s
    · simp [hK, hg, indicator, h]
    · simp [hK, hg, indicator, h]
  have hslice : ∀ s : ℝ, ∫⁻ η, K η s =
      g s * volume {η : TransverseAxis μ → ℝ | angleSupNorm μ η < s} := by
    intro s
    have hs : MeasurableSet {η : TransverseAxis μ → ℝ | angleSupNorm μ η < s} :=
      measurableSet_lt hnorm measurable_const
    have : (fun η => K η s) =
        indicator {η : TransverseAxis μ → ℝ | angleSupNorm μ η < s} fun _ => g s := by
      funext η
      by_cases h : angleSupNorm μ η < s
      · simp [hK, indicator, h]
      · simp [hK, indicator, h]
    rw [this, lintegral_indicator hs, setLIntegral_const]
  set ρ : ℝ → ℝ := fun s => s ^ ((4 : ℝ) - 1) * Real.exp (-(t * s)) with hρ
  have hρint : IntegrableOn ρ (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (4 : ℝ) - 1) (b := t)
      (by norm_num) (by norm_num) ht
    have e : ρ = fun x : ℝ => x ^ ((4 : ℝ) - 1) * Real.exp (-t * x ^ (1 : ℝ)) := by
      funext x
      simp only [hρ, Real.rpow_one, neg_mul]
    rw [e]
    exact h
  have hρval : ∫ s in Ioi (0 : ℝ), ρ s = 6 / t ^ 4 := by
    rw [hρ, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) ht]
    have hG : Real.Gamma 4 = 6 := by
      rw [show (4 : ℝ) = ((3 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num [Nat.factorial]
    rw [hG, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hbound : ∀ s : ℝ, g s * volume {η : TransverseAxis μ → ℝ | angleSupNorm μ η < s} ≤
      (Ioi (0 : ℝ)).indicator (fun s => ENNReal.ofReal (8 * t * ρ s)) s := by
    intro s
    by_cases hs : 0 < s
    · rw [indicator_of_mem (mem_Ioi.mpr hs)]
      refine (mul_le_mul_right (volume_angleSupNorm_lt_le μ s) _).trans ?_
      rw [hg, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      have e : s ^ ((4 : ℝ) - 1) = s ^ 3 := by
        rw [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      simp only [hρ, e]
      ring
    · have hempty : {η : TransverseAxis μ → ℝ | angleSupNorm μ η < s} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun η hη => hs ?_
        exact lt_of_le_of_lt (angleSupNorm_nonneg μ η) hη
      rw [hempty]
      simp
  calc ∫⁻ η : TransverseAxis μ → ℝ, ENNReal.ofReal (Real.exp (-(t * angleSupNorm μ η)))
      = ∫⁻ η, ∫⁻ s, K η s := lintegral_congr hlayer
    _ = ∫⁻ s, ∫⁻ η, K η s := lintegral_lintegral_swap hKm.aemeasurable
    _ ≤ ∫⁻ s, (Ioi (0 : ℝ)).indicator (fun s => ENNReal.ofReal (8 * t * ρ s)) s :=
        lintegral_mono fun s => by rw [hslice s]; exact hbound s
    _ = ENNReal.ofReal (48 / t ^ 3) := by
        rw [lintegral_indicator measurableSet_Ioi,
          ← ofReal_integral_eq_lintegral_ofReal (hρint.const_mul _)
            ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => by
              have hs0 : (0 : ℝ) < s := hs
              simp only [hρ]
              positivity))]
        rw [integral_const_mul, hρval]
        congr 1
        field_simp
        norm_num
def conePotential (a b y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(a * y))) +
    ENNReal.ofReal b * ∫⁻ t in Ioi a, ENNReal.ofReal (Real.exp (-(t * y)))
theorem measurable_conePotential (a b : ℝ) : Measurable (conePotential a b) := by
  have h1 : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (-(a * y))) := by fun_prop
  have h2 : Measurable fun y : ℝ => ∫⁻ t in Ioi a, ENNReal.ofReal (Real.exp (-(t * y))) :=
    Measurable.lintegral_prod_right'
      (f := fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(q.2 * q.1)))) (by fun_prop)
  exact h1.add (h2.const_mul _)
theorem conePotential_zero (a : ℝ) {b : ℝ} (hb : 0 < b) : conePotential a b 0 = ∞ := by
  have h : ∫⁻ t in Ioi a, ENNReal.ofReal (Real.exp (-(t * 0))) = ∞ := by
    simp
  rw [conePotential, h, ENNReal.mul_top (by simpa using hb)]
  simp
theorem conePotential_of_pos (a : ℝ) {b y : ℝ} (hb : 0 ≤ b) (hy : 0 < y) :
    conePotential a b y = ENNReal.ofReal (Real.exp (-(a * y)) * (1 + b / y)) := by
  rw [conePotential, lintegral_exp_neg_mul_Ioi_param hy, ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
theorem lintegral_conePotential_angleSupNorm_le {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫⁻ η : TransverseAxis μ → ℝ, conePotential a b (angleSupNorm μ η) ≤
      ENNReal.ofReal (48 / a ^ 3) + ENNReal.ofReal b * ENNReal.ofReal (24 / a ^ 2) := by
  have hnorm := measurable_angleSupNorm μ
  have hm1 : Measurable fun η : TransverseAxis μ → ℝ =>
      ENNReal.ofReal (Real.exp (-(a * angleSupNorm μ η))) := by fun_prop
  have hm3 : Measurable fun η : TransverseAxis μ → ℝ =>
      ∫⁻ t in Ioi a, ENNReal.ofReal (Real.exp (-(t * angleSupNorm μ η))) :=
    Measurable.lintegral_prod_right'
      (f := fun q : (TransverseAxis μ → ℝ) × ℝ =>
        ENNReal.ofReal (Real.exp (-(q.2 * angleSupNorm μ q.1)))) (by fun_prop)
  simp only [conePotential]
  rw [lintegral_add_left hm1, lintegral_const_mul _ hm3]
  refine add_le_add (lintegral_exp_neg_angleSupNorm_le μ ha) (mul_le_mul_right ?_ _)
  calc ∫⁻ η : TransverseAxis μ → ℝ, ∫⁻ t in Ioi a,
        ENNReal.ofReal (Real.exp (-(t * angleSupNorm μ η)))
      = ∫⁻ t in Ioi a, ∫⁻ η : TransverseAxis μ → ℝ,
          ENNReal.ofReal (Real.exp (-(t * angleSupNorm μ η))) :=
        lintegral_lintegral_swap (by fun_prop)
    _ ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (48 / t ^ 3) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht =>
          lintegral_exp_neg_angleSupNorm_le μ (ha.trans ht)
    _ = ENNReal.ofReal (24 / a ^ 2) := lintegral_inv_cube_Ioi ha
theorem exp_le_conePotential_mul_weight {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) {c k E y w : ℝ}
    (hc : 0 < c) (hk : 0 < k) (hE : 0 < E) (hy : 0 ≤ y) (hcone : k * y ≤ E)
    (hw : c * Real.tanh (2 * r * E) ≤ w) :
    ENNReal.ofReal (Real.exp (-(n * E))) ≤
      ENNReal.ofReal (1 / c) *
        (conePotential (n * k) (1 / (2 * r * k)) y * ENNReal.ofReal w) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : 0 < 2 * r * E := by positivity
  have htanh : 0 < Real.tanh (2 * r * E) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hv) (Real.cosh_pos _)
  have hw0 : 0 < w := lt_of_lt_of_le (mul_pos hc htanh) hw
  rcases hy.eq_or_lt with rfl | hy0
  · rw [conePotential_zero _ (by positivity), ENNReal.top_mul (by simpa using hw0),
      ENNReal.mul_top (by simpa using hc)]
    exact le_top
  · rw [conePotential_of_pos _ (by positivity) hy0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := one_le_tanh_mul_one_add_inv hv
    have h2 : 1 + 1 / (2 * r * E) ≤ 1 + 1 / (2 * r * k) / y := by
      have e : 1 / (2 * r * k) / y = 1 / (2 * r * (k * y)) := by
        field_simp
      rw [e]
      have : 0 < k * y := by positivity
      gcongr
    have h3 : Real.exp (-(n * E)) ≤ Real.exp (-(n * k * y)) := by
      refine Real.exp_le_exp.mpr (neg_le_neg ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hcone hn0.le
    have h4 : Real.tanh (2 * r * E) ≤ w / c := by
      rw [le_div_iff₀ hc, mul_comm]
      exact hw
    have h5 : 1 ≤ w / c * (1 + 1 / (2 * r * k) / y) := by
      refine h1.trans ?_
      have hq : 0 ≤ 1 + 1 / (2 * r * E) := by positivity
      exact mul_le_mul h4 h2 hq (by positivity)
    calc Real.exp (-(n * E)) = Real.exp (-(n * E)) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-(n * k * y)) * (w / c * (1 + 1 / (2 * r * k) / y)) :=
          mul_le_mul h3 h5 zero_le_one (Real.exp_pos _).le
      _ = 1 / c * (Real.exp (-(n * k * y)) * (1 + 1 / (2 * r * k) / y) * w) := by ring
theorem expNegNatMulEnergy_of_ne_top (n : ℕ) {E : ℝ≥0∞} (hE : E ≠ ∞) :
    expNegNatMulEnergy n E = Real.exp (-(n * E.toReal)) := by
  have h : ((expNegEnergy E : unitInterval) : ℝ) = Real.exp (-E.toReal) := by
    simp [expNegEnergy, hE]
  rw [expNegNatMulEnergy, h, ← Real.exp_nat_mul]
  congr 1
  ring
theorem slopeConstant_pos : 0 < slopeConstant := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.slopeConstant_pos <;> assumption
theorem weightConst_pos : 0 < SmearingFilter.weightConst := by
  have h : (1 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  unfold SmearingFilter.weightConst
  linarith
theorem measurableSet_fundamentalBox : MeasurableSet (fundamentalBox μ) := by
  have hbox : fundamentalBox μ = Set.pi univ fun _ => Ioc (-π) π := by
    ext η
    simp [fundamentalBox, Set.mem_pi]
  rw [hbox]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc
theorem lintegral_conePotential_torus_le {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫⁻ η, conePotential a b (torusSupNorm μ η) ∂(torusMeasure μ) ≤
      ENNReal.ofReal (48 / a ^ 3) + ENNReal.ofReal b * ENNReal.ofReal (24 / a ^ 2) := by
  have hF : Measurable fun η => conePotential a b (torusSupNorm μ η) :=
    (measurable_conePotential a b).comp (continuous_torusSupNorm μ).measurable
  rw [torusMeasure, lintegral_map hF (continuous_torusProj μ).measurable]
  have e : ∫⁻ η in fundamentalBox μ, conePotential a b (torusSupNorm μ (torusProj μ η)) =
      ∫⁻ η in fundamentalBox μ, conePotential a b (angleSupNorm μ η) :=
    setLIntegral_congr_fun (measurableSet_fundamentalBox μ) fun η hη => by
      rw [torusSupNorm_torusProj_of_mem hη]
  rw [e]
  exact (setLIntegral_le_lintegral _ _).trans (lintegral_conePotential_angleSupNorm_le μ ha b)
theorem coneDecayTheorem_holds (hKernel : SmearingFilter.Bounds.FilterWeightBounds)
    (hMoments : DirectionPictures.SpectralMeasuresTheorem) :
    EnergyMomentum.ConeDecayTheorem := by
  intro μ r n H hr hn hH m _ C h hC hmC hcone hhm hhb himage
  obtain ⟨-, -, -, -, -, -, -, -, ht, hEm, -, -, hπ⟩ := (hMoments μ).1
  obtain ⟨hΨc, hΨ, -, -, hΨt⟩ := hKernel.2
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc0 := weightConst_pos
  have hk0 := slopeConstant_pos
  set c := SmearingFilter.weightConst with hcdef
  set k := slopeConstant with hkdef
  set p : EnergyMomentum.SpectralSpace μ → EnergyMomentum.DualTorus μ :=
    fun x => torusProj μ x.momentum with hp
  set g : EnergyMomentum.SpectralSpace μ → ℝ := fun x => expNegNatMulEnergy (2 * r) x.energy with hg
  have hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨pow_nonneg (expNegEnergy x.energy).2.1 _, pow_le_one₀ (expNegEnergy x.energy).2.1
      (expNegEnergy x.energy).2.2⟩
  have hgm : Measurable g := ht.pow_const _
  have hΨm : Measurable fun x => SmearingFilter.weightSeries (g x) := by
    have hcont : Continuous fun u : ℝ => SmearingFilter.weightSeries (max 0 (min 1 u)) :=
      hΨc.comp_continuous (by fun_prop) fun u =>
        ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    have he : (fun x => SmearingFilter.weightSeries (g x)) =
        (fun u : ℝ => SmearingFilter.weightSeries (max 0 (min 1 u))) ∘ g := by
      funext x
      have h1 := (hg01 x).1
      have h2 := (hg01 x).2
      simp [min_eq_right h2, max_eq_right h1]
    rw [he]
    exact hcont.measurable.comp hgm
  set w : EnergyMomentum.SpectralSpace μ → ℝ := fun x => (SmearingFilter.weightSeries (g x)).re
    with hw
  have hwm : Measurable w := Complex.measurable_re.comp hΨm
  have hw0 : ∀ x, 0 ≤ w x := fun x => (hΨ _ (hg01 x)).2.1
  have hwc : ∀ x, SmearingFilter.weightSeries (g x) = (w x : ℂ) := fun x =>
    Complex.ext rfl (by simpa using (hΨ _ (hg01 x)).1)
  have hwint : Integrable w m :=
    Integrable.of_bound hwm.aestronglyMeasurable (2 * SmearingFilter.absCoeffSum)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (hw0 x)]
        exact (hΨ _ (hg01 x)).2.2)
  have : IsFiniteMeasure (torusMeasure μ) :=
    ⟨by rw [torusMeasure_univ]; exact ENNReal.ofReal_lt_top⟩
  have hhint : Integrable h (torusMeasure μ) :=
    Integrable.of_bound hhm.aestronglyMeasurable H
      (Filter.Eventually.of_forall fun η => by
        rw [Real.norm_of_nonneg (hhb η).1]
        exact (hhb η).2)
  have hset : ∀ S : Set (EnergyMomentum.DualTorus μ), MeasurableSet S →
      ∫⁻ x in p ⁻¹' S, ENNReal.ofReal (w x) ∂m =
        ∫⁻ η in S, ENNReal.ofReal (h η) ∂(torusMeasure μ) := by
    intro S hS
    have hcplx : ∫ x in p ⁻¹' S, ((w x : ℝ) : ℂ) ∂m =
        ∫ η in S, ((h η : ℝ) : ℂ) ∂(torusMeasure μ) := by
      have hfun : (fun x => ((w x : ℝ) : ℂ)) = fun x =>
          SmearingFilter.weightSeries (expNegNatMulEnergy (2 * r) x.energy) :=
        funext fun x => (hwc x).symm
      rw [hfun]
      exact himage S hS
    rw [integral_complex_ofReal, integral_complex_ofReal] at hcplx
    have hreal := Complex.ofReal_injective hcplx
    rw [← ofReal_integral_eq_lintegral_ofReal hwint.integrableOn
        (Filter.Eventually.of_forall hw0),
      ← ofReal_integral_eq_lintegral_ofReal hhint.integrableOn
        (Filter.Eventually.of_forall fun η => (hhb η).1), hreal]
  have hfw : Measurable fun x => ENNReal.ofReal (w x) := hwm.ennreal_ofReal
  have hfh : Measurable fun η => ENNReal.ofReal (h η) := hhm.ennreal_ofReal
  have hmeas : (m.withDensity fun x => ENNReal.ofReal (w x)).map p =
      (torusMeasure μ).withDensity fun η => ENNReal.ofReal (h η) := by
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply hπ hS, withDensity_apply _ (hπ hS), withDensity_apply _ hS]
    exact hset S hS
  set a : ℝ := n * k with ha
  set b : ℝ := 1 / (2 * r * k) with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  set F : EnergyMomentum.DualTorus μ → ℝ≥0∞ := fun η => conePotential a b (torusSupNorm μ η)
    with hF
  have hFm : Measurable F :=
    (measurable_conePotential a b).comp (continuous_torusSupNorm μ).measurable
  have hpush : ∫⁻ x, F (p x) * ENNReal.ofReal (w x) ∂m =
      ∫⁻ η, F η * ENNReal.ofReal (h η) ∂(torusMeasure μ) := by
    have e1 : ∫⁻ x, F (p x) * ENNReal.ofReal (w x) ∂m =
        ∫⁻ x, F (p x) ∂(m.withDensity fun x => ENNReal.ofReal (w x)) := by
      have h1 := lintegral_withDensity_eq_lintegral_mul m hfw (hFm.comp hπ)
      exact (lintegral_congr fun x => mul_comm _ _).trans h1.symm
    have e2 : ∫⁻ η, F η * ENNReal.ofReal (h η) ∂(torusMeasure μ) =
        ∫⁻ η, F η ∂((torusMeasure μ).withDensity fun η => ENNReal.ofReal (h η)) := by
      have h1 := lintegral_withDensity_eq_lintegral_mul (torusMeasure μ) hfh hFm
      exact (lintegral_congr fun x => mul_comm _ _).trans h1.symm
    rw [e1, e2, ← hmeas, lintegral_map hFm hπ]
  have hupper : ∫⁻ η, F η * ENNReal.ofReal (h η) ∂(torusMeasure μ) ≤
      (ENNReal.ofReal (48 / a ^ 3) + ENNReal.ofReal b * ENNReal.ofReal (24 / a ^ 2)) *
        ENNReal.ofReal H := by
    calc ∫⁻ η, F η * ENNReal.ofReal (h η) ∂(torusMeasure μ)
        ≤ ∫⁻ η, F η * ENNReal.ofReal H ∂(torusMeasure μ) :=
          lintegral_mono fun η =>
            mul_le_mul_right (ENNReal.ofReal_le_ofReal (hhb η).2) _
      _ = (∫⁻ η, F η ∂(torusMeasure μ)) * ENNReal.ofReal H :=
          lintegral_mul_const _ hFm
      _ ≤ _ := mul_le_mul_left (lintegral_conePotential_torus_le μ ha0 b) _
  set A : Set (EnergyMomentum.SpectralSpace μ) := {x | 0 < x.energy ∧ x.energy < ∞} with hAdef
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const hEm).inter (measurableSet_lt hEm measurable_const)
  have hpoint : ∀ x ∈ C, x ∈ A →
      ENNReal.ofReal (expNegNatMulEnergy n x.energy) ≤
        ENNReal.ofReal (1 / c) * (F (p x) * ENNReal.ofReal (w x)) := by
    intro x hxC hxA
    have hne : x.energy ≠ ∞ := hxA.2.ne
    have hE : 0 < x.energy.toReal := ENNReal.toReal_pos hxA.1.ne' hne
    have hFx : F (p x) = conePotential a b (angleSupNorm μ x.momentum) := by
      have hmem : x.momentum ∈ fundamentalBox μ := x.2
      simp only [hF, hp]
      rw [torusSupNorm_torusProj_of_mem hmem]
    have hwx : c * Real.tanh (2 * r * x.energy.toReal) ≤ w x := by
      have hpos : 0 < 2 * r * x.energy.toReal := by positivity
      have h1 := (hΨt (ENNReal.ofReal (2 * r * x.energy.toReal))
        (ENNReal.ofReal_pos.mpr hpos) ENNReal.ofReal_lt_top).2
      rw [ENNReal.toReal_ofReal hpos.le] at h1
      have h2 : SmearingFilter.weightSeriesAtExp (ENNReal.ofReal (2 * r * x.energy.toReal)) =
          SmearingFilter.weightSeries (g x) := by
        rw [SmearingFilter.weightSeriesAtExp, SmearingFilter.extendedExpNeg,
          if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hpos.le]
        simp only [hg]
        rw [expNegNatMulEnergy_of_ne_top _ hne]
        push_cast
        rfl
      rw [h2] at h1
      exact h1
    rw [expNegNatMulEnergy_of_ne_top _ hne, hFx]
    exact exp_le_conePotential_mul_weight hn hr hc0 hk0 hE (angleSupNorm_nonneg μ _)
      (hcone x hxC hxA.2) hwx
  have hae : ∀ᵐ x ∂m, x ∈ C := mem_ae_iff.mpr hmC
  have hmain : ∫⁻ x in A, ENNReal.ofReal (expNegNatMulEnergy n x.energy) ∂m ≤
      ENNReal.ofReal (1 / c) *
        ((ENNReal.ofReal (48 / a ^ 3) + ENNReal.ofReal b * ENNReal.ofReal (24 / a ^ 2)) *
          ENNReal.ofReal H) := by
    calc ∫⁻ x in A, ENNReal.ofReal (expNegNatMulEnergy n x.energy) ∂m
        = ∫⁻ x, A.indicator (fun x => ENNReal.ofReal (expNegNatMulEnergy n x.energy)) x ∂m :=
          (lintegral_indicator hA _).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (1 / c) * (F (p x) * ENNReal.ofReal (w x)) ∂m := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with x hx
          by_cases hxA : x ∈ A
          · rw [indicator_of_mem hxA]
            exact hpoint x hx hxA
          · rw [indicator_of_notMem hxA]
            exact zero_le
      _ = ENNReal.ofReal (1 / c) * ∫⁻ x, F (p x) * ENNReal.ofReal (w x) ∂m :=
          lintegral_const_mul _ ((hFm.comp hπ).mul hfw)
      _ ≤ _ := by
          rw [hpush]
          exact mul_le_mul_right hupper _
  have hnonneg : ∀ x : EnergyMomentum.SpectralSpace μ, 0 ≤ expNegNatMulEnergy n x.energy :=
    fun x => pow_nonneg (expNegEnergy x.energy).2.1 _
  have hem : Measurable fun x : EnergyMomentum.SpectralSpace μ => expNegNatMulEnergy n x.energy :=
    ht.pow_const _
  have hB : 0 ≤ H / (c * k ^ 3) * (48 / (n : ℝ) ^ 3 + 12 / ((r : ℝ) * (n : ℝ) ^ 2)) := by
    positivity
  have hval : ENNReal.ofReal (1 / c) *
      ((ENNReal.ofReal (48 / a ^ 3) + ENNReal.ofReal b * ENNReal.ofReal (24 / a ^ 2)) *
        ENNReal.ofReal H) =
      ENNReal.ofReal (H / (c * k ^ 3) * (48 / (n : ℝ) ^ 3 + 12 / ((r : ℝ) * (n : ℝ) ^ 2))) := by
    rw [← ENNReal.ofReal_mul hb0.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ha, hb]
    field_simp
    ring
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnonneg)
    hem.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB (hval ▸ hmain)
end YangMills.Construction.ReflectionPositivity.ConeDecay
