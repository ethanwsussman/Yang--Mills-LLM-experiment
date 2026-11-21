import YangMills.Construction.LawByMomentsOfTheFlow.BandsBoundAStarMean
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentMethod
section
variable {J : Type} {P : Measure (TranslateValues J)} [IsProbabilityMeasure P]
private theorem shiftInvariantSigma_le_pi : shiftInvariantSigma J ≤ MeasurableSpace.pi := inf_le_right
private theorem setIntegral_le_of_invariantCondExp_le {g : TranslateValues J → ℝ} (hg : Integrable g P) {c : ℝ}
    (hc : ∀ᵐ v ∂P, invariantCondExp P g v ≤ c)
    {A : Set (TranslateValues J)} (hA : MeasurableSet[shiftInvariantSigma J] A) : ∫ v in A, g v ∂P ≤ c * P.real A := by
  have e := setIntegral_condExp (μ := P) shiftInvariantSigma_le_pi hg hA
  rw [← e]
  have h1 : ∫ v in A, (P[g | shiftInvariantSigma J]) v ∂P ≤ ∫ _v in A, c ∂P :=
    setIntegral_mono_ae integrable_condExp.integrableOn (integrableOn_const (by simp)) hc
  refine h1.trans (le_of_eq ?_)
  rw [setIntegral_const, smul_eq_mul, mul_comm]
private theorem setIntegral_rpow_mul_indicator_le {A : Set (TranslateValues J)}
    (hA : MeasurableSet[shiftInvariantSigma J] A) {F E : TranslateValues J → ℝ} {p : ℕ} {b G : ℝ}
    (hp : 2 ≤ p) (hb : 0 ≤ b) (hG : 0 ≤ G) (hF : Integrable F P) (hF0 : ∀ᵐ v ∂P, 0 ≤ F v) (hE : Integrable E P)
    (hE01 : ∀ᵐ v ∂P, E v = 0 ∨ E v = 1) (hFb : ∀ᵐ v ∂P, invariantCondExp P F v ≤ G)
    (hEb : ∀ᵐ v ∂P, invariantCondExp P E v ≤ b) :
    Integrable (fun v => F v ^ (1 / (p : ℝ)) * E v) P ∧ 0 ≤ᵐ[P] (fun v => F v ^ (1 / (p : ℝ)) * E v) ∧
      ∫ v in A, F v ^ (1 / (p : ℝ)) * E v ∂P ≤ G ^ (1 / (p : ℝ)) * b ^ (1 - 1 / (p : ℝ)) * P.real A := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < p := by linarith
  have hc := Real.HolderConjugate.conjExponent hp1
  set q : ℝ := Real.conjExponent p with hq
  have hq0 : 0 < q := hc.symm.pos
  have hqi : 1 / q = 1 - 1 / (p : ℝ) := by
    have h := hc.inv_add_inv_eq_one
    rw [one_div, one_div]
    linarith
  set φ : TranslateValues J → ℝ := fun v => F v ^ (1 / (p : ℝ)) with hφ
  have hφm : AEStronglyMeasurable φ P := (hF.aemeasurable.pow_const _).aestronglyMeasurable
  have hφ0 : ∀ᵐ v ∂P, 0 ≤ φ v := by
    filter_upwards [hF0] with v hv using Real.rpow_nonneg hv _
  have hφp : ∀ᵐ v ∂P, φ v ^ (p : ℝ) = F v := by
    filter_upwards [hF0] with v hv
    show (F v ^ (1 / (p : ℝ))) ^ (p : ℝ) = F v
    rw [← Real.rpow_mul hv]
    rw [one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hφnorm : Integrable (fun v => ‖φ v‖ ^ (ENNReal.ofReal p).toReal) P := by
    rw [ENNReal.toReal_ofReal hp0.le]
    refine hF.congr ?_
    filter_upwards [hφ0, hφp] with v h0 h1
    rw [Real.norm_of_nonneg h0, h1]
  have hφmem : MemLp φ (ENNReal.ofReal p) P :=
    (integrable_norm_rpow_iff hφm (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top).1 hφnorm
  have hφ1 : Integrable φ P := hφmem.integrable (by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp1.le)
  have hE0 : ∀ᵐ v ∂P, 0 ≤ E v := by
    filter_upwards [hE01] with v hv
    rcases hv with h | h <;> rw [h] <;> norm_num
  have hEle : ∀ᵐ v ∂P, E v ≤ 1 := by
    filter_upwards [hE01] with v hv
    rcases hv with h | h <;> rw [h] <;> norm_num
  have hint : Integrable (fun v => φ v * E v) P := by
    refine hφ1.mono (hφm.mul hE.aestronglyMeasurable) ?_
    filter_upwards [hφ0, hE0, hEle] with v h0 h1 h2
    rw [Real.norm_of_nonneg (mul_nonneg h0 h1), Real.norm_of_nonneg h0]
    nlinarith
  refine ⟨hint, ?_, ?_⟩
  · filter_upwards [hφ0, hE0] with v h0 h1
    exact mul_nonneg h0 h1
  set ρ : Measure (TranslateValues J) := P.restrict A with hρ
  have hres : ∀ {Q : TranslateValues J → Prop}, (∀ᵐ v ∂P, Q v) → ∀ᵐ v ∂ρ, Q v := fun h => ae_restrict_of_ae h
  have hmem1 : MemLp φ (ENNReal.ofReal p) ρ := hφmem.restrict A
  have hmem2 : MemLp E (ENNReal.ofReal q) ρ :=
    MemLp.of_bound hE.aestronglyMeasurable.restrict 1 (hres (by
      filter_upwards [hE0, hEle] with v h0 h1
      rw [Real.norm_of_nonneg h0]
      exact h1))
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hc (hres hφ0) (hres hE0) hmem1 hmem2
  have e1 : ∫ v, φ v ^ (p : ℝ) ∂ρ = ∫ v in A, F v ∂P := integral_congr_ae (hres hφp)
  have e2 : ∫ v, E v ^ q ∂ρ = ∫ v in A, E v ∂P := by
    refine integral_congr_ae (hres ?_)
    filter_upwards [hE01] with v hv
    rcases hv with h | h
    · rw [h, Real.zero_rpow hq0.ne']
    · rw [h, Real.one_rpow]
  rw [e1, e2] at hH
  refine hH.trans ?_
  have ha : 0 ≤ P.real A := measureReal_nonneg
  have hF1 := setIntegral_le_of_invariantCondExp_le hF hFb hA
  have hE1 := setIntegral_le_of_invariantCondExp_le hE hEb hA
  have hFi : 0 ≤ ∫ v in A, F v ∂P := integral_nonneg_of_ae (hres hF0)
  have hEi : 0 ≤ ∫ v in A, E v ∂P := integral_nonneg_of_ae (hres hE0)
  have hp' : 0 ≤ 1 / (p : ℝ) := by positivity
  have hq' : 0 ≤ 1 / q := by positivity
  calc (∫ v in A, F v ∂P) ^ (1 / (p : ℝ)) * (∫ v in A, E v ∂P) ^ (1 / q)
      ≤ (G * P.real A) ^ (1 / (p : ℝ)) * (b * P.real A) ^ (1 / q) := by
        gcongr
    _ = G ^ (1 / (p : ℝ)) * b ^ (1 - 1 / (p : ℝ)) * P.real A := by
        rw [Real.mul_rpow hG ha, Real.mul_rpow hb ha, hqi]
        have e : P.real A ^ (1 / (p : ℝ)) * P.real A ^ (1 - 1 / (p : ℝ)) = P.real A := by
          rw [← Real.rpow_add_of_nonneg ha hp' (by rw [← hqi]; exact hq')]
          simp
        calc _ = G ^ (1 / (p : ℝ)) * b ^ (1 - 1 / (p : ℝ)) *
              (P.real A ^ (1 / (p : ℝ)) * P.real A ^ (1 - 1 / (p : ℝ))) := by ring
          _ = _ := by rw [e]
end
theorem invariantCondExp_band_bound : invariantCondExpBandBoundStatement := by
  intro J P _ Y e f p b G Bd hY hY0 he hf hp hb hG hes hfs hlim hsum hrel
  have key : ∀ A, MeasurableSet[shiftInvariantSigma J] A → ∫ v in A, Y v ∂P ≤ Bd * P.real A := by
    intro A hA
    have hAm : MeasurableSet A := shiftInvariantSigma_le_pi _ hA
    have ha : 0 ≤ P.real A := measureReal_nonneg
    have hband := fun (i M : ℕ) => setIntegral_rpow_mul_indicator_le hA (hp i) (hb i) (hG i) (hf i M).1 (hf i M).2
      (he i).1 (he i).2 (hfs i M) (hes i)
    have hmin : ∀ M : ℕ, Integrable (fun v => min (Y v) (M : ℝ)) P := fun M => hY.inf (integrable_const _)
    have hcut : ∀ (I M : ℕ), ∫ v in A, min (Y v) (M : ℝ) ∂P ≤ ((M : ℝ) * b I + Bd) * P.real A := by
      intro I M
      have hae : ∀ᵐ v ∂P, min (Y v) (M : ℝ) ≤ (M : ℝ) * e I v +
          ∑ i ∈ Finset.range I, f i (M ^ p i) v ^ (1 / (p i : ℝ)) * e i v := by
        have hnn : ∀ᵐ v ∂P, ∀ i, 0 ≤ f i (M ^ p i) v ^ (1 / (p i : ℝ)) * e i v :=
          ae_all_iff.2 fun i => (hband i (M ^ p i)).2.1
        filter_upwards [hrel I M, (he I).2, hnn] with v h1 h2 h3
        have h4 : 0 ≤ ∑ i ∈ Finset.range I, f i (M ^ p i) v ^ (1 / (p i : ℝ)) * e i v :=
          Finset.sum_nonneg fun i _ => h3 i
        rcases h2 with h | h
        · rw [h] at h1 ⊢
          simpa using h1
        · rw [h]
          have := min_le_right (Y v) (M : ℝ)
          linarith
      have hR : Integrable (fun v => (M : ℝ) * e I v +
          ∑ i ∈ Finset.range I, f i (M ^ p i) v ^ (1 / (p i : ℝ)) * e i v) P :=
        ((he I).1.const_mul _).add (integrable_finset_sum _ fun i _ => (hband i (M ^ p i)).1)
      have h1 : ∫ v in A, min (Y v) (M : ℝ) ∂P ≤ ∫ v in A, ((M : ℝ) * e I v +
          ∑ i ∈ Finset.range I, f i (M ^ p i) v ^ (1 / (p i : ℝ)) * e i v) ∂P :=
        setIntegral_mono_ae (hmin M).integrableOn hR.integrableOn hae
      refine h1.trans ?_
      rw [integral_add ((he I).1.const_mul _).integrableOn
          (integrable_finset_sum _ fun i _ => (hband i (M ^ p i)).1).integrableOn,
        integral_const_mul, integral_finset_sum _ fun i _ => (hband i (M ^ p i)).1.integrableOn]
      have h2 : ∫ v in A, e I v ∂P ≤ b I * P.real A := setIntegral_le_of_invariantCondExp_le (he I).1 (hes I) hA
      have h3 : ∑ i ∈ Finset.range I, ∫ v in A, f i (M ^ p i) v ^ (1 / (p i : ℝ)) * e i v ∂P ≤
          ∑ i ∈ Finset.range I, G i ^ (1 / (p i : ℝ)) * b i ^ (1 - 1 / (p i : ℝ)) * P.real A :=
        Finset.sum_le_sum fun i _ => (hband i (M ^ p i)).2.2
      rw [← Finset.sum_mul] at h3
      have h4 := mul_le_mul_of_nonneg_right (hsum I) ha
      have h5 : (M : ℝ) * ∫ v in A, e I v ∂P ≤ (M : ℝ) * (b I * P.real A) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg M)
      nlinarith
    have hcut' : ∀ M : ℕ, ∫ v in A, min (Y v) (M : ℝ) ∂P ≤ Bd * P.real A := by
      intro M
      have ht : Tendsto (fun I => ((M : ℝ) * b I + Bd) * P.real A) atTop (𝓝 (((M : ℝ) * 0 + Bd) * P.real A)) :=
        ((hlim.const_mul _).add_const _).mul_const _
      have h0 : ((M : ℝ) * 0 + Bd) * P.real A = Bd * P.real A := by ring
      rw [h0] at ht
      exact ge_of_tendsto' ht fun I => hcut I M
    have hconv : Tendsto (fun M : ℕ => ∫ v in A, min (Y v) (M : ℝ) ∂P) atTop (𝓝 (∫ v in A, Y v ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun v => |Y v|)
        (fun M => (hmin M).aestronglyMeasurable.restrict) hY.abs.integrableOn (fun M => ?_) ?_
      · refine ae_restrict_of_ae ?_
        filter_upwards [hY0] with v hv
        rw [Real.norm_of_nonneg (le_min hv (Nat.cast_nonneg M)), abs_of_nonneg hv]
        exact min_le_left _ _
      · refine Eventually.of_forall fun v => ?_
        obtain ⟨N, hN⟩ := exists_nat_ge (Y v)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with M hM
        have : Y v ≤ (M : ℝ) := hN.trans (by exact_mod_cast hM)
        rw [min_eq_left this]
    exact le_of_tendsto' hconv hcut'
  set Z : TranslateValues J → ℝ := invariantCondExp P Y with hZ
  have hZi : Integrable Z P := integrable_condExp
  have hZs : StronglyMeasurable[shiftInvariantSigma J] Z := stronglyMeasurable_condExp
  set A : Set (TranslateValues J) := {v | Bd < Z v} with hAd
  have hA : MeasurableSet[shiftInvariantSigma J] A := hZs.measurable measurableSet_Ioi
  have hAm : MeasurableSet A := shiftInvariantSigma_le_pi _ hA
  have h1 : ∫ v in A, Z v ∂P = ∫ v in A, Y v ∂P := setIntegral_condExp shiftInvariantSigma_le_pi hY hA
  have h2 : ∫ v in A, (Z v - Bd) ∂P ≤ 0 := by
    rw [integral_sub hZi.integrableOn (integrableOn_const (by simp)), h1, setIntegral_const, smul_eq_mul]
    have := key A hA
    linarith [mul_comm (P.real A) Bd]
  have h3 : 0 ≤ᵐ[P.restrict A] fun v => Z v - Bd := by
    refine (ae_restrict_iff' hAm).2 (Eventually.of_forall fun v hv => ?_)
    exact (sub_pos.2 hv).le
  have hint : Integrable (fun v => Z v - Bd) (P.restrict A) := hZi.integrableOn.sub (integrableOn_const (by simp))
  have h4 : ∫ v in A, (Z v - Bd) ∂P = 0 := le_antisymm h2 (integral_nonneg_of_ae h3)
  have h5 := (integral_eq_zero_iff_of_nonneg_ae h3 hint).1 h4
  have h6 : ∀ᵐ v ∂P, v ∈ A → Z v - Bd = 0 := (ae_restrict_iff' hAm).1 h5
  filter_upwards [h6] with v hv
  by_contra hcon
  have hvA : v ∈ A := not_le.1 hcon
  have := hv hvA
  linarith
end YangMills.Construction.MomentMethod
end
