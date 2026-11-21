import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureCarriedByThePyramid
import YangMills.Construction.EuclideanFunctionals.MeasuresAndOperatorsOfTheReconstruction
import YangMills.Construction.EuclideanFunctionals.OperatorsOfThePlaneSemigroupExpansionAndProductsOverTheWedge
import YangMills.Construction.EuclideanFunctionals.SemigroupOfTheCone
import YangMills.Construction.SpectralTheory.CalculusOfBoundedBorelFunctionsOnTheWholeSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ConeSemigroupProof
open BorelSpectral
open WholeSpaceSpectral
open BorelCalculus (IsBoundedFn conjFn)
open SpectralPoint
def pyramidSet : BorelSubsets (Fin 4 → ℝ) :=
  ⟨{x | ∀ j : Fin 3, |x j.succ| ≤ x 0}, by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le (measurable_pi_apply j.succ).abs (measurable_pi_apply 0)⟩
theorem zero_mem_pyramidSet : (0 : Fin 4 → ℝ) ∈ pyramidSet.1 := fun j => by simp
def expOnPyramid (z : Fin 4 → ℂ) (x : pyramidSet.1) : ℂ := coneExp z ⟨x.1, mem_univ _⟩
theorem continuous_expOnPyramid (z : Fin 4 → ℂ) : Continuous (expOnPyramid z) :=
  (continuous_coneExp z).comp (continuous_subtype_val.subtype_mk _)
def exponentCoeff (x : Fin 4 → ℝ) : Fin 4 → ℂ :=
  ![Complex.I * (x 1 : ℂ), Complex.I * (x 2 : ℂ), Complex.I * (x 3 : ℂ), -(x 0 : ℂ)]
theorem continuous_exponentCoeff (k : Fin 4) : Continuous fun x : Fin 4 → ℝ => exponentCoeff x k := by
  fin_cases k <;> simp only [exponentCoeff] <;> simp <;> fun_prop
theorem norm_exponentCoeff_le (x : pyramidSet.1) (k : Fin 4) : ‖exponentCoeff x.1 k‖ ≤ x.1 0 := by
  have hx := x.2
  have h1 : |x.1 1| ≤ x.1 0 := hx 0
  have h2 : |x.1 2| ≤ x.1 0 := hx 1
  have h3 : |x.1 3| ≤ x.1 0 := hx 2
  have h0 : 0 ≤ x.1 0 := (abs_nonneg _).trans h1
  fin_cases k <;> simp [exponentCoeff, abs_of_nonneg h0, h1, h2, h3]
theorem expOnPyramid_eq_exp (z : Fin 4 → ℂ) (x : pyramidSet.1) :
    expOnPyramid z x = Complex.exp (∑ k, z k * exponentCoeff x.1 k) := by
  simp only [expOnPyramid, coneExp, spatialComplex, SpectralPoint.energyOf,
    SpectralPoint.momentumOf]
  congr 1
  simp only [Fin.sum_univ_three, Fin.sum_univ_four, exponentCoeff]
  simp
  ring
theorem coneMargin_continuous : Continuous coneMargin := by
  unfold coneMargin spatialComplex
  fun_prop
theorem isClosed_coneMargin_nonneg : IsClosed {z : Fin 4 → ℂ | 0 ≤ coneMargin z} :=
  isClosed_le continuous_const coneMargin_continuous
theorem isOpen_coneMargin_pos : IsOpen {z : Fin 4 → ℂ | 0 < coneMargin z} :=
  isOpen_lt continuous_const coneMargin_continuous
theorem coneMargin_superadditive (z z' : Fin 4 → ℂ) :
    coneMargin z + coneMargin z' ≤ coneMargin (z + z') := by
  simp only [coneMargin, spatialComplex, Fin.sum_univ_three, Pi.add_apply, Complex.add_re,
    Complex.add_im]
  have h0 := abs_add_le (z (Fin.castSucc 0)).im (z' (Fin.castSucc 0)).im
  have h1 := abs_add_le (z (Fin.castSucc 1)).im (z' (Fin.castSucc 1)).im
  have h2 := abs_add_le (z (Fin.castSucc 2)).im (z' (Fin.castSucc 2)).im
  linarith
theorem coneMargin_sub_le_add (z w : Fin 4 → ℂ) :
    coneMargin z - ∑ k, ‖w k‖ ≤ coneMargin (z + w) := by
  simp only [coneMargin, spatialComplex, Fin.sum_univ_three, Fin.sum_univ_four, Pi.add_apply,
    Complex.add_re, Complex.add_im]
  have h3 : -‖w 3‖ ≤ (w 3).re := by
    have := Complex.abs_re_le_norm (w 3)
    linarith [neg_abs_le (w 3).re]
  have key : ∀ k : Fin 4, ∀ a : ℝ, |a + (w k).im| ≤ |a| + ‖w k‖ := fun k a =>
    (abs_add_le _ _).trans (by linarith [Complex.abs_im_le_norm (w k)])
  have h0 := key 0 (z (Fin.castSucc 0)).im
  have h1 := key 1 (z (Fin.castSucc 1)).im
  have h2 := key 2 (z (Fin.castSucc 2)).im
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at *
  have e2 : (Fin.castSucc (2 : Fin 3) : Fin 4) = 2 := rfl
  simp only [e2] at *
  linarith
section Calculus
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : SpectralMeasureOnSpace 4 H)
abbrev integralOpPyramid (φ : pyramidSet.1 → ℂ) : H →L[ℂ] H :=
  integralOpOver E pyramidSet φ
theorem zeroExtend_facts {φ : pyramidSet.1 → ℂ} (hφ : IsBoundedMeasurableFn φ) :
    IsBoundedMeasurableFn (zeroExtend pyramidSet.1 φ) ∧
      (fun x : pyramidSet.1 => zeroExtend pyramidSet.1 φ x) = φ := by
  obtain ⟨hm, b, hb⟩ := hφ
  refine ⟨⟨measurable_zeroExtend pyramidSet.2 hm, max b 0, fun x => ?_⟩, ?_⟩
  · by_cases h : x ∈ pyramidSet.1
    · simpa [zeroExtend, h] using Or.inl (hb ⟨x, h⟩)
    · simp [zeroExtend, h]
  · funext x
    simp [zeroExtend, x.2]
variable {E}
theorem norm_integralOpPyramid_le (hr : SupportLaws E pyramidSet) {φ : pyramidSet.1 → ℂ}
    (hm : Measurable φ) {b : ℝ} (hb : ∀ x, ‖φ x‖ ≤ b) : ‖integralOpPyramid E φ‖ ≤ b := by
  have hφ : IsBoundedMeasurableFn φ := ⟨hm, b, hb⟩
  obtain ⟨hF, hback⟩ := zeroExtend_facts hφ
  have h := hr.opNorm_le _ hF
  rw [hback] at h
  have : Nonempty pyramidSet.1 := ⟨⟨0, zero_mem_pyramidSet⟩⟩
  exact h.trans (ciSup_le fun x => (congrArg norm (congrFun hback x)).le.trans (hb x))
theorem integralOpPyramid_eq_integralOp (hr : SupportLaws E pyramidSet)
    {φ : pyramidSet.1 → ℂ} (hφ : IsBoundedMeasurableFn φ)
    {g : EMPoints → ℂ} (hg : IsBoundedMeasurableFn g)
    (h : ∀ x : pyramidSet.1, φ x = g ⟨x.1, mem_univ _⟩) :
    integralOpPyramid E φ = E.integralOp g := by
  obtain ⟨hF, hback⟩ := zeroExtend_facts hφ
  have hG : IsBoundedMeasurableFn fun y : Fin 4 → ℝ => g ⟨y, mem_univ y⟩ := by
    obtain ⟨hm, b, hb⟩ := hg
    exact ⟨hm.comp (measurable_id.subtype_mk), b, fun y => hb _⟩
  have h₁ := hr.eq_integralOpOver _ hF
  rw [hback] at h₁
  have h₂ := hr.congr _ _ hF hG (fun x hx => by
    have := congrFun hback ⟨x, hx⟩
    exact this.trans (h ⟨x, hx⟩))
  exact h₁.symm.trans h₂
theorem isBoundedMeasurableFn_add {φ χ : pyramidSet.1 → ℂ} (hφ : IsBoundedMeasurableFn φ)
    (hχ : IsBoundedMeasurableFn χ) : IsBoundedMeasurableFn (φ + χ) := by
  obtain ⟨hm, b, hb⟩ := hφ
  obtain ⟨hm', b', hb'⟩ := hχ
  exact ⟨hm.add hm', b + b', fun x => (norm_add_le _ _).trans (add_le_add (hb x) (hb' x))⟩
theorem isBoundedMeasurableFn_smul (c : ℂ) {φ : pyramidSet.1 → ℂ}
    (hφ : IsBoundedMeasurableFn φ) : IsBoundedMeasurableFn (c • φ) := by
  obtain ⟨hm, b, hb⟩ := hφ
  refine ⟨hm.const_smul c, ‖c‖ * b, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
theorem isBoundedMeasurableFn_one :
    IsBoundedMeasurableFn (fun _ : pyramidSet.1 => (1 : ℂ)) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem integralOpPyramid_sum (hr : SupportLaws E pyramidSet) {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (φ : ι → pyramidSet.1 → ℂ) (hφ : ∀ i, IsBoundedMeasurableFn (φ i)) :
    IsBoundedMeasurableFn (∑ i ∈ s, a i • φ i) ∧
      integralOpPyramid E (∑ i ∈ s, a i • φ i) = ∑ i ∈ s, a i • integralOpPyramid E (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (0 : pyramidSet.1 → ℂ) = (0 : ℂ) • fun _ => (1 : ℂ) := by simp
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_empty, h0]
      exact isBoundedMeasurableFn_smul 0 isBoundedMeasurableFn_one
    · rw [Finset.sum_empty, Finset.sum_empty, h0]
      have := hr.over_smul 0 _ isBoundedMeasurableFn_one
      simpa using this
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hi' := isBoundedMeasurableFn_smul (a i) (hφ i)
    refine ⟨isBoundedMeasurableFn_add hi' ih.1, ?_⟩
    have h2 := ih.2
    simp only [integralOpPyramid] at h2 ⊢
    rw [hr.over_add _ _ hi' ih.1, hr.over_smul _ _ (hφ i), h2]
theorem norm_expOnPyramid_le_one
    (hb : ∀ (z : Fin 4 → ℂ) (x : pyramidSet.1),
      ‖expOnPyramid z x‖ ≤ Real.exp (-(x.1 0 * coneMargin z)))
    {z : Fin 4 → ℂ} (hz : 0 ≤ coneMargin z) (x : pyramidSet.1) : ‖expOnPyramid z x‖ ≤ 1 := by
  have h0 : 0 ≤ x.1 0 := (abs_nonneg _).trans (x.2 0)
  refine (hb z x).trans ?_
  rw [Real.exp_le_one_iff]
  have := mul_nonneg h0 hz
  linarith
theorem integralOpPyramid_apply_eq_self (hr : SupportLaws E pyramidSet) {z : Fin 4 → ℂ}
    (hφ : IsBoundedMeasurableFn (expOnPyramid z)) {ψ : H}
    (hnull : E.diagMeasure ψ {p | SpectralPoint.energyOf p ≠ 0} = 0) :
    integralOpPyramid E (expOnPyramid z) ψ = ψ := by
  have hone := isBoundedMeasurableFn_smul (-1) isBoundedMeasurableFn_one
  have hχ := isBoundedMeasurableFn_add hφ hone
  obtain ⟨hF, hback⟩ := zeroExtend_facts hχ
  have h₁ := hr.norm_sq _ hF ψ
  rw [hback] at h₁
  have h₂ : ∫ y in (restrictToUniv pyramidSet).1,
      ‖zeroExtend pyramidSet.1 (expOnPyramid z + (-1 : ℂ) • fun _ => (1 : ℂ)) y.1‖ ^ 2
        ∂E.diagMeasure ψ = 0 := by
    apply integral_eq_zero_of_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' (restrictToUniv pyramidSet).2]
    have hae : ∀ᵐ y ∂E.diagMeasure ψ, SpectralPoint.energyOf y = 0 := by
      rw [ae_iff]
      exact hnull
    filter_upwards [hae] with y hy hmem
    have hmem' : y.1 ∈ pyramidSet.1 := hmem
    have h0 : y.1 0 = 0 := hy
    have hj : ∀ j : Fin 3, y.1 j.succ = 0 := fun j => by
      have := hmem' j
      rw [h0] at this
      exact abs_nonpos_iff.mp this
    have h1 : y.1 1 = 0 := hj 0
    have h2 : y.1 2 = 0 := hj 1
    have h3 : y.1 3 = 0 := hj 2
    have hv := congrFun hback ⟨y.1, hmem'⟩
    simp only at hv
    simp only [Pi.zero_apply]
    rw [hv]
    simp [expOnPyramid_eq_exp, exponentCoeff, h0, h1, h2, h3, Fin.sum_univ_four]
  rw [h₂] at h₁
  have h₃ : integralOpPyramid E (expOnPyramid z + (-1 : ℂ) • fun _ => (1 : ℂ)) ψ = 0 := by
    simpa using h₁
  simp only [integralOpPyramid] at h₃
  rw [hr.over_add _ _ hφ hone, hr.over_smul _ _ isBoundedMeasurableFn_one,
    hr.over_one] at h₃
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h₃)
theorem continuousOn_integralOpPyramid (hl : StrongConvergenceOver E pyramidSet)
    (hb : ∀ (z : Fin 4 → ℂ) (x : pyramidSet.1),
      ‖expOnPyramid z x‖ ≤ Real.exp (-(x.1 0 * coneMargin z))) (ψ : H) :
    ContinuousOn (fun z => integralOpPyramid E (expOnPyramid z) ψ)
      {z : Fin 4 → ℂ | 0 ≤ coneMargin z} := by
  intro z₀ _
  refine tendsto_of_seq_tendsto fun u hu => ?_
  obtain ⟨hu₁, hu₂⟩ := tendsto_nhdsWithin_iff.mp hu
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu₂
  have hlim : Tendsto (fun r => u (r + N)) atTop (𝓝 z₀) := (tendsto_add_atTop_iff_nat N).2 hu₁
  have h := hl (fun r => expOnPyramid (u (r + N))) (expOnPyramid z₀)
    (fun r _ => (continuous_expOnPyramid _).measurable)
    ⟨1, fun r _ x => norm_expOnPyramid_le_one hb (hN _ (by omega)) x⟩
    (fun x => by
      have hc : Continuous fun z => expOnPyramid z x := by
        simp only [expOnPyramid_eq_exp]
        fun_prop
      exact (hc.tendsto z₀).comp hlim) ψ
  exact (tendsto_add_atTop_iff_nat N).1 h
end Calculus
section Multinomial
theorem sum_piAntidiag_monomial {K : Type*} [Field K] [CharZero K] (y : Fin 4 → K) (n : ℕ) :
    ∑ γ ∈ Finset.piAntidiag Finset.univ n,
        ((PowerSeries.MultiIndex.factorial γ : ℕ) : K)⁻¹ * PowerSeries.MultiIndex.monomial y γ =
      (∑ k, y k) ^ n / (n.factorial : K) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_div]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  have hs : ∑ i, γ i = n := (Finset.mem_piAntidiag.mp hγ).1
  have spec : PowerSeries.MultiIndex.factorial γ * Nat.multinomial Finset.univ γ = n.factorial := by
    have := Nat.multinomial_spec Finset.univ γ
    rw [hs] at this
    exact this
  have hc : ((PowerSeries.MultiIndex.factorial γ : ℕ) : K) * (Nat.multinomial Finset.univ γ : K) =
      (n.factorial : K) := by
    exact_mod_cast spec
  have hn : (n.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hf : ((PowerSeries.MultiIndex.factorial γ : ℕ) : K) ≠ 0 :=
    fun h => hn (by rw [← hc, h, zero_mul])
  have hm : (Nat.multinomial Finset.univ γ : K) ≠ 0 := fun h => hn (by rw [← hc, h, mul_zero])
  rw [← hc, PowerSeries.MultiIndex.monomial]
  field_simp
def orderLE (N : ℕ) : Finset (PowerSeries.MultiIndex 4) :=
  (Finset.range (N + 1)).biUnion fun n => Finset.piAntidiag Finset.univ n
theorem sum_orderLE {M : Type*} [AddCommMonoid M] (f : PowerSeries.MultiIndex 4 → M) (N : ℕ) :
    ∑ γ ∈ orderLE N, f γ =
      ∑ n ∈ Finset.range (N + 1), ∑ γ ∈ Finset.piAntidiag Finset.univ n, f γ := by
  refine Finset.sum_biUnion fun a _ b _ hab => ?_
  refine Finset.disjoint_left.mpr fun γ ha hb => hab ?_
  exact (Finset.mem_piAntidiag.mp ha).1.symm.trans (Finset.mem_piAntidiag.mp hb).1
theorem mem_orderLE (γ : PowerSeries.MultiIndex 4) {N : ℕ}
    (h : PowerSeries.MultiIndex.order γ ≤ N) : γ ∈ orderLE N :=
  Finset.mem_biUnion.mpr ⟨PowerSeries.MultiIndex.order γ, Finset.mem_range.mpr (by omega),
    Finset.mem_piAntidiag.mpr ⟨rfl, fun _ _ => Finset.mem_univ _⟩⟩
theorem tendsto_orderLE : Tendsto orderLE atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun a b hab γ hγ => ?_)
    fun γ => ⟨PowerSeries.MultiIndex.order γ, mem_orderLE γ le_rfl⟩
  obtain ⟨n, hn, h⟩ := Finset.mem_biUnion.mp hγ
  exact Finset.mem_biUnion.mpr
    ⟨n, Finset.mem_range.mpr (by have := Finset.mem_range.mp hn; omega), h⟩
def multinomialTerm (y : Fin 4 → ℝ) (γ : PowerSeries.MultiIndex 4) : ℝ :=
  ((PowerSeries.MultiIndex.order γ).factorial : ℝ) *
    (((PowerSeries.MultiIndex.factorial γ : ℕ) : ℝ)⁻¹ * PowerSeries.MultiIndex.monomial y γ)
theorem sum_multinomialTerm (y : Fin 4 → ℝ) (n : ℕ) :
    ∑ γ ∈ Finset.piAntidiag Finset.univ n, multinomialTerm y γ = (∑ k, y k) ^ n := by
  have h : ∀ γ ∈ Finset.piAntidiag Finset.univ n, multinomialTerm y γ =
      (n.factorial : ℝ) * (((PowerSeries.MultiIndex.factorial γ : ℕ) : ℝ)⁻¹ *
        PowerSeries.MultiIndex.monomial y γ) := by
    intro γ hγ
    have hs : PowerSeries.MultiIndex.order γ = n := (Finset.mem_piAntidiag.mp hγ).1
    rw [multinomialTerm, hs]
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, sum_piAntidiag_monomial]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
theorem summable_multinomialTerm (y : Fin 4 → ℝ) (hy : ∀ k, 0 ≤ y k) (h1 : ∑ k, y k < 1) :
    Summable (multinomialTerm y) ∧
      ∀ N, ∑ γ ∈ orderLE N, multinomialTerm y γ ≤ (1 - ∑ k, y k)⁻¹ := by
  have ha : 0 ≤ ∑ k, y k := Finset.sum_nonneg fun k _ => hy k
  have hnn : ∀ γ, 0 ≤ multinomialTerm y γ := fun γ =>
    mul_nonneg (by positivity) (mul_nonneg (by positivity)
      (Finset.prod_nonneg fun k _ => pow_nonneg (hy k) _))
  have hle : ∀ N, ∑ γ ∈ orderLE N, multinomialTerm y γ ≤ (1 - ∑ k, y k)⁻¹ := fun N => by
    rw [sum_orderLE]
    simp only [sum_multinomialTerm]
    rw [← tsum_geometric_of_lt_one ha h1]
    exact (summable_geometric_of_lt_one ha h1).sum_le_tsum _ fun _ _ => pow_nonneg ha _
  refine ⟨summable_of_sum_le hnn (c := (1 - ∑ k, y k)⁻¹) fun u => ?_, hle⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun γ hγ => ?_) fun γ _ _ => hnn γ)
    (hle (u.sup PowerSeries.MultiIndex.order))
  exact mem_orderLE γ (Finset.le_sup (f := PowerSeries.MultiIndex.order) hγ)
theorem pow_mul_exp_neg_le {d s : ℝ} (hd : 0 < d) (hs : 0 ≤ s) (n : ℕ) :
    s ^ n * Real.exp (-(s * d)) ≤ (n.factorial : ℝ) * (d ^ n)⁻¹ := by
  have h := Real.pow_div_factorial_le_exp (s * d) (by positivity) n
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  have he := Real.exp_pos (s * d)
  have hdn : 0 < d ^ n := pow_pos hd n
  rw [Real.exp_neg, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ he hdn]
  linarith
theorem norm_monomial (y : Fin 4 → ℂ) (γ : PowerSeries.MultiIndex 4) :
    ‖PowerSeries.MultiIndex.monomial y γ‖ =
      PowerSeries.MultiIndex.monomial (fun k => ‖y k‖) γ := by
  simp [PowerSeries.MultiIndex.monomial, norm_prod]
theorem norm_monomial_mul_bound (w : Fin 4 → ℂ) (d : ℝ) (γ : PowerSeries.MultiIndex 4) :
    ‖PowerSeries.MultiIndex.monomial w γ‖ * (((PowerSeries.MultiIndex.order γ).factorial : ℝ) *
        (d ^ PowerSeries.MultiIndex.order γ)⁻¹ / ((PowerSeries.MultiIndex.factorial γ : ℕ) : ℝ)) =
      multinomialTerm (fun k => ‖w k‖ / d) γ := by
  have h : PowerSeries.MultiIndex.monomial (fun k => ‖w k‖ / d) γ =
      PowerSeries.MultiIndex.monomial (fun k => ‖w k‖) γ / d ^ PowerSeries.MultiIndex.order γ := by
    simp only [PowerSeries.MultiIndex.monomial, PowerSeries.MultiIndex.order, div_pow,
      Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [multinomialTerm, h, norm_monomial]
  simp only [div_eq_mul_inv]
  ring
theorem monomial_mul (y y' : Fin 4 → ℂ) (γ : PowerSeries.MultiIndex 4) :
    PowerSeries.MultiIndex.monomial (fun k => y k * y' k) γ =
      PowerSeries.MultiIndex.monomial y γ * PowerSeries.MultiIndex.monomial y' γ := by
  simp only [PowerSeries.MultiIndex.monomial, mul_pow, Finset.prod_mul_distrib]
end Multinomial
section Series
def seriesCoeff (z₀ : Fin 4 → ℂ) (γ : PowerSeries.MultiIndex 4) (x : pyramidSet.1) : ℂ :=
  ((PowerSeries.MultiIndex.factorial γ : ℕ) : ℂ)⁻¹ *
    (PowerSeries.MultiIndex.monomial (exponentCoeff x.1) γ * expOnPyramid z₀ x)
theorem continuous_seriesCoeff (z₀ : Fin 4 → ℂ) (γ : PowerSeries.MultiIndex 4) :
    Continuous (seriesCoeff z₀ γ) :=
  continuous_const.mul ((continuous_finsetProd _ fun k _ =>
    ((continuous_exponentCoeff k).comp continuous_subtype_val).pow _).mul
      (continuous_expOnPyramid z₀))
theorem norm_seriesCoeff_le {z₀ : Fin 4 → ℂ} (hd : 0 < coneMargin z₀)
    (hb : ∀ (z : Fin 4 → ℂ) (x : pyramidSet.1),
      ‖expOnPyramid z x‖ ≤ Real.exp (-(x.1 0 * coneMargin z)))
    (γ : PowerSeries.MultiIndex 4) (x : pyramidSet.1) :
    ‖seriesCoeff z₀ γ x‖ ≤ ((PowerSeries.MultiIndex.order γ).factorial : ℝ) *
      (coneMargin z₀ ^ PowerSeries.MultiIndex.order γ)⁻¹ /
        ((PowerSeries.MultiIndex.factorial γ : ℕ) : ℝ) := by
  have h0 : 0 ≤ x.1 0 := (abs_nonneg _).trans (x.2 0)
  have hpow : ‖PowerSeries.MultiIndex.monomial (exponentCoeff x.1) γ‖ ≤
      x.1 0 ^ PowerSeries.MultiIndex.order γ := by
    rw [norm_monomial, PowerSeries.MultiIndex.monomial, PowerSeries.MultiIndex.order,
      ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun k _ => by positivity)
      fun k _ => pow_le_pow_left₀ (norm_nonneg _) (norm_exponentCoeff_le x k) _
  have hmain : ‖PowerSeries.MultiIndex.monomial (exponentCoeff x.1) γ * expOnPyramid z₀ x‖ ≤
      ((PowerSeries.MultiIndex.order γ).factorial : ℝ) *
        (coneMargin z₀ ^ PowerSeries.MultiIndex.order γ)⁻¹ := by
    rw [norm_mul]
    exact (mul_le_mul hpow (hb z₀ x) (norm_nonneg _) (by positivity)).trans
      (pow_mul_exp_neg_le hd h0 _)
  rw [seriesCoeff, norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : SpectralMeasureOnSpace 4 H}
theorem hasSum_seriesAt (hr : SupportLaws E pyramidSet) (hl : StrongConvergenceOver E pyramidSet)
    (hb : ∀ (z : Fin 4 → ℂ) (x : pyramidSet.1),
      ‖expOnPyramid z x‖ ≤ Real.exp (-(x.1 0 * coneMargin z)))
    {z₀ : Fin 4 → ℂ} (hd : 0 < coneMargin z₀) {w : Fin 4 → ℂ}
    (hw : ∑ k, ‖w k‖ < coneMargin z₀) :
    Summable (fun γ => ‖PowerSeries.MultiIndex.monomial w γ •
        integralOpPyramid E (seriesCoeff z₀ γ)‖) ∧
      HasSum (fun γ => PowerSeries.MultiIndex.monomial w γ •
          integralOpPyramid E (seriesCoeff z₀ γ))
        (integralOpPyramid E (expOnPyramid (z₀ + w))) := by
  have hsum : ∑ k, ‖w k‖ / coneMargin z₀ < 1 := by
    rw [← Finset.sum_div, div_lt_one hd]
    exact hw
  obtain ⟨hsm, hle⟩ := summable_multinomialTerm (fun k => ‖w k‖ / coneMargin z₀)
    (fun k => by positivity) hsum
  have hop : ∀ γ, ‖PowerSeries.MultiIndex.monomial w γ • integralOpPyramid E (seriesCoeff z₀ γ)‖ ≤
      multinomialTerm (fun k => ‖w k‖ / coneMargin z₀) γ := fun γ => by
    rw [norm_smul, ← norm_monomial_mul_bound]
    exact mul_le_mul_of_nonneg_left (norm_integralOpPyramid_le hr
      (continuous_seriesCoeff z₀ γ).measurable (norm_seriesCoeff_le hd hb γ)) (norm_nonneg _)
  have hS : Summable fun γ =>
      ‖PowerSeries.MultiIndex.monomial w γ • integralOpPyramid E (seriesCoeff z₀ γ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hop hsm
  have hS' := hS.of_norm
  refine ⟨hS, ?_⟩
  have hlim := hS'.hasSum.comp tendsto_orderLE
  have hbb : ∀ γ, IsBoundedMeasurableFn (seriesCoeff z₀ γ) := fun γ =>
    ⟨(continuous_seriesCoeff z₀ γ).measurable, _, norm_seriesCoeff_le hd hb γ⟩
  have hfs := fun N => integralOpPyramid_sum hr (orderLE N) (PowerSeries.MultiIndex.monomial w)
    (seriesCoeff z₀) hbb
  have hbound : ∀ (N : ℕ) (x : pyramidSet.1),
      ‖(∑ γ ∈ orderLE N, PowerSeries.MultiIndex.monomial w γ • seriesCoeff z₀ γ) x‖ ≤
        (1 - ∑ k, ‖w k‖ / coneMargin z₀)⁻¹ := fun N x => by
    rw [Finset.sum_apply]
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun γ _ => ?_) (hle N))
    rw [Pi.smul_apply, norm_smul, ← norm_monomial_mul_bound]
    exact mul_le_mul_of_nonneg_left (norm_seriesCoeff_le hd hb γ x) (norm_nonneg _)
  have hptw : ∀ x : pyramidSet.1,
      Tendsto (fun N => (∑ γ ∈ orderLE N, PowerSeries.MultiIndex.monomial w γ •
          seriesCoeff z₀ γ) x) atTop
        (𝓝 (expOnPyramid (z₀ + w) x)) := fun x => by
    have hexp : HasSum (fun n : ℕ => (∑ k, w k * exponentCoeff x.1 k) ^ n / (n.factorial : ℂ))
        (Complex.exp (∑ k, w k * exponentCoeff x.1 k)) := by
      rw [Complex.exp_eq_exp_ℂ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    have hpart := (tendsto_add_atTop_iff_nat 1).2 hexp.tendsto_sum_nat
    have hval : expOnPyramid (z₀ + w) x =
        expOnPyramid z₀ x * Complex.exp (∑ k, w k * exponentCoeff x.1 k) := by
      simp only [expOnPyramid_eq_exp, ← Complex.exp_add, ← Finset.sum_add_distrib, Pi.add_apply,
        add_mul]
    rw [hval]
    refine (hpart.const_mul (expOnPyramid z₀ x)).congr fun N => ?_
    rw [Finset.sum_apply, sum_orderLE, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← sum_piAntidiag_monomial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [monomial_mul, Pi.smul_apply, smul_eq_mul, seriesCoeff]
    ring
  have hstrong := hl (fun N => ∑ γ ∈ orderLE N, PowerSeries.MultiIndex.monomial w γ •
      seriesCoeff z₀ γ)
    (expOnPyramid (z₀ + w)) (fun N _ => (hfs N).1.1) ⟨_, fun N _ x => hbound N x⟩ hptw
  have heq : (∑' γ, PowerSeries.MultiIndex.monomial w γ • integralOpPyramid E (seriesCoeff z₀ γ)) =
      integralOpPyramid E (expOnPyramid (z₀ + w)) := by
    refine ContinuousLinearMap.ext fun ψ => ?_
    have h2 := ((ContinuousLinearMap.apply ℂ H ψ).continuous.tendsto _).comp hlim
    refine tendsto_nhds_unique (h2.congr fun N => ?_) (hstrong ψ)
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply]
    exact congrArg (fun T : H →L[ℂ] H => T ψ) (hfs N).2.symm
  rw [← heq]
  exact hS'.hasSum
theorem exists_seriesAt (hr : SupportLaws E pyramidSet)
    (hl : StrongConvergenceOver E pyramidSet)
    (hb : ∀ (z : Fin 4 → ℂ) (x : pyramidSet.1),
      ‖expOnPyramid z x‖ ≤ Real.exp (-(x.1 0 * coneMargin z)))
    {z₀ : Fin 4 → ℂ} (hd : 0 < coneMargin z₀) :
    ∃ A : PowerSeries.MultiIndex 4 → H →L[ℂ] H,
      (∀ γ, ‖A γ‖ ≤ ((PowerSeries.MultiIndex.order γ).factorial : ℝ) *
        (coneMargin z₀ ^ PowerSeries.MultiIndex.order γ)⁻¹ /
          ((PowerSeries.MultiIndex.factorial γ : ℕ) : ℝ)) ∧
      ∀ w : Fin 4 → ℂ, ∑ k, ‖w k‖ < coneMargin z₀ →
        0 < coneMargin (z₀ + w) ∧
        Summable (fun γ => ‖PowerSeries.MultiIndex.monomial w γ • A γ‖) ∧
        HasSum (fun γ => PowerSeries.MultiIndex.monomial w γ • A γ)
          (integralOpPyramid E (expOnPyramid (z₀ + w))) := by
  refine ⟨fun γ => integralOpPyramid E (seriesCoeff z₀ γ), fun γ => norm_integralOpPyramid_le hr
    (continuous_seriesCoeff z₀ γ).measurable (norm_seriesCoeff_le hd hb γ), fun w hw => ?_⟩
  obtain ⟨h₁, h₂⟩ := hasSum_seriesAt hr hl hb hd hw
  exact ⟨by linarith [coneMargin_sub_le_add z₀ w], h₁, h₂⟩
theorem isOperatorHolomorphicOn_integralOpPyramid (hr : SupportLaws E pyramidSet)
    (hl : StrongConvergenceOver E pyramidSet)
    (hb : ∀ (z : Fin 4 → ℂ) (x : pyramidSet.1),
      ‖expOnPyramid z x‖ ≤ Real.exp (-(x.1 0 * coneMargin z))) :
    BanachValued.IsOperatorHolomorphicOn (n := 4) {z : Fin 4 → ℂ | 0 < coneMargin z}
      (fun z => integralOpPyramid E (expOnPyramid z)) := by
  refine ⟨isOpen_coneMargin_pos, Or.inl ⟨by norm_num, fun c hc => ?_⟩⟩
  have hc' : 0 < coneMargin c := hc
  obtain ⟨A, -, hA⟩ := exists_seriesAt hr hl hb hc'
  have hρ : 0 < coneMargin c / 5 := by positivity
  have hnorm : ∀ w : Coordinates.ComplexCoordinates 4, ‖w‖ ≤ coneMargin c / 5 →
      ∑ k, ‖w k‖ < coneMargin c := by
    intro w hw
    have hk : ∀ k, ‖w k‖ ≤ coneMargin c / 5 := fun k => (norm_le_pi_norm w k).trans hw
    rw [Fin.sum_univ_four]
    linarith [hk 0, hk 1, hk 2, hk 3]
  refine ⟨coneMargin c / 5, A, hρ, fun z hz => ?_, ?_, fun w hw => (hA w (hnorm w hw)).2.2⟩
  · have := (hA (z - c) (hnorm _ hz)).1
    rw [add_sub_cancel] at this
    exact this
  · have hw : ∑ k : Fin 4, ‖(fun _ => ((coneMargin c / 5 : ℝ) : ℂ)) k‖ < coneMargin c := by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      linarith
    refine (hA _ hw).2.1.congr fun γ => ?_
    rw [norm_smul, norm_monomial, mul_comm]
    simp only [PowerSeries.MultiIndex.monomial, PowerSeries.MultiIndex.order, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ, Finset.prod_pow_eq_pow_sum]
end Series
section Points
theorem reflectConj_last (z : Fin 4 → ℂ) : reflectConj z 3 = conj (z 3) :=
  Fin.snoc_last (α := fun _ => ℂ) _ _
theorem reflectConj_castSucc (z : Fin 4 → ℂ) (j : Fin 3) :
    reflectConj z j.castSucc = -conj (z j.castSucc) := by
  simp [reflectConj, spatialComplex]
theorem coneMargin_reflectConj (z : Fin 4 → ℂ) : coneMargin (reflectConj z) = coneMargin z := by
  simp only [coneMargin, spatialComplex, reflectConj_last, reflectConj_castSucc]
  simp
theorem conjFn_expOnPyramid (z : Fin 4 → ℂ) :
    conjFn (expOnPyramid z) = expOnPyramid (reflectConj z) := by
  funext x
  simp only [conjFn, expOnPyramid, coneExp, spatialComplex, reflectConj_last,
    reflectConj_castSucc]
  rw [← Complex.exp_conj]
  congr 1
  simp [Finset.mul_sum, Complex.conj_ofReal]
theorem expOnPyramid_mul (z z' : Fin 4 → ℂ) :
    expOnPyramid z * expOnPyramid z' = expOnPyramid (z + z') := by
  funext x
  simp only [Pi.mul_apply, expOnPyramid_eq_exp, ← Complex.exp_add, ← Finset.sum_add_distrib,
    Pi.add_apply, add_mul]
theorem coneMargin_ofRealPoint (x : R4) : coneMargin (ofRealPoint x) = x 3 := by
  simp [coneMargin, spatialComplex, ofRealPoint]
theorem coneMargin_planeEmbed (v : ℂ × ℂ) :
    coneMargin (planeEmbed v) = v.1.re - |v.2.im| := by
  simp [coneMargin, spatialComplex, planeEmbed, Fin.sum_univ_three]
theorem coneMargin_planeEmbed_nonneg_iff (v : ℂ × ℂ) :
    0 ≤ coneMargin (planeEmbed v) ↔ v ∈ ForwardTube.closedForwardTube := by
  change _ ↔ (ForwardTube.lightConePlus v).re ≥ 0 ∧ (ForwardTube.lightConeMinus v).re ≥ 0
  have hp : (ForwardTube.lightConePlus v).re = v.1.re - v.2.im := by
    simp [ForwardTube.lightConePlus, sub_eq_add_neg]
  have hm : (ForwardTube.lightConeMinus v).re = v.1.re + v.2.im := by
    simp [ForwardTube.lightConeMinus]
  rw [coneMargin_planeEmbed, hp, hm, sub_nonneg, abs_le]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨a, b⟩
    exact ⟨by linarith, by linarith⟩
theorem coneExp_planeEmbed (v : ℂ × ℂ) (p : EMPoints) :
    coneExp (planeEmbed v) p =
      Complex.exp (-(v.1 * (SpectralPoint.energyOf p : ℂ)) +
        Complex.I * v.2 * (SpectralPoint.momentumOf p 0 : ℂ)) := by
  simp [coneExp, spatialComplex, planeEmbed, Fin.sum_univ_three, mul_assoc]
end Points
section Functional
open BorelSpectral.SpectralMeasure
open EuclidFunctionalWithRecon
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
theorem coneOp_ofRealPoint (hr : SupportLaws σ.jointMeasure pyramidSet)
    (hφ : ∀ x : R4, 0 ≤ x 3 → IsBoundedMeasurableFn (expOnPyramid (ofRealPoint x)))
    (hT : σ.LaplaceFourierRep) (x : R4) (hx : 0 ≤ x 3) :
    σ.coneOp (ofRealPoint x) =
      σ.heatSemigroup (x 3) * σ.spatialShiftOp fun j => x j.castSucc := by
  have ht := (hT (x 3) hx fun j => x j.castSucc).1
  have hfun : laplaceFourierKernel (x 3) (spatialEmbed fun j => x j.castSucc) =
      fun p : SpectralPoint.nonnegEnergy.1 => coneExp (ofRealPoint x) p.1 := by
    funext p
    simp only [laplaceFourierKernel, coneExp, spatialComplex, ofRealPoint, dotR4,
      dot3, spatialEmbed, Fin.snoc_castSucc]
    push_cast
    ring_nf
  have hcont : Continuous fun p : SpectralPoint.nonnegEnergy.1 =>
      coneExp (ofRealPoint x) p.1 :=
    (continuous_coneExp _).comp continuous_subtype_val
  have hle : ∀ p : SpectralPoint.nonnegEnergy.1,
      ‖laplaceFourierKernel (x 3) (spatialEmbed fun j => x j.castSucc) p‖ ≤ 1 := fun p => by
    have hE : 0 ≤ SpectralPoint.energyOf p.1 := p.2
    rw [laplaceFourierKernel, Complex.norm_exp, Real.exp_le_one_iff]
    have := mul_nonneg hx hE
    simpa using this
  have hg : IsBoundedMeasurableFn (zeroExtend SpectralPoint.nonnegEnergy.1
      (laplaceFourierKernel (x 3) (spatialEmbed fun j => x j.castSucc))) := by
    refine ⟨measurable_zeroExtend SpectralPoint.nonnegEnergy.2
      (by rw [hfun]; exact hcont.measurable), 1, fun y => ?_⟩
    by_cases h : y ∈ SpectralPoint.nonnegEnergy.1
    · simpa [zeroExtend, h] using hle ⟨y, h⟩
    · simp [zeroExtend, h]
  have h₂ := integralOpPyramid_eq_integralOp hr (hφ x hx) hg (fun y => by
    have hy : (⟨y.1, mem_univ _⟩ : EMPoints) ∈ SpectralPoint.nonnegEnergy.1 :=
      (abs_nonneg _).trans (y.2 0)
    simp only [zeroExtend]
    rw [dif_pos hy, hfun]
    rfl)
  exact h₂.trans ht.symm
theorem coneOp_planeEmbed (hr : SupportLaws σ.jointMeasure pyramidSet)
    (hMeas : σ.MeasureFacts)
    (hW : ∀ p ∈ wedge.1, ∀ v ∈ ForwardTube.closedForwardTube, ‖planeExpKernel v p‖ ≤ 1)
    {v : ℂ × ℂ} (hv : v ∈ ForwardTube.closedForwardTube)
    (hφ : IsBoundedMeasurableFn (expOnPyramid (planeEmbed v))) :
    σ.coneOp (planeEmbed v) = σ.wedgeIntegralOp v := by
  have hcont : Continuous fun p : wedge.1 => planeExpKernel v p.1 := by
    have h : ∀ i : Fin 2, Continuous fun p : wedge.1 => ((p.1.1 i : ℝ) : ℂ) := fun i =>
      Complex.continuous_ofReal.comp
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val))
    exact Complex.continuous_exp.comp
      (((continuous_const.mul (h 0)).neg).add (continuous_const.mul (h 1)))
  have hfm : Measurable (zeroExtend wedge.1 fun p : wedge.1 => planeExpKernel v p.1) :=
    measurable_zeroExtend wedge.2 hcont.measurable
  have hfb : ∀ y, ‖zeroExtend wedge.1 (fun p : wedge.1 => planeExpKernel v p.1) y‖ ≤ 1 := by
    intro y
    by_cases h : y ∈ wedge.1
    · simpa [zeroExtend, h] using hW y h v hv
    · simp [zeroExtend, h]
  have h₁ := hMeas.planeIntegralOp_eq _ hfm ⟨1, hfb⟩
  have hg : IsBoundedMeasurableFn
      ((zeroExtend wedge.1 fun p : wedge.1 => planeExpKernel v p.1) ∘
        energyMomentumPlane) :=
    ⟨hfm.comp measurable_energyMomentumPlane, 1, fun y => hfb _⟩
  have h₂ := integralOpPyramid_eq_integralOp hr hφ hg (fun y => by
    have hy : energyMomentumPlane ⟨y.1, mem_univ _⟩ ∈ wedge.1 := y.2 0
    simp only [Function.comp_apply, zeroExtend]
    rw [dif_pos hy, expOnPyramid, coneExp_planeEmbed]
    simp [planeExpKernel, energyMomentumPlane])
  exact h₂.trans h₁.symm
end Functional
theorem coneSemigroup_holds (hCalc : WholeSpaceCalculus.BoundedCalculusTheorem)
    (hPyr : EuclidFunctionalWithRecon.CarriedByPyramid.statement)
    (hLink : ReconstructionMeasureOperatorFacts)
    (hPlane : TubeSemigroup.Holds) : ConeSemigroup.statement := by
  intro c S σ hcone
  have hp := hPyr σ hcone
  have hcalc := hCalc σ.space 4 σ.jointMeasure
  have hcarried : IsSupportedOn σ.jointMeasure pyramidSet := hp.2.1
  obtain ⟨hr, hl⟩ := hcalc.2.1 pyramidSet hcarried
  have hb : ∀ (z : Fin 4 → ℂ) (x : pyramidSet.1),
      ‖expOnPyramid z x‖ ≤ Real.exp (-(x.1 0 * coneMargin z)) := fun z x => by
    have h := hp.2.2.2 ⟨x.1, mem_univ _⟩ x.2 z
    exact h.1.le.trans h.2.1
  have hbb : ∀ z, 0 ≤ coneMargin z → IsBoundedMeasurableFn (expOnPyramid z) := fun z hz =>
    ⟨(continuous_expOnPyramid z).measurable, 1, norm_expOnPyramid_le_one hb hz⟩
  obtain ⟨hMeas, -, hTrans, hVac, hCls, -⟩ := hLink c S σ
  have hBdd := (hPlane c S σ hcone).1
  have hreal := coneOp_ofRealPoint σ hr (fun x hx => hbb _
    (by rw [coneMargin_ofRealPoint]; exact hx)) hTrans
  refine ⟨fun z hz => ?_, fun z z' hz hz' => ?_, fun z hz => ?_, fun z hz => ?_, fun x hx => ?_,
    isClosed_coneMargin_nonneg, continuousOn_integralOpPyramid hl hb,
    fun z₀ hz₀ => exists_seriesAt hr hl hb hz₀,
    isOpen_coneMargin_pos, isOperatorHolomorphicOn_integralOpPyramid hr hl hb, fun v => ?_⟩
  · exact norm_integralOpPyramid_le hr (continuous_expOnPyramid z).measurable
      (norm_expOnPyramid_le_one hb hz)
  · refine ⟨by linarith [coneMargin_superadditive z z'], ?_⟩
    have h := hr.over_mul _ _ (hbb z hz) (hbb z' hz')
    rw [expOnPyramid_mul] at h
    exact h.symm
  · refine ⟨coneMargin_reflectConj z, by rw [coneMargin_reflectConj]; exact hz, ?_⟩
    have h := hr.over_conj _ (hbb z hz)
    rw [conjFn_expOnPyramid] at h
    exact h.symm
  · exact integralOpPyramid_apply_eq_self hr (hbb z hz) hVac.2.2
  · refine ⟨coneMargin_ofRealPoint x,
      by rw [coneMargin_ofRealPoint]; exact hx, hreal x hx, fun F => ?_⟩
    obtain ⟨hmem, hcl⟩ := hCls x hx F
    rw [hreal x hx, readClass, dif_pos hmem]
    exact hcl
  · refine ⟨coneMargin_planeEmbed_nonneg_iff v, fun hv => ⟨?_, ?_⟩⟩
    · exact congrArg (σ.jointMeasure.integralOpOn pyramid)
        (funext fun p => coneExp_planeEmbed v p.1)
    · rw [coneOp_planeEmbed σ hr hMeas (fun p hp v hv => hBdd.1 v hv p hp) hv
        (hbb _ ((coneMargin_planeEmbed_nonneg_iff v).mpr hv)), ← hBdd.2.1 v hv]
end YangMills.Construction.EuclideanFunctionals.ConeSemigroupProof
