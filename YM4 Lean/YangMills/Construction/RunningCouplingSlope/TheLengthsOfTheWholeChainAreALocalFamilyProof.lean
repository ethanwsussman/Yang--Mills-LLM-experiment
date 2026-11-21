import YangMills.Construction.Lattice.OneStepObjectsNearSmallPlaquettesProof
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Averaging.EverySmallRadiusServesProof
import YangMills.Construction.Lattice.BlocksBoxesAndPaths
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreIsSmoothProof
import YangMills.Construction.RunningCouplingSlope.FieldsOfAFamilyThroughOne
import YangMills.Construction.RunningCouplingSlope.LegsOfTheOrdersAreContours
import YangMills.Construction.RunningCouplingSlope.PlainAverageOfARealField
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheLengthsOfTheWholeChainAreALocalFamily
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.NoiseRadiusLocal
open Tower Matrices
section Calculus
private theorem tendsto_div_sq_of_deriv {φ φ' : ℝ → ℝ} {c : ℝ}
    (hd : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt φ (φ' u) u) (h0 : φ 0 = 0) (h1 : φ' 0 = 0)
    (h2 : HasDerivAt φ' c 0) :
    Tendsto (fun u => φ u / u ^ 2) (𝓝[≠] 0) (𝓝 (c / 2)) := by
  have hfa : Tendsto φ (𝓝[≠] 0) (𝓝 0) := by
    have h := hd.self_of_nhds.continuousAt.tendsto
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hga : Tendsto (fun u : ℝ => u ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have h : Tendsto (fun u : ℝ => u ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) :=
      (continuous_pow 2).tendsto 0
    rw [zero_pow two_ne_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hslope : Tendsto (fun u => φ' u / (2 * u)) (𝓝[≠] 0) (𝓝 (c / 2)) := by
    have h := h2.tendsto_slope_zero.const_mul (1 / 2 : ℝ)
    have e : (1 / 2 : ℝ) * c = c / 2 := by ring
    rw [e] at h
    refine h.congr fun u => ?_
    simp only [zero_add, h1, sub_zero, smul_eq_mul]
    ring
  have hne : ∀ᶠ u in 𝓝[≠] (0 : ℝ), (2 * u) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact mul_ne_zero two_ne_zero hu
  refine HasDerivAt.lhopital_zero_nhdsNE (f' := φ') (g' := fun u => 2 * u)
    (hd.filter_mono nhdsWithin_le_nhds) (Eventually.of_forall fun u => ?_) hne hfa hga hslope
  simpa using hasDerivAt_pow 2 u
abbrev _root_.YangMills.SharedProofs.p94778 := @tendsto_div_sq_of_deriv
private theorem abs_mixed_deriv_le_of_isLocalMax {g : ℝ → ℝ → ℝ}
    (hg : ContDiffAt ℝ 2 (fun w : ℝ × ℝ => g w.1 w.2) 0) (h1 : g 0 0 = 1)
    (hle : ∀ᶠ w : ℝ × ℝ in 𝓝 0, g w.1 w.2 ≤ 1) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hs : ∀ᶠ u : ℝ in 𝓝 0, 1 - α ^ 2 * u ^ 2 ≤ g u 0)
    (ht : ∀ᶠ u : ℝ in 𝓝 0, 1 - β ^ 2 * u ^ 2 ≤ g 0 u) :
    deriv (fun s => g s 0) 0 = 0 ∧ deriv (fun t => g 0 t) 0 = 0 ∧
      |deriv (fun s => deriv (fun t => g s t) 0) 0| ≤ 2 * α * β := by
  set G : ℝ × ℝ → ℝ := fun w => g w.1 w.2 with hG
  have hG0 : G 0 = 1 := h1
  have hmax : IsLocalMax G 0 := by
    filter_upwards [hle] with w hw
    rw [hG0]
    exact hw
  have hD0 : fderiv ℝ G 0 = 0 := hmax.fderiv_eq_zero
  set D := fderiv ℝ G with hDdef
  have hDd : DifferentiableAt ℝ D 0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set H := fderiv ℝ D 0 with hH
  have hsym : ∀ a b, H a b = H b a := fun a b =>
    (hg.isSymmSndFDerivAt (by simp)) a b
  have hnear : ∀ᶠ w in 𝓝 (0 : ℝ × ℝ), DifferentiableAt ℝ G w := by
    filter_upwards [hg.eventually (by simp)] with w hw
    exact hw.differentiableAt (by norm_num)
  have line : ∀ a : ℝ × ℝ, Tendsto (fun u => (1 - G (u • a)) / u ^ 2) (𝓝[≠] 0)
      (𝓝 (-H a a / 2)) := by
    intro a
    have hcurve : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v • a) a u := fun u => by
      simpa using (hasDerivAt_id u).smul_const a
    have hcont : Tendsto (fun u : ℝ => u • a) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
      have h : Continuous fun u : ℝ => u • a := by fun_prop
      simpa using h.tendsto 0
    have hd : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt (fun u => 1 - G (u • a)) (-(D (u • a) a)) u := by
      filter_upwards [hcont.eventually hnear] with u hu
      have := hu.hasFDerivAt.comp_hasDerivAt u (hcurve u)
      simpa using this.const_sub 1
    have h2 : HasDerivAt (fun u : ℝ => -(D (u • a) a)) (-H a a) 0 := by
      have h₀ : HasFDerivAt D H ((0 : ℝ) • a) := by
        rw [zero_smul]
        exact hDd.hasFDerivAt
      have h₁ := h₀.comp_hasDerivAt (0 : ℝ) (hcurve 0)
      have h₂ := ((ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h₁
      exact h₂.neg
    refine tendsto_div_sq_of_deriv hd ?_ ?_ h2
    · simp [hG0]
    · simp [hD0]
  have neg : ∀ a, H a a ≤ 0 := by
    intro a
    have hcont : Tendsto (fun u : ℝ => u • a) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
      have h : Continuous fun u : ℝ => u • a := by fun_prop
      simpa using h.tendsto 0
    have h₁ : ∀ᶠ u in 𝓝[≠] (0 : ℝ), 0 ≤ (1 - G (u • a)) / u ^ 2 := by
      filter_upwards [(hcont.eventually hle).filter_mono nhdsWithin_le_nhds] with u hu
      exact div_nonneg (by linarith) (by positivity)
    have := ge_of_tendsto (line a) h₁
    linarith
  have e1 : -H (1, 0) (1, 0) ≤ 2 * α ^ 2 := by
    have h₁ : ∀ᶠ u in 𝓝[≠] (0 : ℝ), (1 - G (u • ((1, 0) : ℝ × ℝ))) / u ^ 2 ≤ α ^ 2 := by
      filter_upwards [hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hne
      have hp : 0 < u ^ 2 := by
        have : u ≠ 0 := hne
        positivity
      rw [div_le_iff₀ hp]
      have e : G (u • ((1, 0) : ℝ × ℝ)) = g u 0 := by simp [hG]
      rw [e]
      linarith
    have := le_of_tendsto (line (1, 0)) h₁
    linarith
  have e2 : -H (0, 1) (0, 1) ≤ 2 * β ^ 2 := by
    have h₁ : ∀ᶠ u in 𝓝[≠] (0 : ℝ), (1 - G (u • ((0, 1) : ℝ × ℝ))) / u ^ 2 ≤ β ^ 2 := by
      filter_upwards [ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hne
      have hp : 0 < u ^ 2 := by
        have : u ≠ 0 := hne
        positivity
      rw [div_le_iff₀ hp]
      have e : G (u • ((0, 1) : ℝ × ℝ)) = g 0 u := by simp [hG]
      rw [e]
      linarith
    have := le_of_tendsto (line (0, 1)) h₁
    linarith
  have hd0 : DifferentiableAt ℝ G 0 := hnear.self_of_nhds
  have p1 : HasDerivAt (fun s => g s 0) (D 0 (1, 0)) 0 := by
    have hc : HasDerivAt (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) (f := fun s : ℝ => ((s, 0) : ℝ × ℝ)) hd0.hasFDerivAt hc
  have p2 : HasDerivAt (fun t => g 0 t) (D 0 (0, 1)) 0 := by
    have hc : HasDerivAt (fun t : ℝ => ((0, t) : ℝ × ℝ)) (0, 1) 0 :=
      (hasDerivAt_const 0 0).prodMk (hasDerivAt_id 0)
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) (f := fun t : ℝ => ((0, t) : ℝ × ℝ)) hd0.hasFDerivAt hc
  have hmix : deriv (fun s => deriv (fun t => g s t) 0) 0 = H (1, 0) (0, 1) := by
    have hc : ∀ s : ℝ, HasDerivAt (fun v : ℝ => ((v, 0) : ℝ × ℝ)) (1, 0) s := fun s =>
      (hasDerivAt_id s).prodMk (hasDerivAt_const s 0)
    have ht0 : Tendsto (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
      have h : Continuous fun s : ℝ => ((s, 0) : ℝ × ℝ) := by fun_prop
      exact h.tendsto 0
    have ev : (fun s => deriv (fun t => g s t) 0) =ᶠ[𝓝 0] fun s => D (s, 0) (0, 1) := by
      filter_upwards [ht0.eventually hnear] with s hs'
      have hc' : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) (0, 1) 0 :=
        (hasDerivAt_const 0 s).prodMk (hasDerivAt_id 0)
      exact (HasFDerivAt.comp_hasDerivAt (0 : ℝ) (f := fun t : ℝ => ((s, t) : ℝ × ℝ))
        hs'.hasFDerivAt hc').deriv
    rw [ev.deriv_eq]
    have h₀ : HasFDerivAt D H (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) := hDd.hasFDerivAt
    have h₁ := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (f := fun v : ℝ => ((v, 0) : ℝ × ℝ)) h₀ (hc 0)
    have h₂ := ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).hasFDerivAt).comp_hasDerivAt
      (0 : ℝ) h₁
    exact h₂.deriv
  refine ⟨by rw [p1.deriv, hD0]; simp, by rw [p2.deriv, hD0]; simp, ?_⟩
  rw [hmix]
  set A := -H (1, 0) (1, 0)
  set B := -H (0, 1) (0, 1)
  set C := -H (1, 0) (0, 1)
  have hq : ∀ x : ℝ, 0 ≤ A * (x * x) + (2 * C) * x + B := by
    intro x
    have h := neg (x • ((1, 0) : ℝ × ℝ) + ((0, 1) : ℝ × ℝ))
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul] at h
    rw [hsym (0, 1) (1, 0)] at h
    simp only [A, B, C]
    nlinarith [h]
  have hdis := discrim_le_zero hq
  have hB : 0 ≤ B := by simpa [B] using neg (0, 1)
  have hC : C ^ 2 ≤ (2 * α * β) ^ 2 := by
    have h₁ : C ^ 2 ≤ A * B := by
      unfold discrim at hdis
      nlinarith [hdis]
    have h₂ : A * B ≤ (2 * α ^ 2) * (2 * β ^ 2) :=
      mul_le_mul e1 e2 hB (by positivity)
    nlinarith [h₁, h₂]
  have h3 := abs_le_of_sq_le_sq hC (by positivity)
  have e : |H (1, 0) (0, 1)| = |C| := by simp [C]
  rw [e]
  exact h3
private theorem differentiable_partials {g : ℝ → ℝ → ℝ}
    (hg : ContDiffAt ℝ 2 (fun w : ℝ × ℝ => g w.1 w.2) 0) :
    DifferentiableAt ℝ (fun s => g s 0) 0 ∧ DifferentiableAt ℝ (fun t => g 0 t) 0 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun t => g s t) 0) ∧
      DifferentiableAt ℝ (fun s => deriv (fun t => g s t) 0) 0 := by
  set G : ℝ × ℝ → ℝ := fun w => g w.1 w.2 with hG
  have hDd : DifferentiableAt ℝ (fderiv ℝ G) 0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : ∀ᶠ w in 𝓝 (0 : ℝ × ℝ), DifferentiableAt ℝ G w := by
    filter_upwards [hg.eventually (by simp)] with w hw
    exact hw.differentiableAt (by norm_num)
  have hd0 : DifferentiableAt ℝ G 0 := hnear.self_of_nhds
  have ht0 : Tendsto (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
    have h : Continuous fun s : ℝ => ((s, 0) : ℝ × ℝ) := by fun_prop
    exact h.tendsto 0
  have line : ∀ s : ℝ, DifferentiableAt ℝ G (s, 0) →
      HasDerivAt (fun t => g s t) (fderiv ℝ G (s, 0) (0, 1)) 0 := fun s hs => by
    have hc' : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) (0, 1) 0 :=
      (hasDerivAt_const 0 s).prodMk (hasDerivAt_id 0)
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) (f := fun t : ℝ => ((s, t) : ℝ × ℝ))
      hs.hasFDerivAt hc'
  have ev : (fun s => deriv (fun t => g s t) 0) =ᶠ[𝓝 0] fun s => fderiv ℝ G (s, 0) (0, 1) := by
    filter_upwards [ht0.eventually hnear] with s hs'
    exact (line s hs').deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : HasDerivAt (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
    exact (HasFDerivAt.comp_hasDerivAt (0 : ℝ) (f := fun s : ℝ => ((s, 0) : ℝ × ℝ))
      hd0.hasFDerivAt hc).differentiableAt
  · exact (line 0 hd0).differentiableAt
  · filter_upwards [ht0.eventually hnear] with s hs'
    exact (line s hs').differentiableAt
  · have hc : HasDerivAt (fun v : ℝ => ((v, 0) : ℝ × ℝ)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
    have h₀ : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) 0)
        (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) := hDd.hasFDerivAt
    have h₁ := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (f := fun v : ℝ => ((v, 0) : ℝ × ℝ)) h₀ hc
    have h₂ := ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).hasFDerivAt).comp_hasDerivAt
      (0 : ℝ) h₁
    exact h₂.differentiableAt.congr_of_eventuallyEq ev
private theorem deriv_ofReal_comp {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f 0) :
    deriv (fun s => ((f s : ℝ) : ℂ)) 0 = ((deriv f 0 : ℝ) : ℂ) :=
  hf.hasDerivAt.ofReal_comp.deriv
private theorem mixedDeriv_ofReal_comp {g : ℝ → ℝ → ℝ}
    (hg : ContDiffAt ℝ 2 (fun w : ℝ × ℝ => g w.1 w.2) 0) :
    deriv (fun s => deriv (fun t => ((g s t : ℝ) : ℂ)) 0) 0 =
      ((deriv (fun s => deriv (fun t => g s t) 0) 0 : ℝ) : ℂ) := by
  obtain ⟨-, -, h₁, h₂⟩ := differentiable_partials hg
  have ev : (fun s => deriv (fun t => ((g s t : ℝ) : ℂ)) 0) =ᶠ[𝓝 0]
      fun s => ((deriv (fun t => g s t) 0 : ℝ) : ℂ) := by
    filter_upwards [h₁] with s hs
    exact deriv_ofReal_comp hs
  rw [ev.deriv_eq]
  exact deriv_ofReal_comp h₂
end Calculus
section Matrices
private theorem norm_entry_le (X : ComplexMatrix2) (i j : Fin 2) : ‖X i j‖ ≤ ‖X‖ := by apply _root_.YangMills.SharedProofs.p14523 <;> assumption
private theorem norm_of_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : ‖g‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.mem_specialUnitaryGroup_iff.1 hg).1
private theorem inv_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : g⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem norm_inv_sub_one {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    ‖g⁻¹ - 1‖ = ‖g - 1‖ := by apply _root_.YangMills.Construction.Averaging.SmallRadiusProof.norm_inv_sub_one_specialUnitary <;> assumption
private theorem norm_mul_sub_one_le {a b : ComplexMatrix2} (ha : a ∈ ComplexMatrix2.specialUnitary) :
    ‖a * b - 1‖ ≤ ‖a - 1‖ + ‖b - 1‖ := by
  have e : a * b - 1 = a * (b - 1) + (a - 1) := by noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h := norm_mul_le a (b - 1)
  rw [norm_of_mem_specialUnitary ha, one_mul] at h
  linarith
private theorem normSq_sub_one_eq (z : ℂ) :
    Complex.normSq (z - 1) = Complex.normSq z - 2 * z.re + 1 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring
private theorem one_sub_sq_le_halfTrace_re {q : ComplexMatrix2}
    (hq : q ∈ ComplexMatrix2.specialUnitary) :
    1 - ‖q - 1‖ ^ 2 ≤ (Matrix.trace q).re / 2 := by
  set a := ‖q - 1‖ with ha
  have hu : star q * q = 1 :=
    (Matrix.mem_unitaryGroup_iff').1 (Matrix.mem_specialUnitaryGroup_iff.1 hq).1
  have col : ∀ j : Fin 2, Complex.normSq (q 0 j) + Complex.normSq (q 1 j) = 1 := by
    intro j
    have h := congrFun (congrFun hu j) j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq] at h
    have e : ((Complex.normSq (q 0 j) + Complex.normSq (q 1 j) : ℝ) : ℂ) = 1 := by
      push_cast
      rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
      exact h
    exact_mod_cast e
  have ent : ∀ i j : Fin 2, Complex.normSq ((q - 1) i j) ≤ a ^ 2 := fun i j => by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_entry_le _ i j) 2
  have h0 : 1 - a ^ 2 ≤ (q 0 0).re := by
    have h₁ := ent 0 0
    have h₂ := ent 1 0
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h₁
    have e : (q - 1) 1 0 = q 1 0 := by simp
    rw [e] at h₂
    rw [normSq_sub_one_eq] at h₁
    linarith [col 0]
  have h1 : 1 - a ^ 2 ≤ (q 1 1).re := by
    have h₁ := ent 1 1
    have h₂ := ent 0 1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h₁
    have e : (q - 1) 0 1 = q 0 1 := by simp
    rw [e] at h₂
    rw [normSq_sub_one_eq] at h₁
    linarith [col 1]
  rw [Matrix.trace_fin_two, Complex.add_re]
  linarith
private theorem halfTrace_re_le_one {u : ComplexMatrix2} (hu : u ∈ ComplexMatrix2.specialUnitary) :
    (Matrix.trace u).re / 2 ≤ 1 := by
  have h : ∀ i j, (u i j).re ≤ 1 := fun i j => by
    have := norm_entry_le u i j
    rw [norm_of_mem_specialUnitary hu] at this
    exact (Complex.re_le_norm _).trans this
  rw [Matrix.trace_fin_two, Complex.add_re]
  linarith [h 0 0, h 1 1]
private theorem finsetMean_bounds {ι : Type} (T : Finset ι) (f : ι → ComplexMatrix2)
    (hT : T.Nonempty) {a t : ℝ}
    (h1 : ∀ i ∈ T, ‖f i - 1‖ ≤ a) (h2 : ∀ i ∈ T, ‖f i‖ ≤ 1)
    (h3 : ∀ i ∈ T, t ≤ (Matrix.trace (f i)).re / 2) :
    ‖(T.card : ℂ)⁻¹ • ∑ i ∈ T, f i - 1‖ ≤ a ∧ ‖(T.card : ℂ)⁻¹ • ∑ i ∈ T, f i‖ ≤ 1 ∧
      t ≤ (Matrix.trace ((T.card : ℂ)⁻¹ • ∑ i ∈ T, f i)).re / 2 := by
  have hc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hcc : (T.card : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hn : ‖(T.card : ℂ)⁻¹‖ = (T.card : ℝ)⁻¹ := by simp
  refine ⟨?_, ?_, ?_⟩
  · have e : (T.card : ℂ)⁻¹ • ∑ i ∈ T, f i - 1 = (T.card : ℂ)⁻¹ • ∑ i ∈ T, (f i - 1) := by
      rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hcc, one_smul]
    rw [e, norm_smul, hn]
    have hs : ‖∑ i ∈ T, (f i - 1)‖ ≤ T.card * a := by
      simpa using norm_sum_le_of_le T h1
    calc (T.card : ℝ)⁻¹ * ‖∑ i ∈ T, (f i - 1)‖ ≤ (T.card : ℝ)⁻¹ * (T.card * a) := by gcongr
      _ = a := by field_simp
  · rw [norm_smul, hn]
    have hs : ‖∑ i ∈ T, f i‖ ≤ T.card * 1 := by
      simpa using norm_sum_le_of_le T h2
    calc (T.card : ℝ)⁻¹ * ‖∑ i ∈ T, f i‖ ≤ (T.card : ℝ)⁻¹ * (T.card * 1) := by gcongr
      _ = 1 := by field_simp
  · have e : (Matrix.trace ((T.card : ℂ)⁻¹ • ∑ i ∈ T, f i)).re =
        (T.card : ℝ)⁻¹ * ∑ i ∈ T, (Matrix.trace (f i)).re := by
      rw [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul, ← Complex.ofReal_natCast,
        ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
    rw [e]
    have hs : ∑ _i ∈ T, (2 * t) ≤ ∑ i ∈ T, (Matrix.trace (f i)).re :=
      Finset.sum_le_sum fun i hi => by linarith [h3 i hi]
    rw [Finset.sum_const, nsmul_eq_mul] at hs
    have h4 : (T.card : ℝ)⁻¹ * (T.card * (2 * t)) ≤
        (T.card : ℝ)⁻¹ * ∑ i ∈ T, (Matrix.trace (f i)).re := by gcongr
    have h5 : (T.card : ℝ)⁻¹ * (T.card * (2 * t)) = 2 * t := by field_simp
    linarith
end Matrices
section Means
variable {L n k j : ℕ}
private theorem pathHolonomy_mem {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ ComplexMatrix2.specialUnitary)
    (l : List (Edge L n k j)) : PeriodicLattice.pathHolonomy V l ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.DeltaSharedProofs.p502631 <;> assumption
abbrev _root_.YangMills.SharedProofs.p132511 := @pathHolonomy_mem
private theorem norm_pathHolonomy_sub_one_le {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ ComplexMatrix2.specialUnitary)
    (l : List (Edge L n k j)) {e : ℝ} (he : ∀ b ∈ l, ‖V b - 1‖ ≤ e) :
    ‖PeriodicLattice.pathHolonomy V l - 1‖ ≤ l.length * e := by
  induction l with
  | nil => simp [PeriodicLattice.pathHolonomy]
  | cons b l ih =>
    have e₁ : PeriodicLattice.pathHolonomy V (b :: l) = V b * PeriodicLattice.pathHolonomy V l := by
      simp [PeriodicLattice.pathHolonomy]
    rw [e₁]
    have h₁ := norm_mul_sub_one_le (b := PeriodicLattice.pathHolonomy V l) (hV b)
    have h₂ := he b (by simp)
    have h₃ := ih fun b' hb' => he b' (by simp [hb'])
    simp only [List.length_cons]
    push_cast
    linarith
private theorem contourHolonomy_mem {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ ComplexMatrix2.specialUnitary)
    (c : Edge L n k (j + 1)) (x : Vertex L n k j) (π : Equiv.Perm (Fin 4)) :
    contourHolonomy V c x π ∈ ComplexMatrix2.specialUnitary :=
  ComplexMatrix2.specialUnitary.mul_mem
    (ComplexMatrix2.specialUnitary.mul_mem (pathHolonomy_mem hV _) (pathHolonomy_mem hV _))
    (inv_mem_specialUnitary (pathHolonomy_mem hV _))
private theorem contourMean_bounds (hL : 0 < L) {c : Edge L n k (j + 1)}
    (hcard : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)) = L ^ 4)
    {V : Edge L n k j → ComplexMatrix2} (hV : ∀ b, V b ∈ ComplexMatrix2.specialUnitary) {a : ℝ}
    (ha : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source,
      ∀ π : Equiv.Perm (Fin 4), ‖contourHolonomy V c x π - 1‖ ≤ a) :
    ‖contourMean V c - 1‖ ≤ a ∧ ‖contourMean V c‖ ≤ 1 ∧
      1 - a ^ 2 ≤ (Matrix.trace (contourMean V c)).re / 2 := by
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := by
    have h4 : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero h4
    exact Set.toFinite _
  set S := hfin.toFinset with hS
  have hScard : S.card = L ^ 4 := by
    rw [hS, ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq, hcard]
  set T : Finset (Vertex L n k j × Equiv.Perm (Fin 4)) := S ×ˢ Finset.univ with hT
  have hTcard : T.card = L ^ 4 * 24 := by
    rw [hT, Finset.card_product, hScard, Finset.card_univ, Fintype.card_perm]
    simp [Nat.factorial]
  have hne : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]
    positivity
  have e : contourMean V c = (T.card : ℂ)⁻¹ • ∑ p ∈ T, contourHolonomy V c p.1 p.2 := by
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin, hT, Finset.sum_product, hTcard,
      PeriodicLattice.inverseFourthPowerWeight]
    congr 1
    push_cast
    rw [zpow_neg]
    have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    norm_num
  have hin : ∀ p ∈ T, p.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :=
    fun p hp => by
      have := (Finset.mem_product.1 hp).1
      simpa [hS] using this
  rw [e]
  refine finsetMean_bounds T _ hne (fun p hp => ha _ (hin p hp) _)
    (fun p _ => (norm_of_mem_specialUnitary (contourHolonomy_mem hV c _ _)).le) fun p hp => ?_
  have h₁ := one_sub_sq_le_halfTrace_re (contourHolonomy_mem hV c p.1 p.2)
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ha _ (hin p hp) p.2) 2
  linarith
private theorem meanRadius_bounds {V : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
    {a : ℝ}
    (hm : ‖contourMean V c - 1‖ ≤ a ∧ ‖contourMean V c‖ ≤ 1 ∧
      1 - a ^ 2 ≤ (Matrix.trace (contourMean V c)).re / 2)
    (hr : meanRadius V c = (((meanRadius V c).re : ℝ) : ℂ)) (hr0 : 0 < (meanRadius V c).re)
    (hu : normalizedMean V c ∈ ComplexMatrix2.specialUnitary) :
    1 - a ^ 2 ≤ (meanRadius V c).re ∧ (meanRadius V c).re ≤ 1 ∧
      ‖normalizedMean V c - 1‖ ≤ 2 * a := by
  obtain ⟨h1, h2, h3⟩ := hm
  set r := (meanRadius V c).re with hrdef
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hMu : contourMean V c = (r : ℂ) • normalizedMean V c := by
    rw [normalizedMean]
    show contourMean V c = (r : ℂ) • ((meanRadius V c)⁻¹ • contourMean V c)
    rw [hr, smul_smul, mul_inv_cancel₀ hrc, one_smul]
  have hnorm : ‖contourMean V c‖ = r := by
    rw [hMu, norm_smul, Complex.norm_real, norm_of_mem_specialUnitary hu, mul_one,
      Real.norm_of_nonneg hr0.le]
  have hr1 : r ≤ 1 := hnorm ▸ h2
  have hone : ‖(1 : ComplexMatrix2)‖ = 1 :=
    norm_of_mem_specialUnitary ComplexMatrix2.specialUnitary.one_mem
  have hdist : 1 - r ≤ a := by
    have h := norm_sub_norm_le (1 : ComplexMatrix2) (contourMean V c)
    rw [hone, hnorm, norm_sub_rev] at h
    linarith
  refine ⟨?_, hr1, ?_⟩
  · have e : (Matrix.trace (contourMean V c)).re / 2 =
        r * ((Matrix.trace (normalizedMean V c)).re / 2) := by
      rw [hMu, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring
    have h₄ := halfTrace_re_le_one hu
    rw [e] at h3
    nlinarith
  · have e : normalizedMean V c - 1 =
        ((1 - r : ℝ) : ℂ) • normalizedMean V c + (contourMean V c - 1) := by
      rw [hMu]
      push_cast
      rw [sub_smul, one_smul]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Complex.norm_real, norm_of_mem_specialUnitary hu, mul_one,
      Real.norm_of_nonneg (by linarith)]
    linarith
end Means
section Geometry
variable {L n k : ℕ}
private abbrev cellsRegion (j : ℕ) (Z : Set (Vertex L n k k)) : Set (PeriodicLattice.FourTorus L n) :=
  PeriodicLattice.blockUnionAtLevel (K := k) (j := k) j Z
private structure BlockGeometry (L n k : ℕ) : Prop where
  card : ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)) = L ^ 4
  leg : ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    ∀ y : Vertex L n k (j + 1), (y = c.source ∨ y = c.target) →
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
    ∀ π : Equiv.Perm (Fin 4), (contourLeg y x π).length ≤ 2 * (L - 1) ∧
      ∀ b ∈ contourLeg y x π, b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
  crossing : ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source,
      (PeriodicLattice.crossingPath c x).length = L ∧
      ∀ b ∈ PeriodicLattice.crossingPath c x,
        b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
  translated : ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source,
      PeriodicLattice.shiftAcross c x ∈
        PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.target
  double : ∀ j, j < k → ∀ (Z : Set (Vertex L n k k)) (c : Edge L n k (j + 1)),
    (c.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion (j + 1) Z →
    (c.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion (j + 1) Z →
    ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      (b.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion j Z ∧
        (b.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion j Z
  cell_of : ∀ j, j ≤ k → ∀ (Z : Set (Vertex L n k k)) (x : Vertex L n k j),
    (x : PeriodicLattice.FourTorus L n) ∈ cellsRegion j Z → levelVertexCell x ∈ Z
  cell_mem : ∀ j, j ≤ k → ∀ x : Vertex L n k j,
    (x : PeriodicLattice.FourTorus L n) ∈ cellsRegion j ({levelVertexCell x} : Set (Vertex L n k k))
  near : ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    cellDist (levelVertexCell c.source) (levelVertexCell c.target) ≤ 4 * (L : ℝ) ^ k
  self : ∀ y : Vertex L n k k, cellDist y y = 0
  symm : ∀ y y' : Vertex L n k k, cellDist y y' = cellDist y' y
private theorem coe_toSublattice {L m : ℕ} (hL : 0 < L) {j j' : ℤ} (h : j ≤ j')
    (x : PeriodicLattice.Site L m j) :
    ((x.toSublattice j' : PeriodicLattice.Site L m j') : PeriodicLattice.FourTorus L m) = x := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
private theorem blockGeometry_holds (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k)
    (hP : PeriodicLattice.BlockPaths.Statement)
    (hl : AxisOrderLegsAreContours)
    (hBB : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hCr : PeriodicLattice.CrossingsAndBareBlocks.Statement)
    (hCell : NeighbouringFineVertexCells)
    (hTop : TopEdgesAndCubes) : BlockGeometry L n k := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have data : Averaging.OneStep.Parameters 4 2 L k n ComplexMatrix2.specialUnitary :=
    ⟨rfl, rfl, rfl, hL.1, hL.2, by omega, hn⟩
  obtain ⟨-, -, hOrder, -, hOver, -, hStep⟩ := hBB L k n data
  obtain ⟨hsym, htri, hin, hnb⟩ := hCell L hL n k
  obtain ⟨hzero, -, huniq⟩ := hTop L hL n k hn hk
  have hdepth : ∀ j, j ≤ k → PeriodicLattice.levelDepth k j ≤ PeriodicLattice.levelDepth k 0 :=
    fun j _ => by simp [PeriodicLattice.levelDepth]
  have self_mem : ∀ j, j ≤ k → ∀ x : Vertex L n k j,
      (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock j x := by
    intro j hj x
    have h := ((hOrder j j le_rfl hj).2.1 x).1.2
    rw [← h]
    refine ⟨0, fun μ => ?_, ?_⟩
    · have h1 : (1 : ℤ) ≤ (L : ℤ) ^ j := one_le_pow₀ (by exact_mod_cast hL0)
      simp only [Pi.zero_apply, abs_zero, PeriodicLattice.halfSideSteps]
      exact Int.ediv_nonneg (by omega) (by norm_num)
    · simp only [PeriodicLattice.offsetSite, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
        add_zero]
      exact coe_toSublattice hL0 (by simp [PeriodicLattice.levelDepth]) x
  have fine_cell : ∀ (Z : Set (Vertex L n k k)) (x : Vertex L n k 0),
      (x : PeriodicLattice.FourTorus L n) ∈ cellsRegion 0 Z → fineVertexCell x ∈ Z := by
    intro Z x hx
    obtain ⟨Y, hY, hxY⟩ : ∃ Y ∈ Z,
        (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k Y := by
      simpa [cellsRegion, PeriodicLattice.blockUnionAtLevel, PeriodicLattice.refinedBlockUnion]
        using hx
    have h := huniq _ _ _ (hin x) hxY
    rwa [h]
  have cell_of : ∀ j, j ≤ k → ∀ (Z : Set (Vertex L n k k)) (x : Vertex L n k j),
      (x : PeriodicLattice.FourTorus L n) ∈ cellsRegion j Z → levelVertexCell x ∈ Z := by
    intro j hj Z x hx
    have h1 := (hOver k le_rfl Z).2.2.2 j hj x hx (self_mem j hj x)
    refine fine_cell Z (x.toSublattice (PeriodicLattice.levelDepth k 0)) ?_
    rw [coe_toSublattice hL0 (hdepth j hj) x]
    exact h1
  have cell_mem : ∀ j, j ≤ k → ∀ x : Vertex L n k j,
      (x : PeriodicLattice.FourTorus L n) ∈
        cellsRegion j ({levelVertexCell x} : Set (Vertex L n k k)) := by
    intro j hj x
    have h := (hOrder (k - j) k (by omega) le_rfl).2.2.1.2
    have e : k - (k - j) = j := by omega
    rw [e] at h
    have hx : (x : PeriodicLattice.FourTorus L n) ∈
        (⋃ y : Vertex L n k k, PeriodicLattice.refinedBlock (k - j) y) := by
      rw [h]
      exact x.2
    obtain ⟨Y, hY⟩ := Set.mem_iUnion.1 hx
    have h2 : (x : PeriodicLattice.FourTorus L n) ∈ cellsRegion j ({Y} : Set (Vertex L n k k)) := by
      simpa [cellsRegion, PeriodicLattice.blockUnionAtLevel, PeriodicLattice.refinedBlockUnion]
        using hY
    have h3 := cell_of j hj _ x h2
    rw [Set.mem_singleton_iff] at h3
    rw [h3]
    exact h2
  have walk : ∀ (x : Vertex L n k 0) (μ : Fin 4) (a : ℕ),
      cellDist (fineVertexCell x)
        (fineVertexCell (x + (a : ℤ) • PeriodicLattice.unitStep L n _ μ)) ≤ 4 * (a : ℝ) := by
    intro x μ a
    induction a with
    | zero => simp [hzero]
    | succ a ih =>
      have e : x + ((a + 1 : ℕ) : ℤ) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ =
          (x + (a : ℤ) • PeriodicLattice.unitStep L n _ μ) + PeriodicLattice.unitStep L n _ μ := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rw [e]
      have h' := hnb (x + (a : ℤ) • PeriodicLattice.unitStep L n _ μ) μ
      have h := htri (fineVertexCell x)
        (fineVertexCell (x + (a : ℤ) • PeriodicLattice.unitStep L n _ μ))
        (fineVertexCell ((x + (a : ℤ) • PeriodicLattice.unitStep L n _ μ) +
          PeriodicLattice.unitStep L n _ μ))
      push_cast
      linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, cell_of, cell_mem, ?_, hzero, hsym⟩
  · exact fun j hj c hc => ((hCr L hL n k hn).1 j hj c hc).1
  · intro j hj c hc y hy x hx π
    obtain ⟨σ, hσ⟩ := hl L n _ _ y x π
    obtain ⟨μ, hμ⟩ := hc
    obtain ⟨-, -, -, -, hPaths⟩ := (hP L n k hL.1 hL.2 hn j hj).2 c μ hμ
    have hm : PeriodicLattice.orderedContour y x σ ∈ PeriodicLattice.contourSet y x := ⟨σ, rfl⟩
    have e : contourLeg y x π = PeriodicLattice.orderedContour y x σ := hσ
    rw [e]
    exact ⟨(((hStep j hj).2.2.1 y x hx).1 _ hm).1, fun b hb => (hPaths.1 y hy x hx).1 _ hm b hb⟩
  · intro j hj c hc x hx
    obtain ⟨-, h₂, h₃⟩ := ((hStep j hj).2.1 c hc).2 x hx
    exact ⟨h₂, fun b hb => (h₃ b hb).2⟩
  · exact fun j hj c hc x hx => ((hStep j hj).2.1 c hc).1.mapsTo hx
  · intro j hj Z c ht hh b hb
    have h := (hOver k le_rfl Z).2.2.1 j hj c ht hh
    exact ⟨h hb.1, h hb.2⟩
  · intro j hj c hc
    obtain ⟨μ, hμ⟩ := hc
    have hS := ((hOrder (j + 1) (j + 1) le_rfl hj).2.2.2.2 c μ hμ).1
    rw [Nat.sub_self] at hS
    set x := c.source.toSublattice (PeriodicLattice.levelDepth k 0) with hxdef
    have hx : x ∈ (PeriodicLattice.sitesIn (PeriodicLattice.refinedBlock (j + 1) c.source) :
        Set (Vertex L n k 0)) := by
      change (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock (j + 1) c.source
      rw [hxdef, coe_toSublattice hL0 (hdepth _ hj) c.source]
      exact self_mem (j + 1) hj c.source
    have hz := hS.mapsTo hx
    have hz' := (hOver k le_rfl _).2.2.2 (j + 1) hj c.target (cell_mem (j + 1) hj c.target) hz
    have hc' := fine_cell _ _ hz'
    rw [Set.mem_singleton_iff] at hc'
    show cellDist (fineVertexCell x) (levelVertexCell c.target) ≤ _
    rw [← hc']
    have hw := walk x μ (L ^ (j + 1))
    have e : ((L ^ (j + 1) : ℕ) : ℤ) = (L : ℤ) ^ (j + 1) := by push_cast; rfl
    rw [e] at hw
    refine hw.trans ?_
    push_cast
    have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL0
    have := pow_le_pow_right₀ h1 (show j + 1 ≤ k from hj)
    linarith
end Geometry
section Levels
variable {L n k : ℕ}
private theorem levelField_succ_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
private theorem levelField_succ_neg (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : ¬b.IsPositivelyOriented) :
    levelField X (j + 1) b = (levelField X (j + 1) b.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p5483 <;> assumption
private theorem norm_contourHolonomy_sub_one_le (G : BlockGeometry L n k) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ ComplexMatrix2.specialUnitary) {e : ℝ} (he0 : 0 ≤ e)
    (he : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), ‖V b - 1‖ ≤ e)
    {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source)
    (π : Equiv.Perm (Fin 4)) : ‖contourHolonomy V c x π - 1‖ ≤ 5 * L * e := by
  obtain ⟨l₁, m₁⟩ := G.leg j hj c hc c.source (Or.inl rfl) x hx π
  obtain ⟨l₂, m₂⟩ := G.crossing j hj c hc x hx
  obtain ⟨l₃, m₃⟩ := G.leg j hj c hc c.target (Or.inr rfl) _ (G.translated j hj c hc x hx) π
  have d₁ := norm_pathHolonomy_sub_one_le hV _ fun b hb => he b (m₁ b hb)
  have d₂ := norm_pathHolonomy_sub_one_le hV _ fun b hb => he b (m₂ b hb)
  have d₃ := norm_pathHolonomy_sub_one_le hV _ fun b hb => he b (m₃ b hb)
  have c₁ : ((contourLeg c.source x π).length : ℝ) ≤ 2 * L := by
    have : (contourLeg c.source x π).length ≤ 2 * L := by omega
    exact_mod_cast this
  have c₃ : ((contourLeg c.target (PeriodicLattice.shiftAcross c x) π).length : ℝ) ≤ 2 * L := by
    have : (contourLeg c.target (PeriodicLattice.shiftAcross c x) π).length ≤ 2 * L := by omega
    exact_mod_cast this
  rw [l₂] at d₂
  have f₁ := mul_le_mul_of_nonneg_right c₁ he0
  have f₃ := mul_le_mul_of_nonneg_right c₃ he0
  have s₁ := norm_mul_sub_one_le (b := (PeriodicLattice.pathHolonomy V
    (contourLeg c.target (PeriodicLattice.shiftAcross c x) π))⁻¹)
    (ComplexMatrix2.specialUnitary.mul_mem (pathHolonomy_mem hV (contourLeg c.source x π))
      (pathHolonomy_mem hV (PeriodicLattice.crossingPath c x)))
  have s₂ := norm_mul_sub_one_le (b := PeriodicLattice.pathHolonomy V (PeriodicLattice.crossingPath c x))
    (pathHolonomy_mem hV (contourLeg c.source x π))
  rw [norm_inv_sub_one (pathHolonomy_mem hV _)] at s₁
  show ‖PeriodicLattice.pathHolonomy V (contourLeg c.source x π) *
    PeriodicLattice.pathHolonomy V (PeriodicLattice.crossingPath c x) *
    (PeriodicLattice.pathHolonomy V
      (contourLeg c.target (PeriodicLattice.shiftAcross c x) π))⁻¹ - 1‖ ≤ _
  linarith
private def MeanIsCompactNearOne (L n k : ℕ) (ρ : ℝ) : Prop :=
  ∀ j, j < k → ∀ V ∈ fieldSpace L n k j, (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) →
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      meanRadius V c = (((meanRadius V c).re : ℝ) : ℂ) ∧ 0 < (meanRadius V c).re ∧
        normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup
private structure IsNearUnit (ρ : ℝ) (X : ChainPoint L n k) : Prop where
  real : IsCompactValued X
  near : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ
private theorem IsNearUnit.mem_specialUnitary {ρ : ℝ} {X : ChainPoint L n k} (h : IsNearUnit ρ X)
    {j : ℕ} (hj : j ≤ k) (b : Edge L n k j) : levelField X j b ∈ ComplexMatrix2.specialUnitary :=
  (h.real.2 j hj).1 b (Set.mem_univ b)
private theorem meanRadius_step_bounds (hL : 0 < L) (G : BlockGeometry L n k) {ρ : ℝ}
    (hA : MeanIsCompactNearOne L n k ρ)
    {X : ChainPoint L n k} (hX : IsNearUnit ρ X) {j : ℕ} (hj : j < k) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) {a : ℝ}
    (ha : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source,
      ∀ π : Equiv.Perm (Fin 4), ‖contourHolonomy (levelField X j) c x π - 1‖ ≤ a) :
    1 - a ^ 2 ≤ (meanRadius (levelField X j) c).re ∧ (meanRadius (levelField X j) c).re ≤ 1 ∧
      ‖normalizedMean (levelField X j) c - 1‖ ≤ 2 * a := by
  obtain ⟨h₁, h₂, h₃⟩ := hA j hj _ (hX.real.2 j hj.le) (hX.near j hj.le) c hc
  exact meanRadius_bounds (contourMean_bounds hL (G.card j hj c hc) (hX.mem_specialUnitary hj.le) ha)
    h₁ h₂ h₃
private def growthFactor (L j : ℕ) : ℝ := (1 + 10 * (L : ℝ)) ^ j
private theorem growthFactor_pos (L j : ℕ) : 0 < growthFactor L j := by
  unfold growthFactor
  positivity
private theorem one_le_growthFactor (L j : ℕ) : 1 ≤ growthFactor L j :=
  one_le_pow₀ (by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith)
private theorem growthFactor_succ (L j : ℕ) :
    growthFactor L (j + 1) = (1 + 10 * (L : ℝ)) * growthFactor L j := by
  unfold growthFactor
  rw [pow_succ]
  ring
private theorem norm_levelField_sub_one_le (hL : 0 < L) (G : BlockGeometry L n k) {ρ : ℝ}
    (hA : MeanIsCompactNearOne L n k ρ)
    {X : ChainPoint L n k} (hX : IsNearUnit ρ X) {Z : Set (Vertex L n k k)} {ε : ℝ} (hε : 0 ≤ ε)
    (h0 : ∀ b : Edge L n k 0, (b.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion 0 Z →
      (b.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion 0 Z → ‖X.fine b - 1‖ ≤ ε)
    (hN : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (c.1.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion (i + 1) Z →
      (c.1.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion (i + 1) Z →
        ‖X.noise i c - 1‖ ≤ ε) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion j Z →
      (b.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion j Z →
        ‖levelField X j b - 1‖ ≤ growthFactor L j * ε := by
  intro j
  induction j with
  | zero =>
    intro _ b ht hh
    have h := h0 b ht hh
    show ‖X.fine b - 1‖ ≤ growthFactor L 0 * ε
    simpa [growthFactor] using h
  | succ j ih =>
    intro hj'
    have hj : j < k := hj'
    have pos : ∀ b : Edge L n k (j + 1), b.IsPositivelyOriented →
        (b.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion (j + 1) Z →
        (b.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion (j + 1) Z →
        ‖levelField X (j + 1) b - 1‖ ≤ growthFactor L (j + 1) * ε := by
      intro b hb ht hh
      rw [levelField_succ_pos X hj hb]
      have hin : ∀ b' ∈ (PeriodicLattice.bondsInDoubleBlock b : Set (Edge L n k j)),
          ‖levelField X j b' - 1‖ ≤ growthFactor L j * ε := fun b' h' => by
        obtain ⟨h₁, h₂⟩ := G.double j hj Z b ht hh b' h'
        exact ih hj.le b' h₁ h₂
      have he : 0 ≤ growthFactor L j * ε := mul_nonneg (growthFactor_pos L j).le hε
      obtain ⟨-, -, hu⟩ := meanRadius_step_bounds hL G hA hX hj hb
        (fun x hx π => norm_contourHolonomy_sub_one_le G hj hb (hX.mem_specialUnitary hj.le) he
          hin hx π)
      have h₁ := norm_mul_sub_one_le (b := normalizedMean (levelField X j) b)
        (hX.real.1 ⟨j, hj⟩ ⟨b, hb⟩)
      have h₂ := hN ⟨j, hj⟩ ⟨b, hb⟩ ht hh
      rw [growthFactor_succ]
      have h₃ : ε ≤ growthFactor L j * ε := le_mul_of_one_le_left hε (one_le_growthFactor L j)
      nlinarith
    intro b ht hh
    by_cases hb : b.IsPositivelyOriented
    · exact pos b hb ht hh
    · have hr := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      rw [levelField_succ_neg X hj hb, norm_inv_sub_one (hX.mem_specialUnitary hj' _)]
      exact pos b.opposite hr hh ht
private theorem meanRadius_lower (hL : 0 < L) (G : BlockGeometry L n k) {ρ : ℝ}
    (hA : MeanIsCompactNearOne L n k ρ)
    {X : ChainPoint L n k} (hX : IsNearUnit ρ X) {Z : Set (Vertex L n k k)} {ε : ℝ} (hε : 0 ≤ ε)
    (h0 : ∀ b : Edge L n k 0, (b.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion 0 Z →
      (b.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion 0 Z → ‖X.fine b - 1‖ ≤ ε)
    (hN : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (c.1.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion (i + 1) Z →
      (c.1.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion (i + 1) Z →
        ‖X.noise i c - 1‖ ≤ ε)
    (i : Fin k) (c : PositiveEdge L n k (i + 1))
    (ht : (c.1.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion (i + 1) Z)
    (hh : (c.1.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion (i + 1) Z) :
    1 - (5 * L * (growthFactor L i * ε)) ^ 2 ≤ (meanRadius (levelField X i) c.1).re := by
  have he : 0 ≤ growthFactor L i * ε := mul_nonneg (growthFactor_pos L i).le hε
  have hin : ∀ b' ∈ (PeriodicLattice.bondsInDoubleBlock c.1 : Set (Edge L n k i)),
      ‖levelField X i b' - 1‖ ≤ growthFactor L i * ε := fun b' h' => by
    obtain ⟨h₁, h₂⟩ := G.double i i.2 Z c.1 ht hh b' h'
    exact norm_levelField_sub_one_le hL G hA hX hε h0 hN i i.2.le b' h₁ h₂
  exact (meanRadius_step_bounds hL G hA hX i.2 c.2
    (fun x hx π => norm_contourHolonomy_sub_one_le G i.2 c.2 (hX.mem_specialUnitary i.2.le) he
      hin hx π)).1
private theorem meanRadius_le_one (hL : 0 < L) (G : BlockGeometry L n k) {ρ : ℝ}
    (hA : MeanIsCompactNearOne L n k ρ)
    {X : ChainPoint L n k} (hX : IsNearUnit ρ X) (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    (meanRadius (levelField X i) c.1).re ≤ 1 := by
  refine (meanRadius_step_bounds (a := 2) hL G hA hX i.2 c.2 fun x _ π => ?_).2.1
  have h₁ := norm_of_mem_specialUnitary (contourHolonomy_mem (hX.mem_specialUnitary i.2.le) c.1 x π)
  have h₂ : ‖(1 : ComplexMatrix2)‖ = 1 :=
    norm_of_mem_specialUnitary ComplexMatrix2.specialUnitary.one_mem
  have h₃ := norm_sub_le (contourHolonomy (levelField X i) c.1 x π) 1
  rw [h₁, h₂] at h₃
  linarith
end Levels
section Sizes
variable {L n k : ℕ}
private theorem sq_norm_eq_halfTrace {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ‖A‖ ^ 2 = (ComplexMatrix2.halfTrace (A * A)).re := by
  obtain ⟨hs, ht⟩ := hA
  have h00 : star (A 0 0) = A 0 0 := by
    have h := congrFun (congrFun hs 0) 0
    simpa [Matrix.conjTranspose_apply] using h.symm
  have h10 : A 1 0 = star (A 0 1) := by
    have h := congrFun (congrFun hs 1) 0
    simpa [Matrix.conjTranspose_apply] using h
  have h11 : A 1 1 = -A 0 0 := by
    have h : Matrix.trace A = 0 := ht
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  set c : ℝ := Complex.normSq (A 0 0) + Complex.normSq (A 0 1) with hc
  have hcc : (c : ℂ) = A 0 0 * A 0 0 + A 0 1 * A 1 0 := by
    rw [hc]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self, h10]
    have e : (starRingEnd ℂ) (A 0 0) = A 0 0 := h00
    rw [e]
    have e' : star (A 0 1) = (starRingEnd ℂ) (A 0 1) := rfl
    rw [e']
    ring
  have hsq : A * A = (c : ℂ) • (1 : ComplexMatrix2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hcc, h11] <;> ring
  have hst : star A = A := hs.symm
  have hn : ‖A‖ * ‖A‖ = c := by
    rw [← CStarRing.norm_star_mul_self, hst, hsq, norm_smul,
      norm_of_mem_specialUnitary ComplexMatrix2.specialUnitary.one_mem, mul_one,
      Complex.norm_real, Real.norm_of_nonneg]
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  rw [hsq, sq, hn]
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul]
  ring
private theorem traceFinsumPairing_bounds {ι : Type} [Finite ι] {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (traceFinsumPairing f f).re ∧ ∀ i, ‖f i‖ ^ 2 ≤ (traceFinsumPairing f f).re := by
  let _ := Fintype.ofFinite ι
  have e : (traceFinsumPairing f f).re = ∑ i, ‖f i‖ ^ 2 := by
    rw [traceFinsumPairing, finsum_eq_sum_of_fintype, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => (sq_norm_eq_halfTrace (hf i)).symm
  rw [e]
  exact ⟨Finset.sum_nonneg fun i _ => by positivity, fun i =>
    Finset.single_le_sum (f := fun i => ‖f i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i)⟩
private theorem edgeFormPairing_bounds {j : ℕ} [Finite (PositiveEdge L n k j)]
    (B : edgeFormSpace L n k j) :
    0 ≤ (edgeFormPairing (B : Edge L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2)).re ∧
      ∀ b : Edge L n k j, b.IsPositivelyOriented →
        ‖(B : Edge L n k j → ComplexMatrix2) b‖ ^ 2 ≤
          (edgeFormPairing (B : Edge L n k j → ComplexMatrix2)
            (B : Edge L n k j → ComplexMatrix2)).re := by
  have h := traceFinsumPairing_bounds
    (f := restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2))
    fun b => B.2.1 b.1 b.2
  exact ⟨h.1, fun b hb => h.2 ⟨b, hb⟩⟩
private def IsUnitLevelForms (ξ : LevelForms L n k) : Prop :=
  (∀ b : Edge L n k 0, b.IsPositivelyOriented →
      ‖(ξ.1 : Edge L n k 0 → ComplexMatrix2) b‖ ≤ 1) ∧
    ∀ (i : Fin k) (b : Edge L n k (i + 1)), b.IsPositivelyOriented →
      ‖(ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) b‖ ≤ 1
private theorem levelFormsNormSq_nonneg (hfin : ∀ j, Finite (PositiveEdge L n k j))
    (ξ : LevelForms L n k) : 0 ≤ levelFormsNormSq ξ := by
  have := hfin 0
  have h₀ := (edgeFormPairing_bounds ξ.1).1
  have h₁ : 0 ≤ ∑ i : Fin k, (edgeFormPairing (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2)
      (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2)).re :=
    Finset.sum_nonneg fun i _ => by
      have := hfin (i + 1)
      exact (edgeFormPairing_bounds (ξ.2 i)).1
  exact add_nonneg h₀ h₁
private theorem isUnit_of_levelFormsNormSq_le (hfin : ∀ j, Finite (PositiveEdge L n k j))
    {ξ : LevelForms L n k} (h : levelFormsNormSq ξ ≤ 1) : IsUnitLevelForms ξ := by
  have e : levelFormsNormSq ξ = (edgeFormPairing (ξ.1 : Edge L n k 0 → ComplexMatrix2)
      (ξ.1 : Edge L n k 0 → ComplexMatrix2)).re + ∑ i : Fin k, (edgeFormPairing
      (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2)
      (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2)).re := rfl
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ (edgeFormPairing
      (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2)
      (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2)).re := fun i _ => by
    have := hfin (i + 1)
    exact (edgeFormPairing_bounds (ξ.2 i)).1
  have h₀ : 0 ≤ (edgeFormPairing (ξ.1 : Edge L n k 0 → ComplexMatrix2)
      (ξ.1 : Edge L n k 0 → ComplexMatrix2)).re := by
    have := hfin 0
    exact (edgeFormPairing_bounds ξ.1).1
  have hs := Finset.sum_nonneg hnn
  refine ⟨fun b hb => ?_, fun i b hb => ?_⟩
  · have := hfin 0
    have h₁ := (edgeFormPairing_bounds ξ.1).2 b hb
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by linarith)
  · have := hfin (i + 1)
    have h₁ := (edgeFormPairing_bounds (ξ.2 i)).2 b hb
    have h₂ := Finset.single_le_sum hnn (Finset.mem_univ i)
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by linarith)
private theorem isUnit_of_tripleNormSq_le (hfin : ∀ j, Finite (PositiveEdge L n k j))
    {τ : LevelTriple L n k} (h : tripleNormSq τ ≤ 1) : IsUnitLevelForms τ.1 := by
  have h₁ := levelFormsNormSq_nonneg hfin τ.2.1
  have h₂ : 0 ≤ topFormNormSq τ.2.2 := by
    have := hfin k
    exact (edgeFormPairing_bounds τ.2.2).1
  have e : tripleNormSq τ = levelFormsNormSq τ.1 + levelFormsNormSq τ.2.1 + topFormNormSq τ.2.2 :=
    rfl
  exact isUnit_of_levelFormsNormSq_le hfin (by linarith)
end Sizes
section Family
variable {L n k j : ℕ}
private theorem expTwist_of_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
private theorem expTwist_of_not_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
private theorem matExp_smul_I_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.ExpSurjective.matExp_I_smul_mem_specialUnitary <;> assumption
private theorem unit_mem_fieldSpace :
    (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j :=
  ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun _ => by simp⟩
private theorem expTwist_mem_fieldSpace
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A U : Edge L n k j → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k j)
    (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.expTwist A U ∈ fieldSpace L n k j := by apply _root_.YangMills.SharedProofs.p8814 <;> assumption
private theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p5970 <;> assumption
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p₀ : E}
private theorem analyticAt_inv {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀)
    (hu : (f p₀).det ≠ 0) :
    AnalyticAt ℝ (fun y => (f y)⁻¹) p₀ := by apply _root_.YangMills.SharedProofs.p24898 <;> assumption
private theorem analyticAt_const_smul (c : ℂ) {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => c • f p) p₀ := by apply _root_.YangMills.SharedProofs.p44577 <;> assumption
private theorem analyticAt_matExp {f : E → ComplexMatrix2} (hf : AnalyticAt ℝ f p₀) :
    AnalyticAt ℝ (fun p => ComplexMatrix2.matExp (f p)) p₀ :=
  AnalyticAt.comp (g := ComplexMatrix2.matExp) (NormedSpace.exp_analytic (𝕂 := ℝ) _) hf
private def planeCurve (ξ ξ' : LevelForms L n k) (w : ℝ × ℝ) : ChainPoint L n k :=
  expMove (w.1 • ξ + w.2 • ξ') (unitPoint L n k)
private theorem analyticAt_plane (B B' : ComplexMatrix2) :
    AnalyticAt ℝ (fun w : ℝ × ℝ => w.1 • B + w.2 • B') 0 :=
  (analyticAt_fst.smul analyticAt_const).add (analyticAt_snd.smul analyticAt_const)
private theorem planeCurve_isAnalyticFamily
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (ξ ξ' : LevelForms L n k) : IsAnalyticFamilyThroughUnit (planeCurve ξ ξ') 0 := by
  have hval : ∀ b : Edge L n k 0, AnalyticAt ℝ (fun w : ℝ × ℝ =>
      ComplexMatrix2.matExp (Complex.I •
        (w.1 • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b +
          w.2 • (ξ'.1 : Edge L n k 0 → ComplexMatrix2) b))) 0 := fun b =>
    analyticAt_matExp (analyticAt_const_smul _ (analyticAt_plane _ _))
  refine ⟨?_, fun b => ?_, fun i c => ?_, ?_⟩
  · simp [planeCurve, expMove_zero_unitPoint]
  · by_cases hb : b.IsPositivelyOriented
    · refine (hval b).congr (Eventually.of_forall fun w => ?_)
      show _ = PeriodicLattice.expTwist _ _ b
      rw [expTwist_of_pos hb]
      simp [unitPoint]
    · refine (analyticAt_inv (hval b.opposite) ?_).congr (Eventually.of_forall fun w => ?_)
      · simp [NormedSpace.exp_zero]
      · show _ = PeriodicLattice.expTwist _ _ b
        rw [expTwist_of_not_pos hb]
        simp [unitPoint]
  · refine (analyticAt_matExp (analyticAt_const_smul Complex.I
      (analyticAt_plane ((ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1)
      ((ξ'.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1)))).congr
      (Eventually.of_forall fun w => ?_)
    simp [planeCurve, expMove, unitPoint]
  · refine Eventually.of_forall fun w => ⟨expTwist_mem_fieldSpace hx (w.1 • ξ + w.2 • ξ').1.2
      unit_mem_fieldSpace, fun i c => ?_⟩
    have h : ((w.1 • ξ + w.2 • ξ').2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 ∈
        ComplexMatrix2.hermitianTraceless :=
      ((w.1 • ξ + w.2 • ξ').2 i).2.1 c.1 c.2
    simpa [planeCurve, expMove, unitPoint] using matExp_smul_I_mem h
end Family
section Lengths
variable {L n k : ℕ}
private def radiusAlong (ξ ξ' : LevelForms L n k) (p : NoiseIndex L n k) (s t : ℝ) : ℝ :=
  (meanRadius (levelField (planeCurve ξ ξ' (s, t)) p.1) p.2.1).re
private theorem planeCurve_facts (hF : LevelFieldsAnalyticAlongFamily)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {ρ : ℝ} (hρ : 0 < ρ)
    (ξ ξ' : LevelForms L n k) :
    (∀ p : NoiseIndex L n k,
      ContDiffAt ℝ 2 (fun w : ℝ × ℝ => radiusAlong ξ ξ' p w.1 w.2) 0 ∧
        radiusAlong ξ ξ' p 0 0 = 1) ∧
      ∀ᶠ w : ℝ × ℝ in 𝓝 0, IsNearUnit ρ (planeCurve ξ ξ' w) := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  obtain ⟨h₁, h₂, h₃⟩ := hF L hL k n hk hn (ℝ × ℝ) (planeCurve ξ ξ') 0
    (planeCurve_isAnalyticFamily hx ξ ξ')
  have hfin : ∀ j, Finite (Edge L n k j) := fun j => by
    have : NeZero L := ⟨by omega⟩
    exact PeriodicLattice.instFiniteBond _
  refine ⟨fun p => ⟨?_, ?_⟩, ?_⟩
  · have h := (h₂ p.1 p.2).1
    exact ((Complex.reCLM.analyticAt _).comp h).contDiffAt
  · show (meanRadius (levelField (planeCurve ξ ξ' 0) p.1) p.2.1).re = 1
    rw [(h₂ p.1 p.2).2]
    simp
  · have near : ∀ j ∈ Finset.range (k + 1), ∀ᶠ w in 𝓝 (0 : ℝ × ℝ), ∀ b : Edge L n k j,
        ComplexMatrix2.operatorNorm (levelField (planeCurve ξ ξ' w) j b - 1) < ρ := by
      intro j hj
      have := hfin j
      have hj' : j ≤ k := by
        have := Finset.mem_range.1 hj
        omega
      refine eventually_all.2 fun b => ?_
      obtain ⟨ha, hv⟩ := h₁ j hj' b
      have h₄ := ha.continuousAt.eventually (Metric.ball_mem_nhds _ hρ)
      filter_upwards [h₄] with w hw
      have h₅ := Metric.mem_ball.1 hw
      rw [dist_eq_norm, hv] at h₅
      exact h₅
    filter_upwards [(eventually_all_finset _).2 near, h₃] with w h₄ h₅
    exact ⟨h₅, fun j hj => h₄ j (Finset.mem_range.2 (by omega))⟩
private theorem norm_matExp_sub_one_le (hEL : ComplexMatrix2.ExpLogEstimates) {B : ComplexMatrix2}
    {u : ℝ} (hB : ‖B‖ ≤ 1) (hu : |u| ≤ 1) :
    ‖ComplexMatrix2.matExp (Complex.I • (u • B)) - 1‖ ≤ 2 * |u| := by
  have h1 := (hEL.1 (Complex.I • (u • B))).2
  have hn : ‖Complex.I • (u • B)‖ ≤ |u| := by
    rw [norm_smul, norm_smul]
    simp only [Complex.norm_I, one_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg u) hB
  have h3 := Real.abs_exp_sub_one_le (x := ‖Complex.I • (u • B)‖)
    (by rw [abs_of_nonneg (norm_nonneg _)]; exact hn.trans hu)
  rw [abs_of_nonneg (norm_nonneg (Complex.I • (u • B)))] at h3
  linarith [le_abs_self (Real.exp ‖Complex.I • (u • B)‖ - 1)]
private theorem norm_matExp_value_sub_one_le (hEL : ComplexMatrix2.ExpLogEstimates)
    (G : BlockGeometry L n k)
    {j : ℕ} (hj : j ≤ k) {B : Edge L n k j → ComplexMatrix2} {y : Vertex L n k k}
    (hc : FormSupportedInCell y B)
    (hB : ∀ b : Edge L n k j, b.IsPositivelyOriented → ‖B b‖ ≤ 1) {Z : Set (Vertex L n k k)}
    {u : ℝ} (hu : |u| ≤ 1) {b : Edge L n k j} (hb : b.IsPositivelyOriented)
    (ht : (b.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion j Z) :
    ‖ComplexMatrix2.matExp (Complex.I • (u • B b)) - 1‖ ≤
      (open Classical in if y ∈ Z then 2 * |u| else 0) := by
  classical
  by_cases hy : levelVertexCell b.source = y
  · have h := G.cell_of j hj Z b.source ht
    rw [hy] at h
    rw [if_pos h]
    exact norm_matExp_sub_one_le hEL (hB b hb) hu
  · have h0 : B b = 0 := hc ⟨b, hb⟩ hy
    have he : ComplexMatrix2.matExp (0 : ComplexMatrix2) = 1 := NormedSpace.exp_zero
    rw [h0]
    simp only [smul_zero, he, sub_self, norm_zero]
    split_ifs
    · positivity
    · exact le_rfl
private theorem expMove_near (hEL : ComplexMatrix2.ExpLogEstimates) (G : BlockGeometry L n k)
    {ξ : LevelForms L n k} {y : Vertex L n k k} (hc : LevelFormsSupportedInCell y ξ)
    (hξ : IsUnitLevelForms ξ) {Z : Set (Vertex L n k k)} {u : ℝ} (hu : |u| ≤ 1) :
    (∀ b : Edge L n k 0, (b.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion 0 Z →
      (b.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion 0 Z →
      ‖(expMove (u • ξ) (unitPoint L n k)).fine b - 1‖ ≤
        (open Classical in if y ∈ Z then 2 * |u| else 0)) ∧
    ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (c.1.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion (i + 1) Z →
      (c.1.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion (i + 1) Z →
      ‖(expMove (u • ξ) (unitPoint L n k)).noise i c - 1‖ ≤
        (open Classical in if y ∈ Z then 2 * |u| else 0) := by
  refine ⟨fun b ht hh => ?_, fun i c ht _ => ?_⟩
  · show ‖PeriodicLattice.expTwist ((u • ξ).1 : Edge L n k 0 → ComplexMatrix2) (fun _ => 1) b - 1‖
      ≤ _
    by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_of_pos hb, mul_one]
      exact norm_matExp_value_sub_one_le hEL G (Nat.zero_le k) hc.1 hξ.1 hu hb ht
    · have hr := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      have hm : ComplexMatrix2.matExp
          (Complex.I • ((u • ξ).1 : Edge L n k 0 → ComplexMatrix2) b.opposite) ∈
            ComplexMatrix2.specialUnitary :=
        matExp_smul_I_mem ((u • ξ).1.2.1 _ hr)
      rw [expTwist_of_not_pos hb, mul_one, norm_inv_sub_one hm]
      exact norm_matExp_value_sub_one_le hEL G (Nat.zero_le k) hc.1 hξ.1 hu hr hh
  · show ‖ComplexMatrix2.matExp
      (Complex.I • ((u • ξ).2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) * 1 - 1‖ ≤ _
    rw [mul_one]
    exact norm_matExp_value_sub_one_le hEL G i.2 (hc.2 i) (hξ.2 i) hu c.2 ht
private theorem cellsRegion_mono {j : ℕ} {Z Z' : Set (Vertex L n k k)} (h : Z ⊆ Z') :
    cellsRegion j Z ⊆ cellsRegion j Z' :=
  Set.biUnion_subset_biUnion_left h
private def edgeCells (p : NoiseIndex L n k) : Set (Vertex L n k k) :=
  {levelVertexCell p.2.1.source, levelVertexCell p.2.1.target}
private def departureRate (p : NoiseIndex L n k) (y : Vertex L n k k) : ℝ :=
  open Classical in if y ∈ edgeCells p then 10 * L * growthFactor L p.1 else 0
private theorem departureRate_nonneg (p : NoiseIndex L n k) (y : Vertex L n k k) :
    0 ≤ departureRate p y := by
  unfold departureRate
  split_ifs
  · have := growthFactor_pos L p.1
    positivity
  · exact le_rfl
private theorem radius_lower_along_axis (hL : 0 < L) (hEL : ComplexMatrix2.ExpLogEstimates)
    (G : BlockGeometry L n k) {ρ : ℝ} (hA : MeanIsCompactNearOne L n k ρ) {ξ : LevelForms L n k}
    {y : Vertex L n k k} (hc : LevelFormsSupportedInCell y ξ) (hξ : IsUnitLevelForms ξ)
    {u : ℝ} (hu : |u| ≤ 1) (hX : IsNearUnit ρ (expMove (u • ξ) (unitPoint L n k)))
    (p : NoiseIndex L n k) :
    1 - departureRate p y ^ 2 * u ^ 2 ≤
      (meanRadius (levelField (expMove (u • ξ) (unitPoint L n k)) p.1) p.2.1).re := by
  classical
  have ht : (p.2.1.source : PeriodicLattice.FourTorus L n) ∈ cellsRegion (p.1 + 1) (edgeCells p) :=
    cellsRegion_mono (by simp [edgeCells]) (G.cell_mem _ p.1.2 p.2.1.source)
  have hh : (p.2.1.target : PeriodicLattice.FourTorus L n) ∈ cellsRegion (p.1 + 1) (edgeCells p) :=
    cellsRegion_mono (by simp [edgeCells]) (G.cell_mem _ p.1.2 p.2.1.target)
  obtain ⟨h₁, h₂⟩ := expMove_near hEL G hc hξ (Z := edgeCells p) hu
  have hε : (0 : ℝ) ≤ (open Classical in if y ∈ edgeCells p then 2 * |u| else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  have h := meanRadius_lower hL G hA hX hε h₁ h₂ p.1 p.2 ht hh
  have e : (5 * (L : ℝ) * (growthFactor L p.1 *
      (open Classical in if y ∈ edgeCells p then 2 * |u| else 0))) ^ 2 =
        departureRate p y ^ 2 * u ^ 2 := by
    unfold departureRate
    split_ifs
    · rw [← sq_abs u]
      ring
    · simp
  rw [e] at h
  exact h
private theorem radius_partials_bounds (hF : LevelFieldsAnalyticAlongFamily)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    (hEL : ComplexMatrix2.ExpLogEstimates) (G : BlockGeometry L n k) {ρ : ℝ} (hρ : 0 < ρ)
    (hA : MeanIsCompactNearOne L n k ρ) {ξ ξ' : LevelForms L n k} {y y' : Vertex L n k k}
    (hc : LevelFormsSupportedInCell y ξ) (hc' : LevelFormsSupportedInCell y' ξ')
    (hξ : IsUnitLevelForms ξ) (hξ' : IsUnitLevelForms ξ') (p : NoiseIndex L n k) :
    deriv (fun s => radiusAlong ξ ξ' p s 0) 0 = 0 ∧ deriv (fun t => radiusAlong ξ ξ' p 0 t) 0 = 0 ∧
      |deriv (fun s => deriv (fun t => radiusAlong ξ ξ' p s t) 0) 0| ≤
        2 * departureRate p y * departureRate p y' := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨h₁, h₂⟩ := planeCurve_facts hF hL hn hk hρ ξ ξ'
  have t₁ : Tendsto (fun u : ℝ => ((u, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
    have h : Continuous fun u : ℝ => ((u, 0) : ℝ × ℝ) := by fun_prop
    exact h.tendsto 0
  have t₂ : Tendsto (fun u : ℝ => ((0, u) : ℝ × ℝ)) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
    have h : Continuous fun u : ℝ => ((0, u) : ℝ × ℝ) := by fun_prop
    exact h.tendsto 0
  have small : ∀ᶠ u : ℝ in 𝓝 0, |u| ≤ 1 := by
    have h : ∀ᶠ u : ℝ in 𝓝 0, u ∈ Metric.ball (0 : ℝ) 1 := Metric.ball_mem_nhds _ one_pos
    filter_upwards [h] with u hu
    have := Metric.mem_ball.1 hu
    rw [Real.dist_eq, sub_zero] at this
    exact this.le
  refine abs_mixed_deriv_le_of_isLocalMax (h₁ p).1 (h₁ p).2 ?_ (departureRate_nonneg p y)
    (departureRate_nonneg p y') ?_ ?_
  · filter_upwards [h₂] with w hw
    exact meanRadius_le_one hL0 G hA hw p.1 p.2
  · filter_upwards [t₁.eventually h₂, small] with u hg hu
    have e : planeCurve ξ ξ' (u, 0) = expMove (u • ξ) (unitPoint L n k) := by simp [planeCurve]
    rw [e] at hg
    have := radius_lower_along_axis hL0 hEL G hA hc hξ hu hg p
    simpa [radiusAlong, e] using this
  · filter_upwards [t₂.eventually h₂, small] with u hg hu
    have e : planeCurve ξ ξ' (0, u) = expMove (u • ξ') (unitPoint L n k) := by simp [planeCurve]
    rw [e] at hg
    have := radius_lower_along_axis hL0 hEL G hA hc' hξ' hu hg p
    simpa [radiusAlong, e] using this
end Lengths
section Diagonal
variable {L n k : ℕ}
private theorem diagonal_isLocalOnCells {ι : Type} [Fintype ι] [DecidableEq ι]
    (hself : ∀ y : Vertex L n k k, cellDist y y = 0) (c : ι → Vertex L n k k) (v : ι → ℂ)
    {M θ : ℝ} {m : Vertex L n k k → ℝ} (hM : 0 ≤ M) (hm : ∀ y, 0 ≤ m y)
    (hv : ∀ p, ‖v p‖ ≤ M * m (c p)) : IsLocalOnCells c c (Matrix.diagonal v) M θ m := by
  classical
  intro y' y
  have e : blockBetween c c (Matrix.diagonal v) y' y =
      Matrix.diagonal fun p => if c p = y' ∧ c p = y then v p else 0 := by
    ext p q
    by_cases h : p = q
    · subst h
      simp [blockBetween]
    · simp [blockBetween, Matrix.diagonal_apply_ne _ h]
  have hnn : 0 ≤ M * Real.exp (-(θ * cellDist y' y)) * m y' :=
    mul_nonneg (mul_nonneg hM (Real.exp_pos _).le) (hm _)
  rw [e, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun p => ?_
  split_ifs with h
  · obtain ⟨h₁, h₂⟩ := h
    have hy : y' = y := h₁.symm.trans h₂
    subst hy
    rw [hself, mul_zero, neg_zero, Real.exp_zero, mul_one, ← h₁]
    exact hv p
  · simpa using hnn
end Diagonal
theorem noiseRadiusMatrixIsLocal_of (hF : LevelFieldsAnalyticAlongFamily)
    (hR : NormalizedMeanOfCompactField)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hP : PeriodicLattice.BlockPaths.Statement)
    (hl : AxisOrderLegsAreContours)
    (hBB : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hCr : PeriodicLattice.CrossingsAndBareBlocks.Statement)
    (hCell : NeighbouringFineVertexCells)
    (hTop : TopEdgesAndCubes) :
    NoiseRadiusMatrixIsLocal := by
  intro L hL k hk
  obtain ⟨ρ, hρ, H⟩ := hR L hL
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hLR : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  set D : ℝ := 4 * (L : ℝ) ^ k with hD
  set A : ℝ := 10 * L * growthFactor L k with hAdef
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) (growthFactor_pos L k).le
  have hD0 : 0 ≤ D := by positivity
  set M : ℝ := (1 + 2 * A * A) * Real.exp (2 * D) with hMdef
  have hM1 : 1 ≤ M := by
    have h₁ : 1 ≤ Real.exp (2 * D) := Real.one_le_exp (by positivity)
    have h₂ : 1 ≤ 1 + 2 * A * A := by nlinarith
    nlinarith
  have hM0 : 0 ≤ M := by linarith
  refine ⟨M, 1, by linarith, one_pos, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro _ _
  have G : BlockGeometry L n k := blockGeometry_holds hL hn hk hP hl hBB hCr hCell hTop
  have hAv : MeanIsCompactNearOne L n k ρ := fun j hj V hV hs c hc => H n k j hn hj V hV hs c hc
  have hfin : ∀ j, Finite (PositiveEdge L n k j) := fun j => by
    have : NeZero L := ⟨by omega⟩
    have : Finite (Edge L n k j) := PeriodicLattice.instFiniteBond _
    exact Subtype.finite
  have ezero : noiseRadiusMatrix (0 : LevelTriple L n k) = 1 := by
    rw [← Matrix.diagonal_one]
    show Matrix.diagonal _ = _
    congr 1
    funext p
    have h := ((planeCurve_facts hF hL hn hk hρ (0 : LevelForms L n k) 0).1 p).2
    have e : planeCurve (0 : LevelForms L n k) 0 (0, 0) = expMove 0 (unitPoint L n k) := by
      simp [planeCurve]
    simp only [radiusAlong, e] at h
    show (((meanRadius (levelField (expMove 0 (unitPoint L n k)) p.1) p.2.1).re : ℝ) : ℂ) = 1
    rw [h]
    simp
  refine ⟨by rw [ezero]; simp, ?_, ?_⟩
  · rw [ezero, inv_one, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun p => ?_
    simpa using hM1
  intro y y' τ τ' h₁ h₂ h₃ h₄
  have u₁ := isUnit_of_tripleNormSq_le hfin h₃
  have u₂ := isUnit_of_tripleNormSq_le hfin h₄
  have eT : (fun s t : ℝ => noiseRadiusMatrix (s • τ + t • τ')) =
      fun s t => Matrix.diagonal fun p => ((radiusAlong τ.1 τ'.1 p s t : ℝ) : ℂ) := rfl
  rw [eT]
  obtain ⟨f₁, -⟩ := planeCurve_facts hF hL hn hk hρ τ.1 τ'.1
  have B := fun p => radius_partials_bounds hF hL hn hk hEL G hρ hAv h₁.1 h₂.1 u₁ u₂ p
  have hw : ∀ y₀ y₁ : Vertex L n k k, 0 ≤ cellDecayWeight 1 y₀ y₁ := fun _ _ => (Real.exp_pos _).le
  refine ⟨fun p q => ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : p = q
    · subst h
      simp only [Matrix.diagonal_apply_eq]
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (f₁ p).1
    · simp only [Matrix.diagonal_apply_ne _ h]
      exact contDiffAt_const
  · refine diagonal_isLocalOnCells G.self _ _ hM0 (fun _ => zero_le_one) fun p => ?_
    rw [(f₁ p).2]
    simpa using hM1
  · have e : derivFirst (fun s t : ℝ => Matrix.diagonal fun p =>
        ((radiusAlong τ.1 τ'.1 p s t : ℝ) : ℂ)) = Matrix.diagonal fun _ => 0 := by
      ext p q
      by_cases h : p = q
      · subst h
        simp only [derivFirst, Matrix.diagonal_apply_eq]
        rw [deriv_ofReal_comp (differentiable_partials (f₁ p).1).1, (B p).1]
        simp
      · simp [derivFirst, Matrix.diagonal_apply_ne _ h]
    rw [e]
    exact diagonal_isLocalOnCells G.self _ _ hM0 (hw y) fun p => by
      simpa using mul_nonneg hM0 (hw y _)
  · have e : derivSecond (fun s t : ℝ => Matrix.diagonal fun p =>
        ((radiusAlong τ.1 τ'.1 p s t : ℝ) : ℂ)) = Matrix.diagonal fun _ => 0 := by
      ext p q
      by_cases h : p = q
      · subst h
        simp only [derivSecond, Matrix.diagonal_apply_eq]
        rw [deriv_ofReal_comp (differentiable_partials (f₁ p).1).2.1, (B p).2.1]
        simp
      · simp [derivSecond, Matrix.diagonal_apply_ne _ h]
    rw [e]
    exact diagonal_isLocalOnCells G.self _ _ hM0 (hw y') fun p => by
      simpa using mul_nonneg hM0 (hw y' _)
  · have e : derivMixed (fun s t : ℝ => Matrix.diagonal fun p =>
        ((radiusAlong τ.1 τ'.1 p s t : ℝ) : ℂ)) = Matrix.diagonal fun p =>
        ((deriv (fun s => deriv (fun t => radiusAlong τ.1 τ'.1 p s t) 0) 0 : ℝ) : ℂ) := by
      ext p q
      by_cases h : p = q
      · subst h
        simp only [derivMixed, Matrix.diagonal_apply_eq]
        exact mixedDeriv_ofReal_comp (f₁ p).1
      · simp [derivMixed, Matrix.diagonal_apply_ne _ h]
    rw [e]
    refine diagonal_isLocalOnCells G.self _ _ hM0
      (fun u => mul_nonneg (hw y u) (hw y' u)) fun p => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (B p).2.2.trans ?_
    have hslope : ∀ y₀ : Vertex L n k k, departureRate p y₀ ≤ A * Real.exp D *
        cellDecayWeight 1 y₀ (noiseIndexCell p) := by
      intro y₀
      have hr : growthFactor L p.1 ≤ growthFactor L k :=
        pow_le_pow_right₀ (by linarith) p.1.2.le
      unfold departureRate
      split_ifs with hy
      · have hd : cellDist (noiseIndexCell p) y₀ ≤ D := by
          rcases hy with rfl | hy
          · exact (G.self _).le.trans hD0
          · rw [Set.mem_singleton_iff] at hy
            rw [hy]
            exact G.near p.1 p.1.2 p.2.1 p.2.2
        have h₅ : 1 ≤ Real.exp D * cellDecayWeight 1 y₀ (noiseIndexCell p) := by
          rw [cellDecayWeight, ← Real.exp_add]
          exact Real.one_le_exp (by linarith)
        have h₆ : 10 * (L : ℝ) * growthFactor L p.1 ≤ A :=
          mul_le_mul_of_nonneg_left hr (by positivity)
        calc 10 * (L : ℝ) * growthFactor L p.1 ≤ A := h₆
          _ ≤ A * (Real.exp D * cellDecayWeight 1 y₀ (noiseIndexCell p)) :=
            le_mul_of_one_le_right hA0 h₅
          _ = _ := by ring
      · exact mul_nonneg (mul_nonneg hA0 (Real.exp_pos _).le) (hw _ _)
    have hs₁ := hslope y
    have hs₂ := hslope y'
    have hp₁ := departureRate_nonneg p y
    have hp₂ := departureRate_nonneg p y'
    set w₁ := cellDecayWeight 1 y (noiseIndexCell p)
    set w₂ := cellDecayWeight 1 y' (noiseIndexCell p)
    have hw₁ : 0 ≤ w₁ := hw _ _
    have hw₂ : 0 ≤ w₂ := hw _ _
    have hE : 0 ≤ Real.exp D := (Real.exp_pos _).le
    have hm := mul_le_mul hs₁ hs₂ hp₂ (mul_nonneg (mul_nonneg hA0 hE) hw₁)
    have e₂ : Real.exp (2 * D) = Real.exp D * Real.exp D := by
      rw [← Real.exp_add]
      ring_nf
    show 2 * departureRate p y * departureRate p y' ≤
      (1 + 2 * A * A) * Real.exp (2 * D) * (w₁ * w₂)
    rw [e₂]
    have hnn : 0 ≤ Real.exp D * Real.exp D * (w₁ * w₂) := by positivity
    nlinarith [hm, hnn]
end YangMills.Construction.RunningCouplingSlope.NoiseRadiusLocal
end
