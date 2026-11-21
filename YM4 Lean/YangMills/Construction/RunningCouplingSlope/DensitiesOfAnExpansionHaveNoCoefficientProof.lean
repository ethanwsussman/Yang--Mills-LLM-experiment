import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.RunningCouplingSlope.CoefficientOfTheLeastAction
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficient
import YangMills.Construction.RunningCouplingSlope.DensitiesOfAnExpansionHaveNoCoefficient
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsLocalProof
import YangMills.Construction.RunningCouplingSlope.NumberOfALocalDensity
import YangMills.Construction.RunningCouplingSlope.TotalAtTheLeastFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.TiltOfTheImageProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open Filter
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps SlopeCoefficient
namespace RunningCouplingSlope.ColdDensitiesZeroCoefficientProof
section Cold
variable {n : ℕ}
theorem norm_coe_inv_sub_one (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem norm_coe_mul_sub_one_le (g h : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ + ‖(h : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
theorem isCold_of_forall_norm_sub_one_lt {s : ℝ} {W : TorusField n}
    (h : ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < s / 4) : IsCold s W := by
  intro x μ ν _
  unfold curvature holonomy
  have a1 := norm_coe_mul_sub_one_le (W x μ * W (x + TorusFields.unitStep n μ) ν * (W (x + TorusFields.unitStep n ν) μ)⁻¹) (W x ν)⁻¹
  have a2 := norm_coe_mul_sub_one_le (W x μ * W (x + TorusFields.unitStep n μ) ν) (W (x + TorusFields.unitStep n ν) μ)⁻¹
  have a3 := norm_coe_mul_sub_one_le (W x μ) (W (x + TorusFields.unitStep n μ) ν)
  rw [norm_coe_inv_sub_one] at a1 a2
  have b1 := h x μ
  have b2 := h (x + TorusFields.unitStep n μ) ν
  have b3 := h (x + TorusFields.unitStep n ν) μ
  have b4 := h x ν
  linarith
theorem eventually_norm_sub_one_lt [NeZero n] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ V in 𝓝 (trivialField n), ∀ x i, ‖((V x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < ε := by apply _root_.YangMills.SharedProofs.p18107 <;> assumption
theorem exists_bond_of_transports [NeZero n] (g : TorusIsometry) {W W' : TorusField n}
    (h : g.Transports W W') (y : TorusSite n) (j : Fin 4) :
    ∃ (x : TorusSite n) (k : Fin 4), W' y j = W x k ∨ (W' y j)⁻¹ = W x k := by apply _root_.YangMills.SharedProofs.p7027 <;> assumption
theorem isCold_of_transports [NeZero n] (g : TorusIsometry) {W W' : TorusField n} {s : ℝ}
    (h : g.Transports W W')
    (hW : ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < s / 4) : IsCold s W' := by
  refine isCold_of_forall_norm_sub_one_lt fun y j => ?_
  obtain ⟨x, k, e | e⟩ := exists_bond_of_transports g h y j
  · rw [e]
    exact hW x k
  · have := hW x k
    rw [← e, norm_coe_inv_sub_one] at this
    exact this
theorem norm_trivialField_sub_one_lt {s : ℝ} (hs : 0 < s) (x : TorusSite n) (i : Fin 4) :
    ‖((trivialField n x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < s / 4 := by
  simp [trivialField]
  positivity
end Cold
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem fderiv_fderiv_comp_clm {Ψ : F → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ 0) (L : E →L[ℝ] F) (u v : E) :
    fderiv ℝ (fderiv ℝ (Ψ ∘ L)) 0 u v = fderiv ℝ (fderiv ℝ Ψ) 0 (L u) (L v) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.secondDeriv_comp_clm <;> assumption
end Calculus
section Scaling
variable {n : ℕ}
theorem mixedDeriv_smul {g : TorusField n → ℝ} (c c' : TorusBond n) (X X' : imaginaryQuaternions)
    (hs : ContDiffAt ℝ 2 (fun σ : Fin 2 → ℝ => g (perturb ![c, c'] ![X, X'] σ (trivialField n))) 0) (r r' : ℝ) :
    mixedDeriv g (trivialField n) ![c, c'] ![r • X, r' • X'] =
      r * r' * mixedDeriv g (trivialField n) ![c, c'] ![X, X'] := by
  let S : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi fun l => (if l = 0 then r else r') • ContinuousLinearMap.proj l
  have hcomp : (fun σ : Fin 2 → ℝ => g (perturb ![c, c'] ![r • X, r' • X'] σ (trivialField n))) =
      (fun σ : Fin 2 → ℝ => g (perturb ![c, c'] ![X, X'] σ (trivialField n))) ∘ S := by
    funext σ
    simp only [Function.comp]
    congr 1
    funext x i
    simp [perturb, Fin.sum_univ_two, S, smul_smul, mul_comm]
  have s0 : S (Pi.single 0 1) = r • Pi.single 0 1 := by
    funext l
    fin_cases l <;> simp [S]
  have s1 : S (Pi.single 1 1) = r' • Pi.single 1 1 := by
    funext l
    fin_cases l <;> simp [S]
  unfold mixedDeriv
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hcomp, fderiv_fderiv_comp_clm hs]
  simp only [s0, s1, map_smul, smul_apply, smul_eq_mul]
  ring
theorem mixedDeriv_sub_const (g : TorusField n → ℝ) (C : ℝ) {k : Fin 2 → TorusBond n}
    (X : Fin 2 → imaginaryQuaternions) :
    mixedDeriv (fun V => g V - C) (trivialField n) k X = mixedDeriv g (trivialField n) k X := by
  unfold mixedDeriv
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  have e : fderiv ℝ (fun σ : Fin 2 → ℝ => g (perturb k X σ (trivialField n)) - C) =
      fderiv ℝ (fun σ : Fin 2 → ℝ => g (perturb k X σ (trivialField n))) := by
    funext σ
    exact fderiv_sub_const _
  rw [e]
end Scaling
section Expansion
variable {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity}
theorem isCold_trivialField {n : ℕ} (hσ : 0 < ℓ.threshold) : IsCold ℓ.threshold (trivialField n) :=
  isCold_of_forall_norm_sub_one_lt fun y i => norm_trivialField_sub_one_lt hσ y i
theorem centeredDensityTotal_eq_sum {n : ℕ} [NeZero n] (V : TorusField n) :
    centeredDensityTotal f n V = ∑ y, centered f n y V := by
  simp [centeredDensityTotal, NeZero.ne n]
theorem minimalActionTotal_eq {n : ℕ} [NeZero n] (a : ℝ) (L t : ℕ) (V : TorusField n) :
    minimalActionTotal a L t n V = actionAtLevel a L t Finset.univ V := by
  simp [minimalActionTotal, NeZero.ne n]
theorem eventually_isCold {n : ℕ} [NeZero n] (hσ : 0 < ℓ.threshold) :
    ∀ᶠ V in 𝓝 (trivialField n), IsCold ℓ.threshold V :=
  (eventually_norm_sub_one_lt (show 0 < ℓ.threshold / 4 by positivity)).mono
    fun _ hV => isCold_of_forall_norm_sub_one_lt hV
theorem isGaugeTotalAt_of_coldExpansion (hσ : 0 < ℓ.threshold) (harr : IsInvariantFunctionalAbove ℓ D)
    (hrow : ColdExpansion ℓ t x D f) {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n)
    (hact : IsGaugeTotalAt (minimalActionTotal ℓ.coupling ℓ.side t) n) :
    IsGaugeTotalAt (centeredDensityTotal f) n where
  contDiffAt_perturb := fun k c X => by
    have e : (fun σ : Fin k → ℝ => centeredDensityTotal f n (perturb c X σ (trivialField n))) =
        fun σ => ∑ y, (f n y (perturb c X σ (trivialField n)) - f n y (trivialField n)) := by
      funext σ
      rw [centeredDensityTotal_eq_sum]
      rfl
    rw [e]
    refine ContDiffAt.sum fun y _ => ?_
    exact ((hrow.smooth n hn y (trivialField n) (isCold_trivialField hσ) k c X).of_le (by norm_num)).sub
      contDiffAt_const
  gauge_invariant_near := by
    have hc : Tendsto (Prod.snd : (TorusSite n → UnitQuaternion) × TorusField n → TorusField n)
        (𝓝 (1, trivialField n)) (𝓝 (trivialField n)) :=
      continuous_snd.tendsto _
    filter_upwards [hc.eventually (eventually_isCold hσ)] with p hp
    rw [centeredDensityTotal_eq_sum, centeredDensityTotal_eq_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [centered]
    rw [hrow.gauge n hn y p.1 p.2 hp]
  constant_gauge_invariant := fun g => by
    filter_upwards [eventually_isCold hσ] with V hV
    rw [centeredDensityTotal_eq_sum, centeredDensityTotal_eq_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [centered]
    rw [hrow.gauge n hn y _ V hV]
  isometry_invariant := fun g => by
    filter_upwards [eventually_norm_sub_one_lt (n := n) (show 0 < ℓ.threshold / 4 by positivity),
      hact.isometry_invariant g] with V hV hA V' hc
    have cV := isCold_of_forall_norm_sub_one_lt hV
    have cV' := isCold_of_transports g hc hV
    have f1 := hrow.form n hn V cV
    have f2 := hrow.form n hn V' cV'
    have hD := (harr n hn).2.2.2 g V V' hc
    have hA' := hA V' hc
    rw [minimalActionTotal_eq, minimalActionTotal_eq] at hA'
    rw [centeredDensityTotal_eq_sum, centeredDensityTotal_eq_sum]
    rw [hD, hA'] at f2
    linarith
theorem div_weight_le (hrt : 0 < ℓ.rt) (hE : 0 ≤ ℓ.E) (m : ℕ) :
    ℓ.E / ℓ.weight m ≤ ℓ.E * Real.exp (-(ℓ.weightRate * m)) := by
  unfold StepParameters.weight
  have h1 : Real.exp (ℓ.weightRate * m) ≤
      max 1 (((m : ℝ) / ℓ.n₁) ^ 16000) * Real.exp (ℓ.weightRate * m) :=
    le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hE (Real.exp_pos _) h1
theorem weightRate_pos (hrt : 0 < ℓ.rt) : 0 < ℓ.weightRate := by
  unfold StepParameters.weightRate
  positivity
theorem areUnitVectors_pair {X X' : imaginaryQuaternions} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    AreUnitVectors ![X, X'] := by apply _root_.YangMills.SharedProofs.p1051 <;> assumption
theorem exists_tendsto_mixedDeriv_of_unit (hσ : 0 < ℓ.threshold) (hrt : 0 < ℓ.rt) (hE : 0 ≤ ℓ.E)
    (hn₀ : 0 < ℓ.n₀) (hrow : ColdExpansion ℓ t x D f)
    (c c' : LatticeBond) {X X' : imaginaryQuaternions} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) :
    ∃ v : ℝ, Tendsto (fun n : ℕ => mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'])
      atTop (𝓝 v) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hlim : Tendsto (fun m : ℕ => ℓ.E * Real.exp (-(ℓ.weightRate * m))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ℓ.weightRate * (m : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (weightRate_pos hrt)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul ℓ.E
    simpa [Function.comp_def] using h2
  have hbig := (hlim.eventually (gt_mem_nhds hε)).and
    (eventually_ge_atTop (offsetNorm c.1 + offsetNorm c'.1 + 1))
  obtain ⟨m, hm1, hm2⟩ := hbig.exists
  have hbox : ∀ b : LatticeBond, offsetNorm b.1 + 1 ≤ m → TorusFields.BondOffsetInBox m b := by
    intro b hb
    constructor
    · intro i
      have h1 : (b.1 i).natAbs ≤ offsetNorm b.1 :=
        Finset.le_sup (f := fun i => (b.1 i).natAbs) (Finset.mem_univ i)
      rw [Int.abs_eq_natAbs]
      exact_mod_cast (by omega : (b.1 i).natAbs ≤ m)
    · intro i
      have h1 : (b.1 i).natAbs ≤ offsetNorm b.1 :=
        Finset.le_sup (f := fun i => (b.1 i).natAbs) (Finset.mem_univ i)
      have h2 : ((b.1 + Pi.single b.2 1 : Fin 4 → ℤ) i).natAbs ≤ (b.1 i).natAbs + 1 := by
        simp only [Pi.add_apply]
        refine (Int.natAbs_add_le _ _).trans ?_
        have : ((Pi.single b.2 1 : Fin 4 → ℤ) i).natAbs ≤ 1 := by
          by_cases h : i = b.2
          · subst h
            simp
          · simp [h]
        omega
      rw [Int.abs_eq_natAbs]
      exact_mod_cast (by omega : ((b.1 + Pi.single b.2 1 : Fin 4 → ℤ) i).natAbs ≤ m)
  refine ⟨max ℓ.n₀ (2 * m + 3), fun n hn n' hn' => ?_⟩
  have g1 : ℓ.n₀ ≤ n := (le_max_left _ _).trans hn
  have g2 : ℓ.n₀ ≤ n' := (le_max_left _ _).trans hn'
  have g3 : 2 * m + 2 < n := lt_of_lt_of_le (by omega) ((le_max_right _ _).trans hn)
  have g4 : 2 * m + 2 < n' := lt_of_lt_of_le (by omega) ((le_max_right _ _).trans hn')
  have i1 : NeZero n := ⟨by omega⟩
  have i2 : NeZero n' := ⟨by omega⟩
  have agree : FieldsAgreeNear (trivialField n) (trivialField n') 0 0 m := fun _ _ => rfl
  have hl := hrow.local_density n n' g1 g2 0 0 (trivialField n) (trivialField n') m g3 g4
    (isCold_trivialField hσ) (isCold_trivialField hσ) agree
    2 ![c, c'] ![X, X'] (by norm_num) (by
      intro l
      fin_cases l
      · exact hbox c (by omega)
      · exact hbox c' (by omega))
    (areUnitVectors_pair hX hX')
  have eb : ∀ k : ℕ, (fun l : Fin 2 => bondFrom (0 : TorusSite k) (![c, c'] l)) =
      ![bondFrom 0 c, bondFrom 0 c'] := by
    intro k
    funext l
    fin_cases l <;> rfl
  rw [eb, eb] at hl
  have h1 : mixedDeriv (centered f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] =
      mixedDeriv (f n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] :=
    mixedDeriv_sub_const (f n 0) (f n 0 (trivialField n)) _
  have h2 : mixedDeriv (centered f n' 0) (trivialField n') ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] =
      mixedDeriv (f n' 0) (trivialField n') ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] :=
    mixedDeriv_sub_const (f n' 0) (f n' 0 (trivialField n')) _
  rw [h1, h2] at hl
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hl.trans (div_weight_le hrt hE m)) hm1
theorem hasLimitSecondDeriv (hσ : 0 < ℓ.threshold) (hrt : 0 < ℓ.rt) (hE : 0 ≤ ℓ.E) (hn₀ : 0 < ℓ.n₀)
    (hrow : ColdExpansion ℓ t x D f) : HasLimitSecondDeriv f := by
  intro c c' X X'
  by_cases h0 : X = 0
  · subst h0
    refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn
    have i1 : NeZero n := ⟨by omega⟩
    have hs := (hrow.smooth n hn 0 (trivialField n) (isCold_trivialField hσ) 2
      ![bondFrom 0 c, bondFrom 0 c'] ![0, X']).of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)
    have := mixedDeriv_smul (g := f n 0) (bondFrom 0 c) (bondFrom 0 c') 0 X' hs 0 1
    simp only [zero_smul, one_smul, zero_mul] at this
    exact this.symm
  by_cases h1 : X' = 0
  · subst h1
    refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn
    have i1 : NeZero n := ⟨by omega⟩
    have hs := (hrow.smooth n hn 0 (trivialField n) (isCold_trivialField hσ) 2
      ![bondFrom 0 c, bondFrom 0 c'] ![X, 0]).of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)
    have := mixedDeriv_smul (g := f n 0) (bondFrom 0 c) (bondFrom 0 c') X 0 hs 1 0
    simp only [zero_smul, one_smul, mul_zero, zero_mul] at this
    exact this.symm
  have n0 : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have n1 : ‖X'‖ ≠ 0 := norm_ne_zero_iff.mpr h1
  have u0 : ‖‖X‖⁻¹ • X‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n0]
  have u1 : ‖‖X'‖⁻¹ • X'‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n1]
  obtain ⟨v, hv⟩ := exists_tendsto_mixedDeriv_of_unit hσ hrt hE hn₀ hrow c c' u0 u1
  refine ⟨‖X‖ * ‖X'‖ * v, (hv.const_mul (‖X‖ * ‖X'‖)).congr' ?_⟩
  filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn
  have i1 : NeZero n := ⟨by omega⟩
  have hs := (hrow.smooth n hn 0 (trivialField n) (isCold_trivialField hσ) 2 ![bondFrom 0 c, bondFrom 0 c']
    ![‖X‖⁻¹ • X, ‖X'‖⁻¹ • X']).of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)
  have := mixedDeriv_smul (g := f n 0) (bondFrom 0 c) (bondFrom 0 c') _ _ hs ‖X‖ ‖X'‖
  rw [smul_smul, smul_smul, mul_inv_cancel₀ n0, mul_inv_cancel₀ n1, one_smul, one_smul] at this
  exact this.symm
theorem isLocalGaugeDensity (hσ : 0 < ℓ.threshold) (hrt : 0 < ℓ.rt) (hE : 0 ≤ ℓ.E) (hn₀ : 0 < ℓ.n₀)
    (hrow : ColdExpansion ℓ t x D f) : IsLocalGaugeDensity f where
  contDiffAt := by
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn y k c X
    have i1 : NeZero n := ⟨by omega⟩
    exact (hrow.smooth n hn y (trivialField n) (isCold_trivialField hσ) k c X).of_le (by norm_num)
  gauge_invariant := by
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn y
    have i1 : NeZero n := ⟨by omega⟩
    have hc : Tendsto (Prod.snd : (TorusSite n → UnitQuaternion) × TorusField n → TorusField n)
        (𝓝 (1, trivialField n)) (𝓝 (trivialField n)) :=
      continuous_snd.tendsto _
    filter_upwards [hc.eventually (eventually_isCold hσ)] with p hp
    exact hrow.gauge n hn y p.1 p.2 hp
  translation_invariant := by
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn y u
    have i1 : NeZero n := ⟨by omega⟩
    filter_upwards [eventually_isCold hσ] with V hV
    exact hrow.translation n hn y u V hV
  kernel_decay := by
    refine ⟨ℓ.E, ℓ.weightRate, weightRate_pos hrt, ?_⟩
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn c c' X X' hX hX'
    have i1 : NeZero n := ⟨by omega⟩
    have h := hrow.decay n hn 0 (trivialField n) (isCold_trivialField hσ) 2 ![c, c'] ![X, X']
      (by norm_num) (by norm_num) (areUnitVectors_pair hX hX')
    simp only [show ¬ (2 = 3) by norm_num, if_false] at h
    exact h.trans (div_weight_le hrt hE _)
  tendsto := hasLimitSecondDeriv hσ hrt hE hn₀ hrow
theorem unitPlaneCurvature_antisymm (μ ν : Fin 4) :
    unitPlaneCurvature μ ν = -unitPlaneCurvature ν μ := by apply _root_.YangMills.SharedProofs.p4715 <;> assumption
end Expansion
theorem coldDensitiesHaveZeroCoefficient (hCoef : LocalDensityCoefficient.Claim)
    (hNum : CoefficientFromDensity.Claim) (hAct : MinimalActionHasUnitCoefficient)
    (hComp : PullbackKeepsSlopeCoefficient) (hBlock : MinimizerIsBlockMap)
    (hTot : GaugeTotalAtMinimizer) :
    ColdDensitiesHaveZeroCoefficient := by
  intro T y t x ρ D f hDr hfit h0 h1 harr hrow
  set ℓ := T.stepParameters y with hℓ
  have hσ := hfit.σ_pos
  have hrt := hfit.rt_pos
  have hE : 0 ≤ ℓ.E := hfit.E_pos.le
  have hn₀ : 0 < ℓ.n₀ := by
    have := hfit.n₀_ge
    omega
  have ha : 0 < ℓ.coupling := by linarith [hfit.a_ge]
  have hL : Conventions.IsAdmissibleBlockingFactor ℓ.side := ⟨hfit.L_odd, by
    have := hfit.L_ge
    omega⟩
  obtain ⟨K, hK, -⟩ := hAct T hDr t
  have htot : ∀ᶠ n in atTop, IsGaugeTotalAt (centeredDensityTotal f) n := by
    filter_upwards [hK.eventually_isGaugeTotalAt, eventually_ge_atTop ℓ.n₀] with n ht hn
    have i1 : NeZero n := ⟨by omega⟩
    exact isGaugeTotalAt_of_coldExpansion hσ harr hrow hn ht
  have hloc := isLocalGaugeDensity hσ hrt hE hn₀ hrow
  have hnear : ∀ᶠ n in atTop, ∀ᶠ V in 𝓝 (trivialField n),
      centeredDensityTotal f n V = centeredDensityTotal f n V :=
    Eventually.of_forall fun _ => Eventually.of_forall fun _ => rfl
  obtain ⟨b, hb⟩ := hCoef f (centeredDensityTotal f) hloc htot hnear
  have hs := hNum f _ b hloc hb hnear
  have hz : HasSum (limitFormTerm f unitPlaneCurvature unitPlaneCurvature) 0 :=
    hrow.no_curvature_term unitPlaneCurvature unitPlaneCurvature
      unitPlaneCurvature_antisymm unitPlaneCurvature_antisymm
  have b0 : b = 0 := hs.unique hz
  subst b0
  refine ⟨hb, ?_⟩
  obtain ⟨P, Pl, hM⟩ := hBlock ℓ.coupling ha ℓ.side hL t ρ h0 h1
  have hLpos : 0 < ℓ.side := by
    have := hfit.L_ge
    omega
  exact hComp ℓ.side (centeredDensityTotal f) _ P Pl 0 hLpos hM hb
    (hTot ℓ.coupling ha ℓ.side hL t ρ h0 h1 _ htot)
end RunningCouplingSlope.ColdDensitiesZeroCoefficientProof
end YangMills.Construction
end
