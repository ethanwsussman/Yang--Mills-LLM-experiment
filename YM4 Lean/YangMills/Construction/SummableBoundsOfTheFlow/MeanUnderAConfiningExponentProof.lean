import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAMoveNearATopProof
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false

noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.ConfiningMeans
structure HasPolynomialGrowthDerivs {ι : Type} [Fintype ι] {n : ℕ} (B : Set (Fin n → ℝ)) (C : ℝ) (m : ℕ)
    (G : (Fin n → ℝ) → BondField ι → ℝ) : Prop where
  measurable : ∀ s ∈ B, Measurable (G s)
  contDiffOn : ∀ ζ, ContDiffOn ℝ 3 (fun s => G s ζ) B
  norm_iteratedFDeriv_le : ∀ ζ, ∀ j, j ≤ 3 → ∀ s ∈ B, ‖iteratedFDeriv ℝ j (fun s => G s ζ) s‖ ≤ C * (1 + ‖ζ‖) ^ m
def ConfiningGibbsMeanContDiff : Prop :=
  ∀ (ι : Type) [Fintype ι] (n m : ℕ) (B : Set (Fin n → ℝ)) (c C : ℝ)
    (A H : (Fin n → ℝ) → BondField ι → ℝ), IsOpen B → 0 < c →
    HasPolynomialGrowthDerivs B C m A → HasPolynomialGrowthDerivs B C m H →
    (∀ s ∈ B, ∀ ζ, c * ‖ζ‖ ^ 2 ≤ A s ζ) →
    ContDiffOn ℝ 3 (fun s => (∫ ζ, H s ζ * Real.exp (- A s ζ)) / ∫ ζ, Real.exp (- A s ζ)) B
end YangMills.Construction.ConfiningMeans
end

noncomputable section
open MeasureTheory Set Filter Topology
namespace YangMills.Construction.ConfiningMeans
open ColdStepAtMirrorFrames
section Calculus
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
private theorem norm_iteratedFDeriv_comp_le_at {n : ℕ} {f : E → G} {g : G → H} {x : E} (hf : ContDiffAt ℝ n f x)
    (hg : ContDiffAt ℝ n g (f x)) {C D : ℝ} (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * D ^ n := by apply _root_.YangMills.SharedProofs.p37475 <;> assumption
private theorem norm_iteratedFDeriv_mul_le_of_le_three {B : Set E} (hB : IsOpen B) {f g : E → ℝ} (hf : ContDiffOn ℝ 3 f B)
    (hg : ContDiffOn ℝ 3 g B) {x : E} (hx : x ∈ B) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i f x‖ ≤ M₁) (h₂ : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i g x‖ ≤ M₂)
    {j : ℕ} (hj : j ≤ 3) : ‖iteratedFDeriv ℝ j (fun y => f y * g y) x‖ ≤ 8 * (M₁ * M₂) := by
  have key := norm_iteratedFDerivWithin_mul_le hf hg hB.uniqueDiffOn hx (n := j) (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen j hB hx] at key
  refine key.trans ?_
  calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f B x‖ *
        ‖iteratedFDerivWithin ℝ (j - i) g B x‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * M₁ * M₂ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [iteratedFDerivWithin_of_isOpen i hB hx, iteratedFDerivWithin_of_isOpen (j - i) hB hx]
        have b₁ := h₁ i (by omega)
        have b₂ := h₂ (j - i) (by omega)
        gcongr
    _ = (2 : ℝ) ^ j * (M₁ * M₂) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [this]
        ring
    _ ≤ 8 * (M₁ * M₂) := by
        have : (2 : ℝ) ^ j ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
        have h0 : 0 ≤ M₁ * M₂ := mul_nonneg hM₁ hM₂
        nlinarith
abbrev _root_.YangMills.SharedProofs.p56328 := @norm_iteratedFDeriv_mul_le_of_le_three
private theorem norm_iteratedFDeriv_exp_comp_le {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) {M : ℝ} (hM : 1 ≤ M)
    (h : ∀ i, 1 ≤ i → i ≤ 3 → ‖iteratedFDeriv ℝ i f x‖ ≤ M) {j : ℕ} (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (fun y => Real.exp (f y)) x‖ ≤ 6 * Real.exp (f x) * M ^ 3 := by
  have hexp : ContDiffAt ℝ j Real.exp (f x) := Real.contDiff_exp.contDiffAt
  have hC : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i Real.exp (f x)‖ ≤ Real.exp (f x) := by
    intro i _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ M ^ i := by
    intro i h1 hi
    refine (h i h1 (by omega)).trans ?_
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ i := pow_le_pow_right₀ hM h1
  have hcomp := norm_iteratedFDeriv_comp_le_at (n := j) (hf.of_le (by exact_mod_cast hj)) hexp hC hD
  have e : (fun y => Real.exp (f y)) = Real.exp ∘ f := rfl
  rw [e]
  refine hcomp.trans ?_
  have hfac : ((j.factorial : ℕ) : ℝ) ≤ 6 := by
    have : j.factorial ≤ Nat.factorial 3 := Nat.factorial_le hj
    have h6 : Nat.factorial 3 = 6 := rfl
    rw [h6] at this
    exact_mod_cast this
  have hpow : M ^ j ≤ M ^ 3 := pow_le_pow_right₀ hM hj
  calc ((j.factorial : ℕ) : ℝ) * Real.exp (f x) * M ^ j ≤ 6 * Real.exp (f x) * M ^ 3 := by gcongr
    _ = _ := rfl
end Calculus
private theorem exists_bound_one_add_pow_mul_exp_neg_sq {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ K := by
  refine ⟨2 ^ N * ((N.factorial : ℝ) / c ^ N) * Real.exp c, by positivity, fun t ht => ?_⟩
  have hx : 0 ≤ c * (1 + t ^ 2) := by positivity
  have h1 := Real.pow_div_factorial_le_exp (c * (1 + t ^ 2)) hx N
  have h2 : 1 + t ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (t - 1)]
  have h3 : (1 + t) ^ N ≤ (2 * (1 + t ^ 2)) ^ N := pow_le_pow_left₀ (by linarith) h2 N
  have h4 : (1 + t ^ 2) ^ N ≤ (N.factorial : ℝ) / c ^ N * Real.exp (c * (1 + t ^ 2)) := by
    rw [mul_pow, div_le_iff₀ (by positivity)] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have h5 : Real.exp (c * (1 + t ^ 2)) * Real.exp (-(c * t ^ 2)) = Real.exp c := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 + t) ^ N * Real.exp (-(c * t ^ 2))
      ≤ (2 * (1 + t ^ 2)) ^ N * Real.exp (-(c * t ^ 2)) := by gcongr
    _ = 2 ^ N * (1 + t ^ 2) ^ N * Real.exp (-(c * t ^ 2)) := by rw [mul_pow]
    _ ≤ 2 ^ N * ((N.factorial : ℝ) / c ^ N * Real.exp (c * (1 + t ^ 2))) * Real.exp (-(c * t ^ 2)) := by
        gcongr
    _ = 2 ^ N * ((N.factorial : ℝ) / c ^ N) *
          (Real.exp (c * (1 + t ^ 2)) * Real.exp (-(c * t ^ 2))) := by ring
    _ = _ := by rw [h5]
variable {ι : Type} [Fintype ι]
private def polyWeight (r : ℕ) (ζ : BondField ι) : ℝ := ((1 + ‖ζ‖) ^ r)⁻¹
private theorem polyWeight_pos (r : ℕ) (ζ : BondField ι) : 0 < polyWeight r ζ := by
  have : 0 < 1 + ‖ζ‖ := by positivity
  unfold polyWeight
  positivity
private theorem measurable_polyWeight (r : ℕ) : Measurable (polyWeight (ι := ι) r) := by
  unfold polyWeight
  fun_prop
private def polyWeightMeasure (r : ℕ) : Measure (BondField ι) :=
  volume.withDensity fun ζ => ENNReal.ofReal (polyWeight r ζ)
private theorem integrable_polyWeight {r : ℕ} (hr : Module.finrank ℝ (BondField ι) < r) :
    Integrable (polyWeight (ι := ι) r) := by
  have h := integrable_one_add_norm (E := BondField ι) (μ := volume) (r := (r : ℝ)) (by exact_mod_cast hr)
  refine h.congr (Eventually.of_forall fun ζ => ?_)
  have : (0 : ℝ) ≤ 1 + ‖ζ‖ := by positivity
  simp only [polyWeight]
  rw [Real.rpow_neg this, Real.rpow_natCast]
private theorem isFiniteMeasure_polyWeightMeasure {r : ℕ} (hr : Module.finrank ℝ (BondField ι) < r) :
    IsFiniteMeasure (polyWeightMeasure (ι := ι) r) :=
  isFiniteMeasure_withDensity_ofReal (integrable_polyWeight hr).hasFiniteIntegral
private theorem integral_polyWeightMeasure (r : ℕ) (g : BondField ι → ℝ) :
    ∫ ζ, g ζ ∂polyWeightMeasure r = ∫ ζ, polyWeight r ζ * g ζ := by
  unfold polyWeightMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_polyWeight r).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (polyWeight_pos r ζ).le]
private theorem contDiffOn_integral_mul_exp_neg (hI : DifferentiationUnderIntegral) {n m : ℕ}
    {B : Set (Fin n → ℝ)} {c C C' : ℝ} {m' : ℕ}
    {A F : (Fin n → ℝ) → BondField ι → ℝ} (hB : IsOpen B) (hc : 0 < c)
    (gA : HasPolynomialGrowthDerivs B C m A) (gF : HasPolynomialGrowthDerivs B C' m' F)
    (hfloor : ∀ s ∈ B, ∀ ζ, c * ‖ζ‖ ^ 2 ≤ A s ζ) :
    ContDiffOn ℝ 3 (fun s => ∫ ζ, F s ζ * Real.exp (- A s ζ)) B ∧
      ∀ s ∈ B, Integrable fun ζ => F s ζ * Real.exp (- A s ζ) := by
  obtain ⟨r, hrd⟩ : ∃ r : ℕ, Module.finrank ℝ (BondField ι) < r := ⟨_, Nat.lt_succ_self _⟩
  haveI := isFiniteMeasure_polyWeightMeasure (ι := ι) hrd
  set lg : BondField ι → ℝ := fun ζ => Real.log ((1 + ‖ζ‖) ^ r) with hlg
  set G : (Fin n → ℝ) → BondField ι → ℝ := fun s ζ => F s ζ * Real.exp (- A s ζ + lg ζ) with hG
  have hPpos : ∀ ζ : BondField ι, 0 < (1 + ‖ζ‖) ^ r := fun ζ => by positivity
  have hexplg : ∀ ζ, Real.exp (lg ζ) = (1 + ‖ζ‖) ^ r := fun ζ => Real.exp_log (hPpos ζ)
  set Wa : BondField ι → ℝ := fun ζ => 1 + |C| * (1 + ‖ζ‖) ^ m with hWa
  set Wf : BondField ι → ℝ := fun ζ => 1 + |C'| * (1 + ‖ζ‖) ^ m' with hWf
  have hWa1 : ∀ ζ, 1 ≤ Wa ζ := fun ζ => by
    have : 0 ≤ |C| * (1 + ‖ζ‖) ^ m := by positivity
    simp only [hWa]
    linarith
  have hWf1 : ∀ ζ, 1 ≤ Wf ζ := fun ζ => by
    have : 0 ≤ |C'| * (1 + ‖ζ‖) ^ m' := by positivity
    simp only [hWf]
    linarith
  obtain ⟨K₀, hK₀, hKb⟩ := exists_bound_one_add_pow_mul_exp_neg_sq hc (3 * m + m' + r + m)
  have hsmA : ∀ ζ, ContDiffOn ℝ 3 (fun s => - A s ζ + lg ζ) B := fun ζ =>
    ((gA.contDiffOn ζ).neg).add contDiffOn_const
  have hsmE : ∀ ζ, ContDiffOn ℝ 3 (fun s => Real.exp (- A s ζ + lg ζ)) B := fun ζ =>
    (Real.contDiff_exp.comp_contDiffOn (hsmA ζ))
  have hderA : ∀ ζ, ∀ s ∈ B, ∀ i, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i (fun s => - A s ζ + lg ζ) s‖ ≤ Wa ζ := by
    intro ζ s hs i h1 hi
    have hA := (gA.contDiffOn ζ).contDiffAt (hB.mem_nhds hs)
    have e1 : iteratedFDeriv ℝ i (fun s => - A s ζ + lg ζ) s = - iteratedFDeriv ℝ i (fun s => A s ζ) s := by
      have h2 : iteratedFDeriv ℝ i (fun s => - A s ζ + lg ζ) s =
          iteratedFDeriv ℝ i (fun s => - A s ζ) s + iteratedFDeriv ℝ i (fun _ => lg ζ) s :=
        iteratedFDeriv_add_apply ((hA.neg).of_le (by exact_mod_cast hi)) (contDiffAt_const)
      have h3 : iteratedFDeriv ℝ i (fun _ : Fin n → ℝ => lg ζ) s = 0 := by
        rw [iteratedFDeriv_const_of_ne (by omega)]
        rfl
      rw [h2, h3, add_zero]
      exact iteratedFDeriv_neg_apply
    rw [e1, norm_neg]
    refine (gA.norm_iteratedFDeriv_le ζ i hi s hs).trans ?_
    have : C * (1 + ‖ζ‖) ^ m ≤ |C| * (1 + ‖ζ‖) ^ m := by
      gcongr
      exact le_abs_self C
    simp only [hWa]
    linarith
  have hderG : ∀ ζ, ∀ s ∈ B, ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j (fun s => G s ζ) s‖ ≤
      8 * (Wf ζ * (6 * (Real.exp (-(c * ‖ζ‖ ^ 2)) * (1 + ‖ζ‖) ^ r) * Wa ζ ^ 3)) := by
    intro ζ s hs j hj
    have hW0 : 0 ≤ Wa ζ := by linarith [hWa1 ζ]
    have hE : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i (fun s => Real.exp (- A s ζ + lg ζ)) s‖ ≤
        6 * (Real.exp (-(c * ‖ζ‖ ^ 2)) * (1 + ‖ζ‖) ^ r) * Wa ζ ^ 3 := by
      intro i hi
      refine (norm_iteratedFDeriv_exp_comp_le ((hsmA ζ).contDiffAt (hB.mem_nhds hs)) (hWa1 ζ)
        (hderA ζ s hs) hi).trans ?_
      have : Real.exp (- A s ζ + lg ζ) ≤ Real.exp (-(c * ‖ζ‖ ^ 2)) * (1 + ‖ζ‖) ^ r := by
        rw [Real.exp_add, hexplg]
        have := hfloor s hs ζ
        gcongr
      gcongr
    have hF : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i (fun s => F s ζ) s‖ ≤ Wf ζ := by
      intro i hi
      refine (gF.norm_iteratedFDeriv_le ζ i hi s hs).trans ?_
      have : C' * (1 + ‖ζ‖) ^ m' ≤ |C'| * (1 + ‖ζ‖) ^ m' := by
        gcongr
        exact le_abs_self C'
      simp only [hWf]
      linarith
    exact norm_iteratedFDeriv_mul_le_of_le_three hB (gF.contDiffOn ζ) (hsmE ζ) hs (by linarith [hWf1 ζ])
      (by positivity) hF hE hj
  set K : ℝ := 48 * ((1 + |C'|) * (1 + |C|) ^ 3) * K₀ with hK
  have hbound : ∀ ζ : BondField ι,
      8 * (Wf ζ * (6 * (Real.exp (-(c * ‖ζ‖ ^ 2)) * (1 + ‖ζ‖) ^ r) * Wa ζ ^ 3)) ≤ K := by
    intro ζ
    have h1 : (1 : ℝ) ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
    have hWa' : Wa ζ ≤ (1 + |C|) * (1 + ‖ζ‖) ^ m := by
      have : (1 : ℝ) ≤ (1 + ‖ζ‖) ^ m := one_le_pow₀ h1
      simp only [hWa]
      nlinarith [abs_nonneg C]
    have hWf' : Wf ζ ≤ (1 + |C'|) * (1 + ‖ζ‖) ^ m' := by
      have : (1 : ℝ) ≤ (1 + ‖ζ‖) ^ m' := one_le_pow₀ h1
      simp only [hWf]
      nlinarith [abs_nonneg C']
    have hW3 : Wa ζ ^ 3 ≤ ((1 + |C|) * (1 + ‖ζ‖) ^ m) ^ 3 :=
      pow_le_pow_left₀ (by linarith [hWa1 ζ]) hWa' 3
    have hk := hKb ‖ζ‖ (norm_nonneg ζ)
    have hmore : (1 + ‖ζ‖) ^ (3 * m + m' + r) * Real.exp (-(c * ‖ζ‖ ^ 2)) ≤ K₀ := by
      refine le_trans ?_ hk
      have : (1 + ‖ζ‖) ^ (3 * m + m' + r) ≤ (1 + ‖ζ‖) ^ (3 * m + m' + r + m) :=
        pow_le_pow_right₀ h1 (by omega)
      exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    have hpos := Real.exp_pos (-(c * ‖ζ‖ ^ 2))
    calc 8 * (Wf ζ * (6 * (Real.exp (-(c * ‖ζ‖ ^ 2)) * (1 + ‖ζ‖) ^ r) * Wa ζ ^ 3))
        ≤ 8 * (((1 + |C'|) * (1 + ‖ζ‖) ^ m') * (6 * (Real.exp (-(c * ‖ζ‖ ^ 2)) * (1 + ‖ζ‖) ^ r) *
            ((1 + |C|) * (1 + ‖ζ‖) ^ m) ^ 3)) := by
          have := hWa1 ζ
          have := hWf1 ζ
          gcongr
      _ = 48 * ((1 + |C'|) * (1 + |C|) ^ 3) *
            ((1 + ‖ζ‖) ^ (3 * m + m' + r) * Real.exp (-(c * ‖ζ‖ ^ 2))) := by
          have e : (1 + ‖ζ‖) ^ (3 * m + m' + r) = ((1 + ‖ζ‖) ^ m) ^ 3 * (1 + ‖ζ‖) ^ m' * (1 + ‖ζ‖) ^ r := by
            rw [pow_add, pow_add, mul_comm 3 m, pow_mul]
          rw [e]
          ring
      _ ≤ K := by
          rw [hK]
          gcongr
  have hmeasG : ∀ s ∈ B, Measurable (G s) := by
    intro s hs
    have h1 := gA.measurable s hs
    have h2 := gF.measurable s hs
    have h3 : Measurable lg := by
      simp only [hlg]
      fun_prop
    simp only [hG]
    exact h2.mul (Real.measurable_exp.comp (h1.neg.add h3))
  have hdom : IsDominatedSmoothFamily (polyWeightMeasure (ι := ι) r) 3 B K G := by
    refine ⟨fun s hs => (hmeasG s hs).aestronglyMeasurable, ae_of_all _ fun ζ => ?_,
      ae_of_all _ fun ζ j hj s hs => (hderG ζ s hs j hj).trans (hbound ζ)⟩
    exact_mod_cast (gF.contDiffOn ζ).mul (hsmE ζ)
  have hint : ∀ s ∈ B, Integrable (G s) (polyWeightMeasure (ι := ι) r) := by
    intro s hs
    refine Integrable.of_bound (hmeasG s hs).aestronglyMeasurable K (ae_of_all _ fun ζ => ?_)
    have := (hderG ζ s hs 0 (by norm_num)).trans (hbound ζ)
    rwa [norm_iteratedFDeriv_zero] at this
  have hval : ∀ s ζ, polyWeight r ζ * G s ζ = F s ζ * Real.exp (- A s ζ) := by
    intro s ζ
    simp only [hG, polyWeight]
    rw [Real.exp_add, hexplg]
    have := (hPpos ζ).ne'
    field_simp
  constructor
  · have h1 : ContDiffOn ℝ 3 (fun s => ∫ ζ, G s ζ ∂polyWeightMeasure (ι := ι) r) B := by
      exact_mod_cast (hI (BondField ι) (polyWeightMeasure r) n 3 B K G hB hdom).1
    refine h1.congr fun s _ => ?_
    rw [integral_polyWeightMeasure]
    simp only [hval]
  · intro s hs
    have h1 := hint s hs
    unfold polyWeightMeasure at h1
    rw [integrable_withDensity_iff (measurable_polyWeight r).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h1
    refine h1.congr (Eventually.of_forall fun ζ => ?_)
    simp only []
    rw [ENNReal.toReal_ofReal (polyWeight_pos r ζ).le, mul_comm, hval]
theorem confiningGibbsMeanContDiff_of_gibbsMeanDifferentiation (hW : GibbsMeanDifferentiation) :
    ConfiningGibbsMeanContDiff := by
  intro ι _ n m B c C A F hB hc gA gF hfloor
  have gO : HasPolynomialGrowthDerivs B 1 0 (fun (_ : Fin n → ℝ) (_ : BondField ι) => (1 : ℝ)) := by
    refine ⟨fun _ _ => measurable_const, fun _ => contDiffOn_const, fun ζ j _ s _ => ?_⟩
    by_cases hj : j = 0
    · subst hj
      simp
    · rw [iteratedFDeriv_const_of_ne hj]
      simp
  obtain ⟨hN, -⟩ := contDiffOn_integral_mul_exp_neg hW.1 hB hc gA gF hfloor
  obtain ⟨hD, hDi⟩ := contDiffOn_integral_mul_exp_neg hW.1 hB hc gA gO hfloor
  simp only [one_mul] at hD hDi
  refine hN.div hD fun s hs => ?_
  have := integral_exp_pos (μ := (volume : Measure (BondField ι))) (hDi s hs)
  exact this.ne'
end YangMills.Construction.ConfiningMeans
end
