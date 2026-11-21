import YangMills.Construction.DirichletOperator.BumpOfACubeIsSmoothWithCompactSupportProof
import YangMills.Construction.DirichletOperator.DerivativeBoundsOfTheFunctionsOfACube
import YangMills.Construction.DirichletOperator.SidesOfTheBlocksAtALevel
import YangMills.Construction.PartitionCubes.SmoothedIndicatorDerivatives
import Mathlib
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped ContDiff
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds
theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
structure DerivNormBound (C ρ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 f
  norm_le : ∀ i ≤ 2, ∀ p, ‖iteratedFDeriv ℝ i f p‖ ≤ C * ρ ^ i
theorem DerivNormBound.mono {C C' ρ ρ' : ℝ} {f : (Fin 4 → ℝ) → ℝ} (h : DerivNormBound C ρ f)
    (hC : C ≤ C') (hC' : 0 ≤ C') (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ') : DerivNormBound C' ρ' f :=
  ⟨h.contDiff, fun i hi p => (h.norm_le i hi p).trans
    (mul_le_mul hC (pow_le_pow_left₀ hρ hρ' i) (pow_nonneg hρ i) hC')⟩
theorem DerivNormBound.rescale {C k ρ : ℝ} {f : (Fin 4 → ℝ) → ℝ} (h : DerivNormBound C (k * ρ) f)
    (hC : 0 ≤ C) (hk : 1 ≤ k) (hρ : 0 ≤ ρ) : DerivNormBound (k ^ 2 * C) ρ f := by
  refine ⟨h.contDiff, fun i hi p => (h.norm_le i hi p).trans ?_⟩
  rw [mul_pow, ← mul_assoc, mul_comm C]
  have hp : k ^ i ≤ k ^ 2 := pow_le_pow_right₀ hk hi
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hC) (pow_nonneg hρ i)
theorem DerivNormBound.mul {C₁ C₂ ρ : ℝ} {f g : (Fin 4 → ℝ) → ℝ} (hf : DerivNormBound C₁ ρ f)
    (hg : DerivNormBound C₂ ρ g) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) (hρ : 0 ≤ ρ) :
    DerivNormBound (4 * C₁ * C₂) ρ fun p => f p * g p := by
  refine ⟨hf.contDiff.mul hg.contDiff, fun i hi p => ?_⟩
  have hterm : ∀ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j f p‖ * ‖iteratedFDeriv ℝ (i - j) g p‖ ≤
        (i.choose j : ℝ) * (C₁ * C₂ * ρ ^ i) := by
    intro j hj
    have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have a := hf.norm_le j (hj'.trans hi) p
    have b := hg.norm_le (i - j) ((Nat.sub_le _ _).trans hi) p
    have e : C₁ * C₂ * ρ ^ i = (C₁ * ρ ^ j) * (C₂ * ρ ^ (i - j)) := by
      have e' : ρ ^ i = ρ ^ j * ρ ^ (i - j) := by rw [← pow_add, Nat.add_sub_cancel' hj']
      rw [e']
      ring
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul a b (norm_nonneg _) (mul_nonneg h₁ (pow_nonneg hρ _))) (Nat.cast_nonneg _)
  have hsum : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (C₁ * C₂ * ρ ^ i) =
      2 ^ i * (C₁ * C₂ * ρ ^ i) := by
    rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  have hp : (2 : ℝ) ^ i ≤ 4 := by
    calc (2 : ℝ) ^ i ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hi
      _ = 4 := by norm_num
  have h3 : 0 ≤ C₁ * C₂ * ρ ^ i := by positivity
  calc ‖iteratedFDeriv ℝ i (fun y => f y * g y) p‖ ≤ _ :=
        norm_iteratedFDeriv_mul_le hf.contDiff hg.contDiff p (by exact_mod_cast hi)
    _ ≤ _ := Finset.sum_le_sum hterm
    _ = 2 ^ i * (C₁ * C₂ * ρ ^ i) := hsum
    _ ≤ 4 * (C₁ * C₂ * ρ ^ i) := mul_le_mul_of_nonneg_right hp h3
    _ = 4 * C₁ * C₂ * ρ ^ i := by ring
theorem DerivNormBound.comp {A C ρ : ℝ} {f : (Fin 4 → ℝ) → ℝ} {g : ℝ → ℝ}
    (hf : DerivNormBound A ρ f) (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hg : ContDiff ℝ 2 g)
    (hval : ∀ p, f p ∈ Icc (0 : ℝ) 1)
    (hgC : ∀ i ≤ 2, ∀ y ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ i g y‖ ≤ C) :
    DerivNormBound (2 * C * (A + 1) ^ 2) ρ fun p => g (f p) := by
  refine ⟨hg.comp hf.contDiff, fun i hi p => ?_⟩
  have hD : ∀ j, 1 ≤ j → j ≤ i → ‖iteratedFDeriv ℝ j f p‖ ≤ ((A + 1) * ρ) ^ j := by
    intro j h1 hj
    refine (hf.norm_le j (hj.trans hi) p).trans ?_
    rw [mul_pow]
    have hj0 : j ≠ 0 := by omega
    have hle : A ≤ (A + 1) ^ j :=
      (by linarith : A ≤ A + 1).trans (le_self_pow₀ (by linarith) hj0)
    exact mul_le_mul_of_nonneg_right hle (pow_nonneg hρ j)
  have h := norm_iteratedFDeriv_comp_le hg hf.contDiff (by exact_mod_cast hi) p
    (fun j hj => hgC j (hj.trans hi) _ (hval p)) hD
  refine h.trans ?_
  have hfact : (i.factorial : ℝ) ≤ 2 := by
    interval_cases i <;> norm_num [Nat.factorial]
  have hpow : (A + 1) ^ i ≤ (A + 1) ^ 2 := pow_le_pow_right₀ (by linarith) hi
  have h4 : 0 ≤ C * ρ ^ i := by positivity
  calc (i.factorial : ℝ) * C * ((A + 1) * ρ) ^ i = ((i.factorial : ℝ) * (A + 1) ^ i) * (C * ρ ^ i) := by
        rw [mul_pow]
        ring
    _ ≤ (2 * (A + 1) ^ 2) * (C * ρ ^ i) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hfact hpow (by positivity) (by norm_num)) h4
    _ = 2 * C * (A + 1) ^ 2 * ρ ^ i := by ring
theorem derivNormBound_const_one {ρ : ℝ} (hρ : 0 ≤ ρ) : DerivNormBound 1 ρ fun _ => 1 := by
  refine ⟨contDiff_const, fun i _ p => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [iteratedFDeriv_const_of_ne hi.ne']
    simpa using pow_nonneg hρ i
theorem exists_iteratedFDeriv_bound_Icc {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ 2, ∀ y ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ i g y‖ ≤ C := by
  have key : ∀ i : ℕ, ∃ C, ∀ y ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ i g y‖ ≤ C := fun i =>
    isCompact_Icc.exists_bound_of_continuousOn
      (hg.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).continuousOn
  choose C hC using key
  refine ⟨|C 0| + |C 1| + |C 2|, by positivity, fun i hi y hy => ?_⟩
  have h := hC i y hy
  interval_cases i <;> linarith [abs_nonneg (C 0), abs_nonneg (C 1), abs_nonneg (C 2),
    le_abs_self (C 0), le_abs_self (C 1), le_abs_self (C 2)]
theorem multilinear_norm_le_of_basis {i : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin 4 → ℝ) ℝ)
    {b : ℝ} (hb : 0 ≤ b) (h : ∀ μ : Fin i → Fin 4, |T fun k => Pi.single (μ k) 1| ≤ b) :
    ‖T‖ ≤ 4 ^ i * b := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have hm : m = fun k => ∑ μ, m k μ • (Pi.single μ 1 : Fin 4 → ℝ) := by
    funext k
    ext ν
    simp [Finset.sum_apply, Pi.single_apply]
  have hexp : T m = ∑ r : Fin i → Fin 4, (∏ k, m k (r k)) * T fun k => Pi.single (r k) 1 := by
    conv_lhs => rw [hm]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  rw [hexp]
  calc ‖∑ r : Fin i → Fin 4, (∏ k, m k (r k)) * T fun k => Pi.single (r k) 1‖
      ≤ ∑ r : Fin i → Fin 4, ‖(∏ k, m k (r k)) * T fun k => Pi.single (r k) 1‖ := norm_sum_le _ _
    _ ≤ ∑ _r : Fin i → Fin 4, (∏ k, ‖m k‖) * b := Finset.sum_le_sum fun r _ => by
        rw [norm_mul, norm_prod]
        exact mul_le_mul
          (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => norm_le_pi_norm (m k) (r k))
          (h r) (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = 4 ^ i * b * ∏ k, ‖m k‖ := by
        simp [Finset.sum_const, Finset.card_univ]
        ring
theorem abs_apply_basis_le_norm {i : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin 4 → ℝ) ℝ)
    (μ : Fin i → Fin 4) : |T fun k => Pi.single (μ k) 1| ≤ ‖T‖ := by
  have h := T.le_opNorm fun k => (Pi.single (μ k) 1 : Fin 4 → ℝ)
  have h1 : ∏ k, ‖(Pi.single (μ k) 1 : Fin 4 → ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun ν => ?_
      by_cases e : ν = μ k <;> simp [e]
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _) h1)
theorem derivNormBound_of_partials {C ρ : ℝ} {f : (Fin 4 → ℝ) → ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hs : ContDiff ℝ 2 f)
    (hd : ∀ i ≤ 2, ∀ (μ : Fin i → Fin 4) (p : Fin 4 → ℝ),
      |iteratedFDeriv ℝ i f p fun k => Pi.single (μ k) 1| ≤ C * ρ ^ i) :
    DerivNormBound (16 * C) ρ f := by
  refine ⟨hs, fun i hi p => ?_⟩
  refine (multilinear_norm_le_of_basis _ (by positivity) fun μ => hd i hi μ p).trans ?_
  have hp : (4 : ℝ) ^ i ≤ 16 := by
    calc (4 : ℝ) ^ i ≤ 4 ^ 2 := pow_le_pow_right₀ (by norm_num) hi
      _ = 16 := by norm_num
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hC) (pow_nonneg hρ i)
def bumpProduct (q : Fin 4 → ℝ) : ℝ := ∏ μ, sqPartitionBump (q μ)
theorem contDiff_bumpProduct : ContDiff ℝ ∞ bumpProduct :=
  contDiff_prod fun μ _ => sqPartitionBump_spec.smooth.comp (contDiff_apply ℝ ℝ μ)
theorem hasCompactSupport_bumpProduct : HasCompactSupport bumpProduct := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin 4 → ℝ) 1) fun q hq => ?_
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun μ => ?_
  have hne : sqPartitionBump (q μ) ≠ 0 := fun h0 =>
    (Function.mem_support.1 hq) (Finset.prod_eq_zero (Finset.mem_univ μ) h0)
  have hmem := sqPartitionBump_spec.support_subset (subset_tsupport _ (Function.mem_support.2 hne))
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hmem.1, hmem.2]
theorem exists_bound_bumpProduct :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ 2, ∀ q, ‖iteratedFDeriv ℝ i bumpProduct q‖ ≤ C := by
  have key : ∀ i : ℕ, ∃ C, ∀ q, ‖iteratedFDeriv ℝ i bumpProduct q‖ ≤ C := fun i =>
    (contDiff_bumpProduct.continuous_iteratedFDeriv (m := i)
      (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_bumpProduct.iteratedFDeriv i)
  choose C hC using key
  refine ⟨|C 0| + |C 1| + |C 2|, by positivity, fun i hi y => ?_⟩
  have h := hC i y
  interval_cases i <;> linarith [abs_nonneg (C 0), abs_nonneg (C 1), abs_nonneg (C 2),
    le_abs_self (C 0), le_abs_self (C 1), le_abs_self (C 2)]
theorem derivNormBound_bumpProduct_scaled {C B : ℝ}
    (hC : ∀ i ≤ 2, ∀ q, ‖iteratedFDeriv ℝ i bumpProduct q‖ ≤ C) (hB : 0 < B) (a : Fin 4 → ℝ) :
    DerivNormBound C B⁻¹ fun p => ∏ μ, sqPartitionBump ((p μ - a μ) / B) := by
  have hBi : 0 ≤ B⁻¹ := inv_nonneg.2 hB.le
  set T : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) := B⁻¹ • ContinuousLinearMap.id ℝ _ with hT
  have hTn : ‖T‖ ≤ B⁻¹ := by
    rw [hT]
    refine (norm_smul_le B⁻¹ (ContinuousLinearMap.id ℝ (Fin 4 → ℝ))).trans ?_
    rw [Real.norm_of_nonneg hBi]
    exact mul_le_of_le_one_right hBi ContinuousLinearMap.norm_id_le
  have hfun : (fun p : Fin 4 → ℝ => ∏ μ, sqPartitionBump ((p μ - a μ) / B)) =
      fun p => (bumpProduct ∘ T) (p - a) := by
    funext p
    simp [bumpProduct, hT, div_eq_inv_mul]
  rw [hfun]
  have hsm : ContDiff ℝ ∞ (bumpProduct ∘ T) := contDiff_bumpProduct.comp T.contDiff
  refine ⟨(hsm.of_le two_le_infty).comp (contDiff_id.sub contDiff_const),
    fun i hi p => ?_⟩
  rw [iteratedFDeriv_comp_sub, T.iteratedFDeriv_comp_right contDiff_bumpProduct _
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul (hC i hi _) (pow_le_pow_left₀ (norm_nonneg _) hTn i) (by positivity)
    ((norm_nonneg _).trans (hC i hi 0))
theorem exists_addCircle_rep_Ico {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    ∃ v : ℝ, v ∈ Ico (-(S / 2)) (S / 2) ∧ (v : AddCircle S) = θ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_centred_rep <;> assumption
theorem circleCentredRep_spec {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    circleCentredRep θ ∈ Ico (-(S / 2)) (S / 2) ∧ (circleCentredRep θ : AddCircle S) = θ :=
  Classical.epsilon_spec (exists_addCircle_rep_Ico hS θ)
theorem sqPartitionBump_div_eq_of_coe_eq {S B a b : ℝ} (hS : 0 < S) (hB : 0 < B) (hBS : B ≤ S / 2)
    (hab : (a : AddCircle S) = b) (ha : |a| < 2 / 3 * S) (hb : |b| ≤ S / 2) :
    sqPartitionBump (a / B) = sqPartitionBump (b / B) :=
  _root_.YangMills.Construction.PartitionCubes.ProductBump.sqPartitionBump_div_eq_of_coe_eq (S := S) (B := B) (a := a) (b := b) hS hB hBS hab ha hb
theorem sqPartitionBump_circleCentredRep_eq_near {S B w₀ w : ℝ} (hS : 0 < S) (hB : 0 < B)
    (hBS : B ≤ S / 2) (hw : |w - w₀| < S / 6) :
    sqPartitionBump (circleCentredRep (w : AddCircle S) / B) =
      sqPartitionBump ((w - (round (w₀ / S) : ℤ) * S) / B) := by
  set n : ℤ := round (w₀ / S) with hn
  have hnear : |w₀ - n * S| ≤ S / 2 := by
    have h := abs_sub_round (w₀ / S)
    have e : w₀ - n * S = (w₀ / S - n) * S := by field_simp
    rw [e, abs_mul, abs_of_pos hS]
    nlinarith
  have hsize : |w - n * S| < 2 / 3 * S := by
    have e : w - n * S = (w - w₀) + (w₀ - n * S) := by ring
    have h := abs_add_le (w - w₀) (w₀ - n * S)
    rw [e]
    linarith
  have hcoe : ((w - n * S : ℝ) : AddCircle S) = (circleCentredRep (w : AddCircle S) : ℝ) := by
    have hz : ((n * S : ℝ) : AddCircle S) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩
    rw [AddCircle.coe_sub, hz, sub_zero, (circleCentredRep_spec hS _).2]
  have hb : |circleCentredRep (w : AddCircle S)| ≤ S / 2 := by
    have h := (circleCentredRep_spec hS (w : AddCircle S)).1
    exact abs_le.2 ⟨h.1, h.2.le⟩
  exact (sqPartitionBump_div_eq_of_coe_eq hS hB hBS hcoe hsize hb).symm
theorem derivNormBound_periodicBump {C S B : ℝ}
    (hC : ∀ i ≤ 2, ∀ q, ‖iteratedFDeriv ℝ i bumpProduct q‖ ≤ C) (hS : 0 < S) (hB : 0 < B)
    (hBS : B ≤ S / 2) (c : Fin 4 → ℝ) :
    DerivNormBound C B⁻¹ fun p : Fin 4 → ℝ =>
      ∏ μ, sqPartitionBump (circleCentredRep ((p μ - c μ : ℝ) : AddCircle S) / B) := by
  have hloc : ∀ p₀ : Fin 4 → ℝ, ∃ a : Fin 4 → ℝ,
      (fun p : Fin 4 → ℝ =>
        ∏ μ, sqPartitionBump (circleCentredRep ((p μ - c μ : ℝ) : AddCircle S) / B)) =ᶠ[𝓝 p₀]
      fun p => ∏ μ, sqPartitionBump ((p μ - a μ) / B) := by
    intro p₀
    refine ⟨fun μ => c μ + (round ((p₀ μ - c μ) / S) : ℤ) * S, ?_⟩
    filter_upwards [Metric.ball_mem_nhds p₀ (show 0 < S / 6 by positivity)] with p hp
    refine Finset.prod_congr rfl fun μ _ => ?_
    have hcoord : |(p μ - c μ) - (p₀ μ - c μ)| < S / 6 := by
      have h1 : ‖p - p₀‖ < S / 6 := by simpa [dist_eq_norm] using hp
      have h2 := norm_le_pi_norm (p - p₀) μ
      rw [Real.norm_eq_abs, Pi.sub_apply] at h2
      rw [sub_sub_sub_cancel_right]
      linarith
    rw [sqPartitionBump_circleCentredRep_eq_near hS hB hBS hcoord, sub_sub]
  refine ⟨?_, fun i hi p₀ => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p₀
    obtain ⟨a, ha⟩ := hloc p₀
    exact (derivNormBound_bumpProduct_scaled hC hB a).contDiff.contDiffAt.congr_of_eventuallyEq ha
  · obtain ⟨a, ha⟩ := hloc p₀
    rw [← iteratedFDerivWithin_univ, Filter.EventuallyEq.iteratedFDerivWithin_eq
      (by rwa [nhdsWithin_univ]) (Filter.EventuallyEq.eq_of_nhds ha) i, iteratedFDerivWithin_univ]
    exact (derivNormBound_bumpProduct_scaled hC hB a).norm_le i hi p₀
theorem supNorm_eq_norm {S : ℝ} (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem supSetDist_singleton {S : ℝ} (x : PeriodicTorus 4 S) (A : Set (PeriodicTorus 4 S)) :
    supSetDist {x} A = Metric.infEDist x A := by
  simp only [supSetDist, mem_singleton_iff, iInf_iInf_eq_left, Metric.infEDist, edist_dist,
    dist_eq_norm, supNorm_eq_norm]
theorem isClosed_thicken {𝒮 : NestedRegions} {M : ℕ} (Q : LevelCube 𝒮 M) (ς : ℝ) :
    IsClosed (Q.thicken ς) := by
  have h : Q.thicken ς =
      {x | Metric.infEDist x Q.supp ≤ ENNReal.ofReal (ς * mollifyRadius 𝒮 M Q.level)} := by
    ext x
    simp only [LevelCube.thicken, mem_ofPred_eq, supSetDist_singleton]
  rw [h]
  exact isClosed_le Metric.continuous_infEDist continuous_const
theorem isClosed_le_distToOutside (𝒮 : NestedRegions) (n : ℕ) (c : ENNReal) :
    IsClosed {x : 𝒮.Point | c ≤ distToOutside 𝒮 n x} := by
  have h : {x : 𝒮.Point | c ≤ distToOutside 𝒮 n x} =
      {x | c ≤ Metric.infEDist x (closure (𝒮.Ω n)ᶜ)} := by
    ext x
    simp only [distToOutside, mem_ofPred_eq, supSetDist_singleton]
  rw [h]
  exact isClosed_le continuous_const Metric.continuous_infEDist
theorem measurableSet_borel_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsClosed A) : MeasurableSet[borel X] A := by
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  exact h.measurableSet
def SmoothedIndicatorBound (C₀ : ℝ) : Prop :=
  ∀ (𝒮 : NestedRegions) (r : ℝ), 0 < r →
    ∀ A : Set 𝒮.Point, MeasurableSet[borel 𝒮.Point] A →
      (∀ x, 0 ≤ smoothedIndicator r A x) ∧
      (∀ x, smoothedIndicator r A x ≤ 1) ∧
      ContDiff ℝ ∞ (fun p : Fin 4 → ℝ =>
        smoothedIndicator r A (torusProj 4 𝒮.side p)) ∧
      ∀ i ≤ 2, ∀ (μ : Fin i → Fin 4) (p : Fin 4 → ℝ),
        |iteratedFDeriv ℝ i (fun p : Fin 4 → ℝ =>
            smoothedIndicator r A (torusProj 4 𝒮.side p)) p
          fun k => Pi.single (μ k) 1| ≤ C₀ * r⁻¹ ^ i
theorem smoothedIndicator_mem_and_bound {C₀ : ℝ} (h : SmoothedIndicatorBound C₀) {𝒮 : NestedRegions}
    {r : ℝ} (hr : 0 < r) {A : Set 𝒮.Point} (hA : IsClosed A) :
    (∀ x, smoothedIndicator r A x ∈ Icc (0 : ℝ) 1) ∧
      DerivNormBound (16 * |C₀|) r⁻¹ fun p => smoothedIndicator r A (torusProj 4 𝒮.side p) := by
  obtain ⟨h0, h1, hs, hd⟩ := h 𝒮 r hr A (measurableSet_borel_of_isClosed hA)
  have hri : 0 ≤ r⁻¹ := inv_nonneg.2 hr.le
  refine ⟨fun x => ⟨h0 x, h1 x⟩, derivNormBound_of_partials (abs_nonneg _) hri
    (hs.of_le two_le_infty) fun i hi μ p => (hd i hi μ p).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hri i)
theorem mollifyRadius_pos {𝒮 : NestedRegions} {K m M R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁)
    (n : ℕ) : 0 < mollifyRadius 𝒮 M n := by
  have h13 := 𝒮.thirteen_le_L
  have hL : (0 : ℝ) < 𝒮.L := by exact_mod_cast (by omega : 0 < 𝒮.L)
  have hM : (0 : ℝ) < M := by
    have h1 := h.separated.blockSize_isPowerGe.1
    exact_mod_cast (by omega : 0 < M)
  have hs : 0 < 𝒮.scale n := mul_pos (zpow_pos hL _) 𝒮.ξ_pos
  exact div_pos (mul_pos hM hs) (by positivity)
theorem mollifyRadius_le_succ {𝒮 : NestedRegions} {K m M R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁)
    (n : ℕ) : mollifyRadius 𝒮 M n ≤ mollifyRadius 𝒮 M (n + 1) := by
  have h13 := 𝒮.thirteen_le_L
  have hL1 : (1 : ℝ) ≤ 𝒮.L := by exact_mod_cast (by omega : 1 ≤ 𝒮.L)
  have hM : (0 : ℝ) < M := by
    have h1 := h.separated.blockSize_isPowerGe.1
    exact_mod_cast (by omega : 0 < M)
  have hs : 𝒮.scale n ≤ 𝒮.scale (n + 1) := by
    apply mul_le_mul_of_nonneg_right _ 𝒮.ξ_pos.le
    exact zpow_le_zpow_right₀ hL1 (by push_cast; omega)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hM.le) (by positivity)
theorem levelTransition_mem_and_bound {C₀ : ℝ} (h : SmoothedIndicatorBound C₀) {𝒮 : NestedRegions}
    {M n : ℕ} {R : ℝ} (hR : 0 < R) (hRn : R ≤ mollifyRadius 𝒮 M n) :
    (∀ x, levelTransition 𝒮 M n x ∈ Icc (0 : ℝ) 1) ∧
      DerivNormBound (2 ^ 2 * (16 * |C₀|)) R⁻¹
        fun p => levelTransition 𝒮 M n (torusProj 4 𝒮.side p) := by
  have hr : 0 < mollifyRadius 𝒮 M n := hR.trans_le hRn
  obtain ⟨hv, hb⟩ := smoothedIndicator_mem_and_bound h (𝒮 := 𝒮) (half_pos hr)
    (isClosed_le_distToOutside 𝒮 n (ENNReal.ofReal (3 / 2 * mollifyRadius 𝒮 M n)))
  have hRi : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
  have hinv : (mollifyRadius 𝒮 M n / 2)⁻¹ ≤ 2 * R⁻¹ := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hR hRn) (by norm_num)
  have hb' : DerivNormBound (16 * |C₀|) (2 * R⁻¹) fun p =>
      levelTransition 𝒮 M n (torusProj 4 𝒮.side p) :=
    hb.mono le_rfl (by positivity) (inv_nonneg.2 (half_pos hr).le) hinv
  exact ⟨hv, hb'.rescale (by positivity) (by norm_num) hRi⟩
theorem sin_pi_div_two_mul_mem_Icc {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    Real.sin (Real.pi / 2 * y) ∈ Icc (0 : ℝ) 1 := by
  have hp := Real.pi_pos
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (by positivity) hy.1)
    (by nlinarith [hy.1, hy.2]), Real.sin_le_one _⟩
theorem cos_pi_div_two_mul_mem_Icc {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    Real.cos (Real.pi / 2 * y) ∈ Icc (0 : ℝ) 1 := by
  have hp := Real.pi_pos
  exact ⟨Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by nlinarith [hy.1, hy.2])
    (by nlinarith [hy.1, hy.2]), Real.cos_le_one _⟩
theorem contDiff_sin_pi_div_two_mul : ContDiff ℝ ∞ fun y : ℝ => Real.sin (Real.pi / 2 * y) :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
theorem contDiff_cos_pi_div_two_mul : ContDiff ℝ ∞ fun y : ℝ => Real.cos (Real.pi / 2 * y) :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
theorem sinCutoff_mem_and_bound {C₀ Cs : ℝ} (h : SmoothedIndicatorBound C₀) (hCs0 : 0 ≤ Cs)
    (hCs : ∀ i ≤ 2, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ i (fun y : ℝ => Real.sin (Real.pi / 2 * y)) y‖ ≤ Cs)
    {𝒮 : NestedRegions} {M n : ℕ} {R : ℝ} (hR : 0 < R) (hRn : R ≤ mollifyRadius 𝒮 M n) :
    (∀ x, sinCutoff 𝒮 M n x ∈ Icc (0 : ℝ) 1) ∧
      DerivNormBound (1 + 2 * Cs * (2 ^ 2 * (16 * |C₀|) + 1) ^ 2) R⁻¹
        fun p => sinCutoff 𝒮 M n (torusProj 4 𝒮.side p) := by
  have hRi : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
  have hW : 0 ≤ 2 * Cs * (2 ^ 2 * (16 * |C₀|) + 1) ^ 2 := by positivity
  by_cases hn : n = 0
  · subst hn
    have e : ∀ x, sinCutoff 𝒮 M 0 x = 1 := fun x => by simp [sinCutoff]
    refine ⟨fun x => by simp [e], ?_⟩
    simp only [e]
    exact (derivNormBound_const_one hRi).mono (by linarith) (by linarith) hRi le_rfl
  · obtain ⟨hv, hb⟩ := levelTransition_mem_and_bound h hR hRn
    have e : ∀ x, sinCutoff 𝒮 M n x = Real.sin (Real.pi / 2 * levelTransition 𝒮 M n x) :=
      fun x => by simp [sinCutoff, hn]
    refine ⟨fun x => by rw [e]; exact sin_pi_div_two_mul_mem_Icc (hv x), ?_⟩
    simp only [e]
    exact (hb.comp (by positivity) hRi hCs0 (contDiff_sin_pi_div_two_mul.of_le two_le_infty)
      (fun p => hv _) hCs).mono (by linarith) (by linarith) hRi le_rfl
theorem cosCutoff_mem_and_bound {C₀ Cc : ℝ} (h : SmoothedIndicatorBound C₀) (hCc0 : 0 ≤ Cc)
    (hCc : ∀ i ≤ 2, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ i (fun y : ℝ => Real.cos (Real.pi / 2 * y)) y‖ ≤ Cc)
    {𝒮 : NestedRegions} {M n : ℕ} {R : ℝ} (hR : 0 < R) (hRn : R ≤ mollifyRadius 𝒮 M n) :
    (∀ x, cosCutoff 𝒮 M n x ∈ Icc (0 : ℝ) 1) ∧
      DerivNormBound (2 * Cc * (2 ^ 2 * (16 * |C₀|) + 1) ^ 2) R⁻¹
        fun p => cosCutoff 𝒮 M n (torusProj 4 𝒮.side p) := by
  have hRi : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
  obtain ⟨hv, hb⟩ := levelTransition_mem_and_bound h hR hRn
  refine ⟨fun x => cos_pi_div_two_mul_mem_Icc (hv x), ?_⟩
  exact hb.comp (by positivity) hRi hCc0 (contDiff_cos_pi_div_two_mul.of_le two_le_infty)
    (fun p => hv _) hCc
theorem productBump_mem_Icc {𝒮 : NestedRegions} {M : ℕ} (Q : LevelCube 𝒮 M) (x : 𝒮.Point) :
    Q.productBump x ∈ Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun _ _ => sqPartitionBump_spec.nonneg _,
    Finset.prod_le_one (fun _ _ => sqPartitionBump_spec.nonneg _)
      fun _ _ => sqPartitionBump_spec.le_one _⟩
theorem derivNormBound_productBump {C : ℝ}
    (hC : ∀ i ≤ 2, ∀ q, ‖iteratedFDeriv ℝ i bumpProduct q‖ ≤ C)
    {𝒮 : NestedRegions} {M : ℕ} (Q : LevelCube 𝒮 M) (hB : 0 < cubeSide 𝒮 M Q.level)
    (hBS : cubeSide 𝒮 M Q.level ≤ 𝒮.side / 2) :
    DerivNormBound C (cubeSide 𝒮 M Q.level)⁻¹ fun p => Q.productBump (torusProj 4 𝒮.side p) := by
  choose c hc using fun μ => QuotientAddGroup.mk_surjective (Q.centre μ)
  have hc' : ∀ μ, ((c μ : ℝ) : AddCircle 𝒮.side) = Q.centre μ := hc
  have e : (fun p => Q.productBump (torusProj 4 𝒮.side p)) = fun p : Fin 4 → ℝ => ∏ μ,
      sqPartitionBump (circleCentredRep ((p μ - c μ : ℝ) : AddCircle 𝒮.side) /
        cubeSide 𝒮 M Q.level) := by
    funext p
    simp only [LevelCube.productBump, torusProj, AddCircle.coe_sub, hc']
  rw [e]
  exact derivNormBound_periodicBump hC 𝒮.side_pos hB hBS c
theorem boundedDerivsAtScale_of_derivNormBound {𝒮 : NestedRegions} {c r : ℝ} {φ : 𝒮.Point → ℝ}
    (hv : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hb : DerivNormBound c r⁻¹ fun p => φ (torusProj 4 𝒮.side p)) :
    BoundedDerivsAtScale c r φ :=
  ⟨fun x => (hv x).1, fun x => (hv x).2, hb.contDiff, fun i hi μ p =>
    (abs_apply_basis_le_norm _ μ).trans (hb.norm_le i hi p)⟩
theorem claim_holds (hMoll : SmoothedIndicatorDerivBounds)
    (hSides : LevelCubeSides.Statement) : Claim := by
  obtain ⟨C₀, hC₀⟩ := hMoll
  have hMB : SmoothedIndicatorBound C₀ := hC₀
  obtain ⟨Cb, hCb0, hCb⟩ := exists_bound_bumpProduct
  obtain ⟨Cs, hCs0, hCs⟩ := exists_iteratedFDeriv_bound_Icc contDiff_sin_pi_div_two_mul
  obtain ⟨Cc, hCc0, hCc⟩ := exists_iteratedFDeriv_bound_Icc contDiff_cos_pi_div_two_mul
  set Ws : ℝ := 1 + 2 * Cs * (2 ^ 2 * (16 * |C₀|) + 1) ^ 2 with hWs
  set Wc : ℝ := 2 * Cc * (2 ^ 2 * (16 * |C₀|) + 1) ^ 2 with hWc
  have hWs0 : 0 ≤ Ws := by positivity
  have hWc0 : 0 ≤ Wc := by positivity
  set H : ℝ := 4 * (4 * Cb * Ws) * Wc with hH
  set Z : ℝ := (12 : ℝ) ^ 2 * (16 * |C₀|) with hZ
  have hH0 : 0 ≤ H := by positivity
  have hZ0 : 0 ≤ Z := by positivity
  refine ⟨1 + H + Z, by linarith, fun K m M R₁ 𝒮 hseq _ Q => ?_⟩
  have hR : 0 < mollifyRadius 𝒮 M Q.level := mollifyRadius_pos hseq _
  have hRi : 0 ≤ (mollifyRadius 𝒮 M Q.level)⁻¹ := inv_nonneg.2 hR.le
  have hc0 : 0 ≤ 1 + H + Z := by linarith
  have hLpos : (1 : ℝ) ≤ 6 * (𝒮.L : ℝ) := by
    have h13 := 𝒮.thirteen_le_L
    have : (1 : ℝ) ≤ 𝒮.L := by exact_mod_cast (by omega : 1 ≤ 𝒮.L)
    linarith
  obtain ⟨-, hside, -⟩ := hSides 𝒮 K m M R₁ hseq Q.level Q.level_le
  have hB : 0 < cubeSide 𝒮 M Q.level := by
    have hR' := hR
    simp only [mollifyRadius] at hR'
    by_contra hn
    have : cubeSide 𝒮 M Q.level / (6 * (𝒮.L : ℝ)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) (by linarith)
    linarith
  have hRB : mollifyRadius 𝒮 M Q.level ≤ cubeSide 𝒮 M Q.level := div_le_self hB.le hLpos
  have hg := (derivNormBound_productBump hCb Q hB (by linarith)).mono le_rfl hCb0
    (inv_nonneg.2 hB.le) (inv_anti₀ hR hRB)
  obtain ⟨hsv, hsb⟩ := sinCutoff_mem_and_bound hMB hCs0 hCs (𝒮 := 𝒮) (M := M) (n := Q.level) hR le_rfl
  obtain ⟨hcv, hcb⟩ := cosCutoff_mem_and_bound hMB hCc0 hCc (𝒮 := 𝒮) (M := M) (n := Q.level + 1) hR
    (mollifyRadius_le_succ hseq _)
  have hpart := (hg.mul hsb hCb0 hWs0 hRi).mul hcb (by positivity) hWc0 hRi
  have hcut : ∀ ς : ℝ, (∀ x, smoothedIndicator (mollifyRadius 𝒮 M Q.level / 12) (Q.thicken ς) x ∈
        Icc (0 : ℝ) 1) ∧
      DerivNormBound Z (mollifyRadius 𝒮 M Q.level)⁻¹ fun p =>
        smoothedIndicator (mollifyRadius 𝒮 M Q.level / 12) (Q.thicken ς) (torusProj 4 𝒮.side p) := by
    intro ς
    have hr12 : 0 < mollifyRadius 𝒮 M Q.level / 12 := by positivity
    obtain ⟨hv, hb⟩ := smoothedIndicator_mem_and_bound hMB hr12 (isClosed_thicken Q ς)
    have e : (mollifyRadius 𝒮 M Q.level / 12)⁻¹ = 12 * (mollifyRadius 𝒮 M Q.level)⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    rw [e] at hb
    exact ⟨hv, hb.rescale (by positivity) (by norm_num) hRi⟩
  refine ⟨boundedDerivsAtScale_of_derivNormBound (fun x => ?_)
      (hpart.mono (by linarith) hc0 hRi le_rfl),
    boundedDerivsAtScale_of_derivNormBound (hcut _).1
      ((hcut _).2.mono (by linarith) hc0 hRi le_rfl),
    boundedDerivsAtScale_of_derivNormBound (hcut _).1
      ((hcut _).2.mono (by linarith) hc0 hRi le_rfl)⟩
  have h1 := productBump_mem_Icc Q x
  have h2 := hsv x
  have h3 := hcv x
  exact ⟨mul_nonneg (mul_nonneg h1.1 h2.1) h3.1,
    mul_le_one₀ (mul_le_one₀ h1.2 h2.1 h2.2) h3.1 h3.2⟩
end YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds
