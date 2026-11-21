import YangMills.Construction.ResponseInTheExpansion.PairSymbolOverALattice
import YangMills.Construction.ResponseInTheExpansion.SumOverMomentaOfTheCurlCurl
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.LinearResponse YangMills.Construction.LatticeFourier YangMills.Construction.TorusFields
namespace DoubleCurlSum
private lemma sum_indicator_mul_indicator (x y : Fin 4) (A B : ℝ) :
    ∑ m : Fin 4, (if m = x then A else 0) * (if m = y then B else 0) =
      (if x = y then 1 else 0) * (A * B) := by
  by_cases hxy : x = y
  · subst hxy
    simp [Finset.sum_ite_eq', ← ite_and, ite_mul, mul_ite]
  · have hzero : ∀ m : Fin 4, (if m = x then A else 0) * (if m = y then B else 0) = 0 := by
      intro m
      by_cases hmx : m = x
      · have hmy : m ≠ y := fun hmy => hxy (hmx ▸ hmy)
        simp [hmy]
      · simp [hmx]
    simp [hzero, hxy]
private lemma doubleCurlSymbol_eq (μ ν ρ τ : Fin 4) (p : Fin 4 → ℝ) :
    doubleCurlSymbol μ ν ρ τ p =
      ((((if ν = τ then 1 else 0) * (p μ * p ρ) - (if ν = ρ then 1 else 0) * (p μ * p τ) -
        (if μ = τ then 1 else 0) * (p ν * p ρ) + (if μ = ρ then 1 else 0) * (p ν * p τ) : ℝ) : ℂ)) /
        ((sqNorm p : ℝ) : ℂ) := by
  unfold doubleCurlSymbol
  congr 1
  have hterm : ∀ m : Fin 4, (starRingEnd ℂ) (planeCurl p μ ν m) * planeCurl p ρ τ m =
      ((((if m = ν then p μ else 0) - (if m = μ then p ν else 0)) *
        ((if m = τ then p ρ else 0) - (if m = ρ then p τ else 0)) : ℝ) : ℂ) := by
    intro m
    unfold planeCurl
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    have hrw : -Complex.I * (((if m = ν then p μ else 0) - (if m = μ then p ν else 0) : ℝ) : ℂ) *
        (Complex.I * (((if m = τ then p ρ else 0) - (if m = ρ then p τ else 0) : ℝ) : ℂ)) =
        -(Complex.I * Complex.I) * ((((if m = ν then p μ else 0) - (if m = μ then p ν else 0) : ℝ) : ℂ) *
          (((if m = τ then p ρ else 0) - (if m = ρ then p τ else 0) : ℝ) : ℂ)) := by ring
    rw [hrw, Complex.I_mul_I]
    push_cast
    ring
  simp only [hterm]
  rw [← Complex.ofReal_sum]
  congr 1
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, sum_indicator_mul_indicator]
  ring
private lemma curvatureKernel_eq_hessian (z : Fin 4 → ℝ) (μ ν ρ τ : Fin 4) (hz : sqNorm z ≠ 0) :
    continuumCurvatureKernel z μ ν ρ τ =
      (if ν = τ then 1 else 0) * greenHessian z μ ρ - (if ν = ρ then 1 else 0) * greenHessian z μ τ -
        (if μ = τ then 1 else 0) * greenHessian z ν ρ + (if μ = ρ then 1 else 0) * greenHessian z ν τ := by
  have hs : ∑ i, z i ^ 2 = sqNorm z := rfl
  unfold continuumCurvatureKernel hyperplaneReflection greenHessian
  rw [hs]
  set s := sqNorm z
  generalize (if μ = ρ then (1 : ℝ) else 0) = d1
  generalize (if ν = τ then (1 : ℝ) else 0) = d2
  generalize (if μ = τ then (1 : ℝ) else 0) = d3
  generalize (if ν = ρ then (1 : ℝ) else 0) = d4
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring
private lemma sum_nonzero_sites_eq_tsum (N : ℕ) [NeZero N] (hN : 8 ≤ N) (G : (Fin 4 → ℤ) → ℂ)
    (hG0 : G 0 = 0) (hfar : ∀ k, 1 ≤ ∑ i, circleMomentum N (k i) ^ 2 → G k = 0) :
    ∑ j ∈ (Finset.univ : Finset (TorusSite N)).erase 0, G (fun i => (j i).valMinAbs) = ∑' k, G k := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set lift : TorusSite N → (Fin 4 → ℤ) := fun j i => (j i).valMinAbs with hlift
  have hinj : Function.Injective lift := by
    intro j j' h
    funext i
    have hi := congrFun h i
    have hcast := congrArg (fun n : ℤ => (n : ZMod N)) hi
    simpa [hlift, ZMod.coe_valMinAbs] using hcast
  have hlift0 : lift 0 = 0 := by
    funext i
    simp [hlift]
  rw [tsum_eq_sum (s := ((Finset.univ : Finset (TorusSite N)).erase 0).image lift) ?_,
    Finset.sum_image hinj.injOn]
  intro k hk
  by_cases hk0 : k = 0
  · rw [hk0, hG0]
  by_cases hs : 1 ≤ ∑ i, circleMomentum N (k i) ^ 2
  · exact hfar k hs
  exfalso
  apply hk
  push Not at hs
  set j : TorusSite N := fun i => (k i : ZMod N) with hj
  have hjk : lift j = k := by
    funext i
    have h1 : circleMomentum N (k i) ^ 2 < 1 :=
      (Finset.single_le_sum (f := fun i => circleMomentum N (k i) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)).trans_lt hs
    have h2 : |circleMomentum N (k i)| < 1 := by
      have habs := abs_lt_of_sq_lt_sq (a := circleMomentum N (k i)) (b := 1) (by simpa using h1) zero_le_one
      exact habs
    have h3 : |(k i : ℝ)| * 2 < N := by
      unfold circleMomentum at h2
      rw [abs_div, abs_mul, abs_of_pos hNpos, div_lt_one hNpos, abs_of_pos (by positivity)] at h2
      have hpi := Real.pi_gt_three
      nlinarith [abs_nonneg (k i : ℝ)]
    have h4 : |k i| * 2 < (N : ℤ) := by exact_mod_cast h3
    refine (ZMod.valMinAbs_spec (j i) (k i)).2 ⟨rfl, ?_, ?_⟩
    · have hle := neg_abs_le (k i)
      omega
    · have hle := le_abs_self (k i)
      omega
  refine Finset.mem_image.2 ⟨j, Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩, hjk⟩
  intro hj0
  apply hk0
  rw [← hjk, hj0, hlift0]
private lemma weighted_doubleCurl_term_eq (χ : (Fin 4 → ℝ) → ℝ) (N : ℕ) (z : Fin 4 → ℝ)
    (μ ν ρ τ : Fin 4) (k : Fin 4 → ℤ) :
    (χ (fun i => circleMomentum N (k i)) : ℂ) * doubleCurlSymbol μ ν ρ τ (fun i => circleMomentum N (k i)) *
        Complex.exp (Complex.I * ((∑ i, circleMomentum N (k i) * z i : ℝ) : ℂ)) =
      (((if ν = τ then 1 else 0 : ℝ)) : ℂ) * cutPairSymbolTerm χ N z μ ρ k -
        (((if ν = ρ then 1 else 0 : ℝ)) : ℂ) * cutPairSymbolTerm χ N z μ τ k -
        (((if μ = τ then 1 else 0 : ℝ)) : ℂ) * cutPairSymbolTerm χ N z ν ρ k +
        (((if μ = ρ then 1 else 0 : ℝ)) : ℂ) * cutPairSymbolTerm χ N z ν τ k := by
  rw [doubleCurlSymbol_eq]
  simp only [cutPairSymbolTerm, sqNorm]
  generalize (if μ = ρ then (1 : ℝ) else 0) = d1
  generalize (if ν = τ then (1 : ℝ) else 0) = d2
  generalize (if μ = τ then (1 : ℝ) else 0) = d3
  generalize (if ν = ρ then (1 : ℝ) else 0) = d4
  push_cast
  ring
private lemma norm_indicator_le_one (c : Prop) [Decidable c] :
    ‖(((if c then 1 else 0 : ℝ)) : ℂ)‖ ≤ 1 := by
  split_ifs <;> simp
end DoubleCurlSum
open DoubleCurlSum in
theorem curlCurlMomentumSum_of_cutPairSymbolLattice (hP : cutPairSymbolLatticeStatement) :
    curlCurlMomentumSumStatement := by
  intro χ hχ hnear hfar
  obtain ⟨C, hC⟩ := hP χ hχ hnear hfar
  refine ⟨4 * C, 8, fun N _ μ ν ρ τ z hN _ _ hz1 hzN => ?_⟩
  have hN8 : 8 ≤ N := by exact_mod_cast hN
  have hz1' : 1 ≤ ∑ i, z i ^ 2 := hz1
  have hzN' : ∑ i, z i ^ 2 ≤ ((N : ℝ) / 8) ^ 2 := hzN
  have hz0 : sqNorm z ≠ 0 := by
    intro h
    rw [h] at hz1
    norm_num at hz1
  have hp := fun a b => hC N z a b hN8 hz1' hzN'
  set G : (Fin 4 → ℤ) → ℂ := fun k =>
    (χ (fun i => circleMomentum N (k i)) : ℂ) * doubleCurlSymbol μ ν ρ τ (fun i => circleMomentum N (k i)) *
      Complex.exp (Complex.I * ((∑ i, circleMomentum N (k i) * z i : ℝ) : ℂ)) with hG
  have hG0 : G 0 = 0 := by
    have hm : circleMomentum N 0 = 0 := by simp [circleMomentum]
    simp only [hG, Pi.zero_apply, hm]
    rw [doubleCurlSymbol_eq]
    simp
  have hGfar : ∀ k, 1 ≤ ∑ i, circleMomentum N (k i) ^ 2 → G k = 0 := by
    intro k hk
    have hχk : χ (fun i => circleMomentum N (k i)) = 0 := hfar _ hk
    simp [hG, hχk]
  have hwave : nonzeroMomentumWave N (fun p => (χ p : ℂ) * doubleCurlSymbol μ ν ρ τ p) z =
      ((N : ℂ) ^ 4)⁻¹ * ∑' k, G k := by
    rw [← sum_nonzero_sites_eq_tsum N hN8 G hG0 hGfar]
    rfl
  have hGfun : G = fun k => (((if ν = τ then 1 else 0 : ℝ)) : ℂ) * cutPairSymbolTerm χ N z μ ρ k -
      (((if ν = ρ then 1 else 0 : ℝ)) : ℂ) * cutPairSymbolTerm χ N z μ τ k -
      (((if μ = τ then 1 else 0 : ℝ)) : ℂ) * cutPairSymbolTerm χ N z ν ρ k +
      (((if μ = ρ then 1 else 0 : ℝ)) : ℂ) * cutPairSymbolTerm χ N z ν τ k :=
    funext fun k => weighted_doubleCurl_term_eq χ N z μ ν ρ τ k
  have hsum := ((((hp μ ρ).1.hasSum.mul_left (((if ν = τ then 1 else 0 : ℝ)) : ℂ)).sub
    ((hp μ τ).1.hasSum.mul_left (((if ν = ρ then 1 else 0 : ℝ)) : ℂ))).sub
    ((hp ν ρ).1.hasSum.mul_left (((if μ = τ then 1 else 0 : ℝ)) : ℂ))).add
    ((hp ν τ).1.hasSum.mul_left (((if μ = ρ then 1 else 0 : ℝ)) : ℂ))
  rw [← hGfun] at hsum
  rw [hwave, hsum.tsum_eq, curvatureKernel_eq_hessian z μ ν ρ τ hz0]
  set B : ℝ := C * ((∑ i, z i ^ 2) ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ))) with hB
  have hb := fun a b => (hp a b).2
  set E : Fin 4 → Fin 4 → ℂ := fun a b =>
    ((N : ℂ) ^ 4)⁻¹ * ∑' k, cutPairSymbolTerm χ N z a b k - (greenHessian z a b : ℂ) with hE
  have hE' : ∀ a b, ‖E a b‖ ≤ B := hb
  have hkey : ∀ (c : Prop) [Decidable c] (a b : Fin 4),
      ‖(((if c then 1 else 0 : ℝ)) : ℂ) * E a b‖ ≤ B := by
    intro c _ a b
    rw [norm_mul]
    calc _ ≤ 1 * B := mul_le_mul (norm_indicator_le_one c) (hE' a b) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  have hsplit : ((N : ℂ) ^ 4)⁻¹ * ((((if ν = τ then 1 else 0 : ℝ)) : ℂ) * ∑' k, cutPairSymbolTerm χ N z μ ρ k -
        (((if ν = ρ then 1 else 0 : ℝ)) : ℂ) * ∑' k, cutPairSymbolTerm χ N z μ τ k -
        (((if μ = τ then 1 else 0 : ℝ)) : ℂ) * ∑' k, cutPairSymbolTerm χ N z ν ρ k +
        (((if μ = ρ then 1 else 0 : ℝ)) : ℂ) * ∑' k, cutPairSymbolTerm χ N z ν τ k) -
      (((if ν = τ then 1 else 0) * greenHessian z μ ρ - (if ν = ρ then 1 else 0) * greenHessian z μ τ -
        (if μ = τ then 1 else 0) * greenHessian z ν ρ +
        (if μ = ρ then 1 else 0) * greenHessian z ν τ : ℝ) : ℂ) =
      (((if ν = τ then 1 else 0 : ℝ)) : ℂ) * E μ ρ - (((if ν = ρ then 1 else 0 : ℝ)) : ℂ) * E μ τ -
        (((if μ = τ then 1 else 0 : ℝ)) : ℂ) * E ν ρ + (((if μ = ρ then 1 else 0 : ℝ)) : ℂ) * E ν τ := by
    simp only [hE]
    generalize (if μ = ρ then (1 : ℝ) else 0) = d1
    generalize (if ν = τ then (1 : ℝ) else 0) = d2
    generalize (if μ = τ then (1 : ℝ) else 0) = d3
    generalize (if ν = ρ then (1 : ℝ) else 0) = d4
    push_cast
    ring
  rw [hsplit]
  have n1 := norm_add_le ((((if ν = τ then 1 else 0 : ℝ)) : ℂ) * E μ ρ -
    (((if ν = ρ then 1 else 0 : ℝ)) : ℂ) * E μ τ - (((if μ = τ then 1 else 0 : ℝ)) : ℂ) * E ν ρ)
    ((((if μ = ρ then 1 else 0 : ℝ)) : ℂ) * E ν τ)
  have n2 := norm_sub_le ((((if ν = τ then 1 else 0 : ℝ)) : ℂ) * E μ ρ -
    (((if ν = ρ then 1 else 0 : ℝ)) : ℂ) * E μ τ) ((((if μ = τ then 1 else 0 : ℝ)) : ℂ) * E ν ρ)
  have n3 := norm_sub_le ((((if ν = τ then 1 else 0 : ℝ)) : ℂ) * E μ ρ)
    ((((if ν = ρ then 1 else 0 : ℝ)) : ℂ) * E μ τ)
  have k1 := hkey (ν = τ) μ ρ
  have k2 := hkey (ν = ρ) μ τ
  have k3 := hkey (μ = τ) ν ρ
  have k4 := hkey (μ = ρ) ν τ
  have hfin : 4 * C * (sqNorm z ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ))) = 4 * B := by
    rw [hB]
    have hsq : sqNorm z = ∑ i, z i ^ 2 := rfl
    rw [hsq]
    ring
  rw [hfin]
  linarith
end YangMills.Construction.ResponseInTheExpansion
