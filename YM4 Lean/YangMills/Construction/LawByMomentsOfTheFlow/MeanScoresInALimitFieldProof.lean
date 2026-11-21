import YangMills.Construction.HullsInEveryVolume.MomentsOfTheSizesOfAHull
import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupport
import YangMills.Construction.LawByMomentsOfTheFlow.TelescopeDefs
import YangMills.Construction.ResponseInTheExpansion.ScoredPriceReturnsProof
import YangMills.Construction.SummableBoundsOfTheFlow.RimMomentsOfALawProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepGas ClusterExpansionOfAStep WeightedResponses ResponseInTheExpansion BlockAverages
  LumpContours ColdStepAtMirrorFrames HullTrees ChainNoise MomentMethod LevelTestFunctions
section Numbers
private theorem one_add_pow_le_two_pow_mul {s : ℝ} (hs : 0 ≤ s) (p : ℕ) : (1 + s) ^ p ≤ 2 ^ p * (1 + s ^ p) := by apply _root_.YangMills.SharedProofs.p7069 <;> assumption
private theorem prod_le_sum_inv_mul_pow {p : ℕ} (hp : 1 ≤ p) (a : Fin p → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∏ i, a i ≤ ∑ i, (p : ℝ)⁻¹ * a i ^ p := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpn : p ≠ 0 := by omega
  have hw : ∑ _i : Fin p, (p : ℝ)⁻¹ = 1 := by
    simp [Finset.card_univ, hp0]
  have key := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin p => (p : ℝ)⁻¹)
    (fun i => a i ^ p) (fun _ _ => by positivity) hw (fun i _ => pow_nonneg (ha i) p)
  have hroot : ∀ i, (a i ^ p) ^ ((p : ℝ)⁻¹) = a i := fun i => Real.pow_rpow_inv_natCast (ha i) hpn
  simpa only [hroot] using key
abbrev _root_.YangMills.SharedProofs.p66653 := @prod_le_sum_inv_mul_pow
private theorem one_add_mean_pow_le {ι : Type} (B : Finset ι) (s : ι → ℝ) (hs : ∀ y, 0 ≤ s y) (p : ℕ) :
    (1 + (B.card : ℝ)⁻¹ * ∑ y ∈ B, s y) ^ p ≤ 1 + ∑ y ∈ B, (B.card : ℝ)⁻¹ * (2 ^ p * (1 + s y ^ p)) := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have hc : (B.card : ℝ) ≠ 0 := by
    have := hB.card_pos
    positivity
  have hc0 : (0 : ℝ) ≤ (B.card : ℝ)⁻¹ := by positivity
  have hw : ∑ _y ∈ B, (B.card : ℝ)⁻¹ = 1 := by
    simp [hc]
  have hform : 1 + (B.card : ℝ)⁻¹ * ∑ y ∈ B, s y = ∑ y ∈ B, (B.card : ℝ)⁻¹ * (1 + s y) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum, hw]
  rw [hform]
  have h1 := Real.pow_arith_mean_le_arith_mean_pow B (fun _ => (B.card : ℝ)⁻¹) (fun y => 1 + s y)
    (fun _ _ => hc0) hw (fun y _ => add_nonneg zero_le_one (hs y)) p
  have h2 : ∑ y ∈ B, (B.card : ℝ)⁻¹ * (1 + s y) ^ p ≤ ∑ y ∈ B, (B.card : ℝ)⁻¹ * (2 ^ p * (1 + s y ^ p)) :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (one_add_pow_le_two_pow_mul (hs y) p) hc0
  linarith
abbrev _root_.YangMills.SharedProofs.p14810 := @one_add_mean_pow_le
private theorem one_add_two_pow_le_eight_mul_pow {C F : ℝ} (hC : 1 ≤ C) (hF : 1 ≤ F) {p : ℕ} (hp : 1 ≤ p) :
    1 + 2 ^ p * (1 + C ^ p * F) ≤ (8 * C) ^ p * F := by
  have hCp : 1 ≤ C ^ p := one_le_pow₀ hC
  have h2p : (2 : ℝ) ≤ 2 ^ p := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have hPF : 1 ≤ C ^ p * F := one_le_mul_of_one_le_of_one_le hCp hF
  have h8 : (8 * C) ^ p * F = 2 ^ p * (2 ^ p * (2 ^ p * (C ^ p * F))) := by
    rw [mul_pow, show (8 : ℝ) = 2 * (2 * 2) by norm_num, mul_pow, mul_pow]
    ring
  rw [h8]
  have h22 : (4 : ℝ) ≤ 2 ^ p * 2 ^ p := by nlinarith
  have hbig : 4 * (C ^ p * F) ≤ 2 ^ p * (2 ^ p * (C ^ p * F)) := by nlinarith
  have h3 : 2 ^ p * (1 + C ^ p * F) ≤ 2 ^ p * (2 ^ p * (2 ^ p * (C ^ p * F)) - 1 / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith
  nlinarith
abbrev _root_.YangMills.SharedProofs.p9521 := @one_add_two_pow_le_eight_mul_pow
private theorem exists_offset_of_circleRep_le {L : ℕ} [NeZero L] {K s u : ℕ} (hus : u ≤ s) (hsK : s ≤ K) {c N : ℕ} (hc : 0 < c)
    (hN : (N : ℝ) = (c : ℝ) * (L : ℝ) ^ (K - u)) {R x₀ zc : ℝ} (hzc : |zc| ≤ R) (v : ℕ)
    (h : |circleRep (c : ℝ) ((v : ℝ) * (L : ℝ) ^ u / (L : ℝ) ^ K - x₀ - (L : ℝ) ^ s / (L : ℝ) ^ K * zc)| ≤
      (L : ℝ) ^ u / (2 * (L : ℝ) ^ K)) :
    ∃ k w : ℤ, (v : ℤ) = round (x₀ * (L : ℝ) ^ K / (L : ℝ) ^ u) + w + (N : ℤ) * k ∧
      |(w : ℝ)| ≤ 1 + R * (L : ℝ) ^ (s - u) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hKu : (L : ℝ) ^ K = (L : ℝ) ^ u * (L : ℝ) ^ (K - u) := by
    rw [← pow_add]
    congr 1
    omega
  have hsu : (L : ℝ) ^ s = (L : ℝ) ^ u * (L : ℝ) ^ (s - u) := by
    rw [← pow_add]
    congr 1
    omega
  have hA : (0 : ℝ) < (L : ℝ) ^ u := by positivity
  have hB : (0 : ℝ) < (L : ℝ) ^ (K - u) := by positivity
  have hD : (0 : ℝ) < (L : ℝ) ^ (s - u) := by positivity
  rw [hKu, hsu] at h
  rw [hKu]
  generalize (L : ℝ) ^ u = A at *
  generalize (L : ℝ) ^ (K - u) = B at *
  generalize (L : ℝ) ^ (s - u) = D at *
  have hτ : (v : ℝ) * A / (A * B) - x₀ - A * D / (A * B) * zc = (v : ℝ) / B - x₀ - D / B * zc := by
    field_simp
  rw [hτ] at h
  have hX : x₀ * (A * B) / A = x₀ * B := by
    field_simp
  rw [hX]
  have hbound : A / (2 * (A * B)) = 1 / (2 * B) := by
    field_simp
  rw [hbound] at h
  unfold circleRep at h
  set k : ℤ := round (((v : ℝ) / B - x₀ - D / B * zc) / (c : ℝ)) with hk
  set e : ℝ := (v : ℝ) / B - x₀ - D / B * zc - (c : ℝ) * (k : ℝ) with he
  refine ⟨k, (v : ℤ) - round (x₀ * B) - (N : ℤ) * k, by ring, ?_⟩
  have hv : (v : ℝ) = B * (e + (c : ℝ) * (k : ℝ) + x₀) + D * zc := by
    rw [he]
    field_simp
    ring
  have hw : (((v : ℤ) - round (x₀ * B) - (N : ℤ) * k : ℤ) : ℝ) =
      B * e + (x₀ * B - (round (x₀ * B) : ℝ)) + D * zc := by
    push_cast
    rw [hN, hv]
    ring
  rw [hw]
  have h1 : |B * e| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hB]
    calc B * |e| ≤ B * (1 / (2 * B)) := mul_le_mul_of_nonneg_left h hB.le
      _ = 1 / 2 := by field_simp
  have h2 : |x₀ * B - (round (x₀ * B) : ℝ)| ≤ 1 / 2 := abs_sub_round _
  have h3 : |D * zc| ≤ R * D := by
    rw [abs_mul, abs_of_pos hD, mul_comm]
    exact mul_le_mul_of_nonneg_right hzc hD.le
  calc |B * e + (x₀ * B - (round (x₀ * B) : ℝ)) + D * zc|
      ≤ |B * e + (x₀ * B - (round (x₀ * B) : ℝ))| + |D * zc| := abs_add_le _ _
    _ ≤ |B * e| + |x₀ * B - (round (x₀ * B) : ℝ)| + |D * zc| := by
        have := abs_add_le (B * e) (x₀ * B - (round (x₀ * B) : ℝ))
        linarith
    _ ≤ 1 + R * D := by linarith
private theorem natCast_inv_mul_self_le_one (n : ℕ) : (n : ℝ)⁻¹ * (n : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · rw [inv_mul_cancel₀ (by positivity)]
private theorem prod_map_le_weighted_sum_pow {ι : Type} {k : ℕ} (J : List (Fin k)) (hp : 1 ≤ J.length) (A : Fin k → Finset ι) (x : ι → ℝ)
    (hx : ∀ z, 0 ≤ x z) :
    (J.map fun a => 1 + ((A a).card : ℝ)⁻¹ * ∑ z ∈ A a, x z).prod ≤
      (1 + 2 ^ J.length) + 2 ^ J.length * ∑ e ∈ (Finset.univ : Finset (Fin J.length)).sigma (fun i => A (J.get i)),
        ((J.length : ℝ)⁻¹ * ((A (J.get e.1)).card : ℝ)⁻¹) * x e.2 ^ J.length := by
  have hp0 : (J.length : ℝ) ≠ 0 := by
    have : 0 < J.length := hp
    positivity
  have h2 : (0 : ℝ) ≤ 2 ^ J.length := by positivity
  obtain ⟨a, ha⟩ : ∃ a : Fin J.length → ℝ, a = fun i => 1 + ((A (J.get i)).card : ℝ)⁻¹ * ∑ z ∈ A (J.get i), x z := ⟨_, rfl⟩
  have ha0 : ∀ i, 0 ≤ a i := fun i => by
    rw [ha]
    exact add_nonneg zero_le_one (mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => hx z))
  have hprod : (J.map fun a => 1 + ((A a).card : ℝ)⁻¹ * ∑ z ∈ A a, x z).prod = ∏ i, a i := by
    rw [ha, ← Fin.prod_univ_fun_getElem]
    rfl
  have hone : ∀ i, a i ^ J.length ≤ (1 + 2 ^ J.length) + 2 ^ J.length * ∑ z ∈ A (J.get i), ((A (J.get i)).card : ℝ)⁻¹ * x z ^ J.length := fun i => by
    have h1 := one_add_mean_pow_le (A (J.get i)) x hx J.length
    have hc : ((A (J.get i)).card : ℝ)⁻¹ * ((A (J.get i)).card : ℝ) ≤ 1 := natCast_inv_mul_self_le_one _
    have h3 : ∑ y ∈ A (J.get i), ((A (J.get i)).card : ℝ)⁻¹ * (2 ^ J.length * (1 + x y ^ J.length)) =
        2 ^ J.length * (((A (J.get i)).card : ℝ)⁻¹ * ((A (J.get i)).card : ℝ)) +
          2 ^ J.length * ∑ z ∈ A (J.get i), ((A (J.get i)).card : ℝ)⁻¹ * x z ^ J.length := by
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun y _ => (by ring : ((A (J.get i)).card : ℝ)⁻¹ * (2 ^ J.length * (1 + x y ^ J.length)) =
        2 ^ J.length * ((A (J.get i)).card : ℝ)⁻¹ + 2 ^ J.length * (((A (J.get i)).card : ℝ)⁻¹ * x y ^ J.length))),
        Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    have h4 := mul_le_mul_of_nonneg_left hc h2
    rw [ha]
    simp only at h1 ⊢
    rw [h3] at h1
    linarith
  rw [hprod]
  calc ∏ i, a i ≤ ∑ i, (J.length : ℝ)⁻¹ * a i ^ J.length := prod_le_sum_inv_mul_pow hp a ha0
    _ ≤ ∑ i : Fin J.length, (J.length : ℝ)⁻¹ * ((1 + 2 ^ J.length) + 2 ^ J.length * ∑ z ∈ A (J.get i), ((A (J.get i)).card : ℝ)⁻¹ * x z ^ J.length) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hone i) (by positivity)
    _ = _ := by
        rw [Finset.sum_sigma]
        simp only [mul_add, Finset.sum_add_distrib]
        have e1 : ∑ _i : Fin J.length, (J.length : ℝ)⁻¹ * (1 + 2 ^ J.length) = 1 + 2 ^ J.length := by
          simp [Finset.card_univ, hp0]
        have e1' : ∑ i : Fin J.length, ((J.length : ℝ)⁻¹ * 1 + (J.length : ℝ)⁻¹ * 2 ^ J.length) = 1 + 2 ^ J.length := by
          rw [← e1]
          exact Finset.sum_congr rfl fun _ _ => by ring
        simp only [mul_one] at e1' ⊢
        rw [Finset.sum_add_distrib] at e1'
        rw [e1', Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        ring
private theorem sum_sigma_weights_le_one {ι : Type} {k : ℕ} (J : List (Fin k)) (A : Fin k → Finset ι) :
    ∑ e ∈ (Finset.univ : Finset (Fin J.length)).sigma (fun i => A (J.get i)), ((J.length : ℝ)⁻¹ * ((A (J.get e.1)).card : ℝ)⁻¹) ≤ 1 := by
  rw [Finset.sum_sigma]
  have h1 : ∀ i : Fin J.length, ∑ _z ∈ A (J.get i), ((J.length : ℝ)⁻¹ * ((A (J.get i)).card : ℝ)⁻¹) ≤ (J.length : ℝ)⁻¹ := fun i => by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((A (J.get i)).card : ℝ) * ((A (J.get i)).card : ℝ)⁻¹ ≤ 1 := by
      rw [mul_comm]
      exact natCast_inv_mul_self_le_one _
    calc ((A (J.get i)).card : ℝ) * ((J.length : ℝ)⁻¹ * ((A (J.get i)).card : ℝ)⁻¹)
        = (J.length : ℝ)⁻¹ * (((A (J.get i)).card : ℝ) * ((A (J.get i)).card : ℝ)⁻¹) := by ring
      _ ≤ (J.length : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := mul_one _
  calc _ ≤ ∑ _i : Fin J.length, (J.length : ℝ)⁻¹ := Finset.sum_le_sum fun i _ => h1 i
    _ ≤ 1 := by
      rcases Nat.eq_zero_or_pos J.length with h | h
      · simp [h]
      · have : (J.length : ℝ) ≠ 0 := by positivity
        simp [Finset.card_univ, this]
private theorem exists_strictMono_const_of_mem_finset {α : Type} (s : Finset α) (f : ℕ → α) (h : ∀ n, f n ∈ s) :
    ∃ (c : α) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ n, f (φ n) = c := by
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber (fun n => (⟨f n, h n⟩ : s))
  have hinf := Set.infinite_coe_iff.mp hy
  have hfr := Nat.frequently_atTop_iff_infinite.mpr hinf
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop hfr
  exact ⟨y.1, φ, hφ, fun n => congrArg Subtype.val (hP n)⟩
end Numbers
section Invariant
variable {J : Type} {P : Measure (TranslateValues J)} [IsProbabilityMeasure P]
private theorem shiftInvariantSigma_le_pi : shiftInvariantSigma J ≤ (inferInstance : MeasurableSpace (TranslateValues J)) := inf_le_right
private theorem invariantCondExp_le_weighted {ι : Type} (s : Finset ι) (f : ι → TranslateValues J → ℝ) (W : ι → ℝ) (hf : ∀ z ∈ s, Integrable (f z) P)
    (hW : ∀ z ∈ s, 0 ≤ W z) (b a e : ℝ) (he : 0 ≤ e) (hb : ∀ z ∈ s, ∀ᵐ v ∂P, invariantCondExp P (f z) v ≤ b)
    {X : TranslateValues J → ℝ} (hX : Integrable X P) (hle : ∀ᵐ v ∂P, X v ≤ a + e * ∑ z ∈ s, W z * f z v) :
    ∀ᵐ v ∂P, invariantCondExp P X v ≤ a + e * ((∑ z ∈ s, W z) * b) := by
  have hg : ∀ z ∈ s, Integrable (fun v => W z * f z v) P := fun z hz => (hf z hz).const_mul _
  have hsum : Integrable (fun v => ∑ z ∈ s, W z * f z v) P := integrable_finsetSum _ hg
  have hR : Integrable (fun v => a + e * ∑ z ∈ s, W z * f z v) P := (integrable_const a).add (hsum.const_mul e)
  have h0 : invariantCondExp P X ≤ᵐ[P] invariantCondExp P (fun v => a + e * ∑ z ∈ s, W z * f z v) := condExp_mono hX hR hle
  have h1 : invariantCondExp P (fun v => ∑ z ∈ s, W z * f z v) =ᵐ[P] ∑ z ∈ s, invariantCondExp P (fun v => W z * f z v) := by
    have := condExp_finsetSum (μ := P) (s := s) (f := fun z v => W z * f z v) hg (shiftInvariantSigma J)
    refine (condExp_congr_ae (ae_of_all _ fun v => ?_)).trans this
    simp
  have h2 : invariantCondExp P (fun v => a + e * ∑ z ∈ s, W z * f z v) =ᵐ[P] (fun v => a + e * invariantCondExp P (fun v => ∑ z ∈ s, W z * f z v) v) := by
    have e1 := condExp_add (μ := P) (integrable_const a) (hsum.const_mul e) (shiftInvariantSigma J)
    have e2 := condExp_smul (μ := P) e (fun v => ∑ z ∈ s, W z * f z v) (shiftInvariantSigma J)
    have e3 : P[fun _ : TranslateValues J => a | shiftInvariantSigma J] = fun _ => a := condExp_const shiftInvariantSigma_le_pi a
    unfold invariantCondExp
    filter_upwards [e1, e2] with v h₁ h₂
    have h₁' : P[fun v => a + e * ∑ z ∈ s, W z * f z v | shiftInvariantSigma J] v =
        (P[fun _ : TranslateValues J => a | shiftInvariantSigma J] + P[fun v => e * ∑ z ∈ s, W z * f z v | shiftInvariantSigma J]) v := h₁
    have h₂' : P[fun v => e * ∑ z ∈ s, W z * f z v | shiftInvariantSigma J] v = e * P[fun v => ∑ z ∈ s, W z * f z v | shiftInvariantSigma J] v := by
      have e4 : (fun v => e * ∑ z ∈ s, W z * f z v) = e • (fun v => ∑ z ∈ s, W z * f z v) := rfl
      rw [e4]
      simpa [smul_eq_mul, Pi.smul_apply] using h₂
    rw [h₁', Pi.add_apply, e3, h₂']
  have h3 : ∀ᵐ v ∂P, ∀ z ∈ s, invariantCondExp P (f z) v ≤ b := (ae_ball_iff s.countable_toSet).2 hb
  have h4 : ∀ᵐ v ∂P, ∀ z ∈ s, invariantCondExp P (fun v => W z * f z v) v = W z * invariantCondExp P (f z) v :=
    (ae_ball_iff s.countable_toSet).2 fun z _ => by
      have e2 := condExp_smul (μ := P) (W z) (f z) (shiftInvariantSigma J)
      have e4 : (fun v => W z * f z v) = W z • f z := rfl
      unfold invariantCondExp
      rw [e4]
      filter_upwards [e2] with v h
      simpa [smul_eq_mul, Pi.smul_apply] using h
  filter_upwards [h0, h1, h2, h3, h4] with v a₀ a₁ a₂ a₃ a₄
  refine a₀.trans ?_
  rw [a₂, a₁, Finset.sum_apply]
  have hs : ∑ z ∈ s, invariantCondExp P (fun v => W z * f z v) v ≤ (∑ z ∈ s, W z) * b := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun z hz => ?_
    rw [a₄ z hz]
    exact mul_le_mul_of_nonneg_left (a₃ z hz) (hW z hz)
  nlinarith [mul_le_mul_of_nonneg_left hs he]
end Invariant
section Limit
variable {T : TranslatedLaws} {J : Type} {X : J → T.Family} {P : Measure (TranslateValues J)}
private theorem ae_le_of_eventually_le (hL : IsJointLimitLaw T X P) {I : Type} [Fintype I] (ι : I → J) (φ : (I → ℝ) → ℝ) (hφ : Continuous φ)
    (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), φ (fun c => X (ι c) i ω) ≤ 0) :
    ∀ᵐ v ∂P, φ (fun c => v (ι c, 0)) ≤ 0 := by apply _root_.YangMills.SharedProofs.p13419 <;> assumption
end Limit
section Sites
variable {k : ℕ}
private theorem exists_offset_of_mem_supportSites (hP : supportSitesLocationStatement) {L : ℕ} [NeZero L] (hL : Odd L) (P : LevelData k) {R d : ℝ}
    (hF : P.SupAdmissible L R d) {u : ℕ} (hu : u ≤ P.scaleLevel) (i : Fin k) {y : TorusSite (P.sideAt L u)} (hy : y ∈ P.supportSites L u i) :
    ∃ z ∈ offsetCube (⌈R * (L : ℝ) ^ (P.scaleLevel - u)⌉₊ + 2), ∀ a, y a =
      ((round (P.center a * (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u) : ℤ) : ZMod (P.sideAt L u)) + ((z a : ℤ) : ZMod (P.sideAt L u)) := by
  obtain ⟨ζ, hζ, hζc⟩ := (hP L hL k P u (hu.trans hF.scaleLevel_le) i).1 y hy
  have hzb : ∀ a, |ζ a| ≤ R := hF.isSupTestFamily.abs_coord_le i ζ (subset_tsupport _ hζ)
  have hc : 0 < P.period L := Nat.pos_of_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne L)))
  have key : ∀ a, ∃ w : ℤ, y a = ((round (P.center a * (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u) : ℤ) : ZMod (P.sideAt L u)) +
      ((w : ℤ) : ZMod (P.sideAt L u)) ∧ |(w : ℝ)| ≤ 1 + R * (L : ℝ) ^ (P.scaleLevel - u) := by
    intro a
    obtain ⟨m, w, hv, hw⟩ := exists_offset_of_circleRep_le (L := L) (K := P.windowLevel) (s := P.scaleLevel) (u := u) (N := P.sideAt L u) hu hF.scaleLevel_le hc
      (by unfold LevelData.sideAt; push_cast; ring) (hzb a) (y a).val (hζc a)
    refine ⟨w, ?_, hw⟩
    have h1 := congrArg (Int.cast : ℤ → ZMod (P.sideAt L u)) hv
    have h0 : ((P.sideAt L u : ℕ) : ZMod (P.sideAt L u)) = 0 := ZMod.natCast_self _
    push_cast at h1
    rw [h0, zero_mul, add_zero, ZMod.natCast_zmod_val] at h1
    exact h1
  choose z hz1 hz2 using key
  refine ⟨z, ?_, hz1⟩
  unfold offsetCube
  rw [Fintype.mem_piFinset]
  intro a
  have h3 := hz2 a
  have h4 : R * (L : ℝ) ^ (P.scaleLevel - u) ≤ ((⌈R * (L : ℝ) ^ (P.scaleLevel - u)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h5 := abs_le.1 h3
  rw [Finset.mem_Icc]
  constructor
  · have : ((-(((⌈R * (L : ℝ) ^ (P.scaleLevel - u)⌉₊ + 2 : ℕ) : ℤ)) : ℤ) : ℝ) ≤ ((z a : ℤ) : ℝ) := by
      push_cast
      linarith [h5.1]
    exact_mod_cast this
  · have : ((z a : ℤ) : ℝ) ≤ (((⌈R * (L : ℝ) ^ (P.scaleLevel - u)⌉₊ + 2 : ℕ) : ℤ) : ℝ) := by
      push_cast
      linarith [h5.2]
    exact_mod_cast this
abbrev _root_.YangMills.SharedProofs.p54227 := @exists_offset_of_mem_supportSites
end Sites
section Chain
variable {ℓ : TorusLumps.StepParameters}
private theorem of_eq_nextStageWithResponse {hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup} {lam x'' : ℝ} {c : ChainStage ℓ}
    (A : ResponseSetup c.toStepSetup) {h : CoarseLabelFacts c.toStepSetup} {x₂ : ℝ} {f₂ : LocalDensity}
    {φ₂ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → CoarseLabel c.labels.Ω ℓ.side) → ℝ}
    (A₂ : ResponseSetup (c.next h x₂ f₂ φ₂).toStepSetup)
    (hz : (⟨c.next h x₂ f₂ φ₂, A₂⟩ : StageWithResponse ℓ) = nextStageWithResponse hL lam x'' ⟨c, A⟩) :
    f₂ = c.toStepSetup.renormalizedDensity lam ∧ φ₂ = c.toStepSetup.stateDensity lam ∧
      ∀ ω, A₂.score ω = coarseLabelScore A.responseParams.s₁ A.score ω := by
  obtain ⟨e, he⟩ := Sigma.mk.inj_iff.1 hz
  have h1 : x₂ = x'' := congrArg ChainStage.nextCoupling e
  have h2 : f₂ = c.toStepSetup.renormalizedDensity lam := congrArg ChainStage.density e
  have h3 : φ₂ = c.toStepSetup.stateDensity lam := eq_of_heq (congr_arg_heq ChainStage.siteDensity e)
  subst h1 h2 h3
  have he' := eq_of_heq he
  subst he'
  exact ⟨rfl, rfl, fun _ => rfl⟩
private theorem score_eq_zero_of_eq {z z' : StageWithResponse ℓ} (e : z = z') (h : ∀ w, z'.2.score w = 0) :
    ∀ w, z.2.score w = 0 := by
  subst e
  exact h
private theorem coarseLabelScore_nonneg {Ω : Type} {L : ℕ} {s₁ : ℝ} {s : Ω → ℝ} (h₁ : 0 ≤ s₁) (hs : ∀ w, 0 ≤ s w)
    (ω : CoarseLabel Ω L) : 0 ≤ coarseLabelScore s₁ s ω := by apply _root_.YangMills.Construction.ResponseInTheExpansion.CoarseScore.coarseLabelScore_nonneg <;> assumption
private theorem labelSize_nonneg (T : StageTower ℓ) {s₁ : ℝ} (h₁ : 0 ≤ s₁) :
    ∀ (t : ℕ) (w : (T.stage t).labels.Ω), 0 ≤ HullTrees.labelSize T s₁ t w
  | 0, _ => le_rfl
  | t + 1, w => coarseLabelScore_nonneg h₁ (labelSize_nonneg T h₁ t) w
private theorem siteSize_nonneg (T : StageTower ℓ) {s₁ : ℝ} (h₁ : 0 ≤ s₁) (u n : ℕ) [NeZero n]
    (w : MarkedSample ℓ u n) (y : TorusSite n) : 0 ≤ HullTrees.siteSize T s₁ u n w y := by
  unfold HullTrees.siteSize siteScore
  split_ifs
  · exact labelSize_nonneg T h₁ u _
  · exact le_rfl
abbrev _root_.YangMills.SharedProofs.p9879 := @siteSize_nonneg
private theorem hullDecayRate_nonneg {Tb : ParameterAssignment} (h : Tb.Admissible) : 0 ≤ HullTrees.hullDecayRate Tb := by
  have hL : (0 : ℝ) ≤ Real.log Tb.side := Real.log_natCast_nonneg _
  have hB : 0 < Tb.B := lt_of_lt_of_le one_pos h.B_ge
  have hu : 0 ≤ HullTrees.unitDecayRate Tb := by
    have h1 : 0 ≤ Tb.κ * Tb.threshold ^ 2 := mul_nonneg h.κ_pos.le (sq_nonneg _)
    exact mul_nonneg (by norm_num) (le_min h1 h.cE_pos.le)
  have hp : 0 ≤ HullTrees.separatedUnitRate Tb := div_nonneg hu (by positivity)
  exact le_min (div_nonneg hp (by norm_num)) (div_nonneg hL (by positivity))
abbrev _root_.YangMills.SharedProofs.p10157 := @hullDecayRate_nonneg
private theorem map_sampleBelow_eq (hfit : ℓ.Admissible) (hgt : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (hLaw : sampleBelowLawStatement)
    (T : StageTower ℓ) (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hco : T.MarksMeasurable) (β : ℝ) {K u d : ℕ} (hd : u + d = K)
    (n : ℕ) [NeZero n] :
    Measurable (fun w : MarkedSample ℓ K n => sampleBelow ℓ u d n (hd.symm ▸ w)) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample ℓ K n => sampleBelow ℓ u d n (hd.symm ▸ w)) =
        markedSampleLaw T β u (fineSide ℓ.side d n) := by
  subst hd
  exact (hLaw ℓ hfit hgt T hcut hco β (fun _ => 0)).1 u d n
abbrev _root_.YangMills.SharedProofs.p37385 := @map_sampleBelow_eq
end Chain
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem stageOnFlow_of_le {j : ℕ} (hj : j ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β j ⟨S.tower.stage j, S.resp j⟩ := by apply _root_.YangMills.DeltaSharedProofs.p500519 <;> assumption
abbrev _root_.YangMills.SharedProofs.p6811 := @stageOnFlow_of_le
private theorem stage_next_eq {j : ℕ} (hj : j + 1 ≤ S.data.windowLevel) :
    S.tower.densities j = (S.tower.stage j).toStepSetup.renormalizedDensity Λ.table.lam ∧
      S.tower.siteDensities (S.tower.stage j).toStepSetup = (S.tower.stage j).toStepSetup.stateDensity Λ.table.lam ∧
      ∀ ω, (S.resp (j + 1)).score ω = coarseLabelScore (S.resp j).responseParams.s₁ (S.resp j).score ω := by
  have e1 := S.stage_eq (j + 1) hj
  have e2 := S.stage_eq j (Nat.le_of_succ_le hj)
  refine of_eq_nextStageWithResponse (hL := S.labelFacts) (lam := Λ.table.lam) (x'' := couplingsAlongFlow Λ.stepParams S.β (j + 2)) (c := S.tower.stage j) (S.resp j)
    (h := S.tower.labelFacts _ S.tower.two_le_side) (x₂ := S.tower.couplings j) (f₂ := S.tower.densities j) (φ₂ := S.tower.siteDensities (S.tower.stage j).toStepSetup) (S.resp (j + 1)) ?_
  rw [e2]
  exact e1
abbrev _root_.YangMills.SharedProofs.p36968 := @stage_next_eq
private theorem resp_score_eq_labelSize (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    (S.resp u).score = HullTrees.labelSize S.tower Λ.response.s₁ u := by
  induction u with
  | zero =>
    funext w
    exact score_eq_zero_of_eq (z := ⟨S.tower.stage 0, S.resp 0⟩) (z' := S.initial) (S.stage_eq 0 (Nat.zero_le _)) S.isInitial.score_eq w
  | succ u ih =>
    obtain ⟨-, -, hs⟩ := stage_next_eq S hu
    have ih' := ih (Nat.le_of_succ_le hu)
    have hK : (S.resp u).responseParams = Λ.response := (stageOnFlow_of_le S (Nat.le_of_succ_le hu)).params_eq
    funext ω
    rw [hs ω, hK, ih']
    rfl
abbrev _root_.YangMills.SharedProofs.p9388 := @resp_score_eq_labelSize
private theorem towerFollowsFlow_of_point : TowerFollowsFlow S.tower S.β S.data.windowLevel := by
  intro j hj
  rcases Nat.lt_or_ge j (S.data.windowLevel + 1) with h | h
  · exact (stageOnFlow_of_le S (Nat.lt_succ_iff.1 h)).coupling_eq
  · obtain rfl : j = S.data.windowLevel + 1 := le_antisymm hj h
    exact (stageOnFlow_of_le S le_rfl).nextCoupling_eq
abbrev _root_.YangMills.DeltaSharedProofs.p500739 := @towerFollowsFlow_of_point
abbrev _root_.YangMills.SharedProofs.p11317 := @towerFollowsFlow_of_point
private theorem hullChainAtLevel_of_point (hg : 0 < Λ.g) (hfl : Λ.floor ≤ (Λ.g ^ 2)⁻¹) {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    HullTrees.HullChainAtLevel Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u (S.sideAtLevel u) where
  chain :=
    { g_pos := hg
      le_inv_sq := hfl
      upper_le := S.window_le
      isFirst := S.passage
      volume_le := S.side_le
      follows := towerFollowsFlow_of_point S
      depth_bottom := S.startsAtWilson.depth_eq
      functional_bottom := S.startsAtWilson.functional_eq
      anchor_bottom := (stageOnFlow_of_le S (Nat.zero_le _)).onFamily.onFamily.anchorRadius_eq
      cutoff_bottom := S.isCutoff
      marks := S.marksMeasurable
      expansions := fun j hj => (stageOnFlow_of_le S hj).onFamily.onFamily.isStep.1
      reads_flow :=
        { startsAtWilson := S.startsAtWilson
          coupling_eq := towerFollowsFlow_of_point S
          onFamily := fun j hj => (stageOnFlow_of_le S hj).onFamily.onFamily
          siteDensities_eq := fun j hj => (stage_next_eq S hj).2.1
          densities_eq := fun j hj => (stage_next_eq S hj).1 } }
  le := hu
  side_eq := rfl
private theorem exists_offset_of_mem_supportAt (hP : supportSitesLocationStatement) (hL : Odd Λ.stepParams.side) {u : ℕ} (hu : u ≤ S.data.scaleLevel) (i : Fin Λ.k)
    (n : ℕ) [NeZero n] (hn : n = S.levelSide u) (y : TorusSite n) (hy : y ∈ S.supportAt u n i) :
    ∃ z ∈ offsetCube (S.supportRadius u), y = S.originSite u n + siteOfInt z := by
  subst hn
  obtain ⟨z, hz, hy'⟩ := exists_offset_of_mem_supportSites hP hL S.data S.supAdmissible hu i (y := y) hy
  exact ⟨z, hz, funext hy'⟩
private theorem exists_offsets_of_supportAt (hP : supportSitesLocationStatement) (hL : Odd Λ.stepParams.side) {u : ℕ} (hu : u ≤ S.data.scaleLevel) (i : Fin Λ.k) :
    ∃ A : Finset (Fin 4 → ℤ), A ∈ (offsetCube (S.supportRadius u)).powerset ∧ A.card = (S.supportAt u (S.sideAtLevel u) i).card ∧
      ∀ f : TorusSite (S.sideAtLevel u) → ℝ, ∑ y ∈ S.supportAt u (S.sideAtLevel u) i, f y = ∑ z ∈ A, f (S.siteAt u z) := by
  classical
  have hn : S.sideAtLevel u = S.levelSide u := WeightedResponses.fineSide_eq _ _ _
  have key : ∀ y : {y // y ∈ S.supportAt u (S.sideAtLevel u) i}, ∃ z ∈ offsetCube (S.supportRadius u), y.1 = S.siteAt u z := fun y =>
    exists_offset_of_mem_supportAt S hP hL hu i _ hn y.1 y.2
  choose zf hz1 hz2 using key
  have hinj : Function.Injective zf := fun a b h => Subtype.ext (by rw [hz2 a, hz2 b, h])
  refine ⟨Finset.univ.image zf, ?_, ?_, fun f => ?_⟩
  · rw [Finset.mem_powerset]
    intro z hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact hz1 y
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · rw [Finset.sum_image (fun a _ b _ h => hinj h), ← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl fun y _ => by rw [← hz2 y]
private theorem meanScoreProduct_nonneg_and_le (hs₁ : 0 ≤ Λ.response.s₁) {u : ℕ} (hu : u = S.lastSeparated) (J : List (Fin Λ.k)) (hp : 1 ≤ J.length)
    (A : Fin Λ.k → Finset (Fin 4 → ℤ)) (hc : ∀ i, (A i).card = (S.supportAt u (S.sideAtLevel u) i).card)
    (hA : ∀ i, ∀ f : TorusSite (S.sideAtLevel u) → ℝ, ∑ y ∈ S.supportAt u (S.sideAtLevel u) i, f y = ∑ z ∈ A i, f (S.siteAt u z))
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    0 ≤ meanScoreProduct J S w ∧ meanScoreProduct J S w ≤
      (1 + 2 ^ J.length) + 2 ^ J.length * ∑ e ∈ (Finset.univ : Finset (Fin J.length)).sigma (fun i => A (J.get i)),
        ((J.length : ℝ)⁻¹ * ((A (J.get e.1)).card : ℝ)⁻¹) * hullSizePower u e.2 J.length S w := by
  subst hu
  have hK : S.lastSeparated ≤ S.data.windowLevel := S.lastSeparated_le
  let sz : TorusSite (S.sideAtLevel S.lastSeparated) → ℝ := fun y =>
    siteScore (labelSize S.tower Λ.response.s₁ S.lastSeparated) (S.stateAtLevel S.lastSeparated hK w).2.1 (S.stateAtLevel S.lastSeparated hK w).2.2 y
  have hsz0 : ∀ y, 0 ≤ sz y := fun y => by
    show 0 ≤ siteScore _ _ _ _
    unfold siteScore
    split_ifs
    · exact labelSize_nonneg S.tower hs₁ S.lastSeparated _
    · exact le_rfl
  have hN : ∀ i, S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated S.lastSeparated_le w) =
      1 + ((A i).card : ℝ)⁻¹ * ∑ z ∈ A i, sz (S.siteAt S.lastSeparated z) := fun i => by
    show meanSiteScore (S.resp S.lastSeparated).score _ _ _ = _
    rw [resp_score_eq_labelSize S S.lastSeparated hK]
    show 1 + ((S.supportAt S.lastSeparated (S.sideAtLevel S.lastSeparated) i).card : ℝ)⁻¹ * ∑ y ∈ S.supportAt S.lastSeparated (S.sideAtLevel S.lastSeparated) i, sz y = _
    rw [hA i sz, hc i]
  have hZ : ∀ (z : Fin 4 → ℤ) (p : ℕ), hullSizePower S.lastSeparated z p S w = sz (S.siteAt S.lastSeparated z) ^ p := fun z p => by
    unfold hullSizePower
    rw [dif_pos hK]
    rfl
  have hM : meanScoreProduct J S w = (J.map fun i => 1 + ((A i).card : ℝ)⁻¹ * ∑ z ∈ A i, sz (S.siteAt S.lastSeparated z)).prod := by
    show (J.map fun i => S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)).prod = _
    rw [funext hN]
  refine ⟨?_, ?_⟩
  · rw [hM]
    refine List.prod_nonneg fun a ha => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
    exact add_nonneg zero_le_one (mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => hsz0 _))
  · rw [hM]
    simp only [hZ]
    exact prod_map_le_weighted_sum_pow J hp A (fun z => sz (S.siteAt S.lastSeparated z)) fun z => hsz0 _
private theorem sampleAtLevel_map_eq (hAR : ruleDrawsChainStatement) (hLaw : sampleBelowLawStatement) (hDr : Λ.table.Admissible) (hf : Λ.stepParams.Admissible)
    {rule : NoiseRule Λ.stepParams} (hrule : rule.IsAdmissible S.tower) {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    AEMeasurable (fun ω => S.sampleAtLevel u hu (S.sampleOf rule ω)) S.sampleLaw ∧
      S.sampleLaw.map (fun ω => S.sampleAtLevel u hu (S.sampleOf rule ω)) = markedSampleLaw S.tower S.β u (S.sideAtLevel u) := by
  have hL := hf.L_ge
  have hn : 3 ≤ Λ.stepParams.n₀ := le_trans (by norm_num) hf.n₀_ge
  have hs := S.side_le
  have hm : S.data.sideExponent ≠ 0 := by
    intro h0
    unfold LevelData.period at hs
    rw [h0] at hs
    simp only [pow_zero, mul_one] at hs
    have : 2 ^ 16 * 3 ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.mul_le_mul hL hn
    omega
  have hdiv : Λ.stepParams.side ∣ S.data.period Λ.stepParams.side := by
    obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm
    unfold LevelData.period
    rw [hm', pow_succ]
    exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _
  have h64 : 64 ≤ S.data.period Λ.stepParams.side := by
    have : 2 ^ 16 * 3 ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.mul_le_mul hL hn
    omega
  obtain ⟨hmeas, hmap⟩ := hAR Λ.stepParams hf S.tower rule S.β S.isCutoff S.marksMeasurable hrule S.data.windowLevel (S.data.period Λ.stepParams.side) hdiv h64
  have hc : S.sampleLaw.map (S.sampleOf rule) = markedSampleLaw S.tower S.β S.data.windowLevel (S.data.period Λ.stepParams.side) := hmap
  have hm' : AEMeasurable (S.sampleOf rule) S.sampleLaw := hmeas.aemeasurable
  obtain ⟨h1, h2⟩ := map_sampleBelow_eq hf hDr.L_gt hLaw S.tower S.isCutoff S.marksMeasurable S.β (Nat.add_sub_of_le hu) (S.data.period Λ.stepParams.side)
  refine ⟨h1.comp_aemeasurable hm', ?_⟩
  have h3 := AEMeasurable.map_map_of_aemeasurable (μ := S.sampleLaw) (f := S.sampleOf rule) (by rw [hc]; exact h1.aemeasurable) hm'
  rw [hc, h2] at h3
  exact h3.symm
private theorem hullSizePower_moment_le (hg : 0 < Λ.g) (hfl : Λ.floor ≤ (Λ.g ^ 2)⁻¹) (hy : 0 ≤ Λ.floor) (hDr : Λ.table.Admissible) (hf : Λ.stepParams.Admissible) (hs₁ : 0 ≤ Λ.response.s₁)
    (hAR : ruleDrawsChainStatement) (hLaw : sampleBelowLawStatement) {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (hC : ∀ (β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
      HullTrees.HullChainAtLevel Λ.table Λ.floor Λ.g β K m T u n → ∀ (z : TorusSite n) (k : ℕ), 1 ≤ k →
        Integrable (fun w => HullTrees.siteSize T Λ.response.s₁ u n w z ^ k) (markedSampleLaw T β u n) ∧
        ∫ w, HullTrees.siteSize T Λ.response.s₁ u n w z ^ k ∂(markedSampleLaw T β u n) ≤
          C₀ ^ k * (k.factorial : ℝ) ^ 6 *
            Real.exp (-(HullTrees.hullDecayRate Λ.table * HullTrees.stageCoupling T u / 4)))
    {rule : NoiseRule Λ.stepParams} (hrule : rule.IsAdmissible S.tower) (hprob : IsProbabilityMeasure S.sampleLaw) {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (k q : ℕ) :
    AEMeasurable (fun ω => hullSizePower u z k S (S.sampleOf rule ω)) S.sampleLaw ∧
      ∫⁻ ω, ENNReal.ofReal (|hullSizePower u z k S (S.sampleOf rule ω)| ^ q) ∂S.sampleLaw ≤
        ENNReal.ofReal (1 + C₀ ^ (k * q) * ((k * q).factorial : ℝ) ^ 6) := by
  obtain ⟨hD, hmap⟩ := sampleAtLevel_map_eq S hAR hLaw hDr hf hrule hu
  have hAt := hullChainAtLevel_of_point S hg hfl hu
  haveI hpm : IsProbabilityMeasure (markedSampleLaw S.tower S.β u (S.sideAtLevel u)) := by
    rw [← hmap]
    exact Measure.isProbabilityMeasure_map hD
  obtain ⟨h, hh⟩ : ∃ h : MarkedSample Λ.stepParams u (S.sideAtLevel u) → ℝ,
      h = fun w => HullTrees.siteSize S.tower Λ.response.s₁ u (S.sideAtLevel u) w (S.siteAt u z) := ⟨_, rfl⟩
  have hc : ∀ m : ℕ, 1 ≤ m → Integrable (fun w => h w ^ m) (markedSampleLaw S.tower S.β u (S.sideAtLevel u)) ∧
      ∫ w, h w ^ m ∂(markedSampleLaw S.tower S.β u (S.sideAtLevel u)) ≤ C₀ ^ m * (m.factorial : ℝ) ^ 6 := fun m hm => by
    rw [hh]
    obtain ⟨c1, c2⟩ := hC S.β S.data.windowLevel S.data.sideExponent S.tower u (S.sideAtLevel u) hAt (S.siteAt u z) m hm
    refine ⟨c1, c2.trans ?_⟩
    have hexp : Real.exp (-(HullTrees.hullDecayRate Λ.table * HullTrees.stageCoupling S.tower u / 4)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hx : Λ.floor ≤ HullTrees.stageCoupling S.tower u := (stageOnFlow_of_le S hu).onFamily.onFamily.le_coupling
      have := mul_nonneg (hullDecayRate_nonneg hDr) (hy.trans hx)
      linarith
    exact mul_le_of_le_one_right (by positivity) hexp
  have hh0 : ∀ w, 0 ≤ h w := fun w => by
    rw [hh]
    exact siteSize_nonneg S.tower hs₁ u _ w _
  have hmeas : AEMeasurable h (markedSampleLaw S.tower S.β u (S.sideAtLevel u)) := by
    have := (hc 1 le_rfl).1.aestronglyMeasurable.aemeasurable
    simpa only [pow_one] using this
  have hval : ∀ ω, hullSizePower u z k S (S.sampleOf rule ω) = h (S.sampleAtLevel u hu (S.sampleOf rule ω)) ^ k := fun ω => by
    rw [hh]
    unfold hullSizePower
    rw [dif_pos hu]
  have hmk : AEMeasurable (fun w => h w ^ k) (S.sampleLaw.map fun ω => S.sampleAtLevel u hu (S.sampleOf rule ω)) := by
    rw [hmap]
    exact hmeas.pow_const k
  refine ⟨?_, ?_⟩
  · simp only [hval]
    exact hmk.comp_aemeasurable hD
  · simp only [hval]
    have hG : AEMeasurable (fun w => ENNReal.ofReal (|h w ^ k| ^ q)) (S.sampleLaw.map fun ω => S.sampleAtLevel u hu (S.sampleOf rule ω)) :=
      ((hmk.abs).pow_const q).ennreal_ofReal
    rw [← lintegral_map' hG hD, hmap]
    have hpw : ∀ w, |h w ^ k| ^ q = h w ^ (k * q) := fun w => by
      rw [abs_of_nonneg (pow_nonneg (hh0 w) k), ← pow_mul]
    simp only [hpw]
    rcases Nat.eq_zero_or_pos (k * q) with h0 | h0
    · rw [h0]
      simp only [pow_zero, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]
      simp
    · obtain ⟨c1, c2⟩ := hc (k * q) h0
      rw [← ofReal_integral_eq_lintegral_ofReal c1 (Eventually.of_forall fun w => pow_nonneg (hh0 w) _)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
end Point
section Parameters
private theorem forAllHullParameters_of_eventually {P : ParameterAssignment → ResponseParameters → ℝ → Prop} {Q : MomentParameters → Prop} (h : EventuallyInParameters P)
    (f : ∀ Λ : MomentParameters, P Λ.table Λ.response Λ.floor → Q Λ) : ForAllHullParameters Q := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  obtain ⟨M, G⟩ := H L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  refine ⟨M, ?_⟩
  intro Kr k₁ k₂ k₃ k₄ k₅
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨y₀, ?_⟩
  intro y hy hrow hw g hg hgy k _ hk2 hk8 R d hd
  exact f ⟨Tb, Kr, y, g, k, R, d⟩ (Y y hy hrow hw)
private theorem forAllHullParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁) (h₂ : ForAllHullParameters Q₂) :
    ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem ForAllHullParameters.imp_admissible {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁)
    (f : ∀ Λ : MomentParameters, Odd Λ.stepParams.side → Λ.table.Admissible → Λ.response.Admissible Λ.stepParams → Λ.stepParams.Admissible → 0 ≤ Λ.floor → 0 < Λ.g → Λ.floor ≤ (Λ.g ^ 2)⁻¹ → Q₁ Λ → Q₂ Λ) :
    ForAllHullParameters Q₂ := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  obtain ⟨M, G⟩ := H L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  refine ⟨M, ?_⟩
  intro Kr k₁ k₂ k₃ k₄ k₅
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨max y₀ (max Tb.floorMin 0), ?_⟩
  intro y hy hrow hw g hg hgy k _ hk2 hk8 R d hd
  have hy1 : Tb.floorMin ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hy
  have hy2 : (0 : ℝ) ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hy
  have hfit : (Tb.stepParameters y).Admissible := d₁.fits y hy1
  have hodd : Odd (MomentParameters.stepParams ⟨Tb, Kr, y, g, k, R, d⟩).side := by
    show Odd Tb.side
    rw [e₂]
    exact hL
  exact f ⟨Tb, Kr, y, g, k, R, d⟩ hodd d₁ (k₄ y) hfit hy2 hg hgy (Y y ((le_max_left _ _).trans hy) hrow hw g hg hgy k hk2 hk8 R d hd)
end Parameters
section Main
variable {Λ : MomentParameters}
private theorem exists_subseq_lastSeparated_const (S : MomentPoint Λ) (F : LimitLawAtPoint S) :
    ∃ (t : ℕ) (φ : ℕ → ℕ), t ≤ S.data.scaleLevel ∧ StrictMono φ ∧ ∀ i, (F.points (φ i)).lastSeparated = t := by
  classical
  have hle : ∀ i, (F.points i).lastSeparated ∈ Finset.range (S.data.scaleLevel + 1) := fun i => by
    obtain ⟨a, b, e⟩ := F.points_eq i
    rw [e, Finset.mem_range, Nat.lt_succ_iff]
    unfold MomentPoint.lastSeparated
    exact Nat.findGreatest_le _
  obtain ⟨t, φ, hφ, ht⟩ := exists_strictMono_const_of_mem_finset _ (fun i => (F.points i).lastSeparated) hle
  refine ⟨t, φ, ?_, hφ, ht⟩
  have := hle (φ 0)
  rw [Finset.mem_range, Nat.lt_succ_iff] at this
  rw [← ht 0]
  exact this
private theorem points_fields_eq {S : MomentPoint Λ} (F : LimitLawAtPoint S) (n : ℕ) :
    (F.points n).data.scaleLevel = S.data.scaleLevel ∧ (F.points n).data.windowLevel = S.data.windowLevel ∧ (F.points n).β = S.β ∧ (F.points n).tower = S.tower := by
  obtain ⟨hp, hs, h⟩ := F.points_eq n
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl⟩
private theorem supportRadius_points {S : MomentPoint Λ} (F : LimitLawAtPoint S) (n u : ℕ) : (F.points n).supportRadius u = S.supportRadius u := by
  unfold MomentPoint.supportRadius
  rw [(points_fields_eq F n).1]
private theorem condMeanAt_meanScoreProduct_le (hg : 0 < Λ.g) (hfl : Λ.floor ≤ (Λ.g ^ 2)⁻¹) (hy : 0 ≤ Λ.floor) (hDr : Λ.table.Admissible) (hf : Λ.stepParams.Admissible) (hs₁ : 0 ≤ Λ.response.s₁)
    (hOdd : Odd Λ.stepParams.side) (hP : supportSitesLocationStatement) (hAR : ruleDrawsChainStatement) (hLaw : sampleBelowLawStatement)
    (hMn : jointLimitPropertiesStatement) (hExt : jointLimitExtendStatement) {C₀ C : ℝ} (hC₀ : 1 ≤ C₀) (hC1 : 1 ≤ C)
    (hC : ∀ (β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
      HullTrees.HullChainAtLevel Λ.table Λ.floor Λ.g β K m T u n → ∀ (z : TorusSite n) (k : ℕ), 1 ≤ k →
        Integrable (fun w => HullTrees.siteSize T Λ.response.s₁ u n w z ^ k) (markedSampleLaw T β u n) ∧
        ∫ w, HullTrees.siteSize T Λ.response.s₁ u n w z ^ k ∂(markedSampleLaw T β u n) ≤
          C₀ ^ k * (k.factorial : ℝ) ^ 6 *
            Real.exp (-(HullTrees.hullDecayRate Λ.table * HullTrees.stageCoupling T u / 4)))
    (hHull : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (u : ℕ) (z : Fin 4 → ℤ), u ≤ S.data.windowLevel → ∀ (k : ℕ) (j : F.Index), 1 ≤ k →
      F.observables j = hullSizePower u z k → ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ C ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(hullDecayRate Λ.table * S.coupling u / 4)))
    (hKeep : ∀ (S : MomentPoint Λ) (rule : NoiseRule Λ.stepParams) (ms : ℕ → ℕ) (Sq : ℕ → MomentPoint Λ) (p : ℕ), rule.IsAdmissible S.tower → 1 ≤ p → StrictMono ms →
      (∀ i, ∃ hp hs, Sq i = S.withSideExponent (ms i) hp hs) → (translatedTori Sq p).IsPreserving)
    (S : MomentPoint Λ) (F : LimitLawAtPoint S) (J : List (Fin Λ.k)) (hp : 1 ≤ J.length) (j : F.Index) (hj : F.observables j = meanScoreProduct J) :
    ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ (8 * C) ^ J.length * (J.length.factorial : ℝ) ^ 6 := by
  classical
  haveI hcount := F.countable_index
  obtain ⟨t, φ₁, htS, hφ₁, ht⟩ := exists_subseq_lastSeparated_const S F
  have htK : t ≤ S.data.windowLevel := htS.trans S.supAdmissible.scaleLevel_le
  have hoff : ∀ (n : ℕ) (i : Fin Λ.k), ∃ A : Finset (Fin 4 → ℤ), A ∈ (offsetCube (S.supportRadius t)).powerset ∧
      A.card = ((F.points (φ₁ n)).supportAt t ((F.points (φ₁ n)).sideAtLevel t) i).card ∧
      ∀ f : TorusSite ((F.points (φ₁ n)).sideAtLevel t) → ℝ, ∑ y ∈ (F.points (φ₁ n)).supportAt t ((F.points (φ₁ n)).sideAtLevel t) i, f y = ∑ z ∈ A, f ((F.points (φ₁ n)).siteAt t z) := fun n i => by
    have := exists_offsets_of_supportAt (F.points (φ₁ n)) hP hOdd (u := t) (by rw [(points_fields_eq F _).1]; exact htS) i
    rwa [supportRadius_points] at this
  choose A hA₁ hA₂ hA₃ using hoff
  obtain ⟨B, φ₂, hφ₂, hB⟩ := exists_strictMono_const_of_mem_finset (Fintype.piFinset fun _ : Fin Λ.k => (offsetCube (S.supportRadius t)).powerset) A
    fun n => Fintype.mem_piFinset.2 fun i => hA₁ n i
  obtain ⟨φ, hφd⟩ : ∃ φ : ℕ → ℕ, φ = fun n => φ₁ (φ₂ n) := ⟨_, rfl⟩
  have hφ : StrictMono φ := by
    rw [hφd]
    exact hφ₁.comp hφ₂
  have hrule : ∀ n, F.rule.IsAdmissible (F.points n).tower := fun n => by
    rw [(points_fields_eq F n).2.2.2]
    exact F.rule_admissible
  have hK₁ : (translatedTori (fun i => F.points (φ i)) F.period).IsPreserving :=
    hKeep S F.rule (fun i => F.exponents (φ i)) (fun i => F.points (φ i)) F.period F.rule_admissible F.one_le_period (F.strictMono_exponents.comp hφ) fun i => F.points_eq _
  have hXf : ∀ j, TranslatedLaws.HasBoundedMoments (sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j)) := fun j =>
    ⟨fun i => (F.hasBoundedMoments j).aemeasurable (φ i), fun q => by
      obtain ⟨C, hC⟩ := (F.hasBoundedMoments j).moment_bound q
      exact ⟨C, fun i => hC (φ i)⟩⟩
  have hZ : ∀ z : Fin 4 → ℤ, TranslatedLaws.HasBoundedMoments (sampleFamily F.rule (fun i => F.points (φ i)) F.period (hullSizePower t z J.length)) := fun z =>
    ⟨fun i => (hullSizePower_moment_le (F.points (φ i)) hg hfl hy hDr hf hs₁ hAR hLaw hC₀ hC (hrule _) (hK₁.isProbability i) (by rw [(points_fields_eq F _).2.1]; exact htK) z J.length 0).1,
      fun q => ⟨1 + C₀ ^ (J.length * q) * ((J.length * q).factorial : ℝ) ^ 6, fun i =>
        (hullSizePower_moment_le (F.points (φ i)) hg hfl hy hDr hf hs₁ hAR hLaw hC₀ hC (hrule _) (hK₁.isProbability i) (by rw [(points_fields_eq F _).2.1]; exact htK) z J.length q).2⟩⟩
  have hlim₀ : IsJointLimitLaw (translatedTori (fun i => F.points (φ i)) F.period) (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j)) F.law :=
    ⟨F.isJointLimitLaw.isProbability, fun l a G hG hb => (F.isJointLimitLaw.tendsto l a G hG hb).comp hφ.tendsto_atTop⟩
  obtain ⟨sub, P', hsub, hlim, -, htr⟩ := hExt (translatedTori (fun i => F.points (φ i)) F.period) F.Index (Fin 4 → ℤ)
    (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j))
    (fun z => sampleFamily F.rule (fun i => F.points (φ i)) F.period (hullSizePower t z J.length)) F.law hK₁ hXf hZ hlim₀
  have hφs : StrictMono fun i => φ (sub i) := hφ.comp hsub
  have hlim' : IsJointLimitLaw (translatedTori (fun i => F.points (φ (sub i))) F.period)
      (fun c => sampleFamily F.rule (fun i => F.points (φ (sub i))) F.period (Sum.elim F.observables (fun z => hullSizePower t z J.length) c)) P' := by
    have e1 : (fun c => sampleFamily F.rule (fun i => F.points (φ (sub i))) F.period (Sum.elim F.observables (fun z => hullSizePower t z J.length) c)) =
        fun c i => Sum.elim (fun j => sampleFamily F.rule (fun i => F.points (φ i)) F.period (F.observables j))
          (fun z => sampleFamily F.rule (fun i => F.points (φ i)) F.period (hullSizePower t z J.length)) c (sub i) := by
      funext c
      rcases c with c | c <;> rfl
    rw [e1]
    exact hlim
  let F' : LimitLawAtPoint S :=
    { rule := F.rule, rule_admissible := F.rule_admissible, period := F.period, one_le_period := F.one_le_period, exponents := fun i => F.exponents (φ (sub i)),
      strictMono_exponents := fun _ _ h => F.strictMono_exponents (hφs h),
      points := fun i => F.points (φ (sub i)), points_eq := fun i => F.points_eq _, Index := F.Index ⊕ (Fin 4 → ℤ), countable_index := inferInstance,
      observables := Sum.elim F.observables (fun z => hullSizePower t z J.length),
      hasBoundedMoments := by
        rintro (j | z)
        · exact ⟨fun i => (hXf j).aemeasurable (sub i), fun q => by
            obtain ⟨C, hC⟩ := (hXf j).moment_bound q
            exact ⟨C, fun i => hC (sub i)⟩⟩
        · exact ⟨fun i => (hZ z).aemeasurable (sub i), fun q => by
            obtain ⟨C, hC⟩ := (hZ z).moment_bound q
            exact ⟨C, fun i => hC (sub i)⟩⟩
      law := P', isJointLimitLaw := hlim' }
  haveI hprob : IsProbabilityMeasure P' := hlim'.isProbability
  have hKeep' : (translatedTori F'.points F'.period).IsPreserving :=
    hKeep S F'.rule F'.exponents F'.points F'.period F'.rule_admissible F'.one_le_period F'.strictMono_exponents F'.points_eq
  haveI : Countable F'.Index := F'.countable_index
  have hM' := hMn _ _ _ _ hKeep' F'.hasBoundedMoments F'.isJointLimitLaw
  have hint : ∀ c : F.Index ⊕ (Fin 4 → ℤ), Integrable (fun v : TranslateValues (F.Index ⊕ (Fin 4 → ℤ)) => v (c, 0)) P' := fun c => by
    have h := (hM'.2.1 1 fun _ => (c, 0)).1
    simpa using h
  obtain ⟨E, hE⟩ : ∃ E : Finset (Σ _ : Fin J.length, Fin 4 → ℤ), E = (Finset.univ : Finset (Fin J.length)).sigma (fun i => B (J.get i)) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : (Σ _ : Fin J.length, Fin 4 → ℤ) → ℝ, W = fun e => (J.length : ℝ)⁻¹ * ((B (J.get e.1)).card : ℝ)⁻¹ := ⟨_, rfl⟩
  have hrel : ∀ (n : ℕ) (w : MarkedSample Λ.stepParams (F.points (φ (sub n))).data.windowLevel ((F.points (φ (sub n))).data.period Λ.stepParams.side)),
      0 ≤ meanScoreProduct J (F.points (φ (sub n))) w ∧ meanScoreProduct J (F.points (φ (sub n))) w ≤
        (1 + 2 ^ J.length) + 2 ^ J.length * ∑ e ∈ E, W e * hullSizePower t e.2 J.length (F.points (φ (sub n))) w := fun n w => by
    subst hφd
    rw [hE, hW]
    exact meanScoreProduct_nonneg_and_le (F.points (φ₁ (φ₂ (sub n)))) hs₁ (ht _).symm J hp B
      (fun i => by rw [← hB (sub n)]; exact hA₂ _ i) (fun i f => by rw [← hB (sub n)]; exact hA₃ _ i f) w
  have hval : ∀ (n : ℕ) (ω : (F.points (φ (sub n))).SampleSpace), sampleFamily F.rule (fun i => F.points (φ (sub i))) F.period (Sum.elim F.observables (fun z => hullSizePower t z J.length) (Sum.inl j)) n ω =
      meanScoreProduct J (F.points (φ (sub n))) ((F.points (φ (sub n))).sampleOf F.rule ω) := fun n ω => by
    show F.observables j _ _ = _
    rw [hj]
  have hX0 : ∀ᵐ v ∂P', 0 ≤ v (Sum.inl j, 0) := by
    have h := ae_le_of_eventually_le hlim' (I := Unit) (fun _ => Sum.inl j) (fun y => -y ()) (continuous_apply _).neg
      (Eventually.of_forall fun n => ae_of_all _ fun ω => by
        have h1 := (hrel n ((F.points (φ (sub n))).sampleOf F.rule ω)).1
        rw [← hval n ω] at h1
        exact neg_nonpos.2 h1)
    filter_upwards [h] with v hv
    exact neg_nonpos.1 hv
  obtain ⟨ιf, hιf⟩ : ∃ ιf : Option {e // e ∈ E} → F.Index ⊕ (Fin 4 → ℤ), ιf = fun c => c.elim (Sum.inl j) (fun e => Sum.inr e.1.2) := ⟨_, rfl⟩
  have hle₀ := ae_le_of_eventually_le hlim' ιf
    (fun y => y none - ((1 + 2 ^ J.length) + 2 ^ J.length * ∑ e : {e // e ∈ E}, W e.1 * y (some e)))
    ((continuous_apply _).sub (continuous_const.add (continuous_const.mul
      (continuous_finsetSum _ fun e _ => continuous_const.mul (continuous_apply _)))))
    (Eventually.of_forall fun n => ae_of_all _ fun ω => by
      have h2 := (hrel n ((F.points (φ (sub n))).sampleOf F.rule ω)).2
      rw [← Finset.sum_coe_sort E, ← hval n ω] at h2
      subst hιf
      exact sub_nonpos.2 h2)
  have hle : ∀ᵐ v ∂P', v (Sum.inl j, 0) ≤ (1 + 2 ^ J.length) + 2 ^ J.length * ∑ e ∈ E, W e * v (Sum.inr e.2, 0) := by
    filter_upwards [hle₀] with v hv
    subst hιf
    have e := Finset.sum_coe_sort E (fun e => W e * v (Sum.inr e.2, 0))
    have h : v (Sum.inl j, 0) - ((1 + 2 ^ J.length) + 2 ^ J.length * ∑ e : {e // e ∈ E}, W e.1 * v (Sum.inr e.1.2, 0)) ≤ 0 := hv
    rw [e] at h
    linarith
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = C ^ J.length * (J.length.factorial : ℝ) ^ 6 := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by
    rw [hbd]
    positivity
  have hexp : Real.exp (-(hullDecayRate Λ.table * S.coupling t / 4)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hx : Λ.floor ≤ stageCoupling S.tower t := (stageOnFlow_of_le S htK).onFamily.onFamily.le_coupling
    have hc : stageCoupling S.tower t = S.coupling t := (stageOnFlow_of_le S htK).coupling_eq
    rw [hc] at hx
    have := mul_nonneg (hullDecayRate_nonneg hDr) (hy.trans hx)
    linarith
  have hb : ∀ e ∈ E, ∀ᵐ v ∂P', invariantCondExp P' (fun v => v (Sum.inr e.2, 0)) v ≤ b := fun e _ => by
    filter_upwards [hHull S F' t e.2 htK J.length (Sum.inr e.2) hp rfl] with v hv
    have hv' : invariantCondExp P' (fun v => v (Sum.inr e.2, 0)) v ≤ C ^ J.length * (J.length.factorial : ℝ) ^ 6 * Real.exp (-(hullDecayRate Λ.table * S.coupling t / 4)) := hv
    rw [hbd]
    exact hv'.trans (mul_le_of_le_one_right (by positivity) hexp)
  have hs := invariantCondExp_le_weighted E (fun e v => v (Sum.inr e.2, 0)) W (fun e _ => hint _)
    (fun e _ => by rw [hW]; positivity) b (1 + 2 ^ J.length) (2 ^ J.length) (by positivity) hb (hint (Sum.inl j)) hle
  have hw : ∑ e ∈ E, W e ≤ 1 := by
    rw [hE, hW]
    exact sum_sigma_weights_le_one J B
  have hF1 : (1 : ℝ) ≤ (J.length.factorial : ℝ) ^ 6 :=
    one_le_pow₀ (by exact_mod_cast Nat.succ_le_of_lt J.length.factorial_pos)
  have hBd : (1 + 2 ^ J.length) + 2 ^ J.length * ((∑ e ∈ E, W e) * b) ≤ (8 * C) ^ J.length * (J.length.factorial : ℝ) ^ 6 := by
    have h1 : (∑ e ∈ E, W e) * b ≤ b := mul_le_of_le_one_left hb0 hw
    have h2 : (2 : ℝ) ^ J.length * ((∑ e ∈ E, W e) * b) ≤ 2 ^ J.length * b := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 := one_add_two_pow_le_eight_mul_pow hC1 hF1 hp
    rw [← hbd] at h3
    nlinarith
  have hlow : ∀ᵐ v ∂P', 0 ≤ invariantCondExp P' (fun v => v (Sum.inl j, 0)) v := condExp_nonneg hX0
  have hY : Integrable (evalAtZero j) F.law := by
    have h := ((hMn _ _ _ _ hK₁ hXf hlim₀).2.1 1 fun _ => (j, 0)).1
    have e1 : (fun v : TranslateValues F.Index => ∏ _c : Fin 1, v (j, 0)) = evalAtZero j := by
      funext v
      simp [evalAtZero]
    rwa [e1] at h
  have h2 := htr (evalAtZero j) 0 ((8 * C) ^ J.length * (J.length.factorial : ℝ) ^ 6) hY (by
    filter_upwards [hlow, hs] with v a₁ a₂
    exact ⟨a₁, a₂.trans hBd⟩)
  filter_upwards [h2] with v hv
  exact hv.2
end Main
theorem meanScoreLimitMomentStatement_holds (hH : limitHullBoundsStatement) (hMo : HullTrees.siteSizeMomentStatement)
    (hPL : largerToriStatement) (hMn : jointLimitPropertiesStatement) (hExt : jointLimitExtendStatement)
    (hP : supportSitesLocationStatement) (hAR : ruleDrawsChainStatement) (hLaw : sampleBelowLawStatement) :
    meanScoreLimitMomentStatement := by
  unfold limitHullBoundsStatement at hH
  unfold largerToriStatement at hPL
  unfold HullTrees.siteSizeMomentStatement at hMo
  unfold meanScoreLimitMomentStatement
  have hM' : ForAllHullParameters fun Λ => ∃ C : ℝ, 1 ≤ C ∧ ∀ (β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
      HullTrees.HullChainAtLevel Λ.table Λ.floor Λ.g β K m T u n → ∀ (z : TorusSite n) (k : ℕ), 1 ≤ k →
        Integrable (fun w => HullTrees.siteSize T Λ.response.s₁ u n w z ^ k) (markedSampleLaw T β u n) ∧
        ∫ w, HullTrees.siteSize T Λ.response.s₁ u n w z ^ k ∂(markedSampleLaw T β u n) ≤
          C ^ k * (k.factorial : ℝ) ^ 6 *
            Real.exp (-(HullTrees.hullDecayRate Λ.table * HullTrees.stageCoupling T u / 4)) :=
    forAllHullParameters_of_eventually hMo fun Λ h => h Λ.g
  refine ForAllHullParameters.imp_admissible (forAllHullParameters_and hH (forAllHullParameters_and hPL hM')) fun Λ hOdd hDr hKf hf hy hg hfl h => ?_
  obtain ⟨⟨C, hC1, Q₁⟩, Q₂, C₀, hC₀, Q₃⟩ := h
  have hs₁ : 0 ≤ Λ.response.s₁ := by
    have ha1 : 1 ≤ Λ.stepParams.coupling := hf.a_ge
    have hC0 : 0 ≤ Λ.response.C₀ + 2 := by
      have := hKf.Kc_ge
      have := hKf.N₀_nonneg
      rw [hKf.C₀_eq]
      linarith
    rw [hKf.s₁_eq]
    exact add_nonneg (mul_nonneg (by positivity) hC0) (by linarith)
  refine ⟨8 * C, fun S F p hp J j hJ hj => ?_⟩
  subst hJ
  exact condMeanAt_meanScoreProduct_le hg hfl hy hDr hf hs₁ hOdd hP hAR hLaw hMn hExt hC₀ hC1 Q₃ (fun S F u z hu => (Q₁ S F u z hu).2)
    (fun S rule ms Sq p a b c d => ((Q₂ S).2.2.2 rule ms Sq p a b c d).1) S F J hp j hj
end YangMills.Construction.MomentLaw
end
