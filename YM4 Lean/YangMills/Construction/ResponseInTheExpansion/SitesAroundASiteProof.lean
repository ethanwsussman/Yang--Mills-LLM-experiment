import YangMills.Construction.ResponseInTheExpansion.SitesAroundASite
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFields
private def decayWeight (c : ℝ) (t : ℕ) : ℝ := Real.exp (-(c / 4 * (t : ℝ))) * (1 + (t : ℝ))
private theorem decayWeight_nonneg (c : ℝ) (t : ℕ) : 0 ≤ decayWeight c t := by
  unfold decayWeight
  positivity
private theorem summable_decayWeight (c : ℝ) (hc : 0 < c) : Summable (decayWeight c) := by
  set r := Real.exp (-(c / 4)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0.le]
  have h0 : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0.le hr1
  have h1 : Summable fun n : ℕ => ((n : ℝ)) ^ 1 * r ^ n := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  refine (h0.add h1).congr fun n => ?_
  have : Real.exp (-(c / 4 * (n : ℝ))) = r ^ n := by
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    ring
  simp only [decayWeight, this]
  ring
private theorem summable_decayWeight_natAbs (c : ℝ) (hc : 0 < c) :
    Summable fun t : ℤ => decayWeight c t.natAbs := by
  refine Summable.of_nat_of_neg (f := fun t : ℤ => decayWeight c t.natAbs) ?_ ?_
  · simpa using summable_decayWeight c hc
  · simpa using summable_decayWeight c hc
private theorem sum_decayWeight_zmod_le (c : ℝ) (hc : 0 < c) (N : ℕ) [NeZero N] (w : ZMod N) :
    ∑ b : ZMod N, decayWeight c (b - w).valMinAbs.natAbs ≤ ∑' t : ℤ, decayWeight c t.natAbs := by
  have h1 : ∑ b : ZMod N, decayWeight c (b - w).valMinAbs.natAbs =
      ∑ b : ZMod N, decayWeight c b.valMinAbs.natAbs :=
    (Equiv.subRight w).sum_comp fun b => decayWeight c b.valMinAbs.natAbs
  rw [h1]
  have hinj : Function.Injective fun b : ZMod N => b.valMinAbs := by
    intro b b' h
    have := congrArg (fun t : ℤ => (t : ZMod N)) h
    simpa [ZMod.coe_valMinAbs] using this
  have h2 : ∑ b : ZMod N, decayWeight c b.valMinAbs.natAbs =
      ∑ t ∈ Finset.univ.image (fun b : ZMod N => b.valMinAbs), decayWeight c t.natAbs := by
    rw [Finset.sum_image fun b _ b' _ h => hinj h]
  rw [h2]
  exact (summable_decayWeight_natAbs c hc).sum_le_tsum _ fun t _ => decayWeight_nonneg c _
private theorem expDecay_le_prod_decayWeight (c : ℝ) (hc : 0 < c) (N : ℕ) [NeZero N] (a z : TorusSite N) :
    Real.exp (-(c * (supDist a z : ℝ))) * (1 + (supDist a z : ℝ)) ≤
      ∏ i, decayWeight c (a i - z i).valMinAbs.natAbs := by
  set t : Fin 4 → ℕ := fun i => (a i - z i).valMinAbs.natAbs with ht
  have hle : ∀ i, t i ≤ supDist a z := fun i => Finset.le_sup (f := t) (Finset.mem_univ i)
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty t
  have hd : supDist a z = t j := hj
  simp only [decayWeight, Finset.prod_mul_distrib]
  have h1 : Real.exp (-(c * (supDist a z : ℝ))) ≤ ∏ i, Real.exp (-(c / 4 * (t i : ℝ))) := by
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.mpr ?_
    have hs : ∑ i, (t i : ℝ) ≤ 4 * (supDist a z : ℝ) := by
      calc _ ≤ ∑ _i : Fin 4, (supDist a z : ℝ) :=
            Finset.sum_le_sum fun i _ => by exact_mod_cast hle i
        _ = _ := by simp
    have : ∑ i, -(c / 4 * (t i : ℝ)) = -(c / 4 * ∑ i, (t i : ℝ)) := by
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    rw [this]
    nlinarith
  have h2 : 1 + (supDist a z : ℝ) ≤ ∏ i, (1 + (t i : ℝ)) := by
    rw [hd]
    have hone : ∀ i ∈ Finset.univ, i ≠ j → (1 : ℝ) ≤ 1 + (t i : ℝ) := fun i _ _ => by
      have : (0 : ℝ) ≤ (t i : ℝ) := Nat.cast_nonneg _
      linarith
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    have h3 : (1 : ℝ) ≤ ∏ i ∈ Finset.univ.erase j, (1 + (t i : ℝ)) := by
      calc (1 : ℝ) = ∏ _i ∈ Finset.univ.erase j, (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun i hi =>
          hone i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
    nlinarith
  exact mul_le_mul h1 h2 (by positivity) (by positivity)
theorem expDecaySumAndBallCard_holds : ExpDecaySumAndBallCard := by
  refine ⟨fun c hc => ?_, fun N _ z R => ?_⟩
  · refine ⟨(∑' t : ℤ, decayWeight c t.natAbs) ^ 4, fun N _ z => ?_⟩
    calc _ ≤ ∑ a : TorusSite N, ∏ i, decayWeight c (a i - z i).valMinAbs.natAbs :=
          Finset.sum_le_sum fun a _ => expDecay_le_prod_decayWeight c hc N a z
      _ = ∏ i, ∑ b : ZMod N, decayWeight c (b - z i).valMinAbs.natAbs := by
          rw [Finset.prod_univ_sum]
          simp
      _ ≤ ∏ _i : Fin 4, ∑' t : ℤ, decayWeight c t.natAbs := by
          refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun b _ => decayWeight_nonneg c _) fun i _ => ?_
          exact sum_decayWeight_zmod_le c hc N (z i)
      _ = _ := by simp
  · have hinj : Set.InjOn (fun a : TorusSite N => fun i => (a i - z i).valMinAbs)
        (Finset.univ.filter fun a : TorusSite N => supDist a z ≤ R : Finset (TorusSite N)) := by
      intro a _ a' _ h
      funext i
      have h1 := congrFun h i
      have h2 := congrArg (fun t : ℤ => (t : ZMod N)) h1
      simp only [ZMod.coe_valMinAbs] at h2
      exact sub_left_injective h2
    have hmap : ∀ a ∈ (Finset.univ.filter fun a : TorusSite N => supDist a z ≤ R),
        (fun i => (a i - z i).valMinAbs) ∈ Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) (R : ℤ) := by
      intro a ha
      have hd : supDist a z ≤ R := (Finset.mem_filter.mp ha).2
      refine Fintype.mem_piFinset.mpr fun i => ?_
      have h1 : (a i - z i).valMinAbs.natAbs ≤ supDist a z :=
        Finset.le_sup (f := fun i => (a i - z i).valMinAbs.natAbs) (Finset.mem_univ i)
      have h2 : (a i - z i).valMinAbs.natAbs ≤ R := h1.trans hd
      rw [Finset.mem_Icc]
      omega
    calc _ ≤ (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) (R : ℤ)).card :=
          Finset.card_le_card_of_injOn _ hmap hinj
      _ = (2 * R + 1) ^ 4 := by
          rw [Fintype.card_piFinset]
          simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          congr 1
          omega
end YangMills.Construction.TorusFields
end
