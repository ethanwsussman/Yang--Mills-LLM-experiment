import YangMills.Construction.LawInAState.DecayOverATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusSums
open TorusFields
private theorem one_add_pow_five_le_exp {c : ℝ} (hc : 0 < c) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ 5 ≤ (max 1 (10 / c)) ^ 5 * Real.exp (c * t / 2) := by
  set A := max 1 (10 / c) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA2 : 10 / c ≤ A := le_max_right _ _
  have h1 : 1 + c * t / 10 ≤ Real.exp (c * t / 10) := by
    have := Real.add_one_le_exp (c * t / 10)
    linarith
  have h2 : 1 + t ≤ A * (1 + c * t / 10) := by
    have e1 : t ≤ A * (c * t / 10) := by
      have : 10 ≤ A * c := by
        rw [div_le_iff₀ hc] at hA2
        exact hA2
      nlinarith
    nlinarith
  have h3 : Real.exp (c * t / 2) = Real.exp (c * t / 10) ^ 5 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h3, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ 5
  refine h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
private theorem summable_exp_neg_abs_int {c : ℝ} (hc : 0 < c) :
    Summable fun u : ℤ => Real.exp (-(c * |(u : ℝ)|)) := by
  have h : Summable fun k : ℕ => Real.exp (-(c * (k : ℝ))) := by
    have e : (fun k : ℕ => Real.exp (-(c * (k : ℝ)))) = fun k : ℕ => Real.exp (-c) ^ k := by
      funext k
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [e]
    exact summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using hc)
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h
abbrev _root_.YangMills.DeltaSharedProofs.p3646 := @summable_exp_neg_abs_int
abbrev _root_.YangMills.SharedProofs.p3695 := @summable_exp_neg_abs_int
private theorem sum_zmod_exp_le_tsum {c : ℝ} (hc : 0 < c) (n : ℕ) [NeZero n] :
    ∑ t : ZMod n, Real.exp (-(c * |((t.valMinAbs : ℤ) : ℝ)|)) ≤
      ∑' u : ℤ, Real.exp (-(c * |(u : ℝ)|)) := by
  have hinj : Function.Injective (fun t : ZMod n => t.valMinAbs) := fun a b h => by
    have := congrArg (fun u : ℤ => (u : ZMod n)) h
    simpa [ZMod.coe_valMinAbs] using this
  have : ∑ t : ZMod n, Real.exp (-(c * |((t.valMinAbs : ℤ) : ℝ)|)) =
      ∑ u ∈ Finset.univ.image (fun t : ZMod n => t.valMinAbs), Real.exp (-(c * |(u : ℝ)|)) := by
    rw [Finset.sum_image fun a _ b _ h => hinj h]
  rw [this]
  exact (summable_exp_neg_abs_int hc).sum_le_tsum _ fun _ _ => (Real.exp_pos _).le
private theorem exp_supDist_le_prod {c : ℝ} (hc : 0 < c) {n : ℕ} [NeZero n] (x z : TorusSite n) :
    Real.exp (-(c / 2 * (supDist x z : ℝ))) ≤
      ∏ i, Real.exp (-(c / 8 * |(((x i - z i).valMinAbs : ℤ) : ℝ)|)) := by
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  have hle : ∀ i, |(((x i - z i).valMinAbs : ℤ) : ℝ)| ≤ (supDist x z : ℝ) := by
    intro i
    have h : ((x i - z i).valMinAbs).natAbs ≤ supDist x z :=
      Finset.le_sup (f := fun i => ((x i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 : (((x i - z i).valMinAbs).natAbs : ℝ) ≤ (supDist x z : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_natAbs, Int.cast_abs] at h2
  have hs : ∑ i, |(((x i - z i).valMinAbs : ℤ) : ℝ)| ≤ 4 * (supDist x z : ℝ) := by
    calc _ ≤ ∑ _i : Fin 4, (supDist x z : ℝ) := Finset.sum_le_sum fun i _ => hle i
      _ = _ := by simp
  have e : ∑ i, -(c / 8 * |(((x i - z i).valMinAbs : ℤ) : ℝ)|) =
      -(c / 8 * ∑ i, |(((x i - z i).valMinAbs : ℤ) : ℝ)|) := by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [e]
  nlinarith
theorem expDecaySumBounded : ExpDecaySumBounded := by
  intro c hc
  set B := ∑' u : ℤ, Real.exp (-(c / 8 * |(u : ℝ)|)) with hB
  refine ⟨(max 1 (10 / c)) ^ 5 * B ^ 4, by positivity, ?_⟩
  intro n _ z
  have hc8 : 0 < c / 8 := by positivity
  have hA : 0 ≤ (max 1 (10 / c)) ^ 5 := by positivity
  have h1 : ∀ x : TorusSite n, Real.exp (-(c * (supDist x z : ℝ))) * (1 + (supDist x z : ℝ)) ^ 5 ≤
      (max 1 (10 / c)) ^ 5 * ∏ i, Real.exp (-(c / 8 * |(((x i - z i).valMinAbs : ℤ) : ℝ)|)) := by
    intro x
    have k1 := one_add_pow_five_le_exp hc (supDist x z : ℝ) (Nat.cast_nonneg _)
    have k2 := exp_supDist_le_prod hc x z
    calc _ ≤ Real.exp (-(c * (supDist x z : ℝ))) *
            ((max 1 (10 / c)) ^ 5 * Real.exp (c * (supDist x z : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left k1 (Real.exp_pos _).le
      _ = (max 1 (10 / c)) ^ 5 * Real.exp (-(c / 2 * (supDist x z : ℝ))) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left k2 hA
  refine (Finset.sum_le_sum fun x _ => h1 x).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have e1 : ∑ x : TorusSite n, ∏ i, Real.exp (-(c / 8 * |(((x i - z i).valMinAbs : ℤ) : ℝ)|)) =
      ∏ i : Fin 4, ∑ t : ZMod n, Real.exp (-(c / 8 * |(((t - z i).valMinAbs : ℤ) : ℝ)|)) := by
    rw [Finset.prod_univ_sum]
    simp
  rw [e1]
  have e2 : ∀ i : Fin 4, ∑ t : ZMod n, Real.exp (-(c / 8 * |(((t - z i).valMinAbs : ℤ) : ℝ)|)) ≤ B := by
    intro i
    have := sum_zmod_exp_le_tsum hc8 n
    refine le_trans (le_of_eq ?_) this
    exact Fintype.sum_equiv (Equiv.subRight (z i)) _ _ fun t => by simp
  calc _ ≤ ∏ _i : Fin 4, B :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) fun i _ => e2 i
    _ = B ^ 4 := by simp
end YangMills.Construction.TorusSums
end
