import YangMills.Construction.ClusterExpansionOfAStep.SumsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.SumsOverATorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.TorusSums
open TorusFields TorusLumps
variable {n : ℕ} [NeZero n]
theorem card_supDist_ball_le (y₀ : TorusSite n) (m : ℕ) :
    (((Finset.univ.filter fun y : TorusSite n => supDist y y₀ ≤ m).card : ℕ) : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 4 := by
  classical
  have hcard : (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(m : ℤ)) m).card = (2 * m + 1) ^ 4 := by
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  have hle : (Finset.univ.filter fun y : TorusSite n => supDist y y₀ ≤ m).card ≤
      (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(m : ℤ)) m).card := by
    refine Finset.card_le_card_of_injOn (fun y i => (y i - y₀ i).valMinAbs) ?_ ?_
    · intro y hy
      have hy' := (supDist_le_iff y y₀ m).mp (Finset.mem_filter.mp hy).2
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i
      have := hy' i
      omega
    · intro y _ y₂ _ hyy
      funext i
      have h1 := congrFun hyy i
      have h2 := congrArg (fun k : ℤ => (k : ZMod n)) h1
      simp only [ZMod.coe_valMinAbs] at h2
      exact sub_left_injective h2
  rw [hcard] at hle
  exact_mod_cast hle
theorem sum_pow_natAbs_valMinAbs_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ e : ZMod n, q ^ (e.valMinAbs).natAbs ≤ 2 / (1 - q) := by apply _root_.YangMills.Construction.TorusFields.sum_pow_natAbs_valMinAbs_le <;> assumption
theorem sum_exp_neg_supDist_le (y₀ : TorusSite n) {κ : ℝ} (hκ : 0 < κ) :
    ∑ y : TorusSite n, Real.exp (-(κ * (supDist y y₀ : ℝ))) ≤ (2 / (1 - Real.exp (-(κ / 4)))) ^ 4 := by
  classical
  set q := Real.exp (-(κ / 4)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    linarith
  have hpt : ∀ y : TorusSite n, Real.exp (-(κ * (supDist y y₀ : ℝ))) ≤
      ∏ i : Fin 4, q ^ ((y i - y₀ i).valMinAbs).natAbs := by
    intro y
    have hprod : ∏ i : Fin 4, q ^ ((y i - y₀ i).valMinAbs).natAbs =
        Real.exp (-(κ / 4) * ∑ i : Fin 4, ((((y i - y₀ i).valMinAbs).natAbs : ℕ) : ℝ)) := by
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hq, ← Real.exp_nat_mul]
      ring_nf
    rw [hprod, Real.exp_le_exp]
    have hb : ∀ i : Fin 4, ((((y i - y₀ i).valMinAbs).natAbs : ℕ) : ℝ) ≤ supDist y y₀ := by
      intro i
      exact_mod_cast (supDist_le_iff y y₀ _).mp le_rfl i
    have hs : ∑ i : Fin 4, ((((y i - y₀ i).valMinAbs).natAbs : ℕ) : ℝ) ≤ 4 * (supDist y y₀ : ℝ) := by
      calc _ ≤ ∑ _i : Fin 4, (supDist y y₀ : ℝ) := Finset.sum_le_sum fun i _ => hb i
        _ = _ := by simp
    nlinarith
  calc ∑ y : TorusSite n, Real.exp (-(κ * (supDist y y₀ : ℝ)))
      ≤ ∑ y : TorusSite n, ∏ i : Fin 4, q ^ ((y i - y₀ i).valMinAbs).natAbs :=
        Finset.sum_le_sum fun y _ => hpt y
    _ = ∏ i : Fin 4, ∑ e : ZMod n, q ^ ((e - y₀ i).valMinAbs).natAbs := by
        rw [Finset.prod_univ_sum]
        simp only [Fintype.piFinset_univ]
    _ ≤ ∏ _i : Fin 4, (2 / (1 - q)) := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun e _ => pow_nonneg hq0 _) fun i _ => ?_
        have := sum_pow_natAbs_valMinAbs_le (n := n) hq0 hq1
        rwa [← Equiv.sum_comp (Equiv.subRight (y₀ i))] at this
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
theorem torusSumBounds : TorusSumBounds := fun _ _ y₀ =>
  ⟨fun _ hκ => sum_exp_neg_supDist_le y₀ hκ, card_supDist_ball_le y₀⟩
end YangMills.Construction.TorusSums
end
