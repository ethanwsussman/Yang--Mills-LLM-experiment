import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TorusFields
variable {n : ℕ} [NeZero n]
theorem card_supDist_ball_le (z : TorusSite n) (m : ℕ) :
    (Finset.univ.filter fun y : TorusSite n => supDist y z ≤ m).card ≤ (2 * m + 1) ^ 4 := by
  classical
  set box : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) (m : ℤ) with hbox
  have hsub : (Finset.univ.filter fun y : TorusSite n => supDist y z ≤ m) ⊆
      box.image fun e => z + siteOfInt e := by
    intro y hy
    have hd : supDist y z ≤ m := (Finset.mem_filter.mp hy).2
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist z y
    refine Finset.mem_image.mpr ⟨e, ?_, he.symm⟩
    refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
    have hi := hb i
    rw [supDist_comm] at hi
    omega
  have hcard : box.card = (2 * m + 1) ^ 4 := by
    rw [hbox, Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  calc _ ≤ (box.image fun e => z + siteOfInt e).card := Finset.card_le_card hsub
    _ ≤ box.card := Finset.card_image_le
    _ = _ := hcard
theorem sum_pow_natAbs_valMinAbs_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ u : ZMod n, r ^ (u.valMinAbs).natAbs ≤ 2 / (1 - r) := by
  classical
  set P : Finset (ZMod n) := Finset.univ.filter fun u => 0 ≤ u.valMinAbs with hP
  set Q : Finset (ZMod n) := Finset.univ.filter fun u => ¬ 0 ≤ u.valMinAbs with hQ
  have hgeom : ∀ (A : Finset (ZMod n)), Set.InjOn (fun u : ZMod n => (u.valMinAbs).natAbs) A →
      ∑ u ∈ A, r ^ (u.valMinAbs).natAbs ≤ 1 / (1 - r) := by
    intro A hA
    have hs : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0 hr1
    have himg : ∑ u ∈ A, r ^ (u.valMinAbs).natAbs =
        ∑ k ∈ A.image fun u : ZMod n => (u.valMinAbs).natAbs, r ^ k :=
      (Finset.sum_image hA).symm
    rw [himg]
    refine (hs.sum_le_tsum _ fun i _ => pow_nonneg hr0 i).trans ?_
    rw [tsum_geometric_of_lt_one hr0 hr1, one_div]
  have hinj : ∀ (s : Bool) (A : Finset (ZMod n)), (∀ u ∈ A, (0 ≤ u.valMinAbs) = (s = true)) →
      Set.InjOn (fun u : ZMod n => (u.valMinAbs).natAbs) A := by
    intro s A hs u hu v hv huv
    have heq : u.valMinAbs = v.valMinAbs := by
      have hu' := hs u hu
      have hv' := hs v hv
      simp only at huv
      cases s
      · simp only [Bool.false_eq_true, eq_iff_iff, iff_false, not_le] at hu' hv'
        omega
      · simp only [eq_iff_iff, iff_true] at hu' hv'
        omega
    rw [← ZMod.coe_valMinAbs u, ← ZMod.coe_valMinAbs v, heq]
  have hsplit : ∑ u : ZMod n, r ^ (u.valMinAbs).natAbs =
      ∑ u ∈ P, r ^ (u.valMinAbs).natAbs + ∑ u ∈ Q, r ^ (u.valMinAbs).natAbs := by
    rw [hP, hQ, Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  have hPle := hgeom P (hinj true P fun u hu => by simpa [hP] using (Finset.mem_filter.mp hu).2)
  have hQle := hgeom Q (hinj false Q fun u hu => by simpa [hQ] using (Finset.mem_filter.mp hu).2)
  calc _ ≤ 1 / (1 - r) + 1 / (1 - r) := add_le_add hPle hQle
    _ = 2 / (1 - r) := by ring
theorem sum_exp_neg_mul_supDist_le {β : ℝ} (hβ : 0 < β) (z : TorusSite n) :
    ∑ y : TorusSite n, Real.exp (-β * supDist y z) ≤ (2 / (1 - Real.exp (-β / 4))) ^ 4 := by
  classical
  set r := Real.exp (-β / 4) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith
  have hterm : ∀ y : TorusSite n,
      Real.exp (-β * supDist y z) ≤ ∏ i, r ^ ((y i - z i).valMinAbs).natAbs := by
    intro y
    have hs : ∑ i, ((y i - z i).valMinAbs).natAbs ≤ 4 * supDist y z := by
      have hcoord : ∀ i, ((y i - z i).valMinAbs).natAbs ≤ supDist y z := fun i =>
        (supDist_le_iff y z _).mp le_rfl i
      calc ∑ i, ((y i - z i).valMinAbs).natAbs ≤ ∑ _i : Fin 4, supDist y z :=
            Finset.sum_le_sum fun i _ => hcoord i
        _ = 4 * supDist y z := by simp
    rw [Finset.prod_pow_eq_pow_sum, hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hcast : ((∑ i, ((y i - z i).valMinAbs).natAbs : ℕ) : ℝ) ≤ 4 * (supDist y z : ℝ) := by
      exact_mod_cast hs
    nlinarith
  calc ∑ y : TorusSite n, Real.exp (-β * supDist y z)
      ≤ ∑ y : TorusSite n, ∏ i, r ^ ((y i - z i).valMinAbs).natAbs :=
        Finset.sum_le_sum fun y _ => hterm y
    _ = ∏ i : Fin 4, ∑ u : ZMod n, r ^ ((u - z i).valMinAbs).natAbs := by
        rw [Finset.prod_univ_sum]
        simp [Fintype.piFinset_univ]
    _ = ∏ _i : Fin 4, ∑ u : ZMod n, r ^ (u.valMinAbs).natAbs := by
        refine Finset.prod_congr rfl fun i _ => ?_
        exact Fintype.sum_equiv (Equiv.subRight (z i)) _ _ fun u => rfl
    _ = (∑ u : ZMod n, r ^ (u.valMinAbs).natAbs) ^ 4 := by simp
    _ ≤ _ := by
        have hnonneg : 0 ≤ ∑ u : ZMod n, r ^ (u.valMinAbs).natAbs :=
          Finset.sum_nonneg fun u _ => pow_nonneg hr0 _
        exact pow_le_pow_left₀ hnonneg (sum_pow_natAbs_valMinAbs_le hr0 hr1) 4
theorem abs_sum_sub_sum_le_of_near_of_far {f g : TorusSite n → ℝ} {z : TorusSite n} {m : ℕ}
    {ε C β : ℝ} (hβ : 0 < β) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hnear : ∀ y, 2 * supDist y z ≤ m → |f y - g y| ≤ ε)
    (hfar : ∀ y, m < 2 * supDist y z → |f y| ≤ C * Real.exp (-β * supDist y z) ∧
      |g y| ≤ C * Real.exp (-β * supDist y z)) :
    |∑ y, f y - ∑ y, g y| ≤
      ((m : ℝ) + 1) ^ 4 * ε + 2 * C * Real.exp (-β * m / 4) * (2 / (1 - Real.exp (-(β / 2) / 4))) ^ 4 := by
  classical
  rw [← Finset.sum_sub_distrib]
  have hsplit : ∑ y, (f y - g y) =
      ∑ y ∈ Finset.univ.filter (fun y : TorusSite n => 2 * supDist y z ≤ m), (f y - g y) +
        ∑ y ∈ Finset.univ.filter (fun y : TorusSite n => ¬ 2 * supDist y z ≤ m), (f y - g y) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ε fun y hy => hnear y (Finset.mem_filter.mp hy).2).trans ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hε
    have hball := card_supDist_ball_le z (m / 2)
    have hsub : (Finset.univ.filter fun y : TorusSite n => 2 * supDist y z ≤ m) ⊆
        Finset.univ.filter fun y : TorusSite n => supDist y z ≤ m / 2 := by
      intro y hy
      have := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hcard : ((Finset.univ.filter fun y : TorusSite n => 2 * supDist y z ≤ m).card : ℝ) ≤
        (((2 * (m / 2) + 1) ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans hball
    refine hcard.trans ?_
    push_cast
    have hhalf : ((2 * (m / 2) : ℕ) : ℝ) ≤ m := by
      exact_mod_cast (by omega : 2 * (m / 2) ≤ m)
    push_cast at hhalf
    exact pow_le_pow_left₀ (by positivity) (by linarith) 4
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ y ∈ Finset.univ.filter (fun y : TorusSite n => ¬ 2 * supDist y z ≤ m),
        |f y - g y| ≤ 2 * C * Real.exp (-β * m / 4) * Real.exp (-(β / 2) * supDist y z) := by
      intro y hy
      have hm : m < 2 * supDist y z := not_le.mp (Finset.mem_filter.mp hy).2
      obtain ⟨hf, hg⟩ := hfar y hm
      have hexp : Real.exp (-β * supDist y z) ≤
          Real.exp (-β * m / 4) * Real.exp (-(β / 2) * supDist y z) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : (m : ℝ) ≤ 2 * supDist y z := by exact_mod_cast hm.le
        nlinarith
      calc |f y - g y| ≤ |f y| + |g y| := abs_sub _ _
        _ ≤ C * Real.exp (-β * supDist y z) + C * Real.exp (-β * supDist y z) := add_le_add hf hg
        _ ≤ C * (Real.exp (-β * m / 4) * Real.exp (-(β / 2) * supDist y z)) +
            C * (Real.exp (-β * m / 4) * Real.exp (-(β / 2) * supDist y z)) := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hs := sum_exp_neg_mul_supDist_le (half_pos hβ) z
    have hsub : ∑ y ∈ Finset.univ.filter (fun y : TorusSite n => ¬ 2 * supDist y z ≤ m),
        Real.exp (-(β / 2) * supDist y z) ≤ ∑ y : TorusSite n, Real.exp (-(β / 2) * supDist y z) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => (Real.exp_pos _).le
    have hnonneg : 0 ≤ 2 * C * Real.exp (-β * m / 4) := by positivity
    exact mul_le_mul_of_nonneg_left (hsub.trans hs) hnonneg
end TorusFields
end YangMills.Construction
end
