import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusBalls
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
variable {n : ℕ}
theorem card_thickening_singleton_le [NeZero n] (m : ℕ) (y : TorusSite n) :
    (thickening m ({y} : Finset (TorusSite n))).card ≤ (2 * m + 1) ^ 4 := by
  classical
  have hsub : thickening m ({y} : Finset (TorusSite n)) ⊆
      (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(m : ℤ)) m).image fun e => y + siteOfInt e := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := (TorusFields.mem_thickening m _ z).mp hz
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [TorusFields.supDist_comm] at hzx
    obtain ⟨e, he, hb⟩ := TorusFields.exists_offset_of_supDist x z
    refine Finset.mem_image.mpr ⟨e, Fintype.mem_piFinset.mpr fun i => ?_, he.symm⟩
    have := hb i
    rw [Finset.mem_Icc]
    omega
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply Nat.pow_le_pow_left
  omega
theorem natAbs_ediv_sub_ediv_add_le (L : ℕ) (hL : 0 < L) (u e : ℤ) :
    (u / (L : ℤ) - (u + e) / (L : ℤ)).natAbs ≤ e.natAbs / L + 1 := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have h1 := Int.emod_add_mul_ediv u L
  have h2 := Int.emod_add_mul_ediv (u + e) L
  have h3 := Int.emod_nonneg u hL'.ne'
  have h4 := Int.emod_lt_of_pos u hL'
  have h5 := Int.emod_nonneg (u + e) hL'.ne'
  have h6 := Int.emod_lt_of_pos (u + e) hL'
  set a := u / (L : ℤ)
  set a' := (u + e) / (L : ℤ)
  set s := u % (L : ℤ)
  set s' := (u + e) % (L : ℤ)
  have key : (L : ℤ) * (a - a') = s' - s - e := by linarith [mul_sub (L : ℤ) a a']
  have hb : ((a - a').natAbs : ℤ) * L ≤ (e.natAbs : ℤ) + L := by
    have habs : |(L : ℤ) * (a - a')| ≤ |e| + L := by
      rw [key]
      have : |s' - s - e| ≤ |s' - s| + |e| := by
        simpa [sub_eq_add_neg] using abs_add_le (s' - s) (-e)
      have h7 : |s' - s| ≤ L := by
        rw [abs_le]
        constructor <;> linarith
      linarith
    rw [abs_mul, abs_of_pos hL'] at habs
    have e1 : (((a - a').natAbs : ℕ) : ℤ) = |a - a'| := Int.natCast_natAbs _
    have e2 : ((e.natAbs : ℕ) : ℤ) = |e| := Int.natCast_natAbs _
    rw [e1, e2]
    linarith [mul_comm (L : ℤ) |a - a'|]
  have hb' : (a - a').natAbs * L ≤ e.natAbs + L := by exact_mod_cast hb
  have : (a - a').natAbs ≤ (e.natAbs + L) / L := (Nat.le_div_iff_mul_le hL).mpr hb'
  rwa [Nat.add_div_right _ hL] at this
theorem supDist_parentBlock_le_div_add_one [NeZero n] (L : ℕ) [NeZero L] (p q : TorusSite (n * L)) :
    supDist (parentBlock L p) (parentBlock L q) ≤ supDist p q / L + 1 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  rw [TorusFields.supDist_le_iff]
  intro i
  obtain ⟨e, he, hb⟩ := TorusFields.exists_offset_of_supDist p q
  have hq : q i = p i + ((e i : ℤ) : ZMod (n * L)) := by
    rw [he]
    simp [siteOfInt]
  set cp : ℤ := ((p i).cast : ℤ)
  set cq : ℤ := ((q i).cast : ℤ)
  have hcp : ((cp : ℤ) : ZMod (n * L)) = p i := ZMod.intCast_zmod_cast _
  have hcq : ((cq : ℤ) : ZMod (n * L)) = q i := ZMod.intCast_zmod_cast _
  have hdvd : ((n * L : ℕ) : ℤ) ∣ (cp + e i) - cq := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    rw [hcq, hq]
    push_cast
    rw [hcp]
  obtain ⟨k, hk⟩ := hdvd
  set h : ℤ := ((L : ℤ) - 1) / 2
  have hq' : (cq + h) / (L : ℤ) = (cp + h + e i) / (L : ℤ) - n * k := by
    have h1 : cq + h = (cp + h + e i) + (L : ℤ) * (-(n * k)) := by
      push_cast at hk
      linear_combination -hk
    rw [h1, Int.add_mul_ediv_left _ _ (by exact_mod_cast hL.ne')]
    ring
  have hval : parentBlock L p i - parentBlock L q i =
      (((cp + h) / (L : ℤ) - (cp + h + e i) / (L : ℤ) : ℤ) : ZMod n) := by
    show (((cp + h) / (L : ℤ) : ℤ) : ZMod n) - (((cq + h) / (L : ℤ) : ℤ) : ZMod n) = _
    rw [hq']
    push_cast
    simp
  rw [hval]
  refine (TorusFields.natAbs_valMinAbs_intCast_le _).trans
    ((natAbs_ediv_sub_ediv_add_le L hL _ _).trans ?_)
  exact Nat.add_le_add_right (Nat.div_le_div_right (hb i)) 1
theorem exists_sum_poly_mul_exp_le (c : ℝ) (hc : 0 < c) : ∃ A : ℝ, 0 ≤ A ∧ ∀ (D : ℕ) (s : Finset ℕ),
    (∀ k ∈ s, D ≤ k) →
    ∑ k ∈ s, ((2 * k + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(c * k)) ≤ A * Real.exp (-(c * D / 2)) := by
  have hq0 : 0 ≤ Real.exp (-(c / 4)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(c / 4)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hsum := summable_geometric_of_lt_one hq0 hq1
  set B : ℝ := 24 * (8 / c) ^ 4 * Real.exp (c / 8) with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨B * ∑' k : ℕ, Real.exp (-(c / 4)) ^ k, by positivity, fun D s hs => ?_⟩
  have hterm : ∀ k ∈ s, ((2 * k + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(c * k)) ≤
      B * Real.exp (-(c / 4)) ^ k * Real.exp (-(c * D / 2)) := by
    intro k hk
    have hD : (D : ℝ) ≤ k := by exact_mod_cast hs k hk
    set u : ℝ := c * (2 * k + 1) / 8 with hu
    have hu0 : 0 ≤ u := by positivity
    have hpow : u ^ 4 / (4 : ℕ).factorial ≤ Real.exp u := Real.pow_div_factorial_le_exp u hu0 4
    have hfac : (((4 : ℕ).factorial : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hfac] at hpow
    have h1 : ((2 * k + 1 : ℕ) : ℝ) ^ 4 ≤ 24 * (8 / c) ^ 4 * Real.exp u := by
      have : ((2 * k + 1 : ℕ) : ℝ) = 8 / c * u := by
        rw [hu]
        push_cast
        field_simp
      rw [this, mul_pow]
      have h2 : u ^ 4 ≤ 24 * Real.exp u := by linarith
      have h3 : 0 ≤ (8 / c) ^ 4 := by positivity
      nlinarith
    have hexp : Real.exp (-(c / 4)) ^ k = Real.exp (-(c / 4) * k) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp, hB]
    calc ((2 * k + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(c * k))
        ≤ 24 * (8 / c) ^ 4 * Real.exp u * Real.exp (-(c * k)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 24 * (8 / c) ^ 4 * Real.exp (c / 8) * Real.exp (-(c / 4) * k) *
            Real.exp (-(c * k / 2)) := by
          have he : Real.exp u * Real.exp (-(c * k)) =
              Real.exp (c / 8) * Real.exp (-(c / 4) * k) * Real.exp (-(c * k / 2)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hu]
            congr 1
            ring
          calc 24 * (8 / c) ^ 4 * Real.exp u * Real.exp (-(c * k))
              = 24 * (8 / c) ^ 4 * (Real.exp u * Real.exp (-(c * k))) := by ring
            _ = _ := by rw [he]; ring
      _ ≤ 24 * (8 / c) ^ 4 * Real.exp (c / 8) * Real.exp (-(c / 4) * k) *
            Real.exp (-(c * D / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Real.exp_le_exp]
          nlinarith
  calc ∑ k ∈ s, ((2 * k + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(c * k))
      ≤ ∑ k ∈ s, B * Real.exp (-(c / 4)) ^ k * Real.exp (-(c * D / 2)) := Finset.sum_le_sum hterm
    _ = B * (∑ k ∈ s, Real.exp (-(c / 4)) ^ k) * Real.exp (-(c * D / 2)) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ B * (∑' k : ℕ, Real.exp (-(c / 4)) ^ k) * Real.exp (-(c * D / 2)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hB0) (Real.exp_pos _).le
        exact hsum.sum_le_tsum s fun k _ => pow_nonneg hq0 k
theorem exists_sum_exp_supDist_le (c : ℝ) (hc : 0 < c) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (D : ℕ),
    ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => D ≤ supDist Y y), Real.exp (-(c * supDist Y y)) ≤
      A * Real.exp (-(c * D / 2)) := by
  classical
  obtain ⟨A, hA, h⟩ := exists_sum_poly_mul_exp_le c hc
  refine ⟨A, hA, fun n _ y D => ?_⟩
  set S := Finset.univ.filter (fun Y : TorusSite n => D ≤ supDist Y y) with hS
  set I : Finset ℕ := S.image fun Y => supDist Y y with hI
  have hmaps : ∀ Y ∈ S, supDist Y y ∈ I := fun Y hY => Finset.mem_image_of_mem _ hY
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (h D I fun k hk => ?_)
  · have hfib : ∑ Y ∈ S.filter (fun Y => supDist Y y = k), Real.exp (-(c * supDist Y y)) =
        ((S.filter fun Y => supDist Y y = k).card : ℝ) * Real.exp (-(c * k)) := by
      rw [Finset.sum_congr rfl fun Y hY => by rw [(Finset.mem_filter.mp hY).2], Finset.sum_const,
        nsmul_eq_mul]
    rw [hfib]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hsub : S.filter (fun Y => supDist Y y = k) ⊆ thickening k ({y} : Finset (TorusSite n)) := by
      intro Y hY
      exact (TorusFields.mem_thickening _ _ _).mpr
        ⟨y, Finset.mem_singleton_self _, (Finset.mem_filter.mp hY).2.le⟩
    have h1 := (Finset.card_le_card hsub).trans (card_thickening_singleton_le k y)
    have h2 : (((2 * k + 1) ^ 4 : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) ^ 4 := by push_cast; ring
    rw [← h2]
    exact_mod_cast h1
  · obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hY).2
end YangMills.Construction.TorusBalls
end
