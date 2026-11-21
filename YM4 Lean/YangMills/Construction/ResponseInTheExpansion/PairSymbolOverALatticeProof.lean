import YangMills.Construction.ResponseInTheExpansion.PairSymbolOverALattice
import YangMills.Construction.ResponseInTheExpansion.RapidSymbolOverALattice
import YangMills.Construction.ResponseInTheExpansion.TheCutSymbolIsRapid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFourier
private lemma exists_coord_sq_ge_quarter_normSq (z : Fin 4 → ℝ) :
    ∃ i, (∑ j, z j ^ 2) / 4 ≤ z i ^ 2 := by
  by_contra hno
  simp only [not_exists, not_le] at hno
  have h := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
    (fun i _ => hno i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  norm_num at h
  linarith
private lemma inv_abs_pow_five_le_rpow (R y : ℝ) (hR : 0 < R) (hy : R / 4 ≤ y ^ 2) :
    (|y| ^ 5)⁻¹ ≤ ((1 / 4 : ℝ) ^ (5 / 2 : ℝ))⁻¹ * R ^ (-(5 / 2 : ℝ)) := by
  have h1 : |y| ^ 5 = (y ^ 2) ^ (5 / 2 : ℝ) := by
    rw [← sq_abs y, ← Real.rpow_natCast |y| 2, ← Real.rpow_mul (abs_nonneg y)]
    rw [← Real.rpow_natCast |y| 5]
    norm_num
  have h2 : (R / 4) ^ (5 / 2 : ℝ) ≤ (y ^ 2) ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hy (by norm_num)
  have h3 : (R / 4) ^ (5 / 2 : ℝ) = (1 / 4 : ℝ) ^ (5 / 2 : ℝ) * R ^ (5 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by norm_num) hR.le]
    congr 1
    ring
  rw [h1, Real.rpow_neg hR.le, ← mul_inv]
  refine inv_anti₀ (by positivity) ?_
  rw [← h3]
  exact h2
private lemma circleMomentum_eq_mul (N : ℕ) (n : ℤ) :
    circleMomentum N n = (2 * Real.pi / N) * n := by
  unfold circleMomentum
  ring
theorem cutPairSymbolLattice_holds (hR : schwartzLatticeSumDecayStatement)
    (hC : cutoffSymbolSchwartzStatement) (hG : gaussianSymbolLatticeStatement) :
    cutPairSymbolLatticeStatement := by
  intro χ hχ hnear hfar
  obtain ⟨CG, hCG⟩ := hG
  have hf := hC χ hχ hnear hfar
  choose f hfv using hf
  have hr := fun a b => hR (f a b)
  choose Cr hCr using hr
  set K : ℝ := ((1 / 4 : ℝ) ^ (5 / 2 : ℝ))⁻¹ with hK
  have hpi := Real.pi_pos
  refine ⟨|CG| + K * ∑ a, ∑ b, |Cr a b|, fun N z a b hN hz1 hzN => ?_⟩
  have hN' : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  set h : ℝ := 2 * Real.pi / N with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_one hN0]
    nlinarith [Real.pi_lt_four]
  have hp : ∀ k : Fin 4 → ℤ, (fun j => h * (k j : ℝ)) = fun i => circleMomentum N (k i) := by
    intro k
    funext j
    rw [circleMomentum_eq_mul]
  obtain ⟨i, hi⟩ := exists_coord_sq_ge_quarter_normSq z
  set R := ∑ j, z j ^ 2 with hRdef
  have hR0 : 0 < R := by linarith
  have hzi : z i ≠ 0 := by
    intro h0
    rw [h0] at hi
    norm_num at hi
    linarith
  have hzb : |z i| ≤ (N : ℝ) / 8 := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    exact (Finset.single_le_sum (f := fun j => z j ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)).trans hzN
  have hturn : h * |z i| ≤ Real.pi := by
    calc h * |z i| ≤ h * ((N : ℝ) / 8) := by gcongr
      _ = Real.pi / 4 := by rw [hh]; field_simp; ring
      _ ≤ Real.pi := by linarith
  obtain ⟨hsum, hbound⟩ := hCr a b h z i hh0 hh1 hzi hturn
  obtain ⟨gsum, gbound⟩ := hCG N z a b hN hz1 hzN
  set F : (Fin 4 → ℤ) → ℂ := fun k =>
    f a b (fun j => h * (k j : ℝ)) * Complex.exp (Complex.I * ((∑ j, h * (k j : ℝ) * z j : ℝ) : ℂ))
    with hF
  have hsplit : ∀ k, cutPairSymbolTerm χ N z a b k = gaussianSymbolTerm N z a b k + F k := by
    intro k
    simp only [hF, cutPairSymbolTerm, gaussianSymbolTerm]
    rw [hp k, hfv a b]
    have e1 : (∑ j, h * (k j : ℝ) * z j : ℝ) = ∑ j, circleMomentum N (k j) * z j :=
      Finset.sum_congr rfl fun j _ => by rw [circleMomentum_eq_mul]
    rw [e1, ← add_mul]
    congr 1
    push_cast
    ring
  have hfun : cutPairSymbolTerm χ N z a b = fun k => gaussianSymbolTerm N z a b k + F k :=
    funext hsplit
  refine ⟨by rw [hfun]; exact gsum.add hsum, ?_⟩
  rw [hfun, gsum.tsum_add hsum]
  have e2 : ((N : ℂ) ^ 4)⁻¹ * (∑' k, gaussianSymbolTerm N z a b k + ∑' k, F k) -
      (greenHessian z a b : ℂ) =
      (((N : ℂ) ^ 4)⁻¹ * ∑' k, gaussianSymbolTerm N z a b k - (greenHessian z a b : ℂ)) +
        ((2 * Real.pi : ℂ) ^ 4)⁻¹ * ((h : ℂ) ^ 4 * ∑' k, F k) := by
    have hpc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    rw [hh]
    push_cast
    field_simp
    ring
  rw [e2]
  set Rq : ℝ := R ^ (-(5 / 2 : ℝ)) with hRq
  set Nq : ℝ := (N : ℝ) ^ (-(4 : ℤ)) with hNq
  have hNq0 : 0 ≤ Nq := by positivity
  have hq : ‖((2 * Real.pi : ℂ) ^ 4)⁻¹‖ ≤ 1 := by
    have : ‖((2 * Real.pi : ℂ) ^ 4)⁻¹‖ = ((2 * Real.pi) ^ 4)⁻¹ := by
      rw [norm_inv, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
      norm_num
    rw [this]
    refine inv_le_one_of_one_le₀ ?_
    have : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    exact one_le_pow₀ this
  have hfive := inv_abs_pow_five_le_rpow R (z i) hR0 hi
  have hcr : Cr a b ≤ ∑ a, ∑ b, |Cr a b| := by
    have h1 : Cr a b ≤ |Cr a b| := le_abs_self _
    have h2 : |Cr a b| ≤ ∑ b, |Cr a b| :=
      Finset.single_le_sum (f := fun b => |Cr a b|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
    have h3 : ∑ b, |Cr a b| ≤ ∑ a, ∑ b, |Cr a b| :=
      Finset.single_le_sum (f := fun a => ∑ b, |Cr a b|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith
  set S := ∑ a, ∑ b, |Cr a b| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have b2 : ‖((2 * Real.pi : ℂ) ^ 4)⁻¹ * ((h : ℂ) ^ 4 * ∑' k, F k)‖ ≤ S * (K * Rq) := by
    rw [norm_mul]
    have h0 : 0 ≤ (|z i| ^ 5)⁻¹ := by positivity
    have h1 : ‖(h : ℂ) ^ 4 * ∑' k, F k‖ ≤ S * (K * Rq) := by
      refine hbound.trans ?_
      exact mul_le_mul hcr hfive h0 hS0
    have h2 : 0 ≤ S * (K * Rq) := by positivity
    calc _ ≤ 1 * (S * (K * Rq)) := mul_le_mul hq h1 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have b1 : ‖((N : ℂ) ^ 4)⁻¹ * ∑' k, gaussianSymbolTerm N z a b k - (greenHessian z a b : ℂ)‖ ≤
      |CG| * (Rq + Nq) :=
    gbound.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  refine (norm_add_le _ _).trans ?_
  have hKS : 0 ≤ K * S := by positivity
  nlinarith [mul_nonneg hKS hNq0]
end YangMills.Construction.LatticeFourier
