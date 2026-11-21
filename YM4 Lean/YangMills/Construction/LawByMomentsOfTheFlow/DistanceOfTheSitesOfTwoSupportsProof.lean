import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOnACircle
import YangMills.Construction.LawByMomentsOfTheFlow.DistanceOfTheSitesOfTwoSupports
import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupport
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
open TestFunctions TorusFields
private theorem abs_apply_le_of_mem_closedBall {R : ℝ} {z : EuclideanFourSpace}
    (hz : z ∈ Metric.closedBall (0 : EuclideanFourSpace) R) (a : Fin 4) : |z a| ≤ R := by
  have h1 : ‖z‖ ≤ R := by simpa using hz
  have h2 : ‖z a‖ ≤ ‖z‖ := PiLp.norm_apply_le z a
  rw [Real.norm_eq_abs] at h2
  exact h2.trans h1
private theorem exists_half_le_abs_sub_apply {z z' : EuclideanFourSpace} {d : ℝ} (hd : 0 < d)
    (h : d ≤ dist z z') : ∃ a : Fin 4, d / 2 ≤ |z a - z' a| := by
  by_contra hc
  push Not at hc
  have h1 : dist z z' ^ 2 = ∑ a, (z a - z' a) ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    exact Finset.sum_congr rfl fun a _ => by rw [Real.dist_eq, sq_abs]
  have h2 : ∑ a : Fin 4, (z a - z' a) ^ 2 < ∑ _a : Fin 4, (d / 2) ^ 2 := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun a _ => ?_
    have := hc a
    rw [← sq_abs]
    exact pow_lt_pow_left₀ this (abs_nonneg _) two_ne_zero
  have h3 : ∑ _a : Fin 4, (d / 2) ^ 2 = d ^ 2 := by
    simp
    ring
  have h4 : d ^ 2 ≤ dist z z' ^ 2 := pow_le_pow_left₀ hd.le h 2
  linarith
theorem supportSiteDistanceBounds_holds (hC : CircleRepProperties)
    (hP : supportSitesLocationStatement) : SupportSiteDistanceBounds := by
  obtain ⟨-, hsh, hsub, hneg, hkeep, hsc, hsite⟩ := hC
  intro L _ hL k R d hd P hF t ht i j w hw w' hw'
  obtain ⟨z, hz, hzc⟩ := (hP L hL k P t ht i).1 w hw
  obtain ⟨z', hz', hzc'⟩ := (hP L hL k P t ht j).1 w' hw'
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hT : (0 : ℝ) < (P.period L : ℝ) := by
    have : 0 < P.period L := Nat.pos_of_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne L)))
    exact_mod_cast this
  have hzt : z ∈ tsupport (P.fn i) := subset_tsupport _ hz
  have hzt' : z' ∈ tsupport (P.fn j) := subset_tsupport _ hz'
  have hzb := abs_apply_le_of_mem_closedBall (hF.isTestFamily.tsupport_subset_closedBall i hzt)
  have hzb' := abs_apply_le_of_mem_closedBall (hF.isTestFamily.tsupport_subset_closedBall j hzt')
  set T : ℝ := (P.period L : ℝ) with hTd
  set M : ℝ := (L : ℝ) ^ P.windowLevel with hMd
  set S : ℝ := (L : ℝ) ^ P.scaleLevel with hSd
  set U : ℝ := (L : ℝ) ^ t with hUd
  set Q : ℝ := (L : ℝ) ^ (P.windowLevel - t) with hQd
  have hM : 0 < M := by positivity
  have hS : 0 < S := by positivity
  have hU : 0 < U := by positivity
  have hQ : 0 < Q := by positivity
  have hUQ : U * Q = M := by
    rw [hUd, hQd, hMd, ← pow_add, Nat.add_sub_cancel' ht]
  have hN : ((P.sideAt L t : ℕ) : ℝ) = T * Q := by
    simp only [LevelData.sideAt, hTd, hQd]
    push_cast
    ring
  have hzp : (L : ℝ) ^ ((P.scaleLevel : ℤ) - (t : ℤ)) = S / U := by
    rw [zpow_sub₀ (ne_of_gt hLpos), zpow_natCast, zpow_natCast]
  rw [hzp]
  have coord : ∀ a, |circleRep T (((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M)| * Q =
      ((((w a) - (w' a)).valMinAbs).natAbs : ℝ) := by
    intro a
    have h1 := hsite (P.sideAt L t) (w a) (w' a)
    have h2 := hsc T Q hT hQ (((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M)
    have h3 : (((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M) * Q = ((w a).val : ℝ) - ((w' a).val : ℝ) := by
      rw [← hUQ]
      field_simp
    rw [h3, ← hN] at h2
    rw [h2, abs_mul, abs_of_pos hQ] at h1
    exact h1
  have hε : U / (2 * M) * Q = 1 / 2 := by
    rw [← hUQ]
    field_simp
  have hρQ : S / M * Q = S / U := by
    rw [← hUQ]
    field_simp
  have hsmall : S / M * (2 * R) ≤ T / 2 := by
    have := hF.support_small
    rw [div_mul_eq_mul_div, div_le_iff₀ hM]
    nlinarith
  refine ⟨?_, fun hij => ?_⟩
  · obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty
      (fun i => ((w i - w' i).valMinAbs).natAbs)
    have htd : (supDist w w' : ℝ) = ((((w a) - (w' a)).valMinAbs).natAbs : ℝ) := by
      have : supDist w w' = ((w a - w' a).valMinAbs).natAbs := ha
      rw [this]
    rw [htd, ← coord a]
    have hsplit : ((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M =
        S / M * (z a - z' a) + ((((w a).val : ℝ) * U / M - P.center a - S / M * z a) +
          -(((w' a).val : ℝ) * U / M - P.center a - S / M * z' a)) := by ring
    have h1 := hsub T hT (S / M * (z a - z' a)) ((((w a).val : ℝ) * U / M - P.center a - S / M * z a) +
      -(((w' a).val : ℝ) * U / M - P.center a - S / M * z' a))
    have h2 := hsub T hT (((w a).val : ℝ) * U / M - P.center a - S / M * z a)
      (-(((w' a).val : ℝ) * U / M - P.center a - S / M * z' a))
    have h3 := hneg T hT (((w' a).val : ℝ) * U / M - P.center a - S / M * z' a)
    have h4 := hzc a
    have h5 := hzc' a
    have h6 : |circleRep T (S / M * (z a - z' a))| ≤ S / M * (2 * R) := by
      refine (hsh T hT _).trans ?_
      rw [abs_mul, abs_of_pos (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := abs_sub (z a) (z' a)
      linarith [hzb a, hzb' a]
    rw [← hsplit] at h1
    have h7 : |circleRep T (((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M)| ≤
        S / M * (2 * R) + (U / (2 * M) + U / (2 * M)) := by linarith
    calc |circleRep T (((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M)| * Q
        ≤ (S / M * (2 * R) + (U / (2 * M) + U / (2 * M))) * Q := mul_le_mul_of_nonneg_right h7 hQ.le
      _ = 2 * R * (S / M * Q) + (U / (2 * M) * Q + U / (2 * M) * Q) := by ring
      _ = 2 * R * (S / U) + 1 := by rw [hρQ, hε]; ring
  · obtain ⟨a, ha⟩ := exists_half_le_abs_sub_apply hd (hF.isTestFamily.le_dist_of_ne i j hij z hzt z' hzt')
    have htd : ((((w a) - (w' a)).valMinAbs).natAbs : ℝ) ≤ (supDist w w' : ℝ) := by
      have : ((w a - w' a).valMinAbs).natAbs ≤ supDist w w' := (supDist_le_iff _ _ _).mp le_rfl a
      exact_mod_cast this
    rw [← coord a] at htd
    have hsplit : S / M * (z a - z' a) = (((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M) +
        (-(((w a).val : ℝ) * U / M - P.center a - S / M * z a) +
          (((w' a).val : ℝ) * U / M - P.center a - S / M * z' a)) := by ring
    have h1 := hsub T hT (((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M)
      (-(((w a).val : ℝ) * U / M - P.center a - S / M * z a) +
        (((w' a).val : ℝ) * U / M - P.center a - S / M * z' a))
    have h2 := hsub T hT (-(((w a).val : ℝ) * U / M - P.center a - S / M * z a))
      (((w' a).val : ℝ) * U / M - P.center a - S / M * z' a)
    have h3 := hneg T hT (((w a).val : ℝ) * U / M - P.center a - S / M * z a)
    have h4 := hzc a
    have h5 := hzc' a
    have h6 : |S / M * (z a - z' a)| ≤ T / 2 := by
      rw [abs_mul, abs_of_pos (by positivity)]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hsmall
      have := abs_sub (z a) (z' a)
      linarith [hzb a, hzb' a]
    have h7 := hkeep T hT _ h6
    rw [← hsplit] at h1
    rw [h7, abs_mul, abs_of_pos (by positivity : 0 < S / M)] at h1
    have h8 : S / M * (d / 2) ≤ S / M * |z a - z' a| := mul_le_mul_of_nonneg_left ha (by positivity)
    have h9 : S / M * (d / 2) ≤ |circleRep T (((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M)| +
        (U / (2 * M) + U / (2 * M)) := by linarith
    calc d / 2 * (S / U) = S / M * Q * (d / 2) := by rw [hρQ]; ring
      _ = S / M * (d / 2) * Q := by ring
      _ ≤ (|circleRep T (((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M)| +
          (U / (2 * M) + U / (2 * M))) * Q := mul_le_mul_of_nonneg_right h9 hQ.le
      _ = |circleRep T (((w a).val : ℝ) * U / M - ((w' a).val : ℝ) * U / M)| * Q +
          (U / (2 * M) * Q + U / (2 * M) * Q) := by ring
      _ ≤ (supDist w w' : ℝ) + 1 := by rw [hε]; linarith
end YangMills.Construction.LevelTestFunctions
end
