import YangMills.Construction.Lattice.SupBallCentre
import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.SupBallCentre
open TorusMetric
theorem torusSupNorm_le_iff_forall_norm_le {S : ℝ} (x : Torus4 S) (a : ℝ) :
    torusSupNorm x ≤ a ↔ ∀ μ, ‖x μ‖ ≤ a := by apply _root_.YangMills.Construction.SeparatedSequence.torusSupNorm_le_iff <;> assumption
theorem addCircle_eq_of_closedBall_eq {S r : ℝ} (hS : 0 < S) (hr : 0 ≤ r) (hr' : r ≤ S / 4)
    (a b : AddCircle S) (h : ∀ c : AddCircle S, ‖c - a‖ ≤ r ↔ ‖c - b‖ ≤ r) : a = b := by
  by_contra hne
  obtain ⟨u, hu, hu'⟩ := exists_coe_eq_abs_eq_norm (b - a)
  have hb : b = a + (u : AddCircle S) := by rw [hu]; abel
  have hur : |u| ≤ r := by
    rw [hu']
    exact (h b).2 (by simpa using hr)
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hne
    simpa using hb.symm
  obtain ⟨t, ht, htu⟩ : ∃ t : ℝ, |t| = r ∧ |t + u| = r + |u| := by
    rcases lt_or_gt_of_ne hu0 with hneg | hpos
    · refine ⟨-r, by rw [abs_neg, abs_of_nonneg hr], ?_⟩
      rw [abs_of_neg hneg, abs_of_nonpos (by linarith)]
      ring
    · refine ⟨r, abs_of_nonneg hr, ?_⟩
      rw [abs_of_pos hpos, abs_of_nonneg (by linarith)]
  have hin : ‖(a - (t : AddCircle S)) - a‖ ≤ r := by
    have hcoe : (a - (t : AddCircle S)) - a = ((-t : ℝ) : AddCircle S) := by
      rw [AddCircle.coe_neg]
      abel
    rw [hcoe]
    exact (addCircle_norm_coe_le_abs _).trans (by rw [abs_neg, ht])
  have hout := (h _).1 hin
  have hcoe : (a - (t : AddCircle S)) - b = ((-(t + u) : ℝ) : AddCircle S) := by
    rw [hb, AddCircle.coe_neg, AddCircle.coe_add]
    abel
  have hhalf : |(-(t + u) : ℝ)| ≤ |S| / 2 := by
    rw [abs_neg, htu, abs_of_pos hS]
    linarith
  rw [hcoe, (AddCircle.norm_coe_eq_abs_iff S hS.ne').2 hhalf, abs_neg, htu] at hout
  have : 0 < |u| := abs_pos.2 hu0
  linarith
theorem coord_ball_subset_of_ball_subset {S r : ℝ} (hr : 0 ≤ r) (y z : Torus4 S)
    (h : ∀ x : Torus4 S, (∀ μ, ‖x μ - y μ‖ ≤ r) → ∀ μ, ‖x μ - z μ‖ ≤ r)
    (ν : Fin 4) (c : AddCircle S) (hc : ‖c - y ν‖ ≤ r) : ‖c - z ν‖ ≤ r := by
  have hx := h (Function.update y ν c) (fun μ => by
    by_cases hμ : μ = ν
    · subst hμ
      simpa using hc
    · simpa [Function.update_of_ne hμ] using hr) ν
  simpa using hx
theorem supBallDeterminesCentre_holds : SupBallDeterminesCentre := by
  intro L m K hL _ _ t _ ρ hρ hρ' y z hball
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := by
      have := hL.2
      omega
    exact_mod_cast this
  have hc : (0 : ℝ) < (L : ℝ) ^ levelDepth K t := zpow_pos hL0 _
  have hS : 0 < torusSide L m := by
    unfold torusSide
    positivity
  have hside : sideInLevelUnits L m K t = (L : ℝ) ^ levelDepth K t * torusSide L m := by
    unfold sideInLevelUnits torusSide
    rw [show (m : ℤ) + (K : ℤ) - (t : ℤ) = (m : ℤ) + levelDepth K t by
        simp only [levelDepth]; ring,
      zpow_add₀ hL0.ne', zpow_natCast]
    ring
  have hr : 0 ≤ ρ / (L : ℝ) ^ levelDepth K t := div_nonneg hρ hc.le
  have hr' : ρ / (L : ℝ) ^ levelDepth K t ≤ torusSide L m / 4 := by
    rw [div_le_iff₀ hc]
    rw [hside] at hρ'
    linarith
  have hmem : ∀ n : ℝ, toLevelUnits L K t n ≤ ρ ↔ n ≤ ρ / (L : ℝ) ^ levelDepth K t := by
    intro n
    rw [le_div_iff₀ hc, mul_comm]
    rfl
  have hballs : ∀ x : FourTorus L m, (∀ μ, ‖x μ - y μ‖ ≤ ρ / (L : ℝ) ^ levelDepth K t) ↔
      ∀ μ, ‖x μ - z μ‖ ≤ ρ / (L : ℝ) ^ levelDepth K t := by
    intro x
    have hx : toLevelUnits L K t (torusSupNorm (x - y)) ≤ ρ ↔
        toLevelUnits L K t (torusSupNorm (x - z)) ≤ ρ := Set.ext_iff.1 hball x
    rw [hmem, hmem, torusSupNorm_le_iff_forall_norm_le,
      torusSupNorm_le_iff_forall_norm_le] at hx
    exact hx
  funext ν
  refine addCircle_eq_of_closedBall_eq hS hr hr' _ _ fun c => ⟨?_, ?_⟩
  · exact coord_ball_subset_of_ball_subset hr y z (fun x => (hballs x).1) ν c
  · exact coord_ball_subset_of_ball_subset hr z y (fun x => (hballs x).2) ν c
end YangMills.Construction.PeriodicLattice.SupBallCentre
