import YangMills.Construction.LawByMomentsOfTheFlow.LevelOfTheLastFarGap
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheLastFarLevelInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusLumps RenormalizationStepParameters TorusFields LevelTestFunctions TestFunctions
private theorem supDist_le_dist (x y : EuclideanFourSpace) : supDist x y ≤ dist x y := by apply _root_.YangMills.SharedProofs.p2932 <;> assumption
private theorem admissible_two_mul_of_supAdmissible {k : ℕ} (P : LevelData k) (L : ℕ) (R d : ℝ)
    (h : P.SupAdmissible L R d) : P.Admissible L (2 * R) d := by
  refine ⟨⟨fun i => ?_, h.isSupTestFamily.abs_le_one, fun i x hx => ?_, fun i j hij x hx y hy => ?_⟩,
    h.scaleLevel_le, h.support_small, h.exists_ne_zero⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    exact (h.isSupTestFamily.lipschitz i x y).trans (supDist_le_dist x y)
  · have hb := h.isSupTestFamily.abs_coord_le i x hx
    have hR : 0 ≤ R := (abs_nonneg _).trans (hb 0)
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hsq : ∀ a, ‖x a‖ ^ 2 ≤ R ^ 2 := fun a => by
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb a) 2
    rw [Fin.sum_univ_four]
    nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]
  · exact (h.isSupTestFamily.le_supDist i j hij x hx y hy).trans (supDist_le_dist x y)
abbrev _root_.YangMills.SharedProofs.p11807 := @admissible_two_mul_of_supAdmissible
open Classical in
private theorem findGreatest_separatedBelow_cases {k : ℕ} (P : LevelData k) (ℓ : StepParameters) (β : ℝ)
    (s : ℕ) (hs : s ≤ P.windowLevel) :
    (P.separationLevel ℓ β ≤ s ∧ Nat.findGreatest (P.SeparatedBelow ℓ β) s = P.separationLevel ℓ β) ∨
      Nat.findGreatest (P.SeparatedBelow ℓ β) s = s := by
  have h0 : P.SeparatedBelow ℓ β 0 := fun u hu => absurd hu (Nat.not_lt_zero u)
  have hlv : P.SeparatedBelow ℓ β (P.separationLevel ℓ β) := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) h0
  have hsp : P.SeparatedBelow ℓ β (Nat.findGreatest (P.SeparatedBelow ℓ β) s) :=
    Nat.findGreatest_spec (m := 0) (Nat.zero_le _) h0
  rcases Nat.lt_or_ge s (P.separationLevel ℓ β) with h | h
  · exact Or.inr (le_antisymm (Nat.findGreatest_le s)
      (Nat.le_findGreatest le_rfl fun u hu => hlv u (hu.trans h)))
  · exact Or.inl ⟨h, le_antisymm (Nat.le_findGreatest ((Nat.findGreatest_le s).trans hs) hsp)
      (Nat.le_findGreatest h hlv)⟩
open Classical in
theorem farLevelNearScale_of_separationLevel (hG : separationLevelScaleStatement)
    (hW : CouplingFlowAboveWindow) : farLevelNearScaleStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _ Kr _
  refine ⟨Tb.floorMin, fun y hy hret hbot g hg hgy k _ hk _ R d hd => ?_⟩
  have hf : (Tb.stepParameters y).Admissible := hD.fits y hy
  have hrun : AdmissibleStep (Tb.stepParameters y) := ⟨hf, hret, hbot⟩
  obtain ⟨C, hC⟩ := hG (Tb.stepParameters y) hrun g hg hgy k hk (2 * R) d hd
  refine ⟨fun _ => 1 + |C|, 1, y, one_pos, le_rfl, fun S => ?_⟩
  have hsK : S.data.scaleLevel ≤ S.data.windowLevel := S.supAdmissible.scaleLevel_le
  obtain ⟨hyj, -⟩ := hW (Tb.stepParameters y) hrun g hg hgy S.β S.data.windowLevel S.window_le S.passage
  have hy1 : (1 : ℝ) ≤ y := hf.y₁_ge
  have hxs : y ≤ S.scaleCoupling := hyj S.data.scaleLevel hsK
  have hx1 : 1 ≤ S.scaleCoupling := hy1.trans hxs
  have hlog : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg hx1
  have hr1 : (1 : ℝ) ≤ (S.range : ℝ) := by
    have : 0 < S.range := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
    exact_mod_cast this
  have hCa : 0 ≤ |C| := abs_nonneg C
  have hts : S.lastSeparated ≤ S.data.scaleLevel := Nat.findGreatest_le _
  refine ⟨hts, ?_⟩
  show ((Tb.stepParameters y).side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated) ≤ (1 + |C|) * (S.range : ℝ) ∧
    |S.coupling S.lastSeparated - S.scaleCoupling| ≤ (1 + |C|) * Real.log S.scaleCoupling
  rcases findGreatest_separatedBelow_cases S.data (Tb.stepParameters y) S.β S.data.scaleLevel hsK with
    ⟨hle, ht⟩ | ht
  · have htl : S.lastSeparated = S.data.separationLevel (Tb.stepParameters y) S.β := ht
    obtain ⟨h1, h2⟩ := hC S.data (admissible_two_mul_of_supAdmissible S.data _ R d S.supAdmissible) S.β
      S.window_le S.passage
    rw [← htl] at h1 h2
    have hz : ((Tb.stepParameters y).side : ℝ) ^ ((S.data.scaleLevel : ℤ) - (S.lastSeparated : ℤ)) =
        ((Tb.stepParameters y).side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated) := by
      rw [← Nat.cast_sub hts, zpow_natCast]
    rw [hz] at h1
    have hCC : C ≤ 1 + |C| := by linarith [le_abs_self C]
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hCC (by linarith)),
      h2.trans (mul_le_mul_of_nonneg_right hCC hlog)⟩
  · have hss : S.lastSeparated = S.data.scaleLevel := ht
    rw [hss, Nat.sub_self, pow_zero]
    refine ⟨one_le_mul_of_one_le_of_one_le (by linarith) hr1, ?_⟩
    have h0 : S.coupling S.data.scaleLevel - S.scaleCoupling = 0 := sub_self _
    rw [h0, abs_zero]
    positivity
end YangMills.Construction.MomentLaw
end
