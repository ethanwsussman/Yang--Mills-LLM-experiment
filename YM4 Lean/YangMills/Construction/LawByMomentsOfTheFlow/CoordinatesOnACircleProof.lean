import YangMills.Construction.ColdStepAtMirrorFrames.EnergyOfAFlatChainNearACellProof
import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOnACircle
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
private theorem circleRep_add_mul_int (c : ℝ) (hc : 0 < c) (v : ℝ) (e : ℤ) :
    circleRep c (v + c * e) = circleRep c v := by
  have h : (v + c * e) / c = v / c + e := by field_simp
  unfold circleRep
  rw [h, round_add_intCast]
  push_cast
  ring
private theorem abs_circleRep_le (c : ℝ) (hc : 0 < c) (v : ℝ) (e : ℤ) : |circleRep c v| ≤ |v - c * e| := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatChainEnergy.distToMultiples_le <;> assumption
private theorem abs_circleRep_le_abs (c : ℝ) (hc : 0 < c) (v : ℝ) : |circleRep c v| ≤ |v| := by
  simpa using abs_circleRep_le c hc v 0
private theorem abs_circleRep_add_le (c : ℝ) (hc : 0 < c) (u v : ℝ) :
    |circleRep c (u + v)| ≤ |circleRep c u| + |circleRep c v| := by
  have h := abs_circleRep_le c hc (u + v) (round (u / c) + round (v / c))
  refine h.trans ?_
  have : u + v - c * ((round (u / c) + round (v / c) : ℤ) : ℝ) = circleRep c u + circleRep c v := by
    unfold circleRep
    push_cast
    ring
  rw [this]
  exact abs_add_le _ _
private theorem abs_circleRep_neg_le (c : ℝ) (hc : 0 < c) (v : ℝ) : |circleRep c (-v)| ≤ |circleRep c v| := by
  have h := abs_circleRep_le c hc (-v) (-round (v / c))
  refine h.trans (le_of_eq ?_)
  rw [← abs_neg]
  unfold circleRep
  congr 1
  push_cast
  ring
private theorem abs_circleRep_eq_of_le (c : ℝ) (hc : 0 < c) (v : ℝ) (hv : |v| ≤ c / 2) :
    |circleRep c v| = |v| := by
  refine le_antisymm (abs_circleRep_le_abs c hc v) ?_
  by_cases hr : round (v / c) = 0
  · simp [circleRep, hr]
  have h1 : (1 : ℝ) ≤ |(round (v / c) : ℝ)| := by
    have : (1 : ℤ) ≤ |round (v / c)| := Int.one_le_abs hr
    exact_mod_cast this
  have h2 : |c * (round (v / c) : ℝ)| ≤ |circleRep c v| + |v| := by
    have : c * (round (v / c) : ℝ) = v - circleRep c v := by
      unfold circleRep
      ring
    rw [this]
    exact (abs_sub _ _).trans (by rw [add_comm])
  rw [abs_mul, abs_of_pos hc] at h2
  nlinarith
private theorem circleRep_mul (c M : ℝ) (hc : 0 < c) (hM : 0 < M) (v : ℝ) :
    circleRep (c * M) (v * M) = circleRep c v * M := by
  have h : v * M / (c * M) = v / c := by field_simp
  unfold circleRep
  rw [h]
  ring
private theorem abs_circleRep_val_sub (N : ℕ) [NeZero N] (y y' : ZMod N) :
    |circleRep N ((y.val : ℝ) - (y'.val : ℝ))| = (((y - y').valMinAbs).natAbs : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set e : ℤ := (y - y').valMinAbs with he
  have hc : ((((y.val : ℤ) - (y'.val : ℤ)) : ℤ) : ZMod N) = ((e : ℤ) : ZMod N) := by
    rw [he, ZMod.coe_valMinAbs]
    simp
  obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hc
  have h1 : ((y.val : ℝ) - (y'.val : ℝ)) = (e : ℝ) + N * (-w : ℤ) := by
    have : (e : ℤ) - ((y.val : ℤ) - (y'.val : ℤ)) = (N : ℤ) * w := hw
    have h2 : ((e : ℝ)) - ((y.val : ℝ) - (y'.val : ℝ)) = (N : ℝ) * (w : ℝ) := by exact_mod_cast this
    push_cast
    linarith
  rw [h1, circleRep_add_mul_int _ hN]
  have hb : |(e : ℝ)| ≤ (N : ℝ) / 2 := by
    have h3 : e.natAbs ≤ N / 2 := ZMod.natAbs_valMinAbs_le _
    have h4 : ((e.natAbs : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
      have : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
      exact (by exact_mod_cast h3 : ((e.natAbs : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ)).trans this
    rwa [Nat.cast_natAbs, Int.cast_abs] at h4
  rw [abs_circleRep_eq_of_le _ hN _ hb, Nat.cast_natAbs, Int.cast_abs]
theorem circleRepProperties_holds : CircleRepProperties :=
  ⟨circleRep_add_mul_int, abs_circleRep_le_abs, abs_circleRep_add_le, abs_circleRep_neg_le,
    abs_circleRep_eq_of_le, circleRep_mul, @abs_circleRep_val_sub⟩
end YangMills.Construction.LevelTestFunctions
end
