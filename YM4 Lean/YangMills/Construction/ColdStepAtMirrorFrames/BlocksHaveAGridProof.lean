import YangMills.Construction.ColdStepAtMirrorFrames.BlocksHaveAGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
private def sideIntervalCount (h : ℤ) : ℤ := (h - 8192) / 16384
private def intervalIndex (h o : ℤ) : ℤ :=
  if (o - 8193) / 16384 < sideIntervalCount h - 1 then (o - 8193) / 16384 else sideIntervalCount h - 1
private def intervalLower (h o : ℤ) : ℤ := 8193 + intervalIndex h o * 16384
private def intervalUpper (h o : ℤ) : ℤ :=
  if (o - 8193) / 16384 < sideIntervalCount h - 1 then 8192 + (intervalIndex h o + 1) * 16384 else h
private def lowerEnd (h o : ℤ) : ℤ :=
  if |o| ≤ 8192 then -8192 else if 0 < o then intervalLower h o else -intervalUpper h (-o)
private def upperEnd (h o : ℤ) : ℤ :=
  if |o| ≤ 8192 then 8192 else if 0 < o then intervalUpper h o else -intervalLower h (-o)
private def standardLumpGrid (L : ℕ) (hL : 2 ^ 16 ≤ L) : LumpContours.LumpGrid L where
  lower := lowerEnd (((L : ℤ) - 1) / 2)
  upper := upperEnd (((L : ℤ) - 1) / 2)
  mem_interval := by
    intro o ho
    have hL' : (2 : ℤ) ^ 16 ≤ L := by exact_mod_cast hL
    generalize hh : ((L : ℤ) - 1) / 2 = h at *
    have hh2 : 32767 ≤ h := by omega
    simp only [lowerEnd, upperEnd, intervalLower, intervalUpper, intervalIndex, sideIntervalCount]
    split_ifs <;> simp only [abs_le, not_and_or, not_le] at * <;> omega
  interval_eq := by
    intro o o' ho h1 h2
    have hL' : (2 : ℤ) ^ 16 ≤ L := by exact_mod_cast hL
    generalize hh : ((L : ℤ) - 1) / 2 = h at *
    have hh2 : 32767 ≤ h := by omega
    simp only [lowerEnd, upperEnd, intervalLower, intervalUpper, intervalIndex, sideIntervalCount] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ <;> simp only [abs_le, not_and_or, not_le] at * <;> first | omega | simp
  interval_length := by
    intro o ho
    have hL' : (2 : ℤ) ^ 16 ≤ L := by exact_mod_cast hL
    generalize hh : ((L : ℤ) - 1) / 2 = h at *
    have hh2 : 32767 ≤ h := by omega
    simp only [lowerEnd, upperEnd, intervalLower, intervalUpper, intervalIndex, sideIntervalCount]
    norm_num
    split_ifs <;> simp only [abs_le, not_and_or, not_le] at * <;> omega
  lower_neg := by
    intro o ho
    simp only [lowerEnd, upperEnd, abs_neg, neg_neg]
    split_ifs <;> simp only [abs_le, not_and_or, not_le] at * <;> first | rfl | omega
theorem lumpGridExists : LumpGridExists := fun L hL => ⟨standardLumpGrid L hL⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
