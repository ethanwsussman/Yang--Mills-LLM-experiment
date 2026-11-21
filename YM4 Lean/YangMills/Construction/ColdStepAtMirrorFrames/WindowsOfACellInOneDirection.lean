import YangMills.Construction.ColdStepAtMirrorFrames.BlockMeansOfFormsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
variable {F : BlockFrame}
abbrev cellSide (F : BlockFrame) : ℕ := F.blockSide ^ F.top
def cellHalfSide (F : BlockFrame) : ℤ := ((F.blockSide : ℤ) ^ F.top - 1) / 2
def windowIndex (i : Fin 4) (x : F.Site 0) : ℕ :=
  ((siteCoords x i + cellHalfSide F) % (cellSide F : ℤ)).toNat
def windowStart (i : Fin 4) (x : F.Site 0) : F.Site 0 := x + axisOffset 0 i (-(windowIndex i x : ℤ))
theorem cellSide_pos (hodd : Odd F.blockSide) : 0 < cellSide F := pow_pos hodd.pos _
theorem cellSide_ne_zero (hodd : Odd F.blockSide) : (cellSide F : ℝ) ≠ 0 := by
  have := cellSide_pos hodd
  positivity
theorem natCast_windowIndex (hodd : Odd F.blockSide) (i : Fin 4) (x : F.Site 0) :
    (windowIndex i x : ℤ) = (siteCoords x i + cellHalfSide F) % (cellSide F : ℤ) := by
  unfold windowIndex
  apply Int.toNat_of_nonneg
  apply Int.emod_nonneg
  have := cellSide_pos hodd
  omega
theorem windowIndex_lt (hodd : Odd F.blockSide) (i : Fin 4) (x : F.Site 0) :
    windowIndex i x < cellSide F := by
  have h := natCast_windowIndex hodd i x
  have hp : (0 : ℤ) < (cellSide F : ℤ) := by exact_mod_cast cellSide_pos hodd
  have := Int.emod_lt_of_pos (siteCoords x i + cellHalfSide F) hp
  omega
theorem cellSide_dvd_period (i : Fin 4) : (cellSide F : ℤ) ∣ (F.period 0 i : ℤ) := by
  rw [period_eq_pow_mul_int (Nat.zero_le F.top) le_rfl i]
  simp only [Nat.sub_zero]
  exact ⟨_, by push_cast; rfl⟩
theorem natCast_windowIndex_siteOfCoords (hodd : Odd F.blockSide) (i : Fin 4) (a : Fin 4 → ℤ) :
    (windowIndex i (siteOfCoords 0 a : F.Site 0) : ℤ) = (a i + cellHalfSide F) % (cellSide F : ℤ) := by
  rw [natCast_windowIndex hodd, siteCoords_siteOfCoords, Int.add_emod,
    Int.emod_emod_of_dvd _ (cellSide_dvd_period i), ← Int.add_emod]
theorem add_axisOffset_eq_siteOfCoords (x : F.Site 0) (k : Fin 4) (u : ℤ) :
    x + axisOffset 0 k u = siteOfCoords 0 (siteCoords x + Pi.single k u) := by
  unfold axisOffset
  rw [siteOfCoords_add, siteOfCoords_siteCoords]
theorem natCast_windowIndex_add_axisOffset (hodd : Odd F.blockSide) (i : Fin 4) (x : F.Site 0) (u : ℤ) :
    (windowIndex i (x + axisOffset 0 i u) : ℤ) = ((windowIndex i x : ℤ) + u) % (cellSide F : ℤ) := by
  rw [add_axisOffset_eq_siteOfCoords, natCast_windowIndex_siteOfCoords hodd, natCast_windowIndex hodd]
  simp only [Pi.add_apply, Pi.single_eq_same]
  rw [Int.emod_add_emod]
  congr 1
  ring
theorem windowIndex_add_axisOffset_of_ne (hodd : Odd F.blockSide) {i k : Fin 4} (hki : k ≠ i)
    (x : F.Site 0) (u : ℤ) :
    windowIndex i (x + axisOffset 0 k u) = windowIndex i x := by
  have : (windowIndex i (x + axisOffset 0 k u) : ℤ) = windowIndex i x := by
    rw [add_axisOffset_eq_siteOfCoords, natCast_windowIndex_siteOfCoords hodd, natCast_windowIndex hodd]
    simp only [Pi.add_apply, Pi.single_eq_of_ne hki.symm, add_zero]
  exact_mod_cast this
theorem windowIndex_add_unitStep (hodd : Odd F.blockSide) (i : Fin 4) (x : F.Site 0)
    (h : windowIndex i x + 1 < cellSide F) :
    windowIndex i (x + unitStep 0 i) = windowIndex i x + 1 := by
  have e := natCast_windowIndex_add_axisOffset hodd i x 1
  rw [axisOffset_one] at e
  have h' : ((windowIndex i x : ℤ) + 1) < (cellSide F : ℤ) := by exact_mod_cast h
  rw [Int.emod_eq_of_lt (by positivity) h'] at e
  exact_mod_cast e
theorem windowIndex_add_unitStep_of_eq (hodd : Odd F.blockSide) (i : Fin 4) (x : F.Site 0)
    (h : windowIndex i x + 1 = cellSide F) :
    windowIndex i (x + unitStep 0 i) = 0 := by
  have e := natCast_windowIndex_add_axisOffset hodd i x 1
  rw [axisOffset_one] at e
  have h' : ((windowIndex i x : ℤ) + 1) = (cellSide F : ℤ) := by exact_mod_cast h
  rw [h', Int.emod_self] at e
  exact_mod_cast e
theorem windowStart_add_axisOffset_windowIndex (i : Fin 4) (x : F.Site 0) :
    windowStart i x + axisOffset 0 i (windowIndex i x : ℤ) = x := by
  unfold windowStart
  rw [add_assoc, ← axisOffset_add]
  simp [axisOffset_zero]
theorem windowStart_add_unitStep (hodd : Odd F.blockSide) (i : Fin 4) (x : F.Site 0)
    (h : windowIndex i x + 1 < cellSide F) :
    windowStart i (x + unitStep 0 i) = windowStart i x := by
  unfold windowStart
  rw [windowIndex_add_unitStep hodd i x h, ← axisOffset_one, add_assoc, ← axisOffset_add]
  congr 2
  push_cast
  ring
theorem windowStart_add_unitStep_of_eq (hodd : Odd F.blockSide) (i : Fin 4) (x : F.Site 0)
    (h : windowIndex i x + 1 = cellSide F) :
    windowStart i (x + unitStep 0 i) = windowStart i x + axisOffset 0 i (cellSide F : ℤ) := by
  unfold windowStart
  rw [windowIndex_add_unitStep_of_eq hodd i x h]
  have hN : (cellSide F : ℤ) = (windowIndex i x : ℤ) + 1 := by exact_mod_cast h.symm
  have e : -(windowIndex i x : ℤ) + ((windowIndex i x : ℤ) + 1) = 1 := by ring
  rw [hN, add_assoc x (axisOffset _ _ _), ← axisOffset_add, e, axisOffset_one]
  simp [axisOffset_zero]
theorem windowStart_add_axisOffset_of_ne (hodd : Odd F.blockSide) {i k : Fin 4} (hki : k ≠ i)
    (x : F.Site 0) (u : ℤ) :
    windowStart i (x + axisOffset 0 k u) = windowStart i x + axisOffset 0 k u := by
  unfold windowStart
  rw [windowIndex_add_axisOffset_of_ne hodd hki, add_right_comm]
def windowGauge (Y : LevelForm F 0) (i : Fin 4) (x : F.Site 0) : ℝ :=
  lineSum Y (windowStart i x) i (windowIndex i x) -
    ((windowIndex i x : ℝ) / cellSide F) * lineSum Y (windowStart i x) i (cellSide F)
def windowForm (Y : LevelForm F 0) (i : Fin 4) : LevelForm F 0 := fun x k =>
  if k = i then (1 / (cellSide F : ℝ)) * lineSum Y (windowStart i x) i (cellSide F)
  else (1 - (windowIndex i x : ℝ) / cellSide F) * Y (windowStart i x) k +
    ((windowIndex i x : ℝ) / cellSide F) * Y (windowStart i x + axisOffset 0 i (cellSide F : ℤ)) k
def windowDefect (Y : LevelForm F 0) (i k : Fin 4) (x : F.Site 0) : ℝ :=
  ∑ l ∈ Finset.range (windowIndex i x), plaquetteCurl Y (windowStart i x + axisOffset 0 i (l : ℤ)) i k -
    ((windowIndex i x : ℝ) / cellSide F) *
      ∑ l ∈ Finset.range (cellSide F), plaquetteCurl Y (windowStart i x + axisOffset 0 i (l : ℤ)) i k
theorem latticeGradient_windowGauge_self (hodd : Odd F.blockSide) (Y : LevelForm F 0) (i : Fin 4)
    (x : F.Site 0) :
    latticeGradient (windowGauge Y i) x i = Y x i - windowForm Y i x i := by
  have hN := cellSide_ne_zero hodd
  have hlt := windowIndex_lt hodd i x
  unfold latticeGradient windowForm
  simp only [if_true]
  rcases Nat.lt_or_ge (windowIndex i x + 1) (cellSide F) with h | h
  · unfold windowGauge
    rw [windowStart_add_unitStep hodd i x h, windowIndex_add_unitStep hodd i x h]
    have e : lineSum Y (windowStart i x) i (windowIndex i x + 1) =
        lineSum Y (windowStart i x) i (windowIndex i x) + Y x i := by
      unfold lineSum
      rw [Finset.sum_range_succ, windowStart_add_axisOffset_windowIndex]
    rw [e]
    push_cast
    field_simp
    ring
  · have h1 : windowIndex i x + 1 = cellSide F := by omega
    unfold windowGauge
    rw [windowIndex_add_unitStep_of_eq hodd i x h1]
    have e : lineSum Y (windowStart i x) i (cellSide F) =
        lineSum Y (windowStart i x) i (windowIndex i x) + Y x i := by
      rw [← h1]
      unfold lineSum
      rw [Finset.sum_range_succ, windowStart_add_axisOffset_windowIndex]
    have hr : (windowIndex i x : ℝ) = (cellSide F : ℝ) - 1 := by
      rw [← h1]
      push_cast
      ring
    simp only [lineSum, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_div, zero_mul, sub_zero]
    simp only [lineSum] at e
    rw [e, hr]
    field_simp
    ring
theorem sub_windowForm_sub_latticeGradient_windowGauge (hodd : Odd F.blockSide) (Y : LevelForm F 0)
    {i k : Fin 4} (hki : k ≠ i) (x : F.Site 0) :
    Y x k - windowForm Y i x k - latticeGradient (windowGauge Y i) x k = windowDefect Y i k x := by
  unfold latticeGradient windowForm windowGauge windowDefect
  rw [if_neg hki]
  have e0 : x + unitStep 0 k = x + axisOffset 0 k 1 := rfl
  rw [e0, windowIndex_add_axisOffset_of_ne hodd hki, windowStart_add_axisOffset_of_ne hodd hki, axisOffset_one]
  set s := windowStart i x with hs
  set r := windowIndex i x with hr
  have h1 := sub_lineSum_eq_sum_plaquetteCurl Y s i k r
  have h2 := sub_lineSum_eq_sum_plaquetteCurl Y s i k (cellSide F)
  have hx : s + axisOffset 0 i (r : ℤ) = x := windowStart_add_axisOffset_windowIndex i x
  rw [hx] at h1
  rw [← h1, ← h2]
  ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
