import YangMills.Construction.ColdStepAtMirrorFrames.WindowsOfACellInOneDirection
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def axisMean (Z : LevelForm F 0) (i : Fin 4) : LevelForm F 0 := fun x k =>
  (1 / (cellSide F : ℝ)) * ∑ u ∈ Finset.range (cellSide F), Z (x + axisOffset 0 i (u : ℤ)) k
def axisMeanGauge (Z : LevelForm F 0) (i : Fin 4) (x : F.Site 0) : ℝ :=
  (1 / (cellSide F : ℝ)) * ∑ u ∈ Finset.range (cellSide F), lineSum Z x i u
def axisMeanDefect (Z : LevelForm F 0) (i k : Fin 4) (x : F.Site 0) : ℝ :=
  (1 / (cellSide F : ℝ)) * ∑ u ∈ Finset.range (cellSide F), ∑ l ∈ Finset.range u,
    plaquetteCurl Z (x + axisOffset 0 i (l : ℤ)) i k
theorem axisMean_sub_sub_latticeGradient (hL : Odd F.blockSide) (Z : LevelForm F 0) (i k : Fin 4)
    (x : F.Site 0) :
    axisMean Z i x k - Z x k - latticeGradient (axisMeanGauge Z i) x k = axisMeanDefect Z i k x := by
  have hN := cellSide_ne_zero hL
  unfold axisMeanDefect
  simp only [← sub_lineSum_eq_sum_plaquetteCurl]
  unfold axisMean latticeGradient axisMeanGauge
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
def windowProjection (Z : LevelForm F 0) (i : Fin 4) : LevelForm F 0 := windowForm (axisMean Z i) i
def directionGauge (Z : LevelForm F 0) (i : Fin 4) (x : F.Site 0) : ℝ :=
  windowGauge (axisMean Z i) i x - axisMeanGauge Z i x
def directionDefect (Z : LevelForm F 0) (i : Fin 4) : LevelForm F 0 := fun x k =>
  (if k = i then 0 else windowDefect (axisMean Z i) i k x) - axisMeanDefect Z i k x
theorem latticeGradient_sub (φ ψ : F.Site 0 → ℝ) (x : F.Site 0) (k : Fin 4) :
    latticeGradient (fun y => φ y - ψ y) x k = latticeGradient φ x k - latticeGradient ψ x k := by
  unfold latticeGradient
  ring
theorem eq_windowProjection_add_latticeGradient_add_directionDefect (hL : Odd F.blockSide)
    (Z : LevelForm F 0) (i k : Fin 4) (x : F.Site 0) :
    Z x k = windowProjection Z i x k + latticeGradient (directionGauge Z i) x k +
      directionDefect Z i x k := by
  have h1 := axisMean_sub_sub_latticeGradient hL Z i k x
  have e : directionGauge Z i = fun y => windowGauge (axisMean Z i) i y - axisMeanGauge Z i y := rfl
  rw [e, latticeGradient_sub]
  unfold directionDefect windowProjection
  by_cases hk : k = i
  · subst hk
    rw [if_pos rfl]
    have h2 := latticeGradient_windowGauge_self hL (axisMean Z k) k x
    linarith
  · rw [if_neg hk]
    have h2 := sub_windowForm_sub_latticeGradient_windowGauge hL (axisMean Z i) hk x
    linarith
theorem plaquetteCurl_axisMean (Z : LevelForm F 0) (i : Fin 4) (p : F.Site 0) (k l : Fin 4) :
    plaquetteCurl (axisMean Z i) p k l = (1 / (cellSide F : ℝ)) * ∑ u ∈ Finset.range (cellSide F),
      plaquetteCurl Z (p + axisOffset 0 i (u : ℤ)) k l := by
  have e : ∀ (c : F.Site 0) (m : Fin 4),
      ∑ u ∈ Finset.range (cellSide F), Z (p + c + axisOffset 0 i (u : ℤ)) m =
      ∑ u ∈ Finset.range (cellSide F), Z (p + axisOffset 0 i (u : ℤ) + c) m :=
    fun c m => Finset.sum_congr rfl fun u _ => by rw [add_right_comm]
  unfold plaquetteCurl axisMean
  rw [e, e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring
def IsTemperedWeight (w : F.Site 0 → ℝ) (K : ℝ) : Prop :=
  ∀ (i : Fin 4) (x : F.Site 0) (m : ℤ), |m| ≤ 2 * (cellSide F : ℤ) →
    w x ^ 2 ≤ K * w (x + axisOffset 0 i m) ^ 2
theorem sum_sq_mul_sum_abs_translate_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (i : Fin 4)
    (w G : F.Site 0 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) {ι : Type*} (T : Finset ι) (o : ι → ℤ)
    (hw : ∀ x, ∀ m ∈ T, w x ^ 2 ≤ K * w (x + axisOffset 0 i (o m)) ^ 2) :
    ∑ x ∈ allSites F 0, (w x * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2 ≤
      (T.card : ℝ) ^ 2 * K * ∑ x ∈ allSites F 0, (w x * G x) ^ 2 := by
  have h0 : 0 ≤ F.top := Nat.zero_le _
  have hx : ∀ x, (w x * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2 ≤
      (T.card : ℝ) * K * ∑ m ∈ T, (w (x + axisOffset 0 i (o m)) * G (x + axisOffset 0 i (o m))) ^ 2 := by
    intro x
    have c1 := sq_sum_le_card_mul_sum_sq (s := T) (f := fun m => |G (x + axisOffset 0 i (o m))|)
    rw [mul_pow]
    calc w x ^ 2 * (∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2
        ≤ w x ^ 2 * ((T.card : ℝ) * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))| ^ 2) :=
          mul_le_mul_of_nonneg_left c1 (sq_nonneg _)
      _ = (T.card : ℝ) * ∑ m ∈ T, w x ^ 2 * G (x + axisOffset 0 i (o m)) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [sq_abs]
          ring
      _ ≤ (T.card : ℝ) * ∑ m ∈ T, K * (w (x + axisOffset 0 i (o m)) * G (x + axisOffset 0 i (o m))) ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm => ?_) (by positivity)
          rw [mul_pow, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hw x m hm) (sq_nonneg _)
      _ = _ := by
          rw [← Finset.mul_sum]
          ring
  calc _ ≤ ∑ x ∈ allSites F 0, (T.card : ℝ) * K *
        ∑ m ∈ T, (w (x + axisOffset 0 i (o m)) * G (x + axisOffset 0 i (o m))) ^ 2 :=
        Finset.sum_le_sum fun x _ => hx x
    _ = (T.card : ℝ) * K * ∑ m ∈ T, ∑ x ∈ allSites F 0, (w x * G x) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        exact sum_allSites_add_right hL hs h0 _ (fun x => (w x * G x) ^ 2)
    _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
theorem sum_sq_mul_le_of_abs_le_sum_translate (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (i : Fin 4) (w A G : F.Site 0 → ℝ) (K c : ℝ)
    (hK : 0 ≤ K) (hc : 0 ≤ c) {ι : Type*} (T : Finset ι) (o : ι → ℤ)
    (hw : ∀ x, ∀ m ∈ T, w x ^ 2 ≤ K * w (x + axisOffset 0 i (o m)) ^ 2)
    (hA : ∀ x, |A x| ≤ c * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) :
    ∑ x ∈ allSites F 0, (w x * A x) ^ 2 ≤
      c ^ 2 * ((T.card : ℝ) ^ 2 * K) * ∑ x ∈ allSites F 0, (w x * G x) ^ 2 := by
  have h1 := sum_sq_mul_sum_abs_translate_le hL hs i w G K hK T o hw
  have h2 : ∀ x, (w x * A x) ^ 2 ≤ c ^ 2 * (w x * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2 := by
    intro x
    have : A x ^ 2 ≤ (c * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2 := by
      rw [← sq_abs (A x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2
    calc (w x * A x) ^ 2 = w x ^ 2 * A x ^ 2 := by ring
      _ ≤ w x ^ 2 * (c * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2 :=
          mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = _ := by ring
  calc _ ≤ ∑ x ∈ allSites F 0, c ^ 2 * (w x * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2 :=
        Finset.sum_le_sum fun x _ => h2 x
    _ = c ^ 2 * ∑ x ∈ allSites F 0, (w x * ∑ m ∈ T, |G (x + axisOffset 0 i (o m))|) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ c ^ 2 * ((T.card : ℝ) ^ 2 * K * ∑ x ∈ allSites F 0, (w x * G x) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = _ := by ring
theorem sum_range_shift_le_sum_Icc (f : ℤ → ℝ) (hf : ∀ m, 0 ≤ f m) (n : ℕ) (c A B : ℤ) (hA : A ≤ c)
    (hB : c + n ≤ B + 1) :
    ∑ l ∈ Finset.range n, f ((l : ℤ) + c) ≤ ∑ m ∈ Finset.Icc A B, f m := by
  have e : ∑ l ∈ Finset.range n, f ((l : ℤ) + c) =
      ∑ m ∈ (Finset.range n).image (fun l : ℕ => (l : ℤ) + c), f m := by
    rw [Finset.sum_image]
    intro a _ b _ h
    simpa using h
  rw [e]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hf _)
  intro m hm
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hm
  have := Finset.mem_range.1 hl
  rw [Finset.mem_Icc]
  constructor <;> omega
theorem abs_axisMeanDefect_le (Z : LevelForm F 0) (hL : Odd F.blockSide) (i k : Fin 4) (x : F.Site 0) :
    |axisMeanDefect Z i k x| ≤ 1 * ∑ l ∈ Finset.range (cellSide F),
      |plaquetteCurl Z (x + axisOffset 0 i ((l : ℕ) : ℤ)) i k| := by
  have hN := cellSide_pos hL
  set S := ∑ l ∈ Finset.range (cellSide F), |plaquetteCurl Z (x + axisOffset 0 i ((l : ℕ) : ℤ)) i k| with hS
  have h1 : ∀ u ∈ Finset.range (cellSide F),
      |∑ l ∈ Finset.range u, plaquetteCurl Z (x + axisOffset 0 i (l : ℤ)) i k| ≤ S := by
    intro u hu
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
    intro l hl
    have := Finset.mem_range.1 hu
    have := Finset.mem_range.1 hl
    exact Finset.mem_range.2 (by omega)
  unfold axisMeanDefect
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (cellSide F : ℝ)), one_mul]
  calc _ ≤ (1 / (cellSide F : ℝ)) * ∑ u ∈ Finset.range (cellSide F), S :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h1))
          (by positivity)
    _ = S := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
theorem abs_windowDefect_le (Y : LevelForm F 0) (hL : Odd F.blockSide) (i k : Fin 4) (x : F.Site 0) :
    |windowDefect Y i k x| ≤ 2 * ∑ m ∈ Finset.Icc (-(cellSide F : ℤ)) (cellSide F),
      |plaquetteCurl Y (x + axisOffset 0 i m) i k| := by
  have hlt := windowIndex_lt hL i x
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  set S := ∑ m ∈ Finset.Icc (-(cellSide F : ℤ)) (cellSide F),
    |plaquetteCurl Y (x + axisOffset 0 i m) i k| with hS
  have hfull : ∑ l ∈ Finset.range (cellSide F),
      |plaquetteCurl Y (windowStart i x + axisOffset 0 i (l : ℤ)) i k| ≤ S := by
    have e : ∀ l : ℕ, windowStart i x + axisOffset 0 i (l : ℤ) =
        x + axisOffset 0 i ((l : ℤ) + -(windowIndex i x : ℤ)) := by
      intro l
      unfold windowStart
      rw [add_assoc, ← axisOffset_add, add_comm (-(windowIndex i x : ℤ))]
    simp only [e]
    refine sum_range_shift_le_sum_Icc (fun m => |plaquetteCurl Y (x + axisOffset 0 i m) i k|)
      (fun _ => abs_nonneg _) (cellSide F) (-(windowIndex i x : ℤ)) _ _ ?_ ?_ <;> omega
  have hpart : ∑ l ∈ Finset.range (windowIndex i x),
      |plaquetteCurl Y (windowStart i x + axisOffset 0 i (l : ℤ)) i k| ≤ S := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)) hfull
    intro l hl
    have := Finset.mem_range.1 hl
    exact Finset.mem_range.2 (by omega)
  have hr0 : 0 ≤ (windowIndex i x : ℝ) / cellSide F := by positivity
  have hr1 : (windowIndex i x : ℝ) / cellSide F ≤ 1 := by
    rw [div_le_one hNr]
    exact_mod_cast hlt.le
  unfold windowDefect
  refine (abs_sub _ _).trans ?_
  have a1 := (Finset.abs_sum_le_sum_abs
    (fun l : ℕ => plaquetteCurl Y (windowStart i x + axisOffset 0 i (l : ℤ)) i k)
    (Finset.range (windowIndex i x))).trans hpart
  have a2 := (Finset.abs_sum_le_sum_abs
    (fun l : ℕ => plaquetteCurl Y (windowStart i x + axisOffset 0 i (l : ℤ)) i k)
    (Finset.range (cellSide F))).trans hfull
  rw [abs_mul, abs_of_nonneg hr0]
  nlinarith [mul_le_mul hr1 a2 (abs_nonneg _) zero_le_one]
theorem windowForm_add_unitStep_sub (hL : Odd F.blockSide) (Y : LevelForm F 0) {i l : Fin 4} (hl : l ≠ i)
    (x : F.Site 0) :
    windowForm Y i (x + unitStep 0 i) l - windowForm Y i x l = (1 / (cellSide F : ℝ)) *
      (Y (windowStart i x + axisOffset 0 i (cellSide F : ℤ)) l - Y (windowStart i x) l) := by
  have hN := cellSide_ne_zero hL
  have hlt := windowIndex_lt hL i x
  unfold windowForm
  rw [if_neg hl, if_neg hl]
  rcases Nat.lt_or_ge (windowIndex i x + 1) (cellSide F) with h | h
  · rw [windowStart_add_unitStep hL i x h, windowIndex_add_unitStep hL i x h]
    push_cast
    field_simp
    ring
  · have h1 : windowIndex i x + 1 = cellSide F := by omega
    have hr : (windowIndex i x : ℝ) = (cellSide F : ℝ) - 1 := by
      rw [← h1]
      push_cast
      ring
    rw [windowStart_add_unitStep_of_eq hL i x h1, windowIndex_add_unitStep_of_eq hL i x h1, hr]
    simp only [Nat.cast_zero, zero_div, sub_zero, one_mul, zero_mul, add_zero]
    field_simp
    ring
theorem plaquetteCurl_windowForm_of_ne (hL : Odd F.blockSide) (Y : LevelForm F 0) {i k l : Fin 4}
    (hk : k ≠ i) (hl : l ≠ i) (x : F.Site 0) :
    plaquetteCurl (windowForm Y i) x k l =
      (1 - (windowIndex i x : ℝ) / cellSide F) * plaquetteCurl Y (windowStart i x) k l +
      ((windowIndex i x : ℝ) / cellSide F) *
        plaquetteCurl Y (windowStart i x + axisOffset 0 i (cellSide F : ℤ)) k l := by
  have ek : x + unitStep 0 k = x + axisOffset 0 k 1 := rfl
  have el : x + unitStep 0 l = x + axisOffset 0 l 1 := rfl
  unfold plaquetteCurl windowForm
  simp only [if_neg hk, if_neg hl]
  rw [ek, el, windowIndex_add_axisOffset_of_ne hL hk, windowIndex_add_axisOffset_of_ne hL hl,
    windowStart_add_axisOffset_of_ne hL hk, windowStart_add_axisOffset_of_ne hL hl,
    axisOffset_one, axisOffset_one, add_right_comm (windowStart i x) (unitStep 0 k),
    add_right_comm (windowStart i x) (unitStep 0 l)]
  ring
theorem plaquetteCurl_windowForm_self (hL : Odd F.blockSide) (Y : LevelForm F 0) {i l : Fin 4}
    (hl : l ≠ i) (x : F.Site 0) :
    plaquetteCurl (windowForm Y i) x i l = (1 / (cellSide F : ℝ)) * ∑ m ∈ Finset.range (cellSide F),
      plaquetteCurl Y (windowStart i x + axisOffset 0 i (m : ℤ)) i l := by
  have step := windowForm_add_unitStep_sub hL Y hl x
  have el : x + unitStep 0 l = x + axisOffset 0 l 1 := rfl
  rw [← sub_lineSum_eq_sum_plaquetteCurl Y (windowStart i x) i l (cellSide F)]
  have e1 : windowForm Y i (x + unitStep 0 l) i =
      (1 / (cellSide F : ℝ)) * lineSum Y (windowStart i x + unitStep 0 l) i (cellSide F) := by
    unfold windowForm
    rw [if_pos rfl, el, windowStart_add_axisOffset_of_ne hL hl, axisOffset_one]
  have e2 : windowForm Y i x i =
      (1 / (cellSide F : ℝ)) * lineSum Y (windowStart i x) i (cellSide F) := by
    unfold windowForm
    rw [if_pos rfl]
  show windowForm Y i x i + windowForm Y i (x + unitStep 0 i) l - windowForm Y i (x + unitStep 0 l) i -
    windowForm Y i x l = _
  rw [e1, e2]
  linear_combination step
theorem abs_plaquetteCurl_axisMean_le (Z : LevelForm F 0) (i k l : Fin 4) (hL : Odd F.blockSide)
    (x : F.Site 0) (d : ℤ)
    (h1 : -(cellSide F : ℤ) ≤ d) (h2 : d ≤ (cellSide F : ℤ) + 1) :
    |plaquetteCurl (axisMean Z i) (x + axisOffset 0 i d) k l| ≤ (1 / (cellSide F : ℝ)) *
      ∑ m ∈ Finset.Icc (-(cellSide F : ℤ)) (2 * (cellSide F : ℤ)),
        |plaquetteCurl Z (x + axisOffset 0 i m) k l| := by
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  rw [plaquetteCurl_axisMean, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (cellSide F : ℝ))]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (by positivity)
  have e : ∀ u : ℕ, x + axisOffset 0 i d + axisOffset 0 i (u : ℤ) = x + axisOffset 0 i ((u : ℤ) + d) := by
    intro u
    rw [add_assoc, ← axisOffset_add, add_comm d]
  simp only [e]
  exact sum_range_shift_le_sum_Icc (fun m => |plaquetteCurl Z (x + axisOffset 0 i m) k l|)
    (fun _ => abs_nonneg _) (cellSide F) d _ _ h1 (by omega)
theorem windowStart_add_axisOffset (i : Fin 4) (x : F.Site 0) (m : ℤ) :
    windowStart i x + axisOffset 0 i m = x + axisOffset 0 i (m + -(windowIndex i x : ℤ)) := by
  unfold windowStart
  rw [add_assoc, ← axisOffset_add, add_comm (-(windowIndex i x : ℤ))]
theorem abs_plaquetteCurl_windowProjection_self_le (Z : LevelForm F 0) (hL : Odd F.blockSide) {i l : Fin 4}
    (hl : l ≠ i) (x : F.Site 0) :
    |plaquetteCurl (windowProjection Z i) x i l| ≤ (1 / (cellSide F : ℝ)) *
      ∑ m ∈ Finset.Icc (-(cellSide F : ℤ)) (2 * (cellSide F : ℤ)),
        |plaquetteCurl Z (x + axisOffset 0 i m) i l| := by
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  have hlt := windowIndex_lt hL i x
  set S := (1 / (cellSide F : ℝ)) *
      ∑ m ∈ Finset.Icc (-(cellSide F : ℤ)) (2 * (cellSide F : ℤ)),
        |plaquetteCurl Z (x + axisOffset 0 i m) i l| with hS
  unfold windowProjection
  rw [plaquetteCurl_windowForm_self hL _ hl, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (cellSide F : ℝ))]
  have h1 : ∀ m ∈ Finset.range (cellSide F),
      |plaquetteCurl (axisMean Z i) (windowStart i x + axisOffset 0 i (m : ℤ)) i l| ≤ S := by
    intro m hm
    have := Finset.mem_range.1 hm
    rw [windowStart_add_axisOffset]
    exact abs_plaquetteCurl_axisMean_le Z i i l hL x _ (by omega) (by omega)
  calc _ ≤ (1 / (cellSide F : ℝ)) * ∑ m ∈ Finset.range (cellSide F), S :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h1))
          (by positivity)
    _ = S := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
theorem abs_plaquetteCurl_windowProjection_le (Z : LevelForm F 0) (hL : Odd F.blockSide) (i k l : Fin 4)
    (x : F.Site 0) :
    |plaquetteCurl (windowProjection Z i) x k l| ≤ (1 / (cellSide F : ℝ)) *
      ∑ m ∈ Finset.Icc (-(cellSide F : ℤ)) (2 * (cellSide F : ℤ)),
        |plaquetteCurl Z (x + axisOffset 0 i m) k l| := by
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  have hlt := windowIndex_lt hL i x
  by_cases hkl : k = l
  · subst hkl
    rw [plaquetteCurl_self, abs_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  by_cases hk : k = i
  · subst hk
    exact abs_plaquetteCurl_windowProjection_self_le Z hL (Ne.symm hkl) x
  by_cases hl : l = i
  · subst hl
    have := abs_plaquetteCurl_windowProjection_self_le Z hL hk x
    rw [plaquetteCurl_swap, abs_neg]
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [plaquetteCurl_swap, abs_neg]
  · set S := (1 / (cellSide F : ℝ)) *
      ∑ m ∈ Finset.Icc (-(cellSide F : ℤ)) (2 * (cellSide F : ℤ)),
        |plaquetteCurl Z (x + axisOffset 0 i m) k l| with hS
    unfold windowProjection
    rw [plaquetteCurl_windowForm_of_ne hL _ hk hl]
    have a1 : |plaquetteCurl (axisMean Z i) (windowStart i x) k l| ≤ S := by
      have e := windowStart_add_axisOffset i x 0
      rw [axisOffset_zero, add_zero] at e
      rw [e]
      exact abs_plaquetteCurl_axisMean_le Z i k l hL x _ (by omega) (by omega)
    have a2 : |plaquetteCurl (axisMean Z i) (windowStart i x + axisOffset 0 i (cellSide F : ℤ)) k l| ≤ S := by
      rw [windowStart_add_axisOffset]
      exact abs_plaquetteCurl_axisMean_le Z i k l hL x _ (by omega) (by omega)
    have hr0 : 0 ≤ (windowIndex i x : ℝ) / cellSide F := by positivity
    have hr1 : (windowIndex i x : ℝ) / cellSide F ≤ 1 := by
      rw [div_le_one hNr]
      exact_mod_cast hlt.le
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hr0,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (windowIndex i x : ℝ) / cellSide F)]
    nlinarith [mul_le_mul_of_nonneg_left a1
        (by linarith : (0 : ℝ) ≤ 1 - (windowIndex i x : ℝ) / cellSide F),
      mul_le_mul_of_nonneg_left a2 hr0]
theorem card_Icc_window_le (hL : Odd F.blockSide) :
    ((Finset.Icc (-(cellSide F : ℤ)) (2 * (cellSide F : ℤ))).card : ℝ) ≤ 4 * (cellSide F : ℝ) := by
  have hN := cellSide_pos hL
  have h1 : (Finset.Icc (-(cellSide F : ℤ)) (2 * (cellSide F : ℤ))).card ≤ 4 * cellSide F := by
    rw [Int.card_Icc]
    omega
  exact_mod_cast h1
theorem weightedCurlNormSq_eq_sum_orientedPlanes {j : ℕ} (w : F.Site j → ℝ) (Z : LevelForm F j) :
    weightedCurlNormSq w Z =
      ∑ e ∈ orientedPlanes, ∑ x ∈ allSites F j, (w x * plaquetteCurl Z x e.1 e.2) ^ 2 := by
  unfold weightedCurlNormSq
  exact Finset.sum_comm
theorem sum_sq_plaquetteCurl_le_weightedCurlNormSq {j : ℕ} (w : F.Site j → ℝ) (Z : LevelForm F j)
    (k l : Fin 4) :
    ∑ x ∈ allSites F j, (w x * plaquetteCurl Z x k l) ^ 2 ≤ weightedCurlNormSq w Z :=
  Finset.sum_le_sum fun x _ => sq_plaquetteCurl_le_sum Z x (w x) k l
theorem weightedCurlNormSq_windowProjection_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {w : F.Site 0 → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hw : IsTemperedWeight w K) (Z : LevelForm F 0) (i : Fin 4) :
    weightedCurlNormSq w (windowProjection Z i) ≤ 16 * K * weightedCurlNormSq w Z := by
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  rw [weightedCurlNormSq_eq_sum_orientedPlanes, weightedCurlNormSq_eq_sum_orientedPlanes, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  have b := sum_sq_mul_le_of_abs_le_sum_translate hL hs i w
    (fun x => plaquetteCurl (windowProjection Z i) x e.1 e.2) (fun x => plaquetteCurl Z x e.1 e.2)
    K (1 / (cellSide F : ℝ)) hK (by positivity)
    (Finset.Icc (-(cellSide F : ℤ)) (2 * (cellSide F : ℤ))) id
    (fun x m hm => hw i x m (by
      have := Finset.mem_Icc.1 hm
      rw [abs_le]
      have := cellSide_pos hL
      constructor <;> omega))
    (fun x => abs_plaquetteCurl_windowProjection_le Z hL i e.1 e.2 x)
  refine b.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have c := card_Icc_window_le (F := F) hL
  have c0 : (0 : ℝ) ≤ ((Finset.Icc (-(cellSide F : ℤ)) (2 * (cellSide F : ℤ))).card : ℝ) := by positivity
  have c2 : ((Finset.Icc (-(cellSide F : ℤ)) (2 * (cellSide F : ℤ))).card : ℝ) ^ 2 ≤
      (4 * (cellSide F : ℝ)) ^ 2 := pow_le_pow_left₀ c0 c 2
  calc _ ≤ (1 / (cellSide F : ℝ)) ^ 2 * ((4 * (cellSide F : ℝ)) ^ 2 * K) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_right c2 hK
    _ = _ := by
        field_simp
        ring
theorem weightedNormSq_directionDefect_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {w : F.Site 0 → ℝ} {K : ℝ} (hK : 1 ≤ K)
    (hw : IsTemperedWeight w K) (Z : LevelForm F 0) (i : Fin 4) :
    weightedNormSq w (directionDefect Z i) ≤
      300 * (cellSide F : ℝ) ^ 2 * K ^ 2 * weightedCurlNormSq w Z := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hwc := weightedCurlNormSq_nonneg w Z
  have hNi := cellSide_pos (F := F) hL
  have hmem : ∀ (x : F.Site 0) (m : ℕ), m ∈ Finset.range (cellSide F) →
      w x ^ 2 ≤ K * w (x + axisOffset 0 i ((m : ℕ) : ℤ)) ^ 2 := fun x m hm => hw i x _ (by
    have := Finset.mem_range.1 hm
    rw [abs_le]
    constructor <;> omega)
  have hmean : ∀ k, ∑ x ∈ allSites F 0, (w x * plaquetteCurl (axisMean Z i) x i k) ^ 2 ≤
      K * weightedCurlNormSq w Z := by
    intro k
    have b := sum_sq_mul_le_of_abs_le_sum_translate hL hs i w
      (fun x => plaquetteCurl (axisMean Z i) x i k) (fun x => plaquetteCurl Z x i k)
      K (1 / (cellSide F : ℝ)) hK0 (by positivity) (Finset.range (cellSide F)) (fun m => (m : ℤ))
      hmem (fun x => by
        rw [plaquetteCurl_axisMean, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / (cellSide F : ℝ))]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity))
    have e : (1 / (cellSide F : ℝ)) ^ 2 * (((Finset.range (cellSide F)).card : ℝ) ^ 2 * K) = K := by
      rw [Finset.card_range]
      field_simp
    rw [e] at b
    exact b.trans (mul_le_mul_of_nonneg_left (sum_sq_plaquetteCurl_le_weightedCurlNormSq w Z i k) hK0)
  have hmeanDefect : ∀ k, ∑ x ∈ allSites F 0, (w x * axisMeanDefect Z i k x) ^ 2 ≤
      (cellSide F : ℝ) ^ 2 * K * weightedCurlNormSq w Z := by
    intro k
    have b := sum_sq_mul_le_of_abs_le_sum_translate hL hs i w (fun x => axisMeanDefect Z i k x)
      (fun x => plaquetteCurl Z x i k)
      K 1 hK0 zero_le_one (Finset.range (cellSide F)) (fun m => (m : ℤ))
      hmem (fun x => abs_axisMeanDefect_le Z hL i k x)
    rw [Finset.card_range, one_pow, one_mul] at b
    exact b.trans (mul_le_mul_of_nonneg_left (sum_sq_plaquetteCurl_le_weightedCurlNormSq w Z i k)
      (by positivity))
  have hwin : ∀ k, ∑ x ∈ allSites F 0, (w x * windowDefect (axisMean Z i) i k x) ^ 2 ≤
      36 * (cellSide F : ℝ) ^ 2 * K ^ 2 * weightedCurlNormSq w Z := by
    intro k
    have b := sum_sq_mul_le_of_abs_le_sum_translate hL hs i w
      (fun x => windowDefect (axisMean Z i) i k x)
      (fun x => plaquetteCurl (axisMean Z i) x i k) K 2 hK0 (by norm_num)
      (Finset.Icc (-(cellSide F : ℤ)) (cellSide F)) id
      (fun x m hm => hw i x m (by
        have := Finset.mem_Icc.1 hm
        rw [abs_le]
        constructor <;> omega))
      (fun x => abs_windowDefect_le _ hL i k x)
    have c : ((Finset.Icc (-(cellSide F : ℤ)) (cellSide F)).card : ℝ) ≤ 3 * (cellSide F : ℝ) := by
      have h1 : (Finset.Icc (-(cellSide F : ℤ)) (cellSide F)).card ≤ 3 * cellSide F := by
        rw [Int.card_Icc]
        omega
      exact_mod_cast h1
    have c2 : ((Finset.Icc (-(cellSide F : ℤ)) (cellSide F)).card : ℝ) ^ 2 ≤
        (3 * (cellSide F : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) c 2
    have s0 := hmean k
    have t0 : 0 ≤ ∑ x ∈ allSites F 0, (w x * plaquetteCurl (axisMean Z i) x i k) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc _ ≤ (2 : ℝ) ^ 2 * (((Finset.Icc (-(cellSide F : ℤ)) (cellSide F)).card : ℝ) ^ 2 * K) *
          ∑ x ∈ allSites F 0, (w x * plaquetteCurl (axisMean Z i) x i k) ^ 2 := b
      _ ≤ (2 : ℝ) ^ 2 * ((3 * (cellSide F : ℝ)) ^ 2 * K) * (K * weightedCurlNormSq w Z) := by
          refine mul_le_mul ?_ s0 t0 (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right c2 hK0) (by positivity)
      _ = _ := by ring
  have hk : ∀ k, ∑ x ∈ allSites F 0, (w x * directionDefect Z i x k) ^ 2 ≤
      75 * (cellSide F : ℝ) ^ 2 * K ^ 2 * weightedCurlNormSq w Z := by
    intro k
    have t1 : ∀ x, (w x * directionDefect Z i x k) ^ 2 ≤
        2 * (w x * (if k = i then 0 else windowDefect (axisMean Z i) i k x)) ^ 2 +
          2 * (w x * axisMeanDefect Z i k x) ^ 2 := by
      intro x
      unfold directionDefect
      nlinarith [sq_nonneg (w x * (if k = i then 0 else windowDefect (axisMean Z i) i k x) +
        w x * axisMeanDefect Z i k x)]
    have t2 : ∑ x ∈ allSites F 0,
        (w x * (if k = i then 0 else windowDefect (axisMean Z i) i k x)) ^ 2 ≤
        36 * (cellSide F : ℝ) ^ 2 * K ^ 2 * weightedCurlNormSq w Z := by
      by_cases hki : k = i
      · simp only [hki, if_true, mul_zero]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
        positivity
      · simp only [if_neg hki]
        exact hwin k
    have t3 := hmeanDefect k
    have hKK : K ≤ K ^ 2 := by nlinarith
    have hN2 : 0 ≤ (cellSide F : ℝ) ^ 2 * weightedCurlNormSq w Z := by positivity
    calc _ ≤ ∑ x ∈ allSites F 0,
          (2 * (w x * (if k = i then 0 else windowDefect (axisMean Z i) i k x)) ^ 2 +
          2 * (w x * axisMeanDefect Z i k x) ^ 2) := Finset.sum_le_sum fun x _ => t1 x
      _ = 2 * ∑ x ∈ allSites F 0,
            (w x * (if k = i then 0 else windowDefect (axisMean Z i) i k x)) ^ 2 +
          2 * ∑ x ∈ allSites F 0, (w x * axisMeanDefect Z i k x) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * (36 * (cellSide F : ℝ) ^ 2 * K ^ 2 * weightedCurlNormSq w Z) +
          2 * ((cellSide F : ℝ) ^ 2 * K * weightedCurlNormSq w Z) := by
          linarith
      _ ≤ _ := by
          nlinarith [mul_le_mul_of_nonneg_right hKK hN2]
  unfold weightedNormSq
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _k : Fin 4, 75 * (cellSide F : ℝ) ^ 2 * K ^ 2 * weightedCurlNormSq w Z :=
        Finset.sum_le_sum fun k _ => hk k
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
end ColdStepAtMirrorFrames
end YangMills.Construction
end
