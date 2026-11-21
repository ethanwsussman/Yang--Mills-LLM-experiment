import YangMills.Construction.ColdStepAtMirrorFrames.FormOfTheMeansOfTheCellsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def windowRamp (N r : ℕ) : ℝ := (3 * (r : ℝ) ^ 2 - (2 * (N : ℝ) - 1) * r) / ((N : ℝ) * ((N : ℝ) + 1))
theorem windowRamp_zero (N : ℕ) : windowRamp N 0 = 0 := by
  simp [windowRamp]
theorem windowRamp_self {N : ℕ} (hN : 0 < N) : windowRamp N N = 1 := by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  unfold windowRamp
  field_simp
  ring
theorem sum_range_windowRamp_numerator (N n : ℕ) :
    ∑ r ∈ Finset.range n, (3 * (r : ℝ) ^ 2 - (2 * (N : ℝ) - 1) * r) =
    (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - N) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring
theorem sum_range_windowRamp (N : ℕ) : ∑ r ∈ Finset.range N, windowRamp N r = 0 := by
  unfold windowRamp
  rw [← Finset.sum_div, sum_range_windowRamp_numerator]
  simp
theorem abs_windowRamp_succ_sub_le {N r : ℕ} (hr : r < N) :
    |windowRamp N (r + 1) - windowRamp N r| ≤ 4 / (N : ℝ) := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hrN : (r : ℝ) + 1 ≤ N := by exact_mod_cast hr
  have e : windowRamp N (r + 1) - windowRamp N r =
      (6 * (r : ℝ) + 4 - 2 * N) / ((N : ℝ) * ((N : ℝ) + 1)) := by
    unfold windowRamp
    push_cast
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) * ((N : ℝ) + 1)),
    div_le_div_iff₀ (by positivity) hN]
  have : |6 * (r : ℝ) + 4 - 2 * N| ≤ 4 * ((N : ℝ) + 1) := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith
theorem abs_windowRamp_le {N r : ℕ} (hr : r ≤ N) (hN : 0 < N) : |windowRamp N r| ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrN : (r : ℝ) ≤ N := by exact_mod_cast hr
  unfold windowRamp
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) * ((N : ℝ) + 1)),
    div_le_one (by positivity), abs_le]
  constructor
  · nlinarith [sq_nonneg (6 * (r : ℝ) - (2 * (N : ℝ) - 1))]
  · nlinarith
def axisInterpolate (i : Fin 4) (g : F.Site 0 → ℝ) (x : F.Site 0) : ℝ :=
  g x + windowRamp (cellSide F) (windowIndex i x) * (g (x + axisOffset 0 i (cellSide F : ℤ)) - g x)
def IsWindowConstant (i : Fin 4) (g : F.Site 0 → ℝ) : Prop :=
  ∀ (p : F.Site 0) (u : ℕ), windowIndex i p + u < cellSide F → g (p + axisOffset 0 i (u : ℤ)) = g p
theorem windowIndex_add_axisOffset_cellSide (hL : Odd F.blockSide) (i : Fin 4) (x : F.Site 0) :
    windowIndex i (x + axisOffset 0 i (cellSide F : ℤ)) = windowIndex i x := by
  have e := natCast_windowIndex_add_axisOffset hL i x (cellSide F : ℤ)
  have hlt : (windowIndex i x : ℤ) < (cellSide F : ℤ) := by exact_mod_cast windowIndex_lt hL i x
  have e2 : ((windowIndex i x : ℤ) + (cellSide F : ℤ)) % (cellSide F : ℤ) = (windowIndex i x : ℤ) := by
    have : (windowIndex i x : ℤ) + (cellSide F : ℤ) = (windowIndex i x : ℤ) + 1 * (cellSide F : ℤ) := by
      ring
    rw [this, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity) hlt]
  rw [e2] at e
  exact_mod_cast e
theorem windowIndex_add_axisOffset_natCast (hL : Odd F.blockSide) (i : Fin 4) (p : F.Site 0) (u : ℕ)
    (h : windowIndex i p + u < cellSide F) :
    windowIndex i (p + axisOffset 0 i (u : ℤ)) = windowIndex i p + u := by
  have e := natCast_windowIndex_add_axisOffset hL i p (u : ℤ)
  have h' : (windowIndex i p : ℤ) + u < (cellSide F : ℤ) := by exact_mod_cast h
  rw [Int.emod_eq_of_lt (by positivity) h'] at e
  exact_mod_cast e
theorem axisInterpolate_sub (i : Fin 4) (g g' : F.Site 0 → ℝ) :
    axisInterpolate i (fun x => g x - g' x) = fun x => axisInterpolate i g x - axisInterpolate i g' x := by
  funext x
  unfold axisInterpolate
  ring
theorem axisInterpolate_translate (hL : Odd F.blockSide) {i k : Fin 4} (hk : k ≠ i) (g : F.Site 0 → ℝ)
    (u : ℤ) (x : F.Site 0) :
    axisInterpolate i (fun y => g (y + axisOffset 0 k u)) x = axisInterpolate i g (x + axisOffset 0 k u) := by
  unfold axisInterpolate
  beta_reduce
  rw [windowIndex_add_axisOffset_of_ne hL hk, add_right_comm x (axisOffset 0 i _)]
theorem isWindowConstant_axisInterpolate (hL : Odd F.blockSide) {i j : Fin 4} (hij : j ≠ i)
    (g : F.Site 0 → ℝ) (hg : IsWindowConstant i g) : IsWindowConstant i (axisInterpolate j g) := by
  intro p u h
  unfold axisInterpolate
  rw [windowIndex_add_axisOffset_of_ne hL hij.symm, hg p u h, add_right_comm p (axisOffset 0 i _),
    hg (p + axisOffset 0 j (cellSide F : ℤ)) u (by rw [windowIndex_add_axisOffset_of_ne hL hij]; exact h)]
theorem latticeGradient_axisInterpolate_same (hL : Odd F.blockSide) (i : Fin 4) (g : F.Site 0 → ℝ)
    (hg : IsWindowConstant i g) (x : F.Site 0) :
    latticeGradient (axisInterpolate i g) x i =
      (windowRamp (cellSide F) (windowIndex i x + 1) - windowRamp (cellSide F) (windowIndex i x)) *
      (g (x + axisOffset 0 i (cellSide F : ℤ)) - g x) := by
  have hlt := windowIndex_lt hL i x
  unfold latticeGradient axisInterpolate
  rcases Nat.lt_or_ge (windowIndex i x + 1) (cellSide F) with h | h
  · have h1 : g (x + axisOffset 0 i (1 : ℤ)) = g x := by
      have := hg x 1 (by simpa using h)
      simpa using this
    have h2 : g (x + axisOffset 0 i (cellSide F : ℤ) + axisOffset 0 i (1 : ℤ)) =
        g (x + axisOffset 0 i (cellSide F : ℤ)) := by
      have := hg (x + axisOffset 0 i (cellSide F : ℤ)) 1
        (by rw [windowIndex_add_axisOffset_cellSide hL]; simpa using h)
      simpa using this
    rw [windowIndex_add_unitStep hL i x h, ← axisOffset_one, add_right_comm x (axisOffset 0 i 1), h1, h2]
    ring
  · have h1 : windowIndex i x + 1 = cellSide F := by omega
    have h2 : g (x + axisOffset 0 i (cellSide F : ℤ)) = g (x + unitStep 0 i) := by
      have hw := windowIndex_add_unitStep_of_eq hL i x h1
      have := hg (x + unitStep 0 i) (cellSide F - 1) (by
        rw [hw]
        have := cellSide_pos (F := F) hL
        omega)
      rw [← this, add_assoc, ← axisOffset_one, ← axisOffset_add]
      congr 3
      have hp := cellSide_pos (F := F) hL
      omega
    rw [windowIndex_add_unitStep_of_eq hL i x h1, windowRamp_zero, h1, windowRamp_self (cellSide_pos hL), ← h2]
    ring
theorem latticeGradient_axisInterpolate_of_ne (hL : Odd F.blockSide) {i k : Fin 4} (hk : k ≠ i)
    (g : F.Site 0 → ℝ) (x : F.Site 0) :
    latticeGradient (axisInterpolate i g) x k = axisInterpolate i (fun y => latticeGradient g y k) x := by
  have e : x + unitStep 0 k = x + axisOffset 0 k 1 := rfl
  unfold latticeGradient axisInterpolate
  beta_reduce
  rw [e, windowIndex_add_axisOffset_of_ne hL hk, axisOffset_one, add_right_comm x (unitStep 0 k)]
  ring
theorem isWindowConstant_comp_enclosingCell (hL : Odd F.blockSide) (f : F.Cell → ℝ) (i : Fin 4) :
    IsWindowConstant i (fun x => f (enclosingCell x)) := by
  intro p u h
  have hp : (cellSide F : ℤ) ≠ 0 := by
    have := cellSide_pos (F := F) hL
    omega
  have e : enclosingCell (p + axisOffset 0 i (u : ℤ)) = enclosingCell p := by
    conv_rhs => rw [← siteOfCoords_siteCoords p]
    rw [add_axisOffset_eq_siteOfCoords, enclosingCell_siteOfCoords hL, enclosingCell_siteOfCoords hL]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk
      simp only [Pi.add_apply, Pi.single_eq_same]
      have e1 := Int.emod_add_mul_ediv (siteCoords p k + cellHalfSide F) (cellSide F : ℤ)
      have e2 := natCast_windowIndex hL k p
      have e3 : siteCoords p k + (u : ℤ) + cellHalfSide F =
          ((windowIndex k p : ℤ) + u) + (cellSide F : ℤ) * ((siteCoords p k + cellHalfSide F) / (cellSide F : ℤ)) := by
        rw [e2]
        linear_combination -e1
      rw [e3, Int.add_mul_ediv_left _ _ hp]
      have : ((windowIndex k p : ℤ) + u) / (cellSide F : ℤ) = 0 :=
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast h)
      rw [this, zero_add]
    · simp [Pi.single_eq_of_ne hk]
  simp only [e]
theorem enclosingCell_add_axisOffset_cellSide (hL : Odd F.blockSide) (x : F.Site 0) (i : Fin 4) :
    enclosingCell (x + axisOffset 0 i (cellSide F : ℤ)) = enclosingCell x + unitStep F.top i := by
  have hp : (cellSide F : ℤ) ≠ 0 := by
    have := cellSide_pos (F := F) hL
    omega
  conv_rhs => rw [← siteOfCoords_siteCoords x]
  rw [add_axisOffset_eq_siteOfCoords, enclosingCell_siteOfCoords hL, enclosingCell_siteOfCoords hL]
  unfold unitStep
  rw [← siteOfCoords_add]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.add_apply, Pi.single_eq_same]
    have e : siteCoords x k + (cellSide F : ℤ) + cellHalfSide F =
        (siteCoords x k + cellHalfSide F) + 1 * (cellSide F : ℤ) := by ring
    rw [e, Int.add_mul_ediv_right _ _ hp]
  · simp [Pi.single_eq_of_ne hk]
theorem forwardAxisAverage_axisInterpolate_of_windowIndex_eq_zero (hL : Odd F.blockSide) (i : Fin 4)
    (g : F.Site 0 → ℝ) (hg : IsWindowConstant i g) (p : F.Site 0) (hp : windowIndex i p = 0) :
    forwardAxisAverage i (axisInterpolate i g) p = g p := by
  have hN := cellSide_ne_zero (F := F) hL
  have e : ∀ u ∈ Finset.range (cellSide F), axisInterpolate i g (p + axisOffset 0 i (u : ℤ)) =
      g p + windowRamp (cellSide F) u * (g (p + axisOffset 0 i (cellSide F : ℤ)) - g p) := by
    intro u hu
    have hu' := Finset.mem_range.1 hu
    unfold axisInterpolate
    rw [windowIndex_add_axisOffset_natCast hL i p u (by omega), hp, zero_add, hg p u (by omega),
      add_right_comm p (axisOffset 0 i _),
      hg (p + axisOffset 0 i (cellSide F : ℤ)) u (by rw [windowIndex_add_axisOffset_cellSide hL]; omega)]
  unfold forwardAxisAverage
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.sum_mul, sum_range_windowRamp]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, zero_mul, add_zero]
  field_simp
def cellSpread (f : F.Cell → ℝ) : F.Site 0 → ℝ :=
  axisInterpolate 0 (axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 (fun x => f (enclosingCell x)))))
theorem windowIndex_cellCorner (hL : Odd F.blockSide) (i : Fin 4) (y : F.Cell) :
    windowIndex i (cellCorner y) = 0 := by
  have : (windowIndex i (cellCorner y) : ℤ) = 0 := by
    conv_lhs => rw [← siteOfCoords_siteCoords y, cellCorner_siteOfCoords, natCast_windowIndex_siteOfCoords hL]
    simp
  exact_mod_cast this
theorem enclosingCell_cellCorner (hL : Odd F.blockSide) (y : F.Cell) : enclosingCell (cellCorner y) = y := by
  obtain ⟨k, hk⟩ := hL.pow (n := F.top)
  have hk' : cellSide F = 2 * k + 1 := hk
  unfold cellCorner
  refine enclosingCell_refineSite_add hL y _ ?_
  rw [mem_centredCube_iff hk', cellHalfSide_eq hk']
  intro i
  simp
theorem cellAverage_eq_forwardCellAverage (hL : Odd F.blockSide) (φ : F.Site 0 → ℝ) (y : F.Cell) :
    cellAverage φ y = forwardCellAverage φ (cellCorner y) := by
  rw [forwardCellAverage_cellCorner hL]
  unfold cellAverage
  push_cast
  rfl
theorem forwardAxisAverage_congr_of_invariant (j : Fin 4) (P : F.Site 0 → Prop)
    (hP : ∀ q (u : ℕ), P q → P (q + axisOffset 0 j (u : ℤ)))
    (H G : F.Site 0 → ℝ) (h : ∀ q, P q → H q = G q) (q : F.Site 0) (hq : P q) :
    forwardAxisAverage j H q = forwardAxisAverage j G q := by
  unfold forwardAxisAverage
  congr 1
  exact Finset.sum_congr rfl fun u _ => h _ (hP q u hq)
theorem cellAverage_cellSpread (hL : Odd F.blockSide) (f : F.Cell → ℝ) (y : F.Cell) :
    cellAverage (cellSpread f) y = f y := by
  have n01 : (0 : Fin 4) ≠ 1 := by decide
  have n02 : (0 : Fin 4) ≠ 2 := by decide
  have n03 : (0 : Fin 4) ≠ 3 := by decide
  have n12 : (1 : Fin 4) ≠ 2 := by decide
  have n13 : (1 : Fin 4) ≠ 3 := by decide
  have n23 : (2 : Fin 4) ≠ 3 := by decide
  set m : F.Site 0 → ℝ := fun x => f (enclosingCell x) with hm
  have c3 := isWindowConstant_comp_enclosingCell hL f 3
  have c2 : IsWindowConstant 2 (axisInterpolate 3 m) :=
    isWindowConstant_axisInterpolate hL n23.symm m (isWindowConstant_comp_enclosingCell hL f 2)
  have c1 : IsWindowConstant 1 (axisInterpolate 2 (axisInterpolate 3 m)) :=
    isWindowConstant_axisInterpolate hL n12.symm _
      (isWindowConstant_axisInterpolate hL n13.symm m (isWindowConstant_comp_enclosingCell hL f 1))
  have c0 : IsWindowConstant 0 (axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 m))) :=
    isWindowConstant_axisInterpolate hL n01.symm _ (isWindowConstant_axisInterpolate hL n02.symm _
      (isWindowConstant_axisInterpolate hL n03.symm m (isWindowConstant_comp_enclosingCell hL f 0)))
  have E0 : ∀ q, windowIndex 0 q = 0 →
      forwardAxisAverage 0 (cellSpread f) q = axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 m)) q :=
    fun q hq => forwardAxisAverage_axisInterpolate_of_windowIndex_eq_zero hL 0 _ c0 q hq
  have E1 : ∀ q, (windowIndex 0 q = 0 ∧ windowIndex 1 q = 0) →
      forwardAxisAverage 1 (forwardAxisAverage 0 (cellSpread f)) q = axisInterpolate 2 (axisInterpolate 3 m) q := by
    rintro q ⟨h0, h1⟩
    rw [forwardAxisAverage_congr_of_invariant 1 (fun q => windowIndex 0 q = 0) (fun q u hq => by
      show windowIndex 0 _ = 0
      rw [windowIndex_add_axisOffset_of_ne hL n01.symm]
      exact hq) _ _ E0 q h0]
    exact forwardAxisAverage_axisInterpolate_of_windowIndex_eq_zero hL 1 _ c1 q h1
  have E2 : ∀ q, ((windowIndex 0 q = 0 ∧ windowIndex 1 q = 0) ∧ windowIndex 2 q = 0) →
      forwardAxisAverage 2 (forwardAxisAverage 1 (forwardAxisAverage 0 (cellSpread f))) q =
        axisInterpolate 3 m q := by
    rintro q ⟨h01, h2⟩
    rw [forwardAxisAverage_congr_of_invariant 2 (fun q => windowIndex 0 q = 0 ∧ windowIndex 1 q = 0)
      (fun q u hq => by
        show windowIndex 0 _ = 0 ∧ windowIndex 1 _ = 0
        rw [windowIndex_add_axisOffset_of_ne hL n02.symm, windowIndex_add_axisOffset_of_ne hL n12.symm]
        exact hq) _ _ E1 q h01]
    exact forwardAxisAverage_axisInterpolate_of_windowIndex_eq_zero hL 2 _ c2 q h2
  have E3 : ∀ q, (((windowIndex 0 q = 0 ∧ windowIndex 1 q = 0) ∧ windowIndex 2 q = 0) ∧ windowIndex 3 q = 0) →
      forwardAxisAverage 3 (forwardAxisAverage 2 (forwardAxisAverage 1 (forwardAxisAverage 0 (cellSpread f)))) q =
        m q := by
    rintro q ⟨h012, h3⟩
    rw [forwardAxisAverage_congr_of_invariant 3
      (fun q => (windowIndex 0 q = 0 ∧ windowIndex 1 q = 0) ∧ windowIndex 2 q = 0) (fun q u hq => by
        show (windowIndex 0 _ = 0 ∧ windowIndex 1 _ = 0) ∧ windowIndex 2 _ = 0
        rw [windowIndex_add_axisOffset_of_ne hL n03.symm, windowIndex_add_axisOffset_of_ne hL n13.symm,
          windowIndex_add_axisOffset_of_ne hL n23.symm]
        exact hq) _ _ E2 q h012]
    exact forwardAxisAverage_axisInterpolate_of_windowIndex_eq_zero hL 3 _ c3 q h3
  have e : forwardCellAverage (cellSpread f) =
      forwardAxisAverage 3 (forwardAxisAverage 2 (forwardAxisAverage 1 (forwardAxisAverage 0 (cellSpread f)))) := by
    unfold forwardCellAverage
    rw [forwardAxisAverage_comm 2 3, forwardAxisAverage_comm 1 3, forwardAxisAverage_comm 0 3,
      forwardAxisAverage_comm 1 2, forwardAxisAverage_comm 0 2, forwardAxisAverage_comm 0 1]
  rw [cellAverage_eq_forwardCellAverage hL, e, E3 _ ⟨⟨⟨windowIndex_cellCorner hL 0 y, windowIndex_cellCorner hL 1 y⟩,
    windowIndex_cellCorner hL 2 y⟩, windowIndex_cellCorner hL 3 y⟩]
  simp only [hm, enclosingCell_cellCorner hL]
theorem sum_sq_axisInterpolate_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {w : F.Site 0 → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hw : IsTemperedWeight w K) (i : Fin 4) (g : F.Site 0 → ℝ) :
    ∑ x ∈ allSites F 0, (w x * axisInterpolate i g x) ^ 2 ≤ 16 * K * ∑ x ∈ allSites F 0, (w x * g x) ^ 2 := by
  have hN := cellSide_pos (F := F) hL
  have hNz : (0 : ℤ) < (cellSide F : ℤ) := by exact_mod_cast hN
  have b := sum_sq_mul_le_of_abs_le_sum_translate hL hs i w (axisInterpolate i g) g K 2 hK (by norm_num)
    ({0, (cellSide F : ℤ)} : Finset ℤ) id
    (fun x m hm => hw i x m (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · simp
      · rw [abs_of_pos hNz]
        omega))
    (fun x => by
      rw [Finset.sum_pair hNz.ne]
      simp only [id, axisOffset_zero, add_zero]
      unfold axisInterpolate
      have ht := abs_windowRamp_le (N := cellSide F) (r := windowIndex i x) (windowIndex_lt hL i x).le hN
      set t := windowRamp (cellSide F) (windowIndex i x)
      set a := g x
      set c := g (x + axisOffset 0 i (cellSide F : ℤ))
      have h1 : |t * (c - a)| ≤ |c - a| := by
        rw [abs_mul]
        nlinarith [abs_nonneg (c - a)]
      have h2 : |c - a| ≤ |c| + |a| := abs_sub _ _
      have h3 : |a + t * (c - a)| ≤ |a| + |t * (c - a)| := abs_add_le _ _
      nlinarith [abs_nonneg a, abs_nonneg c])
  have hc : (({0, (cellSide F : ℤ)} : Finset ℤ).card : ℝ) = 2 := by
    rw [Finset.card_pair hNz.ne]
    norm_num
  rw [hc] at b
  refine b.trans (le_of_eq ?_)
  ring
theorem sum_sq_latticeGradient_axisInterpolate_same_le (hL : Odd F.blockSide) (i : Fin 4)
    (w g : F.Site 0 → ℝ) (hg : IsWindowConstant i g) :
    ∑ x ∈ allSites F 0, (w x * latticeGradient (axisInterpolate i g) x i) ^ 2 ≤ 16 / (cellSide F : ℝ) ^ 2 *
      ∑ x ∈ allSites F 0, (w x * (g (x + axisOffset 0 i (cellSide F : ℤ)) - g x)) ^ 2 := by
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [latticeGradient_axisInterpolate_same hL i g hg]
  have ht := abs_windowRamp_succ_sub_le (windowIndex_lt hL i x)
  set t := windowRamp (cellSide F) (windowIndex i x + 1) - windowRamp (cellSide F) (windowIndex i x)
  have h2 : t ^ 2 ≤ 16 / (cellSide F : ℝ) ^ 2 := by
    rw [← sq_abs t]
    calc |t| ^ 2 ≤ (4 / (cellSide F : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ht 2
      _ = _ := by
          field_simp
          norm_num
  calc _ = t ^ 2 * (w x * (g (x + axisOffset 0 i (cellSide F : ℤ)) - g x)) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
theorem axisInterpolate_translate_sub (hL : Odd F.blockSide) {i k : Fin 4} (hk : k ≠ i) (g : F.Site 0 → ℝ) :
    (fun x => axisInterpolate i g (x + axisOffset 0 k (cellSide F : ℤ)) - axisInterpolate i g x) =
      axisInterpolate i (fun x => g (x + axisOffset 0 k (cellSide F : ℤ)) - g x) := by
  rw [axisInterpolate_sub]
  funext x
  rw [axisInterpolate_translate hL hk]
theorem sum_sq_latticeGradient_cellSpread_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {w : F.Site 0 → ℝ} {K : ℝ} (hK : 0 ≤ K) (hw : IsTemperedWeight w K) (f : F.Cell → ℝ) (k : Fin 4) :
    ∑ x ∈ allSites F 0, (w x * latticeGradient (cellSpread f) x k) ^ 2 ≤
      (16 * K) ^ 3 * (16 / (cellSide F : ℝ) ^ 2) *
      ∑ x ∈ allSites F 0, (w x * (f (enclosingCell x + unitStep F.top k) - f (enclosingCell x))) ^ 2 := by
  have n01 : (0 : Fin 4) ≠ 1 := by decide
  have n02 : (0 : Fin 4) ≠ 2 := by decide
  have n03 : (0 : Fin 4) ≠ 3 := by decide
  have n12 : (1 : Fin 4) ≠ 2 := by decide
  have n13 : (1 : Fin 4) ≠ 3 := by decide
  have n23 : (2 : Fin 4) ≠ 3 := by decide
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  set m : F.Site 0 → ℝ := fun x => f (enclosingCell x) with hm
  set c : ℝ := 16 * K with hc
  have hc0 : 0 ≤ c := by positivity
  have hP : 0 ≤ 16 / (cellSide F : ℝ) ^ 2 := by positivity
  have J := fun (i : Fin 4) (g : F.Site 0 → ℝ) => sum_sq_axisInterpolate_le hL hs hK hw i g
  have hD : ∀ k, (fun x => m (x + axisOffset 0 k (cellSide F : ℤ)) - m x) =
      fun x => f (enclosingCell x + unitStep F.top k) - f (enclosingCell x) := by
    intro k
    funext x
    simp only [hm, enclosingCell_add_axisOffset_cellSide hL]
  set S : (F.Site 0 → ℝ) → ℝ := fun g => ∑ x ∈ allSites F 0, (w x * g x) ^ 2 with hS
  have goal_eq : ∑ x ∈ allSites F 0, (w x * (f (enclosingCell x + unitStep F.top k) - f (enclosingCell x))) ^ 2 =
      S (fun x => m (x + axisOffset 0 k (cellSide F : ℤ)) - m x) := by
    rw [hD k]
  rw [goal_eq]
  have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    fin_cases k <;> simp
  rcases hk4 with rfl | rfl | rfl | rfl
  · have c0 : IsWindowConstant 0 (axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 m))) :=
      isWindowConstant_axisInterpolate hL n01.symm _ (isWindowConstant_axisInterpolate hL n02.symm _
        (isWindowConstant_axisInterpolate hL n03.symm m (isWindowConstant_comp_enclosingCell hL f 0)))
    have a1 := sum_sq_latticeGradient_axisInterpolate_same_le hL 0 w _ c0
    have d1 := axisInterpolate_translate_sub hL n01 (axisInterpolate 2 (axisInterpolate 3 m))
    have d2 := axisInterpolate_translate_sub hL n02 (axisInterpolate 3 m)
    have d3 := axisInterpolate_translate_sub hL n03 m
    rw [show (∑ x ∈ allSites F 0, (w x * (axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 m))
      (x + axisOffset 0 0 (cellSide F : ℤ)) - axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 m)) x)) ^ 2) =
      S (axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3
        (fun x => m (x + axisOffset 0 0 (cellSide F : ℤ)) - m x)))) by
        rw [← d3, ← d2, ← d1]] at a1
    have j1 := J 1 (axisInterpolate 2 (axisInterpolate 3 (fun x => m (x + axisOffset 0 0 (cellSide F : ℤ)) - m x)))
    have j2 := J 2 (axisInterpolate 3 (fun x => m (x + axisOffset 0 0 (cellSide F : ℤ)) - m x))
    have j3 := J 3 (fun x => m (x + axisOffset 0 0 (cellSide F : ℤ)) - m x)
    calc _ ≤ _ := a1
      _ ≤ 16 / (cellSide F : ℝ) ^ 2 *
          (c * (c * (c * S (fun x => m (x + axisOffset 0 0 (cellSide F : ℤ)) - m x)))) := by
          refine mul_le_mul_of_nonneg_left (j1.trans ?_) hP
          exact mul_le_mul_of_nonneg_left (j2.trans (mul_le_mul_of_nonneg_left j3 hc0)) hc0
      _ = _ := by ring
  · have c1 : IsWindowConstant 1 (axisInterpolate 2 (axisInterpolate 3 m)) :=
      isWindowConstant_axisInterpolate hL n12.symm _
        (isWindowConstant_axisInterpolate hL n13.symm m (isWindowConstant_comp_enclosingCell hL f 1))
    have a1 := sum_sq_latticeGradient_axisInterpolate_same_le hL 1 w _ c1
    have d2 := axisInterpolate_translate_sub hL n12 (axisInterpolate 3 m)
    have d3 := axisInterpolate_translate_sub hL n13 m
    rw [show (∑ x ∈ allSites F 0, (w x * (axisInterpolate 2 (axisInterpolate 3 m) (x + axisOffset 0 1 (cellSide F : ℤ)) -
      axisInterpolate 2 (axisInterpolate 3 m) x)) ^ 2) =
      S (axisInterpolate 2 (axisInterpolate 3 (fun x => m (x + axisOffset 0 1 (cellSide F : ℤ)) - m x))) by
        rw [← d3, ← d2]] at a1
    have e0 : (fun y => latticeGradient (cellSpread f) y 1) =
        axisInterpolate 0 (fun y => latticeGradient (axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 m))) y 1) := by
      funext x
      exact latticeGradient_axisInterpolate_of_ne hL n01.symm _ x
    have j0 := J 0 (fun y => latticeGradient (axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 m))) y 1)
    have j2 := J 2 (axisInterpolate 3 (fun x => m (x + axisOffset 0 1 (cellSide F : ℤ)) - m x))
    have j3 := J 3 (fun x => m (x + axisOffset 0 1 (cellSide F : ℤ)) - m x)
    rw [show (∑ x ∈ allSites F 0, (w x * latticeGradient (cellSpread f) x 1) ^ 2) =
      ∑ x ∈ allSites F 0, (w x * axisInterpolate 0
        (fun y => latticeGradient (axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 m))) y 1) x) ^ 2 by
        rw [← e0]]
    calc _ ≤ _ := j0
      _ ≤ c * (16 / (cellSide F : ℝ) ^ 2 *
          (c * (c * S (fun x => m (x + axisOffset 0 1 (cellSide F : ℤ)) - m x)))) := by
          refine mul_le_mul_of_nonneg_left (a1.trans ?_) hc0
          exact mul_le_mul_of_nonneg_left (j2.trans (mul_le_mul_of_nonneg_left j3 hc0)) hP
      _ = _ := by ring
  · have c2 : IsWindowConstant 2 (axisInterpolate 3 m) :=
      isWindowConstant_axisInterpolate hL n23.symm m (isWindowConstant_comp_enclosingCell hL f 2)
    have a1 := sum_sq_latticeGradient_axisInterpolate_same_le hL 2 w _ c2
    have d3 := axisInterpolate_translate_sub hL n23 m
    rw [show (∑ x ∈ allSites F 0, (w x * (axisInterpolate 3 m (x + axisOffset 0 2 (cellSide F : ℤ)) -
      axisInterpolate 3 m x)) ^ 2) =
      S (axisInterpolate 3 (fun x => m (x + axisOffset 0 2 (cellSide F : ℤ)) - m x)) by rw [← d3]] at a1
    have e1 : (fun y => latticeGradient (axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 m))) y 2) =
        axisInterpolate 1 (fun y => latticeGradient (axisInterpolate 2 (axisInterpolate 3 m)) y 2) := by
      funext x
      exact latticeGradient_axisInterpolate_of_ne hL n12.symm _ x
    have e0 : (fun y => latticeGradient (cellSpread f) y 2) =
        axisInterpolate 0 (axisInterpolate 1 (fun y => latticeGradient (axisInterpolate 2 (axisInterpolate 3 m)) y 2)) := by
      funext x
      rw [← e1]
      exact latticeGradient_axisInterpolate_of_ne hL n02.symm _ x
    have j0 := J 0 (axisInterpolate 1 (fun y => latticeGradient (axisInterpolate 2 (axisInterpolate 3 m)) y 2))
    have j1 := J 1 (fun y => latticeGradient (axisInterpolate 2 (axisInterpolate 3 m)) y 2)
    have j3 := J 3 (fun x => m (x + axisOffset 0 2 (cellSide F : ℤ)) - m x)
    rw [show (∑ x ∈ allSites F 0, (w x * latticeGradient (cellSpread f) x 2) ^ 2) =
      ∑ x ∈ allSites F 0, (w x * axisInterpolate 0 (axisInterpolate 1
        (fun y => latticeGradient (axisInterpolate 2 (axisInterpolate 3 m)) y 2)) x) ^ 2 by
        rw [← e0]]
    calc _ ≤ _ := j0
      _ ≤ c * (c * (16 / (cellSide F : ℝ) ^ 2 *
          (c * S (fun x => m (x + axisOffset 0 2 (cellSide F : ℤ)) - m x)))) := by
          refine mul_le_mul_of_nonneg_left (j1.trans ?_) hc0
          refine mul_le_mul_of_nonneg_left (a1.trans ?_) hc0
          exact mul_le_mul_of_nonneg_left j3 hP
      _ = _ := by ring
  · have c3 := isWindowConstant_comp_enclosingCell hL f 3
    have a1 := sum_sq_latticeGradient_axisInterpolate_same_le hL 3 w _ c3
    have e2 : (fun y => latticeGradient (axisInterpolate 2 (axisInterpolate 3 m)) y 3) =
        axisInterpolate 2 (fun y => latticeGradient (axisInterpolate 3 m) y 3) := by
      funext x
      exact latticeGradient_axisInterpolate_of_ne hL n23.symm _ x
    have e1 : (fun y => latticeGradient (axisInterpolate 1 (axisInterpolate 2 (axisInterpolate 3 m))) y 3) =
        axisInterpolate 1 (axisInterpolate 2 (fun y => latticeGradient (axisInterpolate 3 m) y 3)) := by
      funext x
      rw [← e2]
      exact latticeGradient_axisInterpolate_of_ne hL n13.symm _ x
    have e0 : (fun y => latticeGradient (cellSpread f) y 3) =
        axisInterpolate 0 (axisInterpolate 1 (axisInterpolate 2 (fun y => latticeGradient (axisInterpolate 3 m) y 3))) := by
      funext x
      rw [← e1]
      exact latticeGradient_axisInterpolate_of_ne hL n03.symm _ x
    have j0 := J 0 (axisInterpolate 1 (axisInterpolate 2 (fun y => latticeGradient (axisInterpolate 3 m) y 3)))
    have j1 := J 1 (axisInterpolate 2 (fun y => latticeGradient (axisInterpolate 3 m) y 3))
    have j2 := J 2 (fun y => latticeGradient (axisInterpolate 3 m) y 3)
    rw [show (∑ x ∈ allSites F 0, (w x * latticeGradient (cellSpread f) x 3) ^ 2) =
      ∑ x ∈ allSites F 0, (w x * axisInterpolate 0 (axisInterpolate 1 (axisInterpolate 2
        (fun y => latticeGradient (axisInterpolate 3 m) y 3))) x) ^ 2 by
        rw [← e0]]
    calc _ ≤ _ := j0
      _ ≤ c * (c * (c * (16 / (cellSide F : ℝ) ^ 2 *
          S (fun x => m (x + axisOffset 0 3 (cellSide F : ℤ)) - m x)))) := by
          refine mul_le_mul_of_nonneg_left (j1.trans ?_) hc0
          refine mul_le_mul_of_nonneg_left (j2.trans ?_) hc0
          exact mul_le_mul_of_nonneg_left a1 hc0
      _ = _ := by ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
