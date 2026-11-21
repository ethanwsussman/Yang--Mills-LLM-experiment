import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfAFormInOneDirection
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def forwardAxisAverage (i : Fin 4) (g : F.Site 0 → ℝ) (x : F.Site 0) : ℝ :=
  (1 / (cellSide F : ℝ)) * ∑ u ∈ Finset.range (cellSide F), g (x + axisOffset 0 i (u : ℤ))
def windowComponent (i k : Fin 4) (g : F.Site 0 → ℝ) (x : F.Site 0) : ℝ :=
  if k = i then forwardAxisAverage i (forwardAxisAverage i g) (windowStart i x)
  else (1 - (windowIndex i x : ℝ) / cellSide F) * forwardAxisAverage i g (windowStart i x) +
    ((windowIndex i x : ℝ) / cellSide F) *
      forwardAxisAverage i g (windowStart i x + axisOffset 0 i (cellSide F : ℤ))
def windowReadMeans (i k : Fin 4) (g : F.Site 0 → ℝ) : F.Site 0 → ℝ :=
  if k = i then forwardAxisAverage i (forwardAxisAverage i g) else forwardAxisAverage i g
theorem windowProjection_eq_windowComponent (Z : LevelForm F 0) (i k : Fin 4) (x : F.Site 0) :
    windowProjection Z i x k = windowComponent i k (fun y => Z y k) x := by
  unfold windowProjection windowForm windowComponent
  by_cases h : k = i
  · subst h
    simp only [if_true]
    rfl
  · simp only [if_neg h]
    rfl
theorem forwardAxisAverage_comm (i j : Fin 4) (g : F.Site 0 → ℝ) :
    forwardAxisAverage i (forwardAxisAverage j g) = forwardAxisAverage j (forwardAxisAverage i g) := by
  funext x
  unfold forwardAxisAverage
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [add_right_comm, mul_left_comm]
theorem forwardAxisAverage_windowComponent (hL : Odd F.blockSide) {i j : Fin 4} (hij : j ≠ i)
    (k : Fin 4) (g : F.Site 0 → ℝ) :
    forwardAxisAverage j (windowComponent i k g) = windowComponent i k (forwardAxisAverage j g) := by
  funext x
  have e : ∀ u : ℕ, windowComponent i k g (x + axisOffset 0 j (u : ℤ)) =
      if k = i then forwardAxisAverage i (forwardAxisAverage i g) (windowStart i x + axisOffset 0 j (u : ℤ))
      else (1 - (windowIndex i x : ℝ) / cellSide F) *
          forwardAxisAverage i g (windowStart i x + axisOffset 0 j (u : ℤ)) +
        ((windowIndex i x : ℝ) / cellSide F) *
          forwardAxisAverage i g (windowStart i x + axisOffset 0 i (cellSide F : ℤ) + axisOffset 0 j (u : ℤ)) := by
    intro u
    unfold windowComponent
    rw [windowIndex_add_axisOffset_of_ne hL hij, windowStart_add_axisOffset_of_ne hL hij,
      add_right_comm _ (axisOffset 0 j _)]
  have e2 : forwardAxisAverage j (windowComponent i k g) x =
      (1 / (cellSide F : ℝ)) * ∑ u ∈ Finset.range (cellSide F),
        windowComponent i k g (x + axisOffset 0 j (u : ℤ)) := rfl
  rw [e2]
  simp only [e]
  unfold windowComponent
  by_cases h : k = i
  · simp only [if_pos h]
    show forwardAxisAverage j (forwardAxisAverage i (forwardAxisAverage i g)) (windowStart i x) = _
    rw [forwardAxisAverage_comm j i (forwardAxisAverage i g), forwardAxisAverage_comm j i g]
  · simp only [if_neg h]
    rw [← forwardAxisAverage_comm j i g]
    rw [Finset.sum_add_distrib, mul_add, ← Finset.mul_sum, ← Finset.mul_sum]
    show _ = (1 - (windowIndex i x : ℝ) / cellSide F) * ((1 / (cellSide F : ℝ)) *
        ∑ u ∈ Finset.range (cellSide F),
          forwardAxisAverage i g (windowStart i x + axisOffset 0 j (u : ℤ))) +
        ((windowIndex i x : ℝ) / cellSide F) * ((1 / (cellSide F : ℝ)) *
        ∑ u ∈ Finset.range (cellSide F),
          forwardAxisAverage i g (windowStart i x + axisOffset 0 i (cellSide F : ℤ) + axisOffset 0 j (u : ℤ)))
    ring
theorem windowReadMeans_windowComponent (hL : Odd F.blockSide) {i j : Fin 4} (hij : j ≠ i)
    (k : Fin 4) (g : F.Site 0 → ℝ) :
    windowReadMeans j k (windowComponent i k g) = windowComponent i k (windowReadMeans j k g) := by
  unfold windowReadMeans
  by_cases h : k = j
  · simp only [if_pos h]
    rw [forwardAxisAverage_windowComponent hL hij, forwardAxisAverage_windowComponent hL hij]
  · simp only [if_neg h]
    rw [forwardAxisAverage_windowComponent hL hij]
def windowEnds : Finset ℤ := {0, 1}
def windowEnd (i : Fin 4) (a : ℤ) (p : F.Site 0) : F.Site 0 :=
  windowStart i p + axisOffset 0 i (a * (cellSide F : ℤ))
theorem sq_windowComponent_le (hL : Odd F.blockSide) (i k : Fin 4) (g : F.Site 0 → ℝ) (x : F.Site 0) :
    windowComponent i k g x ^ 2 ≤ ∑ a ∈ windowEnds, windowReadMeans i k g (windowEnd i a x) ^ 2 := by
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  have hlt := windowIndex_lt hL i x
  have e : ∑ a ∈ windowEnds, windowReadMeans i k g (windowEnd i a x) ^ 2 =
      windowReadMeans i k g (windowStart i x) ^ 2 +
      windowReadMeans i k g (windowStart i x + axisOffset 0 i (cellSide F : ℤ)) ^ 2 := by
    unfold windowEnds windowEnd
    rw [Finset.sum_pair (by norm_num)]
    simp [axisOffset_zero]
  rw [e]
  unfold windowComponent windowReadMeans
  by_cases h : k = i
  · simp only [if_pos h]
    nlinarith [sq_nonneg (forwardAxisAverage i (forwardAxisAverage i g)
      (windowStart i x + axisOffset 0 i (cellSide F : ℤ)))]
  · simp only [if_neg h]
    have hr0 : 0 ≤ (windowIndex i x : ℝ) / cellSide F := by positivity
    have hr1 : (windowIndex i x : ℝ) / cellSide F ≤ 1 := by
      rw [div_le_one hNr]
      exact_mod_cast hlt.le
    set r := (windowIndex i x : ℝ) / cellSide F
    set A := forwardAxisAverage i g (windowStart i x)
    set C := forwardAxisAverage i g (windowStart i x + axisOffset 0 i (cellSide F : ℤ))
    have h2 : ((1 - r) * A + r * C) ^ 2 ≤ (1 - r) * A ^ 2 + r * C ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ 1 - r)) (sq_nonneg (A - C))]
    nlinarith [mul_nonneg hr0 (sq_nonneg A), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - r) (sq_nonneg C)]
def stackedWindowComponent (k : Fin 4) (g : F.Site 0 → ℝ) : F.Site 0 → ℝ :=
  windowComponent 3 k (windowComponent 2 k (windowComponent 1 k (windowComponent 0 k g)))
def forwardCellAverage (g : F.Site 0 → ℝ) : F.Site 0 → ℝ :=
  forwardAxisAverage 0 (forwardAxisAverage 1 (forwardAxisAverage 2 (forwardAxisAverage 3 g)))
theorem windowReadMeans_stack_eq (k : Fin 4) (g : F.Site 0 → ℝ) :
    windowReadMeans 0 k (windowReadMeans 1 k (windowReadMeans 2 k (windowReadMeans 3 k g))) =
      forwardCellAverage (forwardAxisAverage k g) := by
  unfold forwardCellAverage windowReadMeans
  fin_cases k
  · simp only [Fin.isValue, Fin.zero_eta, if_true, Fin.reduceEq, if_false]
    rw [forwardAxisAverage_comm 3 0, forwardAxisAverage_comm 2 0, forwardAxisAverage_comm 1 0]
  · simp only [Fin.isValue, Fin.mk_one, if_true, Fin.reduceEq, if_false]
    rw [forwardAxisAverage_comm 3 1, forwardAxisAverage_comm 2 1]
  · simp only [Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
    rw [forwardAxisAverage_comm 3 2]
  · simp only [Fin.isValue, Fin.reduceFinMk, if_true, Fin.reduceEq, if_false]
theorem sq_stackedWindowComponent_le (hL : Odd F.blockSide) (k : Fin 4) (g : F.Site 0 → ℝ) (x : F.Site 0) :
    stackedWindowComponent k g x ^ 2 ≤ ∑ a ∈ windowEnds, ∑ b ∈ windowEnds, ∑ c ∈ windowEnds, ∑ d ∈ windowEnds,
      forwardCellAverage (forwardAxisAverage k g)
        (windowEnd 0 d (windowEnd 1 c (windowEnd 2 b (windowEnd 3 a x)))) ^ 2 := by
  have n10 : (1 : Fin 4) ≠ 0 := by decide
  have n20 : (2 : Fin 4) ≠ 0 := by decide
  have n30 : (3 : Fin 4) ≠ 0 := by decide
  have n21 : (2 : Fin 4) ≠ 1 := by decide
  have n31 : (3 : Fin 4) ≠ 1 := by decide
  have n32 : (3 : Fin 4) ≠ 2 := by decide
  unfold stackedWindowComponent
  refine (sq_windowComponent_le hL 3 k _ x).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [windowReadMeans_windowComponent hL n32, windowReadMeans_windowComponent hL n31,
    windowReadMeans_windowComponent hL n30]
  refine (sq_windowComponent_le hL 2 k _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [windowReadMeans_windowComponent hL n21, windowReadMeans_windowComponent hL n20]
  refine (sq_windowComponent_le hL 1 k _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [windowReadMeans_windowComponent hL n10]
  refine (sq_windowComponent_le hL 0 k _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [windowReadMeans_stack_eq]
theorem intCast_cellSide : (cellSide F : ℤ) = (F.blockSide : ℤ) ^ F.top := by
  simp [cellSide]
theorem cellHalfSide_eq {k : ℕ} (hk : cellSide F = 2 * k + 1) : cellHalfSide F = k := by
  unfold cellHalfSide
  rw [← intCast_cellSide, hk]
  push_cast
  omega
theorem enclosingCell_siteOfCoords (hL : Odd F.blockSide) (v : Fin 4 → ℤ) :
    enclosingCell (siteOfCoords 0 v : F.Site 0) =
      siteOfCoords F.top fun i => (v i + cellHalfSide F) / (cellSide F : ℤ) := by
  have hN : (cellSide F : ℤ) ≠ 0 := by
    have := cellSide_pos (F := F) hL
    omega
  unfold enclosingCell
  rw [siteOfCoords_eq_iff]
  intro i
  simp only [Nat.sub_zero]
  rw [siteCoords_siteOfCoords, ← intCast_cellSide]
  have hP : (F.period 0 i : ℤ) = (cellSide F : ℤ) * (F.period F.top i : ℤ) := by
    rw [period_eq_pow_mul_int (Nat.zero_le F.top) le_rfl i]
    simp [cellSide]
  have e1 := Int.emod_add_mul_ediv (v i) (F.period 0 i : ℤ)
  have e2 : v i % (F.period 0 i : ℤ) + cellHalfSide F =
      (v i + cellHalfSide F) +
        (cellSide F : ℤ) * (-((F.period F.top i : ℤ) * (v i / (F.period 0 i : ℤ)))) := by
    rw [hP] at e1 ⊢
    linear_combination e1
  show (F.period F.top i : ℤ) ∣ (v i + cellHalfSide F) / (cellSide F : ℤ) -
    (v i % (F.period 0 i : ℤ) + ((F.blockSide : ℤ) ^ F.top - 1) / 2) / (cellSide F : ℤ)
  have e3 : ((F.blockSide : ℤ) ^ F.top - 1) / 2 = cellHalfSide F := rfl
  rw [e3, e2, Int.add_mul_ediv_left _ _ hN]
  exact ⟨v i / (F.period 0 i : ℤ), by ring⟩
theorem enclosingCell_refineSite_add (hL : Odd F.blockSide) (y : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (cellSide F)) :
    enclosingCell (refineSite 0 F.top y + siteOfCoords 0 h) = y := by
  obtain ⟨k, hk⟩ := hL.pow (n := F.top)
  have hN : (cellSide F : ℤ) ≠ 0 := by
    have := cellSide_pos (F := F) hL
    omega
  have hh' := (mem_centredCube_iff hk h).1 hh
  have hNk : (cellSide F : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  unfold refineSite
  rw [← siteOfCoords_add, enclosingCell_siteOfCoords hL]
  conv_rhs => rw [← siteOfCoords_siteCoords y]
  congr 1
  funext i
  simp only [Pi.add_apply, Nat.sub_zero]
  rw [← intCast_cellSide, cellHalfSide_eq hk, add_assoc, Int.mul_add_ediv_left _ _ hN]
  have q := hh' i
  have : (h i + k) / (cellSide F : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  rw [this, add_zero]
def cellCorner (y : F.Cell) : F.Site 0 :=
  refineSite 0 F.top y + siteOfCoords 0 (fun _ => - cellHalfSide F)
theorem cellCorner_siteOfCoords (q : Fin 4 → ℤ) :
    cellCorner (siteOfCoords F.top q : F.Cell) =
      siteOfCoords 0 fun i => (cellSide F : ℤ) * q i - cellHalfSide F := by
  unfold cellCorner
  rw [refineSite_siteOfCoords (Nat.zero_le F.top) le_rfl, ← siteOfCoords_add]
  congr 1
theorem windowEnd_siteOfCoords (hL : Odd F.blockSide) (i : Fin 4) (a : ℤ) (v : Fin 4 → ℤ) :
    windowEnd i a (siteOfCoords 0 v : F.Site 0) =
      siteOfCoords 0 (Function.update v i
        ((cellSide F : ℤ) * ((v i + cellHalfSide F) / (cellSide F : ℤ) + a) - cellHalfSide F)) := by
  unfold windowEnd windowStart
  rw [add_assoc, ← axisOffset_add]
  unfold axisOffset
  rw [← siteOfCoords_add]
  congr 1
  funext l
  by_cases h : l = i
  · subst h
    have e := Int.emod_add_mul_ediv (v l + cellHalfSide F) (cellSide F : ℤ)
    simp only [Pi.add_apply, Pi.single_eq_same, Function.update_self]
    rw [natCast_windowIndex_siteOfCoords hL]
    linear_combination -e
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
theorem windowEnd_iterate_eq_cellCorner (hL : Odd F.blockSide) (x : F.Site 0) (a b c d : ℤ) :
    windowEnd 0 d (windowEnd 1 c (windowEnd 2 b (windowEnd 3 a x))) =
      cellCorner (enclosingCell x + siteOfCoords F.top ![d, c, b, a]) := by
  conv_lhs => rw [← siteOfCoords_siteCoords x]
  conv_rhs => rw [← siteOfCoords_siteCoords x]
  rw [windowEnd_siteOfCoords hL, windowEnd_siteOfCoords hL, windowEnd_siteOfCoords hL,
    windowEnd_siteOfCoords hL, enclosingCell_siteOfCoords hL, ← siteOfCoords_add, cellCorner_siteOfCoords]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_of_ne]
theorem sum_piFinset_fin_four (I : Finset ℤ) (f : (Fin 4 → ℤ) → ℝ) :
    ∑ h ∈ Fintype.piFinset (fun _ : Fin 4 => I), f h =
      ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, ∑ d ∈ I, f ![a, b, c, d] := by
  have e : ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ I, ∑ d ∈ I, f ![a, b, c, d] =
      ∑ p ∈ I ×ˢ (I ×ˢ (I ×ˢ I)), f ![p.1, p.2.1, p.2.2.1, p.2.2.2] := by
    simp only [Finset.sum_product]
  rw [e]
  symm
  refine Finset.sum_nbij (fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨a, b, c, d⟩ hp
    simp only [Finset.mem_product] at hp
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i <;> simp [hp]
  · rintro ⟨a, b, c, d⟩ _ ⟨a', b', c', d'⟩ _ he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    have h2 := congrFun he 2
    have h3 := congrFun he 3
    simp at h0 h1 h2 h3
    simp [h0, h1, h2, h3]
  · intro h hh
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hh
    refine ⟨(h 0, h 1, h 2, h 3), ?_, ?_⟩
    · simp [hh]
    · funext i
      fin_cases i <;> rfl
theorem sum_range_eq_sum_Icc (k : ℕ) (f : ℤ → ℝ) :
    ∑ u ∈ Finset.range (2 * k + 1), f (u : ℤ) = ∑ a ∈ Finset.Icc (-(k : ℤ)) k, f (a + k) := by
  refine Finset.sum_nbij (fun u => (u : ℤ) - k) ?_ ?_ ?_ ?_
  · intro u hu
    have := Finset.mem_range.1 hu
    rw [Finset.mem_Icc]
    constructor <;> omega
  · intro a _ b _ h
    simpa using h
  · intro a ha
    have := Finset.mem_Icc.1 (Finset.mem_coe.1 ha)
    refine ⟨(a + k).toNat, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_range]
      omega
    · simp only
      omega
  · intro u _
    simp
theorem forwardCellAverage_cellCorner (hL : Odd F.blockSide) (G : F.Site 0 → ℝ) (y : F.Cell) :
    forwardCellAverage G (cellCorner y) = (1 / (cellSide F : ℝ) ^ 4) *
      ∑ h ∈ centredCube (cellSide F), G (refineSite 0 F.top y + siteOfCoords 0 h) := by
  obtain ⟨k, hk⟩ := hL.pow (n := F.top)
  have hk' : cellSide F = 2 * k + 1 := hk
  have e0 : ((cellSide F : ℤ) - 1) / 2 = k := by
    rw [hk']
    push_cast
    omega
  have e1 : centredCube (cellSide F) = Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(k : ℤ)) k) := by
    unfold centredCube
    rw [e0]
  rw [e1, sum_piFinset_fin_four]
  have e3 : ∀ (i : Fin 4) (g : F.Site 0 → ℝ) (p : F.Site 0), forwardAxisAverage i g p =
      (1 / (cellSide F : ℝ)) * ∑ a ∈ Finset.Icc (-(k : ℤ)) k, g (p + axisOffset 0 i (a + k)) := by
    intro i g p
    unfold forwardAxisAverage
    congr 1
    have := sum_range_eq_sum_Icc k (fun m => g (p + axisOffset 0 i m))
    rw [← hk'] at this
    exact this
  unfold forwardCellAverage
  simp only [e3]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  have e4 : cellCorner y + axisOffset 0 0 (a + k) + axisOffset 0 1 (b + k) + axisOffset 0 2 (c + k) +
      axisOffset 0 3 (d + k) = refineSite 0 F.top y + siteOfCoords 0 ![a, b, c, d] := by
    unfold cellCorner axisOffset
    rw [add_assoc (refineSite 0 F.top y), add_assoc (refineSite 0 F.top y), add_assoc (refineSite 0 F.top y),
      add_assoc (refineSite 0 F.top y)]
    congr 1
    rw [← siteOfCoords_add, ← siteOfCoords_add, ← siteOfCoords_add, ← siteOfCoords_add, cellHalfSide_eq hk']
    congr 1
    funext i
    fin_cases i <;> simp [Pi.single_apply]
  rw [e4]
  ring
theorem forwardCellAverage_cellCorner_eq_iteratedLineAverage (hL : Odd F.blockSide) (B : LevelForm F 0)
    (k : Fin 4) (y : F.Cell) :
    forwardCellAverage (forwardAxisAverage k (fun x => B x k)) (cellCorner y) =
      (1 / (cellSide F : ℝ)) * iteratedLineAverage B F.top y k := by
  rw [forwardCellAverage_cellCorner hL, iteratedLineAverage_eq hL le_rfl]
  have e : ∀ x, forwardAxisAverage k (fun x => B x k) x =
      (1 / (cellSide F : ℝ)) * lineSum B x k (cellSide F) := fun _ => rfl
  simp only [e]
  rw [← Finset.mul_sum]
  push_cast
  ring
def stackedWindowProjection (B : LevelForm F 0) : LevelForm F 0 :=
  windowProjection (windowProjection (windowProjection (windowProjection B 0) 1) 2) 3
theorem stackedWindowProjection_eq (B : LevelForm F 0) (x : F.Site 0) (k : Fin 4) :
    stackedWindowProjection B x k = stackedWindowComponent k (fun y => B y k) x := by
  have e : ∀ (Z : LevelForm F 0) (i : Fin 4),
      (fun y => windowProjection Z i y k) = windowComponent i k (fun y => Z y k) :=
    fun Z i => funext fun y => windowProjection_eq_windowComponent Z i k y
  unfold stackedWindowProjection stackedWindowComponent
  rw [windowProjection_eq_windowComponent, e, e, e]
theorem sum_allSites_enclosingCell (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (f : F.Cell → ℝ) :
    ∑ x ∈ allSites F 0, f (enclosingCell x) = (cellSide F : ℝ) ^ 4 * ∑ y ∈ allSites F F.top, f y := by
  obtain ⟨k, hk⟩ := hL.pow (n := F.top)
  rw [sum_allSites_eq_sum_blocks hL hs (Nat.zero_le F.top) le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e : ∀ h ∈ centredCube (F.blockSide ^ (F.top - 0)),
      f (enclosingCell (refineSite 0 F.top y + siteOfCoords 0 h)) = f y := by
    intro h hh
    rw [enclosingCell_refineSite_add hL y h hh]
  rw [Finset.sum_congr rfl e]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.sub_zero]
  rw [card_centredCube hk]
  push_cast
  ring
theorem weightedNormSq_stackedWindowProjection_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (w : F.Site 0 → ℝ) (u : F.Cell → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ x, ∀ a ∈ windowEnds, ∀ b ∈ windowEnds, ∀ c ∈ windowEnds, ∀ d ∈ windowEnds,
      w x ^ 2 ≤ K * u (enclosingCell x + siteOfCoords F.top ![d, c, b, a]) ^ 2) (B : LevelForm F 0) :
    weightedNormSq w (stackedWindowProjection B) ≤
      16 * K * (cellSide F : ℝ) ^ 2 * weightedNormSq u (iteratedLineAverage B F.top) := by
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  unfold weightedNormSq
  rw [Finset.sum_comm, Finset.sum_comm (s := allSites F F.top), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  set T : F.Cell → ℝ := fun y => (u y * iteratedLineAverage B F.top y k) ^ 2 with hT
  have hx : ∀ x, (w x * stackedWindowProjection B x k) ^ 2 ≤
      ∑ a ∈ windowEnds, ∑ b ∈ windowEnds, ∑ c ∈ windowEnds, ∑ d ∈ windowEnds,
        K / (cellSide F : ℝ) ^ 2 * T (enclosingCell x + siteOfCoords F.top ![d, c, b, a]) := by
    intro x
    rw [stackedWindowProjection_eq, mul_pow]
    refine (mul_le_mul_of_nonneg_left (sq_stackedWindowComponent_le hL k _ x) (sq_nonneg _)).trans ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
      Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun d hd => ?_
    rw [windowEnd_iterate_eq_cellCorner hL, forwardCellAverage_cellCorner_eq_iteratedLineAverage hL]
    have := hw x a ha b hb c hc d hd
    simp only [hT]
    set y := enclosingCell x + siteOfCoords F.top ![d, c, b, a]
    calc w x ^ 2 * ((1 / (cellSide F : ℝ)) * iteratedLineAverage B F.top y k) ^ 2
        ≤ (K * u y ^ 2) * ((1 / (cellSide F : ℝ)) * iteratedLineAverage B F.top y k) ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = _ := by
          field_simp
  have hc : ∀ e : F.Cell, ∑ x ∈ allSites F 0, T (enclosingCell x + e) =
      (cellSide F : ℝ) ^ 4 * ∑ y ∈ allSites F F.top, T y := by
    intro e
    rw [sum_allSites_enclosingCell hL hs (fun y => T (y + e)), sum_allSites_add_right hL hs le_rfl e T]
  calc _ ≤ ∑ x ∈ allSites F 0, ∑ a ∈ windowEnds, ∑ b ∈ windowEnds, ∑ c ∈ windowEnds, ∑ d ∈ windowEnds,
        K / (cellSide F : ℝ) ^ 2 * T (enclosingCell x + siteOfCoords F.top ![d, c, b, a]) :=
        Finset.sum_le_sum fun x _ => hx x
    _ = ∑ a ∈ windowEnds, ∑ b ∈ windowEnds, ∑ c ∈ windowEnds, ∑ d ∈ windowEnds,
        K / (cellSide F : ℝ) ^ 2 * ((cellSide F : ℝ) ^ 4 * ∑ y ∈ allSites F F.top, T y) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.mul_sum, hc]
    _ = _ := by
        have hcard : (windowEnds.card : ℝ) = 2 := by
          unfold windowEnds
          rw [Finset.card_pair (by norm_num)]
          norm_num
        simp only [Finset.sum_const, nsmul_eq_mul, hcard]
        field_simp
        ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
