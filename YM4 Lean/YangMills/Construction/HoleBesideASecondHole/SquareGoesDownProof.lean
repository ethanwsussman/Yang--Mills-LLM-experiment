import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.HoleBesideASecondHole.SquareGoesDown
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.SquareDescent
open YangMills.Construction.BlockAverages YangMills.Construction.GroupMeans YangMills.Construction.LumpContours
namespace OneLevel
variable {F : BlockFrame}
theorem unitQuaternion_coe_mul (g g' : UnitQuaternion) :
    ((g * g' : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (g' : ℍ[ℝ]) := rfl
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_unitQuaternion_mul (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖(g : ℍ[ℝ]) * q‖ = ‖q‖ := by
  rw [norm_mul, norm_unitQuaternion, one_mul]
theorem norm_mul_unitQuaternion (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖q * (g : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, norm_unitQuaternion, mul_one]
theorem norm_sub_inv_inv (g g' : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g : ℍ[ℝ]) - g'‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathHolonomy_append {j : ℕ} (X : F.GaugeField j) (l l' : List PathStep) :
    ∀ x, pathHolonomy X x (l ++ l') =
      pathHolonomy X x l * pathHolonomy X (x + pathDisplacement j l) l' := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_append <;> assumption
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem linkValue_backward {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_reverse <;> assumption
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) :
    ∀ x, pathHolonomy X (x + pathDisplacement j l) (reversePath l) = (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_reversePath <;> assumption
theorem refineSite_add_step (j : ℕ) (hj : j < F.top) (y : F.Site (j + 1)) (st : PathStep) :
    refineSite (y + stepDisplacement (j + 1) st) =
      refineSite y + F.blockSide • stepDisplacement j st := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.refineSite_add_step <;> assumption
theorem pathDisplacement_replicate (j n : ℕ) (st : PathStep) :
    pathDisplacement (F := F) j (List.replicate n st) = n • stepDisplacement j st := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate <;> assumption
theorem siteOfCoords_eq_sum (j : ℕ) (h : Fin 4 → ℤ) :
    siteOfCoords (F := F) j h = ∑ i, h i • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_eq_sum <;> assumption
theorem pathDisplacement_axisPath (j : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
def legHolonomy {j : ℕ} (W : F.GaugeField j) (y : F.Site (j + 1))
    (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) : UnitQuaternion :=
  pathHolonomy W (refineSite y) (axisPath e.1 e.2)
theorem contourHolonomy_eq (j : ℕ) (hj : j < F.top) (W : F.GaugeField j) (y : F.Site (j + 1))
    (i : Fin 4) (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    contourHolonomy W (y, i) e = legHolonomy W y e *
      pathHolonomy W (refineSite y + siteOfCoords j e.1) (List.replicate F.blockSide (i, true)) *
      (legHolonomy W (y + unitStep (j + 1) i) e)⁻¹ := by
  unfold contourHolonomy bondContour legHolonomy
  rw [pathHolonomy_append, pathHolonomy_append, pathDisplacement_append, pathDisplacement_axisPath,
    pathDisplacement_replicate]
  have e1 : refineSite y + (siteOfCoords j e.1 + F.blockSide • stepDisplacement j (i, true)) =
      refineSite (y + unitStep (j + 1) i) + pathDisplacement j (axisPath e.1 e.2) := by
    have := refineSite_add_step j hj y (i, true)
    simp only [stepDisplacement, if_true] at this ⊢
    rw [this, pathDisplacement_axisPath]
    abel
  rw [e1, pathHolonomy_reversePath]
def stepBond {j : ℕ} (y : F.Site j) (st : PathStep) : F.Site j × Fin 4 :=
  if st.2 then (y, st.1) else (y - unitStep j st.1, st.1)
def stepHolonomy {j : ℕ} (W : F.GaugeField j) (y : F.Site (j + 1)) (st : PathStep) :
    (Fin 4 → ℤ) × Equiv.Perm (Fin 4) → UnitQuaternion :=
  fun e => if st.2 then contourHolonomy W (stepBond y st) e
    else (contourHolonomy W (stepBond y st) e)⁻¹
theorem stepHolonomy_eq (j : ℕ) (hj : j < F.top) (W : F.GaugeField j) (y : F.Site (j + 1))
    (st : PathStep) (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    stepHolonomy W y st e = legHolonomy W y e *
      pathHolonomy W (refineSite y + siteOfCoords j e.1) (List.replicate F.blockSide st) *
      (legHolonomy W (y + stepDisplacement (j + 1) st) e)⁻¹ := by
  obtain ⟨i, b⟩ := st
  cases b
  · simp only [stepHolonomy, stepBond, Bool.false_eq_true, if_false, stepDisplacement]
    rw [contourHolonomy_eq j hj, sub_add_cancel, ← sub_eq_add_neg]
    have h1 := pathHolonomy_reversePath W (List.replicate F.blockSide (i, true))
      (refineSite (y - unitStep (j + 1) i) + siteOfCoords j e.1)
    have e2 : reversePath (List.replicate F.blockSide (i, true)) =
        List.replicate F.blockSide (i, false) := by
      simp [reversePath, List.map_replicate]
    have e3 : refineSite (y - unitStep (j + 1) i) + siteOfCoords j e.1 +
        pathDisplacement j (List.replicate F.blockSide (i, true)) =
        refineSite y + siteOfCoords j e.1 := by
      rw [pathDisplacement_replicate]
      have := refineSite_add_step j hj (y - unitStep (j + 1) i) (i, true)
      simp only [stepDisplacement, if_true, sub_add_cancel] at this ⊢
      rw [this]
      abel
    rw [e2, e3] at h1
    rw [h1]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  · simp only [stepHolonomy, stepBond, if_true, stepDisplacement]
    rw [contourHolonomy_eq j hj]
def pathHolonomies {j : ℕ} (W : F.GaugeField j) :
    F.Site (j + 1) → List PathStep → List ((Fin 4 → ℤ) × Equiv.Perm (Fin 4) → UnitQuaternion)
  | _, [] => []
  | y, st :: r => stepHolonomy W y st :: pathHolonomies W (y + stepDisplacement (j + 1) st) r
theorem pointwiseProd_pathHolonomies (j : ℕ) (hj : j < F.top) (W : F.GaugeField j)
    (l : List PathStep) (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    ∀ y : F.Site (j + 1), pointwiseProd (pathHolonomies W y l) e = legHolonomy W y e *
      pathHolonomy W (refineSite y + siteOfCoords j e.1) (l.flatMap (List.replicate F.blockSide)) *
      (legHolonomy W (y + pathDisplacement (j + 1) l) e)⁻¹ := by
  induction l with
  | nil =>
    intro y
    simp [pathHolonomies, pointwiseProd, pathHolonomy, pathDisplacement]
  | cons st r ih =>
    intro y
    have e0 : pointwiseProd (pathHolonomies W y (st :: r)) e =
        stepHolonomy W y st e *
          pointwiseProd (pathHolonomies W (y + stepDisplacement (j + 1) st) r) e := by
      simp [pathHolonomies, pointwiseProd]
    rw [e0, ih, stepHolonomy_eq j hj, List.flatMap_cons, pathHolonomy_append,
      pathDisplacement_replicate]
    have e1 : y + stepDisplacement (j + 1) st + pathDisplacement (j + 1) r =
        y + pathDisplacement (j + 1) (st :: r) := by
      simp [pathDisplacement, add_assoc]
    have e2 : refineSite (y + stepDisplacement (j + 1) st) + siteOfCoords j e.1 =
        refineSite y + siteOfCoords j e.1 + F.blockSide • stepDisplacement j st := by
      rw [refineSite_add_step j hj]
      abel
    rw [e1, e2]
    simp only [mul_assoc, inv_mul_cancel_left]
theorem flatMap_replicate_replicate (L n : ℕ) (st : PathStep) :
    (List.replicate n st).flatMap (List.replicate L) = List.replicate (n * L) st := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, Nat.succ_mul, add_comm, List.replicate_add]
theorem squarePath_flatMap_replicate (L n : ℕ) (μ ν : Fin 4) :
    (squarePath n μ ν).flatMap (List.replicate L) = squarePath (n * L) μ ν := by
  simp only [squarePath, List.flatMap_append, flatMap_replicate_replicate]
theorem pathDisplacement_squarePath (j n : ℕ) (μ ν : Fin 4) :
    pathDisplacement (F := F) j (squarePath n μ ν) = 0 := by
  simp only [squarePath, pathDisplacement_append, pathDisplacement_replicate, stepDisplacement,
    if_true, Bool.false_eq_true, if_false]
  simp only [smul_neg]
  abel
theorem norm_conj_sub_one (a b : UnitQuaternion) :
    ‖((a * b * a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(b : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem centredCube_nonempty (M : ℕ) (hM : 0 < M) : (centredCube M).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc]
  intro _
  omega
theorem allContours_nonempty (hL : Odd F.blockSide) : (allContours F).Nonempty := by
  have := centredCube_nonempty F.blockSide hL.pos
  exact this.product Finset.univ_nonempty
theorem average_allContours_fst (hL : Odd F.blockSide) (f : (Fin 4 → ℤ) → ℝ) :
    average (allContours F) (fun e => f e.1) = average (centredCube F.blockSide) f := by
  have h0 : ((centredCube F.blockSide).card : ℝ) ≠ 0 := by
    have := (centredCube_nonempty F.blockSide hL.pos).card_pos
    positivity
  simp only [average, allContours]
  rw [Finset.sum_product, Finset.card_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  push_cast
  norm_num [Nat.factorial]
  field_simp
theorem card_centredCube (M : ℕ) (hM : Odd M) : ((centredCube M).card : ℝ) = (M : ℝ) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.card_centredCube_real <;> assumption
theorem quatAverage_contourHolonomy (hL : Odd F.blockSide) {j : ℕ} (W : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) :
    quatAverage (allContours F) (fun e => ((contourHolonomy W c e : UnitQuaternion) : ℍ[ℝ])) =
      contourAverage W c := by
  have hc := card_centredCube F.blockSide hL
  simp only [quatAverage, allContours, contourAverage, contourHolonomy]
  rw [Finset.sum_product, Finset.card_product]
  congr 1
  simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  push_cast
  rw [hc]
  norm_num [Nat.factorial]
  ring_nf
def bondSum {j : ℕ} (f : F.Site j × Fin 4 → ℝ) : F.Site j → List PathStep → ℝ
  | _, [] => 0
  | y, st :: r => f (stepBond y st) + bondSum f (y + stepDisplacement j st) r
theorem bondSum_append {j : ℕ} (f : F.Site j × Fin 4 → ℝ) (l l' : List PathStep) :
    ∀ y, bondSum f y (l ++ l') = bondSum f y l + bondSum f (y + pathDisplacement j l) l' := by
  induction l with
  | nil => intro y; simp [bondSum, pathDisplacement]
  | cons st r ih =>
    intro y
    simp only [List.cons_append, bondSum]
    have : y + stepDisplacement j st + pathDisplacement j r = y + pathDisplacement j (st :: r) := by
      simp [pathDisplacement, add_assoc]
    rw [ih, this]
    exact (add_assoc _ _ _).symm
theorem bondSum_replicate {j : ℕ} (f : F.Site j × Fin 4 → ℝ) (n : ℕ) (st : PathStep) :
    ∀ y, bondSum f y (List.replicate n st) =
      ∑ r ∈ Finset.range n, f (stepBond (y + r • stepDisplacement j st) st) := by
  induction n with
  | zero => intro y; simp [bondSum]
  | succ n ih =>
    intro y
    rw [List.replicate_succ, Finset.sum_range_succ']
    simp only [bondSum]
    rw [ih]
    simp only [zero_smul, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [add_assoc, add_comm (stepDisplacement j st), add_smul, one_smul]
theorem bondSum_squarePath {j : ℕ} (f : F.Site j × Fin 4 → ℝ) (x : F.Site j) (n : ℕ)
    (μ ν : Fin 4) :
    bondSum f x (squarePath n μ ν) = sumAroundSquare f x n μ ν := by
  unfold squarePath sumAroundSquare
  rw [bondSum_append, bondSum_append, bondSum_append]
  simp only [pathDisplacement_append, pathDisplacement_replicate, bondSum_replicate]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [stepBond, stepDisplacement, if_true, Bool.false_eq_true, if_false]
  have h : ∀ a a' b b' c c' d d' : ℝ, a = a' → b = b' → c = c' → d = d' →
      a + b + c + d = a' + b' + c' + d' := by
    intro a a' b b' c c' d d' h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  refine h _ _ _ _ _ _ _ _ rfl rfl ?_ ?_
  · refine congrArg (fun s => f (s, μ)) ?_
    simp only [smul_neg, add_smul, one_smul]
    abel
  · refine congrArg (fun s => f (s, ν)) ?_
    simp only [smul_neg, add_smul, one_smul]
    abel
section Estimate
variable (hm : MeanProductEstimate)
include hm
theorem stepHolonomy_variance_and_direction (hL : Odd F.blockSide) {j : ℕ} (W : F.GaugeField j)
    (V : F.GaugeField (j + 1)) (y : F.Site (j + 1)) (st : PathStep) :
    variance (allContours F) (stepHolonomy W y st) = contourVariance W (stepBond y st) ∧
    ‖((linkValue V y st : UnitQuaternion) : ℍ[ℝ]) -
        meanDirection (allContours F) (stepHolonomy W y st)‖ ≤
      2 * Real.sqrt (blockFit W V (stepBond y st)) + 2 * contourVariance W (stepBond y st) := by
  obtain ⟨-, -, hinv, hfit⟩ := hm _ (allContours F) (allContours_nonempty hL)
  have hf := hfit (contourHolonomy W (stepBond y st)) (V (stepBond y st).1 (stepBond y st).2)
  rw [quatAverage_contourHolonomy hL] at hf
  obtain ⟨i, b⟩ := st
  cases b
  · obtain ⟨h1, h2⟩ := hinv (contourHolonomy W (stepBond y (i, false)))
    have e : stepHolonomy W y (i, false) =
        fun e => (contourHolonomy W (stepBond y (i, false)) e)⁻¹ := by
      funext e
      simp [stepHolonomy]
    rw [e]
    refine ⟨h2, ?_⟩
    rw [h1]
    have e2 : linkValue V y (i, false) =
        (V (stepBond y (i, false)).1 (stepBond y (i, false)).2)⁻¹ := by
      simp [linkValue, stepBond]
    rw [e2, norm_sub_inv_inv]
    exact hf
  · have e : stepHolonomy W y (i, true) = contourHolonomy W (stepBond y (i, true)) := by
      funext e
      simp [stepHolonomy]
    rw [e]
    refine ⟨rfl, ?_⟩
    have e2 : linkValue V y (i, true) = V (stepBond y (i, true)).1 (stepBond y (i, true)).2 := by
      simp [linkValue, stepBond]
    rw [e2]
    exact hf
theorem sum_variance_pathHolonomies (hL : Odd F.blockSide) {j : ℕ} (W : F.GaugeField j)
    (V : F.GaugeField (j + 1)) (l : List PathStep) :
    ∀ y, ((pathHolonomies W y l).map (variance (allContours F))).sum =
      bondSum (contourVariance W) y l := by
  induction l with
  | nil => intro y; simp [pathHolonomies, bondSum]
  | cons st r ih =>
    intro y
    simp only [pathHolonomies, List.map_cons, List.sum_cons, bondSum]
    rw [ih, (stepHolonomy_variance_and_direction hm hL W V y st).1]
theorem norm_pathHolonomy_sub_prodMeanDirections (hL : Odd F.blockSide) {j : ℕ}
    (W : F.GaugeField j) (V : F.GaugeField (j + 1)) (l : List PathStep) :
    ∀ y, ‖((pathHolonomy V y l : UnitQuaternion) : ℍ[ℝ]) -
        (prodMeanDirections (allContours F) (pathHolonomies W y l) : UnitQuaternion)‖ ≤
      bondSum (fun c => 2 * Real.sqrt (blockFit W V c) + 2 * contourVariance W c) y l := by
  induction l with
  | nil =>
    intro y
    simp [pathHolonomies, prodMeanDirections, pathHolonomy, bondSum]
  | cons st r ih =>
    intro y
    have e0 : prodMeanDirections (allContours F) (pathHolonomies W y (st :: r)) =
        meanDirection (allContours F) (stepHolonomy W y st) *
          prodMeanDirections (allContours F)
            (pathHolonomies W (y + stepDisplacement (j + 1) st) r) := by
      simp [prodMeanDirections, pathHolonomies]
    rw [e0]
    simp only [pathHolonomy, bondSum]
    set a := linkValue V y st
    set u := meanDirection (allContours F) (stepHolonomy W y st)
    set A := pathHolonomy V (y + stepDisplacement (j + 1) st) r
    set B := prodMeanDirections (allContours F) (pathHolonomies W (y + stepDisplacement (j + 1) st) r)
    have e1 : ((a * A : UnitQuaternion) : ℍ[ℝ]) - ((u * B : UnitQuaternion) : ℍ[ℝ]) =
        ((a : ℍ[ℝ]) - u) * (A : ℍ[ℝ]) + (u : ℍ[ℝ]) * ((A : ℍ[ℝ]) - B) := by
      rw [unitQuaternion_coe_mul, unitQuaternion_coe_mul]
      noncomm_ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul_unitQuaternion, norm_unitQuaternion_mul]
    exact add_le_add (stepHolonomy_variance_and_direction hm hL W V y st).2 (ih _)
omit hm in
theorem length_pathHolonomies {j : ℕ} (W : F.GaugeField j) (l : List PathStep) :
    ∀ y, (pathHolonomies W y l).length = l.length := by
  induction l with
  | nil => intro y; rfl
  | cons st r ih =>
    intro y
    simp [pathHolonomies, ih]
theorem squareHolonomyDefect_le (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide)
    (W : F.GaugeField j) (V : F.GaugeField (j + 1)) (x : F.Site (j + 1)) (n : ℕ) (μ ν : Fin 4) :
    squareHolonomyDefect V x n μ ν ≤
      average (centredCube F.blockSide)
          (fun h => squareHolonomyDefect W (refineSite x + siteOfCoords j h) (n * F.blockSide) μ ν) +
        sumAroundSquare (fun c => 2 * Real.sqrt (blockFit W V c) + 2 * contourVariance W c) x n μ ν +
        (2 * n : ℝ) * sumAroundSquare (contourVariance W) x n μ ν := by
  obtain ⟨hprod, -, -, -⟩ := hm _ (allContours F) (allContours_nonempty hL)
  have h1 := hprod (pathHolonomies W x (squarePath n μ ν))
  have h2 := norm_pathHolonomy_sub_prodMeanDirections hm hL W V (squarePath n μ ν) x
  have h3 : average (allContours F)
      (fun e => ‖((pointwiseProd (pathHolonomies W x (squarePath n μ ν)) e : UnitQuaternion) :
        ℍ[ℝ]) - 1‖) =
      average (centredCube F.blockSide)
        (fun h => squareHolonomyDefect W (refineSite x + siteOfCoords j h) (n * F.blockSide) μ ν) := by
    rw [← average_allContours_fst hL]
    congr 1
    funext e
    rw [pointwiseProd_pathHolonomies j hj, pathDisplacement_squarePath, add_zero,
      squarePath_flatMap_replicate, norm_conj_sub_one]
    rfl
  rw [h3, length_pathHolonomies, sum_variance_pathHolonomies hm hL W V, bondSum_squarePath] at h1
  rw [bondSum_squarePath] at h2
  have hlen : ((squarePath n μ ν).length : ℝ) / 2 = 2 * n := by
    simp only [squarePath, List.length_append, List.length_replicate]
    push_cast
    ring
  rw [hlen] at h1
  have e : squareHolonomyDefect V x n μ ν ≤
      ‖((pathHolonomy V x (squarePath n μ ν) : UnitQuaternion) : ℍ[ℝ]) -
        (prodMeanDirections (allContours F) (pathHolonomies W x (squarePath n μ ν)) :
          UnitQuaternion)‖ +
      ‖((prodMeanDirections (allContours F) (pathHolonomies W x (squarePath n μ ν)) :
          UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
    unfold squareHolonomyDefect
    refine le_trans (le_of_eq ?_) (norm_add_le _ _)
    congr 1
    abel
  linarith
end Estimate
end OneLevel
theorem squareDescentEstimate_of_meanProductEstimate (hm : MeanProductEstimate) :
    SquareDescentEstimate := by
  intro F j hj hL W V x n μ ν
  exact OneLevel.squareHolonomyDefect_le hm j hj hL W V x n μ ν
end YangMills.Construction.SquareDescent
end
