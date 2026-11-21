import YangMills.Construction.ClusterExpansionOfAStep.BlocksOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ClusterExpansionOfAStep.FitsAlongMoves
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusContours
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusPaths YangMills.Construction.TorusLumps YangMills.Construction.TorusBlocks YangMills.Construction.StepCosts YangMills.Construction.TopLevelSites
section Preliminaries
variable {m : ℕ}
def pathToWord : TorusSite m → List PathStep → BondWord m
  | _, [] => []
  | y, st :: r => if st.2 then ((y, st.1), true) :: pathToWord (y + TorusFields.unitStep m st.1) r
    else ((y - TorusFields.unitStep m st.1, st.1), false) :: pathToWord (y - TorusFields.unitStep m st.1) r
theorem length_pathToWord (y : TorusSite m) (l : List PathStep) : (pathToWord y l).length = l.length := by
  induction l generalizing y with
  | nil => rfl
  | cons st r ih =>
    obtain ⟨i, s⟩ := st
    cases s <;> simp [pathToWord, ih]
theorem pathHolonomy_readAtLevel {F : BlockFrame} {j : ℕ} [NeZero m] (hp : ∀ i, F.period j i = m)
    (W : TorusField m) (x : F.Site j) (l : List PathStep) :
    pathHolonomy (readAtLevel F j W) x l = wordHolonomy W (pathToWord (toTorusSite m x) l) := by
  have : ∀ i, NeZero (F.period j i) := period_neZero hp
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    obtain ⟨i, s⟩ := st
    have hsub : (toTorusSite m (x - BlockAverages.unitStep j i) : TorusSite m) =
        toTorusSite m x - TorusFields.unitStep m i := by
      rw [sub_eq_add_neg, toTorusSite_add hp, toTorusSite_neg hp, toTorusSite_unitStep hp, sub_eq_add_neg]
    cases s
    · have h1 : pathHolonomy (readAtLevel F j W) x ((i, false) :: r) =
          (W (toTorusSite m (x - BlockAverages.unitStep j i)) i)⁻¹ *
            pathHolonomy (readAtLevel F j W) (x - BlockAverages.unitStep j i) r := by
        simp [pathHolonomy, linkValue, stepDisplacement, sub_eq_add_neg]
        rfl
      rw [h1, ih, hsub]
      simp [pathToWord, wordHolonomy, orientedValue]
    · have h1 : pathHolonomy (readAtLevel F j W) x ((i, true) :: r) =
          W (toTorusSite m x) i * pathHolonomy (readAtLevel F j W) (x + BlockAverages.unitStep j i) r := by
        simp [pathHolonomy, linkValue, stepDisplacement]
        rfl
      rw [h1, ih, toTorusSite_add hp, toTorusSite_unitStep hp]
      simp [pathToWord, wordHolonomy, orientedValue]
theorem wordHolonomy_congr {W W' : TorusField m} (l : BondWord m)
    (h : ∀ e ∈ l, W e.1.1 e.1.2 = W' e.1.1 e.1.2) : wordHolonomy W l = wordHolonomy W' l := by
  induction l with
  | nil => rfl
  | cons e r ih =>
    show orientedValue e.2 _ * _ = orientedValue e.2 _ * _
    rw [h e List.mem_cons_self, ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]
variable [NeZero m]
theorem supDist_sub_unitStep_le (y : TorusSite m) (i : Fin 4) :
    supDist y (y - TorusFields.unitStep m i) ≤ 1 := by
  have h := supDist_add_unitStep_le (y - TorusFields.unitStep m i) i
  rw [sub_add_cancel] at h
  rwa [supDist_comm]
theorem supDist_le_length_of_mem_pathToWord (y : TorusSite m) (l : List PathStep) {e : TorusBond m × Bool}
    (he : e ∈ pathToWord y l) : supDist y e.1.1 ≤ l.length := by
  induction l generalizing y with
  | nil => simp [pathToWord] at he
  | cons st r ih =>
    obtain ⟨i, s⟩ := st
    cases s
    · simp only [pathToWord, Bool.false_eq_true, if_false, List.mem_cons] at he
      rcases he with rfl | he
      · have := supDist_sub_unitStep_le y i
        simp only [List.length_cons]
        omega
      · have h1 := ih (y - TorusFields.unitStep m i) he
        have h2 := supDist_sub_unitStep_le y i
        have h3 := supDist_triangle y (y - TorusFields.unitStep m i) e.1.1
        simp only [List.length_cons]
        omega
    · simp only [pathToWord, if_true, List.mem_cons] at he
      rcases he with rfl | he
      · simp [supDist_self]
      · have h1 := ih (y + TorusFields.unitStep m i) he
        have h2 := supDist_add_unitStep_le y i
        have h3 := supDist_triangle y (y + TorusFields.unitStep m i) e.1.1
        simp only [List.length_cons]
        omega
end Preliminaries
section Contour
variable {n : ℕ} [NeZero n]
def contourIndex (L : ℕ) : Finset ((Fin 4 → ℤ) × Equiv.Perm (Fin 4)) := centredCube L ×ˢ Finset.univ
def contourWord (L : ℕ) (Y : TorusSite n) (i : Fin 4) (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    BondWord (n * L) :=
  pathToWord (blockCentreSite L Y) (bondContour L e.1 e.2 i)
def contourWeight (L : ℕ) : ℝ := 1 / (24 * (L : ℝ) ^ 4)
def plainContourAverage (L : ℕ) (Y : TorusSite n) (i : Fin 4) (W : TorusField (n * L)) : ℍ[ℝ] :=
  wordAverage (contourWeight L) (contourIndex L) (contourWord L Y i) W
theorem length_axisPath_le (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) {H : ℕ} (hb : ∀ k, (h k).natAbs ≤ H) :
    (axisPath h π).length ≤ 4 * H := by
  have e : List.finRange 4 = [0, 1, 2, 3] := by decide
  have h0 := hb (π 0)
  have h1 := hb (π 1)
  have h2 := hb (π 2)
  have h3 := hb (π 3)
  simp only [axisPath, e, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_replicate,
    List.length_nil]
  omega
theorem length_bondContour_le {L : ℕ} (hL : Odd L) {h : Fin 4 → ℤ} (hh : h ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) : (bondContour L h π i).length ≤ 5 * L := by
  obtain ⟨q, hq⟩ := hL
  have hb : ∀ k, (h k).natAbs ≤ q := by
    intro k
    have := (mem_centredCube_iff.mp hh) k
    have hz : ((L : ℤ) - 1) / 2 = q := by
      subst hq
      push_cast
      omega
    rw [hz] at this
    omega
  have h1 := length_axisPath_le h π hb
  simp only [bondContour, reversePath, List.length_append, List.length_replicate, List.length_map,
    List.length_reverse]
  omega
omit [NeZero n] in
theorem length_contourWord_le {L : ℕ} (hL : Odd L) (Y : TorusSite n) (i : Fin 4)
    {e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)} (he : e ∈ contourIndex L) : (contourWord L Y i e).length ≤ 5 * L := by
  rw [contourWord, length_pathToWord]
  exact length_bondContour_le hL (Finset.mem_product.mp he).1 _ _
theorem card_centredCube {L : ℕ} (hL : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem card_contourIndex {L : ℕ} (hL : Odd L) : (contourIndex L).card = L ^ 4 * 24 := by
  unfold contourIndex
  rw [Finset.card_product, card_centredCube hL, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rfl
theorem contourWeight_mul_card {L : ℕ} (hL : Odd L) : contourWeight L * (contourIndex L).card = 1 := by
  have hL0 : (L : ℝ) ≠ 0 := by
    have := hL.pos
    positivity
  rw [card_contourIndex hL]
  unfold contourWeight
  push_cast
  field_simp
theorem contourWeight_nonneg (L : ℕ) : 0 ≤ contourWeight L := by
  unfold contourWeight
  positivity
variable {F : BlockFrame}
theorem toTorusSite_refineSite (hn : ∀ i, F.extent i = n) [NeZero (n * F.blockSide)] (Y : TorusSite n) :
    toTorusSite (n * F.blockSide) (refineSite (torusSiteInFrame F F.top Y) : F.Site F.depth) =
      blockCentreSite F.blockSide Y := by
  have : ∀ i, NeZero (F.period F.depth i) := period_neZero (period_depth_of_extent hn)
  unfold refineSite
  rw [toTorusSite_siteOfCoords (period_depth_of_extent hn)]
  unfold blockCentreSite
  congr 1
  funext k
  rw [siteCoords_torusSiteInFrame (period_top_of_extent hn)]
theorem contourAverage_readAtLevel (hn : ∀ i, F.extent i = n) [NeZero (n * F.blockSide)]
    (W : TorusField (n * F.blockSide)) (Y : TorusSite n) (i : Fin 4) :
    contourAverage (readAtLevel F F.depth W) (torusSiteInFrame F F.top Y, i) =
      plainContourAverage F.blockSide Y i W := by
  unfold contourAverage plainContourAverage wordAverage contourWeight
  congr 1
  unfold contourIndex
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
  show ((pathHolonomy (readAtLevel F F.depth W) (refineSite (torusSiteInFrame F F.top Y))
      (bondContour F.blockSide h π i) : UnitQuaternion) : ℍ[ℝ]) =
    ((wordHolonomy W (pathToWord (blockCentreSite F.blockSide Y) (bondContour F.blockSide h π i)) :
      UnitQuaternion) : ℍ[ℝ])
  rw [pathHolonomy_readAtLevel (period_depth_of_extent hn), toTorusSite_refineSite hn]
theorem blockFit_readAtLevel (hn : ∀ i, F.extent i = n) [NeZero (n * F.blockSide)]
    (W : TorusField (n * F.blockSide)) (V : TorusField n) (Y : TorusSite n) (i : Fin 4) :
    blockFit (readAtLevel F F.depth W) (readAtLevel F F.top V) (torusSiteInFrame F F.top Y, i) =
      alignmentDefect (V Y i) (plainContourAverage F.blockSide Y i W) := by
  unfold blockFit alignmentDefect
  rw [contourAverage_readAtLevel hn]
  have h : readAtLevel F F.top V (torusSiteInFrame F F.top Y) i = V Y i :=
    readAtLevel_torusSiteInFrame (period_top_of_extent hn) V Y i
  simp only [h]
end Contour
end YangMills.Construction.TorusContours
end
