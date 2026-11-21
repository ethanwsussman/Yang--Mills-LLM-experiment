import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.MeansOfAPotential
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfACarriedFormProof
import YangMills.Construction.ColdChainAtEveryLevel.DifferencesAreNearlyFlat
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapOnDifferences
import YangMills.Construction.ColdChainAtEveryLevel.NormsOfFunctionsOnCells
import YangMills.Construction.ColdChainAtEveryLevel.WeightChains
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.NearlyFlatDifferences
open BlockAverages GaugeMap LatticePaths PatchPoints LatticeFractionalIntegration
variable {F : BlockFrame}
theorem siteOfCoords_add_eq {j : ℕ} (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j a + siteOfCoords j b = siteOfCoords j fun i => a i + b i := by apply _root_.YangMills.Construction.BlockLines.siteOfCoords_add_fun <;> assumption
theorem siteOfCoords_siteCoords_eq {j : ℕ} (y : F.Site j) : siteOfCoords j (siteCoords y) = y := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem blockSide_pow_sub_eq {j : ℕ} (hj : j < F.top) :
    (F.blockSide : ℤ) ^ (F.top - j) = F.blockSide * (F.blockSide : ℤ) ^ (F.top - (j + 1)) := by apply _root_.YangMills.Construction.BlockLines.blockSide_pow_sub_eq <;> assumption
theorem refineSite_siteOfCoords {j : ℕ} (hj : j < F.top) (a : Fin 4 → ℤ) :
    refineSite (siteOfCoords (F := F) (j + 1) a) = siteOfCoords j fun i => (F.blockSide : ℤ) * a i := by apply _root_.YangMills.Construction.BlockLines.refineSite_siteOfCoords <;> assumption
theorem mem_centredCube (M : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube M ↔ ∀ i, -(((M : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem odd_pow_half (hodd : Odd F.blockSide) (e : ℕ) : ∃ k : ℕ, F.blockSide ^ e = 2 * k + 1 ∧
    (((F.blockSide ^ e : ℕ) : ℤ) - 1) / 2 = k ∧ (F.blockSide : ℤ) ^ e = 2 * (k : ℤ) + 1 := by apply _root_.YangMills.Construction.BlockLines.odd_pow_eq_two_mul_add_one <;> assumption
theorem refineSite_add_mem_sitesOfCells {S : Finset F.Cell} {j : ℕ} (hj : j < F.top)
    (hodd : Odd F.blockSide) (y : F.Site (j + 1)) (hy : y ∈ sitesOfCells S (j + 1)) (g : Fin 4 → ℤ)
    (hg : g ∈ centredCube F.blockSide) :
    refineSite y + siteOfCoords j g ∈ sitesOfCells S j := by apply _root_.YangMills.Construction.BlockLines.refineSite_add_mem_sitesOfCells <;> assumption
def halfBlockSide (F : BlockFrame) : ℤ := ((F.blockSide : ℤ) - 1) / 2
theorem refineSite_add_unitStep {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (i : Fin 4) :
    refineSite (y + unitStep (j + 1) i) =
      refineSite y + siteOfCoords j (fun l => if l = i then (F.blockSide : ℤ) else 0) := by
  have e : y + unitStep (j + 1) i =
      siteOfCoords (j + 1) (fun l => siteCoords y l + Pi.single (M := fun _ => ℤ) i 1 l) := by
    conv_lhs => rw [← siteOfCoords_siteCoords_eq y]
    simp only [unitStep]
    rw [siteOfCoords_add_eq]
  rw [e, refineSite_siteOfCoords hj]
  simp only [refineSite]
  rw [siteOfCoords_add_eq]
  congr 1
  funext l
  by_cases hl : l = i
  · subst hl; simp [mul_add]
  · simp [hl]
theorem refineSite_add_mem_of_bond {S : Finset F.Cell} {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide)
    (y : F.Site (j + 1)) (i : Fin 4) (hy : y ∈ sitesOfCells S (j + 1))
    (hy' : y + unitStep (j + 1) i ∈ sitesOfCells S (j + 1)) (g : Fin 4 → ℤ)
    (ho : ∀ l, l ≠ i → -halfBlockSide F ≤ g l ∧ g l ≤ halfBlockSide F) (h1 : -halfBlockSide F ≤ g i)
    (h2 : g i ≤ halfBlockSide F + F.blockSide) : refineSite y + siteOfCoords j g ∈ sitesOfCells S j := by
  have hcube : ∀ g' : Fin 4 → ℤ, (∀ l, -halfBlockSide F ≤ g' l ∧ g' l ≤ halfBlockSide F) →
      g' ∈ centredCube F.blockSide := by
    intro g' hg'
    rw [mem_centredCube]
    exact hg'
  by_cases hc : g i ≤ halfBlockSide F
  · refine refineSite_add_mem_sitesOfCells hj hodd y hy g (hcube g fun l => ?_)
    by_cases hl : l = i
    · subst hl; exact ⟨h1, hc⟩
    · exact ho l hl
  · have e : refineSite y + siteOfCoords j g = refineSite (y + unitStep (j + 1) i) +
        siteOfCoords j (fun l => g l - if l = i then (F.blockSide : ℤ) else 0) := by
      rw [refineSite_add_unitStep hj, add_assoc, siteOfCoords_add_eq]
      congr 2
      funext l
      ring
    rw [e]
    refine refineSite_add_mem_sitesOfCells hj hodd _ hy' _ (hcube _ fun l => ?_)
    obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_half hodd 1
    rw [pow_one] at hk1 hk2 hk3
    have hh : halfBlockSide F = k := hk2
    by_cases hl : l = i
    · subst hl
      simp only [if_true]
      rw [hh] at hc h2 ⊢
      omega
    · simp only [if_neg hl, sub_zero]
      exact ho l hl
theorem refineSite_add_smul_unitStep {j : ℕ} (y : F.Site (j + 1)) (i : Fin 4) (h : Fin 4 → ℤ) (r : ℕ) :
    refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i =
      refineSite y + siteOfCoords j (fun l => h l + if l = i then (r : ℤ) else 0) := by
  rw [add_assoc]
  congr 1
  funext l
  by_cases hl : l = i
  · subst hl
    simp [siteOfCoords, unitStep]
  · simp [siteOfCoords, unitStep, hl]
theorem mem_innerBonds_of_line {S : Finset F.Cell} {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide)
    (c : F.Site (j + 1) × Fin 4) (hc : c ∈ innerBonds S (j + 1)) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (r : ℕ) (hr : r < F.blockSide) :
    (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) ∈ innerBonds S j := by
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc ⊢
  rw [mem_centredCube] at hh
  have hh' : ∀ l, -halfBlockSide F ≤ h l ∧ h l ≤ halfBlockSide F := hh
  rw [refineSite_add_smul_unitStep]
  constructor
  · refine refineSite_add_mem_of_bond hj hodd c.1 c.2 hc.1 hc.2 _ (fun l hl => ?_) ?_ ?_
    · simpa [hl] using hh' l
    · simp only [if_true]; linarith [(hh' c.2).1]
    · simp only [if_true]; linarith [(hh' c.2).2]
  · have e : refineSite c.1 + siteOfCoords j (fun l => h l + if l = c.2 then (r : ℤ) else 0) +
        unitStep j c.2 =
        refineSite c.1 + siteOfCoords j (fun l => h l + if l = c.2 then ((r : ℤ) + 1) else 0) := by
      rw [add_assoc]
      congr 1
      simp only [unitStep]
      rw [siteOfCoords_add_eq]
      congr 1
      funext l
      by_cases hl : l = c.2
      · subst hl; simp; ring
      · simp [hl]
    rw [e]
    refine refineSite_add_mem_of_bond hj hodd c.1 c.2 hc.1 hc.2 _ (fun l hl => ?_) ?_ ?_
    · simpa [hl] using hh' l
    · simp only [if_true]; linarith [(hh' c.2).1]
    · simp only [if_true]; linarith [(hh' c.2).2]
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
variable {S : Finset F.Cell}
def lineBond {j : ℕ} (c : F.Site (j + 1) × Fin 4) (h : Fin 4 → ℤ) (r : ℕ) : F.Site j × Fin 4 :=
  (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2)
def lineMean {j : ℕ} (g : F.Site j × Fin 4 → ℝ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
    g (lineBond c h r)
theorem norm_parallelAverage_le (hL : 0 < F.blockSide) {j : ℕ} (R : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) :
    ‖parallelAverage R f c‖ ≤ lineMean (fun b => ‖f b.1 b.2‖) c := by
  simp only [parallelAverage, norm_smul, lineMean]
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
      adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
        (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)‖ ≤
      24 * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        ‖f (lineBond c h r).1 (lineBond c h r).2‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    refine le_trans (norm_sum_le _ _) ?_
    have h2 : ∀ π : Equiv.Perm (Fin 4), ‖∑ r ∈ Finset.range F.blockSide,
        adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
          (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)‖ ≤
        ∑ r ∈ Finset.range F.blockSide, ‖f (lineBond c h r).1 (lineBond c h r).2‖ := by
      intro π
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro r _
      rw [norm_adjointAction]
      rfl
    refine le_trans (Finset.sum_le_sum fun π _ => h2 π) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    simp [Nat.factorial]
  have h3 : ‖(1 / (24 * (F.blockSide : ℝ) ^ 4))‖ = 1 / (24 * (F.blockSide : ℝ) ^ 4) := by
    rw [Real.norm_of_nonneg (by positivity)]
  rw [h3]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        (24 * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
          ‖f (lineBond c h r).1 (lineBond c h r).2‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp
theorem adjointAction_mul (a b : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction (a * b) w = adjointAction a (adjointAction b w) := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_mul <;> assumption
theorem adjointAction_sub (g : UnitQuaternion) (a b : ℍ[ℝ]) :
    adjointAction g (a - b) = adjointAction g a - adjointAction g b := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (r : ℝ) (a : ℍ[ℝ]) :
    adjointAction g (r • a) = r • adjointAction g a := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem adjointAction_sum {ι : Type} (g : UnitQuaternion) (t : Finset ι) (f : ι → ℍ[ℝ]) :
    adjointAction g (∑ i ∈ t, f i) = ∑ i ∈ t, adjointAction g (f i) := by
  simp only [adjointAction, Finset.mul_sum, Finset.sum_mul]
theorem norm_adjointAction_sub_le (g : UnitQuaternion) (w : ℍ[ℝ]) :
    ‖adjointAction g w - w‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ * ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction_sub_le <;> assumption
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathHolonomy_append {j : ℕ} (X : F.GaugeField j) (l l' : List PathStep) :
    ∀ x, pathHolonomy X x (l ++ l') = pathHolonomy X x l * pathHolonomy X (x + pathDisplacement j l) l' := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_append <;> assumption
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem linkValue_reverse {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_reverse <;> assumption
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) :
    ∀ x, pathHolonomy X (x + pathDisplacement j l) (reversePath l) = (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_reversePath <;> assumption
theorem stepDisplacement_eq_siteOfCoords (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem pathDisplacement_axisPath (j : ℕ) (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
theorem pathDisplacement_replicate (j : ℕ) (i : Fin 4) (r : ℕ) :
    pathDisplacement (F := F) j (List.replicate r (i, true)) = (r : ℤ) • unitStep j i := by
  induction r with
  | zero => simp [pathDisplacement]
  | succ r ih =>
    have e : pathDisplacement (F := F) j (List.replicate (r + 1) (i, true)) =
        stepDisplacement j (i, true) + pathDisplacement j (List.replicate r (i, true)) := by
      simp [pathDisplacement, List.replicate_succ]
    rw [e, ih]
    simp only [stepDisplacement, if_true]
    push_cast
    rw [add_smul, one_smul, add_comm]
theorem line_far_end {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (i : Fin 4) (h : Lattice4) :
    refineSite y + siteOfCoords j h + (F.blockSide : ℤ) • unitStep j i =
      refineSite (y + unitStep (j + 1) i) + siteOfCoords j h := by
  rw [refineSite_add_unitStep hj]
  have e : (F.blockSide : ℤ) • unitStep (F := F) j i =
      siteOfCoords j (fun l => if l = i then (F.blockSide : ℤ) else 0) := by
    funext l
    by_cases hl : l = i
    · subst hl
      simp [siteOfCoords, unitStep]
    · simp [siteOfCoords, unitStep, hl]
  rw [e]
  abel
def legTransportMean {j : ℕ} (R : F.GaugeField j) (g : F.Site j → ℍ[ℝ]) (y : F.Site (j + 1)) : ℍ[ℝ] :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    adjointAction (pathHolonomy R (refineSite y) (axisPath h π)) (g (refineSite y + siteOfCoords j h))
def blockMean {E : Type} [AddCommMonoid E] [Module ℝ E] {j : ℕ} (f : F.Site j → E) (y : F.Site (j + 1)) : E :=
  (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, f (refineSite y + siteOfCoords j h)
def covDiff {j : ℕ} (R : F.GaugeField j) (g : F.Site j → ℍ[ℝ]) : F.Site j → Fin 4 → ℍ[ℝ] :=
  fun x i => adjointAction (R x i) (g (x + unitStep j i)) - g x
def farEndMean {j : ℕ} (R : F.GaugeField j) (g : F.Site j → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) : ℍ[ℝ] :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate F.blockSide (c.2, true)))
      (g (refineSite c.1 + siteOfCoords j h + (F.blockSide : ℤ) • unitStep j c.2))
theorem parallelAverage_covDiff {j : ℕ} (R : F.GaugeField j) (g : F.Site j → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (covDiff R g) c = farEndMean R g c - legTransportMean R g c.1 := by
  unfold parallelAverage farEndMean legTransportMean
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  set H : ℕ → UnitQuaternion := fun r =>
    pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)) with hH
  set a : ℕ → F.Site j := fun r => refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2 with ha
  have hstep : ∀ r, adjointAction (H r) (covDiff R g (a r) c.2) =
      adjointAction (H (r + 1)) (g (a (r + 1))) - adjointAction (H r) (g (a r)) := by
    intro r
    have e1 : H (r + 1) = H r * R (a r) c.2 := by
      simp only [hH]
      rw [List.replicate_succ', ← List.append_assoc, pathHolonomy_append]
      have e2 : refineSite c.1 + pathDisplacement j (axisPath h π ++ List.replicate r (c.2, true)) = a r := by
        rw [pathDisplacement_append, pathDisplacement_axisPath, pathDisplacement_replicate, ← add_assoc]
      rw [e2]
      simp [pathHolonomy, linkValue]
    have e3 : a (r + 1) = a r + unitStep j c.2 := by
      simp only [ha]
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e1, adjointAction_mul, e3]
    simp only [covDiff, adjointAction_sub]
  have hs : ∑ r ∈ Finset.range F.blockSide, adjointAction (H r) (covDiff R g (a r) c.2) =
      adjointAction (H F.blockSide) (g (a F.blockSide)) - adjointAction (H 0) (g (a 0)) := by
    simp only [hstep]
    exact Finset.sum_range_sub (fun r => adjointAction (H r) (g (a r))) F.blockSide
  have e0 : H 0 = pathHolonomy R (refineSite c.1) (axisPath h π) := by simp [hH]
  have e4 : a 0 = refineSite c.1 + siteOfCoords j h := by simp [ha]
  rw [e0, e4] at hs
  exact hs
theorem pathHolonomy_axisPath_append {j : ℕ} (hj : j < F.top) (R : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) (h : Lattice4) (π : Equiv.Perm (Fin 4)) :
    pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate F.blockSide (c.2, true)) =
      pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) *
        pathHolonomy R (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π) := by
  have e1 : refineSite c.1 + pathDisplacement j (axisPath h π ++ List.replicate F.blockSide (c.2, true)) =
      refineSite (c.1 + unitStep (j + 1) c.2) + pathDisplacement j (axisPath h π) := by
    rw [pathDisplacement_append, pathDisplacement_axisPath, pathDisplacement_replicate, ← add_assoc,
      line_far_end hj]
  have e2 : bondContour F.blockSide h π c.2 =
      (axisPath h π ++ List.replicate F.blockSide (c.2, true)) ++ reversePath (axisPath h π) := rfl
  rw [e2, pathHolonomy_append R (axisPath h π ++ List.replicate F.blockSide (c.2, true))
    (reversePath (axisPath h π)), e1, pathHolonomy_reversePath, mul_assoc, inv_mul_cancel, mul_one]
theorem sum_perm_const (t : ℝ) : ∑ _π : Equiv.Perm (Fin 4), t = 24 * t := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  simp [Nat.factorial]
theorem norm_farEndMean_sub_le (hL : 0 < F.blockSide) {j : ℕ} (hj : j < F.top) (R : F.GaugeField j)
    (g : F.Site j → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) (U : UnitQuaternion) (δ : ℝ)
    (hδ : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) * U⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖
        ≤ δ) :
    ‖farEndMean R g c - adjointAction U (legTransportMean R g (c.1 + unitStep (j + 1) c.2))‖ ≤
      2 * δ * blockMean (fun x => ‖g x‖) (c.1 + unitStep (j + 1) c.2) := by
  set y' := c.1 + unitStep (j + 1) c.2 with hy'
  have hterm : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate F.blockSide (c.2, true)))
          (g (refineSite c.1 + siteOfCoords j h + (F.blockSide : ℤ) • unitStep j c.2)) -
        adjointAction U (adjointAction (pathHolonomy R (refineSite y') (axisPath h π))
          (g (refineSite y' + siteOfCoords j h)))‖ ≤
        2 * δ * ‖g (refineSite y' + siteOfCoords j h)‖ := by
    intro h hh π
    rw [pathHolonomy_axisPath_append hj, line_far_end hj, adjointAction_mul, ← hy']
    set w := adjointAction U (adjointAction (pathHolonomy R (refineSite y') (axisPath h π))
      (g (refineSite y' + siteOfCoords j h))) with hw
    set G := pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) with hG
    have e : G = (G * U⁻¹) * U := by rw [mul_assoc, inv_mul_cancel, mul_one]
    have e2 : adjointAction G (adjointAction (pathHolonomy R (refineSite y') (axisPath h π))
        (g (refineSite y' + siteOfCoords j h))) = adjointAction (G * U⁻¹) w := by
      conv_lhs => rw [e]
      rw [adjointAction_mul]
    rw [e2]
    refine (norm_adjointAction_sub_le _ _).trans ?_
    have hnw : ‖w‖ = ‖g (refineSite y' + siteOfCoords j h)‖ := by
      rw [hw, norm_adjointAction, norm_adjointAction]
    rw [hnw]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hδ h hh π) (by norm_num)) (norm_nonneg _)
  have e0 : farEndMean R g c - adjointAction U (legTransportMean R g y') =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate F.blockSide (c.2, true)))
            (g (refineSite c.1 + siteOfCoords j h + (F.blockSide : ℤ) • unitStep j c.2)) -
          adjointAction U (adjointAction (pathHolonomy R (refineSite y') (axisPath h π))
            (g (refineSite y' + siteOfCoords j h)))) := by
    simp only [farEndMean, legTransportMean, adjointAction_smul, adjointAction_sum, Finset.sum_sub_distrib,
      smul_sub]
  rw [e0, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      (adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate F.blockSide (c.2, true)))
          (g (refineSite c.1 + siteOfCoords j h + (F.blockSide : ℤ) • unitStep j c.2)) -
        adjointAction U (adjointAction (pathHolonomy R (refineSite y') (axisPath h π))
          (g (refineSite y' + siteOfCoords j h))))‖ ≤
      ∑ h ∈ centredCube F.blockSide, 24 * (2 * δ * ‖g (refineSite y' + siteOfCoords j h)‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_perm_const]
    exact Finset.sum_le_sum fun π _ => hterm h hh π
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        ∑ h ∈ centredCube F.blockSide, 24 * (2 * δ * ‖g (refineSite y' + siteOfCoords j h)‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by
      simp only [blockMean, smul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      field_simp
theorem norm_legTransportMean_le (hL : 0 < F.blockSide) {j : ℕ} (R : F.GaugeField j) (g : F.Site j → ℍ[ℝ])
    (y : F.Site (j + 1)) :
    ‖legTransportMean R g y‖ ≤ blockMean (fun x => ‖g x‖) y := by
  unfold legTransportMean blockMean
  rw [norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      adjointAction (pathHolonomy R (refineSite y) (axisPath h π)) (g (refineSite y + siteOfCoords j h))‖ ≤
      ∑ h ∈ centredCube F.blockSide, 24 * ‖g (refineSite y + siteOfCoords j h)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_adjointAction]
    exact sum_perm_const _
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        ∑ h ∈ centredCube F.blockSide, 24 * ‖g (refineSite y + siteOfCoords j h)‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by
      rw [← Finset.mul_sum]
      field_simp
theorem blockMean_mono (hL : 0 < F.blockSide) {j : ℕ} {f f' : F.Site j → ℝ} (h : ∀ x, f x ≤ f' x)
    (y : F.Site (j + 1)) : blockMean f y ≤ blockMean f' y := by
  simp only [blockMean, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => h _) (by positivity)
theorem blockMean_nonneg (hL : 0 < F.blockSide) {j : ℕ} {f : F.Site j → ℝ} (h : ∀ x, 0 ≤ f x)
    (y : F.Site (j + 1)) : 0 ≤ blockMean f y := by
  simp only [blockMean, smul_eq_mul]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => h _)
def transportedMeans (R : F.FieldChain) (ξ : F.Site 0 → ℍ[ℝ]) : (j : ℕ) → F.Site j → ℍ[ℝ]
  | 0 => ξ
  | j + 1 => legTransportMean (R j) (transportedMeans R ξ j)
def iteratedMean {E : Type} [AddCommMonoid E] [Module ℝ E] (f : F.Site 0 → E) : (j : ℕ) → F.Site j → E
  | 0 => f
  | j + 1 => blockMean (iteratedMean f j)
theorem iteratedMean_nonneg (hL : 0 < F.blockSide) {f : F.Site 0 → ℝ} (h : ∀ x, 0 ≤ f x) :
    ∀ (j : ℕ) (y : F.Site j), 0 ≤ iteratedMean f j y
  | 0, y => h y
  | j + 1, y => blockMean_nonneg hL (iteratedMean_nonneg hL h j) y
theorem norm_transportedMeans_le (hL : 0 < F.blockSide) (R : F.FieldChain) (ξ : F.Site 0 → ℍ[ℝ]) :
    ∀ (j : ℕ) (y : F.Site j), ‖transportedMeans R ξ j y‖ ≤ iteratedMean (fun x => ‖ξ x‖) j y
  | 0, _ => le_rfl
  | j + 1, y => (norm_legTransportMean_le hL _ _ y).trans
      (blockMean_mono hL (norm_transportedMeans_le hL R ξ j) y)
theorem sum_shifted_block_le {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide) (f : F.Site j → ℝ)
    (hf : ∀ x, 0 ≤ f x) (y : F.Site (j + 1)) (i : Fin 4) (r : ℕ) (hr : r ≤ F.blockSide) :
    ∑ h ∈ centredCube F.blockSide, f (refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i) ≤
      ∑ h ∈ centredCube F.blockSide, f (refineSite y + siteOfCoords j h) +
        ∑ h ∈ centredCube F.blockSide, f (refineSite (y + unitStep (j + 1) i) + siteOfCoords j h) := by
  classical
  obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_half hodd 1
  rw [pow_one] at hk1 hk2 hk3
  set v : Lattice4 := fun l => if l = i then (r : ℤ) else 0 with hv
  set v' : Lattice4 := fun l => if l = i then (r : ℤ) - F.blockSide else 0 with hv'
  have hs1 : ∀ h : Lattice4, refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i =
      refineSite y + siteOfCoords j (h + v) := by
    intro h
    rw [refineSite_add_smul_unitStep]
    rfl
  have hs2 : ∀ h : Lattice4, refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i =
      refineSite (y + unitStep (j + 1) i) + siteOfCoords j (h + v') := by
    intro h
    rw [hs1, refineSite_add_unitStep hj, add_assoc, siteOfCoords_add_eq]
    congr 2
    funext l
    by_cases hl : l = i
    · subst hl
      simp only [hv, hv', Pi.add_apply, if_true]
      ring
    · simp [hv, hv', hl]
  rw [← Finset.sum_filter_add_sum_filter_not (centredCube F.blockSide) (fun h => h i + (r : ℤ) ≤ k)]
  refine add_le_add ?_ ?_
  · calc ∑ h ∈ (centredCube F.blockSide).filter (fun h => h i + (r : ℤ) ≤ k),
          f (refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i)
        = ∑ u ∈ ((centredCube F.blockSide).filter (fun h => h i + (r : ℤ) ≤ k)).image (fun h => h + v),
            f (refineSite y + siteOfCoords j u) := by
          rw [Finset.sum_image (fun a _ b _ e => add_right_cancel e)]
          exact Finset.sum_congr rfl fun h _ => by rw [hs1]
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hf _
          intro u hu
          obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hu
          obtain ⟨hc, hle⟩ := Finset.mem_filter.1 hh
          rw [mem_centredCube, hk2] at hc ⊢
          intro l
          have h1 := hc l
          by_cases hl : l = i
          · subst hl
            simp only [Pi.add_apply, hv, if_true]
            omega
          · simp only [Pi.add_apply, hv, if_neg hl, add_zero]
            exact h1
  · calc ∑ h ∈ (centredCube F.blockSide).filter (fun h => ¬ h i + (r : ℤ) ≤ k),
          f (refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i)
        = ∑ u ∈ ((centredCube F.blockSide).filter (fun h => ¬ h i + (r : ℤ) ≤ k)).image (fun h => h + v'),
            f (refineSite (y + unitStep (j + 1) i) + siteOfCoords j u) := by
          rw [Finset.sum_image (fun a _ b _ e => add_right_cancel e)]
          exact Finset.sum_congr rfl fun h _ => by rw [hs2]
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hf _
          intro u hu
          obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hu
          obtain ⟨hc, hle⟩ := Finset.mem_filter.1 hh
          rw [mem_centredCube, hk2] at hc ⊢
          intro l
          have h1 := hc l
          have hr' : (r : ℤ) ≤ F.blockSide := by exact_mod_cast hr
          by_cases hl : l = i
          · subst hl
            simp only [Pi.add_apply, hv', if_true]
            omega
          · simp only [Pi.add_apply, hv', if_neg hl, add_zero]
            exact h1
theorem lineMean_le_blockMeans {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide) (f : F.Site j → ℝ)
    (hf : ∀ x, 0 ≤ f x) (c : F.Site (j + 1) × Fin 4) (α : ℝ) (hα : 0 ≤ α) (a : F.Site j × Fin 4 → ℝ)
    (ha : ∀ h ∈ centredCube F.blockSide, ∀ r ∈ Finset.range F.blockSide, a (lineBond c h r) ≤
      α * (f (lineBond c h r).1 + f ((lineBond c h r).1 + unitStep j c.2))) :
    lineMean a c ≤
      2 * α * F.blockSide * (blockMean f c.1 + blockMean f (c.1 + unitStep (j + 1) c.2)) := by
  have hL := hodd.pos
  set B := ∑ h ∈ centredCube F.blockSide, f (refineSite c.1 + siteOfCoords j h) +
    ∑ h ∈ centredCube F.blockSide, f (refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j h) with hB
  have h1 : ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, a (lineBond c h r) ≤
      ∑ r ∈ Finset.range F.blockSide, α * (2 * B) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun r hr => ?_
    have hrl : r < F.blockSide := Finset.mem_range.1 hr
    have e1 := sum_shifted_block_le hj hodd f hf c.1 c.2 r hrl.le
    have e2 := sum_shifted_block_le hj hodd f hf c.1 c.2 (r + 1) hrl
    calc ∑ h ∈ centredCube F.blockSide, a (lineBond c h r)
        ≤ ∑ h ∈ centredCube F.blockSide, α * (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) +
            f (refineSite c.1 + siteOfCoords j h + ((r + 1 : ℕ) : ℤ) • unitStep j c.2)) := by
          refine Finset.sum_le_sum fun h hh => (ha h hh r hr).trans (le_of_eq ?_)
          have e : (lineBond c h r).1 + unitStep j c.2 =
              refineSite c.1 + siteOfCoords j h + ((r + 1 : ℕ) : ℤ) • unitStep j c.2 := by
            simp only [lineBond]
            push_cast
            rw [add_smul, one_smul, add_assoc]
          rw [e]
          rfl
      _ = α * (∑ h ∈ centredCube F.blockSide,
              f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) +
            ∑ h ∈ centredCube F.blockSide,
              f (refineSite c.1 + siteOfCoords j h + ((r + 1 : ℕ) : ℤ) • unitStep j c.2)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ α * (2 * B) := mul_le_mul_of_nonneg_left (by rw [hB]; linarith) hα
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have e3 : blockMean f c.1 + blockMean f (c.1 + unitStep (j + 1) c.2) = (1 / (F.blockSide : ℝ) ^ 4) * B := by
    simp only [blockMean, smul_eq_mul, hB]
    ring
  rw [e3]
  simp only [lineMean]
  calc 1 / (F.blockSide : ℝ) ^ 4 * _ ≤ 1 / (F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) * (α * (2 * B))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring
theorem parallelAverage_sub {j : ℕ} (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (fun x i => f x i - g x i) c = parallelAverage R f c - parallelAverage R g c := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.parallelAverage_sub <;> assumption
theorem levelScale_succ_eq (hL : 0 < F.blockSide) {j : ℕ} (hj : j < F.top) :
    levelScale F (j + 1) = F.blockSide * levelScale F j := by apply _root_.YangMills.Construction.CarriedCurl.levelScale_succ <;> assumption
theorem levelScale_top_eq_one : levelScale F F.top = 1 := by apply _root_.YangMills.Construction.ReferenceBounds.levelScale_top_eq_one <;> assumption
theorem zero_le_levelScale (j : ℕ) : 0 ≤ levelScale F j := by apply _root_.YangMills.Construction.ReferenceBounds.zero_le_levelScale <;> assumption
theorem levelScale_le_one_of_pos (hL : 0 < F.blockSide) (j : ℕ) : levelScale F j ≤ 1 := by
  have h1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  unfold levelScale
  exact pow_le_one₀ (by positivity) (by rw [div_le_one (by linarith)]; exact h1)
theorem linearPart_baseOnly_succ (R : F.FieldChain) (v : F.Site 0 → Fin 4 → imaginaryQuaternions) (j : ℕ)
    (y : F.Site (j + 1)) (i : Fin 4) :
    linearPart R (baseOnlyChart v) (j + 1) y i =
      parallelAverage (R j) (linearPart R (baseOnlyChart v) j) (y, i) := by
  simp [linearPart, baseOnlyChart]
theorem norm_linearPart_sub_covDiff_le (hodd : Odd F.blockSide) (h4 : 4 ≤ F.blockSide) {S : Finset F.Cell}
    (R : F.FieldChain) (ξ : F.Site 0 → ℍ[ℝ]) (v : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (hv : ∀ x i, ((v x i : imaginaryQuaternions) : ℍ[ℝ]) = covDiff (R 0) ξ x i) (κ : ℝ) (hκ : 0 ≤ κ)
    (hΔ : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
      ‖parallelAverage (R j) (covDiff (R j) (transportedMeans R ξ j)) c -
          covDiff (R (j + 1)) (transportedMeans R ξ (j + 1)) c.1 c.2‖ ≤
        κ * levelScale F (j + 1) ^ 2 * iteratedMean (fun x => ‖ξ x‖) (j + 1) (c.1 + unitStep (j + 1) c.2)) :
    ∀ j, j < F.top → ∀ b ∈ innerBonds S j,
      ‖linearPart R (baseOnlyChart v) j b.1 b.2 - covDiff (R j) (transportedMeans R ξ j) b.1 b.2‖ ≤
        2 * κ * levelScale F j ^ 2 *
          (iteratedMean (fun x => ‖ξ x‖) j b.1 + iteratedMean (fun x => ‖ξ x‖) j (b.1 + unitStep j b.2)) := by
  have hL := hodd.pos
  have hL4 : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast h4
  set gb := iteratedMean (F := F) (fun x => ‖ξ x‖) with hgb
  have hgb0 : ∀ j (y : F.Site j), 0 ≤ gb j y := iteratedMean_nonneg hL (fun x => norm_nonneg _)
  intro j
  induction j with
  | zero =>
    intro _ b _
    have e : linearPart R (baseOnlyChart v) 0 b.1 b.2 = covDiff (R 0) (transportedMeans R ξ 0) b.1 b.2 :=
      hv b.1 b.2
    rw [e, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (add_nonneg (hgb0 _ _) (hgb0 _ _))
  | succ j ih =>
    intro hj c hc
    have hj' : j < F.top := by omega
    have hstep := levelScale_succ_eq (F := F) hL hj'
    set e : F.Site j → Fin 4 → ℍ[ℝ] := fun x i =>
      linearPart R (baseOnlyChart v) j x i - covDiff (R j) (transportedMeans R ξ j) x i with he
    have e1 : linearPart R (baseOnlyChart v) (j + 1) c.1 c.2 -
        covDiff (R (j + 1)) (transportedMeans R ξ (j + 1)) c.1 c.2 =
        parallelAverage (R j) e c + (parallelAverage (R j) (covDiff (R j) (transportedMeans R ξ j)) c -
          covDiff (R (j + 1)) (transportedMeans R ξ (j + 1)) c.1 c.2) := by
      rw [linearPart_baseOnly_succ, he, parallelAverage_sub]
      abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have h2 := hΔ j hj c hc
    have h3 := norm_parallelAverage_le hL (R j) e c
    have h4' := lineMean_le_blockMeans hj' hodd (gb j) (hgb0 j) c (2 * κ * levelScale F j ^ 2) (by
        exact mul_nonneg (by positivity) (sq_nonneg _)) (fun b => ‖e b.1 b.2‖) (fun h hh r hr => by
        exact ih hj' _ (mem_innerBonds_of_line hj' hodd c hc h hh r (Finset.mem_range.1 hr)))
    have hgs : blockMean (gb j) c.1 = gb (j + 1) c.1 := rfl
    have hgs' : blockMean (gb j) (c.1 + unitStep (j + 1) c.2) = gb (j + 1) (c.1 + unitStep (j + 1) c.2) := rfl
    rw [hgs, hgs'] at h4'
    set A := gb (j + 1) c.1
    set B := gb (j + 1) (c.1 + unitStep (j + 1) c.2)
    have hA : 0 ≤ A := hgb0 _ _
    have hB : 0 ≤ B := hgb0 _ _
    have hcoef : 2 * (2 * κ * levelScale F j ^ 2) * (F.blockSide : ℝ) ≤ κ * levelScale F (j + 1) ^ 2 := by
      rw [hstep]
      have h5 : 0 ≤ κ * levelScale F j ^ 2 * (F.blockSide : ℝ) := by positivity
      nlinarith
    have h6 : 2 * (2 * κ * levelScale F j ^ 2) * (F.blockSide : ℝ) * (A + B) ≤
        κ * levelScale F (j + 1) ^ 2 * (A + B) :=
      mul_le_mul_of_nonneg_right hcoef (add_nonneg hA hB)
    have h7 : 0 ≤ κ * levelScale F (j + 1) ^ 2 := by positivity
    nlinarith [mul_nonneg h7 hA]
theorem zero_mem_centredCube {M : ℕ} (hM : 0 < M) : (0 : Lattice4) ∈ centredCube M := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.zero_mem_centredCube <;> assumption
theorem norm_parallelAverage_covDiff_sub_le (hL : 0 < F.blockSide) {j : ℕ} (hj : j + 1 < F.top)
    (R : F.FieldChain) (ξ : F.Site 0 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) (δ ε : ℝ) (hε : 0 ≤ ε)
    (hδ : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ)
    (hm : unitDeviation (referenceDefect R j c) ≤ ε) :
    ‖parallelAverage (R j) (covDiff (R j) (transportedMeans R ξ j)) c -
        covDiff (R (j + 1)) (transportedMeans R ξ (j + 1)) c.1 c.2‖ ≤
      (2 * δ + 2 * ε) * iteratedMean (fun x => ‖ξ x‖) (j + 1) (c.1 + unitStep (j + 1) c.2) := by
  set U := polarUnit (contourAverage (R j) c) with hU
  set y' := c.1 + unitStep (j + 1) c.2 with hy'
  set g := transportedMeans R ξ j with hg
  set G := transportedMeans R ξ (j + 1) with hG
  have hGe : G = legTransportMean (R j) g := rfl
  have hGb : ‖G y'‖ ≤ iteratedMean (fun x => ‖ξ x‖) (j + 1) y' := norm_transportedMeans_le hL R ξ (j + 1) y'
  have h1 := norm_farEndMean_sub_le hL (by omega : j < F.top) (R j) g c U δ hδ
  have h2 : blockMean (fun x => ‖g x‖) y' ≤ iteratedMean (fun x => ‖ξ x‖) (j + 1) y' :=
    blockMean_mono hL (norm_transportedMeans_le hL R ξ j) y'
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 (zero_mem_centredCube hL) 1)
  have e1 : R (j + 1) c.1 c.2 = referenceDefect R j c * U := by
    simp [referenceDefect, hU]
  have h3 : ‖adjointAction U (G y') - adjointAction (R (j + 1) c.1 c.2) (G y')‖ ≤ 2 * ε * ‖G y'‖ := by
    rw [e1, adjointAction_mul, norm_sub_rev]
    refine (norm_adjointAction_sub_le _ _).trans ?_
    rw [norm_adjointAction]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) (norm_nonneg _)
  have e2 : parallelAverage (R j) (covDiff (R j) g) c - covDiff (R (j + 1)) G c.1 c.2 =
      (farEndMean (R j) g c - adjointAction U (G y')) +
        (adjointAction U (G y') - adjointAction (R (j + 1) c.1 c.2) (G y')) := by
    rw [parallelAverage_covDiff]
    simp only [covDiff]
    rw [← hy', ← hGe]
    abel
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  have h1' : ‖farEndMean (R j) g c - adjointAction U (G y')‖ ≤ 2 * δ * blockMean (fun x => ‖g x‖) y' := by
    rw [hGe]
    exact h1
  have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * δ)
  have h5 := mul_le_mul_of_nonneg_left hGb (by positivity : 0 ≤ 2 * ε)
  linarith
theorem norm_parallelAverage_covDiff_top_le (hL : 0 < F.blockSide) (R : F.FieldChain) (ξ : F.Site 0 → ℍ[ℝ])
    (c : F.Site F.top × Fin 4) (δ : ℝ)
    (hδ : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (R F.depth) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R F.depth) c))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ) :
    ‖parallelAverage (R F.depth) (covDiff (R F.depth) (transportedMeans R ξ F.depth)) c‖ ≤
      ‖transportedMeans R ξ F.top c.1‖ + ‖transportedMeans R ξ F.top (c.1 + unitStep F.top c.2)‖ +
        2 * δ * iteratedMean (fun x => ‖ξ x‖) F.top (c.1 + unitStep F.top c.2) := by
  set U := polarUnit (contourAverage (R F.depth) c) with hU
  set y' := c.1 + unitStep F.top c.2 with hy'
  set g := transportedMeans R ξ F.depth with hg
  have hGe : transportedMeans R ξ F.top = legTransportMean (R F.depth) g := rfl
  have h1 := norm_farEndMean_sub_le hL (Nat.lt_succ_self F.depth) (R F.depth) g c U δ hδ
  have h2 : blockMean (fun x => ‖g x‖) y' ≤ iteratedMean (fun x => ‖ξ x‖) F.top y' :=
    blockMean_mono hL (norm_transportedMeans_le hL R ξ F.depth) y'
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 (zero_mem_centredCube hL) 1)
  rw [parallelAverage_covDiff]
  have e : farEndMean (R F.depth) g c - legTransportMean (R F.depth) g c.1 =
      (farEndMean (R F.depth) g c - adjointAction U (legTransportMean (R F.depth) g y')) +
        (adjointAction U (legTransportMean (R F.depth) g y') - legTransportMean (R F.depth) g c.1) := by abel
  rw [e, hGe]
  refine (norm_add_le _ _).trans ?_
  have h3 : ‖adjointAction U (legTransportMean (R F.depth) g y') - legTransportMean (R F.depth) g c.1‖ ≤
      ‖legTransportMean (R F.depth) g c.1‖ + ‖legTransportMean (R F.depth) g y'‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_adjointAction, add_comm]
  have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * δ)
  linarith
def InCell (z : F.Cell) (j : ℕ) (x : F.Site j) : Prop :=
  ∃ q ∈ centredCube (F.blockSide ^ (F.top - j)), x = cellCentre j z + siteOfCoords j q
theorem inCell_refineSite_add (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top) {z : F.Cell}
    {y : F.Site (j + 1)} (hy : InCell z (j + 1) y) {g : Lattice4} (hg : g ∈ centredCube F.blockSide) :
    InCell z j (refineSite y + siteOfCoords j g) := by
  obtain ⟨h', hh', rfl⟩ := hy
  refine ⟨fun i => (F.blockSide : ℤ) * h' i + g i, ?_, ?_⟩
  · obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_half hodd 1
    obtain ⟨k', hk1', hk2', hk3'⟩ := odd_pow_half hodd (F.top - (j + 1))
    obtain ⟨K, hK1, hK2, hK3⟩ := odd_pow_half hodd (F.top - j)
    rw [pow_one] at hk1 hk2 hk3
    rw [mem_centredCube] at hg hh' ⊢
    rw [hk2] at hg
    rw [hk2'] at hh'
    rw [hK2]
    have hrel : (K : ℤ) = (F.blockSide : ℤ) * k' + k := by
      have e := blockSide_pow_sub_eq (F := F) hj
      rw [hK3, hk3', hk3] at e
      rw [hk3]
      have : 2 * (K : ℤ) = 2 * ((2 * (k : ℤ) + 1) * k' + k) := by nlinarith
      omega
    intro i
    have h1 := hg i
    have h2 := hh' i
    rw [hrel]
    constructor
    · nlinarith [h1.1, h2.1]
    · nlinarith [h1.2, h2.2]
  · have e1 : cellCentre (j + 1) z + siteOfCoords (j + 1) h' =
        siteOfCoords (F := F) (j + 1)
          (fun i => (F.blockSide : ℤ) ^ (F.top - (j + 1)) * siteCoords z i + h' i) := by
      simp only [cellCentre]
      rw [siteOfCoords_add_eq]
    rw [e1, refineSite_siteOfCoords hj]
    simp only [cellCentre]
    rw [siteOfCoords_add_eq, siteOfCoords_add_eq]
    congr 1
    funext i
    rw [blockSide_pow_sub_eq hj]
    ring
theorem inCell_mem_sitesOfCells {S : Finset F.Cell} {z : F.Cell} (hz : z ∈ S) {j : ℕ} {x : F.Site j}
    (hx : InCell z j x) : x ∈ sitesOfCells S j := by
  obtain ⟨q, hq, rfl⟩ := hx
  exact mem_sitesOfCells.2 ⟨z, hz, q, hq, rfl⟩
theorem inCell_baseSite_mem_patch {S : Finset F.Cell} {z : F.Cell} (hz : z ∈ S)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : InCell z j x) :
    baseSite x ∈ (patchDomain S z).image (patchSite S z) := by
  classical
  obtain ⟨q, hq, rfl⟩ := hx
  have hb : baseSite (cellCentre j z + siteOfCoords j q) =
      cellCentre 0 z + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ j * q i) := by
    rw [baseSite_add j hj, baseSite_cellCentre j hj]
  have hc : (fun i => (F.blockSide : ℤ) ^ j * q i) ∈ centredCube (F.blockSide ^ F.top) := by
    obtain ⟨p, hp1, hp2, hp3⟩ := odd_pow_half hodd j
    obtain ⟨m, hm1, hm2, hm3⟩ := odd_pow_half hodd (F.top - j)
    obtain ⟨M, hM1, hM2, hM3⟩ := odd_pow_half hodd F.top
    rw [mem_centredCube] at hq ⊢
    rw [hm2] at hq
    rw [hM2]
    have hrel : (M : ℤ) = (F.blockSide : ℤ) ^ j * m + p := by
      have e : (F.blockSide : ℤ) ^ F.top = (F.blockSide : ℤ) ^ j * (F.blockSide : ℤ) ^ (F.top - j) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hM3, hm3, hp3] at e
      rw [hp3]
      have : 2 * (M : ℤ) = 2 * ((2 * (p : ℤ) + 1) * m + p) := by nlinarith
      omega
    intro i
    have h1 := hq i
    have hp0 : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ j := by positivity
    rw [hrel]
    have a1 : (F.blockSide : ℤ) ^ j * (-(m : ℤ)) ≤ (F.blockSide : ℤ) ^ j * q i :=
      mul_le_mul_of_nonneg_left h1.1 hp0
    have a2 : (F.blockSide : ℤ) ^ j * q i ≤ (F.blockSide : ℤ) ^ j * m := mul_le_mul_of_nonneg_left h1.2 hp0
    have hpp : (0 : ℤ) ≤ p := by positivity
    constructor
    · nlinarith
    · nlinarith
  rw [hb]
  refine Finset.mem_image.2 ⟨_, patchChart_mem_patchDomain hamb hodd he hz (by simp [cellSupDist]) hc, ?_⟩
  exact patchSite_patchChart he _
theorem linkValue_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (x : F.Site j)
    (st : PathStep) :
    linkValue (gaugeTransform γ X) x st = γ x * linkValue X x st * (γ (x + stepDisplacement j st))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_gaugeTransform <;> assumption
theorem pathHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (l : List PathStep) :
    ∀ x, pathHolonomy (gaugeTransform γ X) x l =
      γ x * pathHolonomy X x l * (γ (x + pathDisplacement j l))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_gaugeTransform <;> assumption
theorem baseSite_siteOfCoords {j : ℕ} (hj : j ≤ F.top) (t : Fin 4 → ℤ) :
    baseSite (siteOfCoords (F := F) j t) = siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ j * t i) := by apply _root_.YangMills.Construction.WeightedAverages.Chains.baseSite_siteOfCoords <;> assumption
theorem baseSite_refineSite_eq {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) :
    baseSite (refineSite y) = baseSite y := by
  have e : refineSite y = siteOfCoords j (fun i => (F.blockSide : ℤ) * siteCoords y i) := rfl
  rw [e, baseSite_siteOfCoords hj.le]
  simp only [baseSite]
  congr 1
  funext i
  rw [pow_succ]
  ring
theorem baseSite_zero_level (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem siteOfCoords_add_step (j : ℕ) (u : Lattice4) (st : PathStep) :
    siteOfCoords (F := F) j (u + FlatPairing.stepDisplacement st) =
      siteOfCoords j u + stepDisplacement j st := by
  rw [stepDisplacement_eq_siteOfCoords, siteOfCoords_add_eq]
  rfl
theorem norm_pathHolonomy_sub_one_le {j : ℕ} (X : F.GaugeField j) (x0 : F.Site j) (P : Lattice4 → Prop)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ u, P u → ∀ st, P (u + FlatPairing.stepDisplacement st) →
      ‖((linkValue X (x0 + siteOfCoords j u) st : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) :
    ∀ (l : List PathStep) (u : Lattice4), AllAlong P u l →
      ‖((pathHolonomy X (x0 + siteOfCoords j u) l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by
  intro l
  induction l with
  | nil =>
    intro u _
    simp [pathHolonomy]
  | cons st r ih =>
    intro u hu
    simp only [pathHolonomy]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    have h1 := hstep u hu.1 st (allAlong_head hu.2)
    have h2 := ih (u + FlatPairing.stepDisplacement st) hu.2
    rw [siteOfCoords_add_step, ← add_assoc] at h2
    simp only [List.length_cons]
    push_cast
    linarith
theorem norm_axisPath_holonomy_sub_one_le {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
    (hz : z ∈ S) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ} (hj : j < F.top) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hB : ∀ b ∈ innerBonds S j, baseSite b.1 ∈ (patchDomain S z).image (patchSite S z) →
      baseSite (b.1 + unitStep j b.2) ∈ (patchDomain S z).image (patchSite S z) →
      unitDeviation (referenceInPatchFrame S V z j b.1 b.2) ≤ ε)
    {y : F.Site (j + 1)} (hy : InCell z (j + 1) y) {h : Lattice4} (hh : h ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) :
    ‖((pathHolonomy (referenceInPatchFrame S V z j) (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ])
      - 1‖ ≤ 2 * F.blockSide * ε := by
  obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_half hodd 1
  rw [pow_one] at hk1 hk2 hk3
  have hcube : ∀ u : Lattice4, BetweenOrigin h u → u ∈ centredCube F.blockSide := by
    intro u hu
    rw [mem_centredCube, hk2] at hh ⊢
    intro μ
    have h1 := hh μ
    have h2 := hu μ
    have a1 : -(k : ℤ) ≤ min 0 (h μ) := le_min (by omega) h1.1
    have a2 : max 0 (h μ) ≤ k := max_le (by omega) h1.2
    exact ⟨a1.trans h2.1, h2.2.trans a2⟩
  have hsite : ∀ u, BetweenOrigin h u → InCell z j (refineSite y + siteOfCoords j u) :=
    fun u hu => inCell_refineSite_add hodd hj hy (hcube u hu)
  have hbond : ∀ (a : F.Site j) (i : Fin 4), InCell z j a → InCell z j (a + unitStep j i) →
      unitDeviation (referenceInPatchFrame S V z j a i) ≤ ε := by
    intro a i ha ha'
    refine hB (a, i) ?_ (inCell_baseSite_mem_patch hz hamb hodd he hj.le ha)
      (inCell_baseSite_mem_patch hz hamb hodd he hj.le ha')
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨inCell_mem_sitesOfCells hz ha, inCell_mem_sitesOfCells hz ha'⟩
  have key := norm_pathHolonomy_sub_one_le (referenceInPatchFrame S V z j) (refineSite y) (BetweenOrigin h) ε hε
    (fun u hu st hu' => by
    have ha := hsite u hu
    have ha' := hsite _ hu'
    rw [siteOfCoords_add_step, ← add_assoc] at ha'
    obtain ⟨i, b⟩ := st
    cases b
    · have e : refineSite y + siteOfCoords j u + stepDisplacement j (i, false) + unitStep j i =
          refineSite y + siteOfCoords j u := by
        simp [stepDisplacement]
      have := hbond _ i ha' (by rw [e]; exact ha)
      have e2 : refineSite y + siteOfCoords j u + stepDisplacement j (i, false) =
          refineSite y + siteOfCoords j u - unitStep j i := by
        simp [stepDisplacement, sub_eq_add_neg]
      rw [e2] at this
      simp only [linkValue, Bool.false_eq_true, if_false]
      rw [norm_coe_inv_sub_one]
      exact this
    · simp only [linkValue, if_true]
      exact hbond _ i ha (by simpa [stepDisplacement] using ha')) (axisPath h π) 0 (axisPath_spec h π).1
  have e0 : siteOfCoords (F := F) j (0 : Lattice4) = 0 := by
    funext i
    simp [siteOfCoords]
  rw [e0, add_zero] at key
  refine key.trans (mul_le_mul_of_nonneg_right ?_ hε)
  have hlen : (axisPath h π).length ≤ 2 * F.blockSide := by
    rw [length_axisPath]
    rw [mem_centredCube, hk2] at hh
    have b : ∀ i, (h i).natAbs ≤ k := fun i => by
      have := hh i
      omega
    have b0 := b (π 0)
    have b1 := b (π 1)
    have b2 := b (π 2)
    have b3 := b (π 3)
    omega
  exact_mod_cast hlen
def inCellFrame (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) {j : ℕ} (g : F.Site j → ℍ[ℝ])
    (y : F.Site j) : ℍ[ℝ] :=
  adjointAction (frameChange S V z (baseSite y))⁻¹ (g y)
theorem norm_inCellFrame (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) {j : ℕ}
    (g : F.Site j → ℍ[ℝ]) (y : F.Site j) :
    ‖inCellFrame S V z g y‖ = ‖g y‖ := norm_adjointAction _ _
theorem blockMean_eq_sum_perm (hL : 0 < F.blockSide) {j : ℕ} (G : F.Site j → ℍ[ℝ]) (y : F.Site (j + 1)) :
    blockMean G y = (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), G (refineSite y + siteOfCoords j h) := by
  have hLR : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : ∀ w : ℍ[ℝ], ∑ _π : Equiv.Perm (Fin 4), w = (24 : ℝ) • w := by
    intro w
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
    simp [Nat.factorial]
  simp only [e, blockMean]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  field_simp
theorem norm_inCellFrame_legTransportMean_sub_le {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
    (hL : 0 < F.blockSide) {j : ℕ} (hj : j < F.top) (g : F.Site j → ℍ[ℝ]) (y : F.Site (j + 1)) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hleg : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (referenceInPatchFrame S V z j) (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ])
        - 1‖ ≤ ε) :
    ‖inCellFrame S V z (legTransportMean (referenceFieldChain S V j) g) y -
        blockMean (inCellFrame S V z g) y‖ ≤
      2 * ε * blockMean (fun x => ‖g x‖) y := by
  set γ : F.Site j → UnitQuaternion := fun x => (frameChange S V z (baseSite x))⁻¹ with hγ
  have hT : ∀ (h : Lattice4) (π : Equiv.Perm (Fin 4)),
      adjointAction (frameChange S V z (baseSite y))⁻¹
          (adjointAction (pathHolonomy (referenceFieldChain S V j) (refineSite y) (axisPath h π))
            (g (refineSite y + siteOfCoords j h))) =
        adjointAction (pathHolonomy (referenceInPatchFrame S V z j) (refineSite y) (axisPath h π))
          (inCellFrame S V z g (refineSite y + siteOfCoords j h)) := by
    intro h π
    have e1 : pathHolonomy (referenceInPatchFrame S V z j) (refineSite y) (axisPath h π) =
        γ (refineSite y) * pathHolonomy (referenceFieldChain S V j) (refineSite y) (axisPath h π) *
          (γ (refineSite y + siteOfCoords j h))⁻¹ := by
      have := pathHolonomy_gaugeTransform γ (referenceFieldChain S V j) (axisPath h π) (refineSite y)
      rw [pathDisplacement_axisPath] at this
      exact this
    have e2 : (frameChange S V z (baseSite y))⁻¹ = γ (refineSite y) := by
      simp only [hγ]
      rw [baseSite_refineSite_eq hj]
    have e3 : inCellFrame S V z g (refineSite y + siteOfCoords j h) =
        adjointAction (γ (refineSite y + siteOfCoords j h)) (g (refineSite y + siteOfCoords j h)) := rfl
    rw [e1, e2, e3, ← adjointAction_mul, ← adjointAction_mul]
    congr 1
    group
  have e0 : inCellFrame S V z (legTransportMean (referenceFieldChain S V j) g) y -
      blockMean (inCellFrame S V z g) y =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (adjointAction (pathHolonomy (referenceInPatchFrame S V z j) (refineSite y) (axisPath h π))
            (inCellFrame S V z g (refineSite y + siteOfCoords j h)) -
          inCellFrame S V z g (refineSite y + siteOfCoords j h)) := by
    rw [blockMean_eq_sum_perm hL]
    simp only [inCellFrame, legTransportMean, adjointAction_smul, adjointAction_sum, Finset.sum_sub_distrib,
      smul_sub]
    congr 1
    refine congrArg _ (Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_)
    exact hT h π
  rw [e0, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      (adjointAction (pathHolonomy (referenceInPatchFrame S V z j) (refineSite y) (axisPath h π))
          (inCellFrame S V z g (refineSite y + siteOfCoords j h)) -
        inCellFrame S V z g (refineSite y + siteOfCoords j h))‖ ≤
      ∑ h ∈ centredCube F.blockSide, 24 * (2 * ε * ‖g (refineSite y + siteOfCoords j h)‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_perm_const]
    refine Finset.sum_le_sum fun π _ => (norm_adjointAction_sub_le _ _).trans ?_
    rw [norm_inCellFrame]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hleg h ‹_› π) (by norm_num)) (norm_nonneg _)
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        ∑ h ∈ centredCube F.blockSide, 24 * (2 * ε * ‖g (refineSite y + siteOfCoords j h)‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by
      simp only [blockMean, smul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      field_simp
theorem norm_inCellFrame_transportedMeans_sub_le {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
    (hz : z ∈ S) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hB : ∀ j, j < F.top → ∀ b ∈ innerBonds S j, baseSite b.1 ∈ (patchDomain S z).image (patchSite S z) →
      baseSite (b.1 + unitStep j b.2) ∈ (patchDomain S z).image (patchSite S z) →
      unitDeviation (referenceInPatchFrame S V z j b.1 b.2) ≤ κ * levelScale F j) (ξ : F.Site 0 → ℍ[ℝ]) :
    ∀ j, j ≤ F.top → ∀ y, InCell z j y →
      ‖inCellFrame S V z (transportedMeans (referenceFieldChain S V) ξ j) y -
          iteratedMean (fun x => adjointAction (frameChange S V z x)⁻¹ (ξ x)) j y‖ ≤
        4 * F.blockSide * κ * levelScale F j * iteratedMean (fun x => ‖ξ x‖) j y := by
  have hL := hodd.pos
  have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h2
  set R := referenceFieldChain S V with hR
  set φ₀ : F.Site 0 → ℍ[ℝ] := fun x => adjointAction (frameChange S V z x)⁻¹ (ξ x) with hφ₀
  set gb := iteratedMean (F := F) (fun x => ‖ξ x‖) with hgb
  have hgb0 : ∀ j (y : F.Site j), 0 ≤ gb j y := iteratedMean_nonneg hL (fun x => norm_nonneg _)
  intro j
  induction j with
  | zero =>
    intro _ y _
    have e : inCellFrame S V z (transportedMeans R ξ 0) y = iteratedMean φ₀ 0 y := by
      simp only [inCellFrame, transportedMeans, iteratedMean, hφ₀, baseSite_zero_level]
    rw [e, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (zero_le_levelScale _)) (hgb0 _ _)
  | succ j ih =>
    intro hj y hy
    have hj' : j < F.top := by omega
    have hlj := zero_le_levelScale (F := F) j
    have hstep := levelScale_succ_eq (F := F) hL hj'
    set g := transportedMeans R ξ j with hg
    have hle : 0 ≤ 2 * (F.blockSide : ℝ) * (κ * levelScale F j) := by positivity
    have s1 := norm_inCellFrame_legTransportMean_sub_le (S := S) (V := V) (z := z) hL hj' g y
      (2 * F.blockSide * (κ * levelScale F j)) hle
      (fun h hh π => norm_axisPath_holonomy_sub_one_le hz hamb hodd he hj' _ (by positivity) (hB j hj') hy hh π)
    have s2 : blockMean (fun x => ‖g x‖) y ≤ gb (j + 1) y :=
      blockMean_mono hL (norm_transportedMeans_le hL R ξ j) y
    have s3 : ‖blockMean (inCellFrame S V z g) y - blockMean (iteratedMean φ₀ j) y‖ ≤
        4 * F.blockSide * κ * levelScale F j * gb (j + 1) y := by
      have e : blockMean (inCellFrame S V z g) y - blockMean (iteratedMean φ₀ j) y =
          (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide,
            (inCellFrame S V z g (refineSite y + siteOfCoords j h) -
              iteratedMean φ₀ j (refineSite y + siteOfCoords j h)) := by
        simp only [blockMean, Finset.sum_sub_distrib, smul_sub]
      rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
      have h1 : ‖∑ h ∈ centredCube F.blockSide, (inCellFrame S V z g (refineSite y + siteOfCoords j h) -
          iteratedMean φ₀ j (refineSite y + siteOfCoords j h))‖ ≤
          ∑ h ∈ centredCube F.blockSide,
            4 * F.blockSide * κ * levelScale F j * gb j (refineSite y + siteOfCoords j h) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh =>
          ih hj'.le _ (inCell_refineSite_add hodd hj' hy hh))
      calc 1 / (F.blockSide : ℝ) ^ 4 * _ ≤ 1 / (F.blockSide : ℝ) ^ 4 *
            ∑ h ∈ centredCube F.blockSide,
              4 * F.blockSide * κ * levelScale F j * gb j (refineSite y + siteOfCoords j h) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by
          have : gb (j + 1) y = (1 / (F.blockSide : ℝ) ^ 4) *
              ∑ h ∈ centredCube F.blockSide, gb j (refineSite y + siteOfCoords j h) := rfl
          rw [this, ← Finset.mul_sum]
          ring
    have e4 : inCellFrame S V z (transportedMeans R ξ (j + 1)) y - iteratedMean φ₀ (j + 1) y =
        (inCellFrame S V z (legTransportMean (R j) g) y - blockMean (inCellFrame S V z g) y) +
          (blockMean (inCellFrame S V z g) y - blockMean (iteratedMean φ₀ j) y) := by
      have : transportedMeans R ξ (j + 1) = legTransportMean (R j) g := rfl
      rw [this]
      have : iteratedMean φ₀ (j + 1) y = blockMean (iteratedMean φ₀ j) y := rfl
      rw [this]
      abel
    rw [e4]
    refine (norm_add_le _ _).trans ?_
    have s4 := mul_le_mul_of_nonneg_left s2
      (by positivity : 0 ≤ 2 * (2 * (F.blockSide : ℝ) * (κ * levelScale F j)))
    have hG := hgb0 (j + 1) y
    have hfin : 8 * (F.blockSide : ℝ) * κ * levelScale F j ≤ 4 * F.blockSide * κ * levelScale F (j + 1) := by
      rw [hstep]
      have : 0 ≤ 4 * (F.blockSide : ℝ) * κ * levelScale F j := by positivity
      nlinarith
    have h6 := mul_le_mul_of_nonneg_right hfin hG
    nlinarith
theorem natAbs_valMinAbs_intCast_le (n : ℕ) (d : ℤ) : ((d : ZMod n).valMinAbs).natAbs ≤ d.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem scaleRadius_pos (hL : 0 < F.blockSide) (j : ℕ) (p : F.Site 0) (x : F.Site j) :
    0 < scaleRadius F j p x := by apply _root_.YangMills.Construction.CoordinateSeminorms.scaleRadius_pos <;> assumption
theorem pow_le_scaleRadius {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (p : F.Site 0) (x : F.Site l) :
    (F.blockSide : ℝ) ^ l ≤ scaleRadius F l p x := by apply _root_.YangMills.Construction.WeightedAverages.Chains.pow_le_scaleRadius <;> assumption
theorem card_scaleRadius_lt_le {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (X : Finset (F.Site l))
    (p : F.Site 0) (m : ℕ) (hm : 2 ^ m * F.blockSide ^ l ≤ F.blockSide ^ F.top) :
    ((X.filter fun x => scaleRadius F l p x < ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ)).card : ℝ) ≤
      81 * 16 ^ m := by apply _root_.YangMills.Construction.WeightedAverages.Chains.card_scaleRadius_lt <;> assumption
theorem sum_inv_scaleRadius_le {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (X : Finset (F.Site l))
    (p : F.Site 0) (m : ℕ) (hm : 2 ^ m * F.blockSide ^ l ≤ F.blockSide ^ F.top) :
    ∑ x ∈ X.filter (fun x => scaleRadius F l p x < ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ)),
      1 / scaleRadius F l p x ≤ 200 * 8 ^ m / (F.blockSide : ℝ) ^ l := by
  classical
  have hR : (0 : ℝ) < (F.blockSide : ℝ) ^ l := by positivity
  induction m with
  | zero =>
    have hempty : X.filter (fun x => scaleRadius F l p x < ((2 ^ 0 * F.blockSide ^ l : ℕ) : ℝ)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro x _
      push Not
      have := pow_le_scaleRadius hl hL p x
      simpa using this
    rw [hempty]
    simp only [Finset.sum_empty, pow_zero]
    positivity
  | succ m ih =>
    have hm' : 2 ^ m * F.blockSide ^ l ≤ F.blockSide ^ F.top := by
      refine le_trans ?_ hm
      rw [pow_succ]
      nlinarith [Nat.one_le_two_pow (n := m), pow_pos hL l]
    have ih' := ih hm'
    set a : ℝ := ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ) with ha
    set a' : ℝ := ((2 ^ (m + 1) * F.blockSide ^ l : ℕ) : ℝ) with ha'
    have haa : a ≤ a' := by
      simp only [ha, ha']
      push_cast
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]
    have hsub : X.filter (fun x => scaleRadius F l p x < a) ⊆ X.filter (fun x => scaleRadius F l p x < a') := by
      intro x hx
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨h1, lt_of_lt_of_le h2 haa⟩
    rw [← Finset.sum_sdiff hsub]
    have hpos_a : 0 < a := by
      simp only [ha]
      have : 0 < 2 ^ m * F.blockSide ^ l := by positivity
      exact_mod_cast this
    have hD : ∑ x ∈ X.filter (fun x => scaleRadius F l p x < a') \ X.filter (fun x => scaleRadius F l p x < a),
        1 / scaleRadius F l p x ≤ 81 * 16 ^ (m + 1) * (1 / a) := by
      calc _ ≤ ∑ _x ∈ X.filter (fun x => scaleRadius F l p x < a') \
              X.filter (fun x => scaleRadius F l p x < a), 1 / a := by
            apply Finset.sum_le_sum
            intro x hx
            obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hx
            have h3 : a ≤ scaleRadius F l p x := by
              by_contra hcon
              exact h2 (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, not_le.1 hcon⟩)
            exact one_div_le_one_div_of_le hpos_a h3
        _ = ((X.filter (fun x => scaleRadius F l p x < a') \
              X.filter (fun x => scaleRadius F l p x < a)).card : ℝ) * (1 / a) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 81 * 16 ^ (m + 1) * (1 / a) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            refine le_trans ?_ (card_scaleRadius_lt_le hl hL X p (m + 1) hm)
            exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have e : (81 : ℝ) * 16 ^ (m + 1) * (1 / a) = 1296 * 8 ^ m / (F.blockSide : ℝ) ^ l := by
      simp only [ha]
      push_cast
      have h16 : (16 : ℝ) ^ m = 8 ^ m * 2 ^ m := by
        rw [← mul_pow]
        norm_num
      rw [pow_succ, h16]
      field_simp
      ring
    rw [e] at hD
    have hfin : (1296 : ℝ) * 8 ^ m / (F.blockSide : ℝ) ^ l + 200 * 8 ^ m / (F.blockSide : ℝ) ^ l ≤
        200 * 8 ^ (m + 1) / (F.blockSide : ℝ) ^ l := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hR.le
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 8) m]
    linarith
theorem sum_div_scaleRadius_le {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (X : Finset (F.Site l))
    (p : F.Site 0) (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1 / 2) :
    ∑ x ∈ X.filter (fun x => scaleRadius F l p x < η * (F.blockSide : ℝ) ^ F.top),
      (F.blockSide : ℝ) ^ F.top / scaleRadius F l p x ≤
        1600 * η ^ 3 * ((F.blockSide : ℝ) ^ (F.top - l)) ^ 4 := by
  classical
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  set R₀ : ℝ := (F.blockSide : ℝ) ^ l with hR₀
  set M : ℝ := (F.blockSide : ℝ) ^ (F.top - l) with hM
  have hR : 0 < R₀ := by positivity
  have hMp : 0 < M := by positivity
  have hNp : 0 < N := by positivity
  have hNM : N = R₀ * M := by
    rw [hN, hR₀, hM, ← pow_add]
    congr 1
    omega
  by_cases hsmall : η * N ≤ R₀
  · have hempty : X.filter (fun x => scaleRadius F l p x < η * N) = ∅ := by
      apply Finset.filter_false_of_mem
      intro x _
      push Not
      exact le_trans hsmall (pow_le_scaleRadius hl hL p x)
    rw [hempty]
    simp only [Finset.sum_empty]
    positivity
  · push Not at hsmall
    have hex : ∃ m : ℕ, η * N ≤ 2 ^ m * R₀ := by
      obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (η * N / R₀) (by norm_num : (1 : ℝ) < 2)
      refine ⟨m, ?_⟩
      rw [div_lt_iff₀ hR] at hm
      exact hm.le
    set m := Nat.find hex with hmdef
    have hm1 : η * N ≤ 2 ^ m * R₀ := Nat.find_spec hex
    have hm0 : m ≠ 0 := by
      intro h
      rw [h] at hm1
      simp at hm1
      linarith
    obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hm2 : 2 ^ m' * R₀ < η * N := by
      have := Nat.find_min hex (m := m') (by omega)
      exact not_le.1 this
    have hm3 : (2 : ℝ) ^ m * R₀ < 2 * (η * N) := by
      rw [hm', pow_succ]
      linarith
    have hnat : 2 ^ m * F.blockSide ^ l ≤ F.blockSide ^ F.top := by
      have h3 : (2 : ℝ) ^ m * R₀ ≤ N := by nlinarith
      have h4 : ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ) ≤ ((F.blockSide ^ F.top : ℕ) : ℝ) := by
        push_cast
        exact h3
      exact_mod_cast h4
    have hs := sum_inv_scaleRadius_le hl hL X p m hnat
    have hcast : ((2 ^ m * F.blockSide ^ l : ℕ) : ℝ) = 2 ^ m * R₀ := by
      push_cast
      rfl
    rw [hcast] at hs
    have hrad : ∀ x : F.Site l, 0 < scaleRadius F l p x := fun x => scaleRadius_pos hL l p x
    have hsub : ∑ x ∈ X.filter (fun x => scaleRadius F l p x < η * N), 1 / scaleRadius F l p x ≤
        ∑ x ∈ X.filter (fun x => scaleRadius F l p x < 2 ^ m * R₀), 1 / scaleRadius F l p x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨h3, h4⟩ := Finset.mem_filter.1 hx
        exact Finset.mem_filter.2 ⟨h3, lt_of_lt_of_le h4 hm1⟩
      · intro x _ _
        have := hrad x
        positivity
    have h8 : (8 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ 3 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h2m : (2 : ℝ) ^ m ≤ 2 * η * M := by
      have : (2 : ℝ) ^ m * R₀ ≤ (2 * η * M) * R₀ := by
        rw [hNM] at hm3
        nlinarith
      exact le_of_mul_le_mul_right this hR
    calc ∑ x ∈ X.filter (fun x => scaleRadius F l p x < η * N), N / scaleRadius F l p x
        = N * ∑ x ∈ X.filter (fun x => scaleRadius F l p x < η * N), 1 / scaleRadius F l p x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ ≤ N * (200 * 8 ^ m / R₀) := mul_le_mul_of_nonneg_left (le_trans hsub hs) hNp.le
      _ = 200 * M * ((2 : ℝ) ^ m) ^ 3 := by
          rw [h8, hNM]
          field_simp
      _ ≤ 200 * M * (2 * η * M) ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (by positivity) h2m 3
      _ = _ := by ring
theorem classWeight_pos (hL : 0 < F.blockSide) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) (l : ℕ)
    (x : F.Site l) : 0 < classWeight F φ θ p l x := by
  simp only [classWeight]
  have := scaleRadius_pos hL l p x
  positivity
theorem sum_centredCube_succ {E : Type} [AddCommMonoid E] (hodd : Odd F.blockSide) (j : ℕ) (G : Lattice4 → E) :
    ∑ q ∈ centredCube (F.blockSide ^ (j + 1)), G q =
      ∑ h ∈ centredCube F.blockSide, ∑ h' ∈ centredCube (F.blockSide ^ j),
        G (fun i => (F.blockSide : ℤ) ^ j * h i + h' i) := by
  classical
  obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_half hodd 1
  rw [pow_one] at hk1 hk2 hk3
  obtain ⟨p, hp1, hp2, hp3⟩ := odd_pow_half hodd j
  obtain ⟨P, hP1, hP2, hP3⟩ := odd_pow_half hodd (j + 1)
  set m : Lattice4 × Lattice4 → Lattice4 := fun a i => (F.blockSide : ℤ) ^ j * a.1 i + a.2 i with hm
  have hLj : (0 : ℤ) < (F.blockSide : ℤ) ^ j := by rw [hp3]; omega
  have hinj : Set.InjOn m ((centredCube F.blockSide ×ˢ centredCube (F.blockSide ^ j) :
      Finset (Lattice4 × Lattice4)) : Set (Lattice4 × Lattice4)) := by
    intro a ha b hb e
    have ha' := Finset.mem_product.1 (Finset.mem_coe.1 ha)
    have hb' := Finset.mem_product.1 (Finset.mem_coe.1 hb)
    have a2 := (mem_centredCube _ _).1 ha'.2
    have b2 := (mem_centredCube _ _).1 hb'.2
    rw [hp2] at a2 b2
    have he : ∀ i, (F.blockSide : ℤ) ^ j * a.1 i + a.2 i = (F.blockSide : ℤ) ^ j * b.1 i + b.2 i :=
      fun i => congrFun e i
    have h2 : ∀ i, a.2 i = b.2 i := by
      intro i
      have hd : (F.blockSide : ℤ) ^ j ∣ a.2 i - b.2 i := ⟨b.1 i - a.1 i, by linear_combination he i⟩
      have habs : |a.2 i - b.2 i| < (F.blockSide : ℤ) ^ j := by
        have u := a2 i
        have w := b2 i
        rw [abs_lt, hp3]
        constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hd habs
      omega
    have h1 : ∀ i, a.1 i = b.1 i := by
      intro i
      have := he i
      rw [h2 i] at this
      exact mul_left_cancel₀ hLj.ne' (by linarith)
    exact Prod.ext (funext h1) (funext h2)
  have hsub : (centredCube F.blockSide ×ˢ centredCube (F.blockSide ^ j)).image m ⊆
      centredCube (F.blockSide ^ (j + 1)) := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hq
    have ha' := Finset.mem_product.1 ha
    have a1 := (mem_centredCube _ _).1 ha'.1
    have a2 := (mem_centredCube _ _).1 ha'.2
    rw [hk2] at a1
    rw [hp2] at a2
    rw [mem_centredCube, hP2]
    have hrel : (P : ℤ) = (F.blockSide : ℤ) ^ j * k + p := by
      have e : 2 * (P : ℤ) + 1 = (2 * (p : ℤ) + 1) * (2 * (k : ℤ) + 1) := by
        rw [← hP3, ← hp3, ← hk3, pow_succ]
      rw [hp3]
      have h2 : (2 : ℤ) * P = 2 * ((2 * (p : ℤ) + 1) * k + p) := by linear_combination e
      exact mul_left_cancel₀ (by norm_num) h2
    intro i
    have u1 := a1 i
    have u2 := a2 i
    simp only [hm]
    rw [hrel]
    have m1 : (F.blockSide : ℤ) ^ j * (-(k : ℤ)) ≤ (F.blockSide : ℤ) ^ j * a.1 i :=
      mul_le_mul_of_nonneg_left u1.1 hLj.le
    have m2 : (F.blockSide : ℤ) ^ j * a.1 i ≤ (F.blockSide : ℤ) ^ j * k := mul_le_mul_of_nonneg_left u1.2 hLj.le
    constructor
    · linarith [u2.1]
    · linarith [u2.2]
  have hcard : (centredCube (F.blockSide ^ (j + 1))).card ≤
      ((centredCube F.blockSide ×ˢ centredCube (F.blockSide ^ j)).image m).card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, card_centredCube hodd, card_centredCube (hodd.pow),
      card_centredCube (hodd.pow)]
    exact (by rw [pow_succ F.blockSide j, mul_pow, mul_comm] :
      (F.blockSide ^ (j + 1)) ^ 4 = F.blockSide ^ 4 * (F.blockSide ^ j) ^ 4).le
  have himg := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← himg, Finset.sum_image hinj, Finset.sum_product]
theorem centredCube_one : centredCube 1 = ({0} : Finset Lattice4) := by apply _root_.YangMills.Construction.PotentialMeans.centredCube_one <;> assumption
theorem siteOfCoords_zero (j : ℕ) : siteOfCoords (F := F) j (0 : Lattice4) = 0 := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_zero <;> assumption
theorem iteratedMean_eq {E : Type} [AddCommMonoid E] [Module ℝ E] (hodd : Odd F.blockSide) (f : F.Site 0 → E) :
    ∀ j, j ≤ F.top → ∀ y : F.Site j, iteratedMean f j y =
      (1 / ((F.blockSide : ℝ) ^ j) ^ 4) • ∑ q ∈ centredCube (F.blockSide ^ j), f (baseSite y + siteOfCoords 0 q) := by
  have hLR : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  intro j
  induction j with
  | zero =>
    intro _ y
    simp only [pow_zero, one_pow, centredCube_one, Finset.sum_singleton, siteOfCoords_zero, add_zero,
      baseSite_zero_level]
    simp [iteratedMean]
  | succ j ih =>
    intro hj y
    have hj' : j < F.top := by omega
    have e1 : iteratedMean f (j + 1) y = (1 / (F.blockSide : ℝ) ^ 4) •
        ∑ h ∈ centredCube F.blockSide, iteratedMean f j (refineSite y + siteOfCoords j h) := rfl
    rw [e1, sum_centredCube_succ hodd j (fun q => f (baseSite y + siteOfCoords 0 q))]
    have e2 : ∀ h ∈ centredCube F.blockSide, iteratedMean f j (refineSite y + siteOfCoords j h) =
        (1 / ((F.blockSide : ℝ) ^ j) ^ 4) • ∑ h' ∈ centredCube (F.blockSide ^ j),
          f (baseSite y + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ j * h i + h' i)) := by
      intro h _
      rw [ih hj'.le]
      congr 1
      refine Finset.sum_congr rfl fun h' _ => ?_
      rw [baseSite_add j hj'.le, baseSite_refineSite_eq hj', add_assoc, siteOfCoords_add_eq]
    rw [Finset.sum_congr rfl e2, ← Finset.smul_sum, smul_smul]
    congr 1
    rw [pow_succ]
    field_simp
    ring
theorem cellCentre_top_self (z : F.Cell) : cellCentre F.top z = z := by apply _root_.YangMills.Construction.BlockAverages.cellCentre_top <;> assumption
theorem baseSite_top (z : F.Cell) : baseSite z = cellCentre 0 z := by apply _root_.YangMills.Construction.ReferenceBounds.baseSite_cell <;> assumption
theorem inCell_top (hL : 0 < F.blockSide) (z : F.Cell) : InCell z F.top z := by
  refine ⟨0, zero_mem_centredCube (by positivity), ?_⟩
  rw [siteOfCoords_zero, add_zero, cellCentre_top_self]
theorem mem_of_mem_sitesOfCells_top {S : Finset F.Cell} {x : F.Cell} (hx : x ∈ sitesOfCells S F.top) :
    x ∈ S := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  simp only [Nat.sub_self, pow_zero, centredCube_one, Finset.mem_singleton] at hh
  rw [hh, siteOfCoords_zero, add_zero, cellCentre_top_self]
  exact hy
theorem iteratedMean_inCellFrame_eq_zero {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
    (hodd : Odd F.blockSide) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (ξ : F.Site 0 → ℍ[ℝ]) (hmf : frameCellMean S V z ξ = 0) :
    iteratedMean (fun x => adjointAction (frameChange S V z x)⁻¹ (ξ x)) F.top z = 0 := by
  have hL := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  set φ₀ : F.Site 0 → ℍ[ℝ] := fun x => adjointAction (frameChange S V z x)⁻¹ (ξ x) with hφ₀
  rw [iteratedMean_eq hodd φ₀ F.top le_rfl z, baseSite_top]
  have hsum : ∑ x ∈ cellOffsets F, φ₀ (patchSite S z x) = 0 := by
    unfold frameCellMean at hmf
    rcases smul_eq_zero.1 hmf with h | h
    · exfalso
      have : (1 / ((cellSideLength F : ℤ) : ℝ) ^ 4) ≠ 0 := by positivity
      exact this h
    · exact h
  have hre : ∑ q ∈ centredCube (F.blockSide ^ F.top), φ₀ (cellCentre 0 z + siteOfCoords 0 q) =
      ∑ x ∈ cellOffsets F, φ₀ (patchSite S z x) := by
    refine (Finset.sum_nbij' (fun q i => closedOrthant S z i * q i + (cellSideLength F - 1) / 2)
      (fun x i => closedOrthant S z i * (x i - (cellSideLength F - 1) / 2)) ?_ ?_ ?_ ?_ ?_)
    · intro q hq
      have hq' := (mem_centredCube_iff q).1 hq
      refine Fintype.mem_piFinset.2 fun i => Finset.mem_Ico.2 ?_
      have u := hq' i
      rcases he i with a | a <;> rw [a] <;> constructor <;> omega
    · intro x hx
      have hx' := Fintype.mem_piFinset.1 hx
      refine (PatchPoints.mem_centredCube_iff _).2 fun i => ?_
      have u := Finset.mem_Ico.1 (hx' i)
      rcases he i with a | a <;> rw [a] <;> constructor <;> omega
    · intro q _
      funext i
      have := closedOrthant_mul_self he i
      show closedOrthant S z i * (closedOrthant S z i * q i + (cellSideLength F - 1) / 2 -
        (cellSideLength F - 1) / 2) = q i
      calc _ = (closedOrthant S z i * closedOrthant S z i) * q i := by ring
        _ = q i := by rw [this, one_mul]
    · intro x _
      funext i
      have := closedOrthant_mul_self he i
      show closedOrthant S z i * (closedOrthant S z i * (x i - (cellSideLength F - 1) / 2)) +
        (cellSideLength F - 1) / 2 = x i
      calc _ = (closedOrthant S z i * closedOrthant S z i) * (x i - (cellSideLength F - 1) / 2) +
            (cellSideLength F - 1) / 2 := by ring
        _ = x i := by rw [this, one_mul]; ring
    · intro q hq
      have e : patchSite S z (fun i => closedOrthant S z i * q i + (cellSideLength F - 1) / 2) =
          cellCentre 0 z + siteOfCoords 0 q := by
        unfold patchSite
        congr 2
        funext i
        have := closedOrthant_mul_self he i
        calc _ = (closedOrthant S z i * closedOrthant S z i) * q i := by ring
          _ = q i := by rw [this, one_mul]
      rw [e]
  rw [hre, hsum, smul_zero]
theorem norm_transportedMeans_top_le {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} (hz : z ∈ S)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hB : ∀ j, j < F.top → ∀ b ∈ innerBonds S j, baseSite b.1 ∈ (patchDomain S z).image (patchSite S z) →
      baseSite (b.1 + unitStep j b.2) ∈ (patchDomain S z).image (patchSite S z) →
      unitDeviation (referenceInPatchFrame S V z j b.1 b.2) ≤ κ * levelScale F j) (ξ : F.Site 0 → ℍ[ℝ])
    (hmf : frameCellMean S V z ξ = 0) :
    ‖transportedMeans (referenceFieldChain S V) ξ F.top z‖ ≤
      4 * F.blockSide * κ * iteratedMean (fun x => ‖ξ x‖) F.top z := by
  have h := norm_inCellFrame_transportedMeans_sub_le hz hamb hodd h2 he κ hκ hB ξ F.top le_rfl z
    (inCell_top hodd.pos z)
  rw [iteratedMean_inCellFrame_eq_zero hodd he ξ hmf, sub_zero, norm_inCellFrame, levelScale_top_eq_one,
    mul_one] at h
  exact h
theorem norm_linearPart_top_le {S : Finset F.Cell} {V : F.GaugeField F.top} (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (h4 : 4 ≤ F.blockSide)
    (hsign : ∀ z, ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (ξ : F.Site 0 → ℍ[ℝ])
    (v : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (hv : ∀ x i, ((v x i : imaginaryQuaternions) : ℍ[ℝ]) = covDiff (referenceFieldChain S V 0) ξ x i) (κ : ℝ)
    (hκ : 0 ≤ κ)
    (hB : ∀ z ∈ S, ∀ j, j < F.top → ∀ b ∈ innerBonds S j,
      baseSite b.1 ∈ (patchDomain S z).image (patchSite S z) →
      baseSite (b.1 + unitStep j b.2) ∈ (patchDomain S z).image (patchSite S z) →
      unitDeviation (referenceInPatchFrame S V z j b.1 b.2) ≤ κ * levelScale F j)
    (hmis : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
      unitDeviation (referenceDefect (referenceFieldChain S V) j c) ≤ κ * levelScale F (j + 1) ^ 3)
    (hcon : ∀ j, j < F.top → ∀ c ∈ innerBonds S (j + 1), ∀ h ∈ centredCube F.blockSide,
      ∀ π : Equiv.Perm (Fin 4),
      unitDeviation (pathHolonomy (referenceFieldChain S V j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (referenceFieldChain S V j) c))⁻¹) ≤ κ * levelScale F (j + 1) ^ 2)
    (hmf : CellMeanFree S V ξ) (c : F.Site F.top × Fin 4) (hc : c ∈ innerBonds S F.top) :
    ‖linearPart (referenceFieldChain S V) (baseOnlyChart v) F.top c.1 c.2‖ ≤
      (6 + 4 * F.blockSide) * κ * (iteratedMean (fun x => ‖ξ x‖) F.top c.1 +
        iteratedMean (fun x => ‖ξ x‖) F.top (c.1 + unitStep F.top c.2)) := by
  have hL := hodd.pos
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
  have hL4 : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast h4
  set R := referenceFieldChain S V with hR
  set gb := iteratedMean (F := F) (fun x => ‖ξ x‖) with hgb
  have hgb0 : ∀ j (y : F.Site j), 0 ≤ gb j y := iteratedMean_nonneg hL (fun x => norm_nonneg _)
  have hcf := Finset.mem_filter.1 hc
  have hy : c.1 ∈ S := mem_of_mem_sitesOfCells_top (Finset.mem_product.1 hcf.1).1
  have hy' : c.1 + unitStep F.top c.2 ∈ S := mem_of_mem_sitesOfCells_top hcf.2
  have hΔ : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
      ‖parallelAverage (R j) (covDiff (R j) (transportedMeans R ξ j)) c -
          covDiff (R (j + 1)) (transportedMeans R ξ (j + 1)) c.1 c.2‖ ≤
        (4 * κ) * levelScale F (j + 1) ^ 2 * gb (j + 1) (c.1 + unitStep (j + 1) c.2) := by
    intro j hj c hc
    have h1 := norm_parallelAverage_covDiff_sub_le hL hj R ξ c (κ * levelScale F (j + 1) ^ 2)
      (κ * levelScale F (j + 1) ^ 3)
      (by have := zero_le_levelScale (F := F) (j + 1); positivity) (hcon j (by omega) c hc) (hmis j hj c hc)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hgb0 _ _))
    have l1 := levelScale_le_one_of_pos (F := F) hL (j + 1)
    have : κ * levelScale F (j + 1) ^ 3 ≤ κ * levelScale F (j + 1) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hκ
      nlinarith [sq_nonneg (levelScale F (j + 1))]
    linarith
  have herr := norm_linearPart_sub_covDiff_le hodd h4 R ξ v hv (4 * κ) (by positivity) hΔ F.depth
    (Nat.lt_succ_self _)
  set e : F.Site F.depth → Fin 4 → ℍ[ℝ] := fun x i =>
    linearPart R (baseOnlyChart v) F.depth x i - covDiff (R F.depth) (transportedMeans R ξ F.depth) x i with he
  have e1 : linearPart R (baseOnlyChart v) F.top c.1 c.2 =
      parallelAverage (R F.depth) e c +
        parallelAverage (R F.depth) (covDiff (R F.depth) (transportedMeans R ξ F.depth)) c := by
    have := linearPart_baseOnly_succ R v F.depth c.1 c.2
    rw [he, parallelAverage_sub]
    rw [show linearPart R (baseOnlyChart v) F.top c.1 c.2 = _ from this]
    abel
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  have hstep := levelScale_succ_eq (F := F) hL (Nat.lt_succ_self F.depth)
  have hls : levelScale F F.depth = 1 / (F.blockSide : ℝ) := by
    have h1 : levelScale F (F.depth + 1) = 1 := levelScale_top_eq_one
    rw [h1] at hstep
    field_simp
    linarith
  have a1 := norm_parallelAverage_le hL (R F.depth) e c
  have a2 := lineMean_le_blockMeans (Nat.lt_succ_self F.depth) hodd (gb F.depth) (hgb0 F.depth) c
    (2 * (4 * κ) * levelScale F F.depth ^ 2) (by positivity) (fun b => ‖e b.1 b.2‖) (fun h hh r hr =>
      herr _ (mem_innerBonds_of_line (Nat.lt_succ_self F.depth) hodd c hc h hh r (Finset.mem_range.1 hr)))
  have a3 := norm_parallelAverage_covDiff_top_le hL R ξ c κ (fun h hh π => by
    have := hcon F.depth (Nat.lt_succ_self _) c hc h hh π
    have e2 : levelScale F (F.depth + 1) = 1 := levelScale_top_eq_one
    rw [e2] at this
    simpa [unitDeviation] using this)
  have a4 := norm_transportedMeans_top_le hy hamb hodd (by omega) (hsign _) κ hκ (hB _ hy) ξ (hmf _ hy)
  have a5 := norm_transportedMeans_top_le hy' hamb hodd (by omega) (hsign _) κ hκ (hB _ hy') ξ (hmf _ hy')
  have hgs : blockMean (gb F.depth) c.1 = gb F.top c.1 := rfl
  have hgs' : blockMean (gb F.depth) (c.1 + unitStep (F.depth + 1) c.2) = gb F.top (c.1 + unitStep F.top c.2) :=
    rfl
  rw [hgs, hgs'] at a2
  set A := gb F.top c.1
  set B := gb F.top (c.1 + unitStep F.top c.2)
  have hA : 0 ≤ A := hgb0 _ _
  have hB' : 0 ≤ B := hgb0 _ _
  have hcoef : 2 * (2 * (4 * κ) * levelScale F F.depth ^ 2) * (F.blockSide : ℝ) ≤ 4 * κ := by
    rw [hls]
    have e3 : 2 * (2 * (4 * κ) * (1 / (F.blockSide : ℝ)) ^ 2) * (F.blockSide : ℝ) = 16 * κ / F.blockSide := by
      field_simp
      ring
    rw [e3, div_le_iff₀ hLR]
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hcoef (add_nonneg hA hB')
  have hκL : 0 ≤ κ * F.blockSide := by positivity
  have h8 : 2 * κ * B ≤ 2 * κ * (A + B) := by nlinarith [mul_nonneg hκ hA]
  nlinarith [mul_nonneg hκ hA, mul_nonneg hκ hB', mul_nonneg hκL hA, mul_nonneg hκL hB']
theorem linearizedCurl_covDiff (R : F.GaugeField 0) (ξ : F.Site 0 → ℍ[ℝ])
    (v : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (hv : ∀ x i, ((v x i : imaginaryQuaternions) : ℍ[ℝ]) = covDiff R ξ x i) (q : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl R v q = adjointAction (plaquetteHolonomy R q) (ξ q.1) - ξ q.1 := by
  obtain ⟨x, μ, ν⟩ := q
  have e : plaquetteHolonomy R (x, μ, ν) =
      R x μ * R (x + unitStep 0 μ) ν * (R (x + unitStep 0 ν) μ)⁻¹ * (R x ν)⁻¹ := by
    have a1 : x + unitStep 0 μ + unitStep 0 ν - unitStep 0 μ = x + unitStep 0 ν := by abel
    have a2 : x + unitStep 0 μ + unitStep 0 ν + -unitStep 0 μ - unitStep 0 ν = x := by abel
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
      if_false, mul_one]
    rw [a1, a2]
    group
  show ((v x μ : imaginaryQuaternions) : ℍ[ℝ]) + adjointAction (R x μ) (v (x + unitStep 0 μ) ν) -
      adjointAction (R x μ * R (x + unitStep 0 μ) ν * (R (x + unitStep 0 ν) μ)⁻¹) (v (x + unitStep 0 ν) μ) -
      adjointAction (R x μ * R (x + unitStep 0 μ) ν * (R (x + unitStep 0 ν) μ)⁻¹ * (R x ν)⁻¹) (v x ν) = _
  rw [e]
  set r1 := R x μ
  set r2 := R (x + unitStep 0 μ) ν
  set r3 := R (x + unitStep 0 ν) μ
  set r4 := R x ν
  simp only [hv, covDiff, adjointAction_sub]
  have t1 : ∀ w, adjointAction r1 (adjointAction r2 w) = adjointAction (r1 * r2) w :=
    fun w => (adjointAction_mul _ _ _).symm
  have t2 : ∀ w, adjointAction (r1 * r2 * r3⁻¹) (adjointAction (R (x + unitStep 0 ν) μ) w) =
      adjointAction (r1 * r2) w := by
    intro w
    rw [← adjointAction_mul]
    congr 1
    show r1 * r2 * r3⁻¹ * r3 = r1 * r2
    group
  have t3 : ∀ w, adjointAction (r1 * r2 * r3⁻¹ * r4⁻¹) (adjointAction (R x ν) w) =
      adjointAction (r1 * r2 * r3⁻¹) w := by
    intro w
    rw [← adjointAction_mul]
    congr 1
    show r1 * r2 * r3⁻¹ * r4⁻¹ * r4 = r1 * r2 * r3⁻¹
    group
  have s1 : x + unitStep 0 ν + unitStep 0 μ = x + unitStep 0 μ + unitStep 0 ν := by abel
  rw [t1, t2, t3, s1]
  abel
theorem cellCentre_add_injOn (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (z : F.Cell) :
    Set.InjOn (fun h : Lattice4 => cellCentre 0 z + siteOfCoords 0 h)
      (centredCube (F.blockSide ^ F.top) : Set Lattice4) := by
  intro a ha b hb e
  have hL := hodd.pos
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  have ha' := (mem_centredCube_iff a).1 (Finset.mem_coe.1 ha)
  have hb' := (mem_centredCube_iff b).1 (Finset.mem_coe.1 hb)
  have e1 : siteOfCoords (F := F) 0 a = siteOfCoords 0 b := add_left_cancel e
  funext i
  have e2 : ((a i : ℤ) : ZMod (F.period 0 i)) = ((b i : ℤ) : ZMod (F.period 0 i)) := congrFun e1 i
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 e2
  have u := ha' i
  have w := hb' i
  rcases period_zero_eq_zero_or hamb hL i with hp | hp
  · rw [hp] at hd
    have : b i - a i = 0 := by simpa using hd
    omega
  · have habs : |b i - a i| < (F.period 0 i : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hd habs
    omega
theorem cellSiteNorm_eq (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {z : F.Cell} (hz : z ∈ S) (q : ℝ) (w : F.Site 0 → ℝ) (ξ : F.Site 0 → ℍ[ℝ]) :
    cellSiteNorm q S w ξ z = (∑ h ∈ centredCube (F.blockSide ^ F.top),
      (w (cellCentre 0 z + siteOfCoords 0 h) * ‖ξ (cellCentre 0 z + siteOfCoords 0 h)‖) ^ q) ^ (1 / q) := by
  unfold cellSiteNorm
  congr 1
  symm
  refine Finset.sum_nbij (fun h : Lattice4 => cellCentre 0 z + siteOfCoords 0 h) ?_
    (cellCentre_add_injOn hamb hodd z) ?_ (fun _ _ => rfl)
  · intro h hh
    refine Finset.mem_filter.2 ⟨mem_sitesOfCells.2 ⟨z, hz, h, by simpa using hh, rfl⟩, ?_⟩
    exact enclosingCell_cellCentre_add hodd z h (by simpa using hh)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
    obtain ⟨y, _, h, hh, rfl⟩ := mem_sitesOfCells.1 hx1
    have := enclosingCell_cellCentre_add hodd y h hh
    rw [hx2] at this
    subst this
    exact ⟨h, by simpa using hh, rfl⟩
theorem sum_sitesOfCells_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (S : Finset F.Cell)
    (t : F.Site 0 → ℝ) :
    ∑ x ∈ sitesOfCells S 0, t x =
      ∑ z ∈ S, ∑ h ∈ centredCube (F.blockSide ^ F.top), t (cellCentre 0 z + siteOfCoords 0 h) := by
  unfold sitesOfCells
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun z _ => ?_
    simp only [Nat.sub_zero]
    rw [Finset.sum_image (cellCentre_add_injOn hamb hodd z)]
  · intro y _ y' _ hne
    refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h', hh', e⟩ := Finset.mem_image.1 hx'
    have e1 := enclosingCell_cellCentre_add hodd y h hh
    have e2 := enclosingCell_cellCentre_add hodd y' h' hh'
    rw [e] at e2
    rw [← e1, e2]
theorem sum_div_scaleRadius_le_total (hL : 0 < F.blockSide) (X : Finset (F.Site 0)) (p : F.Site 0)
    (hX : (X.card : ℝ) ≤ ((F.blockSide : ℝ) ^ F.top) ^ 4) :
    ∑ x ∈ X, (F.blockSide : ℝ) ^ F.top / scaleRadius F 0 p x ≤ 202 * ((F.blockSide : ℝ) ^ F.top) ^ 4 := by
  classical
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have h1 := sum_div_scaleRadius_le (Nat.zero_le F.top) hL X p (1 / 2) (by norm_num) le_rfl
  rw [Nat.sub_zero] at h1
  rw [← Finset.sum_filter_add_sum_filter_not X (fun x => scaleRadius F 0 p x < 1 / 2 * N)]
  have h2 : ∑ x ∈ X.filter (fun x => ¬ scaleRadius F 0 p x < 1 / 2 * N), N / scaleRadius F 0 p x ≤
      2 * N ^ 4 := by
    calc ∑ x ∈ X.filter (fun x => ¬ scaleRadius F 0 p x < 1 / 2 * N), N / scaleRadius F 0 p x
        ≤ ∑ _x ∈ X.filter (fun x => ¬ scaleRadius F 0 p x < 1 / 2 * N), (2 : ℝ) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hx' := not_lt.1 (Finset.mem_filter.1 hx).2
          have hr := scaleRadius_pos hL 0 p x
          rw [div_le_iff₀ hr]
          linarith
      _ = 2 * ((X.filter (fun x => ¬ scaleRadius F 0 p x < 1 / 2 * N)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ 2 * N ^ 4 := by
          have : ((X.filter (fun x => ¬ scaleRadius F 0 p x < 1 / 2 * N)).card : ℝ) ≤ X.card := by
            exact_mod_cast Finset.card_filter_le _ _
          linarith
  linarith
theorem iteratedMean_top_le_cellSiteNorm (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell} (hz : z ∈ S) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) (hθ : |θ| ≤ 1 / 8)
    (ξ : F.Site 0 → ℍ[ℝ]) :
    Real.exp (φ z) * iteratedMean (fun x => ‖ξ x‖) F.top z ≤
      202 / (F.blockSide : ℝ) ^ F.top * cellSiteNorm 4 S (classWeight F φ θ p 0) ξ z := by
  classical
  have hL := hodd.pos
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hNp : 0 < N := by positivity
  set w : F.Site 0 → ℝ := classWeight F φ θ p 0 with hw
  have hw0 : ∀ x, 0 < w x := fun x => classWeight_pos hL φ θ p 0 x
  set c : Lattice4 → F.Site 0 := fun h => cellCentre 0 z + siteOfCoords 0 h with hc
  set C := centredCube (F.blockSide ^ F.top) with hC
  have hcard : (C.card : ℝ) = N ^ 4 := by
    rw [hC, card_centredCube hodd.pow]
    push_cast
    rfl
  rw [iteratedMean_eq hodd _ F.top le_rfl z, baseSite_top, cellSiteNorm_eq hamb hodd hz, smul_eq_mul]
  have hpq : (4 / 3 : ℝ).HolderConjugate 4 := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hI := Real.inner_le_Lp_mul_Lq C (fun h => (w (c h))⁻¹) (fun h => w (c h) * ‖ξ (c h)‖) hpq
  have e1 : ∑ h ∈ C, (w (c h))⁻¹ * (w (c h) * ‖ξ (c h)‖) = ∑ h ∈ C, ‖ξ (c h)‖ :=
    Finset.sum_congr rfl fun h _ => inv_mul_cancel_left₀ (hw0 _).ne' _
  rw [e1] at hI
  have e2 : ∑ h ∈ C, |w (c h) * ‖ξ (c h)‖| ^ (4 : ℝ) = ∑ h ∈ C, (w (c h) * ‖ξ (c h)‖) ^ (4 : ℝ) :=
    Finset.sum_congr rfl fun h _ => by rw [abs_of_nonneg (mul_nonneg (hw0 _).le (norm_nonneg _))]
  rw [e2] at hI
  have hterm : ∀ h ∈ C, |(w (c h))⁻¹| ^ (4 / 3 : ℝ) ≤
      Real.exp (-(φ z) * (4 / 3)) * (N / scaleRadius F 0 p (c h)) := by
    intro h hh
    have hcell : enclosingCell (c h) = z := enclosingCell_cellCentre_add hodd z h (by simpa using hh)
    have hr0 := scaleRadius_pos hL 0 p (c h)
    set r := scaleRadius F 0 p (c h) / N with hr
    have hrp : 0 < r := by positivity
    have hr1 : r ≤ 1 := by
      rw [hr, div_le_one hNp]
      exact min_le_left _ _
    have ew : w (c h) = Real.exp (φ z) * r ^ (-θ) := by
      simp only [hw, classWeight, hcell]
      rfl
    have ei : (w (c h))⁻¹ = Real.exp (-(φ z)) * r ^ θ := by
      rw [ew, mul_inv, Real.rpow_neg hrp.le, inv_inv, Real.exp_neg]
    rw [abs_of_pos (inv_pos.2 (hw0 _)), ei, Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hrp.le _),
      ← Real.exp_mul, ← Real.rpow_mul hrp.le]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have e3 : N / scaleRadius F 0 p (c h) = r ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, hr, inv_div]
    rw [e3]
    refine Real.rpow_le_rpow_of_exponent_ge hrp hr1 ?_
    have := (abs_le.1 hθ).1
    linarith
  have hsum : ∑ h ∈ C, N / scaleRadius F 0 p (c h) ≤ 202 * N ^ 4 := by
    have h1 := sum_div_scaleRadius_le_total hL (C.image c) p (by
      have : ((C.image c).card : ℝ) ≤ C.card := by exact_mod_cast Finset.card_image_le
      rw [hcard] at this
      exact this)
    rwa [Finset.sum_image (cellCentre_add_injOn hamb hodd z)] at h1
  have hA : ∑ h ∈ C, |(w (c h))⁻¹| ^ (4 / 3 : ℝ) ≤ Real.exp (-(φ z) * (4 / 3)) * (202 * N ^ 4) :=
    (Finset.sum_le_sum hterm).trans (by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le)
  have hA0 : 0 ≤ ∑ h ∈ C, |(w (c h))⁻¹| ^ (4 / 3 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  have hroot : (∑ h ∈ C, |(w (c h))⁻¹| ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) ≤
      Real.exp (-(φ z)) * (202 * N ^ 3) := by
    refine (Real.rpow_le_rpow hA0 hA (by norm_num)).trans ?_
    have e4 : (1 / (4 / 3 : ℝ)) = 3 / 4 := by norm_num
    rw [e4, Real.mul_rpow (Real.exp_pos _).le (by positivity), ← Real.exp_mul,
      Real.mul_rpow (by norm_num) (by positivity)]
    have e5 : -(φ z) * (4 / 3) * (3 / 4) = -(φ z) := by ring
    have e6 : (N ^ 4) ^ (3 / 4 : ℝ) = N ^ 3 := by
      rw [← Real.rpow_natCast N 4, ← Real.rpow_mul hNp.le, ← Real.rpow_natCast N 3]
      norm_num
    rw [e5, e6]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (202 : ℝ) ^ (3 / 4 : ℝ) ≤ (202 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 202 := Real.rpow_one _
  set T := (∑ h ∈ C, (w (c h) * ‖ξ (c h)‖) ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) with hT
  have hT0 : 0 ≤ T := Real.rpow_nonneg (Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (mul_nonneg (hw0 _).le (norm_nonneg _)) _) _
  have hfin : ∑ h ∈ C, ‖ξ (c h)‖ ≤ Real.exp (-(φ z)) * (202 * N ^ 3) * T :=
    hI.trans (mul_le_mul_of_nonneg_right hroot hT0)
  have hexp : Real.exp (φ z) * Real.exp (-(φ z)) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (φ z) * (1 / N ^ 4 * ∑ h ∈ C, ‖ξ (c h)‖)
      ≤ Real.exp (φ z) * (1 / N ^ 4 * (Real.exp (-(φ z)) * (202 * N ^ 3) * T)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfin (by positivity)) (Real.exp_pos _).le
    _ = (Real.exp (φ z) * Real.exp (-(φ z))) * (202 / N * T) := by
        field_simp
    _ = 202 / N * T := by rw [hexp, one_mul]
theorem sum_sq_le_cellSiteNorm (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {z : F.Cell} (hz : z ∈ S) (w : F.Site 0 → ℝ) (hw : ∀ x, 0 ≤ w x) (ξ : F.Site 0 → ℍ[ℝ]) :
    ∑ h ∈ centredCube (F.blockSide ^ F.top),
      (w (cellCentre 0 z + siteOfCoords 0 h) * ‖ξ (cellCentre 0 z + siteOfCoords 0 h)‖) ^ 2 ≤
      ((F.blockSide : ℝ) ^ F.top) ^ 2 * cellSiteNorm 4 S w ξ z ^ 2 := by
  have hL := hodd.pos
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hNp : 0 < N := by positivity
  set a : Lattice4 → ℝ := fun h => w (cellCentre 0 z + siteOfCoords 0 h) *
    ‖ξ (cellCentre 0 z + siteOfCoords 0 h)‖ with ha
  have ha0 : ∀ h, 0 ≤ a h := fun h => mul_nonneg (hw _) (norm_nonneg _)
  have h1 := lpNorm_le_card_rpow_mul_lpNorm (centredCube (F.blockSide ^ F.top)) a ha0 (Q := 2) (P := 4)
    (by norm_num) (by norm_num)
  have hcard : (((centredCube (F.blockSide ^ F.top)).card : ℕ) : ℝ) = N ^ 4 := by
    rw [card_centredCube hodd.pow]
    push_cast
    rfl
  have e1 : (N ^ 4) ^ (1 / (2 : ℝ) - 1 / 4) = N := by
    rw [← Real.rpow_natCast N 4, ← Real.rpow_mul hNp.le]
    norm_num
  have hT' : (∑ i ∈ centredCube (F.blockSide ^ F.top), a i ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) =
      cellSiteNorm 4 S w ξ z :=
    (cellSiteNorm_eq hamb hodd hz 4 w ξ).symm
  rw [hcard, e1, hT'] at h1
  have e2 : ∑ h ∈ centredCube (F.blockSide ^ F.top), a h ^ (2 : ℝ) =
      ∑ h ∈ centredCube (F.blockSide ^ F.top), a h ^ 2 :=
    Finset.sum_congr rfl fun h _ => Real.rpow_two _
  rw [e2, ← Real.sqrt_eq_rpow] at h1
  have hy : 0 ≤ N * cellSiteNorm 4 S w ξ z := (Real.sqrt_nonneg _).trans h1
  have h2 := (Real.sqrt_le_left hy).1 h1
  calc _ ≤ (N * cellSiteNorm 4 S w ξ z) ^ 2 := h2
    _ = _ := by ring
theorem cellSupDist_add_unitStep_le (y : F.Cell) (i : Fin 4) : cellSupDist y (y + unitStep F.top i) ≤ 1 := by
  refine Finset.sup_le fun l _ => ?_
  show ((y l - (y + unitStep F.top i : F.Cell) l).valMinAbs).natAbs ≤ 1
  have e : y l - (y + unitStep F.top i : F.Cell) l =
      ((-(Pi.single i 1 : Lattice4) l : ℤ) : ZMod (F.period F.top l)) := by
    simp [unitStep, siteOfCoords]
  rw [e]
  refine (natAbs_valMinAbs_intCast_le _ _).trans ?_
  by_cases hl : l = i
  · subst hl
    simp
  · simp [hl]
theorem classWeight_top (hodd : Odd F.blockSide) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) (x : F.Cell) :
    classWeight F φ θ p F.top x = Real.exp (φ x) := by
  have hL := hodd.pos
  have hc : enclosingCell x = x := by
    have := enclosingCell_cellCentre_add hodd x (0 : Lattice4) (j := F.top) (zero_mem_centredCube (by positivity))
    rwa [siteOfCoords_zero, add_zero, cellCentre_top_self] at this
  have hr : scaleRadius F F.top p x = (F.blockSide : ℝ) ^ F.top := by simp [scaleRadius]
  simp only [classWeight, hc, hr]
  rw [div_self (by positivity), Real.one_rpow, mul_one]
theorem sum_innerBonds_top_ends_le {S : Finset F.Cell} (G : F.Cell → ℝ) (hG : ∀ z, 0 ≤ G z) :
    ∑ c ∈ innerBonds S F.top, (G c.1 + G (c.1 + unitStep F.top c.2)) ≤ 8 * ∑ z ∈ S, G z := by
  classical
  have hmem : ∀ c ∈ innerBonds S F.top, c.1 ∈ S ∧ c.1 + unitStep F.top c.2 ∈ S := by
    intro c hc
    have hcf := Finset.mem_filter.1 hc
    exact ⟨mem_of_mem_sitesOfCells_top (Finset.mem_product.1 hcf.1).1, mem_of_mem_sitesOfCells_top hcf.2⟩
  have h1 : ∑ c ∈ innerBonds S F.top, G c.1 ≤ 4 * ∑ z ∈ S, G z := by
    calc ∑ c ∈ innerBonds S F.top, G c.1 ≤ ∑ c ∈ S ×ˢ (Finset.univ : Finset (Fin 4)), G c.1 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hG _
          intro c hc
          exact Finset.mem_product.2 ⟨(hmem c hc).1, Finset.mem_univ _⟩
      _ = 4 * ∑ z ∈ S, G z := by
          rw [Finset.sum_product]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.mul_sum]
          norm_num
  have h2 : ∑ c ∈ innerBonds S F.top, G (c.1 + unitStep F.top c.2) ≤ 4 * ∑ z ∈ S, G z := by
    calc ∑ c ∈ innerBonds S F.top, G (c.1 + unitStep F.top c.2)
        ≤ ∑ c ∈ (S ×ˢ (Finset.univ : Finset (Fin 4))).filter (fun c => c.1 + unitStep F.top c.2 ∈ S),
            G (c.1 + unitStep F.top c.2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hG _
          intro c hc
          exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨(hmem c hc).1, Finset.mem_univ _⟩, (hmem c hc).2⟩
      _ = ∑ i : Fin 4, ∑ y ∈ S.filter (fun y => y + unitStep F.top i ∈ S), G (y + unitStep F.top i) := by
          rw [Finset.sum_filter, Finset.sum_product_right]
          exact Finset.sum_congr rfl fun i _ => (Finset.sum_filter _ _).symm
      _ ≤ ∑ _i : Fin 4, ∑ z ∈ S, G z := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc ∑ y ∈ S.filter (fun y => y + unitStep F.top i ∈ S), G (y + unitStep F.top i)
              = ∑ z ∈ (S.filter (fun y => y + unitStep F.top i ∈ S)).image (fun y => y + unitStep F.top i),
                  G z := by
                rw [Finset.sum_image (fun a _ b _ e => add_right_cancel e)]
            _ ≤ ∑ z ∈ S, G z := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hG _
                intro z hz
                obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
                exact (Finset.mem_filter.1 hy).2
      _ = 4 * ∑ z ∈ S, G z := by
          simp
  calc _ = ∑ c ∈ innerBonds S F.top, G c.1 + ∑ c ∈ innerBonds S F.top, G (c.1 + unitStep F.top c.2) :=
        Finset.sum_add_distrib
    _ ≤ _ := by linarith
theorem sqrt_le_mul_sqrt_of_le {X a T : ℝ} (ha : 0 ≤ a) (h : X ≤ a ^ 2 * T) :
    Real.sqrt X ≤ a * Real.sqrt T := by
  calc Real.sqrt X ≤ Real.sqrt (a ^ 2 * T) := Real.sqrt_le_sqrt h
    _ = a * Real.sqrt T := by rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
theorem levelScale_zero_eq (hL : 0 < F.blockSide) : levelScale F 0 = 1 / (F.blockSide : ℝ) ^ F.top := by
  simp [levelScale]
theorem cellSiteNorm_nonneg (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {z : F.Cell} (hz : z ∈ S) (w : F.Site 0 → ℝ) (hw : ∀ x, 0 ≤ w x) (ξ : F.Site 0 → ℍ[ℝ]) :
    0 ≤ cellSiteNorm 4 S w ξ z := by
  rw [cellSiteNorm_eq hamb hodd hz]
  exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (mul_nonneg (hw _) (norm_nonneg _)) _) _
theorem exp_le_three_mul_exp_add_unitStep (φ : F.Cell → ℝ) (del : ℝ) (hdel : |del| ≤ 1 / 8)
    (hφ : ∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y') (y : F.Cell) (i : Fin 4) :
    Real.exp (φ y) ≤ 3 * Real.exp (φ (y + unitStep F.top i)) := by
  have d1 := hφ y (y + unitStep F.top i)
  have d2 : (cellSupDist y (y + unitStep F.top i) : ℝ) ≤ 1 := by exact_mod_cast cellSupDist_add_unitStep_le y i
  have d3 : φ y ≤ φ (y + unitStep F.top i) + 1 := by
    have := (abs_le.1 d1).2
    have d4 : |del| * cellSupDist y (y + unitStep F.top i) ≤ 1 := by
      have := abs_nonneg del
      nlinarith
    linarith
  calc Real.exp (φ y) ≤ Real.exp (φ (y + unitStep F.top i) + 1) := Real.exp_le_exp.2 d3
    _ = Real.exp 1 * Real.exp (φ (y + unitStep F.top i)) := by rw [Real.exp_add, mul_comm]
    _ ≤ 3 * Real.exp (φ (y + unitStep F.top i)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have := Real.exp_one_lt_d9
        linarith
theorem exp_mul_iteratedMean_ends_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {y y' : F.Cell} (hy : y ∈ S) (hy' : y' ∈ S) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0)
    (hθ : |θ| ≤ 1 / 8) (ξ : F.Site 0 → ℍ[ℝ]) (hexp : Real.exp (φ y) ≤ 3 * Real.exp (φ y')) :
    Real.exp (φ y) * (iteratedMean (fun x => ‖ξ x‖) F.top y + iteratedMean (fun x => ‖ξ x‖) F.top y') ≤
      606 / (F.blockSide : ℝ) ^ F.top * (cellSiteNorm 4 S (classWeight F φ θ p 0) ξ y +
        cellSiteNorm 4 S (classWeight F φ θ p 0) ξ y') := by
  have hL := hodd.pos
  have hw : ∀ x, 0 ≤ classWeight F φ θ p 0 x := fun x => (classWeight_pos hL φ θ p 0 x).le
  have hA'0 : 0 ≤ iteratedMean (F := F) (fun x => ‖ξ x‖) F.top y' :=
    iteratedMean_nonneg hL (fun x => norm_nonneg _) _ _
  have t1 := iteratedMean_top_le_cellSiteNorm hamb hodd hy φ θ p hθ ξ
  have t2 := iteratedMean_top_le_cellSiteNorm hamb hodd hy' φ θ p hθ ξ
  have hT1 := cellSiteNorm_nonneg hamb hodd hy _ hw ξ
  have t3 := mul_le_mul_of_nonneg_right hexp hA'0
  have hN2 : 0 ≤ 202 / (F.blockSide : ℝ) ^ F.top := by positivity
  have e3 : 606 / (F.blockSide : ℝ) ^ F.top = 3 * (202 / (F.blockSide : ℝ) ^ F.top) := by ring
  rw [e3]
  have m1 := mul_nonneg hN2 hT1
  have e4 : 3 * Real.exp (φ y') * iteratedMean (F := F) (fun x => ‖ξ x‖) F.top y' =
      3 * (Real.exp (φ y') * iteratedMean (F := F) (fun x => ‖ξ x‖) F.top y') := by ring
  rw [e4] at t3
  rw [mul_add, mul_add]
  linarith
theorem sum_sq_linearizedCurl_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    (R : F.GaugeField 0) (ξ : F.Site 0 → ℍ[ℝ]) (v : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (hv : ∀ x i, ((v x i : imaginaryQuaternions) : ℍ[ℝ]) = covDiff R ξ x i)
    (w : F.Site 0 → ℝ) (hw0 : ∀ x, 0 ≤ w x) (B : ℝ) (hB0 : 0 ≤ B)
    (hcurv : ∀ q ∈ innerPlaquettes S 0, 2 * ‖((plaquetteHolonomy R q : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ B) :
    ∑ q ∈ plaquettesOver S S 0, (w q.1 * ‖linearizedCurl R v q‖) ^ 2 ≤
      (4 * (B * (F.blockSide : ℝ) ^ F.top)) ^ 2 * ∑ z ∈ S, cellSiteNorm 4 S w ξ z ^ 2 := by
  classical
  have hterm : ∀ q ∈ plaquettesOver S S 0, (w q.1 * ‖linearizedCurl R v q‖) ^ 2 ≤
      B ^ 2 * (w q.1 * ‖ξ q.1‖) ^ 2 := by
    intro q hq
    have hqp : q ∈ innerPlaquettes S 0 := by
      unfold plaquettesOver at hq
      exact (Finset.mem_filter.1 hq).1
    have h2 : ‖linearizedCurl R v q‖ ≤ B * ‖ξ q.1‖ := by
      rw [linearizedCurl_covDiff _ ξ v hv q]
      exact (norm_adjointAction_sub_le _ _).trans (mul_le_mul_of_nonneg_right (hcurv q hqp) (norm_nonneg _))
    have h4 := mul_le_mul_of_nonneg_left h2 (hw0 q.1)
    have h5 : 0 ≤ w q.1 * ‖linearizedCurl R v q‖ := mul_nonneg (hw0 _) (norm_nonneg _)
    calc _ ≤ (w q.1 * (B * ‖ξ q.1‖)) ^ 2 := pow_le_pow_left₀ h5 h4 2
      _ = _ := by ring
  have hsum : ∑ q ∈ plaquettesOver S S 0, (w q.1 * ‖ξ q.1‖) ^ 2 ≤
      16 * ∑ x ∈ sitesOfCells S 0, (w x * ‖ξ x‖) ^ 2 := by
    calc ∑ q ∈ plaquettesOver S S 0, (w q.1 * ‖ξ q.1‖) ^ 2
        ≤ ∑ q ∈ sitesOfCells S 0 ×ˢ ((Finset.univ : Finset (Fin 4)) ×ˢ (Finset.univ : Finset (Fin 4))),
            (w q.1 * ‖ξ q.1‖) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
          intro q hq
          unfold plaquettesOver at hq
          exact (Finset.mem_filter.1 (Finset.mem_filter.1 hq).1).1
      _ = _ := by
          rw [Finset.sum_product]
          simp only [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.mul_sum]
          norm_num
  have hcell : ∑ x ∈ sitesOfCells S 0, (w x * ‖ξ x‖) ^ 2 ≤
      ((F.blockSide : ℝ) ^ F.top) ^ 2 * ∑ z ∈ S, cellSiteNorm 4 S w ξ z ^ 2 := by
    rw [sum_sitesOfCells_zero hamb hodd S (fun x => (w x * ‖ξ x‖) ^ 2), Finset.mul_sum]
    exact Finset.sum_le_sum fun z hz => sum_sq_le_cellSiteNorm hamb hodd hz w hw0 ξ
  calc _ ≤ ∑ q ∈ plaquettesOver S S 0, B ^ 2 * (w q.1 * ‖ξ q.1‖) ^ 2 := Finset.sum_le_sum hterm
    _ = B ^ 2 * ∑ q ∈ plaquettesOver S S 0, (w q.1 * ‖ξ q.1‖) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ B ^ 2 * (16 * (((F.blockSide : ℝ) ^ F.top) ^ 2 * ∑ z ∈ S, cellSiteNorm 4 S w ξ z ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (sq_nonneg _)
        linarith
    _ = _ := by ring
theorem sum_sq_innerBonds_top_le {S : Finset F.Cell} (T : F.Cell → ℝ) (Wt : F.Site F.top × Fin 4 → ℝ)
    (Dc : ℝ) (hDc : 0 ≤ Dc)
    (hterm : ∀ c ∈ innerBonds S F.top, 0 ≤ Wt c ∧ Wt c ≤ Dc * (T c.1 + T (c.1 + unitStep F.top c.2))) :
    ∑ c ∈ innerBonds S F.top, Wt c ^ 2 ≤ (4 * Dc) ^ 2 * ∑ z ∈ S, T z ^ 2 := by
  have h1 : ∀ c ∈ innerBonds S F.top, Wt c ^ 2 ≤
      2 * Dc ^ 2 * (T c.1 ^ 2 + T (c.1 + unitStep F.top c.2) ^ 2) := by
    intro c hc
    obtain ⟨h0, h2⟩ := hterm c hc
    set a := T c.1
    set b := T (c.1 + unitStep F.top c.2)
    have h3 := pow_le_pow_left₀ h0 h2 2
    have h4 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
    have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg Dc)
    calc Wt c ^ 2 ≤ (Dc * (a + b)) ^ 2 := h3
      _ = Dc ^ 2 * (a + b) ^ 2 := by ring
      _ ≤ Dc ^ 2 * (2 * (a ^ 2 + b ^ 2)) := h5
      _ = _ := by ring
  calc _ ≤ ∑ c ∈ innerBonds S F.top, 2 * Dc ^ 2 * (T c.1 ^ 2 + T (c.1 + unitStep F.top c.2) ^ 2) :=
        Finset.sum_le_sum h1
    _ = 2 * Dc ^ 2 * ∑ c ∈ innerBonds S F.top, (T c.1 ^ 2 + T (c.1 + unitStep F.top c.2) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * Dc ^ 2 * (8 * ∑ z ∈ S, T z ^ 2) := mul_le_mul_of_nonneg_left
        (sum_innerBonds_top_ends_le (fun z => T z ^ 2) (fun _ => sq_nonneg _)) (by positivity)
    _ = _ := by ring
theorem covariantDiffNearlyFlat (hRef : referenceBoundsStatement) (hGauge : gaugeMapOnDifferencesStatement) :
    covariantDiffNearlyFlatStatement := by
  obtain ⟨C₁, c₁, L₁, hC₁, hc₁, hB⟩ := hRef
  obtain ⟨c₂, C₂, L₂, hc₂, hC₂, hG⟩ := hGauge
  refine ⟨max (max L₁ L₂) 5, fun L hoddL hLge => ⟨min c₁ c₂, (8 + 2424 * (6 + 4 * (L : ℝ))) * C₁ * C₂,
    lt_min hc₁ hc₂, by positivity, ?_⟩⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold φ θ del p hθ hdel hφ ξ v hmf hvD
  subst hFL
  have hodd := hoddL
  have hL := hodd.pos
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
  have hL5 : 5 ≤ F.blockSide := (le_max_right _ _).trans hLge
  have hL1 : L₁ ≤ F.blockSide := ((le_max_left _ _).trans (le_max_left _ _)).trans hLge
  have hL2 : L₂ ≤ F.blockSide := ((le_max_right _ _).trans (le_max_left _ _)).trans hLge
  obtain ⟨b1, b2, b3, -, b5, -⟩ := hB F m S hodd hL1 hamb hm hreg s V hs (hsc.trans (min_le_left _ _)) hcold
  obtain ⟨-, hG'⟩ := hG F m S hodd hL2 hamb hm hreg s V hs (hsc.trans (min_le_right _ _)) hcold
  obtain ⟨-, hPoi, -⟩ := hG' ξ hmf
  have hPo := (hPoi φ θ del p hθ hdel hφ).2.1
  have hvd : ∀ x i, ((v x i : imaginaryQuaternions) : ℍ[ℝ]) = covDiff (referenceFieldChain S V 0) ξ x i := hvD
  have hsign : ∀ z, ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 :=
    fun z => (closedOrthant_spec hreg (by omega) z).1
  have hκ0 : 0 ≤ C₁ * s := by positivity
  have hNp : 0 < (F.blockSide : ℝ) ^ F.top := by positivity
  have hNc : ((cellSideLength F : ℤ) : ℝ) = (F.blockSide : ℝ) ^ F.top := by simp [cellSideLength]
  have hw0 : ∀ x, 0 ≤ classWeight F φ θ p 0 x := fun x => (classWeight_pos hL φ θ p 0 x).le
  have hMe : cellwiseL4Norm S (classWeight F φ θ p 0) (covariantDiff (referenceFieldChain S V 0) ξ) =
      cellwiseL4Norm S (classWeight F φ θ p 0) (fun x i => ((v x i : imaginaryQuaternions) : ℍ[ℝ])) := by
    congr 1
    funext x i
    exact (hvD x i).symm
  rw [hMe, hNc] at hPo
  have hB0 : 0 ≤ 2 * (C₁ * s * (1 / (F.blockSide : ℝ) ^ F.top) ^ 2) := by positivity
  have hcurl := sum_sq_linearizedCurl_le hamb hodd (referenceFieldChain S V 0) ξ v hvd
    (classWeight F φ θ p 0) hw0 _ hB0
    (fun q hq => by
      have h1 := b2 0 (Nat.succ_pos _) q hq
      rw [levelScale_zero_eq hL] at h1
      have h3 : ‖((plaquetteHolonomy (referenceFieldChain S V 0) q : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          C₁ * s * (1 / (F.blockSide : ℝ) ^ F.top) ^ 2 := h1
      linarith)
  have hDc : 0 ≤ (6 + 4 * (F.blockSide : ℝ)) * (C₁ * s) * (606 / (F.blockSide : ℝ) ^ F.top) := by positivity
  have htop := sum_sq_innerBonds_top_le (S := S) (cellSiteNorm 4 S (classWeight F φ θ p 0) ξ)
    (fun c => classWeight F φ θ p F.top c.1 *
      ‖linearPart (referenceFieldChain S V) (baseOnlyChart v) F.top c.1 c.2‖) _ hDc
    (fun c hc => by
      have hcf := Finset.mem_filter.1 hc
      have hy : c.1 ∈ S := mem_of_mem_sitesOfCells_top (Finset.mem_product.1 hcf.1).1
      have hy' : c.1 + unitStep F.top c.2 ∈ S := mem_of_mem_sitesOfCells_top hcf.2
      have h1 := norm_linearPart_top_le hamb hodd (by omega) hsign ξ v hvd (C₁ * s) hκ0
        (fun z hz j hj b hb => b1 j hj z hz b hb) b3 b5 hmf c hc
      have h2 := exp_mul_iteratedMean_ends_le hamb hodd hy hy' φ θ p hθ ξ
        (exp_le_three_mul_exp_add_unitStep φ del hdel hφ c.1 c.2)
      refine ⟨mul_nonneg (classWeight_pos hL φ θ p _ _).le (norm_nonneg _), ?_⟩
      show classWeight F φ θ p F.top c.1 * _ ≤ _
      rw [classWeight_top hodd φ θ p c.1]
      calc _ ≤ Real.exp (φ c.1) * ((6 + 4 * (F.blockSide : ℝ)) * (C₁ * s) *
              (iteratedMean (fun x => ‖ξ x‖) F.top c.1 +
                iteratedMean (fun x => ‖ξ x‖) F.top (c.1 + unitStep F.top c.2))) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = (6 + 4 * (F.blockSide : ℝ)) * (C₁ * s) * (Real.exp (φ c.1) *
              (iteratedMean (fun x => ‖ξ x‖) F.top c.1 +
                iteratedMean (fun x => ‖ξ x‖) F.top (c.1 + unitStep F.top c.2))) := by ring
        _ ≤ (6 + 4 * (F.blockSide : ℝ)) * (C₁ * s) * _ := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring)
  have r1 := sqrt_le_mul_sqrt_of_le (by positivity) hcurl
  have r2 := sqrt_le_mul_sqrt_of_le (by positivity) htop
  have hsum : 4 * (2 * (C₁ * s * (1 / (F.blockSide : ℝ) ^ F.top) ^ 2) * (F.blockSide : ℝ) ^ F.top) +
      4 * ((6 + 4 * (F.blockSide : ℝ)) * (C₁ * s) * (606 / (F.blockSide : ℝ) ^ F.top)) =
      (8 + 2424 * (6 + 4 * (F.blockSide : ℝ))) * (C₁ * s) / (F.blockSide : ℝ) ^ F.top := by
    field_simp
    ring
  have hc0 : 0 ≤ (8 + 2424 * (6 + 4 * (F.blockSide : ℝ))) * (C₁ * s) / (F.blockSide : ℝ) ^ F.top := by
    positivity
  have hgoal := add_le_add r1 r2
  rw [← add_mul, hsum] at hgoal
  refine hgoal.trans ((mul_le_mul_of_nonneg_left hPo hc0).trans (le_of_eq ?_))
  field_simp
end YangMills.Construction.NearlyFlatDifferences
end
