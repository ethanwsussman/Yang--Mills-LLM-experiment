import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainsOnATorus
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
open BlockAverages LatticePaths
variable {F : BlockFrame}
def contourAverage {j : ℕ} (B : LevelForm F j) : LevelForm F (j + 1) := fun y i =>
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    pathSum B (refineSite y) (bondContour F.blockSide h π i)
def legAverage {j : ℕ} (B : LevelForm F j) : F.Site (j + 1) → ℝ := fun y =>
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    pathSum B (refineSite y) (axisPath h π)
def contourChainMisfit (B : FormChain F) (j : ℕ) : LevelForm F (j + 1) := fun y i =>
  contourAverage (B j) y i - B (j + 1) y i
def contourChainEnergy (a : ℝ) (B : FormChain F) : ℝ :=
  (∑ x ∈ sitesOfCells (finiteCells F) 0, ∑ e ∈ orientedPlanes, plaquetteCurl (B 0) x e.1 e.2 ^ 2) +
    a * ∑ j ∈ Finset.range F.top, ∑ y ∈ sitesOfCells (finiteCells F) (j + 1), ∑ i : Fin 4,
      contourChainMisfit B j y i ^ 2
def blockLift {j : ℕ} (g : F.Site (j + 1) → ℝ) : F.Site j → ℝ := fun x => g (ancestorSite (j + 1) x)
def walkTarget {j : ℕ} : F.Site j → List PathStep → F.Site j
  | x, [] => x
  | x, st :: r => walkTarget (x + BlockAverages.stepDisplacement j st) r
theorem siteOfCoords_map_add {j : ℕ} (u v : (Fin 4 → ℤ)) :
    (siteOfCoords j (u + v) : F.Site j) = siteOfCoords j u + siteOfCoords j v := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_map_neg {j : ℕ} (u : (Fin 4 → ℤ)) :
    (siteOfCoords j (-u) : F.Site j) = - siteOfCoords j u := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_neg <;> assumption
theorem siteOfCoords_map_zero {j : ℕ} : (siteOfCoords j (0 : (Fin 4 → ℤ)) : F.Site j) = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem siteOfCoords_siteCoords_self {j : ℕ} (y : F.Site j) : siteOfCoords j (siteCoords y) = y := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem siteOfCoords_eq_of_dvd {j : ℕ} {z z' : (Fin 4 → ℤ)} (h : ∀ i, (F.period j i : ℤ) ∣ z' i - z i) :
    (siteOfCoords j z : F.Site j) = siteOfCoords j z' := by
  funext i
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (h i)
theorem period_dvd_sub_siteCoords {j : ℕ} (z : (Fin 4 → ℤ)) (i : Fin 4) :
    (F.period j i : ℤ) ∣ z i - siteCoords (siteOfCoords j z : F.Site j) i := by
  have h1 : ((ZMod.cast ((z i : ℤ) : ZMod (F.period j i)) : ℤ) : ZMod (F.period j i)) =
      ((z i : ℤ) : ZMod (F.period j i)) := ZMod.intCast_zmod_cast _
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
theorem period_eq_mul_blockSide {j : ℕ} (hj : j < F.top) (i : Fin 4) :
    F.period j i = F.period (j + 1) i * F.blockSide := by
  unfold BlockFrame.period
  have h : F.top - j = (F.top - (j + 1)) + 1 := by omega
  rw [h, pow_succ]
  ring
theorem refineSite_siteOfCoords_mul {j : ℕ} (hj : j < F.top) (z : (Fin 4 → ℤ)) :
    (refineSite (siteOfCoords (j + 1) z : F.Site (j + 1)) : F.Site j) =
      siteOfCoords j (fun i => (F.blockSide : ℤ) * z i) := by apply _root_.YangMills.Construction.BlockLines.refineSite_siteOfCoords <;> assumption
private theorem refineSite_add_unitStep {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (i : Fin 4) :
    (refineSite (y + unitStep (j + 1) i) : F.Site j) =
      refineSite y + siteOfCoords j (Pi.single i (F.blockSide : ℤ)) := by
  have e1 : y + unitStep (j + 1) i = siteOfCoords (j + 1) (siteCoords y + Pi.single i 1) := by
    rw [siteOfCoords_map_add, siteOfCoords_siteCoords_self]
    rfl
  rw [e1, refineSite_siteOfCoords_mul hj]
  have e2 : (refineSite y : F.Site j) = siteOfCoords j (fun i => (F.blockSide : ℤ) * siteCoords y i) := rfl
  rw [e2, ← siteOfCoords_map_add]
  congr 1
  funext l
  by_cases h : l = i
  · subst h; simp [mul_add]
  · simp [Pi.single_apply, h]
theorem walkTarget_append {j : ℕ} (x : F.Site j) (l l' : List PathStep) :
    walkTarget x (l ++ l') = walkTarget (walkTarget x l) l' := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih => exact ih _
theorem walkTarget_add {j : ℕ} (x u : F.Site j) (l : List PathStep) :
    walkTarget (x + u) l = walkTarget x l + u := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    show walkTarget (x + u + BlockAverages.stepDisplacement j st) r =
      walkTarget (x + BlockAverages.stepDisplacement j st) r + u
    rw [← ih]
    congr 1
    abel
theorem stepDisplacement_eq_siteOfCoords {j : ℕ} (st : PathStep) :
    (BlockAverages.stepDisplacement j st : F.Site j) = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem walkTarget_siteOfCoords {j : ℕ} (z : (Fin 4 → ℤ)) (l : List PathStep) :
    walkTarget (siteOfCoords j z : F.Site j) l = siteOfCoords j (endpoint z l) := by
  induction l generalizing z with
  | nil => rfl
  | cons st r ih =>
    show walkTarget (siteOfCoords j z + BlockAverages.stepDisplacement j st) r =
      siteOfCoords j (endpoint (z + FlatPairing.stepDisplacement st) r)
    rw [stepDisplacement_eq_siteOfCoords, ← siteOfCoords_map_add, ih]
theorem walkTarget_axisPath {j : ℕ} (x : F.Site j) (h : (Fin 4 → ℤ)) (π : Equiv.Perm (Fin 4)) :
    walkTarget x (axisPath h π) = x + siteOfCoords j h := by
  have e : walkTarget (0 + x) (axisPath h π) = walkTarget (0 : F.Site j) (axisPath h π) + x :=
    walkTarget_add _ _ _
  have e0 : walkTarget (0 : F.Site j) (axisPath h π) = siteOfCoords j h := by
    rw [← siteOfCoords_map_zero (j := j), walkTarget_siteOfCoords, (axisPath_spec h π).2]
  rw [zero_add] at e
  rw [e, e0, add_comm]
theorem walkTarget_replicate {j : ℕ} (x : F.Site j) (i : Fin 4) (n : ℕ) :
    walkTarget x (List.replicate n (i, true)) = x + siteOfCoords j (Pi.single i (n : ℤ)) := by
  induction n with
  | zero => simp [walkTarget, siteOfCoords_map_zero]
  | succ n ih =>
    rw [List.replicate_succ', walkTarget_append, ih]
    show x + siteOfCoords j (Pi.single i (n : ℤ)) + BlockAverages.stepDisplacement j (i, true) = _
    rw [stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_map_add]
    congr 2
    simp [FlatPairing.stepDisplacement, LatticeFractionalIntegration.basisVector, ← Pi.single_add]
theorem walkTarget_reversePath {j : ℕ} (x : F.Site j) (l : List PathStep) :
    walkTarget (walkTarget x l) (reversePath l) = x := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    show walkTarget (walkTarget (x + BlockAverages.stepDisplacement j st) r) (reversePath (st :: r)) = x
    rw [reversePath_cons, walkTarget_append, ih]
    show x + BlockAverages.stepDisplacement j st + BlockAverages.stepDisplacement j (st.1, !st.2) = x
    obtain ⟨d, b⟩ := st
    cases b <;> simp [BlockAverages.stepDisplacement]
theorem pathSum_append {j : ℕ} (B : LevelForm F j) (x : F.Site j) (l l' : List PathStep) :
    pathSum B x (l ++ l') = pathSum B x l + pathSum B (walkTarget x l) l' := by
  induction l generalizing x with
  | nil => simp [pathSum, walkTarget]
  | cons st r ih =>
    simp only [List.cons_append, pathSum, walkTarget]
    rw [ih]
    ring
theorem pathSum_reversePath {j : ℕ} (B : LevelForm F j) (x : F.Site j) (l : List PathStep) :
    pathSum B (walkTarget x l) (reversePath l) = - pathSum B x l := by
  induction l generalizing x with
  | nil => simp [pathSum, walkTarget, reversePath]
  | cons st r ih =>
    show pathSum B (walkTarget (x + BlockAverages.stepDisplacement j st) r) (reversePath (st :: r)) = _
    rw [reversePath_cons, pathSum_append, ih, walkTarget_reversePath]
    obtain ⟨d, b⟩ := st
    cases b <;> simp [pathSum, BlockAverages.stepDisplacement] <;> ring
theorem pathSum_replicate {j : ℕ} (B : LevelForm F j) (x : F.Site j) (i : Fin 4) (n : ℕ) :
    pathSum B x (List.replicate n (i, true)) =
      ∑ l ∈ Finset.range n, B (x + siteOfCoords j (Pi.single i (l : ℤ))) i := by
  induction n with
  | zero => simp [pathSum]
  | succ n ih =>
    rw [List.replicate_succ', pathSum_append, ih, walkTarget_replicate, Finset.sum_range_succ]
    simp [pathSum]
theorem pathSum_addGradient {j : ℕ} (B : LevelForm F j) (φ : F.Site j → ℝ) (x : F.Site j)
    (l : List PathStep) :
    pathSum (addGradient B φ) x l = pathSum B x l + (φ (walkTarget x l) - φ x) := by
  induction l generalizing x with
  | nil => simp [pathSum, walkTarget]
  | cons st r ih =>
    obtain ⟨d, b⟩ := st
    cases b
    · simp only [pathSum, walkTarget, ih, addGradient, BlockAverages.stepDisplacement]
      simp
      rw [sub_eq_add_neg x]
      ring
    · simp only [pathSum, walkTarget, ih, addGradient, BlockAverages.stepDisplacement]
      simp
      ring
theorem pathSum_bondContour {j : ℕ} (hj : j < F.top) (B : LevelForm F j) (y : F.Site (j + 1))
    (h : (Fin 4 → ℤ)) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    pathSum B (refineSite y) (bondContour F.blockSide h π i) =
      pathSum B (refineSite y) (axisPath h π) +
        (∑ l ∈ Finset.range F.blockSide,
          B (refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i (l : ℤ))) i) -
        pathSum B (refineSite (y + unitStep (j + 1) i)) (axisPath h π) := by
  unfold bondContour
  rw [pathSum_append, pathSum_append, pathSum_replicate, walkTarget_axisPath, walkTarget_append,
    walkTarget_axisPath, walkTarget_replicate]
  have e : refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i (F.blockSide : ℤ)) =
      walkTarget (refineSite (y + unitStep (j + 1) i)) (axisPath h π) := by
    rw [walkTarget_axisPath, refineSite_add_unitStep hj]
    abel
  rw [e, pathSum_reversePath]
  ring
theorem walkTarget_bondContour {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (h : (Fin 4 → ℤ))
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    walkTarget (refineSite y) (bondContour F.blockSide h π i) = refineSite (y + unitStep (j + 1) i) := by
  unfold bondContour
  rw [walkTarget_append, walkTarget_append, walkTarget_axisPath, walkTarget_replicate]
  have e : refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i (F.blockSide : ℤ)) =
      walkTarget (refineSite (y + unitStep (j + 1) i)) (axisPath h π) := by
    rw [walkTarget_axisPath, refineSite_add_unitStep hj]
    abel
  rw [e, walkTarget_reversePath]
theorem card_perm_fin_four : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = 24 := by apply _root_.YangMills.Construction.ReferenceBounds.card_perm_fin_four <;> assumption
theorem contourAverage_eq {j : ℕ} (hL : Odd F.blockSide) (hj : j < F.top) (B : LevelForm F j)
    (y : F.Site (j + 1)) (i : Fin 4) :
    contourAverage B y i = lineAverage B y i + legAverage B y - legAverage B (y + unitStep (j + 1) i) := by
  have hL0 : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hL.pos.ne'
  unfold contourAverage legAverage lineAverage
  simp_rw [pathSum_bondContour hj]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, card_perm_fin_four,
    nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  field_simp
  ring
theorem contourAverage_addGradient {j : ℕ} (hL : Odd F.blockSide) (hj : j < F.top) (B : LevelForm F j)
    (φ : F.Site j → ℝ) (y : F.Site (j + 1)) (i : Fin 4) :
    contourAverage (addGradient B φ) y i =
      contourAverage B y i + (φ (refineSite (y + unitStep (j + 1) i)) - φ (refineSite y)) := by
  have hL0 : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hL.pos.ne'
  unfold contourAverage
  simp_rw [pathSum_addGradient, walkTarget_bondContour hj]
  simp only [Finset.sum_add_distrib, Finset.sum_const, card_perm_fin_four, nsmul_eq_mul, card_centredCube hL]
  push_cast
  field_simp
theorem lineAverage_addGradient {j : ℕ} (hj : j < F.top) (hL : Odd F.blockSide) (B : LevelForm F j)
    (φ : F.Site j → ℝ) (y : F.Site (j + 1)) (i : Fin 4) :
    lineAverage (addGradient B φ) y i =
      lineAverage B y i + (blockAverage φ (y + unitStep (j + 1) i) - blockAverage φ y) := by
  unfold lineAverage blockAverage
  have e : ∀ h : Fin 4 → ℤ, ∑ l ∈ Finset.range F.blockSide,
      addGradient B φ (refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i (l : ℤ))) i =
      ∑ l ∈ Finset.range F.blockSide,
          B (refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i (l : ℤ))) i +
        (φ (refineSite (y + unitStep (j + 1) i) + siteOfCoords j h) - φ (refineSite y + siteOfCoords j h)) := by
    intro h
    unfold addGradient
    rw [Finset.sum_add_distrib]
    congr 1
    have e1 : ∀ l : ℕ, refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i (l : ℤ)) + unitStep j i =
        refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i ((l + 1 : ℕ) : ℤ)) := by
      intro l
      rw [add_assoc, show (unitStep j i : F.Site j) = siteOfCoords j (Pi.single i 1) from rfl,
        ← siteOfCoords_map_add]
      congr 2
      push_cast
      rw [Pi.single_add]
    simp_rw [e1]
    rw [Finset.sum_range_sub
      (fun l : ℕ => φ (refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i (l : ℤ))))]
    rw [refineSite_add_unitStep hj]
    have e2 : refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i ((0 : ℕ) : ℤ)) =
        refineSite y + siteOfCoords j h := by
      simp [siteOfCoords_map_zero]
    rw [e2, add_right_comm]
  simp_rw [e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring
theorem ancestorSite_refineSite_add {j : ℕ} (hL : Odd F.blockSide) (hj : j < F.top) (y : F.Site (j + 1))
    {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide) :
    ancestorSite (j + 1) (refineSite y + siteOfCoords j h : F.Site j) = y := by
  obtain ⟨k, hk⟩ := hL
  have hx : (refineSite y + siteOfCoords j h : F.Site j) =
      siteOfCoords j (fun i => (F.blockSide : ℤ) * siteCoords y i + h i) := by
    have : (refineSite y : F.Site j) = siteOfCoords j (fun i => (F.blockSide : ℤ) * siteCoords y i) := rfl
    rw [this, ← siteOfCoords_map_add]
    rfl
  rw [hx]
  unfold ancestorSite
  conv_rhs => rw [← siteOfCoords_siteCoords_self y]
  apply siteOfCoords_eq_of_dvd
  intro i
  obtain ⟨d, hd⟩ := period_dvd_sub_siteCoords (F := F) (j := j)
    (fun i => (F.blockSide : ℤ) * siteCoords y i + h i) i
  have hc : ((F.blockSide : ℤ) - 1) / 2 = k := by
    have : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    rw [this]
    omega
  have hi := (Finset.mem_Icc.1 ((Fintype.mem_piFinset.1 hh) i))
  rw [hc] at hi
  have e1 : j + 1 - j = 1 := by omega
  simp only [e1, pow_one, hc]
  have hper := period_eq_mul_blockSide hj i
  set z' := siteCoords (siteOfCoords j (fun i => (F.blockSide : ℤ) * siteCoords y i + h i) : F.Site j) i
    with hz'
  have e2 : z' + (k : ℤ) =
      (h i + k) + (F.blockSide : ℤ) * (siteCoords y i - (F.period (j + 1) i : ℤ) * d) := by
    have hd2 : (F.blockSide : ℤ) * siteCoords y i + h i - z' = (F.period j i : ℤ) * d := hd
    rw [hper] at hd2
    push_cast at hd2
    linear_combination -hd2
  have hLpos : (0 : ℤ) < (F.blockSide : ℤ) := by omega
  have e3 : (z' + (k : ℤ)) / (F.blockSide : ℤ) = siteCoords y i - (F.period (j + 1) i : ℤ) * d := by
    rw [e2, Int.add_mul_ediv_left _ _ hLpos.ne']
    have : (h i + k) / (F.blockSide : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    rw [this, zero_add]
  rw [e3]
  exact ⟨d, by ring⟩
theorem zero_mem_centredCube (L : ℕ) (hL : Odd L) : (0 : Fin 4 → ℤ) ∈ centredCube L := by
  obtain ⟨k, hk⟩ := hL
  unfold centredCube
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have : (L : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  simp only [Pi.zero_apply]
  omega
theorem blockLift_refineSite {j : ℕ} (hL : Odd F.blockSide) (hj : j < F.top) (g : F.Site (j + 1) → ℝ)
    (y : F.Site (j + 1)) : blockLift g (refineSite y : F.Site j) = g y := by
  unfold blockLift
  have := ancestorSite_refineSite_add hL hj y (zero_mem_centredCube F.blockSide hL)
  rw [siteOfCoords_map_zero, add_zero] at this
  rw [this]
theorem blockAverage_blockLift {j : ℕ} (hL : Odd F.blockSide) (hj : j < F.top) (g : F.Site (j + 1) → ℝ)
    (y : F.Site (j + 1)) : blockAverage (blockLift g : F.Site j → ℝ) y = g y := by
  have hL0 : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hL.pos.ne'
  unfold blockAverage blockLift
  rw [Finset.sum_congr rfl fun h hh => by rw [ancestorSite_refineSite_add hL hj y hh]]
  rw [Finset.sum_const, card_centredCube hL, nsmul_eq_mul]
  push_cast
  field_simp
theorem plaquetteCurl_addGradient {j : ℕ} (B : LevelForm F j) (φ : F.Site j → ℝ) (x : F.Site j)
    (μ ν : Fin 4) : plaquetteCurl (addGradient B φ) x μ ν = plaquetteCurl B x μ ν := by
  unfold plaquetteCurl addGradient
  rw [add_right_comm x (unitStep j ν) (unitStep j μ)]
  ring
theorem exists_descending_gauge (S : (j : ℕ) → F.Site (j + 1) → ℝ) :
    ∃ ν : (j : ℕ) → F.Site j → ℝ, ν F.top = 0 ∧
      ∀ j, j < F.top → ν j = blockLift (ν (j + 1) + S j) := by
  have key : ∀ k, k ≤ F.top → ∃ ν : (j : ℕ) → F.Site j → ℝ, ν F.top = 0 ∧
      ∀ j, F.top ≤ j + k → j < F.top → ν j = blockLift (ν (j + 1) + S j) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun _ _ => 0, rfl, fun j h1 h2 => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨ν, h0, h1⟩ := ih (by omega)
      set j₀ := F.top - (k + 1) with hj₀
      refine ⟨Function.update ν j₀ (blockLift (ν (j₀ + 1) + S j₀)), ?_, ?_⟩
      · rw [Function.update_of_ne (by omega)]
        exact h0
      · intro j h2 h3
        by_cases hj : j = j₀
        · subst hj
          rw [Function.update_self, Function.update_of_ne (by omega)]
        · rw [Function.update_of_ne hj, Function.update_of_ne (by omega)]
          exact h1 j (by omega) h3
  obtain ⟨ν, h0, h1⟩ := key F.top le_rfl
  exact ⟨ν, h0, fun j hj => h1 j (by omega) hj⟩
theorem exists_lineChain_of_contourChain (hL : Odd F.blockSide) (β : FormChain F) :
    ∃ B : FormChain F, B F.top = β F.top ∧
      (∀ j x μ ν, plaquetteCurl (B j) x μ ν = plaquetteCurl (β j) x μ ν) ∧
      ∀ j, j < F.top → ∀ y i, chainMisfit B j y i = contourChainMisfit β j y i := by
  obtain ⟨ν, h0, h1⟩ := exists_descending_gauge (F := F) fun j => - legAverage (β j)
  refine ⟨fun j => addGradient (β j) (ν j), ?_, fun j x μ ν' => plaquetteCurl_addGradient _ _ _ _ _, ?_⟩
  · funext x i
    simp [addGradient, h0]
  · intro j hj y i
    have hb : ∀ y, blockAverage (ν j) y = ν (j + 1) y - legAverage (β j) y := by
      intro y
      rw [h1 j hj, blockAverage_blockLift hL hj]
      simp [sub_eq_add_neg]
    unfold chainMisfit contourChainMisfit
    rw [lineAverage_addGradient hj hL, contourAverage_eq hL hj, hb, hb]
    simp only [addGradient]
    ring
theorem exists_contourChain_of_lineChain (hL : Odd F.blockSide) (U : FormChain F) :
    ∃ B : FormChain F, B F.top = U F.top ∧
      (∀ j x μ ν, plaquetteCurl (B j) x μ ν = plaquetteCurl (U j) x μ ν) ∧
      ∀ j, j < F.top → ∀ y i, contourChainMisfit B j y i = chainMisfit U j y i := by
  obtain ⟨ν, h0, h1⟩ := exists_descending_gauge (F := F) fun j => legAverage (U j)
  refine ⟨fun j => addGradient (U j) (ν j), ?_, fun j x μ ν' => plaquetteCurl_addGradient _ _ _ _ _, ?_⟩
  · funext x i
    simp [addGradient, h0]
  · intro j hj y i
    have hb : ∀ y, ν j (refineSite y) = ν (j + 1) y + legAverage (U j) y := by
      intro y
      rw [h1 j hj, blockLift_refineSite hL hj]
      rfl
    unfold chainMisfit contourChainMisfit
    rw [contourAverage_addGradient hL hj, contourAverage_eq hL hj, hb, hb]
    simp only [addGradient]
    ring
theorem contourChainEnergy_eq (a : ℝ) (β U : FormChain F)
    (hc : ∀ x μ ν, plaquetteCurl (β 0) x μ ν = plaquetteCurl (U 0) x μ ν)
    (hm : ∀ j, j < F.top → ∀ y i, contourChainMisfit β j y i = chainMisfit U j y i) :
    contourChainEnergy a β = chainEnergyPolar a U U := by
  unfold contourChainEnergy chainEnergyPolar
  congr 1
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun e _ => ?_
    rw [hc, sq]
  · congr 1
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hm j (Finset.mem_range.1 hj), sq]
theorem plaquetteCurl_add_smul {j : ℕ} (B D : LevelForm F j) (ε : ℝ) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteCurl (fun x i => B x i + ε * D x i) x μ ν = plaquetteCurl B x μ ν + ε * plaquetteCurl D x μ ν := by
  unfold plaquetteCurl
  ring
private theorem lineAverage_add_smul {j : ℕ} (B D : LevelForm F j) (ε : ℝ) (y : F.Site (j + 1)) (i : Fin 4) :
    lineAverage (fun x i => B x i + ε * D x i) y i = lineAverage B y i + ε * lineAverage D y i := by
  unfold lineAverage
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
theorem chainEnergyPolar_add_smul (a ε : ℝ) (B D : FormChain F) :
    chainEnergyPolar a (fun j x i => B j x i + ε * D j x i) (fun j x i => B j x i + ε * D j x i) =
      chainEnergyPolar a B B + 2 * ε * chainEnergyPolar a B D + ε ^ 2 * chainEnergyPolar a D D := by
  have hm : ∀ (j : ℕ) (y : F.Site (j + 1)) (i : Fin 4),
      chainMisfit (fun j x i => B j x i + ε * D j x i) j y i = chainMisfit B j y i + ε * chainMisfit D j y i := by
    intro j y i
    unfold chainMisfit
    rw [lineAverage_add_smul]
    ring
  have t : ∀ u v : ℝ, (u + ε * v) * (u + ε * v) = u * u + 2 * ε * (u * v) + ε ^ 2 * (v * v) := by
    intro u v
    ring
  unfold chainEnergyPolar
  simp only [plaquetteCurl_add_smul, hm, t, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
theorem exists_flatChain_of_isLeast_contourEnergy (a : ℝ) (hL : Odd F.blockSide)
    (c : F.Site F.top × Fin 4) (β : FormChain F) (htop : β F.top = topBondIndicator c)
    (hleast : ∀ U : FormChain F, U F.top = topBondIndicator c → contourChainEnergy a β ≤ chainEnergyPolar a U U) :
    ∃ B : FormChain F, IsFlatChain a c B ∧
      (∀ x μ ν, plaquetteCurl (B F.depth) x μ ν = plaquetteCurl (β F.depth) x μ ν) ∧
      ∀ y i, contourAverage (β F.depth) y i = topBondIndicator c y i + chainMisfit B F.depth y i := by
  obtain ⟨B, h1, h2, h3⟩ := exists_lineChain_of_contourChain hL β
  have he : contourChainEnergy a β = chainEnergyPolar a B B :=
    contourChainEnergy_eq a β B (fun x μ ν => (h2 0 x μ ν).symm) fun j hj y i => (h3 j hj y i).symm
  refine ⟨B, ⟨h1.trans htop, ?_⟩, fun x μ ν => h2 _ x μ ν, ?_⟩
  · intro D hD
    have hq : ∀ ε : ℝ, 0 ≤ 2 * ε * chainEnergyPolar a B D + ε ^ 2 * chainEnergyPolar a D D := by
      intro ε
      have := hleast (fun j x i => B j x i + ε * D j x i) (by
        funext x i
        simp [hD, h1, htop])
      rw [he, chainEnergyPolar_add_smul] at this
      linarith
    by_contra hne
    set p := chainEnergyPolar a B D with hp
    set q := chainEnergyPolar a D D with hq'
    have hq0 : 0 ≤ q := by
      have h1 := hq 1
      have h2 := hq (-1)
      nlinarith
    have h3 := hq (-p / (q + 1))
    have e : 2 * (-p / (q + 1)) * p + (-p / (q + 1)) ^ 2 * q = - (p ^ 2 * (q + 2)) / (q + 1) ^ 2 := by
      field_simp
      ring
    rw [e] at h3
    have h4 : 0 < p ^ 2 := by positivity
    have h5 : - (p ^ 2 * (q + 2)) / (q + 1) ^ 2 < 0 := by
      apply div_neg_of_neg_of_pos
      · nlinarith
      · positivity
    linarith
  · intro y i
    have := h3 F.depth (by simp [BlockFrame.top]) y i
    rw [this]
    unfold contourChainMisfit
    rw [htop]
    ring
end ColdStepAtMirrorFrames
end YangMills.Construction
end
