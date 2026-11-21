import YangMills.Construction.ColdChainAtEveryLevel.FloorOfTheChartFormProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelowProof
import YangMills.Construction.ColdStepAtMirrorFrames.ContourOfAChartFieldProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.TorusForms.BlocksCorridorsDomainsTreesProof
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfACellProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockMeansOfFormsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbersProof
import YangMills.Construction.ColdStepAtMirrorFrames.SizeOfAFlatResponse
import YangMills.Construction.ColdStepAtMirrorFrames.SquareSumOfTheCurlOfAFlatChain
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace AxialResponseDecay
variable {F : BlockFrame}
def halfSide (F : BlockFrame) : ℤ := ((F.blockSide : ℤ) - 1) / 2
theorem blockSide_eq_two_mul_halfSide (hL : Odd F.blockSide) : (F.blockSide : ℤ) = 2 * halfSide F + 1 := by apply _root_.YangMills.Construction.GaugeFixing.blockSide_eq_two_mul_halfSide_add_one <;> assumption
theorem halfSide_nonneg (hL : Odd F.blockSide) : 0 ≤ halfSide F := by apply _root_.YangMills.Construction.BlockAverages.ChartFloor.halfSide_nonneg <;> assumption
def InBlock (F : BlockFrame) (o : Fin 4 → ℤ) : Prop := ∀ i, - halfSide F ≤ o i ∧ o i ≤ halfSide F
theorem mem_centredCube_iff (o : Fin 4 → ℤ) : o ∈ centredCube F.blockSide ↔ InBlock F o := by
  simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc, InBlock, halfSide]
theorem siteOfCoords_congr {j : ℕ} {u v : Fin 4 → ℤ} (h : ∀ i, (F.period j i : ℤ) ∣ v i - u i) :
    (siteOfCoords j u : F.Site j) = siteOfCoords j v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_eq_of_dvd <;> assumption
theorem siteOfCoords_add {j : ℕ} (u v : Fin 4 → ℤ) :
    (siteOfCoords j (u + v) : F.Site j) = siteOfCoords j u + siteOfCoords j v := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_sub {j : ℕ} (u v : Fin 4 → ℤ) :
    (siteOfCoords j (u - v) : F.Site j) = siteOfCoords j u - siteOfCoords j v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.siteOfCoords_sub <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem dvd_siteCoords_sub {j : ℕ} (z : Fin 4 → ℤ) (i : Fin 4) :
    (F.period j i : ℤ) ∣ siteCoords (siteOfCoords j z : F.Site j) i - z i := by
  have h : siteCoords (siteOfCoords j z : F.Site j) i = z i % (F.period j i : ℤ) := by
    simp only [siteCoords, siteOfCoords]
    exact ZMod.coe_intCast _
  rw [h, Int.emod_def]
  exact ⟨- (z i / (F.period j i : ℤ)), by ring⟩
theorem period_depth (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
def blockSite (q o : Fin 4 → ℤ) : F.Site F.depth := siteOfCoords F.depth fun i => (F.blockSide : ℤ) * q i + o i
theorem blockSite_add (q o v : Fin 4 → ℤ) :
    (blockSite q o : F.Site F.depth) + siteOfCoords F.depth v = blockSite q (o + v) := by
  unfold blockSite
  rw [← _root_.YangMills.Construction.ColdStepAtMirrorFrames.AxialResponseDecay.siteOfCoords_add]
  congr 1
  funext i
  simp only [Pi.add_apply]
  ring
theorem blockSite_sub (q o v : Fin 4 → ℤ) :
    (blockSite q o : F.Site F.depth) - siteOfCoords F.depth v = blockSite q (o - v) := by
  unfold blockSite
  rw [← siteOfCoords_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  ring
theorem blockSite_add_unitStep (q o : Fin 4 → ℤ) (i : Fin 4) :
    (blockSite q o : F.Site F.depth) + unitStep F.depth i = blockSite q (o + Pi.single i 1) :=
  blockSite_add q o _
theorem blockSite_sub_unitStep (q o : Fin 4 → ℤ) (i : Fin 4) :
    (blockSite q o : F.Site F.depth) - unitStep F.depth i = blockSite q (o - Pi.single i 1) :=
  blockSite_sub q o _
theorem blockSite_shift (q o : Fin 4 → ℤ) (i : Fin 4) :
    (blockSite q o : F.Site F.depth) = blockSite (q + Pi.single i 1) (o - Pi.single i (F.blockSide : ℤ)) := by
  unfold blockSite
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp
    ring
  · simp [Pi.single_eq_of_ne hk]
theorem blockSite_congr {q q' : Fin 4 → ℤ} (o : Fin 4 → ℤ)
    (h : ∀ i, (F.extent i : ℤ) ∣ q' i - q i) : (blockSite q o : F.Site F.depth) = blockSite q' o := by
  unfold blockSite
  apply siteOfCoords_congr
  intro i
  rw [period_depth]
  obtain ⟨k, hk⟩ := h i
  refine ⟨k, ?_⟩
  have : (F.blockSide : ℤ) * q' i + o i - ((F.blockSide : ℤ) * q i + o i) = (F.blockSide : ℤ) * (q' i - q i) := by ring
  rw [this, hk]
  push_cast
  ring
theorem refineSite_eq (y : F.Cell) : (_root_.YangMills.Construction.BlockAverages.refineSite y : F.Site F.depth) = blockSite (siteCoords y) 0 := by
  simp [_root_.YangMills.Construction.BlockAverages.refineSite, blockSite]
theorem enclosingCell_siteOfCoords (z : Fin 4 → ℤ) (hL : 0 < F.blockSide) :
    enclosingCell (siteOfCoords F.depth z : F.Site F.depth) =
      siteOfCoords F.top fun i => (z i + halfSide F) / (F.blockSide : ℤ) := by
  apply siteOfCoords_congr
  intro i
  obtain ⟨k, hk⟩ := dvd_siteCoords_sub (F := F) (j := F.depth) z i
  rw [period_depth] at hk
  rw [period_top]
  have hn : F.top - F.depth = 1 := by simp
  rw [hn, pow_one]
  have hne : (F.blockSide : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hc : siteCoords (siteOfCoords F.depth z : F.Site F.depth) i + halfSide F =
      (z i + halfSide F) + (F.blockSide : ℤ) * (((F.extent i : ℤ)) * k) := by
    push_cast at hk
    linear_combination hk
  have hh : ((F.blockSide : ℤ) - 1) / 2 = halfSide F := rfl
  rw [hh, hc, Int.add_mul_ediv_left _ _ hne]
  exact ⟨- k, by ring⟩
theorem ediv_blockSide_of_inBlock (hL : Odd F.blockSide) (q o : Fin 4 → ℤ) (ho : InBlock F o) (i : Fin 4) :
    ((F.blockSide : ℤ) * q i + o i + halfSide F) / (F.blockSide : ℤ) = q i := by
  have h2 := blockSide_eq_two_mul_halfSide hL
  have hpos : (0 : ℤ) < F.blockSide := by exact_mod_cast hL.pos
  have e : (F.blockSide : ℤ) * q i + o i + halfSide F = (o i + halfSide F) + (F.blockSide : ℤ) * q i := by ring
  rw [e, Int.add_mul_ediv_left _ _ hpos.ne', Int.ediv_eq_zero_of_lt (by linarith [(ho i).1]) (by linarith [(ho i).2]),
    zero_add]
theorem enclosingCell_blockSite (hL : Odd F.blockSide) (q o : Fin 4 → ℤ) (ho : InBlock F o) :
    enclosingCell (blockSite q o : F.Site F.depth) = siteOfCoords F.top q := by
  unfold blockSite
  rw [enclosingCell_siteOfCoords _ hL.pos]
  congr 1
  funext i
  exact ediv_blockSide_of_inBlock hL q o ho i
theorem cellOffset_blockSite (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (q o : Fin 4 → ℤ) (ho : InBlock F o)
    (i : Fin 4) : cellOffset (blockSite q o : F.Site F.depth) i = o i := by
  unfold cellOffset
  rw [enclosingCell_blockSite hL q o ho]
  have hc : (cellCentre F.depth (siteOfCoords F.top q : F.Cell) : F.Site F.depth) = blockSite q 0 := by
    unfold cellCentre
    have hn : F.top - F.depth = 1 := by simp
    rw [hn, pow_one]
    unfold blockSite
    apply siteOfCoords_congr
    intro k
    rw [period_depth]
    obtain ⟨u, hu⟩ := dvd_siteCoords_sub (F := F) (j := F.top) q k
    rw [period_top] at hu
    refine ⟨- u, ?_⟩
    simp only [Pi.zero_apply, add_zero]
    push_cast
    linear_combination (- (F.blockSide : ℤ)) * hu
  rw [hc]
  have hx : (blockSite q o : F.Site F.depth) - blockSite q 0 = siteOfCoords F.depth o := by
    have := blockSite_add (F := F) q 0 o
    rw [zero_add] at this
    rw [← this]
    abel
  rw [hx]
  have h2 := blockSide_eq_two_mul_halfSide hL
  have hper : ((F.blockSide : ℤ)) ≤ (F.period F.depth i : ℤ) := by
    rw [period_depth]
    have h1 : (1 : ℤ) ≤ F.extent i := by exact_mod_cast hs i
    push_cast
    have hp : (0 : ℤ) ≤ F.blockSide := by positivity
    nlinarith
  have : NeZero (F.period F.depth i) := ⟨by
    rw [period_depth]
    exact Nat.mul_ne_zero (hs i).ne' hL.pos.ne'⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩
  · linarith [(ho i).1]
  · linarith [(ho i).2]
theorem exists_blockSite (hL : Odd F.blockSide) (x : F.Site F.depth) :
    ∃ o, InBlock F o ∧ x = blockSite (siteCoords (enclosingCell x)) o := by
  have h2 := blockSide_eq_two_mul_halfSide hL
  have hpos : (0 : ℤ) < F.blockSide := by exact_mod_cast hL.pos
  let q : Fin 4 → ℤ := fun i => (siteCoords x i + halfSide F) / (F.blockSide : ℤ)
  let o : Fin 4 → ℤ := fun i => siteCoords x i - (F.blockSide : ℤ) * q i
  have ho : InBlock F o := by
    intro i
    have e1 := Int.emod_add_mul_ediv (siteCoords x i + halfSide F) (F.blockSide : ℤ)
    have e2 := Int.emod_nonneg (siteCoords x i + halfSide F) hpos.ne'
    have e3 := Int.emod_lt_of_pos (siteCoords x i + halfSide F) hpos
    constructor <;> linarith
  have hx : x = blockSite q o := by
    conv_lhs => rw [← siteOfCoords_siteCoords x]
    unfold blockSite
    congr 1
    funext i
    simp only [o]
    ring
  refine ⟨o, ho, ?_⟩
  have hc : enclosingCell x = siteOfCoords F.top q := by
    rw [hx]
    exact enclosingCell_blockSite hL q o ho
  rw [hc]
  conv_lhs => rw [hx]
  apply blockSite_congr
  intro i
  have := dvd_siteCoords_sub (F := F) (j := F.top) q i
  rw [period_top] at this
  exact this
theorem not_isCrossingBond (hL : Odd F.blockSide) (q o : Fin 4 → ℤ) (ho : InBlock F o) (i : Fin 4)
    (hi : o i ≠ halfSide F) : ¬ IsCrossingBond ((blockSite q o : F.Site F.depth), i) := by
  unfold IsCrossingBond
  simp only [not_not]
  have ho' : InBlock F (o + Pi.single i 1) := by
    intro k
    by_cases hk : k = i
    · subst hk
      have := (ho k).1
      have h3 := (ho k).2
      have : o k < halfSide F := lt_of_le_of_ne h3 hi
      simp
      constructor <;> omega
    · simpa [Pi.single_eq_of_ne hk] using ho k
  rw [blockSite_add_unitStep, enclosingCell_blockSite hL q _ ho', enclosingCell_blockSite hL q o ho]
theorem isAxialTreeBond_blockSite (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (q o : Fin 4 → ℤ) (ho : InBlock F o)
    (i : Fin 4) (hi : o i ≠ halfSide F) (h0 : ∀ l, i < l → o l = 0) :
    IsAxialTreeBond ((blockSite q o : F.Site F.depth), i) := by
  refine ⟨not_isCrossingBond hL q o ho i hi, ?_⟩
  intro l hl
  rw [cellOffset_blockSite hL hs q o ho l]
  exact h0 l hl
def pathDisplacement (F : BlockFrame) (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathDisplacement_nil (j : ℕ) : pathDisplacement F j [] = 0 := by simp [pathDisplacement]
theorem pathDisplacement_cons (j : ℕ) (st : PathStep) (r : List PathStep) :
    pathDisplacement F j (st :: r) = stepDisplacement j st + pathDisplacement F j r := by simp [pathDisplacement]
theorem pathDisplacement_append (j : ℕ) (l₁ l₂ : List PathStep) :
    pathDisplacement F j (l₁ ++ l₂) = pathDisplacement F j l₁ + pathDisplacement F j l₂ := by simp [pathDisplacement]
theorem pathSum_append {j : ℕ} (B : LevelForm F j) (l₁ l₂ : List PathStep) (x : F.Site j) :
    pathSum B x (l₁ ++ l₂) = pathSum B x l₁ + pathSum B (x + pathDisplacement F j l₁) l₂ := by
  induction l₁ generalizing x with
  | nil => simp [pathSum, pathDisplacement_nil]
  | cons st r ih =>
    simp only [List.cons_append, pathSum]
    rw [ih, pathDisplacement_cons, add_assoc, add_assoc]
theorem stepDisplacement_flip (j : ℕ) (d : Fin 4) (s : Bool) :
    (stepDisplacement j (d, !s) : F.Site j) = - stepDisplacement j (d, s) := by
  cases s <;> simp [stepDisplacement]
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement F j (reversePath l) = - pathDisplacement F j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem pathSum_reversePath {j : ℕ} (B : LevelForm F j) (l : List PathStep) (x : F.Site j) :
    pathSum B (x + pathDisplacement F j l) (reversePath l) = - pathSum B x l := by
  induction l generalizing x with
  | nil => simp [reversePath, pathSum]
  | cons st r ih =>
    have hrev : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have e1 : x + pathDisplacement F j (st :: r) = (x + stepDisplacement j st) + pathDisplacement F j r := by
      rw [pathDisplacement_cons, add_assoc]
    rw [hrev, pathSum_append, e1, ih (x + stepDisplacement j st), pathDisplacement_reversePath]
    have e2 : x + stepDisplacement j st + pathDisplacement F j r + - pathDisplacement F j r =
        x + stepDisplacement j st := by abel
    rw [e2]
    obtain ⟨d, s⟩ := st
    cases s <;> simp [pathSum, stepDisplacement] <;> ring_nf
def stepSign (s : Bool) : ℤ := if s then 1 else -1
theorem stepSign_true : stepSign true = 1 := rfl
theorem stepSign_false : stepSign false = -1 := rfl
theorem siteOfCoords_zero (j : ℕ) : (siteOfCoords j 0 : F.Site j) = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem stepDisplacement_eq (j : ℕ) (d : Fin 4) (s : Bool) :
    (stepDisplacement j (d, s) : F.Site j) = siteOfCoords j (Pi.single d (stepSign s)) := by
  cases s
  · have h : (Pi.single d (-1 : ℤ) : Fin 4 → ℤ) = 0 - Pi.single d 1 := by
      rw [zero_sub, Pi.single_neg]
    simp only [stepDisplacement, stepSign]
    simp only [Bool.false_eq_true, if_false]
    rw [h, siteOfCoords_sub, siteOfCoords_zero, zero_sub]
    rfl
  · simp [stepDisplacement, stepSign, unitStep]
theorem pathDisplacement_replicate (d : Fin 4) (s : Bool) (n : ℕ) :
    pathDisplacement F F.depth (List.replicate n (d, s)) = siteOfCoords F.depth (Pi.single d ((n : ℤ) * stepSign s)) := by
  induction n with
  | zero => simp [pathDisplacement_nil, siteOfCoords_zero]
  | succ n ih =>
    rw [List.replicate_succ, pathDisplacement_cons, ih, stepDisplacement_eq, ← _root_.YangMills.Construction.ColdStepAtMirrorFrames.AxialResponseDecay.siteOfCoords_add]
    congr 1
    rw [← Pi.single_add]
    congr 1
    push_cast
    ring
theorem InBlock.add_single {o : Fin 4 → ℤ} (ho : InBlock F o) (d : Fin 4) (v : ℤ)
    (h1 : - halfSide F ≤ o d + v) (h2 : o d + v ≤ halfSide F) : InBlock F (o + Pi.single d v) := by
  intro k
  by_cases hk : k = d
  · subst hk
    simpa using ⟨h1, h2⟩
  · simpa [Pi.single_eq_of_ne hk] using ho k
theorem pathSum_replicate_le {W : LevelForm F F.depth} {q : Fin 4 → ℤ} {Bd : ℝ} (hb0 : 0 ≤ Bd)
    (hbd : ∀ o, InBlock F o → ∀ i, o i ≠ halfSide F → |W (blockSite q o) i| ≤ Bd) (d : Fin 4) (s : Bool) :
    ∀ (n : ℕ) (o : Fin 4 → ℤ), InBlock F o → - halfSide F ≤ o d + (n : ℤ) * stepSign s →
      o d + (n : ℤ) * stepSign s ≤ halfSide F →
      |pathSum W (blockSite q o) (List.replicate n (d, s))| ≤ (n : ℝ) * Bd := by
  intro n
  induction n with
  | zero =>
    intro o _ _ _
    simp [pathSum]
  | succ n ih =>
    intro o ho h1 h2
    rw [List.replicate_succ]
    simp only [pathSum]
    have hc := ho d
    have hnext : (blockSite q o : F.Site F.depth) + stepDisplacement F.depth (d, s) =
        blockSite q (o + Pi.single d (stepSign s)) := by
      rw [stepDisplacement_eq, blockSite_add]
    rw [hnext]
    have hn0 : (0 : ℤ) ≤ n := by positivity
    cases s with
    | true =>
      simp only [stepSign_true, if_true] at h1 h2 ih ⊢
      push_cast at h1 h2
      have hne : o d ≠ halfSide F := by omega
      have hcube : InBlock F (o + Pi.single d 1) := InBlock.add_single ho d 1 (by omega) (by omega)
      have hr := ih (o + Pi.single d 1) hcube (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
        (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
      have hf := hbd o ho d hne
      have := abs_add_le (W (blockSite q o) d) (pathSum W (blockSite q (o + Pi.single d 1))
        (List.replicate n (d, true)))
      push_cast
      linarith
    | false =>
      simp only [stepSign_false, Bool.false_eq_true, if_false] at h1 h2 ih ⊢
      push_cast at h1 h2
      have hcube : InBlock F (o + Pi.single d (-1)) := InBlock.add_single ho d (-1) (by omega) (by omega)
      have hr := ih (o + Pi.single d (-1)) hcube (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
        (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
      have hprev : (blockSite q o : F.Site F.depth) - unitStep F.depth d = blockSite q (o + Pi.single d (-1)) := by
        rw [blockSite_sub_unitStep, Pi.single_neg, sub_eq_add_neg]
      have hne : (o + Pi.single d (-1) : Fin 4 → ℤ) d ≠ halfSide F := by
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      have hf := hbd _ hcube d hne
      rw [hprev]
      have := abs_add_le (- W (blockSite q (o + Pi.single d (-1))) d)
        (pathSum W (blockSite q (o + Pi.single d (-1))) (List.replicate n (d, false)))
      rw [abs_neg] at this
      push_cast
      linarith
def axisFlows (h : Fin 4 → ℤ) (ds : List (Fin 4)) : List PathStep :=
  ds.flatMap fun d => List.replicate (h d).natAbs (d, decide (0 ≤ h d))
theorem axisPath_eq_axisFlows (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π = axisFlows h ((List.finRange 4).map π) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.axisPath_eq_flatMap <;> assumption
theorem natAbs_mul_stepSign (v : ℤ) : (v.natAbs : ℤ) * stepSign (decide (0 ≤ v)) = v := by apply _root_.YangMills.Construction.BlockSpin.BlockGeometry.natAbs_mul_signOfMove <;> assumption
theorem pathSum_axisFlows_le {W : LevelForm F F.depth} {q : Fin 4 → ℤ} {Bd : ℝ} (hL : Odd F.blockSide) (hb0 : 0 ≤ Bd)
    (hbd : ∀ o, InBlock F o → ∀ i, o i ≠ halfSide F → |W (blockSite q o) i| ≤ Bd) {h : Fin 4 → ℤ}
    (hh : InBlock F h) :
    ∀ (ds : List (Fin 4)) (o : Fin 4 → ℤ), ds.Nodup → InBlock F o → (∀ d ∈ ds, o d = 0) →
      |pathSum W (blockSite q o) (axisFlows h ds)| ≤ (ds.length : ℝ) * ((halfSide F : ℝ) * Bd) := by
  intro ds
  induction ds with
  | nil =>
    intro o _ _ _
    simp [axisFlows, pathSum]
  | cons d ds ih =>
    intro o hnd ho h0
    have hrun : axisFlows h (d :: ds) = List.replicate (h d).natAbs (d, decide (0 ≤ h d)) ++ axisFlows h ds := by
      simp [axisFlows, List.flatMap_cons]
    have hod : o d = 0 := h0 d (by simp)
    have hv := natAbs_mul_stepSign (h d)
    have hr := pathSum_replicate_le hb0 hbd d (decide (0 ≤ h d)) (h d).natAbs o ho
      (by rw [hv, hod, zero_add]; exact (hh d).1) (by rw [hv, hod, zero_add]; exact (hh d).2)
    have hcube : InBlock F (o + Pi.single d (h d)) :=
      InBlock.add_single ho d _ (by rw [hod, zero_add]; exact (hh d).1)
        (by rw [hod, zero_add]; exact (hh d).2)
    have hnd' := List.nodup_cons.mp hnd
    have hrest := ih (o + Pi.single d (h d)) hnd'.2 hcube (by
      intro d' hd'
      have hne : d' ≠ d := fun e => hnd'.1 (e ▸ hd')
      simp [Pi.single_eq_of_ne hne, h0 d' (by simp [hd'])])
    rw [hrun, pathSum_append, pathDisplacement_replicate, hv, blockSite_add]
    have hn : ((h d).natAbs : ℝ) ≤ (halfSide F : ℝ) := by
      have h1 : ((h d).natAbs : ℤ) ≤ halfSide F := by
        have := hh d
        omega
      calc ((h d).natAbs : ℝ) = (((h d).natAbs : ℤ) : ℝ) := (Int.cast_natCast _).symm
        _ ≤ (halfSide F : ℝ) := Int.cast_le.mpr h1
    have hm : ((h d).natAbs : ℝ) * Bd ≤ (halfSide F : ℝ) * Bd := mul_le_mul_of_nonneg_right hn hb0
    have := abs_add_le (pathSum W (blockSite q o) (List.replicate (h d).natAbs (d, decide (0 ≤ h d))))
      (pathSum W (blockSite q (o + Pi.single d (h d))) (axisFlows h ds))
    simp only [List.length_cons]
    push_cast
    linarith
theorem pathDisplacement_axisFlows (h : Fin 4 → ℤ) (ds : List (Fin 4)) :
    pathDisplacement F F.depth (axisFlows h ds) = siteOfCoords F.depth ((ds.map fun d => Pi.single d (h d)).sum) := by
  induction ds with
  | nil => simp [axisFlows, pathDisplacement_nil, siteOfCoords_zero]
  | cons d ds ih =>
    have hrun : axisFlows h (d :: ds) = List.replicate (h d).natAbs (d, decide (0 ≤ h d)) ++ axisFlows h ds := by
      simp [axisFlows, List.flatMap_cons]
    rw [hrun, pathDisplacement_append, ih, pathDisplacement_replicate, natAbs_mul_stepSign, ← _root_.YangMills.Construction.ColdStepAtMirrorFrames.AxialResponseDecay.siteOfCoords_add]
    simp
theorem pathDisplacement_axisPath (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement F F.depth (axisPath h π) = siteOfCoords F.depth h := by
  rw [axisPath_eq_axisFlows, pathDisplacement_axisFlows]
  congr 1
  rw [List.map_map]
  have h1 := (Fin.sum_univ_def (fun k => (Pi.single (π k) (h (π k)) : Fin 4 → ℤ)))
  have h2 : ((List.finRange 4).map ((fun d => (Pi.single d (h d) : Fin 4 → ℤ)) ∘ π)).sum =
      ∑ k, (Pi.single (π k) (h (π k)) : Fin 4 → ℤ) := by
    rw [h1]
    rfl
  rw [h2, Equiv.sum_comp π (fun d => (Pi.single d (h d) : Fin 4 → ℤ))]
  exact Finset.univ_sum_single h
theorem pathSum_axisPath_le {W : LevelForm F F.depth} {q : Fin 4 → ℤ} {Bd : ℝ} (hL : Odd F.blockSide) (hb0 : 0 ≤ Bd)
    (hbd : ∀ o, InBlock F o → ∀ i, o i ≠ halfSide F → |W (blockSite q o) i| ≤ Bd) {h : Fin 4 → ℤ}
    (hh : InBlock F h) (π : Equiv.Perm (Fin 4)) :
    |pathSum W (blockSite q 0) (axisPath h π)| ≤ 4 * ((halfSide F : ℝ) * Bd) := by
  have h0 : InBlock F (0 : Fin 4 → ℤ) := by
    intro k
    have := halfSide_nonneg hL
    simp
    omega
  have := pathSum_axisFlows_le hL hb0 hbd hh ((List.finRange 4).map π) 0
    ((List.nodup_finRange 4).map π.injective) h0 (by simp)
  rw [axisPath_eq_axisFlows]
  simpa using this
theorem plaquetteCurl_swap {j : ℕ} (W : LevelForm F j) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteCurl W x μ ν = - plaquetteCurl W x ν μ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.plaquetteCurl_swap <;> assumption
theorem plaquette_relation (W : LevelForm F F.depth) (x : F.Site F.depth) (μ ν : Fin 4) :
    W (x + unitStep F.depth ν) μ - W x μ =
      W (x + unitStep F.depth μ) ν - W x ν - plaquetteCurl W x μ ν := by
  unfold plaquetteCurl
  ring
def BlockCurlBound (W : LevelForm F F.depth) (q : Fin 4 → ℤ) (M : ℝ) : Prop :=
  ∀ o, InBlock F o → ∀ μ ν, μ < ν → |plaquetteCurl W (blockSite q o) μ ν| ≤ M
theorem BlockCurlBound.of_ne {W : LevelForm F F.depth} {q : Fin 4 → ℤ} {M : ℝ} (h : BlockCurlBound W q M)
    {o : Fin 4 → ℤ} (ho : InBlock F o) {μ ν : Fin 4} (hne : μ ≠ ν) :
    |plaquetteCurl W (blockSite q o) μ ν| ≤ M := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h o ho μ ν hlt
  · rw [plaquetteCurl_swap, abs_neg]
    exact h o ho ν μ hlt
theorem abs_sub_le_of_axial {W : LevelForm F F.depth} {q : Fin 4 → ℤ} {M : ℝ} (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (htree : ∀ b : F.Site F.depth × Fin 4, IsAxialTreeBond b → W b.1 b.2 = 0)
    (hB : BlockCurlBound W q M) {o : Fin 4 → ℤ} (ho : InBlock F o) {i l : Fin 4} (hil : i < l)
    (hoi : o i ≠ halfSide F) (hol : o l ≠ halfSide F) (habove : ∀ l', l < l' → o l' = 0) :
    |W (blockSite q (o + Pi.single l 1)) i - W (blockSite q o) i| ≤ M := by
  have hne : l ≠ i := hil.ne'
  have hc := ho i
  have hcube : InBlock F (o + Pi.single i 1) := InBlock.add_single ho i 1 (by omega) (by omega)
  have t1 : W (blockSite q o) l = 0 := htree (blockSite q o, l) (isAxialTreeBond_blockSite hL hs q o ho l hol habove)
  have t2 : W (blockSite q (o + Pi.single i 1)) l = 0 :=
    htree (blockSite q (o + Pi.single i 1), l) (isAxialTreeBond_blockSite hL hs q _ hcube l
      (by simpa [Pi.single_eq_of_ne hne] using hol)
      (by
        intro l' hl'
        have h' : l' ≠ i := (hil.trans hl').ne'
        simpa [Pi.single_eq_of_ne h'] using habove l' hl'))
  have key := plaquette_relation W (blockSite q o) i l
  rw [blockSite_add_unitStep, blockSite_add_unitStep, t1, t2] at key
  rw [key]
  simp only [sub_zero, zero_sub, abs_neg]
  exact hB o ho i l hil
def heightAbove (i : Fin 4) (o : Fin 4 → ℤ) : ℕ := ∑ l, if i < l then (o l).natAbs else 0
theorem heightAbove_lt {i l : Fin 4} {o o' : Fin 4 → ℤ} (hil : i < l)
    (hless : (o' l).natAbs < (o l).natAbs) (hsame : ∀ k, k ≠ l → o' k = o k) :
    heightAbove i o' < heightAbove i o := by
  unfold heightAbove
  apply Finset.sum_lt_sum
  · intro k _
    by_cases hk : k = l
    · subst hk
      split_ifs <;> omega
    · rw [hsame k hk]
  · exact ⟨l, Finset.mem_univ _, by simp [hil, hless]⟩
theorem abs_le_heightAbove_mul {W : LevelForm F F.depth} {q : Fin 4 → ℤ} {M : ℝ} (hM : 0 ≤ M) (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (htree : ∀ b : F.Site F.depth × Fin 4, IsAxialTreeBond b → W b.1 b.2 = 0)
    (hB : BlockCurlBound W q M) (i : Fin 4) :
    ∀ (n : ℕ) (o : Fin 4 → ℤ), heightAbove i o = n → InBlock F o → o i ≠ halfSide F →
      |W (blockSite q o) i| ≤ (n : ℝ) * M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro o hn ho hoi
    by_cases hall : ∀ l, i < l → o l = 0
    · have t : W (blockSite q o) i = 0 := htree (blockSite q o, i) (isAxialTreeBond_blockSite hL hs q o ho i hoi hall)
      rw [t, abs_zero]
      positivity
    · push_neg at hall
      obtain ⟨l0, h1, h2⟩ := hall
      obtain ⟨l, hlS, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun l => i < l ∧ o l ≠ 0) id
        ⟨l0, by simp [h1, h2]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hlS hmax
      obtain ⟨hil, hol⟩ := hlS
      have habove : ∀ l', l < l' → o l' = 0 := by
        intro l' hl'
        by_contra hne
        exact absurd (hmax l' ⟨hil.trans hl', hne⟩) (not_le.mpr hl')
      have hh := halfSide_nonneg (F := F) hL
      have hcl := ho l
      rcases lt_or_gt_of_ne hol with hneg | hpos
      · have hcube : InBlock F (o + Pi.single l 1) := InBlock.add_single ho l 1 (by omega) (by omega)
        have hst := abs_sub_le_of_axial hL hs htree hB ho hil hoi (by omega) habove
        have hlt : heightAbove i (o + Pi.single l 1) < n := hn ▸ heightAbove_lt hil
          (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
          (by
            intro k hk
            simp [Pi.single_eq_of_ne hk])
        have hoi' : (o + Pi.single l 1 : Fin 4 → ℤ) i ≠ halfSide F := by
          simpa [Pi.single_eq_of_ne hil.ne] using hoi
        have hi := ih _ hlt (o + Pi.single l 1) rfl hcube hoi'
        have hcast : ((heightAbove i (o + Pi.single l 1) : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hlt
        have habs := abs_sub_abs_le_abs_sub (W (blockSite q o) i) (W (blockSite q (o + Pi.single l 1)) i)
        rw [abs_sub_comm (W (blockSite q o) i)] at habs
        have := mul_le_mul_of_nonneg_right hcast hM
        linarith
      · have hcube : InBlock F (o + Pi.single l (-1)) :=
          InBlock.add_single ho l (-1) (by omega) (by omega)
        have hoi' : (o + Pi.single l (-1) : Fin 4 → ℤ) i ≠ halfSide F := by
          simpa [Pi.single_eq_of_ne hil.ne] using hoi
        have hst := abs_sub_le_of_axial hL hs htree hB hcube hil hoi'
          (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
          (by
            intro l' hl'
            have h' : l' ≠ l := hl'.ne'
            simpa [Pi.single_eq_of_ne h'] using habove l' hl')
        have hback : (o + Pi.single l (-1) + Pi.single l 1 : Fin 4 → ℤ) = o := by
          rw [add_assoc, ← Pi.single_add]
          simp
        rw [hback] at hst
        have hlt : heightAbove i (o + Pi.single l (-1)) < n := hn ▸ heightAbove_lt hil
          (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
          (by
            intro k hk
            simp [Pi.single_eq_of_ne hk])
        have hi := ih _ hlt (o + Pi.single l (-1)) rfl hcube hoi'
        have hcast : ((heightAbove i (o + Pi.single l (-1)) : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hlt
        have habs := abs_sub_abs_le_abs_sub (W (blockSite q o) i) (W (blockSite q (o + Pi.single l (-1))) i)
        have := mul_le_mul_of_nonneg_right hcast hM
        linarith
theorem heightAbove_le (hL : Odd F.blockSide) (i : Fin 4) {o : Fin 4 → ℤ} (ho : InBlock F o) :
    (heightAbove i o : ℝ) ≤ 4 * (halfSide F : ℝ) := by
  have hh := halfSide_nonneg (F := F) hL
  have h1 : (heightAbove i o : ℤ) ≤ 4 * halfSide F := by
    unfold heightAbove
    push_cast
    calc (∑ l : Fin 4, ((if i < l then |o l| else 0))) ≤ ∑ _l : Fin 4, halfSide F := by
          apply Finset.sum_le_sum
          intro l _
          have := ho l
          split_ifs
          · exact abs_le.mpr this
          · exact hh
      _ = 4 * halfSide F := by simp
  calc (heightAbove i o : ℝ) = ((heightAbove i o : ℤ) : ℝ) := (Int.cast_natCast _).symm
    _ ≤ ((4 * halfSide F : ℤ) : ℝ) := Int.cast_le.mpr h1
    _ = 4 * (halfSide F : ℝ) := by push_cast; ring
theorem abs_le_of_ne_halfSide {W : LevelForm F F.depth} {q : Fin 4 → ℤ} {M : ℝ} (hM : 0 ≤ M) (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (htree : ∀ b : F.Site F.depth × Fin 4, IsAxialTreeBond b → W b.1 b.2 = 0)
    (hB : BlockCurlBound W q M) {o : Fin 4 → ℤ} (ho : InBlock F o) {i : Fin 4} (hi : o i ≠ halfSide F) :
    |W (blockSite q o) i| ≤ 4 * (halfSide F : ℝ) * M :=
  (abs_le_heightAbove_mul hM hL hs htree hB i _ o rfl ho hi).trans
    (mul_le_mul_of_nonneg_right (heightAbove_le hL i ho) hM)
theorem abs_pathSum_bondContour_sub_le {W : LevelForm F F.depth} {q : Fin 4 → ℤ} {Bd : ℝ} (hL : Odd F.blockSide)
    (hb0 : 0 ≤ Bd) {i : Fin 4}
    (hbd : ∀ o, InBlock F o → ∀ k, o k ≠ halfSide F → |W (blockSite q o) k| ≤ Bd)
    (hbd' : ∀ o, InBlock F o → ∀ k, o k ≠ halfSide F → |W (blockSite (q + Pi.single i 1) o) k| ≤ Bd)
    {h : Fin 4 → ℤ} (hh : InBlock F h) (π : Equiv.Perm (Fin 4)) :
    |pathSum W (blockSite q 0) (bondContour F.blockSide h π i) -
      W (blockSite q (h + Pi.single i (halfSide F - h i))) i| ≤ 10 * ((halfSide F : ℝ) * Bd) := by
  have h2 := blockSide_eq_two_mul_halfSide (F := F) hL
  have hci := hh i
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, (n : ℤ) = halfSide F - h i :=
    ⟨(halfSide F - h i).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n : ℕ, (n : ℤ) = halfSide F + h i :=
    ⟨(halfSide F + h i).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hsplit : F.blockSide = n₁ + (n₂ + 1) := by omega
  have hrep : List.replicate F.blockSide ((i, true) : PathStep) =
      List.replicate n₁ (i, true) ++ (i, true) :: List.replicate n₂ (i, true) := by
    conv_lhs => rw [hsplit]
    rw [List.replicate_add, List.replicate_succ]
  set A := axisPath h π with hA
  have hAend : pathDisplacement F F.depth A = siteOfCoords F.depth h := pathDisplacement_axisPath h π
  set hm : Fin 4 → ℤ := h + Pi.single i (halfSide F - h i) with hhm
  have hmcube : InBlock F hm := InBlock.add_single hh i _ (by omega) (by omega)
  have hmi : hm i = halfSide F := by simp [hhm]
  have e0 : (blockSite q 0 : F.Site F.depth) + pathDisplacement F F.depth A = blockSite q h := by
    rw [hAend, blockSite_add, zero_add]
  have e1 : (blockSite q h : F.Site F.depth) + pathDisplacement F F.depth (List.replicate n₁ (i, true)) =
      blockSite q hm := by
    rw [pathDisplacement_replicate, blockSite_add, stepSign_true, mul_one, hn₁]
  set o₂ : Fin 4 → ℤ := hm + Pi.single i 1 - Pi.single i (F.blockSide : ℤ) with ho₂
  have e2 : (blockSite q hm : F.Site F.depth) + stepDisplacement F.depth (i, true) =
      blockSite (q + Pi.single i 1) o₂ := by
    rw [stepDisplacement_eq, stepSign_true, blockSite_add, blockSite_shift q _ i]
  have ho₂i : o₂ i = - halfSide F := by
    simp only [ho₂, Pi.sub_apply, Pi.add_apply, Pi.single_eq_same, hmi]
    omega
  have ho₂cube : InBlock F o₂ := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [ho₂i]
      have := halfSide_nonneg (F := F) hL
      omega
    · have : o₂ k = hm k := by simp [ho₂, Pi.single_eq_of_ne hk]
      rw [this]
      exact hmcube k
  have e3 : (blockSite q 0 : F.Site F.depth) + pathDisplacement F F.depth (A ++ List.replicate F.blockSide (i, true)) =
      blockSite (q + Pi.single i 1) 0 + pathDisplacement F F.depth A := by
    rw [pathDisplacement_append, hAend, pathDisplacement_replicate, ← add_assoc, blockSite_add q 0,
      blockSite_add q (0 + h), blockSite_add (q + Pi.single i 1) 0, zero_add, stepSign_true, mul_one,
      blockSite_shift q _ i]
    congr 1
    simp
  have b1 := pathSum_axisPath_le hL hb0 hbd hh π
  have b2 := pathSum_axisPath_le hL hb0 hbd' hh π
  have b3 := pathSum_replicate_le hb0 hbd i true n₁ h hh (by rw [stepSign_true, hn₁]; omega)
    (by rw [stepSign_true, hn₁]; omega)
  have b4 := pathSum_replicate_le hb0 hbd' i true n₂ o₂ ho₂cube (by rw [stepSign_true, hn₂, ho₂i]; omega)
    (by rw [stepSign_true, hn₂, ho₂i]; omega)
  have hsum : (n₁ : ℝ) + n₂ = 2 * (halfSide F : ℝ) := by
    have : (n₁ : ℤ) + n₂ = 2 * halfSide F := by omega
    exact_mod_cast this
  have hform : pathSum W (blockSite q 0) (bondContour F.blockSide h π i) =
      pathSum W (blockSite q 0) A +
        (pathSum W (blockSite q h) (List.replicate n₁ (i, true)) +
          (W (blockSite q hm) i + pathSum W (blockSite (q + Pi.single i 1) o₂) (List.replicate n₂ (i, true)))) -
        pathSum W (blockSite (q + Pi.single i 1) 0) A := by
    unfold bondContour
    rw [← hA, pathSum_append, pathSum_append, e3, pathSum_reversePath, e0, hrep, pathSum_append, e1]
    simp only [pathSum, if_true, e2]
    ring
  rw [hform]
  have c1 := abs_le.mp b1
  have c2 := abs_le.mp b2
  have c3 := abs_le.mp b3
  have c4 := abs_le.mp b4
  have hprod : (n₁ : ℝ) * Bd + n₂ * Bd = 2 * ((halfSide F : ℝ) * Bd) := by
    rw [← add_mul, hsum]
    ring
  rw [abs_le]
  constructor <;> linarith [c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, c4.1, c4.2]
theorem abs_boundary_step_le {W : LevelForm F F.depth} {q : Fin 4 → ℤ} {M Bd : ℝ} (hL : Odd F.blockSide)
    (hB : BlockCurlBound W q M) {i k : Fin 4}
    (hbd : ∀ o, InBlock F o → ∀ k, o k ≠ halfSide F → |W (blockSite q o) k| ≤ Bd)
    (hbd' : ∀ o, InBlock F o → ∀ k, o k ≠ halfSide F → |W (blockSite (q + Pi.single i 1) o) k| ≤ Bd)
    {o : Fin 4 → ℤ} (ho : InBlock F o) (hik : i ≠ k) (hoi : o i = halfSide F) (hok : o k ≠ halfSide F) :
    |W (blockSite q (o + Pi.single k 1)) i - W (blockSite q o) i| ≤ M + 2 * Bd := by
  have h2 := blockSide_eq_two_mul_halfSide (F := F) hL
  set o₂ : Fin 4 → ℤ := o + Pi.single i 1 - Pi.single i (F.blockSide : ℤ) with ho₂
  have ho₂i : o₂ i = - halfSide F := by
    simp only [ho₂, Pi.sub_apply, Pi.add_apply, Pi.single_eq_same, hoi]
    omega
  have ho₂c : ∀ c, c ≠ i → o₂ c = o c := by
    intro c hc
    simp [ho₂, Pi.single_eq_of_ne hc]
  have ho₂cube : InBlock F o₂ := by
    intro c
    by_cases hc : c = i
    · subst hc
      rw [ho₂i]
      omega
    · rw [ho₂c c hc]
      exact ho c
  have key := plaquette_relation W (blockSite q o) i k
  have e2 : (blockSite q o : F.Site F.depth) + unitStep F.depth i = blockSite (q + Pi.single i 1) o₂ := by
    rw [blockSite_add_unitStep, blockSite_shift q _ i]
  rw [e2, blockSite_add_unitStep] at key
  rw [key]
  have b1 := hbd' o₂ ho₂cube k (by rw [ho₂c k hik.symm]; exact hok)
  have b2 := hbd o ho k hok
  have b3 := BlockCurlBound.of_ne hB ho hik
  have c1 := abs_le.mp b1
  have c2 := abs_le.mp b2
  have c3 := abs_le.mp b3
  rw [abs_le]
  constructor <;> linarith [c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]
def offsetDist (o o' : Fin 4 → ℤ) : ℕ := ∑ k, (o k - o' k).natAbs
theorem offsetDist_lt {k : Fin 4} {o o₁ o' : Fin 4 → ℤ} (hless : (o₁ k - o' k).natAbs < (o k - o' k).natAbs)
    (hsame : ∀ c, c ≠ k → o₁ c = o c) : offsetDist o₁ o' < offsetDist o o' := by
  unfold offsetDist
  apply Finset.sum_lt_sum
  · intro c _
    by_cases hc : c = k
    · subst hc
      omega
    · rw [hsame c hc]
  · exact ⟨k, Finset.mem_univ _, hless⟩
theorem abs_boundary_sub_le {W : LevelForm F F.depth} {q : Fin 4 → ℤ} {M Bd : ℝ} (hL : Odd F.blockSide)
    (hS : 0 ≤ M + 2 * Bd) (hB : BlockCurlBound W q M) {i : Fin 4}
    (hbd : ∀ o, InBlock F o → ∀ k, o k ≠ halfSide F → |W (blockSite q o) k| ≤ Bd)
    (hbd' : ∀ o, InBlock F o → ∀ k, o k ≠ halfSide F → |W (blockSite (q + Pi.single i 1) o) k| ≤ Bd)
    {o' : Fin 4 → ℤ} (ho' : InBlock F o') (ho'i : o' i = halfSide F) :
    ∀ (n : ℕ) (o : Fin 4 → ℤ), offsetDist o o' = n → InBlock F o → o i = halfSide F →
      |W (blockSite q o) i - W (blockSite q o') i| ≤ (n : ℝ) * (M + 2 * Bd) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro o hn ho hoi
    by_cases heq : o = o'
    · subst heq
      simp only [sub_self, abs_zero]
      positivity
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp heq
      have hik : i ≠ k := by
        intro e
        subst e
        exact hk (hoi.trans ho'i.symm)
      have hck := ho k
      have hck' := ho' k
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · have hcube : InBlock F (o + Pi.single k 1) := InBlock.add_single ho k 1 (by omega) (by omega)
        have hst := abs_boundary_step_le hL hB hbd hbd' ho hik hoi (by omega)
        have hlt' : offsetDist (o + Pi.single k 1) o' < n := hn ▸ offsetDist_lt (k := k)
          (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
          (by
            intro c hc
            simp [Pi.single_eq_of_ne hc])
        have hi := ih _ hlt' (o + Pi.single k 1) rfl hcube (by simp [Pi.single_eq_of_ne hik, hoi])
        have hcast : ((offsetDist (o + Pi.single k 1) o' : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hlt'
        have hmul := mul_le_mul_of_nonneg_right hcast hS
        have c1 := abs_le.mp hst
        have c2 := abs_le.mp hi
        rw [abs_le]
        constructor <;> linarith [c1.1, c1.2, c2.1, c2.2]
      · have hcube : InBlock F (o + Pi.single k (-1)) :=
          InBlock.add_single ho k (-1) (by omega) (by omega)
        have hoi₁ : (o + Pi.single k (-1) : Fin 4 → ℤ) i = halfSide F := by
          simp [Pi.single_eq_of_ne hik, hoi]
        have hst := abs_boundary_step_le hL hB hbd hbd' hcube hik hoi₁
          (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
        have hback : (o + Pi.single k (-1) + Pi.single k 1 : Fin 4 → ℤ) = o := by
          rw [add_assoc, ← Pi.single_add]
          simp
        rw [hback] at hst
        have hlt' : offsetDist (o + Pi.single k (-1)) o' < n := hn ▸ offsetDist_lt (k := k)
          (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
          (by
            intro c hc
            simp [Pi.single_eq_of_ne hc])
        have hi := ih _ hlt' (o + Pi.single k (-1)) rfl hcube hoi₁
        have hcast : ((offsetDist (o + Pi.single k (-1)) o' : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hlt'
        have hmul := mul_le_mul_of_nonneg_right hcast hS
        have c1 := abs_le.mp hst
        have c2 := abs_le.mp hi
        rw [abs_le]
        constructor <;> linarith [c1.1, c1.2, c2.1, c2.2]
theorem offsetDist_le (hL : Odd F.blockSide) {o o' : Fin 4 → ℤ} (ho : InBlock F o) (ho' : InBlock F o') :
    (offsetDist o o' : ℝ) ≤ 8 * (halfSide F : ℝ) := by
  have h1 : (offsetDist o o' : ℤ) ≤ 8 * halfSide F := by
    unfold offsetDist
    push_cast
    calc (∑ k : Fin 4, |o k - o' k|) ≤ ∑ _k : Fin 4, 2 * halfSide F := by
          apply Finset.sum_le_sum
          intro k _
          have := ho k
          have := ho' k
          rw [abs_le]
          constructor <;> omega
      _ = 8 * halfSide F := by
          simp
          ring
  calc (offsetDist o o' : ℝ) = ((offsetDist o o' : ℤ) : ℝ) := (Int.cast_natCast _).symm
    _ ≤ ((8 * halfSide F : ℤ) : ℝ) := Int.cast_le.mpr h1
    _ = 8 * (halfSide F : ℝ) := by push_cast; ring
theorem card_centredCube (hL : Odd F.blockSide) : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by apply _root_.YangMills.Construction.CompositeMean.card_centredCube_blockSide <;> assumption
theorem abs_sub_le_of_mean (hL : Odd F.blockSide) (V : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℝ) {D R w : ℝ}
    (hmean : (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), V h π = R)
    (hD : ∀ h ∈ centredCube F.blockSide, ∀ π, |w - V h π| ≤ D) : |w - R| ≤ D := by
  have hLpos : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have hc : (Fintype.card (Equiv.Perm (Fin 4)) : ℝ) = 24 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hS : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (w - V h π) =
      24 * (F.blockSide : ℝ) ^ 4 * w - ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), V h π := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc,
      card_centredCube hL]
    ring
  have hw : w - R = (1 / (24 * (F.blockSide : ℝ) ^ 4)) *
      ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (w - V h π) := by
    rw [hS, ← hmean]
    field_simp
  have hb : |∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (w - V h π)| ≤
      24 * (F.blockSide : ℝ) ^ 4 * D := by
    calc |∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (w - V h π)|
        ≤ ∑ h ∈ centredCube F.blockSide, |∑ π : Equiv.Perm (Fin 4), (w - V h π)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), |w - V h π| :=
          Finset.sum_le_sum fun h _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), D :=
          Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun π _ => hD h hh π
      _ = 24 * (F.blockSide : ℝ) ^ 4 * D := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, card_centredCube hL]
          ring
  rw [hw, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (24 * (F.blockSide : ℝ) ^ 4))]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        |∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (w - V h π)|
      ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) * (24 * (F.blockSide : ℝ) ^ 4 * D) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = D := by field_simp
theorem abs_boundary_sub_mean_le {W : LevelForm F F.depth} {M Bd R : ℝ} (hL : Odd F.blockSide) (hb0 : 0 ≤ Bd)
    (hS : 0 ≤ M + 2 * Bd) {y : F.Cell} {i : Fin 4} (hB : BlockCurlBound W (siteCoords y) M)
    (hbd : ∀ o, InBlock F o → ∀ k, o k ≠ halfSide F → |W (blockSite (siteCoords y) o) k| ≤ Bd)
    (hbd' : ∀ o, InBlock F o → ∀ k, o k ≠ halfSide F →
      |W (blockSite (siteCoords y + Pi.single i 1) o) k| ≤ Bd)
    (hmean : (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      pathSum W (_root_.YangMills.Construction.BlockAverages.refineSite y) (bondContour F.blockSide h π i) = R)
    {o : Fin 4 → ℤ} (ho : InBlock F o) (hoi : o i = halfSide F) :
    |W (blockSite (siteCoords y) o) i - R| ≤
      8 * (halfSide F : ℝ) * (M + 2 * Bd) + 10 * ((halfSide F : ℝ) * Bd) := by
  apply abs_sub_le_of_mean hL (fun h π => pathSum W (_root_.YangMills.Construction.BlockAverages.refineSite y) (bondContour F.blockSide h π i)) hmean
  intro h hh π
  have hcube := (mem_centredCube_iff h).mp hh
  have hci := hcube i
  have hmcube : InBlock F (h + Pi.single i (halfSide F - h i)) :=
    InBlock.add_single hcube i _ (by omega) (by omega)
  have b1 := abs_pathSum_bondContour_sub_le hL hb0 hbd hbd' hcube π
  rw [← refineSite_eq] at b1
  have b2 := abs_boundary_sub_le hL hS hB hbd hbd' hmcube (by simp) _ o rfl ho hoi
  have b3 : (offsetDist o (h + Pi.single i (halfSide F - h i)) : ℝ) * (M + 2 * Bd) ≤
      8 * (halfSide F : ℝ) * (M + 2 * Bd) :=
    mul_le_mul_of_nonneg_right (offsetDist_le hL ho hmcube) hS
  have c1 := abs_le.mp b1
  have c2 := abs_le.mp b2
  rw [abs_le]
  constructor <;> linarith [c1.1, c1.2, c2.1, c2.2]
theorem mem_finiteCells (hs : ∀ i, 0 < F.extent i) (y : F.Cell) : y ∈ finiteCells F := by apply _root_.YangMills.Construction.FrameTorusAction.mem_finiteCells <;> assumption
theorem mem_sitesOfCells_depth (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (x : F.Site F.depth) :
    x ∈ sitesOfCells (finiteCells F) F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.blocksCoverLowerLevel <;> assumption
theorem mem_sitesOfCells_top (hs : ∀ i, 0 < F.extent i) (y : F.Cell) : y ∈ sitesOfCells (finiteCells F) F.top := by
  unfold sitesOfCells
  rw [Finset.mem_biUnion]
  refine ⟨y, _root_.YangMills.Construction.ColdStepAtMirrorFrames.AxialResponseDecay.mem_finiteCells hs _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨0, by simp [centredCube]; rfl, ?_⟩
  rw [siteOfCoords_zero, add_zero]
  simp only [cellCentre, Nat.sub_self, pow_zero, Nat.cast_one, one_mul, Int.cast_one]
  have : (fun i => (1 : ℤ) * siteCoords y i) = siteCoords y := by
    funext i
    simp
  exact siteOfCoords_siteCoords y
theorem enclosingCell_cell (y : F.Cell) : enclosingCell y = y := by apply _root_.YangMills.Construction.PotentialMeans.enclosingCell_self <;> assumption
theorem cellSupDist_self (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_shift_le (hs : ∀ i, 3 ≤ F.extent i) (q : Fin 4 → ℤ) (i : Fin 4) :
    cellSupDist (siteOfCoords F.top (q + Pi.single i 1) : F.Cell) (siteOfCoords F.top q) ≤ 1 := by
  unfold cellSupDist
  apply Finset.sup_le
  intro k _
  have hd : (siteOfCoords F.top (q + Pi.single i 1) : F.Cell) k - (siteOfCoords F.top q : F.Cell) k =
      (((Pi.single i 1 : Fin 4 → ℤ) k : ℤ) : ZMod (F.period F.top k)) := by
    simp [siteOfCoords]
  rw [hd]
  have hN : 3 ≤ F.period F.top k := by
    rw [period_top]
    exact hs k
  have : NeZero (F.period F.top k) := ⟨by omega⟩
  by_cases hk : k = i
  · subst hk
    have hv : (((Pi.single k 1 : Fin 4 → ℤ) k : ℤ) : ZMod (F.period F.top k)).valMinAbs = 1 := by
      rw [ZMod.valMinAbs_spec]
      refine ⟨by simp, ?_, ?_⟩
      · have : (3 : ℤ) ≤ F.period F.top k := by exact_mod_cast hN
        omega
      · have : (3 : ℤ) ≤ F.period F.top k := by exact_mod_cast hN
        omega
    rw [hv]
    simp
  · simp [Pi.single_eq_of_ne hk]
open Classical in
theorem chainMisfit_sq_le {a : ℝ} (ha : 1 ≤ a) (hs : ∀ i, 0 < F.extent i) (B : FormChain F) {X : Set F.Cell}
    {y : F.Cell} (hy : y ∈ X) (i : Fin 4) : chainMisfit B F.depth y i ^ 2 ≤ chainEnergyOnCells a B X := by
  unfold chainEnergyOnCells
  have h0 : 0 ≤ ∑ x ∈ (sitesOfCells (finiteCells F) 0).filter (fun x => enclosingCell x ∈ X), ∑ e ∈ orientedPlanes,
      plaquetteCurl (B 0) x e.1 e.2 ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : chainMisfit B F.depth y i ^ 2 ≤ ∑ k : Fin 4, chainMisfit B F.depth y k ^ 2 :=
    Finset.single_le_sum (f := fun k => chainMisfit B F.depth y k ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : ∑ k : Fin 4, chainMisfit B F.depth y k ^ 2 ≤
      ∑ y' ∈ (sitesOfCells (finiteCells F) (F.depth + 1)).filter (fun y' => enclosingCell y' ∈ X), ∑ k : Fin 4,
        chainMisfit B F.depth y' k ^ 2 :=
    Finset.single_le_sum (f := fun y' : F.Site (F.depth + 1) => ∑ k : Fin 4, chainMisfit B F.depth y' k ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_filter.mpr ⟨mem_sitesOfCells_top hs y, by rw [enclosingCell_cell]; exact hy⟩)
  have h3 : ∑ y' ∈ (sitesOfCells (finiteCells F) (F.depth + 1)).filter (fun y' => enclosingCell y' ∈ X), ∑ k : Fin 4,
        chainMisfit B F.depth y' k ^ 2 ≤
      ∑ j ∈ Finset.range F.top, ∑ y' ∈ (sitesOfCells (finiteCells F) (j + 1)).filter (fun y' => enclosingCell y' ∈ X),
        ∑ k : Fin 4, chainMisfit B j y' k ^ 2 :=
    Finset.single_le_sum (f := fun j => ∑ y' ∈ (sitesOfCells (finiteCells F) (j + 1)).filter
        (fun y' => enclosingCell y' ∈ X), ∑ k : Fin 4, chainMisfit B j y' k ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_self _))
  nlinarith
theorem abs_response_le {c : F.Site F.top × Fin 4} {B : FormChain F} {W : LevelForm F F.depth} {M : ℝ} (hM : 0 ≤ M)
    (hL : Odd F.blockSide) (hs : ∀ i, 3 ≤ F.extent i) (hresp : IsAxialResponse c B W) {y : F.Cell}
    (hcurl : ∀ (p : F.Site F.depth) (e : Fin 4 × Fin 4), e ∈ orientedPlanes → cellSupDist (enclosingCell p) y ≤ 2 →
      |plaquetteCurl W p e.1 e.2| ≤ M)
    (x : F.Site F.depth) (hx : enclosingCell x = y) (i : Fin 4) :
    |W x i| ≤ 112 * (F.blockSide : ℝ) ^ 2 * M + |topBondIndicator c y i + chainMisfit B F.depth y i| := by
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have htree : ∀ b : F.Site F.depth × Fin 4, IsAxialTreeBond b → W b.1 b.2 = 0 := hresp.vanishes_on_tree
  have hB : BlockCurlBound W (siteCoords y) M := by
    intro o ho μ ν hμν
    apply hcurl _ (μ, ν) (by simp [orientedPlanes, hμν])
    rw [enclosingCell_blockSite hL _ o ho, siteOfCoords_siteCoords, cellSupDist_self]
    omega
  have hB' : BlockCurlBound W (siteCoords y + Pi.single i 1) M := by
    intro o ho μ ν hμν
    apply hcurl _ (μ, ν) (by simp [orientedPlanes, hμν])
    rw [enclosingCell_blockSite hL _ o ho]
    have h1 := cellSupDist_shift_le hs (siteCoords y) i
    rw [siteOfCoords_siteCoords] at h1
    omega
  have hh : (0 : ℝ) ≤ (halfSide F : ℝ) := by exact_mod_cast halfSide_nonneg (F := F) hL
  set Bd : ℝ := 4 * (halfSide F : ℝ) * M with hBd
  have hb0 : 0 ≤ Bd := by positivity
  have hbd : ∀ o, InBlock F o → ∀ k, o k ≠ halfSide F → |W (blockSite (siteCoords y) o) k| ≤ Bd :=
    fun o ho k hk => abs_le_of_ne_halfSide hM hL hs0 htree hB ho hk
  have hbd' : ∀ o, InBlock F o → ∀ k, o k ≠ halfSide F →
      |W (blockSite (siteCoords y + Pi.single i 1) o) k| ≤ Bd :=
    fun o ho k hk => abs_le_of_ne_halfSide hM hL hs0 htree hB' ho hk
  obtain ⟨o, ho, hxo⟩ := exists_blockSite hL x
  rw [hx] at hxo
  rw [hxo]
  have hLr : (F.blockSide : ℝ) = 2 * (halfSide F : ℝ) + 1 := by
    exact_mod_cast blockSide_eq_two_mul_halfSide (F := F) hL
  have hhL : (halfSide F : ℝ) ≤ (F.blockSide : ℝ) ^ 2 := by nlinarith
  have hhL2 : (halfSide F : ℝ) ^ 2 ≤ (F.blockSide : ℝ) ^ 2 := by nlinarith
  have hR := abs_nonneg (topBondIndicator c y i + chainMisfit B F.depth y i)
  by_cases hoi : o i = halfSide F
  · have hc := abs_boundary_sub_mean_le (R := topBondIndicator c y i + chainMisfit B F.depth y i) hL hb0
      (by positivity) hB hbd hbd' (hresp.contour_mean y i) ho hoi
    have hD : 8 * (halfSide F : ℝ) * (M + 2 * Bd) + 10 * ((halfSide F : ℝ) * Bd) ≤
        112 * (F.blockSide : ℝ) ^ 2 * M := by
      have e : 8 * (halfSide F : ℝ) * (M + 2 * Bd) + 10 * ((halfSide F : ℝ) * Bd) =
          (8 * (halfSide F : ℝ) + 104 * (halfSide F : ℝ) ^ 2) * M := by
        rw [hBd]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (by linarith) hM
    have habs := abs_sub_abs_le_abs_sub (W (blockSite (siteCoords y) o) i)
      (topBondIndicator c y i + chainMisfit B F.depth y i)
    linarith
  · have hc := hbd o ho i hoi
    have hD : Bd ≤ 112 * (F.blockSide : ℝ) ^ 2 * M := by
      rw [hBd]
      exact mul_le_mul_of_nonneg_right (by linarith) hM
    linarith
end AxialResponseDecay
open AxialResponseDecay in
theorem axialResponseDecay_holds (h₁ : flatChainEnergyNearCell)
    (h₂ : CurlSquareSumBound) : axialResponseDecay := by
  intro a ha
  obtain ⟨del, C, hdel, hdel1, hC, L₁, hE⟩ := h₁ a ha
  obtain ⟨Cs, hCs, L₂, hS⟩ := h₂ a ha
  refine ⟨del, 112 * Real.sqrt (Cs * C) + 1 + Real.sqrt C, hdel, hdel1, by positivity, max L₁ L₂, ?_⟩
  intro F c B W hL hL0 hcub hflat hresp b _
  obtain ⟨n, hn, hside⟩ := hcub
  have hcub : IsLargeCubicTorus F := ⟨n, hn, hside⟩
  have hs : ∀ i, 3 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  set y : F.Cell := enclosingCell b.1 with hy
  set d : ℝ := (cellSupDist y c.1 : ℝ) with hd
  set u : ℝ := Real.exp (-(del * d)) with hu
  have hu0 : 0 < u := Real.exp_pos _
  set E : ℝ := chainEnergyOnCells a B (cellBall y 24) with hEdef
  have hEle : E ≤ C * u ^ 2 := by
    have h := hE F c B hL (le_trans (le_max_left _ _) hL0) hcub hflat y 24 le_rfl
    have e : Real.exp (-(2 * del * (cellSupDist y c.1 : ℝ))) = u ^ 2 := by
      rw [hu, sq, ← Real.exp_add]
      congr 1
      rw [hd]
      ring
    rwa [e] at h
  have hSq := hS F c B hL (le_trans (le_max_right _ _) hL0) hcub hflat y
  have hmem : y ∈ cellBall y 24 := by
    show cellSupDist y y ≤ 24
    rw [cellSupDist_self]
    omega
  have hmis := chainMisfit_sq_le ha hs0 B hmem b.2
  have hE0 : 0 ≤ E := le_trans (sq_nonneg _) hmis
  have hcurl : ∀ (p : F.Site F.depth) (e : Fin 4 × Fin 4), e ∈ orientedPlanes →
      cellSupDist (enclosingCell p) y ≤ 2 → |plaquetteCurl W p e.1 e.2| ≤ Real.sqrt (Cs * E) := by
    intro p e he hp
    rw [hresp.curl_eq p e he]
    apply Real.abs_le_sqrt
    refine le_trans ?_ hSq
    have t1 : plaquetteCurl (B F.depth) p e.1 e.2 ^ 2 ≤
        ∑ e' ∈ orientedPlanes, plaquetteCurl (B F.depth) p e'.1 e'.2 ^ 2 :=
      Finset.single_le_sum (f := fun e' : Fin 4 × Fin 4 => plaquetteCurl (B F.depth) p e'.1 e'.2 ^ 2)
        (fun _ _ => sq_nonneg _) he
    refine le_trans t1 ?_
    exact Finset.single_le_sum
      (f := fun p' : F.Site F.depth => ∑ e' ∈ orientedPlanes, plaquetteCurl (B F.depth) p' e'.1 e'.2 ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_filter.mpr ⟨mem_sitesOfCells_depth hL hs0 p, hp⟩)
  have hmain := abs_response_le (Real.sqrt_nonneg _) hL hs hresp hcurl b.1 hy.symm b.2
  have hs1 : Real.sqrt (Cs * E) ≤ Real.sqrt (Cs * C) * u := by
    have e : Real.sqrt (Cs * C) * u = Real.sqrt (Cs * C * u ^ 2) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Cs * C) (u ^ 2), Real.sqrt_sq hu0.le]
    rw [e]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hEle hCs.le
    linarith
  have hs2 : |chainMisfit B F.depth y b.2| ≤ Real.sqrt C * u := by
    have e : Real.sqrt C * u = Real.sqrt (C * u ^ 2) := by
      rw [Real.sqrt_mul hC.le (u ^ 2), Real.sqrt_sq hu0.le]
    rw [e]
    exact Real.abs_le_sqrt (hmis.trans hEle)
  have hs3 : |topBondIndicator c y b.2| ≤ u := by
    unfold topBondIndicator
    split_ifs with hc
    · have hyc : y = c.1 := by rw [← hc]
      have hd0 : d = 0 := by
        rw [hd, ← hyc, cellSupDist_self]
        simp
      rw [hu, hd0]
      simp
    · simpa using hu0.le
  have htri := abs_add_le (topBondIndicator c y b.2) (chainMisfit B F.depth y b.2)
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL.pos
  have hLsq : (F.blockSide : ℝ) ^ 2 ≤ (F.blockSide : ℝ) ^ 3 := by nlinarith [sq_nonneg (F.blockSide : ℝ)]
  have hL3 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 3 := one_le_pow₀ hL1
  have hr := Real.sqrt_nonneg (Cs * C)
  have hr' := Real.sqrt_nonneg C
  have hfin : 112 * (F.blockSide : ℝ) ^ 2 * (Real.sqrt (Cs * C) * u) + (u + Real.sqrt C * u) ≤
      (112 * Real.sqrt (Cs * C) + 1 + Real.sqrt C) * (F.blockSide : ℝ) ^ 3 * u := by
    have e : (112 * Real.sqrt (Cs * C) + 1 + Real.sqrt C) * (F.blockSide : ℝ) ^ 3 * u =
        (112 * Real.sqrt (Cs * C) * (F.blockSide : ℝ) ^ 3 + (1 + Real.sqrt C) * (F.blockSide : ℝ) ^ 3) * u := by
      ring
    have e' : 112 * (F.blockSide : ℝ) ^ 2 * (Real.sqrt (Cs * C) * u) + (u + Real.sqrt C * u) =
        (112 * Real.sqrt (Cs * C) * (F.blockSide : ℝ) ^ 2 + (1 + Real.sqrt C)) * u := by ring
    rw [e, e']
    apply mul_le_mul_of_nonneg_right _ hu0.le
    have t1 := mul_le_mul_of_nonneg_left hLsq (by positivity : (0 : ℝ) ≤ 112 * Real.sqrt (Cs * C))
    have t2 := mul_le_mul_of_nonneg_left hL3 (by positivity : (0 : ℝ) ≤ 1 + Real.sqrt C)
    linarith
  have hp : 112 * (F.blockSide : ℝ) ^ 2 * Real.sqrt (Cs * E) ≤
      112 * (F.blockSide : ℝ) ^ 2 * (Real.sqrt (Cs * C) * u) :=
    mul_le_mul_of_nonneg_left hs1 (by positivity)
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
