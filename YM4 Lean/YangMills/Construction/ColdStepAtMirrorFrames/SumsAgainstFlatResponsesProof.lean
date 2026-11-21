import YangMills.Construction.ColdStepAtMirrorFrames.ShiftOfTheCurlOfAFlatChainProof
import YangMills.Construction.HoleBesideASecondHole.ComponentsOfLumpsProof
import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumpsProof
import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.ColdChainAtEveryLevel.PointsOfAPatchForm
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyAtTheLeastChartProof
import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbersProof
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyOfAFlatChainNearACell
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOverContoursOfAFormForm
import YangMills.Construction.ColdStepAtMirrorFrames.SizeOfAFlatResponse
import YangMills.Construction.ColdStepAtMirrorFrames.SizeOfTheCurlOfAFlatChainProof
import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponses
import YangMills.Construction.HoleBesideASecondHole.CutActionIsTheLeastActionProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums
variable {F : BlockFrame}
def stepStart (m : ℤ) (s : ℕ) : ℤ := if 0 ≤ m then (s : ℤ) else -((s : ℤ) + 1)
def stepSign (m : ℤ) : ℝ := if 0 ≤ m then 1 else -1
theorem stepStart_of_nonneg {m : ℤ} (h : 0 ≤ m) (s : ℕ) : stepStart m s = s := if_pos h
theorem stepStart_of_neg {m : ℤ} (h : m < 0) (s : ℕ) : stepStart m s = -((s : ℤ) + 1) := if_neg (not_le.mpr h)
theorem stepSign_of_nonneg {m : ℤ} (h : 0 ≤ m) : stepSign m = 1 := if_pos h
theorem stepSign_of_neg {m : ℤ} (h : m < 0) : stepSign m = -1 := if_neg (not_le.mpr h)
def segmentSum (g : ℤ → ℝ) (m : ℤ) : ℝ :=
  ∑ s ∈ Finset.range m.natAbs, stepSign m * g (stepStart m s)
theorem segmentSum_zero (g : ℤ → ℝ) : segmentSum g 0 = 0 := by simp [segmentSum]
theorem segmentSum_succ (g : ℤ → ℝ) (m : ℤ) : segmentSum g (m + 1) = segmentSum g m + g m := by
  rcases le_or_gt 0 m with h | h
  · have h1 : (m + 1).natAbs = m.natAbs + 1 := by omega
    have h2 : (0 : ℤ) ≤ m + 1 := by omega
    unfold segmentSum
    rw [h1, Finset.sum_range_succ]
    have e1 : ∀ s, stepStart (m + 1) s = stepStart m s := fun s => by
      rw [stepStart_of_nonneg h, stepStart_of_nonneg h2]
    have e2 : stepSign (m + 1) = stepSign m := by rw [stepSign_of_nonneg h, stepSign_of_nonneg h2]
    have e3 : stepStart m m.natAbs = m := by
      rw [stepStart_of_nonneg h]; omega
    simp only [e1, e2, e3]
    rw [stepSign_of_nonneg h, one_mul]
  · have h1 : (m + 1).natAbs + 1 = m.natAbs := by omega
    unfold segmentSum
    rw [← h1, Finset.sum_range_succ]
    have e3 : stepStart m (m + 1).natAbs = m := by
      rw [stepStart_of_neg h]; omega
    rw [e3, stepSign_of_neg h]
    have : ∑ s ∈ Finset.range (m + 1).natAbs, stepSign (m + 1) * g (stepStart (m + 1) s) =
        ∑ s ∈ Finset.range (m + 1).natAbs, (-1 : ℝ) * g (stepStart m s) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : s < (m + 1).natAbs := Finset.mem_range.mp hs
      have h3 : m + 1 < 0 := by omega
      rw [stepSign_of_neg h3, stepStart_of_neg h3, stepStart_of_neg h]
    rw [this]
    ring
theorem segmentSum_telescope (f : ℤ → ℝ) (m : ℤ) : segmentSum (fun j => f (j + 1) - f j) m = f m - f 0 := by
  induction m using Int.induction_on with
  | zero => simp [segmentSum_zero]
  | succ i ih =>
    rw [segmentSum_succ, ih]; ring
  | pred i ih =>
    have := segmentSum_succ (fun j => f (j + 1) - f j) (-(i : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [ih] at this
    linarith
theorem segmentSum_const (c : ℝ) (m : ℤ) : segmentSum (fun _ => c) m = (m : ℝ) * c := by
  induction m using Int.induction_on with
  | zero => simp [segmentSum_zero]
  | succ i ih =>
    rw [segmentSum_succ, ih]; push_cast; ring
  | pred i ih =>
    have := segmentSum_succ (fun _ => c) (-(i : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [ih] at this
    push_cast at this ⊢
    linarith
theorem segmentSum_add (g h : ℤ → ℝ) (m : ℤ) :
    segmentSum (fun j => g j + h j) m = segmentSum g m + segmentSum h m := by
  simp [segmentSum, mul_add, Finset.sum_add_distrib]
theorem segmentSum_sub (g h : ℤ → ℝ) (m : ℤ) :
    segmentSum (fun j => g j - h j) m = segmentSum g m - segmentSum h m := by
  simp [segmentSum, mul_sub, Finset.sum_sub_distrib]
theorem abs_segmentSum_le (g : ℤ → ℝ) (m : ℤ) :
    |segmentSum g m| ≤ ∑ s ∈ Finset.range m.natAbs, |g (stepStart m s)| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro s _
  rw [abs_mul]
  have : |stepSign m| = 1 := by unfold stepSign; split_ifs <;> simp
  rw [this, one_mul]
def axisVec (k : Fin 4) (j : ℤ) : Fin 4 → ℤ := Pi.single k j
theorem axisVec_zero (k : Fin 4) : axisVec k 0 = 0 := by simp [axisVec]
theorem axisVec_add (k : Fin 4) (j j' : ℤ) : axisVec k j + axisVec k j' = axisVec k (j + j') := by
  funext l
  by_cases h : l = k
  · subst h; simp [axisVec]
  · simp [axisVec, Pi.single_apply, h]
def leadingCoords (o : Fin 4 → ℤ) (k : ℕ) : Fin 4 → ℤ := fun j => if j.val < k then o j else 0
theorem leadingCoords_succ (o : Fin 4 → ℤ) (k : Fin 4) :
    leadingCoords o (k.val + 1) = leadingCoords o k.val + axisVec k (o k) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.partialOffset_succ <;> assumption
theorem leadingCoords_four (o : Fin 4 → ℤ) : leadingCoords o 4 = o := by
  funext j
  simp [leadingCoords, j.isLt]
def latticePathSum (A : (Fin 4 → ℤ) → Fin 4 → ℝ) (o : Fin 4 → ℤ) : ℝ :=
  ∑ k : Fin 4, segmentSum (fun j => A (leadingCoords o k.val + axisVec k j) k) (o k)
def latticeCurl (A : (Fin 4 → ℤ) → Fin 4 → ℝ) (v : Fin 4 → ℤ) (μ ν : Fin 4) : ℝ :=
  A v μ + A (v + axisVec μ 1) ν - A (v + axisVec ν 1) μ - A v ν
theorem leadingCoords_shift_of_le (o : Fin 4 → ℤ) (i : Fin 4) (k : ℕ) (hk : k ≤ i.val) :
    leadingCoords (o + axisVec i 1) k = leadingCoords o k := by
  funext j
  by_cases h : j.val < k
  · have : j ≠ i := fun e => by subst e; omega
    simp [leadingCoords, axisVec, h, this]
  · simp [leadingCoords, h]
theorem leadingCoords_shift_of_gt (o : Fin 4 → ℤ) (i : Fin 4) (k : ℕ) (hk : i.val < k) :
    leadingCoords (o + axisVec i 1) k = leadingCoords o k + axisVec i 1 := by
  funext j
  by_cases h : j.val < k
  · simp [leadingCoords, h]
  · have : j ≠ i := fun e => by subst e; omega
    simp [leadingCoords, axisVec, h, this]
theorem shift_apply_ne (o : Fin 4 → ℤ) {i k : Fin 4} (h : k ≠ i) : (o + axisVec i 1) k = o k := by
  simp [axisVec, h]
theorem shift_apply_self (o : Fin 4 → ℤ) (i : Fin 4) : (o + axisVec i 1) i = o i + 1 := by
  simp [axisVec]
theorem segmentSum_latticeCurl (A : (Fin 4 → ℤ) → Fin 4 → ℝ) (o : Fin 4 → ℤ) (i k : Fin 4) (hik : i < k) :
    segmentSum (fun j => latticeCurl A (leadingCoords o k.val + axisVec k j) k i) (o k) =
      segmentSum (fun j => A (leadingCoords o k.val + axisVec k j) k) (o k) -
        segmentSum (fun j => A (leadingCoords (o + axisVec i 1) k.val + axisVec k j) k)
          ((o + axisVec i 1) k) +
        (A (leadingCoords o (k.val + 1)) i - A (leadingCoords o k.val) i) := by
  have hne : k ≠ i := ne_of_gt hik
  rw [shift_apply_ne o hne, leadingCoords_shift_of_gt o i k.val hik, leadingCoords_succ]
  have e2 : ∀ j : ℤ, leadingCoords o k.val + axisVec k j + axisVec k 1 =
      leadingCoords o k.val + axisVec k (j + 1) := by
    intro j
    rw [add_assoc, axisVec_add]
  have e3 : ∀ j : ℤ, leadingCoords o k.val + axisVec i 1 + axisVec k j =
      leadingCoords o k.val + axisVec k j + axisVec i 1 := by
    intro j; abel
  have key := segmentSum_telescope (fun j => A (leadingCoords o k.val + axisVec k j) i) (o k)
  simp only [axisVec_zero, add_zero] at key
  simp only [latticeCurl, e2, e3]
  rw [← key, ← segmentSum_sub, ← segmentSum_add]
  apply congrArg (fun g => segmentSum g (o k))
  funext j
  ring
theorem sum_four_axes (i : Fin 4) (d S : Fin 4 → ℝ) (a : ℕ → ℝ) (hlow : ∀ k, k < i → d k = 0)
    (hsame : d i = - a (i.val + 1)) (hhigh : ∀ k, i < k → S k = d k + (a (k.val + 1) - a k.val)) :
    a 4 + ∑ k, d k = ∑ k : Fin 4, if i < k then S k else 0 := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  fin_cases i
  · have s1 := hhigh 1 (by decide)
    have s2 := hhigh 2 (by decide)
    have s3 := hhigh 3 (by decide)
    simp at hsame s1 s2 s3 ⊢
    linarith
  · have s1 := hlow 0 (by decide)
    have s2 := hhigh 2 (by decide)
    have s3 := hhigh 3 (by decide)
    simp at hsame s1 s2 s3 ⊢
    linarith
  · have s1 := hlow 0 (by decide)
    have s2 := hlow 1 (by decide)
    have s3 := hhigh 3 (by decide)
    simp at hsame s1 s2 s3 ⊢
    linarith
  · have s1 := hlow 0 (by decide)
    have s2 := hlow 1 (by decide)
    have s3 := hlow 2 (by decide)
    simp at hsame s1 s2 s3 ⊢
    linarith
theorem bond_add_latticePathSum_sub (A : (Fin 4 → ℤ) → Fin 4 → ℝ) (o : Fin 4 → ℤ) (i : Fin 4) :
    A o i + latticePathSum A o - latticePathSum A (o + axisVec i 1) =
      ∑ k : Fin 4, if i < k then
        segmentSum (fun j => latticeCurl A (leadingCoords o k.val + axisVec k j) k i) (o k) else 0 := by
  have main := sum_four_axes i
    (fun k => segmentSum (fun j => A (leadingCoords o k.val + axisVec k j) k) (o k) -
      segmentSum (fun j => A (leadingCoords (o + axisVec i 1) k.val + axisVec k j) k) ((o + axisVec i 1) k))
    (fun k => segmentSum (fun j => latticeCurl A (leadingCoords o k.val + axisVec k j) k i) (o k))
    (fun k => A (leadingCoords o k) i)
    (by
      intro k hk
      have hne : k ≠ i := ne_of_lt hk
      rw [shift_apply_ne o hne, leadingCoords_shift_of_le o i k.val (le_of_lt hk)]
      ring)
    (by
      rw [shift_apply_self, leadingCoords_shift_of_le o i i.val le_rfl, segmentSum_succ, leadingCoords_succ]
      ring)
    (by
      intro k hk
      exact segmentSum_latticeCurl A o i k hk)
  rw [← main, leadingCoords_four]
  unfold latticePathSum
  rw [Finset.sum_sub_distrib]
  ring
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_zero (j : ℕ) : siteOfCoords (F := F) j 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem siteOfCoords_neg (j : ℕ) (a : Fin 4 → ℤ) : siteOfCoords (F := F) j (-a) = - siteOfCoords j a := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_map_neg <;> assumption
theorem unitStep_eq (j : ℕ) (i : Fin 4) : unitStep (F := F) j i = siteOfCoords j (axisVec i 1) := rfl
theorem pathSum_append {j : ℕ} (B : LevelForm F j) (x : F.Site j) (l₁ l₂ : List PathStep) :
    pathSum B x (l₁ ++ l₂) =
      pathSum B x l₁ + pathSum B (x + (l₁.map (stepDisplacement j)).sum) l₂ := by
  induction l₁ generalizing x with
  | nil => simp [pathSum]
  | cons st r ih =>
    simp only [List.cons_append, pathSum, List.map_cons, List.sum_cons]
    rw [ih]
    simp only [add_assoc]
theorem pathSum_replicate_forward {j : ℕ} (B : LevelForm F j) (x : F.Site j) (k : Fin 4) (n : ℕ) :
    pathSum B x (List.replicate n (k, true)) =
      ∑ s ∈ Finset.range n, B (x + siteOfCoords j (axisVec k s)) k := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.pathSum_replicate <;> assumption
theorem pathSum_replicate_backward {j : ℕ} (B : LevelForm F j) (x : F.Site j) (k : Fin 4) (n : ℕ) :
    pathSum B x (List.replicate n (k, false)) =
      - ∑ s ∈ Finset.range n, B (x + siteOfCoords j (axisVec k (-((s : ℤ) + 1)))) k := by
  induction n generalizing x with
  | zero => simp [pathSum]
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [pathSum, Bool.false_eq_true, if_false]
    rw [ih, Finset.sum_range_succ']
    have e1 : stepDisplacement j (k, false) = siteOfCoords (F := F) j (axisVec k (-1)) := by
      have : axisVec k (-1) = - axisVec k 1 := by
        funext l
        by_cases h : l = k
        · subst h; simp [axisVec]
        · simp [axisVec, h]
      simp [stepDisplacement, unitStep_eq, this, siteOfCoords_neg]
    have e0 : x - unitStep j k = x + siteOfCoords j (axisVec k (-(((0 : ℕ) : ℤ) + 1))) := by
      have : axisVec k (-(((0 : ℕ) : ℤ) + 1)) = - axisVec k 1 := by
        funext l
        by_cases h : l = k
        · subst h; simp [axisVec]
        · simp [axisVec, h]
      rw [this, siteOfCoords_neg, unitStep_eq, sub_eq_add_neg]
    have hs : ∑ s ∈ Finset.range n,
        B (x + stepDisplacement j (k, false) + siteOfCoords j (axisVec k (-((s : ℤ) + 1)))) k =
        ∑ s ∈ Finset.range n, B (x + siteOfCoords j (axisVec k (-(((s + 1 : ℕ) : ℤ) + 1)))) k := by
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      rw [e1, add_assoc, ← siteOfCoords_add, axisVec_add]
      congr 3
      push_cast
      ring
    rw [hs, e0]
    ring
theorem pathSum_segment {j : ℕ} (B : LevelForm F j) (x : F.Site j) (k : Fin 4) (m : ℤ) :
    pathSum B x (List.replicate m.natAbs (k, decide (0 ≤ m))) =
      segmentSum (fun l => B (x + siteOfCoords j (axisVec k l)) k) m := by
  rcases le_or_gt 0 m with h | h
  · have : decide (0 ≤ m) = true := by simp [h]
    rw [this, pathSum_replicate_forward]
    unfold segmentSum
    apply Finset.sum_congr rfl
    intro s _
    rw [stepSign_of_nonneg h, stepStart_of_nonneg h, one_mul]
  · have : decide (0 ≤ m) = false := by simp [not_le.mpr h]
    rw [this, pathSum_replicate_backward]
    unfold segmentSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [stepSign_of_neg h, stepStart_of_neg h]
    ring
theorem sum_stepDisplacement_segment (j : ℕ) (k : Fin 4) (m : ℤ) :
    ((List.replicate m.natAbs (k, decide (0 ≤ m))).map (stepDisplacement (F := F) j)).sum =
      siteOfCoords j (axisVec k m) := by
  simp only [List.map_replicate, List.sum_replicate]
  funext i
  by_cases h : i = k
  · subst h
    rcases le_or_gt 0 m with h0 | h0
    · have : decide (0 ≤ m) = true := by simp [h0]
      simp only [this, stepDisplacement, if_true, unitStep, siteOfCoords, axisVec, Pi.smul_apply,
        Pi.single_eq_same]
      have hm : ((m.natAbs : ℤ)) = m := by omega
      simp only [nsmul_eq_mul, Int.cast_one, mul_one]
      conv_rhs => rw [← hm]
      simp
    · have : decide (0 ≤ m) = false := by simp [not_le.mpr h0]
      simp only [this, stepDisplacement, Bool.false_eq_true, if_false, unitStep, siteOfCoords, axisVec,
        Pi.smul_apply, Pi.neg_apply, Pi.single_eq_same]
      have hm : -((m.natAbs : ℤ)) = m := by omega
      simp only [nsmul_eq_mul, Int.cast_one, mul_neg, mul_one]
      conv_rhs => rw [← hm]
      simp
  · by_cases hb : decide (0 ≤ m) = true
    · simp [hb, stepDisplacement, unitStep, siteOfCoords, axisVec, h]
    · have hb' : decide (0 ≤ m) = false := by simpa using hb
      simp [hb', stepDisplacement, unitStep, siteOfCoords, axisVec, h]
theorem pathSum_axisPath {j : ℕ} (B : LevelForm F j) (y : F.Site j) (o : Fin 4 → ℤ) :
    pathSum B y (axisPath o 1) = latticePathSum (fun v i => B (y + siteOfCoords j v) i) o := by
  have hr : List.finRange 4 = [0, 1, 2, 3] := by decide
  have h1 : leadingCoords o 1 = axisVec 0 (o 0) := by
    funext l
    fin_cases l <;> simp [leadingCoords, axisVec]
  have h2 : leadingCoords o 2 = axisVec 0 (o 0) + axisVec 1 (o 1) := by
    have := leadingCoords_succ o 1
    simpa [h1] using this
  have h3 : leadingCoords o 3 = axisVec 0 (o 0) + axisVec 1 (o 1) + axisVec 2 (o 2) := by
    have := leadingCoords_succ o 2
    simpa [h2] using this
  have h0 : leadingCoords o 0 = 0 := by
    funext l
    simp [leadingCoords]
  have hl : axisPath o 1 = List.replicate (o 0).natAbs (0, decide (0 ≤ o 0)) ++
      (List.replicate (o 1).natAbs (1, decide (0 ≤ o 1)) ++
        (List.replicate (o 2).natAbs (2, decide (0 ≤ o 2)) ++
          List.replicate (o 3).natAbs (3, decide (0 ≤ o 3)))) := by
    simp only [axisPath, hr, List.flatMap_cons, List.flatMap_nil, Equiv.Perm.coe_one, id,
      List.append_nil]
    rfl
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [hl, pathSum_append, pathSum_append, pathSum_append, latticePathSum, Fin.sum_univ_four]
  simp only [sum_stepDisplacement_segment, pathSum_segment, v0, v1, v2, v3, h0, h1, h2, h3,
    siteOfCoords_add, siteOfCoords_zero, add_zero, zero_add, add_assoc]
theorem latticeCurl_eq {j : ℕ} (B : LevelForm F j) (y : F.Site j) (v : Fin 4 → ℤ) (μ ν : Fin 4) :
    latticeCurl (fun v i => B (y + siteOfCoords j v) i) v μ ν = plaquetteCurl B (y + siteOfCoords j v) μ ν := by
  simp only [latticeCurl, plaquetteCurl, siteOfCoords_add, unitStep_eq, add_assoc]
theorem siteOffset_add_siteOfCoords (y : F.Site F.depth) (o : Fin 4 → ℤ)
    (hpos : ∀ i, 0 < F.period F.depth i)
    (ho : ∀ i, 2 * |o i| < F.period F.depth i) : siteOffset y (y + siteOfCoords F.depth o) = o := by
  funext i
  haveI : NeZero (F.period F.depth i) := ⟨(hpos i).ne'⟩
  simp only [siteOffset, add_sub_cancel_left, siteOfCoords]
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  have := ho i
  have h1 := abs_lt.mp (show |o i * 2| < (F.period F.depth i : ℤ) by rw [abs_mul]; simpa [mul_comm] using this)
  exact ⟨h1.1, h1.2.le⟩
theorem add_siteOfCoords_siteOffset (y x : F.Site F.depth) : y + siteOfCoords F.depth (siteOffset y x) = x := by
  funext i
  simp [siteOfCoords, siteOffset, ZMod.coe_valMinAbs]
theorem localAxialGauge_eq_curlStrip (R : ℝ) (y : F.Site F.depth) (W : LevelForm F F.depth) (o : Fin 4 → ℤ)
    (i : Fin 4) (hR : 0 < R) (hpos : ∀ i, 0 < F.period F.depth i)
    (ho : ∀ l, 2 * (|o l| + 1) < F.period F.depth l)
    (h1 : (siteSupDist (y + siteOfCoords F.depth o) y : ℝ) ≤ R)
    (h2 : (siteSupDist (y + siteOfCoords F.depth (o + axisVec i 1)) y : ℝ) ≤ R) :
    localAxialGauge R y W (y + siteOfCoords F.depth o) i =
      ∑ k : Fin 4, if i < k then
        segmentSum (fun j => plaquetteCurl W (y + siteOfCoords F.depth (leadingCoords o k.val + axisVec k j)) k i)
          (o k) else 0 := by
  have c1 : smoothCutoff R y (y + siteOfCoords F.depth o) = 1 := by
    unfold smoothCutoff
    have : 1 ≤ 2 - (siteSupDist (y + siteOfCoords F.depth o) y : ℝ) / R := by
      have : (siteSupDist (y + siteOfCoords F.depth o) y : ℝ) / R ≤ 1 := (div_le_one hR).mpr h1
      linarith
    rw [max_eq_right (by linarith), min_eq_left this]
  have c2 : smoothCutoff R y (y + siteOfCoords F.depth (o + axisVec i 1)) = 1 := by
    unfold smoothCutoff
    have : 1 ≤ 2 - (siteSupDist (y + siteOfCoords F.depth (o + axisVec i 1)) y : ℝ) / R := by
      have : (siteSupDist (y + siteOfCoords F.depth (o + axisVec i 1)) y : ℝ) / R ≤ 1 :=
        (div_le_one hR).mpr h2
      linarith
    rw [max_eq_right (by linarith), min_eq_left this]
  have off1 : siteOffset y (y + siteOfCoords F.depth o) = o :=
    siteOffset_add_siteOfCoords y o hpos fun l => by have := ho l; linarith
  have off2 : siteOffset y (y + siteOfCoords F.depth (o + axisVec i 1)) = o + axisVec i 1 := by
    apply siteOffset_add_siteOfCoords y _ hpos
    intro l
    have := ho l
    have hb : |(o + axisVec i 1) l| ≤ |o l| + 1 := by
      by_cases h : l = i
      · subst h
        simp only [Pi.add_apply, axisVec, Pi.single_eq_same]
        exact (abs_add_le _ _).trans (by simp)
      · simp [axisVec, h]
    linarith
  have e : y + siteOfCoords F.depth o + unitStep F.depth i = y + siteOfCoords F.depth (o + axisVec i 1) := by
    rw [siteOfCoords_add, unitStep_eq, add_assoc]
  have key := bond_add_latticePathSum_sub (fun v i => W (y + siteOfCoords F.depth v) i) o i
  simp only [latticeCurl_eq] at key
  rw [← key]
  simp only [localAxialGauge, addGradient, e, c1, c2, off1, off2, one_mul, pathSum_axisPath]
  ring
theorem abs_sub_mul_ediv_le (P u : ℤ) (hP : 0 < P) (hodd : P % 2 = 1) :
    |u - P * ((u + (P - 1) / 2) / P)| ≤ (P - 1) / 2 := by
  have h1 := Int.mul_ediv_add_emod (u + (P - 1) / 2) P
  have h2 := Int.emod_nonneg (u + (P - 1) / 2) hP.ne'
  have h3 := Int.emod_lt_of_pos (u + (P - 1) / 2) hP
  set w := (u + (P - 1) / 2) / P
  set r := (u + (P - 1) / 2) % P
  rw [abs_le]
  constructor <;> omega
theorem natAbs_valMinAbs_intCast_le (N : ℕ) [NeZero N] (b : ℤ) :
    ((b : ZMod N).valMinAbs).natAbs ≤ b.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) (hpos : 0 < F.period j i) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CurlSize.siteCoords_intCast <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) (hpos : ∀ i, 0 < F.period j i) :
    siteOfCoords j (siteCoords x) = x := by
  funext i
  exact siteCoords_cast x i (hpos i)
theorem top_sub_depth (F : BlockFrame) : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem period_depth (F : BlockFrame) (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem period_top (F : BlockFrame) (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
structure IsAdmissible (F : BlockFrame) : Prop where
  blockSide_odd : Odd F.blockSide
  extent_ge : ∀ i, 64 ≤ F.extent i
theorem IsAdmissible.blockSide_pos (h : IsAdmissible F) : 0 < F.blockSide := h.blockSide_odd.pos
theorem IsAdmissible.period_pos (h : IsAdmissible F) (j : ℕ) (i : Fin 4) : 0 < F.period j i := by
  have := h.extent_ge i
  have h2 := h.blockSide_pos
  unfold BlockFrame.period
  positivity
theorem blockSide_pow_emod_two (h : IsAdmissible F) (k : ℕ) : ((F.blockSide : ℤ) ^ k) % 2 = 1 := by
  have : Odd ((F.blockSide : ℤ) ^ k) := Odd.pow (by exact_mod_cast h.blockSide_odd)
  exact Int.odd_iff.mp this
theorem enclosingCell_spec (h : IsAdmissible F) {j : ℕ} (x : F.Site j) :
    ∃ w : Fin 4 → ℤ, enclosingCell x = siteOfCoords F.top w ∧
      ∀ i, |siteCoords x i - (F.blockSide : ℤ) ^ (F.top - j) * w i| ≤
        ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2 := by
  refine ⟨_, rfl, fun i => ?_⟩
  exact abs_sub_mul_ediv_le _ _ (by have := h.blockSide_pos; positivity) (blockSide_pow_emod_two h _)
theorem exists_eq_valMinAbs_add_mul {N : ℕ} (hN : 0 < N) (a : ℤ) (x : ZMod N) (hx : ((a : ℤ) : ZMod N) = x) :
    ∃ m : ℤ, a = x.valMinAbs + m * N := by
  have : NeZero N := ⟨hN.ne'⟩
  have : ((a - x.valMinAbs : ℤ) : ZMod N) = 0 := by
    push_cast
    rw [hx]; simp [ZMod.coe_valMinAbs]
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  exact ⟨m, by linarith [mul_comm (N : ℤ) m]⟩
theorem blockSide_mul_cellSupDist_le (h : IsAdmissible F) (x x' : F.Site F.depth) :
    F.blockSide * cellSupDist (enclosingCell x) (enclosingCell x') ≤ siteSupDist x x' + F.blockSide := by
  obtain ⟨w, hw, hb⟩ := enclosingCell_spec h x
  obtain ⟨w', hw', hb'⟩ := enclosingCell_spec h x'
  simp only [top_sub_depth, pow_one] at hb hb'
  unfold cellSupDist
  rw [Nat.mul_comm]
  have hL := h.blockSide_pos
  suffices H : ∀ i : Fin 4, (((enclosingCell x) i - (enclosingCell x') i).valMinAbs).natAbs * F.blockSide ≤
      siteSupDist x x' + F.blockSide by
    have : (Finset.univ.sup fun i => (((enclosingCell x) i - (enclosingCell x') i).valMinAbs).natAbs) ≤
        (siteSupDist x x' + F.blockSide) / F.blockSide := by
      apply Finset.sup_le
      intro i _
      exact (Nat.le_div_iff_mul_le hL).mpr (H i)
    calc _ ≤ ((siteSupDist x x' + F.blockSide) / F.blockSide) * F.blockSide := Nat.mul_le_mul_right _ this
      _ ≤ _ := Nat.div_mul_le_self _ _
  intro i
  have hpos := h.period_pos F.depth i
  have hposn := h.period_pos F.top i
  have : NeZero (F.period F.top i) := ⟨hposn.ne'⟩
  obtain ⟨m, hm⟩ := exists_eq_valMinAbs_add_mul hpos (siteCoords x i - siteCoords x' i) (x i - x' i) (by
    push_cast
    rw [siteCoords_cast x i hpos, siteCoords_cast x' i hpos])
  have hd : ((x i - x' i).valMinAbs).natAbs ≤ siteSupDist x x' := by
    unfold siteSupDist
    exact Finset.le_sup (f := fun i => ((x i - x' i).valMinAbs).natAbs) (Finset.mem_univ i)
  set d := (x i - x' i).valMinAbs
  have hper : (F.period F.depth i : ℤ) = (F.extent i : ℤ) * F.blockSide := by
    rw [period_depth]; push_cast; ring
  set β := w i - w' i - m * (F.extent i : ℤ) with hβ
  have hcast : (enclosingCell x) i - (enclosingCell x') i = ((β : ℤ) : ZMod (F.period F.top i)) := by
    rw [hw, hw']
    simp only [siteOfCoords, Pi.sub_apply, hβ]
    push_cast
    have : ((F.extent i : ℕ) : ZMod (F.period F.top i)) = 0 := by
      have e : F.period F.top i = F.extent i := period_top F i
      rw [← e]; simp
    rw [this]; ring
  have hB := natAbs_valMinAbs_intCast_le (F.period F.top i) β
  rw [← hcast] at hB
  rw [hper] at hm
  have e1 : (F.blockSide : ℤ) * β =
      d - (siteCoords x i - F.blockSide * w i) + (siteCoords x' i - F.blockSide * w' i) := by
    rw [hβ]
    linear_combination hm
  have h3 : |(F.blockSide : ℤ) * β| ≤ |d| + ((F.blockSide : ℤ) - 1) := by
    rw [e1]
    have a1 := abs_le.mp (hb i)
    have a2 := abs_le.mp (hb' i)
    have a3 := abs_le.mp (le_refl |d|)
    rw [abs_le]
    constructor <;> omega
  have h2 : |(F.blockSide : ℤ) * β| = (β.natAbs : ℤ) * F.blockSide := by
    rw [abs_mul, Nat.abs_cast, Int.natCast_natAbs]; ring
  have hB' : ((((enclosingCell x) i - (enclosingCell x') i).valMinAbs).natAbs : ℤ) * F.blockSide ≤
      (β.natAbs : ℤ) * F.blockSide :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hB) (by positivity)
  have goalZ : ((((enclosingCell x) i - (enclosingCell x') i).valMinAbs).natAbs : ℤ) * F.blockSide ≤
      (siteSupDist x x' : ℤ) + F.blockSide := by linarith
  exact_mod_cast goalZ
theorem natAbs_valMinAbs_le_siteSupDist {j : ℕ} (x y : F.Site j) (i : Fin 4) :
    ((x i - y i).valMinAbs).natAbs ≤ siteSupDist x y := by apply _root_.YangMills.Construction.LumpContours.natAbs_valMinAbs_sub_le_supDist <;> assumption
theorem natAbs_valMinAbs_le_cellSupDist (x y : F.Cell) (i : Fin 4) :
    ((x i - y i).valMinAbs).natAbs ≤ cellSupDist x y := by apply _root_.YangMills.Construction.PatchPoints.natAbs_valMinAbs_le_cellSupDist <;> assumption
theorem siteSupDist_comm {j : ℕ} (x y : F.Site j) : siteSupDist x y = siteSupDist y x := by apply _root_.YangMills.Construction.Holes.LinkComponentFacts.supDist_comm <;> assumption
theorem cellSupDist_comm (x y : F.Cell) : cellSupDist x y = cellSupDist y x := siteSupDist_comm x y
theorem cellSupDist_triangle (a b c : F.Cell) : cellSupDist a c ≤ cellSupDist a b + cellSupDist b c := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem siteSupDist_add_siteOfCoords_le (h : IsAdmissible F) {j : ℕ} (y : F.Site j) (v : Fin 4 → ℤ) (A : ℕ)
    (hv : ∀ i, |v i| ≤ A) : siteSupDist (y + siteOfCoords j v) y ≤ A := by
  unfold siteSupDist
  apply Finset.sup_le
  intro i _
  have : NeZero (F.period j i) := ⟨(h.period_pos j i).ne'⟩
  simp only [Pi.add_apply, add_sub_cancel_left, siteOfCoords]
  refine (natAbs_valMinAbs_intCast_le _ _).trans ?_
  have := hv i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
theorem mem_centredCube (M : ℕ) (o : Fin 4 → ℤ) :
    o ∈ centredCube M ↔ ∀ i, -(((M : ℤ) - 1) / 2) ≤ o i ∧ o i ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem card_centredCube (h : IsAdmissible F) : (centredCube F.blockSide).card = F.blockSide ^ 4 := by
  simp only [centredCube, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  have := h.blockSide_odd
  obtain ⟨k, hk⟩ := this
  rw [hk]
  push_cast
  have : (2 * (k : ℤ) + 1 - 1) / 2 = k := by omega
  rw [this]
  have : (k : ℤ) + 1 - -(k : ℤ) = ((2 * k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]
theorem cellCentre_siteOfCoords (h : IsAdmissible F) (w : Fin 4 → ℤ) :
    cellCentre F.depth (siteOfCoords F.top w) = siteOfCoords F.depth fun i => (F.blockSide : ℤ) * w i := by
  funext i
  simp only [cellCentre, siteOfCoords, top_sub_depth, pow_one]
  have hposn := h.period_pos F.top i
  have e : ((siteCoords (siteOfCoords (F := F) F.top w) i : ℤ) : ZMod (F.period F.top i)) =
      ((w i : ℤ) : ZMod (F.period F.top i)) :=
    siteCoords_cast _ i hposn
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at e
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  obtain ⟨m, hm⟩ := e
  rw [period_depth]
  rw [period_top] at hm
  refine ⟨m, ?_⟩
  push_cast
  linear_combination (F.blockSide : ℤ) * hm
theorem exists_offset_mem_centredCube (h : IsAdmissible F) (x : F.Site F.depth) :
    ∃ o ∈ centredCube F.blockSide, x = cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth o := by
  obtain ⟨w, hw, hb⟩ := enclosingCell_spec h x
  simp only [top_sub_depth, pow_one] at hb
  refine ⟨fun i => siteCoords x i - F.blockSide * w i, ?_, ?_⟩
  · rw [mem_centredCube]
    intro i
    exact abs_le.mp (hb i)
  · rw [hw, cellCentre_siteOfCoords h, ← siteOfCoords_add]
    have : ((fun i => (F.blockSide : ℤ) * w i) + fun i => siteCoords x i - F.blockSide * w i) =
        siteCoords x := by
      funext i; simp
    rw [this, siteOfCoords_siteCoords x (h.period_pos F.depth)]
theorem finite_cell (h : IsAdmissible F) : Finite F.Cell := by
  haveI : ∀ i, NeZero (F.period F.top i) := fun i => ⟨(h.period_pos _ i).ne'⟩
  exact Finite.of_fintype ((i : Fin 4) → ZMod (F.period F.top i))
theorem mem_finiteCells (h : IsAdmissible F) (z : F.Cell) : z ∈ finiteCells F := by
  haveI := finite_cell h
  unfold finiteCells
  rw [dif_pos (finite_cell h)]
  exact @Finset.mem_univ _ (Fintype.ofFinite _) z
theorem mem_sitesOfCells (h : IsAdmissible F) (x : F.Site F.depth) :
    x ∈ sitesOfCells (finiteCells F) F.depth := by
  obtain ⟨o, ho, e⟩ := exists_offset_mem_centredCube h x
  unfold sitesOfCells
  rw [Finset.mem_biUnion]
  refine ⟨enclosingCell x, mem_finiteCells h _, ?_⟩
  rw [Finset.mem_image, top_sub_depth, pow_one]
  exact ⟨o, ho, e.symm⟩
theorem mem_chordBonds_or_isAxialTreeBond (h : IsAdmissible F) (b : F.Site F.depth × Fin 4) :
    b ∈ chordBonds (finiteCells F) ∨ IsAxialTreeBond b := by
  by_cases hb : IsAxialTreeBond b
  · exact Or.inr hb
  · left
    unfold chordBonds innerBonds
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨⟨mem_sitesOfCells h _, mem_sitesOfCells h _⟩, hb⟩
theorem blockFineSites_subset (h : IsAdmissible F) (Y : F.Cell) :
    blockFineSites Y ⊆ (centredCube F.blockSide).image fun o => cellCentre F.depth Y + siteOfCoords F.depth o := by
  intro y hy
  unfold blockFineSites at hy
  rw [Finset.mem_filter] at hy
  obtain ⟨o, ho, e⟩ := exists_offset_mem_centredCube h y
  rw [Finset.mem_image]
  exact ⟨o, ho, by rw [← hy.2, ← e]⟩
theorem card_blockFineSites_le (h : IsAdmissible F) (Y : F.Cell) :
    (blockFineSites Y).card ≤ F.blockSide ^ 4 := by
  refine (Finset.card_le_card (blockFineSites_subset h Y)).trans ?_
  exact Finset.card_image_le.trans (card_centredCube h).le
theorem siteSupDist_cellCentre_le (h : IsAdmissible F) (Y : F.Cell) (y : F.Site F.depth)
    (hy : y ∈ blockFineSites Y) : siteSupDist y (cellCentre F.depth Y) ≤ F.blockSide := by
  have := blockFineSites_subset h Y hy
  rw [Finset.mem_image] at this
  obtain ⟨o, ho, rfl⟩ := this
  rw [siteSupDist_comm, siteSupDist_comm]
  apply siteSupDist_add_siteOfCoords_le h
  intro i
  have := (mem_centredCube _ _).mp ho i
  rw [abs_le]
  have hL := h.blockSide_pos
  constructor <;> omega
theorem enclosingCell_of_mem (Y : F.Cell) (y : F.Site F.depth) (hy : y ∈ blockFineSites Y) :
    enclosingCell y = Y := by
  unfold blockFineSites at hy
  exact (Finset.mem_filter.mp hy).2
theorem sum_sitesOfCells_le (h : IsAdmissible F) (f : F.Cell → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ x ∈ sitesOfCells (finiteCells F) F.depth, f (enclosingCell x) ≤
      (F.blockSide : ℝ) ^ 4 * ∑ z ∈ finiteCells F, f z := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := sitesOfCells (finiteCells F) F.depth) (t := finiteCells F)
    (g := enclosingCell) (fun x _ => mem_finiteCells h _), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have e : ∑ x ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun x => enclosingCell x = z),
      f (enclosingCell x) =
      (((sitesOfCells (finiteCells F) F.depth).filter (fun x => enclosingCell x = z)).card : ℝ) * f z := by
    rw [Finset.sum_congr rfl (g := fun _ => f z)
      (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const, nsmul_eq_mul]
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (hf z)
  have : ((sitesOfCells (finiteCells F) F.depth).filter (fun x => enclosingCell x = z)).card ≤
      F.blockSide ^ 4 := by
    refine le_trans (le_of_eq ?_) (card_blockFineSites_le h z)
    unfold blockFineSites
    congr
  exact_mod_cast this
def offsetBox (A : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(A : ℤ)) A
theorem mem_offsetBox (A : ℕ) (o : Fin 4 → ℤ) : o ∈ offsetBox A ↔ ∀ i, |o i| ≤ A := by
  simp [offsetBox, Fintype.mem_piFinset, abs_le]
theorem card_offsetBox (A : ℕ) : (offsetBox A).card = (2 * A + 1) ^ 4 := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.card_cubeBox <;> assumption
theorem sum_range_geometric_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, r ^ j ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric_of_lt_one h0 h1]
  exact (summable_geometric_of_lt_one h0 h1).sum_le_tsum _ fun _ _ => pow_nonneg h0 _
theorem sum_Icc_pow_natAbs_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) M, r ^ m.natAbs ≤ 2 * (1 - r)⁻¹ := by
  classical
  have hsub : Finset.Icc (-(M : ℤ)) M ⊆
      (Finset.range (M + 1)).image (fun j : ℕ => (j : ℤ)) ∪
        (Finset.range (M + 1)).image (fun j : ℕ => -(j : ℤ)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases le_or_gt 0 m with h | h
    · left
      exact ⟨m.toNat, by simp; omega, by omega⟩
    · right
      exact ⟨(-m).toNat, by simp; omega, by omega⟩
  have nn : ∀ m : ℤ, 0 ≤ r ^ m.natAbs := fun m => pow_nonneg h0 _
  calc ∑ m ∈ Finset.Icc (-(M : ℤ)) M, r ^ m.natAbs
      ≤ ∑ m ∈ (Finset.range (M + 1)).image (fun j : ℕ => (j : ℤ)) ∪
        (Finset.range (M + 1)).image (fun j : ℕ => -(j : ℤ)), r ^ m.natAbs :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => nn m
    _ ≤ ∑ m ∈ (Finset.range (M + 1)).image (fun j : ℕ => (j : ℤ)), r ^ m.natAbs +
        ∑ m ∈ (Finset.range (M + 1)).image (fun j : ℕ => -(j : ℤ)), r ^ m.natAbs := by
        rw [← Finset.sum_union_inter]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun m _ => nn m)
    _ = ∑ j ∈ Finset.range (M + 1), r ^ j + ∑ j ∈ Finset.range (M + 1), r ^ j := by
        rw [Finset.sum_image (fun a _ b _ e => by simpa using e),
          Finset.sum_image (fun a _ b _ e => by simpa using e)]
        simp
    _ ≤ 2 * (1 - r)⁻¹ := by
        have := sum_range_geometric_le h0 h1 (M + 1)
        linarith
def cellDecaySum (κ : ℝ) : ℝ := (2 * (1 - Real.exp (-(κ / 4)))⁻¹) ^ 4
theorem cellDecaySum_pos {κ : ℝ} (hκ : 0 < κ) : 0 < cellDecaySum κ := by
  have : Real.exp (-(κ / 4)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  unfold cellDecaySum
  have : 0 < 1 - Real.exp (-(κ / 4)) := by linarith
  positivity
theorem sum_exp_cellSupDist_le (h : IsAdmissible F) {κ : ℝ} (hκ : 0 < κ) (c : F.Cell) :
    ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ cellDecaySum κ := by
  classical
  set r := Real.exp (-(κ / 4)) with hr
  have r0 : 0 ≤ r := (Real.exp_pos _).le
  have r1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; linarith
  set M : ℕ := ∑ i, F.period F.top i with hM
  let off : F.Cell → Fin 4 → ℤ := fun z i => (z i - c i).valMinAbs
  have hinj : Set.InjOn off (finiteCells F) := by
    intro z _ z' _ e
    funext i
    have := congrFun e i
    have h2 : ((z i - c i).valMinAbs : ZMod (F.period F.top i)) =
        ((z' i - c i).valMinAbs : ZMod (F.period F.top i)) := by
      simp only [off] at this
      rw [this]
    rw [ZMod.coe_valMinAbs, ZMod.coe_valMinAbs] at h2
    exact sub_left_injective h2
  have hbound : ∀ z ∈ finiteCells F, off z ∈ offsetBox M := by
    intro z _
    rw [mem_offsetBox]
    intro i
    have : NeZero (F.period F.top i) := ⟨(h.period_pos _ i).ne'⟩
    have a1 := ZMod.natAbs_valMinAbs_le (z i - c i)
    have a2 : F.period F.top i ≤ M := Finset.single_le_sum (f := fun i => F.period F.top i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have a3 : F.period F.top i / 2 ≤ F.period F.top i := Nat.div_le_self _ _
    simp only [off]
    rw [Int.abs_eq_natAbs]
    exact_mod_cast a1.trans (a3.trans a2)
  have term : ∀ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ ∏ i, r ^ (off z i).natAbs := by
    intro z _
    rw [Finset.prod_pow_eq_pow_sum, hr, ← Real.exp_nat_mul, Real.exp_le_exp]
    have hs : ∑ i, (off z i).natAbs ≤ 4 * cellSupDist z c := by
      calc ∑ i, (off z i).natAbs ≤ ∑ _i : Fin 4, cellSupDist z c :=
            Finset.sum_le_sum fun i _ => natAbs_valMinAbs_le_cellSupDist z c i
        _ = 4 * cellSupDist z c := by simp
    have hs' : ((∑ i, (off z i).natAbs : ℕ) : ℝ) ≤ 4 * cellSupDist z c := by exact_mod_cast hs
    nlinarith
  calc ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c))
      ≤ ∑ z ∈ finiteCells F, ∏ i, r ^ (off z i).natAbs := Finset.sum_le_sum term
    _ = ∑ o ∈ (finiteCells F).image off, ∏ i, r ^ (o i).natAbs := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ o ∈ offsetBox M, ∏ i, r ^ (o i).natAbs := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro o ho
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ho
          exact hbound z hz
        · intro o _ _
          exact Finset.prod_nonneg fun i _ => pow_nonneg r0 _
    _ = ∏ _i : Fin 4, ∑ m ∈ Finset.Icc (-(M : ℤ)) M, r ^ m.natAbs := by
        rw [Finset.prod_univ_sum]
        rfl
    _ ≤ ∏ _i : Fin 4, 2 * (1 - r)⁻¹ := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg fun m _ => pow_nonneg r0 _
        · intro i _
          exact sum_Icc_pow_natAbs_le r0 r1 M
    _ = cellDecaySum κ := by simp [cellDecaySum, hr]
theorem cellSupDist_le_of_coords (h : IsAdmissible F) (v w : Fin 4 → ℤ) (Y : F.Cell)
    (hd : siteSupDist (siteOfCoords F.depth v) (cellCentre F.depth Y) ≤ 9 * F.blockSide)
    (he : ∀ i, |(F.blockSide : ℤ) * w i - v i| ≤ F.blockSide) :
    cellSupDist (siteOfCoords F.top w) Y ≤ 24 := by
  show (Finset.univ.sup fun i => ((siteOfCoords F.top w i - Y i).valMinAbs).natAbs) ≤ 24
  apply Finset.sup_le
  intro i _
  have hL := h.blockSide_pos
  have hpos := h.period_pos F.depth i
  have hposn := h.period_pos F.top i
  have : NeZero (F.period F.top i) := ⟨hposn.ne'⟩
  set cY := siteCoords Y i with hcY
  obtain ⟨m, hm⟩ := exists_eq_valMinAbs_add_mul hpos (v i - F.blockSide * cY)
    ((siteOfCoords F.depth v) i - (cellCentre F.depth Y) i) (by
    simp only [siteOfCoords, cellCentre, top_sub_depth, pow_one]
    push_cast
    rfl)
  have hdi := natAbs_valMinAbs_le_siteSupDist (siteOfCoords F.depth v) (cellCentre F.depth Y) i
  set d := ((siteOfCoords F.depth v) i - (cellCentre F.depth Y) i).valMinAbs
  have hper : (F.period F.depth i : ℤ) = (F.extent i : ℤ) * F.blockSide := by
    rw [period_depth]; push_cast; ring
  rw [hper] at hm
  set β := w i - cY - m * (F.extent i : ℤ) with hβ
  have hcast : siteOfCoords F.top w i - Y i = ((β : ℤ) : ZMod (F.period F.top i)) := by
    have e0 : ((cY : ℤ) : ZMod (F.period F.top i)) = Y i := siteCoords_cast Y i hposn
    simp only [siteOfCoords, hβ]
    push_cast
    have : ((F.extent i : ℕ) : ZMod (F.period F.top i)) = 0 := by
      have e : F.period F.top i = F.extent i := period_top F i
      rw [← e]; simp
    rw [this, e0]; ring
  rw [hcast]
  refine (natAbs_valMinAbs_intCast_le _ _).trans ?_
  have e1 : (F.blockSide : ℤ) * β = ((F.blockSide : ℤ) * w i - v i) + d := by
    rw [hβ]
    linear_combination hm
  have a1 := abs_le.mp (he i)
  have a2 : |d| ≤ 9 * F.blockSide := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hdi.trans hd
  have a3 := abs_le.mp a2
  have hb : |(F.blockSide : ℤ) * β| ≤ 10 * F.blockSide := by
    rw [e1, abs_le]
    constructor <;> omega
  rw [abs_mul, Nat.abs_cast, mul_comm] at hb
  have hb' : |β| ≤ 10 := by
    have hLp : (0 : ℤ) < F.blockSide := by exact_mod_cast hL
    exact le_of_mul_le_mul_right hb hLp
  have : (β.natAbs : ℤ) ≤ 10 := by rw [Int.natCast_natAbs]; exact hb'
  omega
theorem enclosingCell_mem_cellBall (h : IsAdmissible F) {j : ℕ} (hj : j ≤ F.top) (x : F.Site j) (Y : F.Cell)
    (hx : depthSite x ∈ depthBall (cellCentre F.depth Y) (9 * F.blockSide)) :
    enclosingCell x ∈ cellBall Y 24 := by
  have hL := h.blockSide_pos
  obtain ⟨w, hw, hb⟩ := enclosingCell_spec h x
  show cellSupDist (enclosingCell x) Y ≤ 24
  rw [hw]
  unfold depthBall depthSite at hx
  rw [Set.mem_setOf_eq] at hx
  by_cases hjt : j ≤ F.depth
  · rw [if_pos hjt] at hx
    set P : ℤ := (F.blockSide : ℤ) ^ (F.depth - j) with hP
    have hPp : 0 < P := by positivity
    have hPo : P % 2 = 1 := blockSide_pow_emod_two h _
    have hnj : (F.blockSide : ℤ) ^ (F.top - j) = P * F.blockSide := by
      rw [hP, ← pow_succ]
      congr 1
      simp only [BlockFrame.top]
      omega
    unfold ancestorSite at hx
    refine cellSupDist_le_of_coords h _ w Y hx fun i => ?_
    have b1 := abs_sub_mul_ediv_le P (siteCoords x i) hPp hPo
    have b2 := hb i
    rw [hnj] at b2
    set v := (siteCoords x i + (P - 1) / 2) / P
    have a1 := abs_le.mp b1
    have a2 := abs_le.mp b2
    have hPL : P ≤ P * F.blockSide := le_mul_of_one_le_right hPp.le (by omega)
    have e : P * ((F.blockSide : ℤ) * w i - v) =
        (siteCoords x i - P * v) - (siteCoords x i - P * F.blockSide * w i) := by ring
    have hb3 : |P * ((F.blockSide : ℤ) * w i - v)| ≤ P * F.blockSide := by
      rw [e, abs_le]
      constructor <;> omega
    rw [abs_mul, abs_of_pos hPp] at hb3
    exact le_of_mul_le_mul_left hb3 hPp
  · have hjn : j = F.top := by
      simp only [BlockFrame.top] at hj ⊢
      omega
    subst hjn
    rw [if_neg hjt] at hx
    refine cellSupDist_le_of_coords h _ w Y hx fun i => ?_
    have b2 := hb i
    simp only [Nat.sub_self, pow_zero, one_mul] at b2
    have : siteCoords x i - w i = 0 := by
      have := abs_le.mp b2
      simp only [sub_self, Int.zero_ediv] at this
      omega
    have e : (F.blockSide : ℤ) * w i - (F.blockSide : ℤ) * siteCoords x i = 0 := by
      linear_combination (-(F.blockSide : ℤ)) * this
    simp only [e, abs_zero]
    positivity
def weightScale (L : ℕ) : ℝ := (L : ℝ) ^ (1 / 640 : ℝ)
theorem weightScale_pow (L : ℕ) : weightScale L ^ 640 = L := by
  unfold weightScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num
theorem decayWeight_def (L : ℕ) (δ x : ℝ) :
    torusDecayFactor L δ x = max 1 ((x / weightScale L) ^ 16000) * Real.exp (δ * x) := rfl
theorem one_le_decayWeight (L : ℕ) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) : 1 ≤ torusDecayFactor L δ x := by
  rw [decayWeight_def]
  have h1 : 1 ≤ max 1 ((x / weightScale L) ^ 16000) := le_max_left _ _
  have h2 : 1 ≤ Real.exp (δ * x) := Real.one_le_exp (by positivity)
  nlinarith
theorem decayWeight_pos (L : ℕ) (δ x : ℝ) : 0 < torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
theorem decayWeight_monotone (L : ℕ) (hL : 0 < L) {δ x x' : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hxx : x ≤ x') :
    torusDecayFactor L δ x ≤ torusDecayFactor L δ x' := by
  rw [decayWeight_def, decayWeight_def]
  have hs : 0 < weightScale L := by unfold weightScale; positivity
  have h1 : (x / weightScale L) ^ 16000 ≤ (x' / weightScale L) ^ 16000 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) _
  have h2 : max 1 ((x / weightScale L) ^ 16000) ≤ max 1 ((x' / weightScale L) ^ 16000) :=
    max_le_max le_rfl h1
  have h3 : Real.exp (δ * x) ≤ Real.exp (δ * x') := Real.exp_le_exp.mpr (by gcongr)
  have h4 : (0 : ℝ) ≤ max 1 ((x / weightScale L) ^ 16000) := le_trans zero_le_one (le_max_left _ _)
  exact mul_le_mul h2 h3 (Real.exp_pos _).le (h4.trans h2)
theorem pow_le_decayWeight (L : ℕ) (hL : 0 < L) {δ x : ℝ} (hδ : 0 ≤ δ) (hs1 : 1 ≤ weightScale L)
    (hx : weightScale L ^ 5 ≤ x) : weightScale L ^ 64000 ≤ torusDecayFactor L δ x := by
  set ν := weightScale L
  have hν : 0 < ν := by linarith
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  rw [decayWeight_def]
  have h1 : ν ^ 4 ≤ x / ν := by
    rw [le_div_iff₀ hν]; calc ν ^ 4 * ν = ν ^ 5 := by ring
      _ ≤ x := hx
  have h2 : ν ^ 64000 ≤ (x / ν) ^ 16000 := by
    calc ν ^ 64000 = (ν ^ 4) ^ 16000 := by rw [← pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) h1 _
  have h3 : 1 ≤ Real.exp (δ * x) := Real.one_le_exp (by positivity)
  calc ν ^ 64000 ≤ max 1 ((x / ν) ^ 16000) := h2.trans (le_max_right _ _)
    _ ≤ max 1 ((x / ν) ^ 16000) * Real.exp (δ * x) :=
      le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) h3
theorem pow_mul_decayWeight_le (L : ℕ) (hL : 0 < L) {δ x n : ℝ} (hδ : 0 ≤ δ) (hs2 : 2 ≤ weightScale L)
    (hn : 0 ≤ n) (hx : weightScale L ^ 5 ≤ x) (hxn : (L : ℝ) * n ≤ 4 * x) :
    weightScale L ^ 64000 * torusDecayFactor L δ n ≤ torusDecayFactor L δ x := by
  have hpow := weightScale_pow L
  set ν := weightScale L with hνdef
  have hν : 0 < ν := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hL4 : ν ^ 4 * 4 ≤ (L : ℝ) := by
    rw [← hpow]
    have h1 : (2 : ℝ) ^ 2 ≤ ν ^ 2 := pow_le_pow_left₀ (by norm_num) hs2 2
    have h2 : ν ^ 6 ≤ ν ^ 640 / ν ^ 0 := by
      simpa using pow_le_pow_right₀ hν1 (by norm_num : 6 ≤ 640)
    have h3 : ν ^ 4 * 4 ≤ ν ^ 6 := by nlinarith [pow_pos hν 4]
    simpa using h3.trans h2
  have hnx : n ≤ x := by
    have : (4 : ℝ) ≤ L := by nlinarith [one_le_pow₀ hν1 (n := 4)]
    nlinarith
  rw [decayWeight_def, decayWeight_def, ← hνdef]
  have hexp : Real.exp (δ * n) ≤ Real.exp (δ * x) := Real.exp_le_exp.mpr (by gcongr)
  have hbig : ν ^ 64000 * max 1 ((n / ν) ^ 16000) ≤ (x / ν) ^ 16000 := by
    rcases le_total ((n / ν) ^ 16000) 1 with h | h
    · rw [max_eq_left h, mul_one]
      have h1 : ν ^ 4 ≤ x / ν := by
        rw [le_div_iff₀ hν]; calc ν ^ 4 * ν = ν ^ 5 := by ring
          _ ≤ x := hx
      calc ν ^ 64000 = (ν ^ 4) ^ 16000 := by rw [← pow_mul]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) h1 _
    · rw [max_eq_right h]
      have h1 : ν ^ 4 * (n / ν) ≤ x / ν := by
        have : ν ^ 4 * (n / ν) * 4 ≤ (L : ℝ) * (n / ν) := by
          have hq : 0 ≤ n / ν := by positivity
          nlinarith
        have h5 : (L : ℝ) * (n / ν) ≤ 4 * (x / ν) := by
          rw [mul_div_assoc', mul_div_assoc']
          gcongr
        linarith
      calc ν ^ 64000 * (n / ν) ^ 16000 = (ν ^ 4 * (n / ν)) ^ 16000 := by rw [mul_pow, ← pow_mul]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) h1 _
  calc ν ^ 64000 * (max 1 ((n / ν) ^ 16000) * Real.exp (δ * n))
      = (ν ^ 64000 * max 1 ((n / ν) ^ 16000)) * Real.exp (δ * n) := by ring
    _ ≤ (x / ν) ^ 16000 * Real.exp (δ * x) :=
      mul_le_mul hbig hexp (Real.exp_pos _).le (pow_nonneg (div_nonneg hx0 hν.le) _)
    _ ≤ max 1 ((x / ν) ^ 16000) * Real.exp (δ * x) := by
      gcongr
      exact le_max_right _ _
theorem decayWeight_mul_exp_le_one (L : ℕ) (hL : 0 < L) {δ del n : ℝ} (hδ : 0 ≤ δ) (hdel : 0 < del)
    (hδd : δ ≤ del / 64) (hs : 1000000 / del ≤ weightScale L) (hn : 0 ≤ n) :
    torusDecayFactor L δ n * Real.exp (-(del * n / 8)) ≤ 1 := by
  set ν := weightScale L
  have hν : 0 < ν := lt_of_lt_of_le (by positivity) hs
  rw [decayWeight_def, mul_assoc, ← Real.exp_add]
  rcases le_total ((n / ν) ^ 16000) 1 with h | h
  · rw [max_eq_left h, one_mul]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  · rw [max_eq_right h]
    set u := n / ν with hu
    have hu0 : 0 ≤ u := by positivity
    have hn' : n = u * ν := by rw [hu]; field_simp
    have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have h2 : u ^ 16000 ≤ Real.exp (16000 * u) := by
      calc u ^ 16000 ≤ (Real.exp u) ^ 16000 := pow_le_pow_left₀ hu0 h1 _
        _ = Real.exp (16000 * u) := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : 1000000 ≤ del * ν := by
      rw [div_le_iff₀ hdel] at hs
      linarith
    have h4 : δ * n + -(del * n / 8) ≤ -(16000 * u) := by
      have a1 : δ * n ≤ del / 64 * n := by gcongr
      have a2 : del * n = (del * ν) * u := by rw [hn']; ring
      have a3 : 1000000 * u ≤ (del * ν) * u := by gcongr
      nlinarith
    calc u ^ 16000 * Real.exp (δ * n + -(del * n / 8))
        ≤ Real.exp (16000 * u) * Real.exp (-(16000 * u)) :=
          mul_le_mul h2 (Real.exp_le_exp.mpr h4) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
def stripSite (o : Fin 4 → ℤ) (k : Fin 4) (s : ℕ) : Fin 4 → ℤ :=
  leadingCoords o k.val + axisVec k (stepStart (o k) s)
theorem abs_stepStart_le (m : ℤ) (s : ℕ) (hs : s < m.natAbs) : |stepStart m s| ≤ |m| := by
  rcases le_or_gt 0 m with h | h
  · rw [stepStart_of_nonneg h, abs_of_nonneg (by positivity), abs_of_nonneg h]
    omega
  · rw [stepStart_of_neg h, abs_of_neg (by omega), abs_of_neg h]
    omega
theorem abs_stripSite_le (o : Fin 4 → ℤ) (k : Fin 4) (s : ℕ) (hs : s < (o k).natAbs) (D : ℕ)
    (hD : ∀ l, |o l| ≤ D) (l : Fin 4) : |stripSite o k s l| ≤ D := by
  unfold stripSite
  by_cases hl : l = k
  · subst hl
    simp only [Pi.add_apply, leadingCoords, lt_self_iff_false, if_false, zero_add, axisVec,
      Pi.single_eq_same]
    exact (abs_stepStart_le _ _ hs).trans (hD _)
  · simp only [Pi.add_apply, axisVec, Pi.single_apply, hl, if_false, add_zero, leadingCoords]
    split_ifs
    · exact hD l
    · simp
def stripTotal (A : ℕ) (Φ : (Fin 4 → ℤ) → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ o ∈ offsetBox A, ∑ i : Fin 4, ∑ k : Fin 4, if i < k then
    ∑ s ∈ Finset.range (o k).natAbs, Φ (stripSite o k s) i k else 0
def stripIndices (A : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4 × Fin 4 × ℕ) :=
  offsetBox A ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ Finset.range A))
theorem card_stripIndices (A : ℕ) : (stripIndices A).card = (2 * A + 1) ^ 4 * (4 * (4 * A)) := by
  simp [stripIndices, Finset.card_product, card_offsetBox]
def stripTerm (Φ : (Fin 4 → ℤ) → Fin 4 → Fin 4 → ℝ) (ι : (Fin 4 → ℤ) × Fin 4 × Fin 4 × ℕ) : ℝ :=
  if ι.2.1 < ι.2.2.1 ∧ ι.2.2.2 < (ι.1 ι.2.2.1).natAbs then
    Φ (stripSite ι.1 ι.2.2.1 ι.2.2.2) ι.2.1 ι.2.2.1 else 0
theorem stripTotal_eq_sum (A : ℕ) (Φ : (Fin 4 → ℤ) → Fin 4 → Fin 4 → ℝ) :
    stripTotal A Φ = ∑ ι ∈ stripIndices A, stripTerm Φ ι := by
  unfold stripTotal stripIndices
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro o ho
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (o k).natAbs ≤ A := by
    have := (mem_offsetBox A o).mp ho k
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  by_cases hik : i < k
  · simp only [stripTerm, hik, true_and, if_true]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ fun _ _ => rfl
    ext s
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  · simp [stripTerm, hik]
theorem stripTotal_le_of_bound (A : ℕ) (Φ : (Fin 4 → ℤ) → Fin 4 → Fin 4 → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ (v : Fin 4 → ℤ) (i k : Fin 4), i < k → (∀ l, |v l| ≤ (A : ℤ)) → Φ v i k ≤ D) :
    stripTotal A Φ ≤ ((stripIndices A).card : ℝ) * D := by
  rw [stripTotal_eq_sum, ← nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro ι hι
  unfold stripTerm
  split_ifs with hc
  · apply h _ _ _ hc.1
    have ho : ι.1 ∈ offsetBox A := by
      simp only [stripIndices, Finset.mem_product] at hι
      exact hι.1
    exact abs_stripSite_le _ _ _ hc.2 A ((mem_offsetBox A _).mp ho)
  · exact hD
theorem sum_stripTotal_sq_le {J : Type} (S : Finset J) (A : ℕ) (Φ : J → (Fin 4 → ℤ) → Fin 4 → Fin 4 → ℝ)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (h : ∀ (v : Fin 4 → ℤ) (i k : Fin 4), i < k → (∀ l, |v l| ≤ (A : ℤ)) → ∑ y ∈ S, Φ y v i k ^ 2 ≤ Q) :
    ∑ y ∈ S, stripTotal A (Φ y) ^ 2 ≤ ((stripIndices A).card : ℝ) ^ 2 * Q := by
  have h1 : ∀ y ∈ S, stripTotal A (Φ y) ^ 2 ≤
      ((stripIndices A).card : ℝ) * ∑ ι ∈ stripIndices A, stripTerm (Φ y) ι ^ 2 := by
    intro y _
    rw [stripTotal_eq_sum]
    exact sq_sum_le_card_mul_sum_sq
  calc ∑ y ∈ S, stripTotal A (Φ y) ^ 2
      ≤ ∑ y ∈ S, ((stripIndices A).card : ℝ) * ∑ ι ∈ stripIndices A, stripTerm (Φ y) ι ^ 2 :=
        Finset.sum_le_sum h1
    _ = ((stripIndices A).card : ℝ) * ∑ ι ∈ stripIndices A, ∑ y ∈ S, stripTerm (Φ y) ι ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ((stripIndices A).card : ℝ) * ∑ _ι ∈ stripIndices A, Q := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro ι hι
        by_cases hc : ι.2.1 < ι.2.2.1 ∧ ι.2.2.2 < (ι.1 ι.2.2.1).natAbs
        · simp only [stripTerm, hc, and_self, if_true]
          apply h _ _ _ hc.1
          have ho : ι.1 ∈ offsetBox A := by
            simp only [stripIndices, Finset.mem_product] at hι
            exact hι.1
          exact abs_stripSite_le _ _ _ hc.2 A ((mem_offsetBox A _).mp ho)
        · simp only [stripTerm, hc, if_false]
          simpa using hQ
    _ = ((stripIndices A).card : ℝ) ^ 2 * Q := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring
def nearbyBonds (A : ℕ) (y : F.Site F.depth) : Finset (F.Site F.depth × Fin 4) :=
  (fineBonds F).filter fun b => siteSupDist b.1 y ≤ A
theorem sum_nearbyBonds_le (h : IsAdmissible F) (A : ℕ) (y : F.Site F.depth) (f : F.Site F.depth × Fin 4 → ℝ)
    (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ nearbyBonds A y, f b ≤ ∑ o ∈ offsetBox A, ∑ i : Fin 4, f (y + siteOfCoords F.depth o, i) := by
  classical
  let off : F.Site F.depth × Fin 4 → (Fin 4 → ℤ) × Fin 4 := fun b => (siteOffset y b.1, b.2)
  have hinj : Set.InjOn off (nearbyBonds A y) := by
    intro b _ b' _ e
    have e1 : siteOffset y b.1 = siteOffset y b'.1 := (Prod.ext_iff.mp e).1
    have e2 : b.2 = b'.2 := (Prod.ext_iff.mp e).2
    have : b.1 = b'.1 := by
      rw [← add_siteOfCoords_siteOffset y b.1, e1, add_siteOfCoords_siteOffset]
    exact Prod.ext this e2
  have hrec : ∀ b, f b = (fun u : (Fin 4 → ℤ) × Fin 4 => f (y + siteOfCoords F.depth u.1, u.2)) (off b) := by
    intro b
    simp only [off, add_siteOfCoords_siteOffset]
  calc ∑ b ∈ nearbyBonds A y, f b
      = ∑ u ∈ (nearbyBonds A y).image off, f (y + siteOfCoords F.depth u.1, u.2) := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl fun b _ => hrec b
    _ ≤ ∑ u ∈ offsetBox A ×ˢ (Finset.univ : Finset (Fin 4)), f (y + siteOfCoords F.depth u.1, u.2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
          simp only [Finset.mem_product, Finset.mem_univ, and_true, off]
          rw [mem_offsetBox]
          intro i
          have h1 := natAbs_valMinAbs_le_siteSupDist b.1 y i
          have h2 := (Finset.mem_filter.mp hb).2
          simp only [siteOffset, Pi.sub_apply]
          rw [Int.abs_eq_natAbs]
          exact_mod_cast h1.trans h2
        · intro u _ _
          exact hf _
    _ = _ := by rw [Finset.sum_product]
theorem localAxialGauge_of_mem_offsetBox (h : IsAdmissible F) (R : ℝ) (W : LevelForm F F.depth)
    (y : F.Site F.depth) (A : ℕ) (hA : (A : ℝ) + 1 ≤ R)
    (hA2 : 2 * (A + 1) < 64 * F.blockSide) (o : Fin 4 → ℤ) (ho : o ∈ offsetBox A) (i : Fin 4) :
    localAxialGauge R y W (y + siteOfCoords F.depth o) i =
      ∑ k : Fin 4, if i < k then
        segmentSum (fun j => plaquetteCurl W (y + siteOfCoords F.depth (leadingCoords o k.val + axisVec k j)) k i)
          (o k) else 0 := by
  have hb := (mem_offsetBox A o).mp ho
  have hR : 0 < R := by
    have : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    linarith
  apply localAxialGauge_eq_curlStrip R y W o i hR (h.period_pos F.depth)
  · intro l
    have a1 := hb l
    have a2 : (F.period F.depth l : ℤ) = (F.extent l : ℤ) * F.blockSide := by
      rw [period_depth]; push_cast; ring
    have a3 : (64 : ℤ) ≤ F.extent l := by exact_mod_cast h.extent_ge l
    have a5 : (64 : ℤ) * F.blockSide ≤ F.period F.depth l := by rw [a2]; nlinarith
    omega
  · have : siteSupDist (y + siteOfCoords F.depth o) y ≤ A := siteSupDist_add_siteOfCoords_le h y o A hb
    have : (siteSupDist (y + siteOfCoords F.depth o) y : ℝ) ≤ A := by exact_mod_cast this
    linarith
  · have : siteSupDist (y + siteOfCoords F.depth (o + axisVec i 1)) y ≤ A + 1 := by
      apply siteSupDist_add_siteOfCoords_le h
      intro l
      have a1 := hb l
      have hb' : |(o + axisVec i 1) l| ≤ |o l| + 1 := by
        by_cases hl : l = i
        · subst hl
          simp only [Pi.add_apply, axisVec, Pi.single_eq_same]
          exact (abs_add_le _ _).trans (by simp)
        · simp [axisVec, hl]
      push_cast
      linarith
    have : (siteSupDist (y + siteOfCoords F.depth (o + axisVec i 1)) y : ℝ) ≤ A + 1 := by exact_mod_cast this
    linarith
def curlMagnitudes (W : LevelForm F F.depth) (y : F.Site F.depth) : (Fin 4 → ℤ) → Fin 4 → Fin 4 → ℝ :=
  fun v i k => |plaquetteCurl W (y + siteOfCoords F.depth v) k i|
theorem sum_nearbyBonds_abs_localAxialGauge_le (h : IsAdmissible F) (R : ℝ) (W : LevelForm F F.depth)
    (y : F.Site F.depth) (A : ℕ) (hA : (A : ℝ) + 1 ≤ R) (hA2 : 2 * (A + 1) < 64 * F.blockSide) :
    ∑ b ∈ nearbyBonds A y, |localAxialGauge R y W b.1 b.2| ≤ stripTotal A (curlMagnitudes W y) := by
  refine (sum_nearbyBonds_le h A y (fun b => |localAxialGauge R y W b.1 b.2|) fun _ => abs_nonneg _).trans ?_
  apply Finset.sum_le_sum
  intro o ho
  apply Finset.sum_le_sum
  intro i _
  simp only
  rw [localAxialGauge_of_mem_offsetBox h R W y A hA hA2 o ho i]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  by_cases hik : i < k
  · simp only [hik, if_true]
    refine (abs_segmentSum_le _ _).trans (le_of_eq ?_)
    rfl
  · simp [hik]
theorem exp_natCast_le_three_pow (m : ℕ) : Real.exp m ≤ 3 ^ m := by
  have h : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  calc Real.exp m = (Real.exp 1) ^ m := by rw [← Real.exp_nat_mul]; simp
    _ ≤ 3 ^ m := pow_le_pow_left₀ (Real.exp_pos _).le h _
theorem exp_neg_le_three_pow_mul {del : ℝ} (h0 : 0 < del) (h1 : del ≤ 1) (a b m : ℕ) (hab : a ≤ b + m) :
    Real.exp (-(del * b)) ≤ 3 ^ m * Real.exp (-(del * a)) := by
  have e : Real.exp (-(del * b)) ≤ Real.exp m * Real.exp (-(del * a)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have : (a : ℝ) ≤ b + m := by exact_mod_cast hab
    nlinarith
  exact e.trans (mul_le_mul_of_nonneg_right (exp_natCast_le_three_pow m) (Real.exp_pos _).le)
theorem cellSupDist_le_two (h : IsAdmissible F) (x x' : F.Site F.depth) (hd : siteSupDist x x' ≤ F.blockSide) :
    cellSupDist (enclosingCell x) (enclosingCell x') ≤ 2 := by
  have h1 := blockSide_mul_cellSupDist_le h x x'
  have hL := h.blockSide_pos
  by_contra hc
  push_neg at hc
  have : F.blockSide * 3 ≤ F.blockSide * cellSupDist (enclosingCell x) (enclosingCell x') :=
    Nat.mul_le_mul_left _ hc
  omega
section ResponseBounds
variable (W : LevelForm F F.depth) (cc : F.Cell) (K del : ℝ)
theorem abs_pathSum_axisPath_le (h : IsAdmissible F) (h0 : 0 < del) (h1 : del ≤ 1) (hK : 0 ≤ K)
    (hW : ∀ x i, |W x i| ≤ K * Real.exp (-(del * cellSupDist (enclosingCell x) cc))) (y z : F.Site F.depth)
    (hd : siteSupDist z y ≤ F.blockSide) :
    |pathSum W y (axisPath (siteOffset y z) 1)| ≤
      4 * siteSupDist z y * (9 * K * Real.exp (-(del * cellSupDist (enclosingCell y) cc))) := by
  set o := siteOffset y z with ho
  set d := siteSupDist z y with hdd
  set M := 9 * K * Real.exp (-(del * cellSupDist (enclosingCell y) cc)) with hM
  have hM0 : 0 ≤ M := by positivity
  have hb : ∀ l, |o l| ≤ (d : ℤ) := by
    intro l
    have := natAbs_valMinAbs_le_siteSupDist z y l
    simp only [ho, siteOffset, Pi.sub_apply]
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this
  have hseg : ∀ k : Fin 4,
      |segmentSum (fun j => W (y + siteOfCoords F.depth (leadingCoords o k.val + axisVec k j)) k) (o k)| ≤
        d * M := by
    intro k
    refine (abs_segmentSum_le _ _).trans ?_
    have hterm : ∀ s ∈ Finset.range (o k).natAbs,
        |W (y + siteOfCoords F.depth (leadingCoords o k.val + axisVec k (stepStart (o k) s))) k| ≤ M := by
      intro s hs
      have hs' := Finset.mem_range.mp hs
      have hp : siteSupDist (y + siteOfCoords F.depth (stripSite o k s)) y ≤ d :=
        siteSupDist_add_siteOfCoords_le h y _ d (abs_stripSite_le o k s hs' d hb)
      have hc := cellSupDist_le_two h _ _ (hp.trans hd)
      refine (hW _ _).trans ?_
      rw [hM, mul_assoc 9, mul_left_comm]
      apply mul_le_mul_of_nonneg_left _ hK
      have := exp_neg_le_three_pow_mul h0 h1 (cellSupDist (enclosingCell y) cc)
        (cellSupDist (enclosingCell (y + siteOfCoords F.depth (stripSite o k s))) cc) 2 (by
          have a := cellSupDist_triangle (enclosingCell y)
            (enclosingCell (y + siteOfCoords F.depth (stripSite o k s))) cc
          have b := cellSupDist_comm (enclosingCell y) (enclosingCell (y + siteOfCoords F.depth (stripSite o k s)))
          omega)
      unfold stripSite at this
      norm_num at this
      linarith
    calc _ ≤ ∑ _s ∈ Finset.range (o k).natAbs, M := Finset.sum_le_sum hterm
      _ = ((o k).natAbs : ℝ) * M := by simp
      _ ≤ d * M := by
        apply mul_le_mul_of_nonneg_right _ hM0
        have := hb k
        rw [Int.abs_eq_natAbs] at this
        exact_mod_cast this
  rw [pathSum_axisPath]
  unfold latticePathSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _k : Fin 4, (d : ℝ) * M := Finset.sum_le_sum fun k _ => hseg k
    _ = _ := by simp; ring
theorem abs_localAxialGauge_le (h : IsAdmissible F) (h0 : 0 < del) (h1 : del ≤ 1) (hK : 0 ≤ K)
    (hW : ∀ x i, |W x i| ≤ K * Real.exp (-(del * cellSupDist (enclosingCell x) cc))) (R : ℝ) (hR1 : 1 ≤ R)
    (hRL : 2 * R ≤ F.blockSide) (y x : F.Site F.depth) (i : Fin 4) :
    |localAxialGauge R y W x i| ≤ 12000 * R * K * Real.exp (-(del * cellSupDist (enclosingCell x) cc)) := by
  set Dx := Real.exp (-(del * cellSupDist (enclosingCell x) cc)) with hDx
  have hR0 : 0 < R := by linarith
  have hφ : ∀ z, siteSupDist z x ≤ 1 →
      |smoothCutoff R y z * (- pathSum W y (axisPath (siteOffset y z) 1))| ≤ 5832 * R * K * Dx := by
    intro z hz
    by_cases hzy : (siteSupDist z y : ℝ) < 2 * R
    · have hle : siteSupDist z y ≤ F.blockSide := by
        have : (siteSupDist z y : ℝ) ≤ F.blockSide := by linarith
        exact_mod_cast this
      have hp := abs_pathSum_axisPath_le W cc K del h h0 h1 hK hW y z hle
      have hc0 : 0 ≤ smoothCutoff R y z := by
        unfold smoothCutoff
        exact le_min zero_le_one (le_max_left _ _)
      have hc1 : smoothCutoff R y z ≤ 1 := min_le_left _ _
      have hL := h.blockSide_pos
      have c1 := cellSupDist_le_two h z y hle
      have c2 := cellSupDist_le_two h z x (hz.trans (by omega))
      have hshift := exp_neg_le_three_pow_mul h0 h1 (cellSupDist (enclosingCell x) cc)
        (cellSupDist (enclosingCell y) cc) 4 (by
        have a := cellSupDist_triangle (enclosingCell x) (enclosingCell y) cc
        have b := cellSupDist_triangle (enclosingCell x) (enclosingCell z) (enclosingCell y)
        have e := cellSupDist_comm (enclosingCell x) (enclosingCell z)
        omega)
      rw [abs_mul, abs_neg, abs_of_nonneg hc0]
      set Dy := Real.exp (-(del * cellSupDist (enclosingCell y) cc)) with hDy
      have e1 : |pathSum W y (axisPath (siteOffset y z) 1)| ≤ 4 * (2 * R) * (9 * K * Dy) := by
        refine hp.trans ?_
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      have e2 : Dy ≤ 81 * Dx := by
        have : (3 : ℝ) ^ 4 = 81 := by norm_num
        rw [this] at hshift
        exact hshift
      calc smoothCutoff R y z * |pathSum W y (axisPath (siteOffset y z) 1)|
          ≤ 1 * |pathSum W y (axisPath (siteOffset y z) 1)| :=
            mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
        _ ≤ 4 * (2 * R) * (9 * K * Dy) := by rw [one_mul]; exact e1
        _ ≤ 4 * (2 * R) * (9 * K * (81 * Dx)) := by gcongr
        _ = 5832 * R * K * Dx := by ring
    · have : smoothCutoff R y z = 0 := by
        unfold smoothCutoff
        have h2 : 2 - (siteSupDist z y : ℝ) / R ≤ 0 := by
          have : 2 ≤ (siteSupDist z y : ℝ) / R := by
            rw [le_div_iff₀ hR0]; linarith
          linarith
        rw [max_eq_left h2, min_eq_right zero_le_one]
      rw [this, zero_mul, abs_zero]
      positivity
  have hb : |W x i| ≤ R * K * Dx := by
    refine (hW x i).trans ?_
    have : K * Dx ≤ R * (K * Dx) := le_mul_of_one_le_left (by positivity) hR1
    linarith
  have hx1 := hφ x (by simp [siteSupDist, ZMod.valMinAbs_zero])
  have hx2 := hφ (x + unitStep F.depth i) (by
    rw [unitStep_eq]
    apply siteSupDist_add_siteOfCoords_le h
    intro l
    by_cases hl : l = i
    · subst hl; simp [axisVec]
    · simp [axisVec, hl])
  unfold localAxialGauge addGradient
  have hh : 0 ≤ R * K * Dx := by positivity
  rw [abs_le]
  have a1 := abs_le.mp hb
  have a2 := abs_le.mp hx1
  have a3 := abs_le.mp hx2
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
theorem sum_fineBonds_le (h : IsAdmissible F) (f : F.Cell → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ b ∈ fineBonds F, f (enclosingCell b.1) ≤ 4 * ((F.blockSide : ℝ) ^ 4 * ∑ z ∈ finiteCells F, f z) := by
  unfold fineBonds
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have := sum_sitesOfCells_le h f hf
  push_cast
  linarith
def bondsNearCell (n : ℕ) (Y : F.Cell) : Finset (F.Site F.depth × Fin 4) :=
  (fineBonds F).filter fun b => 4 * cellSupDist (enclosingCell b.1) Y < n + 4
theorem sum_abs_localAxialGauge_le (h : IsAdmissible F) (h0 : 0 < del) (h1 : del ≤ 1) (hK : 0 ≤ K)
    (hW : ∀ x i, |W x i| ≤ K * Real.exp (-(del * cellSupDist (enclosingCell x) cc))) (R : ℝ) (hR1 : 1 ≤ R)
    (hRL : 2 * R ≤ F.blockSide) (y : F.Site F.depth) :
    ∑ b ∈ fineBonds F, |localAxialGauge R y W b.1 b.2| ≤
      12000 * R * K * (4 * ((F.blockSide : ℝ) ^ 4 * cellDecaySum (del / 2))) := by
  have hk : 0 ≤ 12000 * R * K := by positivity
  calc _ ≤ ∑ b ∈ fineBonds F,
        12000 * R * K * Real.exp (-(del / 2 * cellSupDist (enclosingCell b.1) cc)) := by
        apply Finset.sum_le_sum
        intro b _
        refine (abs_localAxialGauge_le W cc K del h h0 h1 hK hW R hR1 hRL y b.1 b.2).trans ?_
        apply mul_le_mul_of_nonneg_left _ hk
        rw [Real.exp_le_exp]
        have : (0 : ℝ) ≤ cellSupDist (enclosingCell b.1) cc := Nat.cast_nonneg _
        nlinarith
    _ = 12000 * R * K * ∑ b ∈ fineBonds F, Real.exp (-(del / 2 * cellSupDist (enclosingCell b.1) cc)) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hk
        refine (sum_fineBonds_le h (fun z => Real.exp (-(del / 2 * cellSupDist z cc)))
          fun _ => (Real.exp_pos _).le).trans ?_
        have := sum_exp_cellSupDist_le h (half_pos h0) cc
        gcongr
theorem sum_bondsNearCell_abs_localAxialGauge_le (h : IsAdmissible F) (h0 : 0 < del) (h1 : del ≤ 1)
    (hK : 0 ≤ K)
    (hW : ∀ x i, |W x i| ≤ K * Real.exp (-(del * cellSupDist (enclosingCell x) cc))) (R : ℝ) (hR1 : 1 ≤ R)
    (hRL : 2 * R ≤ F.blockSide) (y : F.Site F.depth) (n : ℕ) (Y : F.Cell) (hn : n ≤ 2 * cellSupDist Y cc) :
    ∑ b ∈ bondsNearCell n Y, |localAxialGauge R y W b.1 b.2| ≤
      3 * Real.exp (-(del * n / 8)) *
        (12000 * R * K * (4 * ((F.blockSide : ℝ) ^ 4 * cellDecaySum (del / 2)))) := by
  have hk : 0 ≤ 12000 * R * K := by positivity
  set E8 := Real.exp (-(del * n / 8)) with hE8
  have hE0 : 0 < E8 := Real.exp_pos _
  calc _ ≤ ∑ b ∈ bondsNearCell n Y,
        3 * E8 * (12000 * R * K * Real.exp (-(del / 2 * cellSupDist (enclosingCell b.1) cc))) := by
        apply Finset.sum_le_sum
        intro b hb
        refine (abs_localAxialGauge_le W cc K del h h0 h1 hK hW R hR1 hRL y b.1 b.2).trans ?_
        have hc := (Finset.mem_filter.mp hb).2
        have ht : cellSupDist Y cc ≤ cellSupDist (enclosingCell b.1) Y + cellSupDist (enclosingCell b.1) cc := by
          have a := cellSupDist_triangle Y (enclosingCell b.1) cc
          have e := cellSupDist_comm Y (enclosingCell b.1)
          omega
        set db := cellSupDist (enclosingCell b.1) cc
        set dc := cellSupDist (enclosingCell b.1) Y
        have hreal : (n : ℝ) / 4 - 1 ≤ db := by
          have e1 : (4 : ℝ) * dc ≤ n + 4 := by exact_mod_cast hc.le
          have e2 : (n : ℝ) ≤ 2 * cellSupDist Y cc := by exact_mod_cast hn
          have e3 : (cellSupDist Y cc : ℝ) ≤ dc + db := by exact_mod_cast ht
          linarith
        have hsplit : Real.exp (-(del * db)) ≤ 3 * E8 * Real.exp (-(del / 2 * db)) := by
          have e1 : Real.exp (-(del / 2 * db)) ≤ Real.exp 1 * E8 := by
            rw [hE8, ← Real.exp_add, Real.exp_le_exp]
            nlinarith
          have e2 : Real.exp 1 ≤ 3 := by
            have := Real.exp_one_lt_d9
            linarith
          have e3 : Real.exp (-(del * db)) = Real.exp (-(del / 2 * db)) * Real.exp (-(del / 2 * db)) := by
            rw [← Real.exp_add]; ring_nf
          rw [e3]
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact e1.trans (mul_le_mul_of_nonneg_right e2 hE0.le)
        calc 12000 * R * K * Real.exp (-(del * db))
            ≤ 12000 * R * K * (3 * E8 * Real.exp (-(del / 2 * db))) :=
              mul_le_mul_of_nonneg_left hsplit hk
          _ = _ := by ring
    _ ≤ ∑ b ∈ fineBonds F,
        3 * E8 * (12000 * R * K * Real.exp (-(del / 2 * cellSupDist (enclosingCell b.1) cc))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro _ _ _
        positivity
    _ = 3 * E8 * (12000 * R * K *
        ∑ b ∈ fineBonds F, Real.exp (-(del / 2 * cellSupDist (enclosingCell b.1) cc))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hk
        refine (sum_fineBonds_le h (fun z => Real.exp (-(del / 2 * cellSupDist z cc)))
          fun _ => (Real.exp_pos _).le).trans ?_
        have := sum_exp_cellSupDist_le h (half_pos h0) cc
        gcongr
end ResponseBounds
theorem inv_decayWeight_anti (L : ℕ) (hL : 0 < L) {δ x x' : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hxx : x ≤ x') :
    (torusDecayFactor L δ x')⁻¹ ≤ (torusDecayFactor L δ x)⁻¹ :=
  inv_anti₀ (decayWeight_pos _ _ _) (decayWeight_monotone L hL hδ hx hxx)
theorem exists_slot_bondSpan_le {k : ℕ} (hk : 0 < k) (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) :
    ∃ l, bondSpan Y c ≤ 2 * cellSupDist Y (c l).1 := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin k)) Finset.univ_nonempty
    (fun l => siteSupDist Y (c l).1)
  refine ⟨l, ?_⟩
  have hm : ∀ l', siteSupDist Y (c l').1 ≤ siteSupDist Y (c l).1 := fun l' => by
    rw [← hl]
    exact Finset.le_sup (f := fun l => siteSupDist Y (c l).1) (Finset.mem_univ l')
  have e : cellSupDist Y (c l).1 = siteSupDist Y (c l).1 := rfl
  rw [e]
  unfold bondSpan
  apply max_le
  · rw [hl]
    omega
  · apply Finset.sup_le
    intro a _
    apply Finset.sup_le
    intro b _
    have t : cellSupDist (c a).1 (c b).1 ≤ cellSupDist (c a).1 Y + cellSupDist Y (c b).1 :=
      cellSupDist_triangle _ _ _
    have e1 : cellSupDist (c a).1 Y = cellSupDist Y (c a).1 := cellSupDist_comm _ _
    have e2 : cellSupDist (c a).1 (c b).1 = siteSupDist (c a).1 (c b).1 := rfl
    have e3 : ∀ l', cellSupDist Y (c l').1 = siteSupDist Y (c l').1 := fun _ => rfl
    have h1 := hm a
    have h2 := hm b
    rw [e1, e3, e3] at t
    omega
theorem bondSpan_le_sum {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) :
    bondSpan Y c ≤ ∑ l, cellSupDist Y (c l).1 := by
  classical
  have one : ∀ l, cellSupDist Y (c l).1 ≤ ∑ l, cellSupDist Y (c l).1 := fun l =>
    Finset.single_le_sum (f := fun l => cellSupDist Y (c l).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  unfold bondSpan
  apply max_le
  · apply Finset.sup_le
    intro a _
    exact one a
  · apply Finset.sup_le
    intro a _
    apply Finset.sup_le
    intro b _
    have t : cellSupDist (c a).1 (c b).1 ≤ cellSupDist (c a).1 Y + cellSupDist Y (c b).1 :=
      cellSupDist_triangle _ _ _
    have e1 : cellSupDist (c a).1 Y = cellSupDist Y (c a).1 := cellSupDist_comm _ _
    have e2 : siteSupDist (c a).1 (c b).1 = cellSupDist (c a).1 (c b).1 := rfl
    rw [e2]
    by_cases hab : a = b
    · subst hab
      have : cellSupDist (c a).1 (c a).1 = 0 := by simp [cellSupDist, ZMod.valMinAbs_zero]
      omega
    · have s1 := Finset.add_sum_erase Finset.univ (fun l => cellSupDist Y (c l).1) (Finset.mem_univ a)
      have s2 : cellSupDist Y (c b).1 ≤ ∑ l ∈ Finset.univ.erase a, cellSupDist Y (c l).1 :=
        Finset.single_le_sum (f := fun l => cellSupDist Y (c l).1) (fun _ _ => Nat.zero_le _)
          (Finset.mem_erase.mpr ⟨fun e => hab e.symm, Finset.mem_univ b⟩)
      omega
theorem siteSupDist_le_bondSpan {k : ℕ} (y : F.Site F.depth) (β : Fin k → F.Site F.depth × Fin 4) (l : Fin k) :
    siteSupDist y (β l).1 ≤ bondSpan y β :=
  (Finset.le_sup (f := fun l => siteSupDist y (β l).1) (Finset.mem_univ l)).trans (le_max_left _ _)
theorem sum_far_tuples_le (h : IsAdmissible F) {k : ℕ} (hk : 0 < k) (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    {δ del : ℝ} (hδ : 0 ≤ δ) (hdel : 0 < del) (hδd : δ ≤ del / 64)
    (hs : 1000000 / del ≤ weightScale F.blockSide) (hs2 : 2 ≤ weightScale F.blockSide) (y : F.Site F.depth)
    (hy : y ∈ blockFineSites Y)
    (A : ℕ) (hA : weightScale F.blockSide ^ 5 ≤ (A : ℝ) + 1) (U : Fin k → F.Site F.depth × Fin 4 → ℝ)
    (hU0 : ∀ l b, 0 ≤ U l b) (T : ℝ) (hT : 0 ≤ T) (hU : ∀ l, ∑ b ∈ fineBonds F, U l b ≤ T)
    (hC : ∀ l, bondSpan Y c ≤ 2 * cellSupDist Y (c l).1 →
      ∑ b ∈ bondsNearCell (bondSpan Y c) Y, U l b ≤
        3 * Real.exp (-(del * (bondSpan Y c : ℕ) / 8)) * T) (P : (Fin k → F.Site F.depth × Fin 4) → ℝ)
    (hP : ∀ β, P β = ∏ l, U l (β l)) :
    ∑ β ∈ (Fintype.piFinset fun _ : Fin k => fineBonds F).filter
        (fun β => ¬ ∀ l, β l ∈ nearbyBonds A y),
      (torusDecayFactor F.blockSide δ (bondSpan y β))⁻¹ * P β ≤
      4 * (weightScale F.blockSide ^ 64000)⁻¹ * T ^ k * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by
  classical
  have hLp := h.blockSide_pos
  set n := bondSpan Y c with hn
  obtain ⟨ls, hls⟩ := exists_slot_bondSpan_le hk Y c
  set ε := (weightScale F.blockSide ^ 64000)⁻¹ with hε
  set Gn := torusDecayFactor F.blockSide δ (n : ℝ) with hGn
  have hGn0 : 0 < Gn := decayWeight_pos _ _ _
  have hε0 : 0 ≤ ε := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hP0 : ∀ β, 0 ≤ P β := fun β => by
    rw [hP]; exact Finset.prod_nonneg fun l _ => hU0 l _
  have hcy : enclosingCell y = Y := enclosingCell_of_mem Y y hy
  have point : ∀ β ∈ (Fintype.piFinset fun _ : Fin k => fineBonds F).filter
      (fun β => ¬ ∀ l, β l ∈ nearbyBonds A y),
      (torusDecayFactor F.blockSide δ (bondSpan y β))⁻¹ * P β ≤
        ε * Gn⁻¹ * P β + ε * (if β ls ∈ bondsNearCell n Y then P β else 0) := by
    intro β hβ
    obtain ⟨hβ1, hβ2⟩ := Finset.mem_filter.mp hβ
    rw [Fintype.mem_piFinset] at hβ1
    push_neg at hβ2
    obtain ⟨l₀, hl₀⟩ := hβ2
    have hfar : A < siteSupDist (β l₀).1 y := by
      by_contra hc
      exact hl₀ (Finset.mem_filter.mpr ⟨hβ1 l₀, not_lt.mp hc⟩)
    set r : ℕ := Finset.univ.sup fun l => siteSupDist y (β l).1 with hr
    have hr1 : ∀ l, siteSupDist y (β l).1 ≤ r := fun l =>
      Finset.le_sup (f := fun l => siteSupDist y (β l).1) (Finset.mem_univ l)
    have hr2 : r ≤ bondSpan y β := le_max_left _ _
    have hrA : A + 1 ≤ r := by
      have := hr1 l₀
      rw [siteSupDist_comm] at this
      omega
    have hrν : weightScale F.blockSide ^ 5 ≤ (r : ℝ) := hA.trans (by exact_mod_cast hrA)
    have hGr : (torusDecayFactor F.blockSide δ (bondSpan y β))⁻¹ ≤ (torusDecayFactor F.blockSide δ r)⁻¹ :=
      inv_decayWeight_anti _ hLp hδ (Nat.cast_nonneg _) (by exact_mod_cast hr2)
    have hPb := hP0 β
    have hsec : 0 ≤ ε * (if β ls ∈ bondsNearCell n Y then P β else 0) := by
      apply mul_nonneg hε0
      split_ifs
      · exact hPb
      · exact le_rfl
    rcases Nat.lt_or_ge (4 * r) (F.blockSide * n) with hc | hc
    · have hcl : β ls ∈ bondsNearCell n Y := by
        refine Finset.mem_filter.mpr ⟨hβ1 ls, ?_⟩
        have a1 := blockSide_mul_cellSupDist_le h (β ls).1 y
        rw [hcy] at a1
        have a2 := hr1 ls
        rw [siteSupDist_comm] at a2
        have a3 : F.blockSide * (4 * cellSupDist (enclosingCell (β ls).1) Y) < F.blockSide * (n + 4) := by
          calc F.blockSide * (4 * cellSupDist (enclosingCell (β ls).1) Y) =
                4 * (F.blockSide * cellSupDist (enclosingCell (β ls).1) Y) := by ring
            _ ≤ 4 * (siteSupDist (β ls).1 y + F.blockSide) := Nat.mul_le_mul_left _ a1
            _ < F.blockSide * (n + 4) := by nlinarith
        exact Nat.lt_of_mul_lt_mul_left a3
      rw [if_pos hcl]
      have hfw := pow_le_decayWeight F.blockSide hLp hδ (by linarith) hrν
      have hinv : (torusDecayFactor F.blockSide δ r)⁻¹ ≤ ε := inv_anti₀ (by positivity) hfw
      have : (torusDecayFactor F.blockSide δ (bondSpan y β))⁻¹ * P β ≤ ε * P β :=
        mul_le_mul_of_nonneg_right (hGr.trans hinv) hPb
      have h3 : 0 ≤ ε * Gn⁻¹ * P β := by positivity
      linarith
    · have hxn : (F.blockSide : ℝ) * n ≤ 4 * r := by exact_mod_cast hc
      have hcw := pow_mul_decayWeight_le F.blockSide hLp hδ hs2 hn0 hrν hxn
      have hinv : (torusDecayFactor F.blockSide δ r)⁻¹ ≤ ε * Gn⁻¹ := by
        rw [hε, ← mul_inv]
        exact inv_anti₀ (by positivity) hcw
      have : (torusDecayFactor F.blockSide δ (bondSpan y β))⁻¹ * P β ≤ ε * Gn⁻¹ * P β :=
        mul_le_mul_of_nonneg_right (hGr.trans hinv) hPb
      linarith
  have hsum1 : ∑ β ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F), P β ≤ T ^ k := by
    calc ∑ β ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F), P β
        = ∏ l, ∑ b ∈ fineBonds F, U l b := by
          rw [Finset.prod_univ_sum]
          exact Finset.sum_congr rfl fun β _ => hP β
      _ ≤ ∏ _l : Fin k, T := Finset.prod_le_prod (fun l _ => Finset.sum_nonneg fun b _ => hU0 l b)
          fun l _ => hU l
      _ = T ^ k := by simp
  set E8 := Real.exp (-(del * (n : ℝ) / 8)) with hE8
  have hE0 : 0 < E8 := Real.exp_pos _
  have hsum2 : ∑ β ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
      (if β ls ∈ bondsNearCell n Y then P β else 0) ≤ 3 * E8 * T ^ k := by
    set t : Fin k → Finset (F.Site F.depth × Fin 4) := fun l =>
      if l = ls then bondsNearCell n Y else fineBonds F with ht
    have hfil : (Fintype.piFinset (fun _ : Fin k => fineBonds F)).filter
        (fun β => β ls ∈ bondsNearCell n Y) = Fintype.piFinset t := by
      ext β
      simp only [Finset.mem_filter, Fintype.mem_piFinset, ht]
      constructor
      · rintro ⟨a, b⟩ l
        by_cases hl : l = ls
        · subst hl; simpa using b
        · simpa [hl] using a l
      · intro a
        refine ⟨fun l => ?_, by simpa using a ls⟩
        by_cases hl : l = ls
        · subst hl
          have := a l
          simp only [if_true] at this
          exact (Finset.mem_filter.mp this).1
        · simpa [hl] using a l
    rw [← Finset.sum_filter, hfil]
    calc ∑ β ∈ Fintype.piFinset t, P β = ∏ l, ∑ b ∈ t l, U l b := by
          rw [Finset.prod_univ_sum]
          exact Finset.sum_congr rfl fun β _ => hP β
      _ ≤ ∏ l : Fin k, ((if l = ls then 3 * E8 else 1) * T) := by
          apply Finset.prod_le_prod (fun l _ => Finset.sum_nonneg fun b _ => hU0 l b)
          intro l _
          by_cases hl : l = ls
          · subst hl
            simp only [ht, if_true]
            exact hC l hls
          · simp only [ht, hl, if_false, one_mul]
            exact hU l
      _ = 3 * E8 * T ^ k := by
          rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ ls (fun _ => 3 * E8)]
          simp
  have hE8G : E8 ≤ Gn⁻¹ := by
    have := decayWeight_mul_exp_le_one F.blockSide hLp hδ hdel hδd hs hn0
    rw [← hGn, ← hE8] at this
    rw [le_inv_comm₀ hE0 hGn0]
    rw [inv_eq_one_div, le_div_iff₀ hE0]
    linarith
  calc _ ≤ ∑ β ∈ (Fintype.piFinset fun _ : Fin k => fineBonds F).filter
        (fun β => ¬ ∀ l, β l ∈ nearbyBonds A y),
        (ε * Gn⁻¹ * P β + ε * (if β ls ∈ bondsNearCell n Y then P β else 0)) := Finset.sum_le_sum point
    _ ≤ ∑ β ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
        (ε * Gn⁻¹ * P β + ε * (if β ls ∈ bondsNearCell n Y then P β else 0)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro β _ _
        have := hP0 β
        have h2 : 0 ≤ (if β ls ∈ bondsNearCell n Y then P β else 0) := by split_ifs <;> simp [this]
        positivity
    _ = ε * Gn⁻¹ * ∑ β ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F), P β +
        ε * ∑ β ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
          (if β ls ∈ bondsNearCell n Y then P β else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ε * Gn⁻¹ * T ^ k + ε * (3 * Gn⁻¹ * T ^ k) := by
        have h1 : ε * Gn⁻¹ * ∑ β ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F), P β ≤
            ε * Gn⁻¹ * T ^ k :=
          mul_le_mul_of_nonneg_left hsum1 (by positivity)
        have h2 : 3 * E8 * T ^ k ≤ 3 * Gn⁻¹ * T ^ k := by gcongr
        have h3 := mul_le_mul_of_nonneg_left (hsum2.trans h2) hε0
        linarith
    _ = _ := by ring
theorem plaquetteCurl_antisymm (W : LevelForm F F.depth) (x : F.Site F.depth) (μ ν : Fin 4) :
    plaquetteCurl W x μ ν = - plaquetteCurl W x ν μ := by
  unfold plaquetteCurl; ring
def curlSquareNear (W : LevelForm F F.depth) (Y : F.Cell) : ℝ :=
  ∑ p ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun p => cellSupDist (enclosingCell p) Y ≤ 2),
    ∑ e ∈ orientedPlanes, plaquetteCurl W p e.1 e.2 ^ 2
theorem curlSquareNear_nonneg (W : LevelForm F F.depth) (Y : F.Cell) : 0 ≤ curlSquareNear W Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem mem_orientedPlanes {i k : Fin 4} (h : i < k) : (i, k) ∈ orientedPlanes := by
  simp [orientedPlanes, h]
theorem enclosingCell_near (h : IsAdmissible F) (Y : F.Cell) (y : F.Site F.depth) (hy : y ∈ blockFineSites Y)
    (A : ℕ) (hA : A ≤ F.blockSide) (v : Fin 4 → ℤ) (hv : ∀ l, |v l| ≤ (A : ℤ)) :
    cellSupDist (enclosingCell (y + siteOfCoords F.depth v)) Y ≤ 2 := by
  have := cellSupDist_le_two h (y + siteOfCoords F.depth v) y
    ((siteSupDist_add_siteOfCoords_le h y v A hv).trans hA)
  rwa [enclosingCell_of_mem Y y hy] at this
theorem sum_stripTotal_curl_sq_le (h : IsAdmissible F) (W : LevelForm F F.depth) (Y : F.Cell) (A : ℕ)
    (hA : A ≤ F.blockSide) :
    ∑ y ∈ blockFineSites Y, stripTotal A (curlMagnitudes W y) ^ 2 ≤
      ((stripIndices A).card : ℝ) ^ 2 * curlSquareNear W Y := by
  classical
  apply sum_stripTotal_sq_le (blockFineSites Y) A (fun y => curlMagnitudes W y) _ (curlSquareNear_nonneg W Y)
  intro v i k hik hv
  have hinj : Set.InjOn (fun y : F.Site F.depth => y + siteOfCoords F.depth v) (blockFineSites Y) :=
    fun a _ b _ e => add_right_cancel e
  calc ∑ y ∈ blockFineSites Y, curlMagnitudes W y v i k ^ 2
      ≤ ∑ y ∈ blockFineSites Y, ∑ e ∈ orientedPlanes,
          plaquetteCurl W (y + siteOfCoords F.depth v) e.1 e.2 ^ 2 := by
        apply Finset.sum_le_sum
        intro y _
        have e1 : curlMagnitudes W y v i k ^ 2 = plaquetteCurl W (y + siteOfCoords F.depth v) i k ^ 2 := by
          simp only [curlMagnitudes, sq_abs]
          rw [plaquetteCurl_antisymm]; ring
        rw [e1]
        exact Finset.single_le_sum
          (f := fun e : Fin 4 × Fin 4 => plaquetteCurl W (y + siteOfCoords F.depth v) e.1 e.2 ^ 2)
          (fun _ _ => sq_nonneg _) (mem_orientedPlanes hik)
    _ = ∑ p ∈ (blockFineSites Y).image (fun y => y + siteOfCoords F.depth v), ∑ e ∈ orientedPlanes,
          plaquetteCurl W p e.1 e.2 ^ 2 := by
        rw [Finset.sum_image hinj]
    _ ≤ curlSquareNear W Y := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
          exact Finset.mem_filter.mpr ⟨mem_sitesOfCells h _, enclosingCell_near h Y y hy A hA v hv⟩
        · intro _ _ _
          exact Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem stripTotal_curl_le (h : IsAdmissible F) (W : LevelForm F F.depth) (Y : F.Cell) (A : ℕ)
    (hA : A ≤ F.blockSide) (D : ℝ) (hD : 0 ≤ D)
    (hs : ∀ p, ∀ e ∈ orientedPlanes, cellSupDist (enclosingCell p) Y ≤ 2 → |plaquetteCurl W p e.1 e.2| ≤ D)
    (y : F.Site F.depth) (hy : y ∈ blockFineSites Y) :
    stripTotal A (curlMagnitudes W y) ≤ ((stripIndices A).card : ℝ) * D := by
  apply stripTotal_le_of_bound A _ D hD
  intro v i k hik hv
  simp only [curlMagnitudes]
  rw [plaquetteCurl_antisymm, abs_neg]
  exact hs _ _ (mem_orientedPlanes hik) (enclosingCell_near h Y y hy A hA v hv)
theorem stripTotal_curl_nonneg (A : ℕ) (W : LevelForm F F.depth) (y : F.Site F.depth) :
    0 ≤ stripTotal A (curlMagnitudes W y) := by
  unfold stripTotal
  refine Finset.sum_nonneg fun o _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs
  · exact Finset.sum_nonneg fun s _ => abs_nonneg _
  · exact le_rfl
theorem sum_prod_le_of_two_square_means {J : Type} (S : Finset J) {k : ℕ} (hk : 3 ≤ k) (s : Fin k → J → ℝ)
    (hs : ∀ l y, 0 ≤ s l y) (g : Fin k → ℝ) (hg : ∀ l, 0 ≤ g l) (m τ : ℝ) (hm : 0 ≤ m) (hτ : 0 ≤ τ)
    (hτ1 : τ ≤ 1)
    (h2 : ∀ l, ∑ y ∈ S, s l y ^ 2 ≤ m ^ 2 * g l ^ 2) (hsup : ∀ l, ∀ y ∈ S, s l y ≤ τ * g l) :
    ∑ y ∈ S, ∏ l, s l y ≤ m ^ 2 * τ * ∏ l, g l := by
  classical
  let l0 : Fin k := ⟨0, by omega⟩
  let l1 : Fin k := ⟨1, by omega⟩
  let l2 : Fin k := ⟨2, by omega⟩
  have h01 : l1 ≠ l0 := by simp [l0, l1, Fin.ext_iff]
  have h21 : l2 ≠ l1 := by simp [l2, l1, Fin.ext_iff]
  have h20 : l2 ≠ l0 := by simp [l2, l0, Fin.ext_iff]
  set rest := (Finset.univ.erase l0).erase l1 with hrest
  have hl2 : l2 ∈ rest := by simp [hrest, h21, h20]
  have split : ∀ f : Fin k → ℝ, ∏ l, f l = f l0 * (f l1 * ∏ l ∈ rest, f l) := by
    intro f
    rw [hrest, Finset.mul_prod_erase _ f (by simp [h01]), Finset.mul_prod_erase _ f (Finset.mem_univ _)]
  have hrestcard : 1 ≤ rest.card := Finset.card_pos.mpr ⟨l2, hl2⟩
  have hgrest : 0 ≤ ∏ l ∈ rest, g l := Finset.prod_nonneg fun l _ => hg l
  have hpoint : ∀ y ∈ S, ∏ l, s l y ≤ s l0 y * s l1 y * (τ * ∏ l ∈ rest, g l) := by
    intro y hy
    rw [split fun l => s l y, ← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hs _ _) (hs _ _))
    calc ∏ l ∈ rest, s l y ≤ ∏ l ∈ rest, (τ * g l) :=
          Finset.prod_le_prod (fun l _ => hs l y) fun l _ => hsup l y hy
      _ = τ ^ rest.card * ∏ l ∈ rest, g l := by rw [Finset.prod_mul_distrib]; simp
      _ ≤ τ * ∏ l ∈ rest, g l := by
          apply mul_le_mul_of_nonneg_right _ hgrest
          calc τ ^ rest.card ≤ τ ^ 1 := pow_le_pow_of_le_one hτ hτ1 hrestcard
            _ = τ := pow_one τ
  have hcs : ∑ y ∈ S, s l0 y * s l1 y ≤ (m * g l0) * (m * g l1) := by
    refine (Real.sum_mul_le_sqrt_mul_sqrt S _ _).trans ?_
    have a : ∀ l, Real.sqrt (∑ y ∈ S, s l y ^ 2) ≤ m * g l := by
      intro l
      apply Real.sqrt_le_iff.mpr
      exact ⟨mul_nonneg hm (hg l), by rw [mul_pow]; exact h2 l⟩
    exact mul_le_mul (a l0) (a l1) (Real.sqrt_nonneg _) (mul_nonneg hm (hg _))
  calc ∑ y ∈ S, ∏ l, s l y ≤ ∑ y ∈ S, s l0 y * s l1 y * (τ * ∏ l ∈ rest, g l) := Finset.sum_le_sum hpoint
    _ = (∑ y ∈ S, s l0 y * s l1 y) * (τ * ∏ l ∈ rest, g l) := by rw [Finset.sum_mul]
    _ ≤ ((m * g l0) * (m * g l1)) * (τ * ∏ l ∈ rest, g l) :=
        mul_le_mul_of_nonneg_right hcs (mul_nonneg hτ hgrest)
    _ = m ^ 2 * τ * ∏ l, g l := by
        rw [split g]; ring
theorem sum_piFinset_nearbyBonds_prod (A : ℕ) {k : ℕ} (y : F.Site F.depth)
    (U : Fin k → F.Site F.depth × Fin 4 → ℝ) :
    ∑ β ∈ Fintype.piFinset (fun _ : Fin k => nearbyBonds A y), ∏ l, U l (β l) =
      ∏ l, ∑ b ∈ nearbyBonds A y, U l b := by
  rw [Finset.prod_univ_sum]
theorem isAdmissible_of (h1 : Odd F.blockSide) (h2 : IsLargeCubicTorus F) : IsAdmissible F := by
  obtain ⟨n, hn, hs⟩ := h2
  exact ⟨h1, fun i => by rw [hs i]; exact hn⟩
theorem sqrt_blockSide_eq (L : ℕ) (hν : 0 < weightScale L) : Real.sqrt (L : ℝ) = weightScale L ^ 320 := by
  rw [← weightScale_pow L]
  have : weightScale L ^ 640 = (weightScale L ^ 320) ^ 2 := by rw [← pow_mul]
  rw [this, Real.sqrt_sq (pow_nonneg hν.le _)]
theorem blockSide_rpow_neg_half (L : ℕ) (hν : 0 < weightScale L) :
    (L : ℝ) ^ (-(1 / 2 : ℝ)) = (weightScale L ^ 320)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, sqrt_blockSide_eq L hν]
theorem blockSide_rpow_neg_quarter (L : ℕ) (hν : 0 < weightScale L) :
    (L : ℝ) ^ (-(1 / 4 : ℝ)) = (weightScale L ^ 160)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  congr 1
  rw [← weightScale_pow L, ← Real.rpow_natCast (weightScale L) 640, ← Real.rpow_mul hν.le,
    ← Real.rpow_natCast (weightScale L) 160]
  norm_num
structure FlatConstants (a del CS CE C6 C2 C9 : ℝ) (L₁ : ℕ) : Prop where
  coupling_pos : 0 < a
  rate_pos : 0 < del
  rate_le_one : del ≤ 1
  one_le_sizeConst : 1 ≤ CS
  one_le_energyConst : 1 ≤ CE
  one_le_curlConst : 1 ≤ C6
  one_le_squareConst : 1 ≤ C2
  one_le_shiftConst : 1 ≤ C9
  response_bound : ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F) (W : LevelForm F F.depth),
    Odd F.blockSide → L₁ ≤ F.blockSide →
    IsLargeCubicTorus F → IsFlatChain a c B → IsAxialResponse c B W → ∀ x i,
      |W x i| ≤ CS * (F.blockSide : ℝ) ^ 3 * Real.exp (-(del * cellSupDist (enclosingCell x) c.1))
  energy_bound : ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F), Odd F.blockSide →
    L₁ ≤ F.blockSide →
    IsLargeCubicTorus F → IsFlatChain a c B → ∀ z : F.Cell,
      chainEnergyOnCells a B (cellBall z 24) ≤ CE * Real.exp (-(2 * del * cellSupDist z c.1))
  curl_bound : ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F), Odd F.blockSide →
    L₁ ≤ F.blockSide →
    IsLargeCubicTorus F → IsFlatChain a c B → ∀ (Y : F.Cell) (p : F.Site F.depth) (e : Fin 4 × Fin 4),
      e ∈ orientedPlanes →
      cellSupDist (enclosingCell p) Y ≤ 2 →
      |plaquetteCurl (B F.depth) p e.1 e.2| ≤
        C6 * (F.blockSide : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (chainEnergyOnCells a B (cellBall Y 24))
  square_bound : ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F), Odd F.blockSide →
    L₁ ≤ F.blockSide →
    IsLargeCubicTorus F → IsFlatChain a c B → ∀ Y : F.Cell,
      curlSquareNear (B F.depth) Y ≤ C2 * chainEnergyOnCells a B (cellBall Y 24)
  shift_bound : ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F), Odd F.blockSide →
    L₁ ≤ F.blockSide →
    IsLargeCubicTorus F → IsFlatChain a c B → ∀ (z : F.Site F.depth) (h : Fin 4 → ℤ) (n : ℕ),
      (∀ i, |h i| ≤ n) → (∃ i, |h i| = n) → 1 ≤ n → n ≤ F.blockSide →
      ∑ p ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun p => siteSupDist p z ≤ F.blockSide),
        ∑ e ∈ orientedPlanes,
        (plaquetteCurl (B F.depth) (p + siteOfCoords F.depth h) e.1 e.2 - plaquetteCurl (B F.depth) p e.1 e.2) ^ 2 ≤
      C9 * ((n : ℝ) / F.blockSide) * chainEnergyOnSites a B (depthBall z (9 * F.blockSide))
theorem exists_flatConstants (hS : axialResponseDecay) (hE : flatChainEnergyNearCell)
    (h9 : CurlShiftBound) (h6 : CurlSizeBound) (h2 : CurlSquareSumBound) (a : ℝ) (ha : 1 ≤ a) :
    ∃ (del CS CE C6 C2 C9 : ℝ) (L₁ : ℕ), FlatConstants a del CS CE C6 C2 C9 L₁ := by
  obtain ⟨dS, CS, dS0, dS1, CS0, LS, hS⟩ := hS a ha
  obtain ⟨dE, CE, dE0, dE1, CE0, LE, hE⟩ := hE a ha
  obtain ⟨C9, C90, L9, h9⟩ := h9 a ha
  obtain ⟨C6, C60, L6, h6⟩ := h6 a ha
  obtain ⟨C2, C20, L2, h2⟩ := h2 a ha
  have en0 : ∀ (F : BlockFrame) (B : FormChain F) (X : Set (F.Site F.depth)), 0 ≤ chainEnergyOnSites a B X := by
    intro F B X
    unfold chainEnergyOnSites
    have : 0 ≤ a := by linarith
    refine add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) ?_
    exact mul_nonneg this (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have ec0 : ∀ (F : BlockFrame) (B : FormChain F) (X : Set F.Cell), 0 ≤ chainEnergyOnCells a B X := by
    intro F B X
    unfold chainEnergyOnCells
    have : 0 ≤ a := by linarith
    refine add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) ?_
    exact mul_nonneg this (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)
  refine ⟨min dS dE, max 1 CS, max 1 CE, max 1 C6, max 1 C2, max 1 C9, max (max LS LE) (max L9 (max L6 L2)),
    ⟨by linarith, lt_min dS0 dE0, (min_le_left _ _).trans dS1, le_max_left _ _, le_max_left _ _,
      le_max_left _ _, le_max_left _ _, le_max_left _ _, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro F c B W hL hL₁ hc hf ht x i
    have hg := isAdmissible_of hL hc
    have hLS : LS ≤ F.blockSide := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL₁
    have hpos : 0 ≤ max 1 CS * (F.blockSide : ℝ) ^ 3 := by positivity
    have hd : (0 : ℝ) ≤ cellSupDist (enclosingCell x) c.1 := Nat.cast_nonneg _
    rcases mem_chordBonds_or_isAxialTreeBond hg (x, i) with hb | hb
    · refine (hS F c B W hL hLS hc hf ht (x, i) hb).trans ?_
      have h1 : CS * (F.blockSide : ℝ) ^ 3 ≤ max 1 CS * (F.blockSide : ℝ) ^ 3 := by
        gcongr
        exact le_max_right _ _
      apply mul_le_mul h1 _ (Real.exp_pos _).le hpos
      rw [Real.exp_le_exp]
      have := min_le_left dS dE
      nlinarith
    · rw [ht.vanishes_on_tree (x, i) hb, abs_zero]
      positivity
  · intro F c B hL hL₁ hc hf z
    have hLE : LE ≤ F.blockSide := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL₁
    refine (hE F c B hL hLE hc hf z 24 le_rfl).trans ?_
    apply mul_le_mul (le_max_right _ _) _ (Real.exp_pos _).le (by positivity)
    rw [Real.exp_le_exp]
    have := min_le_right dS dE
    have hd : (0 : ℝ) ≤ cellSupDist z c.1 := Nat.cast_nonneg _
    nlinarith
  · intro F c B hL hL₁ hc hf Y p e he hp
    have hL6 : L6 ≤ F.blockSide :=
      le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right L9 _)) (le_max_right _ _)) hL₁
    refine (h6 F c B hL hL6 hc hf Y p e he hp).trans ?_
    gcongr
    exact le_max_right _ _
  · intro F c B hL hL₁ hc hf Y
    have hL2 : L2 ≤ F.blockSide :=
      le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right L9 _)) (le_max_right _ _)) hL₁
    refine (h2 F c B hL hL2 hc hf Y).trans ?_
    apply mul_le_mul_of_nonneg_right (le_max_right _ _) (ec0 F B _)
  · intro F c B hL hL₁ hc hf z h n h1 h3 h4 h5
    have hL9 : L9 ≤ F.blockSide := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL₁
    refine (h9 F c B hL hL9 hc hf z h n h1 h3 h4 h5).trans ?_
    apply mul_le_mul_of_nonneg_right _ (en0 F B _)
    gcongr
    exact le_max_right _ _
theorem weightScale_facts (L : ℕ) (hs : 2 ≤ weightScale L) :
    weightScale L ^ 5 ≤ (⌈weightScale L ^ 5⌉₊ : ℝ) + 1 ∧ ((⌈weightScale L ^ 5⌉₊ : ℝ) + 1 ≤ Real.sqrt L) ∧
      2 * (⌈weightScale L ^ 5⌉₊ + 1) < 64 * L ∧ ⌈weightScale L ^ 5⌉₊ ≤ L ∧
      (((stripIndices ⌈weightScale L ^ 5⌉₊).card : ℕ) : ℝ) ≤ 20000 * weightScale L ^ 25 ∧ 1 ≤ Real.sqrt L ∧
      2 * Real.sqrt L ≤ L := by
  have hν0 : 0 < weightScale L := by linarith
  rw [sqrt_blockSide_eq L hν0]
  have hp : (L : ℝ) = weightScale L ^ 640 := (weightScale_pow L).symm
  set ν := weightScale L
  set A := ⌈ν ^ 5⌉₊ with hAdef
  have hν1 : 1 ≤ ν := by linarith
  have h5 : 32 ≤ ν ^ 5 := by
    have : (2 : ℝ) ^ 5 ≤ ν ^ 5 := pow_le_pow_left₀ (by norm_num) hs 5
    linarith
  have hA1 : ν ^ 5 ≤ A := Nat.le_ceil _
  have hA2 : (A : ℝ) < ν ^ 5 + 1 := Nat.ceil_lt_add_one (by positivity)
  have h6 : 2 * ν ^ 5 ≤ ν ^ 6 := by
    have : ν ^ 6 = ν * ν ^ 5 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hs (by positivity)
  have h320 : ν ^ 6 ≤ ν ^ 320 := pow_le_pow_right₀ hν1 (by norm_num)
  have hAR : (A : ℝ) + 1 ≤ ν ^ 320 := by linarith
  have h2R : 2 ≤ ν ^ 320 := by linarith
  have hRL : 2 * ν ^ 320 ≤ (L : ℝ) := by
    rw [hp]
    have : ν ^ 640 = ν ^ 320 * ν ^ 320 := by rw [← pow_add]
    rw [this]
    exact mul_le_mul_of_nonneg_right h2R (pow_nonneg hν0.le _)
  have hLpos : (0 : ℝ) < L := by rw [hp]; exact pow_pos hν0 _
  refine ⟨by linarith, hAR, ?_, ?_, ?_, by linarith, hRL⟩
  · have : (2 : ℝ) * ((A : ℝ) + 1) < 64 * L := by linarith
    exact_mod_cast this
  · have : (A : ℝ) ≤ L := by linarith
    exact_mod_cast this
  · rw [card_stripIndices]
    push_cast
    have b1 : 2 * (A : ℝ) + 1 ≤ 5 * ν ^ 5 := by linarith
    have b2 : (A : ℝ) ≤ 2 * ν ^ 5 := by linarith
    calc (2 * (A : ℝ) + 1) ^ 4 * (4 * (4 * A)) ≤ (5 * ν ^ 5) ^ 4 * (4 * (4 * (2 * ν ^ 5))) := by
          gcongr
      _ = 20000 * ν ^ 25 := by ring
theorem near_powers_le (ν X : ℝ) (hν : 2 ≤ ν) (hX : 0 ≤ X) (h16 : 16000000000000 * X ≤ ν) :
    8000000000000 * ν ^ 75 * X * (ν ^ 320)⁻¹ ≤ 1 / 2 * (ν ^ 160)⁻¹ := by
  have hν0 : 0 < ν := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have e : ν ^ 320 = ν ^ 75 * (ν ^ 84 * ν) * ν ^ 160 := by ring
  have h84 : ν ≤ ν ^ 84 * ν := le_mul_of_one_le_left hν0.le (one_le_pow₀ hν1)
  rw [e]
  field_simp
  nlinarith
theorem far_powers_le (ν : ℝ) (hν : 2 ≤ ν) :
    ν ^ 2560 * (4 * (ν ^ 64000)⁻¹ * ν ^ 38400) ≤ 1 / 2 * (ν ^ 160)⁻¹ := by
  have hν0 : 0 < ν := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have e : ν ^ 64000 = ν ^ 2560 * ν ^ 38400 * ν ^ 22880 * ν ^ 160 := by
    rw [← pow_add, ← pow_add, ← pow_add]
  have h8 : 8 ≤ ν ^ 22880 := by
    have a : (2 : ℝ) ^ 3 ≤ ν ^ 3 := pow_le_pow_left₀ (by norm_num) hν 3
    have b : ν ^ 3 ≤ ν ^ 22880 := pow_le_pow_right₀ hν1 (by norm_num)
    linarith
  have p3 := pow_pos hν0 22880
  have p4 := pow_pos hν0 160
  rw [e]
  have : ν ^ 2560 * (4 * (ν ^ 2560 * ν ^ 38400 * ν ^ 22880 * ν ^ 160)⁻¹ * ν ^ 38400) =
      4 * (ν ^ 22880)⁻¹ * (ν ^ 160)⁻¹ := by
    field_simp
  rw [this]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr p4.le)
  rw [mul_inv_le_iff₀ p3]
  linarith
def scaleThreshold (del CS CE C6 C2 : ℝ) : ℝ :=
  max 2 (max (1000000 / del) (max (48000 * CS * cellDecaySum (del / 2))
    (16000000000000 * (C2 ^ 2 * C6 * CE ^ 6))))
theorem chainEnergyOnCells_nonneg {a : ℝ} (ha : 0 < a) (B : FormChain F) (X : Set F.Cell) :
    0 ≤ chainEnergyOnCells a B X := by
  unfold chainEnergyOnCells
  refine add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) ?_
  exact mul_nonneg ha.le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)
theorem curlSquareNear_of_isAxialResponse {a : ℝ} (c : F.Site F.top × Fin 4) (B : FormChain F)
    (W : LevelForm F F.depth)
    (ht : IsAxialResponse c B W) (Y : F.Cell) : curlSquareNear W Y = curlSquareNear (B F.depth) Y := by
  unfold curlSquareNear
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e he => ?_
  rw [ht.curl_eq p e he]
theorem sqrt_chainEnergyOnCells_le {a del CE : ℝ} (ha : 0 < a) (hCE : 1 ≤ CE) (B : FormChain F) (Y : F.Cell)
    (d : ℝ)
    (h : chainEnergyOnCells a B (cellBall Y 24) ≤ CE * Real.exp (-(2 * del * d))) :
    Real.sqrt (chainEnergyOnCells a B (cellBall Y 24)) ≤ CE * Real.exp (-(del * d)) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, h.trans ?_⟩
  have e : Real.exp (-(2 * del * d)) = Real.exp (-(del * d)) ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [e, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith
theorem stripTotal_bounds {a del CS CE C6 C2 C9 : ℝ} {L₁ : ℕ} (hN : FlatConstants a del CS CE C6 C2 C9 L₁)
    (F : BlockFrame) (Y : F.Cell) (c : F.Site F.top × Fin 4) (B : FormChain F) (W : LevelForm F F.depth)
    (hodd : Odd F.blockSide) (hL₁ : L₁ ≤ F.blockSide) (hcub : IsLargeCubicTorus F) (hf : IsFlatChain a c B)
    (ht : IsAxialResponse c B W) (A : ℕ) (hAL : A ≤ F.blockSide) (hν0 : 0 < weightScale F.blockSide) :
    ∑ y ∈ blockFineSites Y, stripTotal A (curlMagnitudes W y) ^ 2 ≤
        (((stripIndices A).card : ℝ) * C2) ^ 2 * Real.sqrt (chainEnergyOnCells a B (cellBall Y 24)) ^ 2 ∧
      ∀ y ∈ blockFineSites Y, stripTotal A (curlMagnitudes W y) ≤
        (((stripIndices A).card : ℝ) * (C6 * (weightScale F.blockSide ^ 320)⁻¹)) *
          Real.sqrt (chainEnergyOnCells a B (cellBall Y 24)) := by
  have hg := isAdmissible_of hodd hcub
  have he0 : 0 ≤ chainEnergyOnCells a B (cellBall Y 24) := chainEnergyOnCells_nonneg hN.coupling_pos _ _
  have hC2 := hN.one_le_squareConst
  have hC6 := hN.one_le_curlConst
  constructor
  · refine (sum_stripTotal_curl_sq_le hg W Y A hAL).trans ?_
    rw [curlSquareNear_of_isAxialResponse (a := a) c B W ht Y, Real.sq_sqrt he0, mul_pow, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have a1 := hN.square_bound F c B hodd hL₁ hcub hf Y
    have a2 : C2 ≤ C2 ^ 2 := by nlinarith
    exact a1.trans (mul_le_mul_of_nonneg_right a2 he0)
  · intro y hy
    have := stripTotal_curl_le hg W Y A hAL
      (C6 * (weightScale F.blockSide ^ 320)⁻¹ * Real.sqrt (chainEnergyOnCells a B (cellBall Y 24)))
      (by positivity) (by
        intro q ε' hε' hq
        rw [ht.curl_eq q ε' hε']
        have := hN.curl_bound F c B hodd hL₁ hcub hf Y q ε' hε' hq
        rwa [blockSide_rpow_neg_half F.blockSide hν0] at this) y hy
    rw [mul_assoc]
    exact this
theorem prod_sqrt_energy_le {a del CS CE C6 C2 C9 : ℝ} {L₁ : ℕ} (hN : FlatConstants a del CS CE C6 C2 C9 L₁)
    (F : BlockFrame) (δ : ℝ) (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (B : Fin k → FormChain F)
    (hk6 : k ≤ 6) (hodd : Odd F.blockSide) (hL₁ : L₁ ≤ F.blockSide) (hcub : IsLargeCubicTorus F) (hδ : 0 ≤ δ)
    (hδd : δ ≤ del / 64)
    (hf : ∀ i, IsFlatChain a (c i) (B i)) (hsd : 1000000 / del ≤ weightScale F.blockSide) :
    ∏ l, Real.sqrt (chainEnergyOnCells a (B l) (cellBall Y 24)) ≤
      CE ^ 6 * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by
  have hCE := hN.one_le_energyConst
  have hdel := hN.rate_pos
  have hLp := (isAdmissible_of hodd hcub).blockSide_pos
  have hGn0 : 0 < torusDecayFactor F.blockSide δ (bondSpan Y c) := decayWeight_pos _ _ _
  have h1 : ∀ l ∈ (Finset.univ : Finset (Fin k)), Real.sqrt (chainEnergyOnCells a (B l) (cellBall Y 24)) ≤
      CE * Real.exp (-(del * cellSupDist Y (c l).1)) := by
    intro l _
    exact sqrt_chainEnergyOnCells_le hN.coupling_pos hCE (B l) Y _
      (hN.energy_bound F (c l) (B l) hodd hL₁ hcub (hf l) Y)
  calc ∏ l, Real.sqrt (chainEnergyOnCells a (B l) (cellBall Y 24))
      ≤ ∏ l, (CE * Real.exp (-(del * cellSupDist Y (c l).1))) :=
        Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) h1
    _ = CE ^ k * Real.exp (-(del * ∑ l, (cellSupDist Y (c l).1 : ℝ))) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
        simp
    _ ≤ CE ^ 6 * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by
        have b1 : CE ^ k ≤ CE ^ 6 := pow_le_pow_right₀ hCE hk6
        have b2 : ((bondSpan Y c : ℕ) : ℝ) ≤ ∑ l, (cellSupDist Y (c l).1 : ℝ) := by
          have := bondSpan_le_sum Y c
          exact_mod_cast this
        have hn0 : (0 : ℝ) ≤ (bondSpan Y c : ℕ) := Nat.cast_nonneg _
        have b3 : Real.exp (-(del * ∑ l, (cellSupDist Y (c l).1 : ℝ))) ≤
            Real.exp (-(del * ((bondSpan Y c : ℕ) : ℝ) / 8)) := by
          rw [Real.exp_le_exp]
          nlinarith
        have b4 : Real.exp (-(del * ((bondSpan Y c : ℕ) : ℝ) / 8)) ≤
            (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by
          have := decayWeight_mul_exp_le_one F.blockSide hLp hδ hdel hδd hsd hn0
          have hE0 := Real.exp_pos (-(del * ((bondSpan Y c : ℕ) : ℝ) / 8))
          rw [le_inv_comm₀ hE0 hGn0, inv_eq_one_div, le_div_iff₀ hE0]
          exact this
        exact mul_le_mul b1 (b3.trans b4) (Real.exp_pos _).le (by positivity)
theorem slot_constant_le (L : ℕ) (CS cs : ℝ) (hs2 : 2 ≤ weightScale L) (hsT : 48000 * CS * cs ≤ weightScale L)
    (hCS : 0 ≤ CS) (hcs : 0 ≤ cs) :
    12000 * Real.sqrt L * (CS * (L : ℝ) ^ 3) * (4 * ((L : ℝ) ^ 4 * cs)) ≤ weightScale L ^ 6400 := by
  have hν0 : 0 < weightScale L := by linarith
  have hν1 : 1 ≤ weightScale L := by linarith
  rw [sqrt_blockSide_eq L hν0]
  have hLν : (L : ℝ) = weightScale L ^ 640 := (weightScale_pow L).symm
  rw [hLν]
  generalize weightScale L = ν at *
  have e : 12000 * ν ^ 320 * (CS * (ν ^ 640) ^ 3) * (4 * ((ν ^ 640) ^ 4 * cs)) =
      (48000 * CS * cs) * ν ^ 4800 := by ring
  rw [e]
  calc _ ≤ ν * ν ^ 4800 := mul_le_mul_of_nonneg_right hsT (pow_nonneg hν0.le _)
    _ = ν ^ 4801 := by ring
    _ ≤ ν ^ 6400 := pow_le_pow_right₀ hν1 (by norm_num)
theorem scaleThreshold_facts {del CS CE C6 C2 ν : ℝ} (hfl : scaleThreshold del CS CE C6 C2 ≤ ν) :
    2 ≤ ν ∧ 1000000 / del ≤ ν ∧ 48000 * CS * cellDecaySum (del / 2) ≤ ν ∧
      16000000000000 * (C2 ^ 2 * C6 * CE ^ 6) ≤ ν :=
  ⟨(le_max_left _ _).trans hfl, ((le_max_left _ _).trans (le_max_right _ _)).trans hfl,
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hfl,
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hfl⟩
theorem sum_tuples_at_site_le {a del CS CE C6 C2 C9 : ℝ} {L₁ : ℕ} (hN : FlatConstants a del CS CE C6 C2 C9 L₁)
    (F : BlockFrame) (δ : ℝ) (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (B : Fin k → FormChain F)
    (W : Fin k → LevelForm F F.depth) (hk : 0 < k) (hodd : Odd F.blockSide) (hL₁ : L₁ ≤ F.blockSide)
    (hcub : IsLargeCubicTorus F) (hδ : 0 ≤ δ) (hδd : δ ≤ del / 64) (hf : ∀ i, IsFlatChain a (c i) (B i))
    (ht : ∀ i, IsAxialResponse (c i) (B i) (W i))
    (hfl : scaleThreshold del CS CE C6 C2 ≤ weightScale F.blockSide)
    (A : ℕ) (hA1 : weightScale F.blockSide ^ 5 ≤ (A : ℝ) + 1) (hAR : (A : ℝ) + 1 ≤ Real.sqrt F.blockSide)
    (hA64 : 2 * (A + 1) < 64 * F.blockSide) (hR1 : 1 ≤ Real.sqrt F.blockSide)
    (hRL : 2 * Real.sqrt F.blockSide ≤ F.blockSide)
    (y : F.Site F.depth) (hy : y ∈ blockFineSites Y) :
    ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
      (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹ *
        ∏ i, |localAxialGauge (Real.sqrt F.blockSide) y (W i) (b i).1 (b i).2| ≤
      ∏ l, stripTotal A (curlMagnitudes (W l) y) +
        4 * (weightScale F.blockSide ^ 64000)⁻¹ * (weightScale F.blockSide ^ 6400) ^ k *
          (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by
  classical
  have hg := isAdmissible_of hodd hcub
  obtain ⟨hs2, hsd, hsT, -⟩ := scaleThreshold_facts hfl
  have hdel := hN.rate_pos
  have hdel1 := hN.rate_le_one
  have hCS := hN.one_le_sizeConst
  have hcs : 0 < cellDecaySum (del / 2) := cellDecaySum_pos (half_pos hdel)
  have hslotT := slot_constant_le F.blockSide CS (cellDecaySum (del / 2)) hs2 hsT (by linarith) hcs.le
  have hK : ∀ l : Fin k, ∀ x i, |W l x i| ≤
      CS * (F.blockSide : ℝ) ^ 3 * Real.exp (-(del * cellSupDist (enclosingCell x) (c l).1)) :=
    fun l x i => hN.response_bound F (c l) (B l) (W l) hodd hL₁ hcub (hf l) (ht l) x i
  have hK0 : 0 ≤ CS * (F.blockSide : ℝ) ^ 3 := by positivity
  have hT0 : 0 ≤ weightScale F.blockSide ^ 6400 := pow_nonneg (by linarith) _
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun β => ∀ l, β l ∈ nearbyBonds A y)]
  apply add_le_add
  · calc _ ≤ ∑ b ∈ (Fintype.piFinset fun _ : Fin k => fineBonds F).filter
            (fun β => ∀ l, β l ∈ nearbyBonds A y),
            ∏ i, |localAxialGauge (Real.sqrt F.blockSide) y (W i) (b i).1 (b i).2| := by
          apply Finset.sum_le_sum
          intro b _
          have hP : 0 ≤ ∏ i, |localAxialGauge (Real.sqrt F.blockSide) y (W i) (b i).1 (b i).2| :=
            Finset.prod_nonneg fun _ _ => abs_nonneg _
          have hG : (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (one_le_decayWeight _ hδ (Nat.cast_nonneg _))
          exact mul_le_of_le_one_left hP hG
      _ ≤ ∑ b ∈ Fintype.piFinset (fun _ : Fin k => nearbyBonds A y),
          ∏ i, |localAxialGauge (Real.sqrt F.blockSide) y (W i) (b i).1 (b i).2| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro b hb
            exact Fintype.mem_piFinset.mpr (Finset.mem_filter.mp hb).2
          · intro b _ _
            exact Finset.prod_nonneg fun _ _ => abs_nonneg _
      _ = ∏ l, ∑ b ∈ nearbyBonds A y, |localAxialGauge (Real.sqrt F.blockSide) y (W l) b.1 b.2| :=
          sum_piFinset_nearbyBonds_prod A y fun l b => |localAxialGauge (Real.sqrt F.blockSide) y (W l) b.1 b.2|
      _ ≤ _ := by
          apply Finset.prod_le_prod (fun l _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          intro l _
          exact sum_nearbyBonds_abs_localAxialGauge_le hg _ (W l) y A hAR hA64
  · refine sum_far_tuples_le hg hk Y c hδ hdel hδd hsd hs2 y hy A hA1
      (fun l b => |localAxialGauge (Real.sqrt F.blockSide) y (W l) b.1 b.2|) (fun _ _ => abs_nonneg _) _ hT0
      ?_ ?_ _ (fun _ => rfl)
    · intro l
      exact (sum_abs_localAxialGauge_le (W l) (c l).1 _ del hg hdel hdel1 hK0 (hK l) _ hR1 hRL y).trans hslotT
    · intro l hl
      refine (sum_bondsNearCell_abs_localAxialGauge_le (W l) (c l).1 _ del hg hdel hdel1 hK0 (hK l) _ hR1 hRL y
        _ Y hl).trans ?_
      exact mul_le_mul_of_nonneg_left hslotT (by positivity)
theorem strip_ratio_le_one (ν M C6 : ℝ) (hν : 2 ≤ ν) (hM0 : 0 ≤ M) (hMb : M ≤ 20000 * ν ^ 25) (hC6 : 0 ≤ C6)
    (h : 20000 * C6 ≤ ν) : M * (C6 * (ν ^ 320)⁻¹) ≤ 1 := by
  have hν0 : 0 < ν := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have p320 : 0 < ν ^ 320 := pow_pos hν0 _
  have e : M * (C6 * (ν ^ 320)⁻¹) = M * C6 * (ν ^ 320)⁻¹ := by ring
  rw [e, mul_inv_le_iff₀ p320, one_mul]
  calc M * C6 ≤ 20000 * ν ^ 25 * C6 := mul_le_mul_of_nonneg_right hMb hC6
    _ = ν ^ 25 * (20000 * C6) := by ring
    _ ≤ ν ^ 25 * ν := mul_le_mul_of_nonneg_left h (pow_nonneg hν0.le _)
    _ = ν ^ 26 := by ring
    _ ≤ ν ^ 320 := pow_le_pow_right₀ hν1 (by norm_num)
theorem near_total_le (ν M C2 C6 CE Gi P : ℝ) (hν : 2 ≤ ν) (hM0 : 0 ≤ M) (hMb : M ≤ 20000 * ν ^ 25)
    (hC2 : 0 ≤ C2) (hC6 : 0 ≤ C6) (hCE : 0 ≤ CE) (hGi : 0 ≤ Gi) (hP : P ≤ CE ^ 6 * Gi)
    (hX : 16000000000000 * (C2 ^ 2 * C6 * CE ^ 6) ≤ ν) :
    (M * C2) ^ 2 * (M * (C6 * (ν ^ 320)⁻¹)) * P ≤ 1 / 2 * (ν ^ 160)⁻¹ * Gi := by
  have hν0 : 0 < ν := by linarith
  have hp : 0 ≤ (ν ^ 320)⁻¹ := inv_nonneg.mpr (pow_nonneg hν0.le _)
  have hX0 : 0 ≤ C2 ^ 2 * C6 * CE ^ 6 := by positivity
  have c1 : (M * C2) ^ 2 * (M * (C6 * (ν ^ 320)⁻¹)) * P ≤
      (M * C2) ^ 2 * (M * (C6 * (ν ^ 320)⁻¹)) * (CE ^ 6 * Gi) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have c2 : (M * C2) ^ 2 * (M * (C6 * (ν ^ 320)⁻¹)) * (CE ^ 6 * Gi) =
      M ^ 3 * (C2 ^ 2 * C6 * CE ^ 6) * (ν ^ 320)⁻¹ * Gi := by ring
  have c3 : M ^ 3 ≤ (20000 * ν ^ 25) ^ 3 := pow_le_pow_left₀ hM0 hMb 3
  have c4 : (20000 * ν ^ 25) ^ 3 = 8000000000000 * ν ^ 75 := by ring
  have c5 := near_powers_le ν (C2 ^ 2 * C6 * CE ^ 6) hν hX0 hX
  have c6 : M ^ 3 * (C2 ^ 2 * C6 * CE ^ 6) * (ν ^ 320)⁻¹ ≤
      8000000000000 * ν ^ 75 * (C2 ^ 2 * C6 * CE ^ 6) * (ν ^ 320)⁻¹ := by
    rw [← c4]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c3 hX0) hp
  calc _ ≤ _ := c1
    _ = _ := c2
    _ ≤ _ := mul_le_mul_of_nonneg_right (c6.trans c5) hGi
theorem far_total_le (ν N Gi : ℝ) (k : ℕ) (hν : 2 ≤ ν) (hN0 : 0 ≤ N) (hN : N ≤ ν ^ 2560) (hk : k ≤ 6)
    (hGi : 0 ≤ Gi) :
    N * (4 * (ν ^ 64000)⁻¹ * (ν ^ 6400) ^ k * Gi) ≤ 1 / 2 * (ν ^ 160)⁻¹ * Gi := by
  have hν0 : 0 < ν := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have hTk : (ν ^ 6400) ^ k ≤ ν ^ 38400 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hν1 (by omega)
  have hε : 0 ≤ 4 * (ν ^ 64000)⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.mpr (pow_nonneg hν0.le _))
  have := far_powers_le ν hν
  calc _ = (N * (4 * (ν ^ 64000)⁻¹ * (ν ^ 6400) ^ k)) * Gi := by ring
    _ ≤ (ν ^ 2560 * (4 * (ν ^ 64000)⁻¹ * ν ^ 38400)) * Gi := by
        apply mul_le_mul_of_nonneg_right _ hGi
        apply mul_le_mul hN _ (mul_nonneg hε (pow_nonneg (pow_nonneg hν0.le _) _)) (pow_nonneg hν0.le _)
        exact mul_le_mul_of_nonneg_left hTk hε
    _ ≤ _ := mul_le_mul_of_nonneg_right this hGi
theorem card_blockFineSites_le_pow (h : IsAdmissible F) (Y : F.Cell) :
    ((blockFineSites Y).card : ℝ) ≤ weightScale F.blockSide ^ 2560 := by
  have : ((blockFineSites Y).card : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := by
    exact_mod_cast card_blockFineSites_le h Y
  calc _ ≤ (F.blockSide : ℝ) ^ 4 := this
    _ = (weightScale F.blockSide ^ 640) ^ 4 := by rw [weightScale_pow]
    _ = weightScale F.blockSide ^ 2560 := by rw [← pow_mul]
theorem multilinear_sum_le {a del CS CE C6 C2 C9 : ℝ} {L₁ : ℕ} (hN : FlatConstants a del CS CE C6 C2 C9 L₁)
    (F : BlockFrame) (δ : ℝ) (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (B : Fin k → FormChain F)
    (W : Fin k → LevelForm F F.depth) (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (hodd : Odd F.blockSide)
    (hL₁ : L₁ ≤ F.blockSide)
    (hcub : IsLargeCubicTorus F) (hδ : 0 < δ) (hδd : δ ≤ del / 64) (hf : ∀ i, IsFlatChain a (c i) (B i))
    (ht : ∀ i, IsAxialResponse (c i) (B i) (W i))
    (hfl : scaleThreshold del CS CE C6 C2 ≤ weightScale F.blockSide) :
    ∑ y ∈ blockFineSites Y, ∑ b ∈ Fintype.piFinset (fun _ : Fin k => fineBonds F),
      (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹ *
        ∏ i, |localAxialGauge (Real.sqrt F.blockSide) y (W i) (b i).1 (b i).2| ≤
      (weightScale F.blockSide ^ 160)⁻¹ / torusDecayFactor F.blockSide δ (bondSpan Y c) := by
  have hg := isAdmissible_of hodd hcub
  obtain ⟨hs2, hsd, hsT, hsX⟩ := scaleThreshold_facts hfl
  obtain ⟨hA1, hAR, hA64, hAL, hM, hR1, hRL⟩ := weightScale_facts F.blockSide hs2
  have hν0 : 0 < weightScale F.blockSide := by linarith
  have hCE := hN.one_le_energyConst
  have hC6 := hN.one_le_curlConst
  have hC2 := hN.one_le_squareConst
  have hGn0 : 0 < torusDecayFactor F.blockSide δ (bondSpan Y c) := decayWeight_pos _ _ _
  have hGi : 0 ≤ (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by positivity
  generalize ⌈weightScale F.blockSide ^ 5⌉₊ = A at *
  have hM0 : (0 : ℝ) ≤ (stripIndices A).card := Nat.cast_nonneg _
  have hX1 : C6 ≤ C2 ^ 2 * C6 * CE ^ 6 := by
    have a1 : 1 ≤ C2 ^ 2 := one_le_pow₀ hC2
    have a2 : 1 ≤ CE ^ 6 := one_le_pow₀ hCE
    have a3 : C6 ≤ C2 ^ 2 * C6 := le_mul_of_one_le_left (by linarith) a1
    exact a3.trans (le_mul_of_one_le_right (by positivity) a2)
  have hτ1 := strip_ratio_le_one (weightScale F.blockSide) ((stripIndices A).card) C6 hs2 hM0 hM
    (by linarith) (by linarith)
  have hnear := sum_prod_le_of_two_square_means (blockFineSites Y) hk3
    (fun l y => stripTotal A (curlMagnitudes (W l) y))
    (fun l y => stripTotal_curl_nonneg A (W l) y)
    (fun l => Real.sqrt (chainEnergyOnCells a (B l) (cellBall Y 24)))
    (fun l => Real.sqrt_nonneg _) (((stripIndices A).card : ℝ) * C2)
    (((stripIndices A).card : ℝ) * (C6 * (weightScale F.blockSide ^ 320)⁻¹)) (by positivity) (by positivity) hτ1
    (fun l => (stripTotal_bounds hN F Y (c l) (B l) (W l) hodd hL₁ hcub (hf l) (ht l) A hAL hν0).1)
    (fun l => (stripTotal_bounds hN F Y (c l) (B l) (W l) hodd hL₁ hcub (hf l) (ht l) A hAL hν0).2)
  have hprod := prod_sqrt_energy_le hN F δ Y k c B hk6 hodd hL₁ hcub hδ.le hδd hf hsd
  have hnearAll := near_total_le (weightScale F.blockSide) ((stripIndices A).card) C2 C6 CE _ _ hs2 hM0 hM
    (by linarith) (by linarith) (by linarith) hGi hprod hsX
  have hfarAll := far_total_le (weightScale F.blockSide) ((blockFineSites Y).card) _ k hs2 (Nat.cast_nonneg _)
    (card_blockFineSites_le_pow hg Y) hk6 hGi
  calc _ ≤ ∑ y ∈ blockFineSites Y, (∏ l, stripTotal A (curlMagnitudes (W l) y) +
        4 * (weightScale F.blockSide ^ 64000)⁻¹ * (weightScale F.blockSide ^ 6400) ^ k *
          (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹) := by
        apply Finset.sum_le_sum
        intro y hy
        exact sum_tuples_at_site_le hN F δ Y k c B W (by omega) hodd hL₁ hcub hδ.le hδd hf ht hfl A hA1 hAR
          hA64 hR1 hRL y hy
    _ = ∑ y ∈ blockFineSites Y, ∏ l, stripTotal A (curlMagnitudes (W l) y) +
        ((blockFineSites Y).card : ℝ) * (4 * (weightScale F.blockSide ^ 64000)⁻¹ *
          (weightScale F.blockSide ^ 6400) ^ k * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 / 2 * (weightScale F.blockSide ^ 160)⁻¹ * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ +
        1 / 2 * (weightScale F.blockSide ^ 160)⁻¹ * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ :=
        add_le_add (hnear.trans hnearAll) hfarAll
    _ = _ := by rw [div_eq_mul_inv]; ring
theorem chainEnergyOnSites_le_cells (h : IsAdmissible F) {a : ℝ} (ha : 0 < a) (B : FormChain F) (Y : F.Cell) :
    chainEnergyOnSites a B (depthBall (cellCentre F.depth Y) (9 * F.blockSide)) ≤
      chainEnergyOnCells a B (cellBall Y 24) := by
  classical
  unfold chainEnergyOnSites chainEnergyOnCells
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      have := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨this.1, enclosingCell_mem_cellBall h (Nat.zero_le _) x Y this.2⟩
    · intro _ _ _
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · apply mul_le_mul_of_nonneg_left _ ha.le
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j + 1 ≤ F.top := Finset.mem_range.mp hj
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      have := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨this.1, enclosingCell_mem_cellBall h hj' x Y this.2⟩
    · intro _ _ _
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
def curlIncrements (W : LevelForm F F.depth) (y : F.Site F.depth) : (Fin 4 → ℤ) → Fin 4 → Fin 4 → ℝ :=
  fun v i k => |plaquetteCurl W (y + siteOfCoords F.depth v) k i - plaquetteCurl W y k i|
theorem stripTotal_increments_nonneg (A : ℕ) (W : LevelForm F F.depth) (y : F.Site F.depth) :
    0 ≤ stripTotal A (curlIncrements W y) := by
  unfold stripTotal
  refine Finset.sum_nonneg fun o _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs
  · exact Finset.sum_nonneg fun s _ => abs_nonneg _
  · exact le_rfl
theorem sum_curlIncrements_sq_le {a del CS CE C6 C2 C9 : ℝ} {L₁ : ℕ}
    (hN : FlatConstants a del CS CE C6 C2 C9 L₁)
    (F : BlockFrame) (Y : F.Cell) (c : F.Site F.top × Fin 4) (B : FormChain F) (W : LevelForm F F.depth)
    (hodd : Odd F.blockSide) (hL₁ : L₁ ≤ F.blockSide) (hcub : IsLargeCubicTorus F) (hf : IsFlatChain a c B)
    (ht : IsAxialResponse c B W) (A : ℕ) (hAL : A ≤ F.blockSide) (v : Fin 4 → ℤ) (i k : Fin 4) (hik : i < k)
    (hv : ∀ l, |v l| ≤ (A : ℤ)) :
    ∑ y ∈ blockFineSites Y, curlIncrements W y v i k ^ 2 ≤
      C9 * ((A : ℝ) / F.blockSide) * chainEnergyOnCells a B (cellBall Y 24) := by
  have hg := isAdmissible_of hodd hcub
  have hLp := hg.blockSide_pos
  have he0 : 0 ≤ chainEnergyOnCells a B (cellBall Y 24) := chainEnergyOnCells_nonneg hN.coupling_pos _ _
  have hC9 := hN.one_le_shiftConst
  have hterm : ∀ y, curlIncrements W y v i k ^ 2 =
      (plaquetteCurl (B F.depth) (y + siteOfCoords F.depth v) i k - plaquetteCurl (B F.depth) y i k) ^ 2 := by
    intro y
    simp only [curlIncrements, sq_abs]
    have e1 := ht.curl_eq (y + siteOfCoords F.depth v) (i, k) (mem_orientedPlanes hik)
    have e2 := ht.curl_eq y (i, k) (mem_orientedPlanes hik)
    simp only at e1 e2
    rw [plaquetteCurl_antisymm W (y + siteOfCoords F.depth v) k i, plaquetteCurl_antisymm W y k i, e1, e2]
    ring
  set n : ℕ := Finset.univ.sup fun l => (v l).natAbs with hn
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty
    (fun l => (v l).natAbs)
  have hnv : ∀ l, (v l).natAbs ≤ n := fun l =>
    Finset.le_sup (f := fun l => (v l).natAbs) (Finset.mem_univ l)
  have hnA : n ≤ A := by
    rw [hn, hl₀]
    have := hv l₀
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos n with h0 | h1
  · have hz : v = 0 := by
      funext l
      have := hnv l
      simp only [Pi.zero_apply]
      omega
    have : ∀ y, curlIncrements W y v i k = 0 := by
      intro y
      simp [curlIncrements, hz, siteOfCoords_zero]
    simp only [this]
    have : (0 : ℝ) ≤ C9 * ((A : ℝ) / F.blockSide) * chainEnergyOnCells a B (cellBall Y 24) := by positivity
    simpa using this
  · have hs := hN.shift_bound F c B hodd hL₁ hcub hf (cellCentre F.depth Y) v n
      (fun l => by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hnv l)
      ⟨l₀, by
        rw [Int.abs_eq_natAbs, hn, hl₀]⟩ h1 (hnA.trans hAL)
    have hen := chainEnergyOnSites_le_cells hg hN.coupling_pos B Y
    calc ∑ y ∈ blockFineSites Y, curlIncrements W y v i k ^ 2
        ≤ ∑ y ∈ blockFineSites Y, ∑ e ∈ orientedPlanes,
            (plaquetteCurl (B F.depth) (y + siteOfCoords F.depth v) e.1 e.2 -
              plaquetteCurl (B F.depth) y e.1 e.2) ^ 2 := by
          apply Finset.sum_le_sum
          intro y _
          rw [hterm]
          exact Finset.single_le_sum
            (f := fun e : Fin 4 × Fin 4 => (plaquetteCurl (B F.depth) (y + siteOfCoords F.depth v) e.1 e.2 -
              plaquetteCurl (B F.depth) y e.1 e.2) ^ 2)
            (fun _ _ => sq_nonneg _) (mem_orientedPlanes hik)
      _ ≤ ∑ p ∈ (sitesOfCells (finiteCells F) F.depth).filter
            (fun p => siteSupDist p (cellCentre F.depth Y) ≤ F.blockSide), ∑ e ∈ orientedPlanes,
            (plaquetteCurl (B F.depth) (p + siteOfCoords F.depth v) e.1 e.2 -
              plaquetteCurl (B F.depth) p e.1 e.2) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro y hy
            exact Finset.mem_filter.mpr ⟨mem_sitesOfCells hg y, siteSupDist_cellCentre_le hg Y y hy⟩
          · intro _ _ _
            exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      _ ≤ C9 * ((n : ℝ) / F.blockSide) *
            chainEnergyOnSites a B (depthBall (cellCentre F.depth Y) (9 * F.blockSide)) := hs
      _ ≤ C9 * ((A : ℝ) / F.blockSide) * chainEnergyOnCells a B (cellBall Y 24) := by
          have hnA' : (n : ℝ) ≤ A := by exact_mod_cast hnA
          have : C9 * ((n : ℝ) / F.blockSide) ≤ C9 * ((A : ℝ) / F.blockSide) := by gcongr
          have hes : 0 ≤ chainEnergyOnSites a B (depthBall (cellCentre F.depth Y) (9 * F.blockSide)) := by
            unfold chainEnergyOnSites
            refine add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) ?_
            exact mul_nonneg hN.coupling_pos.le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
              Finset.sum_nonneg fun _ _ => sq_nonneg _)
          exact mul_le_mul this hen hes (by positivity)
theorem localAxialGauge_sub_axialGaugePotential (h : IsAdmissible F) (R : ℝ) (W : LevelForm F F.depth)
    (y : F.Site F.depth) (A : ℕ) (hA : (A : ℝ) + 1 ≤ R)
    (hA2 : 2 * (A + 1) < 64 * F.blockSide) (o : Fin 4 → ℤ) (ho : o ∈ offsetBox A) (i : Fin 4) :
    localAxialGauge R y W (y + siteOfCoords F.depth o) i -
      axialGaugePotential y (fun μ ν => plaquetteCurl W y μ ν) (y + siteOfCoords F.depth o) i =
      ∑ k : Fin 4, if i < k then
        segmentSum (fun j => plaquetteCurl W (y + siteOfCoords F.depth (leadingCoords o k.val + axisVec k j)) k i -
          plaquetteCurl W y k i) (o k) else 0 := by
  have hb := (mem_offsetBox A o).mp ho
  have hoff : siteOffset y (y + siteOfCoords F.depth o) = o := by
    apply siteOffset_add_siteOfCoords y o (h.period_pos F.depth)
    intro l
    have a1 := hb l
    have a2 : (F.period F.depth l : ℤ) = (F.extent l : ℤ) * F.blockSide := by
      rw [period_depth]; push_cast; ring
    have a3 : (64 : ℤ) ≤ F.extent l := by exact_mod_cast h.extent_ge l
    have a5 : (64 : ℤ) * F.blockSide ≤ F.period F.depth l := by rw [a2]; nlinarith
    omega
  rw [localAxialGauge_of_mem_offsetBox h R W y A hA hA2 o ho i]
  unfold axialGaugePotential
  rw [hoff, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i < k
  · simp only [hik, if_true]
    rw [segmentSum_sub, segmentSum_const]
  · simp [hik]
theorem sum_nearbyBonds_abs_sub_le (h : IsAdmissible F) (R : ℝ) (W : LevelForm F F.depth) (y : F.Site F.depth)
    (A : ℕ) (hA : (A : ℝ) + 1 ≤ R) (hA2 : 2 * (A + 1) < 64 * F.blockSide) :
    ∑ b ∈ nearbyBonds A y, |localAxialGauge R y W b.1 b.2 -
      axialGaugePotential y (fun μ ν => plaquetteCurl W y μ ν) b.1 b.2| ≤ stripTotal A (curlIncrements W y) := by
  refine (sum_nearbyBonds_le h A y (fun b => |localAxialGauge R y W b.1 b.2 -
    axialGaugePotential y (fun μ ν => plaquetteCurl W y μ ν) b.1 b.2|) fun _ => abs_nonneg _).trans ?_
  apply Finset.sum_le_sum
  intro o ho
  apply Finset.sum_le_sum
  intro i _
  simp only
  rw [localAxialGauge_sub_axialGaugePotential h R W y A hA hA2 o ho i]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  by_cases hik : i < k
  · simp only [hik, if_true]
    refine (abs_segmentSum_le _ _).trans (le_of_eq ?_)
    rfl
  · simp [hik]
theorem abs_axialGaugePotential_le (y x : F.Site F.depth) (Fm : Fin 4 → Fin 4 → ℝ) (i : Fin 4) :
    |axialGaugePotential y Fm x i| ≤ (siteSupDist x y : ℝ) * ∑ μ, ∑ ν, |Fm μ ν| := by
  unfold axialGaugePotential
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hrow : ∀ l : Fin 4, |if i < l then (siteOffset y x l : ℝ) * Fm l i else 0| ≤
      (siteSupDist x y : ℝ) * |Fm l i| := by
    intro l
    split_ifs
    · rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have := natAbs_valMinAbs_le_siteSupDist x y l
      simp only [siteOffset, Pi.sub_apply]
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      exact_mod_cast this
    · simp only [abs_zero]
      positivity
  calc _ ≤ ∑ l, (siteSupDist x y : ℝ) * |Fm l i| := Finset.sum_le_sum fun l _ => hrow l
    _ = (siteSupDist x y : ℝ) * ∑ l, |Fm l i| := by rw [Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro l _
        exact Finset.single_le_sum (f := fun ν => |Fm l ν|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
theorem card_nearbyBonds_le (h : IsAdmissible F) (A : ℕ) (y : F.Site F.depth) :
    ((nearbyBonds A y).card : ℝ) ≤ (2 * (A : ℝ) + 1) ^ 4 * 4 := by
  have := sum_nearbyBonds_le h A y (fun _ => (1 : ℝ)) fun _ => zero_le_one
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin,
    card_offsetBox] at this
  push_cast at this
  linarith
theorem sum_piFinset_two {α : Type} [DecidableEq α] (S : Finset α) (f : α → α → ℝ) :
    ∑ β ∈ Fintype.piFinset (fun _ : Fin 2 => S), f (β 0) (β 1) = ∑ b ∈ S, ∑ b' ∈ S, f b b' := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun β => (β 0, β 1)) (fun p => ![p.1, p.2])
  · intro β hβ
    rw [Fintype.mem_piFinset] at hβ
    exact Finset.mem_product.mpr ⟨hβ 0, hβ 1⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    rw [Fintype.mem_piFinset]
    intro l
    fin_cases l
    · exact h1
    · exact h2
  · intro β _
    funext l
    fin_cases l <;> rfl
  · intro p _
    rfl
  · intro β _
    rfl
theorem bondPairing_addGradient (q : F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ)
    (A A' : LevelForm F F.depth) (φ φ' : F.Site F.depth → ℝ)
    (h1 : ∀ (A : LevelForm F F.depth) (φ : F.Site F.depth → ℝ),
      bondPairing q (addGradient (fun _ _ => 0) φ) A = 0)
    (h2 : ∀ (A : LevelForm F F.depth) (φ : F.Site F.depth → ℝ),
      bondPairing q A (addGradient (fun _ _ => 0) φ) = 0) :
    bondPairing q (addGradient A φ) (addGradient A' φ') = bondPairing q A A' := by
  have add1 : ∀ (X X' Z : LevelForm F F.depth),
      bondPairing q (fun x i => X x i + X' x i) Z = bondPairing q X Z + bondPairing q X' Z := by
    intro X X' Z
    unfold bondPairing
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  have add2 : ∀ (X X' Z : LevelForm F F.depth),
      bondPairing q Z (fun x i => X x i + X' x i) = bondPairing q Z X + bondPairing q Z X' := by
    intro X X' Z
    unfold bondPairing
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  have e : ∀ (X : LevelForm F F.depth) (ψ : F.Site F.depth → ℝ), addGradient X ψ =
      fun x i => X x i + addGradient (fun _ _ => 0) ψ x i := by
    intro X ψ
    funext x i
    simp [addGradient]
  rw [e A φ, e A' φ', add1, add2, add2, h1, h1, h2]
  simp
theorem sum_pairs_split (A : ℕ) (y : F.Site F.depth) (f : F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ) :
    ∑ b ∈ fineBonds F, ∑ b' ∈ fineBonds F, f b b' =
      ∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y, f b b' +
        ∑ β ∈ (Fintype.piFinset fun _ : Fin 2 => fineBonds F).filter
          (fun β => ¬ ∀ l, β l ∈ nearbyBonds A y), f (β 0) (β 1) := by
  classical
  rw [← sum_piFinset_two, ← Finset.sum_filter_add_sum_filter_not _ (fun β => ∀ l, β l ∈ nearbyBonds A y),
    ← sum_piFinset_two (nearbyBonds A y)]
  congr 1
  apply Finset.sum_congr _ fun _ _ => rfl
  ext β
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨fun l => (Finset.mem_filter.mp (h l)).1, h⟩
theorem abs_double_sum_le (S S' : Finset (F.Site F.depth × Fin 4))
    (q : F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ)
    (E : ℝ) (hE : 0 ≤ E) (hq : ∀ b b', |q b b'| ≤ E) (u v : F.Site F.depth × Fin 4 → ℝ) :
    |∑ b ∈ S, ∑ b' ∈ S', q b b' * u b * v b'| ≤ E * ((∑ b ∈ S, |u b|) * ∑ b' ∈ S', |v b'|) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b' _
  rw [abs_mul, abs_mul]
  have := hq b b'
  calc |q b b'| * |u b| * |v b'| ≤ E * |u b| * |v b'| := by gcongr
    _ = E * (|u b| * |v b'|) := by ring
theorem abs_near_pairs_sub_le (h : IsAdmissible F) (R : ℝ) (A : ℕ) (y : F.Site F.depth) (hAR : (A : ℝ) + 1 ≤ R)
    (hA64 : 2 * (A + 1) < 64 * F.blockSide) (q : F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ) (E : ℝ)
    (hE : 0 ≤ E) (hq : ∀ b b', |q b b'| ≤ E) (W₀ W₁ : LevelForm F F.depth) :
    |∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y,
        q b b' * localAxialGauge R y W₀ b.1 b.2 * localAxialGauge R y W₁ b'.1 b'.2 -
      ∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y,
        q b b' * axialGaugePotential y (fun μ ν => plaquetteCurl W₀ y μ ν) b.1 b.2 *
          axialGaugePotential y (fun μ ν => plaquetteCurl W₁ y μ ν) b'.1 b'.2| ≤
      E * (stripTotal A (curlIncrements W₀ y) * stripTotal A (curlMagnitudes W₁ y) +
        (stripTotal A (curlMagnitudes W₀ y) + stripTotal A (curlIncrements W₀ y)) *
          stripTotal A (curlIncrements W₁ y)) := by
  set U₀ : F.Site F.depth × Fin 4 → ℝ := fun b => localAxialGauge R y W₀ b.1 b.2 with hU₀
  set U₁ : F.Site F.depth × Fin 4 → ℝ := fun b => localAxialGauge R y W₁ b.1 b.2 with hU₁
  set X₀ : F.Site F.depth × Fin 4 → ℝ :=
    fun b => axialGaugePotential y (fun μ ν => plaquetteCurl W₀ y μ ν) b.1 b.2 with hX₀
  set X₁ : F.Site F.depth × Fin 4 → ℝ :=
    fun b => axialGaugePotential y (fun μ ν => plaquetteCurl W₁ y μ ν) b.1 b.2 with hX₁
  have e : ∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y, q b b' * U₀ b * U₁ b' -
      ∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y, q b b' * X₀ b * X₁ b' =
      ∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y, q b b' * (fun b => U₀ b - X₀ b) b * U₁ b' +
      ∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y, q b b' * X₀ b * (fun b => U₁ b - X₁ b) b' := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  have t0 : ∑ b ∈ nearbyBonds A y, |U₀ b - X₀ b| ≤ stripTotal A (curlIncrements W₀ y) :=
    sum_nearbyBonds_abs_sub_le h R W₀ y A hAR hA64
  have t1 : ∑ b ∈ nearbyBonds A y, |U₁ b - X₁ b| ≤ stripTotal A (curlIncrements W₁ y) :=
    sum_nearbyBonds_abs_sub_le h R W₁ y A hAR hA64
  have s0 : ∑ b ∈ nearbyBonds A y, |U₀ b| ≤ stripTotal A (curlMagnitudes W₀ y) :=
    sum_nearbyBonds_abs_localAxialGauge_le h R W₀ y A hAR hA64
  have s1 : ∑ b ∈ nearbyBonds A y, |U₁ b| ≤ stripTotal A (curlMagnitudes W₁ y) :=
    sum_nearbyBonds_abs_localAxialGauge_le h R W₁ y A hAR hA64
  have x0 : ∑ b ∈ nearbyBonds A y, |X₀ b| ≤
      stripTotal A (curlMagnitudes W₀ y) + stripTotal A (curlIncrements W₀ y) := by
    calc _ ≤ ∑ b ∈ nearbyBonds A y, (|U₀ b| + |U₀ b - X₀ b|) := by
          apply Finset.sum_le_sum
          intro b _
          have := abs_sub_abs_le_abs_sub (X₀ b) (U₀ b)
          rw [abs_sub_comm (X₀ b)] at this
          linarith
      _ ≤ _ := by
          rw [Finset.sum_add_distrib]
          exact add_le_add s0 t0
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have n1 : 0 ≤ ∑ b ∈ nearbyBonds A y, |U₁ b| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n2 : 0 ≤ ∑ b ∈ nearbyBonds A y, |X₀ b| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n3 := stripTotal_increments_nonneg A W₀ y
  have a1 := abs_double_sum_le (nearbyBonds A y) (nearbyBonds A y) q E hE hq (fun b => U₀ b - X₀ b) U₁
  have a2 := abs_double_sum_le (nearbyBonds A y) (nearbyBonds A y) q E hE hq X₀ (fun b => U₁ b - X₁ b)
  refine (add_le_add a1 a2).trans ?_
  rw [mul_add]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hE
    exact mul_le_mul t0 s1 n1 n3
  · apply mul_le_mul_of_nonneg_left _ hE
    exact mul_le_mul x0 t1 (Finset.sum_nonneg fun _ _ => abs_nonneg _) (n2.trans x0)
theorem abs_axial_pairs_sub_le (h : IsAdmissible F) (R : ℝ) (hR0 : 0 ≤ R) (A ρ : ℕ) (hρ : (ρ : ℝ) ≤ R)
    (hρ2 : R < (ρ : ℝ) + 1) (hAρ : A ≤ ρ)
    (y : F.Site F.depth) (q : F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ) (E ε Φ₀ Φ₁ : ℝ)
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (hΦ₀ : 0 ≤ Φ₀) (hΦ₁ : 0 ≤ Φ₁)
    (hq : ∀ b b', (A < siteSupDist b.1 y ∨ A < siteSupDist b'.1 y) → |q b b'| ≤ ε * E)
    (u v : F.Site F.depth × Fin 4 → ℝ)
    (hu : ∀ b, (siteSupDist b.1 y : ℝ) ≤ R → |u b| ≤ R * Φ₀)
    (hv : ∀ b, (siteSupDist b.1 y : ℝ) ≤ R → |v b| ≤ R * Φ₁) :
    |∑ b ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ R),
        ∑ b' ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ R), q b b' * u b * v b' -
      ∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y, q b b' * u b * v b'| ≤
      ((2 * (ρ : ℝ) + 1) ^ 4 * 4) ^ 2 * (ε * E * (R * Φ₀) * (R * Φ₁)) := by
  classical
  set RB := (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ R) with hRB
  have hsub : nearbyBonds A y ⊆ RB := by
    intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨h1, ?_⟩
    have : (siteSupDist b.1 y : ℝ) ≤ A := by exact_mod_cast h2
    have hA' : (A : ℝ) ≤ ρ := by exact_mod_cast hAρ
    linarith
  have hRBρ : RB ⊆ nearbyBonds ρ y := by
    intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨h1, ?_⟩
    have : (siteSupDist b.1 y : ℝ) < (ρ : ℝ) + 1 := lt_of_le_of_lt h2 hρ2
    have : siteSupDist b.1 y < ρ + 1 := by exact_mod_cast this
    omega
  have hcard : (RB.card : ℝ) ≤ (2 * (ρ : ℝ) + 1) ^ 4 * 4 := by
    refine le_trans ?_ (card_nearbyBonds_le h ρ y)
    exact_mod_cast Finset.card_le_card hRBρ
  set f : (F.Site F.depth × Fin 4) × (F.Site F.depth × Fin 4) → ℝ :=
    fun p => q p.1 p.2 * u p.1 * v p.2 with hf
  have e1 : ∑ b ∈ RB, ∑ b' ∈ RB, q b b' * u b * v b' = ∑ p ∈ RB ×ˢ RB, f p := by
    rw [Finset.sum_product]
  have e2 : ∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y, q b b' * u b * v b' =
      ∑ p ∈ nearbyBonds A y ×ˢ nearbyBonds A y, f p := by
    rw [Finset.sum_product]
  rw [e1, e2, ← Finset.sum_sdiff (Finset.product_subset_product hsub hsub), add_sub_cancel_right]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ p ∈ (RB ×ˢ RB) \ (nearbyBonds A y ×ˢ nearbyBonds A y),
      |f p| ≤ ε * E * (R * Φ₀) * (R * Φ₁) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hb, hb'⟩ := Finset.mem_product.mp hp1
    have hb1 := Finset.mem_filter.mp hb
    have hb2 := Finset.mem_filter.mp hb'
    have hfar : A < siteSupDist p.1.1 y ∨ A < siteSupDist p.2.1 y := by
      by_contra hc
      push_neg at hc
      exact hp2 (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hb1.1, hc.1⟩,
        Finset.mem_filter.mpr ⟨hb2.1, hc.2⟩⟩)
    simp only [hf]
    rw [abs_mul, abs_mul]
    have a1 := hq p.1 p.2 hfar
    have a2 := hu p.1 hb1.2
    have a3 := hv p.2 hb2.2
    have : 0 ≤ ε * E := by positivity
    calc |q p.1 p.2| * |u p.1| * |v p.2| ≤ (ε * E) * (R * Φ₀) * (R * Φ₁) := by gcongr
      _ = _ := rfl
  have hpos : 0 ≤ ε * E * (R * Φ₀) * (R * Φ₁) := by positivity
  calc _ ≤ ∑ _p ∈ (RB ×ˢ RB) \ (nearbyBonds A y ×ˢ nearbyBonds A y), ε * E * (R * Φ₀) * (R * Φ₁) :=
        Finset.sum_le_sum hterm
    _ = (((RB ×ˢ RB) \ (nearbyBonds A y ×ˢ nearbyBonds A y)).card : ℝ) * (ε * E * (R * Φ₀) * (R * Φ₁)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * (ρ : ℝ) + 1) ^ 4 * 4) ^ 2 * (ε * E * (R * Φ₀) * (R * Φ₁)) := by
        apply mul_le_mul_of_nonneg_right _ hpos
        have c1 : (((RB ×ˢ RB) \ (nearbyBonds A y ×ˢ nearbyBonds A y)).card : ℝ) ≤ (RB.card : ℝ) ^ 2 := by
          have : ((RB ×ˢ RB) \ (nearbyBonds A y ×ˢ nearbyBonds A y)).card ≤ RB.card * RB.card :=
            (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq (Finset.card_product _ _))
          rw [sq]
          exact_mod_cast this
        exact c1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2)
theorem sum_far_tuples_at_site_le {a del CS CE C6 C2 C9 : ℝ} {L₁ : ℕ}
    (hN : FlatConstants a del CS CE C6 C2 C9 L₁)
    (F : BlockFrame) (δ : ℝ) (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (B : Fin k → FormChain F)
    (W : Fin k → LevelForm F F.depth) (hk : 0 < k) (hodd : Odd F.blockSide) (hL₁ : L₁ ≤ F.blockSide)
    (hcub : IsLargeCubicTorus F) (hδ : 0 ≤ δ) (hδd : δ ≤ del / 64) (hf : ∀ i, IsFlatChain a (c i) (B i))
    (ht : ∀ i, IsAxialResponse (c i) (B i) (W i))
    (hfl : scaleThreshold del CS CE C6 C2 ≤ weightScale F.blockSide)
    (A : ℕ) (hA1 : weightScale F.blockSide ^ 5 ≤ (A : ℝ) + 1) (hR1 : 1 ≤ Real.sqrt F.blockSide)
    (hRL : 2 * Real.sqrt F.blockSide ≤ F.blockSide)
    (y : F.Site F.depth) (hy : y ∈ blockFineSites Y) :
    ∑ b ∈ (Fintype.piFinset fun _ : Fin k => fineBonds F).filter
        (fun β => ¬ ∀ l, β l ∈ nearbyBonds A y),
      (torusDecayFactor F.blockSide δ (bondSpan y b))⁻¹ *
        ∏ i, |localAxialGauge (Real.sqrt F.blockSide) y (W i) (b i).1 (b i).2| ≤
      4 * (weightScale F.blockSide ^ 64000)⁻¹ * (weightScale F.blockSide ^ 6400) ^ k *
        (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by
  have hg := isAdmissible_of hodd hcub
  obtain ⟨hs2, hsd, hsT, -⟩ := scaleThreshold_facts hfl
  have hdel := hN.rate_pos
  have hdel1 := hN.rate_le_one
  have hCS := hN.one_le_sizeConst
  have hcs : 0 < cellDecaySum (del / 2) := cellDecaySum_pos (half_pos hdel)
  have hslotT := slot_constant_le F.blockSide CS (cellDecaySum (del / 2)) hs2 hsT (by linarith) hcs.le
  have hK : ∀ l : Fin k, ∀ x i, |W l x i| ≤
      CS * (F.blockSide : ℝ) ^ 3 * Real.exp (-(del * cellSupDist (enclosingCell x) (c l).1)) :=
    fun l x i => hN.response_bound F (c l) (B l) (W l) hodd hL₁ hcub (hf l) (ht l) x i
  have hK0 : 0 ≤ CS * (F.blockSide : ℝ) ^ 3 := by positivity
  have hT0 : 0 ≤ weightScale F.blockSide ^ 6400 := pow_nonneg (by linarith) _
  refine sum_far_tuples_le hg hk Y c hδ hdel hδd hsd hs2 y hy A hA1
    (fun l b => |localAxialGauge (Real.sqrt F.blockSide) y (W l) b.1 b.2|) (fun _ _ => abs_nonneg _) _ hT0 ?_ ?_ _
    (fun _ => rfl)
  · intro l
    exact (sum_abs_localAxialGauge_le (W l) (c l).1 _ del hg hdel hdel1 hK0 (hK l) _ hR1 hRL y).trans hslotT
  · intro l hl
    refine (sum_bondsNearCell_abs_localAxialGauge_le (W l) (c l).1 _ del hg hdel hdel1 hK0 (hK l) _ hR1 hRL y
      _ Y hl).trans ?_
    exact mul_le_mul_of_nonneg_left hslotT (by positivity)
theorem small_terms_le (L : ℕ) (hs2 : 2 ≤ weightScale L) (ρ : ℕ) (hρ : (ρ : ℝ) ≤ Real.sqrt L) :
    (L : ℝ) ^ (-(7000 : ℝ)) + ((2 * (ρ : ℝ) + 1) ^ 4 * 4) ^ 2 *
      ((weightScale L ^ 64000)⁻¹ * (Real.sqrt L * Real.sqrt L)) ≤
      2 * (weightScale L ^ 8000)⁻¹ := by
  have hν0 : 0 < weightScale L := by linarith
  have hν1 : 1 ≤ weightScale L := by linarith
  have hLpos : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hLν : (L : ℝ) = weightScale L ^ 640 := (weightScale_pow L).symm
  have h1 : (L : ℝ) ^ (-(7000 : ℝ)) ≤ (weightScale L ^ 8000)⁻¹ := by
    rw [Real.rpow_neg hLpos]
    have e : (L : ℝ) ^ (7000 : ℝ) = (L : ℝ) ^ (7000 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [e, hLν, ← pow_mul]
    exact inv_anti₀ (pow_pos hν0 _) (pow_le_pow_right₀ hν1 (by norm_num))
  rw [sqrt_blockSide_eq L hν0] at hρ ⊢
  generalize weightScale L = ν at *
  have hR1 : 1 ≤ ν ^ 320 := one_le_pow₀ hν1
  have b1 : 2 * (ρ : ℝ) + 1 ≤ 3 * ν ^ 320 := by linarith
  have b2 : ((2 * (ρ : ℝ) + 1) ^ 4 * 4) ^ 2 ≤ ((3 * ν ^ 320) ^ 4 * 4) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    exact pow_le_pow_left₀ (by positivity) b1 4
  have b4 : 104976 * ν ^ 3200 * (ν ^ 64000)⁻¹ ≤ (ν ^ 8000)⁻¹ := by
    have e : ν ^ 64000 = ν ^ 3200 * ν ^ 8000 * ν ^ 52800 := by rw [← pow_add, ← pow_add]
    have p2 := pow_pos hν0 8000
    have p3 := pow_pos hν0 52800
    have c1 : (104976 : ℝ) ≤ ν ^ 52800 := by
      have a : (2 : ℝ) ^ 17 ≤ ν ^ 17 := pow_le_pow_left₀ (by norm_num) hs2 17
      have b : ν ^ 17 ≤ ν ^ 52800 := pow_le_pow_right₀ hν1 (by norm_num)
      norm_num at a
      linarith
    rw [e]
    have : 104976 * ν ^ 3200 * (ν ^ 3200 * ν ^ 8000 * ν ^ 52800)⁻¹ =
        (104976 * (ν ^ 52800)⁻¹) * (ν ^ 8000)⁻¹ := by
      field_simp
    rw [this]
    apply mul_le_of_le_one_left (inv_nonneg.mpr p2.le)
    rw [mul_inv_le_iff₀ p3]
    linarith
  have b5 : ((2 * (ρ : ℝ) + 1) ^ 4 * 4) ^ 2 * ((ν ^ 64000)⁻¹ * (ν ^ 320 * ν ^ 320)) ≤
      ((3 * ν ^ 320) ^ 4 * 4) ^ 2 * ((ν ^ 64000)⁻¹ * (ν ^ 320 * ν ^ 320)) :=
    mul_le_mul_of_nonneg_right b2 (by positivity)
  linarith
theorem abs_bondPairing_at_site_le {a del CS CE C6 C2 C9 : ℝ} {L₁ : ℕ}
    (hN : FlatConstants a del CS CE C6 C2 C9 L₁)
    (F : BlockFrame) (δ E : ℝ) (Y : F.Cell) (c : Fin 2 → F.Site F.top × Fin 4) (B : Fin 2 → FormChain F)
    (W : Fin 2 → LevelForm F F.depth) (hodd : Odd F.blockSide) (hL₁ : L₁ ≤ F.blockSide)
    (hcub : IsLargeCubicTorus F) (hδ : 0 ≤ δ) (hδd : δ ≤ del / 64) (hE : 0 ≤ E) (hf : ∀ i, IsFlatChain a (c i) (B i))
    (ht : ∀ i, IsAxialResponse (c i) (B i) (W i))
    (hfl : scaleThreshold del CS CE C6 C2 ≤ weightScale F.blockSide)
    (A : ℕ) (hA1 : weightScale F.blockSide ^ 5 ≤ (A : ℝ) + 1) (hAR : (A : ℝ) + 1 ≤ Real.sqrt F.blockSide)
    (hA64 : 2 * (A + 1) < 64 * F.blockSide) (hR1 : 1 ≤ Real.sqrt F.blockSide)
    (hRL : 2 * Real.sqrt F.blockSide ≤ F.blockSide)
    (y : F.Site F.depth) (hy : y ∈ blockFineSites Y) (q : F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ)
    (hq0 : ∀ (A : LevelForm F F.depth) (φ : F.Site F.depth → ℝ),
      bondPairing q (addGradient (fun _ _ => 0) φ) A = 0 ∧
      bondPairing q A (addGradient (fun _ _ => 0) φ) = 0)
    (hq1 : ∀ b b', |q b b'| ≤ E / torusDecayFactor F.blockSide δ (bondSpan y ![b, b']))
    (hq2 : ∀ (Fm Fm' : Fin 4 → Fin 4 → ℝ), (∀ μ ν, Fm μ ν = - Fm ν μ) → (∀ μ ν, Fm' μ ν = - Fm' ν μ) →
      |∑ b ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
        ∑ b' ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
          q b b' * axialGaugePotential y Fm b.1 b.2 * axialGaugePotential y Fm' b'.1 b'.2| ≤
        (F.blockSide : ℝ) ^ (-(7000 : ℝ)) * E * (∑ μ, ∑ ν, |Fm μ ν|) * ∑ μ, ∑ ν, |Fm' μ ν|) :
    |bondPairing q (W 0) (W 1)| ≤
      E * (stripTotal A (curlIncrements (W 0) y) * stripTotal A (curlMagnitudes (W 1) y) +
        (stripTotal A (curlMagnitudes (W 0) y) + stripTotal A (curlIncrements (W 0) y)) *
          stripTotal A (curlIncrements (W 1) y)) +
      2 * (weightScale F.blockSide ^ 8000)⁻¹ * E *
        ((∑ μ, ∑ ν, |plaquetteCurl (W 0) y μ ν|) * ∑ μ, ∑ ν, |plaquetteCurl (W 1) y μ ν|) +
      E * (4 * (weightScale F.blockSide ^ 64000)⁻¹ * (weightScale F.blockSide ^ 6400) ^ 2 *
        (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹) := by
  classical
  have hg := isAdmissible_of hodd hcub
  have hLp := hg.blockSide_pos
  obtain ⟨hs2, hsd, -, -⟩ := scaleThreshold_facts hfl
  have hν0 : 0 < weightScale F.blockSide := by linarith
  have hν1 : 1 ≤ weightScale F.blockSide := by linarith
  set R := Real.sqrt (F.blockSide : ℝ) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hqE : ∀ b b', |q b b'| ≤ E := by
    intro b b'
    refine (hq1 b b').trans ?_
    exact div_le_self hE (one_le_decayWeight _ hδ (Nat.cast_nonneg _))
  set U : Fin 2 → F.Site F.depth × Fin 4 → ℝ := fun l b => localAxialGauge R y (W l) b.1 b.2 with hU
  have e0 : bondPairing q (W 0) (W 1) =
      ∑ b ∈ fineBonds F, ∑ b' ∈ fineBonds F, q b b' * U 0 b * U 1 b' := by
    have := bondPairing_addGradient q (W 0) (W 1)
      (fun z => smoothCutoff R y z * (- pathSum (W 0) y (axisPath (siteOffset y z) 1)))
      (fun z => smoothCutoff R y z * (- pathSum (W 1) y (axisPath (siteOffset y z) 1)))
      (fun A φ => (hq0 A φ).1) (fun A φ => (hq0 A φ).2)
    rw [← this]
    rfl
  rw [e0, sum_pairs_split A y]
  set Far := ∑ β ∈ (Fintype.piFinset fun _ : Fin 2 => fineBonds F).filter
    (fun β => ¬ ∀ l, β l ∈ nearbyBonds A y), q (β 0) (β 1) * U 0 (β 0) * U 1 (β 1) with hFar
  set NN := ∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y, q b b' * U 0 b * U 1 b' with hNN
  set X : Fin 2 → F.Site F.depth × Fin 4 → ℝ := fun l b =>
    axialGaugePotential y (fun μ ν => plaquetteCurl (W l) y μ ν) b.1 b.2 with hX
  set NX := ∑ b ∈ nearbyBonds A y, ∑ b' ∈ nearbyBonds A y, q b b' * X 0 b * X 1 b' with hNX
  set RX := ∑ b ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ R),
    ∑ b' ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ R), q b b' * X 0 b * X 1 b' with hRX
  set Φ₀ := ∑ μ, ∑ ν, |plaquetteCurl (W 0) y μ ν| with hΦ₀
  set Φ₁ := ∑ μ, ∑ ν, |plaquetteCurl (W 1) y μ ν| with hΦ₁
  have hΦ₀0 : 0 ≤ Φ₀ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hΦ₁0 : 0 ≤ Φ₁ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hfar : |Far| ≤ E * (4 * (weightScale F.blockSide ^ 64000)⁻¹ * (weightScale F.blockSide ^ 6400) ^ 2 *
      (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹) := by
    have hmain := sum_far_tuples_at_site_le hN F δ Y 2 c B W (by norm_num) hodd hL₁ hcub hδ hδd hf ht hfl A hA1
      hR1 hRL y hy
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hmain hE)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro β _
    have e1 : (![β 0, β 1] : Fin 2 → F.Site F.depth × Fin 4) = β := by
      funext l
      fin_cases l <;> rfl
    have h1 := hq1 (β 0) (β 1)
    rw [e1] at h1
    rw [Fin.prod_univ_two, abs_mul, abs_mul]
    calc |q (β 0) (β 1)| * |U 0 (β 0)| * |U 1 (β 1)|
        ≤ E / torusDecayFactor F.blockSide δ (bondSpan y β) * |U 0 (β 0)| * |U 1 (β 1)| := by gcongr
      _ = _ := by simp only [hU]; rw [div_eq_mul_inv]; ring
  have hnear : |NN - NX| ≤ _ := abs_near_pairs_sub_le hg R A y hAR hA64 q E hE hqE (W 0) (W 1)
  have hax := hq2 (fun μ ν => plaquetteCurl (W 0) y μ ν) (fun μ ν => plaquetteCurl (W 1) y μ ν)
    (fun μ ν => plaquetteCurl_antisymm _ _ _ _) (fun μ ν => plaquetteCurl_antisymm _ _ _ _)
  set ρ := ⌊R⌋₊ with hρ
  have hρ1 : (ρ : ℝ) ≤ R := Nat.floor_le hR0
  have hρ2 : R < (ρ : ℝ) + 1 := Nat.lt_floor_add_one R
  have hAρ : A ≤ ρ := by
    apply Nat.le_floor
    have : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    linarith
  have hrest := abs_axial_pairs_sub_le hg R hR0 A ρ hρ1 hρ2 hAρ y q E (weightScale F.blockSide ^ 64000)⁻¹ Φ₀ Φ₁
    (inv_nonneg.mpr (pow_nonneg hν0.le _)) hE hΦ₀0 hΦ₁0
    (by
      intro b b' hfarb
      have hspan : A + 1 ≤ bondSpan y ![b, b'] := by
        rcases hfarb with hb | hb
        · have := siteSupDist_le_bondSpan y ![b, b'] 0
          simp only [Matrix.cons_val_zero] at this
          rw [siteSupDist_comm] at hb
          omega
        · have := siteSupDist_le_bondSpan y ![b, b'] 1
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
          rw [siteSupDist_comm] at hb
          omega
      have hs5 : weightScale F.blockSide ^ 5 ≤ (bondSpan y ![b, b'] : ℝ) :=
        hA1.trans (by exact_mod_cast hspan)
      have hw := pow_le_decayWeight F.blockSide hLp hδ hν1 hs5
      refine (hq1 b b').trans ?_
      rw [div_eq_mul_inv, mul_comm]
      apply mul_le_mul_of_nonneg_right _ hE
      exact inv_anti₀ (pow_pos hν0 _) hw)
    (X 0) (X 1)
    (fun b hb => by
      simp only [hX]
      refine (abs_axialGaugePotential_le y b.1 _ b.2).trans ?_
      exact mul_le_mul_of_nonneg_right hb hΦ₀0)
    (fun b hb => by
      simp only [hX]
      refine (abs_axialGaugePotential_le y b.1 _ b.2).trans ?_
      exact mul_le_mul_of_nonneg_right hb hΦ₁0)
  have hsmall := small_terms_le F.blockSide hs2 ρ hρ1
  have hEΦ : 0 ≤ E * (Φ₀ * Φ₁) := by positivity
  have hsum : |NX| ≤ 2 * (weightScale F.blockSide ^ 8000)⁻¹ * E * (Φ₀ * Φ₁) := by
    have t1 : |NX| ≤ |RX| + |RX - NX| := by
      have := abs_sub_abs_le_abs_sub NX RX
      rw [abs_sub_comm NX RX] at this
      linarith
    have t2 : |RX| ≤ (F.blockSide : ℝ) ^ (-(7000 : ℝ)) * (E * (Φ₀ * Φ₁)) := by
      refine hax.trans (le_of_eq ?_)
      ring
    have t3 : |RX - NX| ≤ ((2 * (ρ : ℝ) + 1) ^ 4 * 4) ^ 2 * ((weightScale F.blockSide ^ 64000)⁻¹ * (R * R)) *
        (E * (Φ₀ * Φ₁)) := by
      refine hrest.trans (le_of_eq ?_)
      ring
    have t4 := mul_le_mul_of_nonneg_right hsmall hEΦ
    rw [add_mul] at t4
    calc |NX| ≤ _ := t1
      _ ≤ _ := add_le_add t2 t3
      _ ≤ _ := t4
      _ = _ := by ring
  have hNN2 : |NN| ≤ |NN - NX| + |NX| := by
    have := abs_sub_abs_le_abs_sub NN NX
    linarith
  calc |NN + Far| ≤ |NN| + |Far| := abs_add_le _ _
    _ ≤ _ := by
      have := add_le_add (hNN2.trans (add_le_add hnear hsum)) hfar
      exact this
theorem sum_mul_le_of_sq {J : Type} (S : Finset J) (u v : J → ℝ) (x z : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hu : ∑ y ∈ S, u y ^ 2 ≤ x ^ 2) (hv : ∑ y ∈ S, v y ^ 2 ≤ z ^ 2) : ∑ y ∈ S, u y * v y ≤ x * z := by
  refine (Real.sum_mul_le_sqrt_mul_sqrt S _ _).trans ?_
  have a : Real.sqrt (∑ y ∈ S, u y ^ 2) ≤ x := Real.sqrt_le_iff.mpr ⟨hx, hu⟩
  have b : Real.sqrt (∑ y ∈ S, v y ^ 2) ≤ z := Real.sqrt_le_iff.mpr ⟨hz, hv⟩
  exact mul_le_mul a b (Real.sqrt_nonneg _) hx
def scaleThresholdTwo (del CS CE C6 C2 C9 : ℝ) : ℝ :=
  max (scaleThreshold del CS CE C6 C2) (max (4800000000 * (C2 * C9 * CE ^ 6)) (2048 * (C6 ^ 2 * CE ^ 6)))
theorem bilinear_near_total_le (ν M C2 C9 CE Gi g₀ g₁ E : ℝ) (hν : 2 ≤ ν) (hM0 : 0 ≤ M)
    (hMb : M ≤ 20000 * ν ^ 25)
    (hC2 : 1 ≤ C2) (hC9 : 1 ≤ C9) (hCE : 1 ≤ CE) (hGi : 0 ≤ Gi) (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁)
    (hP : g₀ * g₁ ≤ CE ^ 6 * Gi) (hE : 0 ≤ E) (hX : 4800000000 * (C2 * C9 * CE ^ 6) ≤ ν) :
    E * ((M * (C9 * (ν ^ 317)⁻¹) * g₀) * (M * C2 * g₁) + (M * C2 * g₀) * (M * (C9 * (ν ^ 317)⁻¹) * g₁) +
      (M * (C9 * (ν ^ 317)⁻¹) * g₀) * (M * (C9 * (ν ^ 317)⁻¹) * g₁)) ≤ 1 / 4 * (ν ^ 160)⁻¹ * E * Gi := by
  have hν0 : 0 < ν := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have hp : 0 < ν ^ 317 := pow_pos hν0 _
  have hZ1 : 1 ≤ C2 * C9 * CE ^ 6 := by
    have a1 : 1 ≤ CE ^ 6 := one_le_pow₀ hCE
    have a2 : 1 ≤ C2 * C9 := by nlinarith
    nlinarith
  set r := C9 * (ν ^ 317)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    have c1 : C9 ≤ C2 * C9 * CE ^ 6 := by
      have a1 : 1 ≤ CE ^ 6 := one_le_pow₀ hCE
      have a2 : C9 ≤ C2 * C9 := le_mul_of_one_le_left (by linarith) hC2
      exact a2.trans (le_mul_of_one_le_right (by positivity) a1)
    have c2 : C9 ≤ ν := by linarith
    have c3 : ν ≤ ν ^ 317 := by
      calc ν = ν ^ 1 := (pow_one ν).symm
        _ ≤ ν ^ 317 := pow_le_pow_right₀ hν1 (by norm_num)
    rw [hr, mul_inv_le_iff₀ hp, one_mul]
    linarith
  have e : (M * r * g₀) * (M * C2 * g₁) + (M * C2 * g₀) * (M * r * g₁) + (M * r * g₀) * (M * r * g₁) =
      M ^ 2 * r * (2 * C2 + r) * (g₀ * g₁) := by ring
  rw [e]
  have h3 : 2 * C2 + r ≤ 3 * C2 := by linarith
  have hM2 : M ^ 2 ≤ (20000 * ν ^ 25) ^ 2 := pow_le_pow_left₀ hM0 hMb 2
  have hgg : 0 ≤ g₀ * g₁ := mul_nonneg hg₀ hg₁
  have b1 : M ^ 2 * r * (2 * C2 + r) * (g₀ * g₁) ≤
      (20000 * ν ^ 25) ^ 2 * r * (3 * C2) * (CE ^ 6 * Gi) := by
    apply mul_le_mul _ hP hgg (by positivity)
    apply mul_le_mul _ h3 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hM2 hr0
  have b2 : (20000 * ν ^ 25) ^ 2 * r * (3 * C2) * (CE ^ 6 * Gi) =
      (1200000000 * (C2 * C9 * CE ^ 6)) * ν ^ 50 * (ν ^ 317)⁻¹ * Gi := by
    rw [hr]; ring
  have b3 : (1200000000 * (C2 * C9 * CE ^ 6)) * ν ^ 50 * (ν ^ 317)⁻¹ ≤ 1 / 4 * (ν ^ 160)⁻¹ := by
    have e2 : ν ^ 317 = ν ^ 50 * (ν ^ 106 * ν) * ν ^ 160 := by ring
    have h84 : ν ≤ ν ^ 106 * ν := le_mul_of_one_le_left hν0.le (one_le_pow₀ hν1)
    have p50 := pow_pos hν0 50
    have p160 := pow_pos hν0 160
    have q : 0 < ν ^ 106 * ν := by positivity
    rw [e2]
    field_simp
    nlinarith
  calc _ ≤ E * ((1200000000 * (C2 * C9 * CE ^ 6)) * ν ^ 50 * (ν ^ 317)⁻¹ * Gi) := by
        rw [← b2]
        exact mul_le_mul_of_nonneg_left b1 hE
    _ ≤ E * (1 / 4 * (ν ^ 160)⁻¹ * Gi) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right b3 hGi) hE
    _ = _ := by ring
theorem bilinear_small_total_le (ν N C6 CE Gi g₀ g₁ E : ℝ) (hν : 2 ≤ ν) (hN0 : 0 ≤ N) (hN : N ≤ ν ^ 2560)
    (hC6 : 1 ≤ C6) (hCE : 1 ≤ CE) (hGi : 0 ≤ Gi) (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁)
    (hP : g₀ * g₁ ≤ CE ^ 6 * Gi) (hE : 0 ≤ E) (hX : 2048 * (C6 ^ 2 * CE ^ 6) ≤ ν) :
    2 * (ν ^ 8000)⁻¹ * E * (N * ((16 * (C6 * (ν ^ 320)⁻¹ * g₀)) * (16 * (C6 * (ν ^ 320)⁻¹ * g₁)))) ≤
      1 / 4 * (ν ^ 160)⁻¹ * E * Gi := by
  have hν0 : 0 < ν := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have hp1 : (ν ^ 320)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hν1)
  have hp0 : 0 ≤ (ν ^ 320)⁻¹ := inv_nonneg.mpr (pow_nonneg hν0.le _)
  have hgg : 0 ≤ g₀ * g₁ := mul_nonneg hg₀ hg₁
  have e : 2 * (ν ^ 8000)⁻¹ * E * (N * ((16 * (C6 * (ν ^ 320)⁻¹ * g₀)) * (16 * (C6 * (ν ^ 320)⁻¹ * g₁)))) =
      E * ((512 * C6 ^ 2) * (N * (ν ^ 8000)⁻¹) * ((ν ^ 320)⁻¹ ^ 2 * (g₀ * g₁))) := by ring
  rw [e]
  have h2 : (ν ^ 320)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ hp0 hp1
  have hNν : N * (ν ^ 8000)⁻¹ ≤ (ν ^ 5440)⁻¹ := by
    have e2 : ν ^ 8000 = ν ^ 2560 * ν ^ 5440 := by rw [← pow_add]
    rw [e2, mul_inv, ← mul_assoc]
    apply mul_le_of_le_one_left (inv_nonneg.mpr (pow_nonneg hν0.le _))
    rw [mul_inv_le_iff₀ (pow_pos hν0 _), one_mul]
    exact hN
  have hfinal : (512 * C6 ^ 2) * (ν ^ 5440)⁻¹ * (CE ^ 6) ≤ 1 / 4 * (ν ^ 160)⁻¹ := by
    have e3 : ν ^ 5440 = (ν ^ 5279 * ν) * ν ^ 160 := by ring
    have h84 : ν ≤ ν ^ 5279 * ν := le_mul_of_one_le_left hν0.le (one_le_pow₀ hν1)
    rw [e3]
    field_simp
    nlinarith
  have b1 : (512 * C6 ^ 2) * (N * (ν ^ 8000)⁻¹) * ((ν ^ 320)⁻¹ ^ 2 * (g₀ * g₁)) ≤
      (512 * C6 ^ 2) * (ν ^ 5440)⁻¹ * (1 * (CE ^ 6 * Gi)) := by
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · exact mul_le_mul_of_nonneg_left hNν (by positivity)
    · exact mul_le_mul h2 hP hgg zero_le_one
  calc _ ≤ E * ((512 * C6 ^ 2) * (ν ^ 5440)⁻¹ * (1 * (CE ^ 6 * Gi))) := mul_le_mul_of_nonneg_left b1 hE
    _ = E * (((512 * C6 ^ 2) * (ν ^ 5440)⁻¹ * CE ^ 6) * Gi) := by ring
    _ ≤ E * (1 / 4 * (ν ^ 160)⁻¹ * Gi) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfinal hGi) hE
    _ = _ := by ring
theorem shift_rate_le (ν A L C9 : ℝ) (hν : 2 ≤ ν) (hL : L = ν ^ 640) (hA0 : 0 ≤ A) (hA : A ≤ 2 * ν ^ 5)
    (hC9 : 1 ≤ C9) :
    C9 * (A / L) ≤ (C9 * (ν ^ 317)⁻¹) ^ 2 := by
  have hν0 : 0 < ν := by linarith
  have p2 : 0 < ν ^ 640 := pow_pos hν0 _
  have e : (C9 * (ν ^ 317)⁻¹) ^ 2 = C9 ^ 2 * (ν ^ 634)⁻¹ := by
    rw [mul_pow, inv_pow, ← pow_mul]
  rw [e, hL]
  have a1 : A / ν ^ 640 ≤ (ν ^ 634)⁻¹ := by
    rw [div_le_iff₀ p2]
    have e2 : ν ^ 640 = ν ^ 634 * ν ^ 5 * ν := by ring
    rw [e2]
    have : (ν ^ 634)⁻¹ * (ν ^ 634 * ν ^ 5 * ν) = ν ^ 5 * ν := by field_simp
    rw [this]
    nlinarith
  have a2 : C9 ≤ C9 ^ 2 := by nlinarith
  exact mul_le_mul a2 a1 (div_nonneg hA0 p2.le) (sq_nonneg _)
theorem sum_abs_plaquetteCurl_le {a del CS CE C6 C2 C9 : ℝ} {L₁ : ℕ}
    (hN : FlatConstants a del CS CE C6 C2 C9 L₁)
    (F : BlockFrame) (Y : F.Cell) (c : F.Site F.top × Fin 4) (B : FormChain F) (W : LevelForm F F.depth)
    (hodd : Odd F.blockSide) (hL₁ : L₁ ≤ F.blockSide) (hcub : IsLargeCubicTorus F) (hf : IsFlatChain a c B)
    (ht : IsAxialResponse c B W) (hν0 : 0 < weightScale F.blockSide) (y : F.Site F.depth)
    (hy : y ∈ blockFineSites Y) :
    ∑ μ, ∑ ν, |plaquetteCurl W y μ ν| ≤
      16 * (C6 * (weightScale F.blockSide ^ 320)⁻¹ * Real.sqrt (chainEnergyOnCells a B (cellBall Y 24))) := by
  have hC6 := hN.one_le_curlConst
  set D := C6 * (weightScale F.blockSide ^ 320)⁻¹ * Real.sqrt (chainEnergyOnCells a B (cellBall Y 24)) with hD
  have hD0 : 0 ≤ D := by positivity
  have hcell : cellSupDist (enclosingCell y) Y ≤ 2 := by
    rw [enclosingCell_of_mem Y y hy]
    simp [cellSupDist, ZMod.valMinAbs_zero]
  have hlt : ∀ μ ν : Fin 4, μ < ν → |plaquetteCurl W y μ ν| ≤ D := by
    intro μ ν hμν
    have h1 := ht.curl_eq y (μ, ν) (mem_orientedPlanes hμν)
    have h2 := hN.curl_bound F c B hodd hL₁ hcub hf Y y (μ, ν) (mem_orientedPlanes hμν) hcell
    rw [blockSide_rpow_neg_half F.blockSide hν0] at h2
    simp only at h1 h2
    rw [h1]
    exact h2
  have hall : ∀ μ ν : Fin 4, |plaquetteCurl W y μ ν| ≤ D := by
    intro μ ν
    rcases lt_trichotomy μ ν with h | h | h
    · exact hlt μ ν h
    · subst h
      have : plaquetteCurl W y μ μ = 0 := by simp [plaquetteCurl]
      rw [this, abs_zero]
      exact hD0
    · rw [plaquetteCurl_antisymm, abs_neg]
      exact hlt ν μ h
  calc _ ≤ ∑ _μ : Fin 4, ∑ _ν : Fin 4, D :=
        Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => hall μ ν
    _ = 16 * D := by simp; ring
theorem bilinear_sum_le {a del CS CE C6 C2 C9 : ℝ} {L₁ : ℕ} (hN : FlatConstants a del CS CE C6 C2 C9 L₁)
    (F : BlockFrame) (δ E : ℝ) (Y : F.Cell) (c : Fin 2 → F.Site F.top × Fin 4) (B : Fin 2 → FormChain F)
    (W : Fin 2 → LevelForm F F.depth)
    (q : F.Site F.depth → F.Site F.depth × Fin 4 → F.Site F.depth × Fin 4 → ℝ)
    (hodd : Odd F.blockSide) (hL₁ : L₁ ≤ F.blockSide) (hcub : IsLargeCubicTorus F) (hδ : 0 < δ)
    (hδd : δ ≤ del / 64) (hE : 0 ≤ E)
    (hf : ∀ i, IsFlatChain a (c i) (B i)) (ht : ∀ i, IsAxialResponse (c i) (B i) (W i))
    (hq0 : ∀ y (A : LevelForm F F.depth) (φ : F.Site F.depth → ℝ),
      bondPairing (q y) (addGradient (fun _ _ => 0) φ) A = 0 ∧
      bondPairing (q y) A (addGradient (fun _ _ => 0) φ) = 0)
    (hq1 : ∀ y b b', |q y b b'| ≤ E / torusDecayFactor F.blockSide δ (bondSpan y ![b, b']))
    (hq2 : ∀ y (Fm Fm' : Fin 4 → Fin 4 → ℝ), (∀ μ ν, Fm μ ν = - Fm ν μ) → (∀ μ ν, Fm' μ ν = - Fm' ν μ) →
      |∑ b ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
        ∑ b' ∈ (fineBonds F).filter (fun b => (siteSupDist b.1 y : ℝ) ≤ Real.sqrt F.blockSide),
          q y b b' * axialGaugePotential y Fm b.1 b.2 * axialGaugePotential y Fm' b'.1 b'.2| ≤
        (F.blockSide : ℝ) ^ (-(7000 : ℝ)) * E * (∑ μ, ∑ ν, |Fm μ ν|) * ∑ μ, ∑ ν, |Fm' μ ν|)
    (hfl : scaleThresholdTwo del CS CE C6 C2 C9 ≤ weightScale F.blockSide) :
    |∑ y ∈ blockFineSites Y, bondPairing (q y) (W 0) (W 1)| ≤
      (weightScale F.blockSide ^ 160)⁻¹ * E / torusDecayFactor F.blockSide δ (bondSpan Y c) := by
  have hg := isAdmissible_of hodd hcub
  have hfl1 : scaleThreshold del CS CE C6 C2 ≤ weightScale F.blockSide := (le_max_left _ _).trans hfl
  have hX1 : 4800000000 * (C2 * C9 * CE ^ 6) ≤ weightScale F.blockSide :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hfl
  have hX2 : 2048 * (C6 ^ 2 * CE ^ 6) ≤ weightScale F.blockSide :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hfl
  obtain ⟨hs2, hsd, hsT, hsX⟩ := scaleThreshold_facts hfl1
  obtain ⟨hA1, hAR, hA64, hAL, hM, hR1, hRL⟩ := weightScale_facts F.blockSide hs2
  have hν0 : 0 < weightScale F.blockSide := by linarith
  have hν1 : 1 ≤ weightScale F.blockSide := by linarith
  have hAν : (⌈weightScale F.blockSide ^ 5⌉₊ : ℝ) ≤ 2 * weightScale F.blockSide ^ 5 := by
    have a1 : (⌈weightScale F.blockSide ^ 5⌉₊ : ℝ) < weightScale F.blockSide ^ 5 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have a2 : 1 ≤ weightScale F.blockSide ^ 5 := one_le_pow₀ hν1
    linarith
  have hCE := hN.one_le_energyConst
  have hC6 := hN.one_le_curlConst
  have hC2 := hN.one_le_squareConst
  have hC9 := hN.one_le_shiftConst
  have hGn0 : 0 < torusDecayFactor F.blockSide δ (bondSpan Y c) := decayWeight_pos _ _ _
  have hGi : 0 ≤ (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by positivity
  generalize ⌈weightScale F.blockSide ^ 5⌉₊ = A at *
  have hM0 : (0 : ℝ) ≤ (stripIndices A).card := Nat.cast_nonneg _
  have hLr : (F.blockSide : ℝ) = weightScale F.blockSide ^ 640 := (weightScale_pow F.blockSide).symm
  have hdr := shift_rate_le (weightScale F.blockSide) A F.blockSide C9 hs2 hLr (Nat.cast_nonneg _) hAν hC9
  set e : Fin 2 → ℝ := fun l => chainEnergyOnCells a (B l) (cellBall Y 24) with he
  have he0 : ∀ l, 0 ≤ e l := fun l => chainEnergyOnCells_nonneg hN.coupling_pos _ _
  set g : Fin 2 → ℝ := fun l => Real.sqrt (e l) with hgdef
  have hg0 : ∀ l, 0 ≤ g l := fun l => Real.sqrt_nonneg _
  set M : ℝ := ((stripIndices A).card : ℝ) with hMdef
  set r := C9 * (weightScale F.blockSide ^ 317)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hs : ∀ l, ∑ y ∈ blockFineSites Y, stripTotal A (curlMagnitudes (W l) y) ^ 2 ≤ (M * C2 * g l) ^ 2 := by
    intro l
    have := (stripTotal_bounds hN F Y (c l) (B l) (W l) hodd hL₁ hcub (hf l) (ht l) A hAL hν0).1
    rw [mul_pow (M * C2)]
    exact this
  have hd : ∀ l, ∑ y ∈ blockFineSites Y, stripTotal A (curlIncrements (W l) y) ^ 2 ≤ (M * r * g l) ^ 2 := by
    intro l
    have a1 := sum_stripTotal_sq_le (blockFineSites Y) A (fun y => curlIncrements (W l) y)
      (C9 * ((A : ℝ) / F.blockSide) * e l)
      (mul_nonneg (mul_nonneg (by linarith) (by positivity)) (he0 l))
      (fun v i k hik hv => sum_curlIncrements_sq_le hN F Y (c l) (B l) (W l) hodd hL₁ hcub (hf l) (ht l) A hAL
        v i k hik hv)
    refine a1.trans ?_
    rw [mul_pow (M * r), mul_pow M r, Real.sq_sqrt (he0 l)]
    calc M ^ 2 * (C9 * ((A : ℝ) / F.blockSide) * e l) ≤ M ^ 2 * (r ^ 2 * e l) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right hdr (he0 l)
      _ = _ := by ring
  have hprod : g 0 * g 1 ≤ CE ^ 6 * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by
    have := prod_sqrt_energy_le hN F δ Y 2 c B (by norm_num) hodd hL₁ hcub hδ.le hδd hf hsd
    rwa [Fin.prod_univ_two] at this
  have hsum01 := sum_mul_le_of_sq (blockFineSites Y) (fun y => stripTotal A (curlIncrements (W 0) y))
    (fun y => stripTotal A (curlMagnitudes (W 1) y)) _ _ (by have := hg0 0; positivity)
    (by have := hg0 1; positivity) (hd 0) (hs 1)
  have hsum10 := sum_mul_le_of_sq (blockFineSites Y) (fun y => stripTotal A (curlMagnitudes (W 0) y))
    (fun y => stripTotal A (curlIncrements (W 1) y)) _ _ (by have := hg0 0; positivity)
    (by have := hg0 1; positivity) (hs 0) (hd 1)
  have hsum11 := sum_mul_le_of_sq (blockFineSites Y) (fun y => stripTotal A (curlIncrements (W 0) y))
    (fun y => stripTotal A (curlIncrements (W 1) y)) _ _ (by have := hg0 0; positivity)
    (by have := hg0 1; positivity) (hd 0) (hd 1)
  set p := (weightScale F.blockSide ^ 320)⁻¹ with hp
  have hp0 : 0 ≤ p := by positivity
  set p' := (weightScale F.blockSide ^ 8000)⁻¹ with hp'
  have hp'0 : 0 ≤ p' := by positivity
  have hΦ : ∑ y ∈ blockFineSites Y,
      ((∑ μ, ∑ ν, |plaquetteCurl (W 0) y μ ν|) * ∑ μ, ∑ ν, |plaquetteCurl (W 1) y μ ν|) ≤
      ((blockFineSites Y).card : ℝ) * ((16 * (C6 * p * g 0)) * (16 * (C6 * p * g 1))) := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro y hy
    apply mul_le_mul
    · exact sum_abs_plaquetteCurl_le hN F Y (c 0) (B 0) (W 0) hodd hL₁ hcub (hf 0) (ht 0) hν0 y hy
    · exact sum_abs_plaquetteCurl_le hN F Y (c 1) (B 1) (W 1) hodd hL₁ hcub (hf 1) (ht 1) hν0 y hy
    · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    · have := hg0 0
      positivity
  have hN1 := bilinear_near_total_le (weightScale F.blockSide) M C2 C9 CE _ (g 0) (g 1) E hs2 hM0 hM hC2 hC9
    hCE hGi (hg0 0) (hg0 1) hprod hE hX1
  have hN2 := bilinear_small_total_le (weightScale F.blockSide) ((blockFineSites Y).card) C6 CE _ (g 0) (g 1) E
    hs2 (Nat.cast_nonneg _) (card_blockFineSites_le_pow hg Y) hC6 hCE hGi (hg0 0) (hg0 1) hprod hE hX2
  have hN3 := far_total_le (weightScale F.blockSide) ((blockFineSites Y).card) _ 2 hs2 (Nat.cast_nonneg _)
    (card_blockFineSites_le_pow hg Y) (by norm_num) hGi
  have hpt : ∀ y ∈ blockFineSites Y, |bondPairing (q y) (W 0) (W 1)| ≤ _ := fun y hy =>
    abs_bondPairing_at_site_le hN F δ E Y c B W hodd hL₁ hcub hδ.le hδd hE hf ht hfl1 A hA1 hAR hA64 hR1 hRL
      y hy (q y) (hq0 y) (hq1 y) (hq2 y)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hpt).trans ?_)
  have hEF : 0 ≤ E * (4 * (weightScale F.blockSide ^ 64000)⁻¹ * (weightScale F.blockSide ^ 6400) ^ 2 *
      (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹) := by positivity
  have e1 : ∀ y, E * (stripTotal A (curlIncrements (W 0) y) * stripTotal A (curlMagnitudes (W 1) y) +
        (stripTotal A (curlMagnitudes (W 0) y) + stripTotal A (curlIncrements (W 0) y)) *
          stripTotal A (curlIncrements (W 1) y)) =
      E * (stripTotal A (curlIncrements (W 0) y) * stripTotal A (curlMagnitudes (W 1) y)) +
      E * (stripTotal A (curlMagnitudes (W 0) y) * stripTotal A (curlIncrements (W 1) y)) +
      E * (stripTotal A (curlIncrements (W 0) y) * stripTotal A (curlIncrements (W 1) y)) := fun y => by ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have c1 := mul_le_mul_of_nonneg_left hsum01 hE
  have c2 := mul_le_mul_of_nonneg_left hsum10 hE
  have c3 := mul_le_mul_of_nonneg_left hsum11 hE
  have c4 : 2 * p' * E * ∑ y ∈ blockFineSites Y,
      ((∑ μ, ∑ ν, |plaquetteCurl (W 0) y μ ν|) * ∑ μ, ∑ ν, |plaquetteCurl (W 1) y μ ν|) ≤
      2 * p' * E * (((blockFineSites Y).card : ℝ) * ((16 * (C6 * p * g 0)) * (16 * (C6 * p * g 1)))) :=
    mul_le_mul_of_nonneg_left hΦ (by positivity)
  have c5 : ((blockFineSites Y).card : ℝ) * (E * (4 * (weightScale F.blockSide ^ 64000)⁻¹ *
      (weightScale F.blockSide ^ 6400) ^ 2 * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹)) ≤
      E * (1 / 2 * (weightScale F.blockSide ^ 160)⁻¹ * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹) := by
    have := mul_le_mul_of_nonneg_left hN3 hE
    calc _ = E * (((blockFineSites Y).card : ℝ) * (4 * (weightScale F.blockSide ^ 64000)⁻¹ *
          (weightScale F.blockSide ^ 6400) ^ 2 * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹)) := by ring
      _ ≤ _ := this
  have c6 : (weightScale F.blockSide ^ 160)⁻¹ * E / torusDecayFactor F.blockSide δ (bondSpan Y c) =
      1 / 4 * (weightScale F.blockSide ^ 160)⁻¹ * E * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ +
      1 / 4 * (weightScale F.blockSide ^ 160)⁻¹ * E * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ +
      E * (1 / 2 * (weightScale F.blockSide ^ 160)⁻¹ * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹) := by
    rw [div_eq_mul_inv]; ring
  rw [c6]
  have c7 : E * ((M * r * g 0) * (M * C2 * g 1)) + E * ((M * C2 * g 0) * (M * r * g 1)) +
      E * ((M * r * g 0) * (M * r * g 1)) ≤
      1 / 4 * (weightScale F.blockSide ^ 160)⁻¹ * E * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by
    refine le_trans (le_of_eq ?_) hN1
    ring
  linarith
theorem blockSide_rpow_fifty (L : ℕ) (hν : 0 < weightScale L) :
    (L : ℝ) ^ (50 / 640 : ℝ) = weightScale L ^ 50 := by
  rw [← weightScale_pow L, ← Real.rpow_natCast (weightScale L) 640, ← Real.rpow_mul hν.le,
    ← Real.rpow_natCast (weightScale L) 50]
  norm_num
theorem plain_total_le (ν M C2 CE Gi g₀ g₁ : ℝ) (hν : 2 ≤ ν) (hM0 : 0 ≤ M) (hMb : M ≤ 20000 * ν ^ 25)
    (hC2 : 1 ≤ C2) (hCE : 1 ≤ CE) (hGi : 0 ≤ Gi) (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁)
    (hP : g₀ * g₁ ≤ CE ^ 6 * Gi) :
    (M * C2 * g₀) * (M * C2 * g₁) + 1 / 2 * (ν ^ 160)⁻¹ * Gi ≤
      (400000000 * C2 ^ 2 * CE ^ 6 + 1) * ν ^ 50 * Gi := by
  have hν1 : 1 ≤ ν := by linarith
  have hM2 : M ^ 2 ≤ (20000 * ν ^ 25) ^ 2 := pow_le_pow_left₀ hM0 hMb 2
  have hgg : 0 ≤ g₀ * g₁ := mul_nonneg hg₀ hg₁
  have e : (M * C2 * g₀) * (M * C2 * g₁) = M ^ 2 * C2 ^ 2 * (g₀ * g₁) := by ring
  have b1 : M ^ 2 * C2 ^ 2 * (g₀ * g₁) ≤ (20000 * ν ^ 25) ^ 2 * C2 ^ 2 * (CE ^ 6 * Gi) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hM2 (sq_nonneg _)) hP hgg (by positivity)
  have b2 : (20000 * ν ^ 25) ^ 2 * C2 ^ 2 * (CE ^ 6 * Gi) = 400000000 * C2 ^ 2 * CE ^ 6 * ν ^ 50 * Gi := by ring
  have b3 : 1 / 2 * (ν ^ 160)⁻¹ ≤ ν ^ 50 := by
    have a1 : (ν ^ 160)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hν1)
    have a2 : 1 ≤ ν ^ 50 := one_le_pow₀ hν1
    linarith
  have b4 := mul_le_mul_of_nonneg_right b3 hGi
  rw [e]
  calc _ ≤ 400000000 * C2 ^ 2 * CE ^ 6 * ν ^ 50 * Gi + ν ^ 50 * Gi := by
        rw [← b2]
        exact add_le_add b1 b4
    _ = _ := by ring
theorem plain_bilinear_sum_le {a del CS CE C6 C2 C9 : ℝ} {L₁ : ℕ} (hN : FlatConstants a del CS CE C6 C2 C9 L₁)
    (F : BlockFrame) (δ : ℝ) (Y : F.Cell) (c : Fin 2 → F.Site F.top × Fin 4) (B : Fin 2 → FormChain F)
    (W : Fin 2 → LevelForm F F.depth) (hodd : Odd F.blockSide) (hL₁ : L₁ ≤ F.blockSide) (hcub : IsLargeCubicTorus F)
    (hδ : 0 < δ) (hδd : δ ≤ del / 64) (hf : ∀ i, IsFlatChain a (c i) (B i))
    (ht : ∀ i, IsAxialResponse (c i) (B i) (W i))
    (hfl : scaleThreshold del CS CE C6 C2 ≤ weightScale F.blockSide) :
    ∑ y ∈ blockFineSites Y, ∑ b₁ ∈ fineBonds F, ∑ b₂ ∈ fineBonds F,
      (torusDecayFactor F.blockSide δ (bondSpan y ![b₁, b₂]))⁻¹ *
        |localAxialGauge (Real.sqrt F.blockSide) y (W 0) b₁.1 b₁.2| *
        |localAxialGauge (Real.sqrt F.blockSide) y (W 1) b₂.1 b₂.2| ≤
      (400000000 * C2 ^ 2 * CE ^ 6 + 1) * weightScale F.blockSide ^ 50 /
        torusDecayFactor F.blockSide δ (bondSpan Y c) := by
  have hg := isAdmissible_of hodd hcub
  obtain ⟨hs2, hsd, hsT, hsX⟩ := scaleThreshold_facts hfl
  obtain ⟨hA1, hAR, hA64, hAL, hM, hR1, hRL⟩ := weightScale_facts F.blockSide hs2
  have hν0 : 0 < weightScale F.blockSide := by linarith
  have hCE := hN.one_le_energyConst
  have hC2 := hN.one_le_squareConst
  have hGn0 : 0 < torusDecayFactor F.blockSide δ (bondSpan Y c) := decayWeight_pos _ _ _
  have hGi : 0 ≤ (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by positivity
  generalize ⌈weightScale F.blockSide ^ 5⌉₊ = A at *
  have hM0 : (0 : ℝ) ≤ (stripIndices A).card := Nat.cast_nonneg _
  have hs : ∀ l, ∑ y ∈ blockFineSites Y, stripTotal A (curlMagnitudes (W l) y) ^ 2 ≤
      (((stripIndices A).card : ℝ) * C2 * Real.sqrt (chainEnergyOnCells a (B l) (cellBall Y 24))) ^ 2 := by
    intro l
    have := (stripTotal_bounds hN F Y (c l) (B l) (W l) hodd hL₁ hcub (hf l) (ht l) A hAL hν0).1
    rw [mul_pow (((stripIndices A).card : ℝ) * C2)]
    exact this
  have hcs := sum_mul_le_of_sq (blockFineSites Y) (fun y => stripTotal A (curlMagnitudes (W 0) y))
    (fun y => stripTotal A (curlMagnitudes (W 1) y)) _ _
    (mul_nonneg (mul_nonneg hM0 (by linarith)) (Real.sqrt_nonneg _))
    (mul_nonneg (mul_nonneg hM0 (by linarith)) (Real.sqrt_nonneg _)) (hs 0) (hs 1)
  have hprod : Real.sqrt (chainEnergyOnCells a (B 0) (cellBall Y 24)) *
      Real.sqrt (chainEnergyOnCells a (B 1) (cellBall Y 24)) ≤
      CE ^ 6 * (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by
    have := prod_sqrt_energy_le hN F δ Y 2 c B (by norm_num) hodd hL₁ hcub hδ.le hδd hf hsd
    rwa [Fin.prod_univ_two] at this
  have hfar := far_total_le (weightScale F.blockSide) ((blockFineSites Y).card) _ 2 hs2 (Nat.cast_nonneg _)
    (card_blockFineSites_le_pow hg Y) (by norm_num) hGi
  have hpl := plain_total_le (weightScale F.blockSide) ((stripIndices A).card) C2 CE _ _ _ hs2 hM0 hM hC2 hCE
    hGi (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hprod
  have hpt : ∀ y ∈ blockFineSites Y, ∑ b₁ ∈ fineBonds F, ∑ b₂ ∈ fineBonds F,
      (torusDecayFactor F.blockSide δ (bondSpan y ![b₁, b₂]))⁻¹ *
        |localAxialGauge (Real.sqrt F.blockSide) y (W 0) b₁.1 b₁.2| *
        |localAxialGauge (Real.sqrt F.blockSide) y (W 1) b₂.1 b₂.2| ≤
      stripTotal A (curlMagnitudes (W 0) y) * stripTotal A (curlMagnitudes (W 1) y) +
        4 * (weightScale F.blockSide ^ 64000)⁻¹ * (weightScale F.blockSide ^ 6400) ^ 2 *
          (torusDecayFactor F.blockSide δ (bondSpan Y c))⁻¹ := by
    intro y hy
    have h1 := sum_tuples_at_site_le hN F δ Y 2 c B W (by norm_num) hodd hL₁ hcub hδ.le hδd hf ht hfl A hA1 hAR
      hA64 hR1 hRL y hy
    rw [Fin.prod_univ_two] at h1
    refine le_trans (le_of_eq ?_) h1
    rw [← sum_piFinset_two (fineBonds F) (fun b₁ b₂ => (torusDecayFactor F.blockSide δ (bondSpan y ![b₁, b₂]))⁻¹ *
      |localAxialGauge (Real.sqrt F.blockSide) y (W 0) b₁.1 b₁.2| *
      |localAxialGauge (Real.sqrt F.blockSide) y (W 1) b₂.1 b₂.2|)]
    apply Finset.sum_congr rfl
    intro β _
    have e : (![β 0, β 1] : Fin 2 → F.Site F.depth × Fin 4) = β := by
      funext l
      fin_cases l <;> rfl
    rw [e, Fin.prod_univ_two]
    ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  exact (add_le_add hcs hfar).trans hpl
theorem le_weightScale_of_le (ν₀ : ℝ) (h0 : 0 ≤ ν₀) (L : ℕ) (h : ⌈ν₀⌉₊ ^ 640 ≤ L) : ν₀ ≤ weightScale L := by
  have hs0 : 0 ≤ weightScale L := by unfold weightScale; positivity
  have a1 : ν₀ ^ 640 ≤ weightScale L ^ 640 := by
    rw [weightScale_pow]
    calc ν₀ ^ 640 ≤ (⌈ν₀⌉₊ : ℝ) ^ 640 := pow_le_pow_left₀ h0 (Nat.le_ceil _) _
      _ ≤ L := by exact_mod_cast h
  exact (pow_le_pow_iff_left₀ h0 hs0 (by norm_num)).mp a1
theorem scaleThreshold_nonneg (del CS CE C6 C2 : ℝ) : 0 ≤ scaleThreshold del CS CE C6 C2 :=
  le_trans (by norm_num) (le_max_left _ _)
theorem scaleThresholdTwo_nonneg (del CS CE C6 C2 C9 : ℝ) : 0 ≤ scaleThresholdTwo del CS CE C6 C2 C9 :=
  le_trans (scaleThreshold_nonneg _ _ _ _ _) (le_max_left _ _)
theorem flatResponseSumBounds_holds (hS : axialResponseDecay)
    (hE : flatChainEnergyNearCell) (h9 : CurlShiftBound)
    (h6 : CurlSizeBound) (h2 : CurlSquareSumBound) :
    YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSumBounds := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨del, CS, CE, C6, C2, C9, L₁, hN⟩ := exists_flatConstants hS hE h9 h6 h2 a ha
    refine ⟨del, hN.rate_pos, max L₁ (⌈scaleThreshold del CS CE C6 C2⌉₊ ^ 640), ?_⟩
    intro F δ Y k c B W hk3 hk6 hodd hL hcub hδ hδd hf ht
    have hfl := le_weightScale_of_le _ (scaleThreshold_nonneg del CS CE C6 C2) F.blockSide
      ((le_max_right _ _).trans hL)
    have hs2 : 2 ≤ weightScale F.blockSide := (scaleThreshold_facts hfl).1
    unfold YangMills.Construction.Interpolation.flatResponseSum
    rw [blockSide_rpow_neg_quarter F.blockSide (by linarith)]
    exact multilinear_sum_le hN F δ Y k c B W hk3 hk6 hodd ((le_max_left _ _).trans hL) hcub hδ hδd hf ht hfl
  · intro a ha
    obtain ⟨del, CS, CE, C6, C2, C9, L₁, hN⟩ := exists_flatConstants hS hE h9 h6 h2 a ha
    refine ⟨del, hN.rate_pos, max L₁ (⌈scaleThresholdTwo del CS CE C6 C2 C9⌉₊ ^ 640), ?_⟩
    intro F δ E Y c B W q hodd hL hcub hδ hδd hE0 hf ht hq0 hq1 hq2
    have hfl := le_weightScale_of_le _ (scaleThresholdTwo_nonneg del CS CE C6 C2 C9) F.blockSide
      ((le_max_right _ _).trans hL)
    have hs2 : 2 ≤ weightScale F.blockSide := (scaleThreshold_facts ((le_max_left _ _).trans hfl)).1
    rw [blockSide_rpow_neg_quarter F.blockSide (by linarith)]
    exact bilinear_sum_le hN F δ E Y c B W q hodd ((le_max_left _ _).trans hL) hcub hδ hδd hE0 hf ht hq0 hq1 hq2
      hfl
  · intro a ha
    obtain ⟨del, CS, CE, C6, C2, C9, L₁, hN⟩ := exists_flatConstants hS hE h9 h6 h2 a ha
    have hC2 := hN.one_le_squareConst
    have hCE := hN.one_le_energyConst
    refine ⟨del, 400000000 * C2 ^ 2 * CE ^ 6 + 1, hN.rate_pos, by positivity,
      max L₁ (⌈scaleThreshold del CS CE C6 C2⌉₊ ^ 640), ?_⟩
    intro F δ Y c B W hodd hL hcub hδ hδd hf ht
    have hfl := le_weightScale_of_le _ (scaleThreshold_nonneg del CS CE C6 C2) F.blockSide
      ((le_max_right _ _).trans hL)
    have hs2 : 2 ≤ weightScale F.blockSide := (scaleThreshold_facts hfl).1
    rw [blockSide_rpow_fifty F.blockSide (by linarith)]
    exact plain_bilinear_sum_le hN F δ Y c B W hodd ((le_max_left _ _).trans hL) hcub hδ hδd hf ht hfl
end YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums
end
