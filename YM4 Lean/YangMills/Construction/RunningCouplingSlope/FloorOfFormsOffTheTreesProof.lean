import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormulaProof
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.ClusterExpansionOfAStep.BlocksOnATorus
import YangMills.Construction.HoleBesideASecondHole.CellsLeftOffTheSpotsProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.RunningCouplingSlope.FloorOfFormsOffTheTrees
import YangMills.Construction.RunningCouplingSlope.OperatorsOfAStepAtTheFlatField
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
noncomputable section
open YangMills.Construction.LatticeFractionalIntegration (basisVector)
open YangMills.Construction.FlatPairing (stepDisplacement)
open YangMills.Construction.FlatLinearization (LatticeOneForm RealOneForm latticeLineSum pathIntegral stepEndpoint
  plaquetteCurl curlEnergy contourAverage coarseSite offsetFromCentre IsBlockTreeBond CrossesBlockBoundary
  VanishesOnBlockTrees)
open YangMills.Construction.BlockAverages (PathStep axisPath reversePath bondContour centredCube)
open YangMills.Construction.TorusFields (TorusSite TorusBond unitStep siteOfInt)
open YangMills.Construction.TorusBlocks (blockCentreSite parentBlock_blockCentreSite_add parentBlock_blockCentreSite
  exists_eq_blockCentreSite_add)
open YangMills.Construction.TorusLumps (parentBlock siteOfInt_zero_offset)
namespace YangMills.Construction.RunningCouplingSlope.OffTreeForms
private def InBox (r : ℕ) (z : Fin 4 → ℤ) : Prop := ∀ i, |z i| ≤ (r : ℤ)
private def latticeCurl (η : LatticeOneForm) (z : Fin 4 → ℤ) (μ ν : Fin 4) : ℝ :=
  η (z, μ) + η (z + basisVector μ, ν) - η (z + basisVector ν, μ) - η (z, ν)
private def translateForm (η : LatticeOneForm) (w : Fin 4 → ℤ) : LatticeOneForm := fun b => η (b.1 + w, b.2)
private theorem basisVector_apply (i j : Fin 4) : basisVector i j = if j = i then 1 else 0 := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.StaircaseHomotopy.basisVector_apply <;> assumption
private theorem inBox_add_smul {r : ℕ} {h : Fin 4 → ℤ} (hh : InBox r h) (μ : Fin 4) (c : ℤ)
    (hc : |h μ + c| ≤ (r : ℤ)) : InBox r (h + c • basisVector μ) := by
  intro i
  rcases eq_or_ne i μ with rfl | e
  · simpa [basisVector_apply] using hc
  · simpa [basisVector_apply, e] using hh i
private theorem inBox_add_basis {r : ℕ} {z : Fin 4 → ℤ} (hz : InBox r z) {l : Fin 4} (hl : z l < 0) :
    InBox r (z + basisVector l) := by
  have h := inBox_add_smul hz l 1 (by
    have := abs_le.mp (hz l)
    exact abs_le.mpr ⟨by omega, by omega⟩)
  simpa using h
private theorem inBox_sub_basis {r : ℕ} {z : Fin 4 → ℤ} (hz : InBox r z) {l : Fin 4} (hl : 0 < z l) :
    InBox r (z - basisVector l) := by
  have h := inBox_add_smul hz l (-1) (by
    have := abs_le.mp (hz l)
    exact abs_le.mpr ⟨by omega, by omega⟩)
  simpa [sub_eq_add_neg] using h
private def coordWeight (P : Fin 4 → Prop) [DecidablePred P] (z : Fin 4 → ℤ) : ℕ :=
  ∑ l, if P l then (z l).natAbs else 0
private theorem sum_succ_le_of_lt (f g : Fin 4 → ℕ) (l : Fin 4) (h : g l + 1 ≤ f l) (h' : ∀ i, i ≠ l → g i ≤ f i) :
    ∑ i, g i + 1 ≤ ∑ i, f i := by
  rw [← Finset.add_sum_erase _ g (Finset.mem_univ l), ← Finset.add_sum_erase _ f (Finset.mem_univ l)]
  have : ∑ i ∈ Finset.univ.erase l, g i ≤ ∑ i ∈ Finset.univ.erase l, f i :=
    Finset.sum_le_sum fun i hi => h' i (Finset.ne_of_mem_erase hi)
  omega
private theorem coordWeight_succ_le (P : Fin 4 → Prop) [DecidablePred P] {z z' : Fin 4 → ℤ} {l : Fin 4} (hP : P l)
    (h : (z' l).natAbs + 1 ≤ (z l).natAbs) (h' : ∀ i, i ≠ l → z' i = z i) :
    coordWeight P z' + 1 ≤ coordWeight P z := by
  refine sum_succ_le_of_lt _ _ l ?_ fun i hi => ?_
  · simpa [hP] using h
  · simp [h' i hi]
private theorem coordWeight_add_basis (P : Fin 4 → Prop) [DecidablePred P] {z : Fin 4 → ℤ} {l : Fin 4} (hP : P l)
    (hl : z l < 0) : coordWeight P (z + basisVector l) + 1 ≤ coordWeight P z := by
  refine coordWeight_succ_le P hP ?_ fun i hi => ?_
  · simp only [Pi.add_apply, basisVector_apply, if_true]
    omega
  · simp [basisVector_apply, hi]
private theorem coordWeight_sub_basis (P : Fin 4 → Prop) [DecidablePred P] {z : Fin 4 → ℤ} {l : Fin 4} (hP : P l)
    (hl : 0 < z l) : coordWeight P (z - basisVector l) + 1 ≤ coordWeight P z := by
  refine coordWeight_succ_le P hP ?_ fun i hi => ?_
  · simp only [Pi.sub_apply, basisVector_apply, if_true]
    omega
  · simp [basisVector_apply, hi]
private theorem coordWeight_le (P : Fin 4 → Prop) [DecidablePred P] {r : ℕ} {z : Fin 4 → ℤ} (hz : InBox r z) :
    coordWeight P z ≤ 4 * r := by
  have : ∀ l ∈ (Finset.univ : Finset (Fin 4)), (if P l then (z l).natAbs else 0) ≤ r := by
    intro l _
    have := abs_le.mp (hz l)
    split_ifs <;> omega
  simpa [coordWeight] using Finset.sum_le_card_nsmul _ _ _ this
section Chords
variable {r : ℕ} {η : LatticeOneForm} {K : ℝ}
private theorem chord_step (hc : ∀ z μ ν, μ ≠ ν → InBox r z → |latticeCurl η z μ ν| ≤ K)
    (ht : ∀ z μ, InBox r z → InBox r (z + basisVector μ) → (∀ l, μ < l → z l = 0) → η (z, μ) = 0)
    {y : Fin 4 → ℤ} {μ l : Fin 4} (hμl : μ < l) (hy : InBox r y) (hy1 : InBox r (y + basisVector l))
    (hyμ : InBox r (y + basisVector μ)) (hyμ1 : InBox r (y + basisVector μ + basisVector l))
    (hup : ∀ l', l < l' → y l' = 0) :
    |η (y, μ) - η (y + basisVector l, μ)| ≤ K := by
  have h1 : η (y, l) = 0 := ht y l hy hy1 hup
  have h2 : η (y + basisVector μ, l) = 0 := ht _ l hyμ hyμ1 fun l' h' => by
    have e : l' ≠ μ := ne_of_gt (hμl.trans h')
    simp [basisVector_apply, hup l' h', e]
  have h3 := hc y μ l hμl.ne hy
  simp only [latticeCurl, h1, h2] at h3
  simpa using h3
private theorem chord_le (hK : 0 ≤ K) (hc : ∀ z μ ν, μ ≠ ν → InBox r z → |latticeCurl η z μ ν| ≤ K)
    (ht : ∀ z μ, InBox r z → InBox r (z + basisVector μ) → (∀ l, μ < l → z l = 0) → η (z, μ) = 0) :
    ∀ (N : ℕ) (z : Fin 4 → ℤ) (μ : Fin 4), InBox r z → InBox r (z + basisVector μ) →
      coordWeight (fun l => μ < l) z ≤ N → |η (z, μ)| ≤ N * K := by
  intro N
  induction N with
  | zero =>
    intro z μ hz hz1 hw
    have h0 : ∀ l, μ < l → z l = 0 := by
      intro l hl
      have := Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hw) l (Finset.mem_univ l)
      simpa [hl] using this
    rw [ht z μ hz hz1 h0]
    simp
  | succ N ih =>
    intro z μ hz hz1 hw
    by_cases htree : ∀ l, μ < l → z l = 0
    · rw [ht z μ hz hz1 htree, abs_zero]
      positivity
    · push Not at htree
      obtain ⟨l, hμl, hzl, hup⟩ : ∃ l, μ < l ∧ z l ≠ 0 ∧ ∀ l', l < l' → z l' = 0 := by
        classical
        let S : Finset (Fin 4) := Finset.univ.filter fun l => μ < l ∧ z l ≠ 0
        have hS : S.Nonempty := by
          obtain ⟨l, h1, h2⟩ := htree
          exact ⟨l, by simp [S, h1, h2]⟩
        have hm := Finset.max'_mem S hS
        have hm' : μ < S.max' hS ∧ z (S.max' hS) ≠ 0 := by simpa [S] using hm
        refine ⟨S.max' hS, hm'.1, hm'.2, fun l' hl' => ?_⟩
        by_contra hne
        have : l' ∈ S := by simp [S, hm'.1.trans hl', hne]
        exact absurd (Finset.le_max' S l' this) (not_le.mpr hl')
      have hlμ : l ≠ μ := ne_of_gt hμl
      have e1 : ∀ v : Fin 4 → ℤ, z + v + basisVector μ = z + basisVector μ + v := fun v => add_right_comm _ _ _
      rcases lt_or_gt_of_ne hzl with hneg | hpos
      · have hzμ : (z + basisVector μ) l < 0 := by simpa [basisVector_apply, hlμ] using hneg
        have a := chord_step hc ht hμl hz (inBox_add_basis hz hneg) hz1 (inBox_add_basis hz1 hzμ) hup
        have b := ih (z + basisVector l) μ (inBox_add_basis hz hneg)
          (by rw [e1]; exact inBox_add_basis hz1 hzμ) (by
          have := coordWeight_add_basis (fun l => μ < l) hμl hneg
          omega)
        have c := abs_sub_abs_le_abs_sub (η (z, μ)) (η (z + basisVector l, μ))
        push_cast
        linarith
      · have hzμ : 0 < (z + basisVector μ) l := by simpa [basisVector_apply, hlμ] using hpos
        have e2 : z - basisVector l + basisVector l = z := by abel
        have e3 : z - basisVector l + basisVector μ = z + basisVector μ - basisVector l := by abel
        have hy := inBox_sub_basis hz hpos
        have hy2 : InBox r (z - basisVector l + basisVector μ) := by rw [e3]; exact inBox_sub_basis hz1 hzμ
        have a := chord_step hc ht hμl hy (by rw [e2]; exact hz) hy2
          (by rw [e3, sub_add_cancel]; exact hz1)
          (fun l' hl' => by
            have e : l' ≠ l := ne_of_gt hl'
            simp [basisVector_apply, hup l' hl', e])
        rw [e2] at a
        have b := ih (z - basisVector l) μ hy hy2 (by
          have := coordWeight_sub_basis (fun l => μ < l) hμl hpos
          omega)
        have c := abs_sub_abs_le_abs_sub (η (z, μ)) (η (z - basisVector l, μ))
        rw [abs_sub_comm (η (z, μ))] at c
        push_cast
        linarith
end Chords
private def pathEnd : (Fin 4 → ℤ) → List PathStep → (Fin 4 → ℤ)
  | z, [] => z
  | z, st :: r => pathEnd (z + stepDisplacement st) r
private theorem pathEnd_append (l l' : List PathStep) : ∀ z, pathEnd z (l ++ l') = pathEnd (pathEnd z l) l' := by
  induction l with
  | nil => intro z; rfl
  | cons st r ih => intro z; simpa [pathEnd] using ih _
private theorem lineSum_append (ξ : LatticeOneForm) (l l' : List PathStep) : ∀ z,
    latticeLineSum ξ z (l ++ l') = latticeLineSum ξ z l + latticeLineSum ξ (pathEnd z l) l' := by
  induction l with
  | nil => intro z; simp [latticeLineSum, pathEnd]
  | cons st r ih => intro z; simp [latticeLineSum, pathEnd, ih, add_assoc]
private theorem pathEnd_add (w : Fin 4 → ℤ) (l : List PathStep) : ∀ z, pathEnd (z + w) l = pathEnd z l + w := by
  induction l with
  | nil => intro z; rfl
  | cons st r ih =>
    intro z
    simp only [pathEnd]
    rw [← ih]
    congr 1
    abel
private theorem lineSum_translate (η : LatticeOneForm) (w : Fin 4 → ℤ) (l : List PathStep) : ∀ z,
    latticeLineSum (translateForm η w) z l = latticeLineSum η (z + w) l := by
  induction l with
  | nil => intro z; rfl
  | cons st r ih =>
    intro z
    rcases st with ⟨i, s⟩
    have e : z + w + stepDisplacement (i, s) = z + stepDisplacement (i, s) + w := add_right_comm _ _ _
    cases s
    · simp only [latticeLineSum, translateForm, ih, e]
      have e2 : z - basisVector i + w = z + w - basisVector i := by abel
      simp [e2]
    · simp only [latticeLineSum, translateForm, ih, e]
      simp
private theorem stepDisplacement_flip (st : PathStep) : stepDisplacement (st.1, !st.2) = - stepDisplacement st := by apply _root_.YangMills.Construction.LatticePaths.stepDisplacement_flip <;> assumption
private theorem pathEnd_reversePath (l : List PathStep) : ∀ x, pathEnd (pathEnd x l) (reversePath l) = x := by
  induction l with
  | nil => intro x; rfl
  | cons st r ih =>
    intro x
    have h : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    rw [h, pathEnd_append]
    simp only [pathEnd]
    rw [ih, stepDisplacement_flip]
    simp
private theorem lineSum_reversePath (ξ : LatticeOneForm) (l : List PathStep) : ∀ x,
    latticeLineSum ξ (pathEnd x l) (reversePath l) = - latticeLineSum ξ x l := by
  induction l with
  | nil => intro x; simp [latticeLineSum, pathEnd, reversePath]
  | cons st r ih =>
    intro x
    have h : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    rw [h, lineSum_append]
    simp only [pathEnd]
    rw [ih, pathEnd_reversePath]
    rcases st with ⟨i, s⟩
    cases s
    · simp [latticeLineSum, stepDisplacement, sub_eq_add_neg]
    · simp [latticeLineSum, stepDisplacement]
private theorem lineSum_straight (η : LatticeOneForm) (μ : Fin 4) (t : ℕ) : ∀ z,
    latticeLineSum η z (List.replicate t (μ, true)) = ∑ a ∈ Finset.range t, η (z + (a : ℤ) • basisVector μ, μ) ∧
      pathEnd z (List.replicate t (μ, true)) = z + (t : ℤ) • basisVector μ := by
  induction t with
  | zero => intro z; simp [latticeLineSum, pathEnd]
  | succ t ih =>
    intro z
    obtain ⟨h1, h2⟩ := ih (z + basisVector μ)
    have hs : stepDisplacement (μ, true) = basisVector μ := by simp [stepDisplacement]
    rw [List.replicate_succ]
    simp only [latticeLineSum, pathEnd, if_true, hs]
    rw [h1, h2, Finset.sum_range_succ']
    constructor
    · simp only [Nat.cast_zero, zero_smul, add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 2
      push_cast
      rw [add_smul, one_smul]
      abel
    · push_cast
      rw [add_smul, one_smul]
      abel
section Legs
variable {r : ℕ} {η : LatticeOneForm} {B : ℝ}
private theorem segment_up (hB : ∀ z ν, InBox r z → InBox r (z + basisVector ν) → |η (z, ν)| ≤ B) (k : Fin 4) :
    ∀ (t : ℕ) (z : Fin 4 → ℤ), InBox r z → 0 ≤ z k → z k + t ≤ r →
      |latticeLineSum η z (List.replicate t (k, true))| ≤ t * B ∧
        pathEnd z (List.replicate t (k, true)) = z + (t : ℤ) • basisVector k := by
  intro t
  induction t with
  | zero => intro z _ _ _; simp [latticeLineSum, pathEnd]
  | succ t ih =>
    intro z hz h0 ht
    have hs : stepDisplacement (k, true) = basisVector k := by simp [stepDisplacement]
    have hz1 : InBox r (z + basisVector k) := by
      have h := inBox_add_smul hz k 1 (by
        push_cast at ht
        exact abs_le.mpr ⟨by omega, by omega⟩)
      simpa using h
    obtain ⟨h1, h2⟩ := ih (z + basisVector k) hz1 (by simp [basisVector_apply]; omega) (by
      simp only [Pi.add_apply, basisVector_apply, if_true]
      push_cast at ht
      omega)
    rw [List.replicate_succ]
    simp only [latticeLineSum, pathEnd, if_true, hs]
    constructor
    · have := hB z k hz hz1
      calc _ ≤ |η (z, k)| + |latticeLineSum η (z + basisVector k) (List.replicate t (k, true))| := abs_add_le _ _
        _ ≤ ((t + 1 : ℕ) : ℝ) * B := by push_cast; linarith
    · rw [h2]
      push_cast
      rw [add_smul, one_smul]
      abel
private theorem segment_down (hB : ∀ z ν, InBox r z → InBox r (z + basisVector ν) → |η (z, ν)| ≤ B) (k : Fin 4) :
    ∀ (t : ℕ) (z : Fin 4 → ℤ), InBox r z → z k ≤ 0 → -(r : ℤ) ≤ z k - t →
      |latticeLineSum η z (List.replicate t (k, false))| ≤ t * B ∧
        pathEnd z (List.replicate t (k, false)) = z - (t : ℤ) • basisVector k := by
  intro t
  induction t with
  | zero => intro z _ _ _; simp [latticeLineSum, pathEnd]
  | succ t ih =>
    intro z hz h0 ht
    have hs : stepDisplacement (k, false) = - basisVector k := by simp [stepDisplacement]
    have hz1 : InBox r (z - basisVector k) := by
      have h := inBox_add_smul hz k (-1) (by
        push_cast at ht
        exact abs_le.mpr ⟨by omega, by omega⟩)
      simpa [sub_eq_add_neg] using h
    have e : z + - basisVector k = z - basisVector k := by abel
    obtain ⟨h1, h2⟩ := ih (z - basisVector k) hz1 (by simp [basisVector_apply]; omega) (by
      simp only [Pi.sub_apply, basisVector_apply, if_true]
      push_cast at ht
      omega)
    rw [List.replicate_succ]
    simp only [latticeLineSum, pathEnd, hs, e, Bool.false_eq_true, if_false]
    constructor
    · have := hB (z - basisVector k) k hz1 (by simpa using hz)
      calc _ ≤ |- η (z - basisVector k, k)| +
            |latticeLineSum η (z - basisVector k) (List.replicate t (k, false))| := abs_add_le _ _
        _ ≤ ((t + 1 : ℕ) : ℝ) * B := by rw [abs_neg]; push_cast; linarith
    · rw [h2]
      push_cast
      rw [add_smul, one_smul]
      abel
private theorem segment_leg (hB : ∀ z ν, InBox r z → InBox r (z + basisVector ν) → |η (z, ν)| ≤ B) (hB0 : 0 ≤ B)
    {h : Fin 4 → ℤ} (hh : InBox r h) (k : Fin 4) (z : Fin 4 → ℤ) (hz : InBox r z) (h0 : z k = 0) :
    |latticeLineSum η z (List.replicate (h k).natAbs (k, decide (0 ≤ h k)))| ≤ r * B ∧
      pathEnd z (List.replicate (h k).natAbs (k, decide (0 ≤ h k))) = z + h k • basisVector k := by
  have hk := abs_le.mp (hh k)
  have hn : ((h k).natAbs : ℝ) ≤ r := by
    have : (h k).natAbs ≤ r := by omega
    exact_mod_cast this
  have hm : ((h k).natAbs : ℝ) * B ≤ r * B := mul_le_mul_of_nonneg_right hn hB0
  by_cases hs : 0 ≤ h k
  · have e : ((h k).natAbs : ℤ) = h k := by omega
    obtain ⟨h1, h2⟩ := segment_up hB k (h k).natAbs z hz (by omega) (by omega)
    simp only [hs, decide_true]
    exact ⟨h1.trans hm, by rw [h2, e]⟩
  · have e : ((h k).natAbs : ℤ) = - h k := by omega
    obtain ⟨h1, h2⟩ := segment_down hB k (h k).natAbs z hz (by omega) (by omega)
    simp only [hs, decide_false]
    refine ⟨h1.trans hm, ?_⟩
    rw [h2, e, neg_smul, sub_neg_eq_add]
private theorem axisPath_aux (hB : ∀ z ν, InBox r z → InBox r (z + basisVector ν) → |η (z, ν)| ≤ B) (hB0 : 0 ≤ B)
    {h : Fin 4 → ℤ} (hh : InBox r h) (π : Equiv.Perm (Fin 4)) : ∀ (ks : List (Fin 4)), (ks.map π).Nodup →
      ∀ z, InBox r z → (∀ k ∈ ks, z (π k) = 0) →
      |latticeLineSum η z (ks.flatMap fun k => List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k))))|
          ≤ ks.length * (r * B) ∧
        ∀ i, pathEnd z (ks.flatMap fun k => List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))) i =
          if i ∈ ks.map π then h i else z i := by
  intro ks
  induction ks with
  | nil => intro _ z _ _; simp [latticeLineSum, pathEnd]
  | cons k ks ih =>
    intro hnd z hz h0
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s1, s2⟩ := segment_leg hB hB0 hh (π k) z hz (h0 k (by simp))
    have hz' : InBox r (z + h (π k) • basisVector (π k)) := inBox_add_smul hz _ _ (by
      rw [h0 k (by simp), zero_add]
      exact hh _)
    obtain ⟨i1, i2⟩ := ih hnd.2 _ hz' (fun k' hk' => by
      have e : π k' ≠ π k := fun e => hnd.1 (by rw [← e]; exact List.mem_map_of_mem hk')
      simpa [basisVector_apply, e] using h0 k' (by simp [hk']))
    rw [List.flatMap_cons, lineSum_append, pathEnd_append, s2]
    constructor
    · calc _ ≤ _ := abs_add_le _ _
        _ ≤ r * B + ks.length * (r * B) := add_le_add s1 i1
        _ = _ := by simp; ring
    · intro i
      rw [i2 i]
      by_cases e : i = π k
      · subst e
        simp [basisVector_apply, h0 k]
      · simp [basisVector_apply, e]
private theorem axisPath_bound (hB : ∀ z ν, InBox r z → InBox r (z + basisVector ν) → |η (z, ν)| ≤ B) (hB0 : 0 ≤ B)
    {h : Fin 4 → ℤ} (hh : InBox r h) (π : Equiv.Perm (Fin 4)) :
    |latticeLineSum η 0 (axisPath h π)| ≤ 4 * r * B ∧ pathEnd 0 (axisPath h π) = h := by
  obtain ⟨h1, h2⟩ := axisPath_aux hB hB0 hh π (List.finRange 4)
    ((List.nodup_finRange 4).map π.injective) 0 (fun i => by simp) (fun _ _ => rfl)
  constructor
  · calc _ ≤ _ := h1
      _ = _ := by simp; ring
  · funext i
    have : i ∈ (List.finRange 4).map π := by
      simp only [List.mem_map, List.mem_finRange, true_and]
      exact ⟨π.symm i, by simp⟩
    simpa [this, axisPath] using h2 i
end Legs
private def neighbourCentre (ℓ : ℕ) (μ : Fin 4) : Fin 4 → ℤ := ((2 * ℓ + 1 : ℕ) : ℤ) • basisVector μ
section Crossings
variable {ℓ : ℕ} {η : LatticeOneForm} {K B : ℝ} {μ : Fin 4}
private theorem straight_sub_le (hB : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → |η (z, ν)| ≤ B)
    (hB1 : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → |translateForm η (neighbourCentre ℓ μ) (z, ν)| ≤ B)
    {h : Fin 4 → ℤ} (hh : InBox ℓ h) :
    |∑ a ∈ Finset.range (2 * ℓ + 1), η (h + (a : ℤ) • basisVector μ, μ) -
        η (h + ((ℓ : ℤ) - h μ) • basisVector μ, μ)| ≤ 2 * ℓ * B := by
  have hk := abs_le.mp (hh μ)
  obtain ⟨t₀, e₀⟩ : ∃ t₀ : ℕ, (t₀ : ℤ) = (ℓ : ℤ) - h μ :=
    ⟨((ℓ : ℤ) - h μ).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hmem : t₀ ∈ Finset.range (2 * ℓ + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ hmem, e₀, add_sub_cancel_left]
  have each : ∀ a ∈ (Finset.range (2 * ℓ + 1)).erase t₀, |η (h + (a : ℤ) • basisVector μ, μ)| ≤ B := by
    intro a ha
    have ha1 := Finset.ne_of_mem_erase ha
    have ha2 := Finset.mem_range.mp (Finset.mem_of_mem_erase ha)
    rcases lt_or_gt_of_ne ha1 with hlt | hgt
    · have e : h + (a : ℤ) • basisVector μ + basisVector μ = h + ((a : ℤ) + 1) • basisVector μ := by
        rw [add_smul, one_smul, add_assoc]
      refine hB _ μ (inBox_add_smul hh μ _ (abs_le.mpr ⟨by omega, by omega⟩)) ?_
      rw [e]
      exact inBox_add_smul hh μ _ (abs_le.mpr ⟨by omega, by omega⟩)
    · have e : h + ((a : ℤ) - ((2 * ℓ + 1 : ℕ) : ℤ)) • basisVector μ + basisVector μ =
          h + ((a : ℤ) - ((2 * ℓ + 1 : ℕ) : ℤ) + 1) • basisVector μ := by
        rw [add_smul _ (1 : ℤ), one_smul, add_assoc]
      have e2 : translateForm η (neighbourCentre ℓ μ) (h + ((a : ℤ) - ((2 * ℓ + 1 : ℕ) : ℤ)) • basisVector μ, μ) =
          η (h + (a : ℤ) • basisVector μ, μ) := by
        show η (h + ((a : ℤ) - ((2 * ℓ + 1 : ℕ) : ℤ)) • basisVector μ + neighbourCentre ℓ μ, μ) = _
        rw [neighbourCentre, add_assoc, ← add_smul, sub_add_cancel]
      rw [← e2]
      refine hB1 _ μ (inBox_add_smul hh μ _ (abs_le.mpr ⟨by omega, by omega⟩)) ?_
      rw [e]
      exact inBox_add_smul hh μ _ (abs_le.mpr ⟨by omega, by omega⟩)
  have hcard : (((Finset.range (2 * ℓ + 1)).erase t₀).card : ℝ) = 2 * ℓ := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_range]
    simp
  calc _ ≤ ∑ a ∈ (Finset.range (2 * ℓ + 1)).erase t₀, |η (h + (a : ℤ) • basisVector μ, μ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ (Finset.range (2 * ℓ + 1)).erase t₀, B := Finset.sum_le_sum each
    _ = 2 * ℓ * B := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
private theorem crossing_step (hc : ∀ z a b, a ≠ b → InBox ℓ z → |latticeCurl η z a b| ≤ K)
    (hB : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → |η (z, ν)| ≤ B)
    (hB1 : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → |translateForm η (neighbourCentre ℓ μ) (z, ν)| ≤ B)
    {y : Fin 4 → ℤ} {l : Fin 4} (hl : l ≠ μ) (hy : InBox ℓ y) (hy1 : InBox ℓ (y + basisVector l))
    (hyμ : y μ = ℓ) : |η (y, μ) - η (y + basisVector l, μ)| ≤ K + 2 * B := by
  have c := hc y μ l hl.symm hy
  have a := hB y l hy hy1
  have hμl : μ ≠ l := hl.symm
  have hs : InBox ℓ (y + (1 - ((2 * ℓ + 1 : ℕ) : ℤ)) • basisVector μ) :=
    inBox_add_smul hy μ _ (by rw [hyμ]; exact abs_le.mpr ⟨by omega, by omega⟩)
  have hs1 : InBox ℓ (y + (1 - ((2 * ℓ + 1 : ℕ) : ℤ)) • basisVector μ + basisVector l) := by
    rw [add_right_comm]
    refine inBox_add_smul hy1 μ _ ?_
    simp only [Pi.add_apply, basisVector_apply, hμl, if_false, add_zero, hyμ]
    exact abs_le.mpr ⟨by omega, by omega⟩
  have b := hB1 _ l hs hs1
  have e : translateForm η (neighbourCentre ℓ μ) (y + (1 - ((2 * ℓ + 1 : ℕ) : ℤ)) • basisVector μ, l) =
      η (y + basisVector μ, l) := by
    show η (y + (1 - ((2 * ℓ + 1 : ℕ) : ℤ)) • basisVector μ + neighbourCentre ℓ μ, l) = _
    rw [neighbourCentre, add_assoc, ← add_smul, sub_add_cancel, one_smul]
  rw [e] at b
  simp only [latticeCurl] at c
  have c' := abs_le.mp c
  have a' := abs_le.mp a
  have b' := abs_le.mp b
  exact abs_le.mpr ⟨by linarith [c'.1, c'.2, a'.1, a'.2, b'.1, b'.2],
    by linarith [c'.1, c'.2, a'.1, a'.2, b'.1, b'.2]⟩
private theorem crossing_transverse (hK : 0 ≤ K) (hB0 : 0 ≤ B)
    (hc : ∀ z a b, a ≠ b → InBox ℓ z → |latticeCurl η z a b| ≤ K)
    (hB : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → |η (z, ν)| ≤ B)
    (hB1 : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → |translateForm η (neighbourCentre ℓ μ) (z, ν)| ≤ B) :
    ∀ (N : ℕ) (z : Fin 4 → ℤ), InBox ℓ z → z μ = ℓ → coordWeight (fun l => l ≠ μ) z ≤ N →
      |η (z, μ) - η ((ℓ : ℤ) • basisVector μ, μ)| ≤ N * (K + 2 * B) := by
  have base : ∀ (z : Fin 4 → ℤ), z μ = ℓ → (∀ l, l ≠ μ → z l = 0) → z = (ℓ : ℤ) • basisVector μ := by
    intro z h1 h2
    funext i
    rcases eq_or_ne i μ with rfl | e
    · simp [basisVector_apply, h1]
    · simp [basisVector_apply, e, h2 i e]
  intro N
  induction N with
  | zero =>
    intro z hz hzμ hw
    have h0 : ∀ l, l ≠ μ → z l = 0 := by
      intro l hl
      have := Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hw) l (Finset.mem_univ l)
      simpa [hl] using this
    rw [← base z hzμ h0]
    simp
  | succ N ih =>
    intro z hz hzμ hw
    by_cases h0 : ∀ l, l ≠ μ → z l = 0
    · rw [← base z hzμ h0, sub_self, abs_zero]
      positivity
    · push Not at h0
      obtain ⟨l, hl, hzl⟩ := h0
      have hμl : μ ≠ l := hl.symm
      rcases lt_or_gt_of_ne hzl with hneg | hpos
      · have a := crossing_step hc hB hB1 hl hz (inBox_add_basis hz hneg) hzμ
        have b := ih (z + basisVector l) (inBox_add_basis hz hneg) (by simp [basisVector_apply, hμl, hzμ]) (by
          have := coordWeight_add_basis (fun l => l ≠ μ) hl hneg
          omega)
        have c := abs_sub_le (η (z, μ)) (η (z + basisVector l, μ)) (η ((ℓ : ℤ) • basisVector μ, μ))
        push_cast
        linarith
      · have hy := inBox_sub_basis hz hpos
        have a := crossing_step hc hB hB1 hl hy (by rw [sub_add_cancel]; exact hz)
          (by simp [basisVector_apply, hμl, hzμ])
        rw [sub_add_cancel, abs_sub_comm] at a
        have b := ih (z - basisVector l) hy (by simp [basisVector_apply, hμl, hzμ]) (by
          have := coordWeight_sub_basis (fun l => l ≠ μ) hl hpos
          omega)
        have c := abs_sub_le (η (z, μ)) (η (z - basisVector l, μ)) (η ((ℓ : ℤ) • basisVector μ, μ))
        push_cast
        linarith
private theorem lineSum_bondContour (η : LatticeOneForm) (ℓ : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4))
    (μ : Fin 4) (hend : pathEnd 0 (axisPath h π) = h) :
    latticeLineSum η 0 (bondContour (2 * ℓ + 1) h π μ) =
      latticeLineSum η 0 (axisPath h π) + ∑ a ∈ Finset.range (2 * ℓ + 1), η (h + (a : ℤ) • basisVector μ, μ) -
        latticeLineSum (translateForm η (neighbourCentre ℓ μ)) 0 (axisPath h π) := by
  obtain ⟨s1, s2⟩ := lineSum_straight η μ (2 * ℓ + 1) h
  have e : pathEnd (0 + neighbourCentre ℓ μ) (axisPath h π) = h + neighbourCentre ℓ μ := by
    rw [pathEnd_add, hend]
  have r := lineSum_reversePath η (axisPath h π) (0 + neighbourCentre ℓ μ)
  have r2 : latticeLineSum η (0 + neighbourCentre ℓ μ) (axisPath h π) =
      latticeLineSum (translateForm η (neighbourCentre ℓ μ)) 0 (axisPath h π) := (lineSum_translate _ _ _ _).symm
  rw [e, r2] at r
  unfold bondContour
  rw [lineSum_append, lineSum_append, pathEnd_append, hend, s1, s2]
  rw [show h + ((2 * ℓ + 1 : ℕ) : ℤ) • basisVector μ = h + neighbourCentre ℓ μ from rfl, r]
  ring
private theorem bondContour_sub_le (hK : 0 ≤ K) (hB0 : 0 ≤ B)
    (hc : ∀ z a b, a ≠ b → InBox ℓ z → |latticeCurl η z a b| ≤ K)
    (hB : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → |η (z, ν)| ≤ B)
    (hB1 : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → |translateForm η (neighbourCentre ℓ μ) (z, ν)| ≤ B)
    {h : Fin 4 → ℤ} (hh : InBox ℓ h) (π : Equiv.Perm (Fin 4)) :
    |latticeLineSum η 0 (bondContour (2 * ℓ + 1) h π μ) - η ((ℓ : ℤ) • basisVector μ, μ)| ≤
      10 * ℓ * B + 4 * ℓ * (K + 2 * B) := by
  obtain ⟨p1, p2⟩ := axisPath_bound hB hB0 hh π
  obtain ⟨q1, _⟩ := axisPath_bound hB1 hB0 hh π
  rw [lineSum_bondContour η ℓ h π μ p2]
  have st := straight_sub_le hB hB1 hh
  have hzin : InBox ℓ (h + ((ℓ : ℤ) - h μ) • basisVector μ) := inBox_add_smul hh μ _ (by
    have : h μ + ((ℓ : ℤ) - h μ) = ℓ := by ring
    rw [this]
    exact abs_le.mpr ⟨by omega, le_refl _⟩)
  have hzμ : (h + ((ℓ : ℤ) - h μ) • basisVector μ) μ = ℓ := by simp [basisVector_apply]
  have tr := crossing_transverse hK hB0 hc hB hB1 (4 * ℓ) _ hzin hzμ (coordWeight_le _ hzin)
  push_cast at tr
  have p' := abs_le.mp p1
  have q' := abs_le.mp q1
  have s' := abs_le.mp st
  have t' := abs_le.mp tr
  exact abs_le.mpr ⟨by linarith [p'.1, q'.2, s'.1, t'.1], by linarith [p'.2, q'.1, s'.2, t'.2]⟩
end Crossings
private theorem mem_centredCube_iff {ℓ : ℕ} {h : Fin 4 → ℤ} : h ∈ centredCube (2 * ℓ + 1) ↔ InBox ℓ h := by apply _root_.YangMills.Construction.HoleSavings.mem_centredCube_odd <;> assumption
private theorem card_centredCube (ℓ : ℕ) : (centredCube (2 * ℓ + 1)).card = (2 * ℓ + 1) ^ 4 := by apply _root_.YangMills.Construction.HoleSavings.card_centredCube_odd <;> assumption
private theorem average_sub_le {ℓ : ℕ} (S : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℝ) (X E : ℝ)
    (hS : ∀ h ∈ centredCube (2 * ℓ + 1), ∀ π, |S h π - X| ≤ E) :
    |(1 / (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4)) * ∑ h ∈ centredCube (2 * ℓ + 1), ∑ π, S h π - X| ≤ E := by
  have hcount : ∑ _h ∈ centredCube (2 * ℓ + 1), ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) =
      24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, card_centredCube]
    simp [Nat.factorial]
    ring
  have h1 : ∑ h ∈ centredCube (2 * ℓ + 1), ∑ π, (S h π - X) =
      ∑ h ∈ centredCube (2 * ℓ + 1), ∑ π, S h π - (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4) * X := by
    rw [← hcount, Finset.sum_mul]
    simp only [Finset.sum_mul, one_mul, Finset.sum_sub_distrib]
  have h2 : |∑ h ∈ centredCube (2 * ℓ + 1), ∑ π, (S h π - X)| ≤ (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4) * E := by
    rw [← hcount, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun h hh => ?_)
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun π _ => ?_)
    simpa using hS h hh π
  have h3 : (1 / (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4)) * ∑ h ∈ centredCube (2 * ℓ + 1), ∑ π, S h π - X =
      (1 / (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4)) * ∑ h ∈ centredCube (2 * ℓ + 1), ∑ π, (S h π - X) := by
    rw [h1]
    field_simp
  rw [h3, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4))]
  calc _ ≤ (1 / (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4)) * ((24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4) * E) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = E := by field_simp
private def blockConstant (ℓ : ℕ) : ℝ := 10 * ℓ * (4 * ℓ) + 2 * (4 * ℓ * (1 + 2 * (4 * ℓ)))
private theorem bond_le_average {ℓ : ℕ} {η : LatticeOneForm} {K : ℝ} (hK : 0 ≤ K) (μ : Fin 4)
    (hc : ∀ z, InBox (3 * ℓ + 1) z → ∀ a b, a ≠ b → |latticeCurl η z a b| ≤ K)
    (ht0 : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → (∀ l, ν < l → z l = 0) → η (z, ν) = 0)
    (ht1 : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → (∀ l, ν < l → z l = 0) →
      translateForm η (neighbourCentre ℓ μ) (z, ν) = 0)
    {z : Fin 4 → ℤ} (hz : InBox ℓ z) :
    |η (z, μ)| ≤ |(1 / (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4)) * ∑ h ∈ centredCube (2 * ℓ + 1),
        ∑ π : Equiv.Perm (Fin 4), latticeLineSum η 0 (bondContour (2 * ℓ + 1) h π μ)| + blockConstant ℓ * K := by
  have hin : ∀ {y : Fin 4 → ℤ}, InBox ℓ y → InBox (3 * ℓ + 1) y := fun hy i => by
    have := abs_le.mp (hy i)
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hcs : ∀ y a b, a ≠ b → InBox ℓ y → |latticeCurl η y a b| ≤ K := fun y a b hab hy => hc y (hin hy) a b hab
  have hcs1 : ∀ y a b, a ≠ b → InBox ℓ y → |latticeCurl (translateForm η (neighbourCentre ℓ μ)) y a b| ≤ K := by
    intro y a b hab hy
    have e : latticeCurl (translateForm η (neighbourCentre ℓ μ)) y a b =
        latticeCurl η (y + neighbourCentre ℓ μ) a b := by
      simp only [latticeCurl, translateForm, add_right_comm]
    rw [e]
    refine hc _ (fun i => ?_) a b hab
    have := abs_le.mp (hy i)
    simp only [neighbourCentre, Pi.add_apply, Pi.smul_apply, basisVector_apply, smul_eq_mul]
    refine abs_le.mpr ?_
    split_ifs
    · constructor <;> push_cast <;> omega
    · constructor <;> omega
  have hB0 : 0 ≤ ((4 * ℓ : ℕ) : ℝ) * K := by positivity
  have hB : ∀ y ν, InBox ℓ y → InBox ℓ (y + basisVector ν) → |η (y, ν)| ≤ ((4 * ℓ : ℕ) : ℝ) * K :=
    fun y ν hy hy1 => chord_le hK hcs ht0 (4 * ℓ) y ν hy hy1 (coordWeight_le _ hy)
  have hB1 : ∀ y ν, InBox ℓ y → InBox ℓ (y + basisVector ν) →
      |translateForm η (neighbourCentre ℓ μ) (y, ν)| ≤ ((4 * ℓ : ℕ) : ℝ) * K :=
    fun y ν hy hy1 => chord_le hK hcs1 ht1 (4 * ℓ) y ν hy hy1 (coordWeight_le _ hy)
  have hbig : 0 ≤ (ℓ : ℝ) * K := by positivity
  have hbig2 : 0 ≤ (ℓ : ℝ) * ℓ * K := by positivity
  by_cases hz1 : InBox ℓ (z + basisVector μ)
  · have a := hB z μ hz hz1
    have hm := abs_nonneg ((1 / (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4)) * ∑ h ∈ centredCube (2 * ℓ + 1),
        ∑ π : Equiv.Perm (Fin 4), latticeLineSum η 0 (bondContour (2 * ℓ + 1) h π μ))
    unfold blockConstant
    push_cast at a
    nlinarith
  · have hzμ : z μ = ℓ := by
      by_contra hne
      refine hz1 fun i => ?_
      rcases eq_or_ne i μ with rfl | e
      · have := abs_le.mp (hz i)
        simp only [Pi.add_apply, basisVector_apply, if_true]
        exact abs_le.mpr ⟨by omega, by omega⟩
      · simpa [basisVector_apply, e] using hz i
    have tr := crossing_transverse hK hB0 hcs hB hB1 (4 * ℓ) z hz hzμ (coordWeight_le _ hz)
    have mn := average_sub_le (ℓ := ℓ) (fun h π => latticeLineSum η 0 (bondContour (2 * ℓ + 1) h π μ))
      (η ((ℓ : ℤ) • basisVector μ, μ)) _
      (fun h hh π => bondContour_sub_le hK hB0 hcs hB hB1 (mem_centredCube_iff.mp hh) π)
    have e1 := abs_sub_abs_le_abs_sub (η (z, μ)) (η ((ℓ : ℤ) • basisVector μ, μ))
    have e2 := abs_sub_abs_le_abs_sub (η ((ℓ : ℤ) • basisVector μ, μ))
      ((1 / (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4)) * ∑ h ∈ centredCube (2 * ℓ + 1), ∑ π : Equiv.Perm (Fin 4),
        latticeLineSum η 0 (bondContour (2 * ℓ + 1) h π μ))
    rw [abs_sub_comm (η ((ℓ : ℤ) • basisVector μ, μ))] at e2
    have hv : ((4 * ℓ : ℕ) : ℝ) = 4 * ℓ := by push_cast; ring
    simp only [hv] at tr mn
    unfold blockConstant
    nlinarith
section Torus
private def pullback {m : ℕ} (ξ : RealOneForm m) (x₀ : TorusSite m) : LatticeOneForm :=
  fun b => ξ (x₀ + siteOfInt b.1, b.2)
private theorem siteOfInt_basisVector {m : ℕ} (i : Fin 4) :
    (siteOfInt (basisVector i) : TorusSite m) = unitStep m i := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
abbrev _root_.YangMills.SharedProofs.p5838 := @siteOfInt_basisVector
private theorem siteOfInt_add {m : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfInt (a + b) : TorusSite m) = siteOfInt a + siteOfInt b := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_add <;> assumption
private theorem siteOfInt_sub {m : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfInt (a - b) : TorusSite m) = siteOfInt a - siteOfInt b := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.siteOfInt_sub <;> assumption
private theorem pathIntegral_eq_lineSum {m : ℕ} (ξ : RealOneForm m) (x₀ : TorusSite m) (l : List PathStep) : ∀ z,
    pathIntegral ξ (x₀ + siteOfInt z) l = latticeLineSum (pullback ξ x₀) z l := by
  induction l with
  | nil => intro z; rfl
  | cons st r ih =>
    intro z
    rcases st with ⟨i, s⟩
    have e : stepEndpoint (x₀ + siteOfInt z) (i, s) = x₀ + siteOfInt (z + stepDisplacement (i, s)) := by
      cases s
      · have : z + stepDisplacement (i, false) = z - basisVector i := by
          simp [stepDisplacement, sub_eq_add_neg]
        rw [this, siteOfInt_sub, siteOfInt_basisVector]
        simp [stepEndpoint, add_sub_assoc]
      · have : z + stepDisplacement (i, true) = z + basisVector i := by simp [stepDisplacement]
        rw [this, siteOfInt_add, siteOfInt_basisVector]
        simp [stepEndpoint, add_assoc]
    simp only [pathIntegral, latticeLineSum, e, ih]
    congr 1
    cases s
    · simp only [Bool.false_eq_true, if_false, pullback]
      rw [siteOfInt_sub, siteOfInt_basisVector, add_sub_assoc]
    · simp only [if_true, pullback]
private theorem latticeCurl_pullback {m : ℕ} (ξ : RealOneForm m) (x₀ : TorusSite m) (z : Fin 4 → ℤ)
    (μ ν : Fin 4) : latticeCurl (pullback ξ x₀) z μ ν = plaquetteCurl ξ (x₀ + siteOfInt z) μ ν := by
  simp only [latticeCurl, pullback, plaquetteCurl, siteOfInt_add, siteOfInt_basisVector, add_assoc]
private theorem translateForm_pullback {m : ℕ} (ξ : RealOneForm m) (x₀ : TorusSite m) (w : Fin 4 → ℤ) :
    translateForm (pullback ξ x₀) w = pullback ξ (x₀ + siteOfInt w) := by
  funext b
  simp only [translateForm, pullback, siteOfInt_add]
  rw [add_assoc, add_comm (siteOfInt w)]
variable {ℓ n : ℕ} [NeZero n] [NeZero (2 * ℓ + 1)]
private theorem slopeCentre_eq (Y : TorusSite n) :
    SlopeCoefficient.blockCentreSite (2 * ℓ + 1) Y = blockCentreSite (2 * ℓ + 1) Y := by
  funext k
  have e : (((Y k).cast : ℤ)) = (((Y k).val : ℕ) : ℤ) := (ZMod.natCast_val (Y k)).symm
  simp only [SlopeCoefficient.blockCentreSite, blockCentreSite, siteOfInt]
  rw [e]
  push_cast
  rfl
private theorem coarseSite_eq (x : TorusSite (n * (2 * ℓ + 1))) :
    coarseSite (2 * ℓ + 1) x = parentBlock (2 * ℓ + 1) x := rfl
private theorem parentBlock_of_inBox {z : Fin 4 → ℤ} (hz : InBox ℓ z) (Y : TorusSite n) :
    parentBlock (2 * ℓ + 1) (blockCentreSite (2 * ℓ + 1) Y + siteOfInt z) = Y := by
  rw [parentBlock_blockCentreSite_add]
  have e : (fun i => (z i + (((2 * ℓ + 1 : ℕ) : ℤ) - 1) / 2) / (((2 * ℓ + 1 : ℕ) : ℤ))) = (0 : Fin 4 → ℤ) := by
    funext i
    have := abs_le.mp (hz i)
    exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
  rw [e, siteOfInt_zero_offset, add_zero]
private theorem isBlockTreeBond_of (Y : TorusSite n) {z : Fin 4 → ℤ} {ν : Fin 4} (hz : InBox ℓ z)
    (hz1 : InBox ℓ (z + basisVector ν)) (hup : ∀ l, ν < l → z l = 0) :
    IsBlockTreeBond (2 * ℓ + 1)
      ((blockCentreSite (2 * ℓ + 1) Y + siteOfInt z, ν) : TorusBond (n * (2 * ℓ + 1))) := by
  refine ⟨?_, fun l hl => ?_⟩
  · have e : blockCentreSite (2 * ℓ + 1) Y + siteOfInt z + unitStep (n * (2 * ℓ + 1)) ν =
        blockCentreSite (2 * ℓ + 1) Y + siteOfInt (z + basisVector ν) := by
      rw [siteOfInt_add, siteOfInt_basisVector, add_assoc]
    simp only [CrossesBlockBoundary, coarseSite_eq, e, parentBlock_of_inBox hz, parentBlock_of_inBox hz1, ne_eq,
      not_true_eq_false, not_false_eq_true]
  · simp only [offsetFromCentre, coarseSite_eq, parentBlock_of_inBox hz, slopeCentre_eq, add_sub_cancel_left]
    simp [siteOfInt, hup l hl]
private theorem centre_cast_add (a : ZMod n) (z : ℤ) :
    ((((2 * ℓ + 1 : ℕ) : ℤ) * ((a + (z : ZMod n)).cast : ℤ) : ℤ) : ZMod (n * (2 * ℓ + 1))) =
      ((((2 * ℓ + 1 : ℕ) : ℤ) * (a.cast : ℤ) + ((2 * ℓ + 1 : ℕ) : ℤ) * z : ℤ) : ZMod (n * (2 * ℓ + 1))) := by
  have h1 : ((((a + (z : ZMod n)).cast : ℤ)) : ZMod n) = (((a.cast : ℤ) + z : ℤ) : ZMod n) := by
    push_cast
    simp [ZMod.intCast_zmod_cast]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨c, hc⟩ := h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨c, ?_⟩
  push_cast
  push_cast at hc
  linear_combination (2 * (ℓ : ℤ) + 1) * hc
private theorem blockCentreSite_add_unitStep (Y : TorusSite n) (μ : Fin 4) :
    blockCentreSite (2 * ℓ + 1) (Y + unitStep n μ) =
      blockCentreSite (2 * ℓ + 1) Y + siteOfInt (neighbourCentre ℓ μ) := by
  funext k
  have e : unitStep n μ k = ((basisVector μ k : ℤ) : ZMod n) := by
    by_cases h : k = μ
    · subst h
      simp [unitStep, basisVector]
    · simp [unitStep, basisVector, h]
  have := centre_cast_add (ℓ := ℓ) (Y k) (basisVector μ k)
  simp only [blockCentreSite, siteOfInt, Pi.add_apply, neighbourCentre, Pi.smul_apply, smul_eq_mul]
  rw [e, this]
  push_cast
  ring
private theorem sum_le_sum_blocks (hL : Odd (2 * ℓ + 1)) (f : TorusSite (n * (2 * ℓ + 1)) → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x, f x ≤ ∑ Y : TorusSite n, ∑ e ∈ centredCube (2 * ℓ + 1), f (blockCentreSite (2 * ℓ + 1) Y + siteOfInt e) := by
  classical
  have himg : ((Finset.univ : Finset (TorusSite n)) ×ˢ centredCube (2 * ℓ + 1)).image
      (fun p => blockCentreSite (2 * ℓ + 1) p.1 + siteOfInt p.2 :
        TorusSite n × (Fin 4 → ℤ) → TorusSite (n * (2 * ℓ + 1))) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun x => ?_
    obtain ⟨o, ho, hx⟩ := exists_eq_blockCentreSite_add hL x
    refine Finset.mem_image.mpr ⟨(parentBlock (2 * ℓ + 1) x, o), ?_, hx.symm⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_centredCube_iff.mpr fun i => ?_⟩
    have e : (((2 * ℓ + 1 : ℕ) : ℤ) - 1) / 2 = ℓ := by omega
    have := ho i
    rw [e] at this
    show |o i| ≤ _
    exact abs_le.mpr ⟨by omega, by omega⟩
  calc ∑ x, f x = ∑ x ∈ ((Finset.univ : Finset (TorusSite n)) ×ˢ centredCube (2 * ℓ + 1)).image
        (fun p => blockCentreSite (2 * ℓ + 1) p.1 + siteOfInt p.2 :
          TorusSite n × (Fin 4 → ℤ) → TorusSite (n * (2 * ℓ + 1))), f x := by
        rw [himg]
    _ ≤ ∑ p ∈ (Finset.univ : Finset (TorusSite n)) ×ˢ centredCube (2 * ℓ + 1),
          f (blockCentreSite (2 * ℓ + 1) p.1 + siteOfInt p.2) :=
        Finset.sum_image_le_of_nonneg fun _ _ => hf _
    _ = _ := Finset.sum_product _ _ _
private theorem sum_blocks_le (hL : Odd (2 * ℓ + 1)) (e : Fin 4 → ℤ) (f : TorusSite (n * (2 * ℓ + 1)) → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ Y : TorusSite n, f (blockCentreSite (2 * ℓ + 1) Y + siteOfInt e) ≤ ∑ x, f x := by
  classical
  have hinj : Function.Injective fun Y : TorusSite n =>
      blockCentreSite (2 * ℓ + 1) Y + (siteOfInt e : TorusSite (n * (2 * ℓ + 1))) := by
    intro Y Y' h
    have h' := add_right_cancel h
    have := congrArg (parentBlock (2 * ℓ + 1)) h'
    rwa [parentBlock_blockCentreSite hL, parentBlock_blockCentreSite hL] at this
  calc _ = ∑ x ∈ (Finset.univ : Finset (TorusSite n)).image
        (fun Y => blockCentreSite (2 * ℓ + 1) Y + (siteOfInt e : TorusSite (n * (2 * ℓ + 1)))), f x :=
        (Finset.sum_image hinj.injOn).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hf _
private def siteCurlEnergy {m : ℕ} (ξ : RealOneForm m) (x : TorusSite m) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then plaquetteCurl ξ x μ ν ^ 2 else 0
private theorem siteCurlEnergy_nonneg {m : ℕ} (ξ : RealOneForm m) (x : TorusSite m) : 0 ≤ siteCurlEnergy ξ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
private theorem sq_plaquetteCurl_le {m : ℕ} (ξ : RealOneForm m) (x : TorusSite m) {μ ν : Fin 4} (h : μ < ν) :
    plaquetteCurl ξ x μ ν ^ 2 ≤ siteCurlEnergy ξ x := by
  have h1 : plaquetteCurl ξ x μ ν ^ 2 ≤ ∑ ν' : Fin 4, if μ < ν' then plaquetteCurl ξ x μ ν' ^ 2 else 0 := by
    have := Finset.single_le_sum (f := fun ν' => if μ < ν' then plaquetteCurl ξ x μ ν' ^ 2 else 0)
      (fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ ν)
    simpa [h] using this
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun μ' => ∑ ν' : Fin 4, if μ' < ν' then plaquetteCurl ξ x μ' ν' ^ 2 else 0)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ μ)
private def nearCurlEnergy (ξ : RealOneForm (n * (2 * ℓ + 1))) (Y : TorusSite n) : ℝ :=
  ∑ z ∈ centredCube (2 * (3 * ℓ + 1) + 1), siteCurlEnergy ξ (blockCentreSite (2 * ℓ + 1) Y + siteOfInt z)
private theorem nearCurlEnergy_nonneg (ξ : RealOneForm (n * (2 * ℓ + 1))) (Y : TorusSite n) :
    0 ≤ nearCurlEnergy ξ Y :=
  Finset.sum_nonneg fun _ _ => siteCurlEnergy_nonneg _ _
private theorem sq_le_local (ξ : RealOneForm (n * (2 * ℓ + 1))) (hξ : VanishesOnBlockTrees (2 * ℓ + 1) ξ)
    (Y : TorusSite n) {e : Fin 4 → ℤ} (he : e ∈ centredCube (2 * ℓ + 1)) (μ : Fin 4) :
    ξ (blockCentreSite (2 * ℓ + 1) Y + siteOfInt e, μ) ^ 2 ≤
      2 * contourAverage (2 * ℓ + 1) ξ (Y, μ) ^ 2 + 2 * blockConstant ℓ ^ 2 * nearCurlEnergy ξ Y := by
  set x₀ := blockCentreSite (2 * ℓ + 1) Y with hx₀
  set K := Real.sqrt (nearCurlEnergy ξ Y) with hKdef
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hK2 : K ^ 2 = nearCurlEnergy ξ Y := Real.sq_sqrt (nearCurlEnergy_nonneg ξ Y)
  have hlt : ∀ z, InBox (3 * ℓ + 1) z → ∀ a b, a < b → |latticeCurl (pullback ξ x₀) z a b| ≤ K := by
    intro z hz a b hab
    refine Real.abs_le_sqrt ?_
    rw [latticeCurl_pullback]
    refine (sq_plaquetteCurl_le ξ _ hab).trans ?_
    exact Finset.single_le_sum (f := fun z => siteCurlEnergy ξ (blockCentreSite (2 * ℓ + 1) Y + siteOfInt z))
      (fun _ _ => siteCurlEnergy_nonneg _ _) (mem_centredCube_iff.mpr hz)
  have hc : ∀ z, InBox (3 * ℓ + 1) z → ∀ a b, a ≠ b → |latticeCurl (pullback ξ x₀) z a b| ≤ K := by
    intro z hz a b hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact hlt z hz a b h
    · have e2 : latticeCurl (pullback ξ x₀) z a b = - latticeCurl (pullback ξ x₀) z b a := by
        simp only [latticeCurl]
        ring
      rw [e2, abs_neg]
      exact hlt z hz b a h
  have ht0 : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → (∀ l, ν < l → z l = 0) →
      pullback ξ x₀ (z, ν) = 0 :=
    fun z ν hz hz1 hup => hξ _ (isBlockTreeBond_of Y hz hz1 hup)
  have ht1 : ∀ z ν, InBox ℓ z → InBox ℓ (z + basisVector ν) → (∀ l, ν < l → z l = 0) →
      translateForm (pullback ξ x₀) (neighbourCentre ℓ μ) (z, ν) = 0 := by
    intro z ν hz hz1 hup
    rw [translateForm_pullback, hx₀, ← blockCentreSite_add_unitStep]
    exact hξ _ (isBlockTreeBond_of (Y + unitStep n μ) hz hz1 hup)
  have main := bond_le_average hK μ hc ht0 ht1 (mem_centredCube_iff.mp he)
  have hmean : (1 / (24 * (((2 * ℓ + 1 : ℕ) : ℝ)) ^ 4)) * ∑ h ∈ centredCube (2 * ℓ + 1), ∑ π : Equiv.Perm (Fin 4),
      latticeLineSum (pullback ξ x₀) 0 (bondContour (2 * ℓ + 1) h π μ) = contourAverage (2 * ℓ + 1) ξ (Y, μ) := by
    simp only [contourAverage, slopeCentre_eq, ← hx₀]
    congr 1
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun π _ => ?_
    rw [← pathIntegral_eq_lineSum, siteOfInt_zero_offset, add_zero]
  rw [hmean] at main
  have main' : |ξ (x₀ + siteOfInt e, μ)| ≤ |contourAverage (2 * ℓ + 1) ξ (Y, μ)| + blockConstant ℓ * K := main
  rw [← hK2]
  have hsq : ξ (x₀ + siteOfInt e, μ) ^ 2 ≤ (|contourAverage (2 * ℓ + 1) ξ (Y, μ)| + blockConstant ℓ * K) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) main' 2
  have hab := sq_abs (contourAverage (2 * ℓ + 1) ξ (Y, μ))
  nlinarith [sq_nonneg (|contourAverage (2 * ℓ + 1) ξ (Y, μ)| - blockConstant ℓ * K)]
private theorem sum_nearCurlEnergy_le (hL : Odd (2 * ℓ + 1)) (ξ : RealOneForm (n * (2 * ℓ + 1))) :
    ∑ Y : TorusSite n, nearCurlEnergy ξ Y ≤ ((centredCube (2 * (3 * ℓ + 1) + 1)).card : ℝ) * curlEnergy ξ := by
  unfold nearCurlEnergy
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _z ∈ centredCube (2 * (3 * ℓ + 1) + 1), curlEnergy ξ :=
        Finset.sum_le_sum fun z _ => sum_blocks_le hL z (siteCurlEnergy ξ) (siteCurlEnergy_nonneg ξ)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
private theorem sum_sq_le (hL : Odd (2 * ℓ + 1)) (ξ : RealOneForm (n * (2 * ℓ + 1)))
    (hξ : VanishesOnBlockTrees (2 * ℓ + 1) ξ) :
    ∑ b, ξ b ^ 2 ≤ (((2 * ℓ + 1 : ℕ) : ℝ) ^ 4 *
        (2 + 8 * blockConstant ℓ ^ 2 * ((centredCube (2 * (3 * ℓ + 1) + 1)).card : ℝ))) *
      (curlEnergy ξ + ∑ c : TorusBond n, contourAverage (2 * ℓ + 1) ξ c ^ 2) := by
  set p : ℝ := ((2 * ℓ + 1 : ℕ) : ℝ) ^ 4 with hp
  set d : ℝ := 8 * blockConstant ℓ ^ 2 with hd
  set N : ℝ := ((centredCube (2 * (3 * ℓ + 1) + 1)).card : ℝ) with hN
  set A : ℝ := ∑ c : TorusBond n, contourAverage (2 * ℓ + 1) ξ c ^ 2 with hA
  have hcs : 0 ≤ curlEnergy ξ := Finset.sum_nonneg fun x _ => siteCurlEnergy_nonneg ξ x
  have hcard : ((centredCube (2 * ℓ + 1)).card : ℝ) = p := by rw [card_centredCube, hp, Nat.cast_pow]
  have step1 : ∑ b, ξ b ^ 2 ≤ ∑ Y : TorusSite n, ∑ e ∈ centredCube (2 * ℓ + 1), ∑ μ : Fin 4,
      ξ (blockCentreSite (2 * ℓ + 1) Y + siteOfInt e, μ) ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact sum_le_sum_blocks hL (fun x => ∑ μ : Fin 4, ξ (x, μ) ^ 2) fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have step2 : ∀ Y : TorusSite n, ∑ e ∈ centredCube (2 * ℓ + 1), ∑ μ : Fin 4,
      ξ (blockCentreSite (2 * ℓ + 1) Y + siteOfInt e, μ) ^ 2 ≤
        p * (2 * ∑ μ : Fin 4, contourAverage (2 * ℓ + 1) ξ (Y, μ) ^ 2 + d * nearCurlEnergy ξ Y) := by
    intro Y
    calc _ ≤ ∑ _e ∈ centredCube (2 * ℓ + 1), ∑ μ : Fin 4,
          (2 * contourAverage (2 * ℓ + 1) ξ (Y, μ) ^ 2 + 2 * blockConstant ℓ ^ 2 * nearCurlEnergy ξ Y) :=
          Finset.sum_le_sum fun e he => Finset.sum_le_sum fun μ _ => sq_le_local ξ hξ Y he μ
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hd]
        push_cast
        ring
  have step3 : ∑ Y : TorusSite n,
      p * (2 * ∑ μ : Fin 4, contourAverage (2 * ℓ + 1) ξ (Y, μ) ^ 2 + d * nearCurlEnergy ξ Y) =
      2 * p * A + d * p * ∑ Y : TorusSite n, nearCurlEnergy ξ Y := by
    rw [hA, Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y _ => ?_
    ring
  have hW := sum_nearCurlEnergy_le hL ξ
  have h1 : d * p * ∑ Y : TorusSite n, nearCurlEnergy ξ Y ≤ d * p * (N * curlEnergy ξ) :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  have h2 : 0 ≤ 2 * p * curlEnergy ξ := by positivity
  have h3 : 0 ≤ d * N * p * A := by positivity
  calc _ ≤ _ := step1
    _ ≤ _ := Finset.sum_le_sum fun Y _ => step2 Y
    _ = _ := step3
    _ ≤ p * (2 + d * N) * (curlEnergy ξ + A) := by nlinarith
end Torus
theorem offTreeFormLowerBound : offTreeFormLowerBoundStatement := by
  intro L hL
  obtain ⟨ℓ, rfl⟩ := hL.1
  refine ⟨((2 * ℓ + 1 : ℕ) : ℝ) ^ 4 *
      (2 + 8 * blockConstant ℓ ^ 2 * ((centredCube (2 * (3 * ℓ + 1) + 1)).card : ℝ)), ?_,
    Filter.Eventually.of_forall fun n _ _ ξ hξ => sum_sq_le hL.1 ξ hξ⟩
  have : (0 : ℝ) ≤ 8 * blockConstant ℓ ^ 2 * ((centredCube (2 * (3 * ℓ + 1) + 1)).card : ℝ) := by positivity
  positivity
end YangMills.Construction.RunningCouplingSlope.OffTreeForms
end
