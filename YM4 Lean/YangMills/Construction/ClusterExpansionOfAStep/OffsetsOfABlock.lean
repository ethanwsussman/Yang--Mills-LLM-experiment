import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.LumpsAreFibres
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.HoleBesideASecondHole.CutActionIsTheLeastActionProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.BlockOffsets
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepSettings YangMills.Construction.StepCosts
section
variable {L n : ℕ}
theorem period_zero (i : Fin 4) : (stepBlockFrame L n).period 0 i = n * L := by
  simp [BlockFrame.period, stepBlockFrame, BlockFrame.top]
theorem period_one (i : Fin 4) : (stepBlockFrame L n).period 1 i = n := by
  simp [BlockFrame.period, stepBlockFrame, BlockFrame.top]
theorem intCast_cast_of_eq (P N : ℕ) (h : P = N) [NeZero P] (z : ℤ) :
    (((ZMod.cast (z : ZMod P) : ℤ)) : ZMod N) = (z : ZMod N) := by apply _root_.YangMills.Construction.TorusLumps.castInt_intCast <;> assumption
theorem intCast_sub_mul_of_eq (P N : ℕ) (h : P = N) (A k : ℤ) :
    ((A - (N : ℤ) * k : ℤ) : ZMod P) = (A : ZMod P) := by
  subst h
  simp
variable [NeZero L] [NeZero n]
theorem siteCoords_siteOfCoords_zero (z : Fin 4 → ℤ) (i : Fin 4) :
    siteCoords (siteOfCoords (F := stepBlockFrame L n) 0 z) i = z i % ((n * L : ℕ) : ℤ) := by
  have h := ZMod.coe_intCast (n := (stepBlockFrame L n).period 0 i) (z i)
  simp only [siteCoords, siteOfCoords]
  rw [h, period_zero]
theorem siteCoords_siteOfCoords_one (z : Fin 4 → ℤ) (i : Fin 4) :
    siteCoords (siteOfCoords (F := stepBlockFrame L n) 1 z) i = z i % (n : ℤ) := by
  have h := ZMod.coe_intCast (n := (stepBlockFrame L n).period 1 i) (z i)
  simp only [siteCoords, siteOfCoords]
  rw [h, period_one]
theorem readAtLevel_siteOfCoords (W : TorusField (n * L)) (z : Fin 4 → ℤ) (i : Fin 4) :
    readAtLevel (stepBlockFrame L n) 0 W (siteOfCoords 0 z) i = W (siteOfInt z) i := by
  unfold readAtLevel
  congr 1
  funext k
  simp only [siteOfInt]
  rw [siteCoords_siteOfCoords_zero]
  exact ZMod.intCast_mod _ _
theorem torusSiteInFrame_siteOfInt (z : Fin 4 → ℤ) :
    torusSiteInFrame (stepBlockFrame L n) 0 (siteOfInt z : TorusSite (n * L)) = siteOfCoords 0 z := by
  funext i
  simp only [torusSiteInFrame, siteOfCoords, siteOfInt]
  exact intCast_cast_of_eq (n * L) _ (period_zero i).symm (z i)
omit [NeZero L] [NeZero n] in
theorem siteOfCoords_add (j : ℕ) (z w : Fin 4 → ℤ) :
    (siteOfCoords (F := stepBlockFrame L n) j (z + w)) = siteOfCoords j z + siteOfCoords j w := by
  funext i
  simp [siteOfCoords]
omit [NeZero L] [NeZero n] in
theorem mem_centredCube_iff (o : Fin 4 → ℤ) :
    o ∈ centredCube L ↔ ∀ i, -(((L : ℤ) - 1) / 2) ≤ o i ∧ o i ≤ ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
def blockPoint (L : ℕ) (A o : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * A i + o i
theorem enclosingCell_blockPoint (hodd : Odd L) (A o : Fin 4 → ℤ) (ho : o ∈ centredCube L) :
    enclosingCell (siteOfCoords (F := stepBlockFrame L n) 0 (blockPoint L A o)) = siteOfCoords 1 A := by
  obtain ⟨H, hH⟩ := hodd
  have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
  funext i
  have hb := (mem_centredCube_iff o).mp ho i
  rw [hL] at hb
  have hpow : ((stepBlockFrame L n).blockSide : ℤ) ^ ((stepBlockFrame L n).top - 0) = (L : ℤ) := by
    simp [stepBlockFrame, BlockFrame.top]
  simp only [enclosingCell, siteOfCoords]
  rw [hpow, siteCoords_siteOfCoords_zero]
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Z := blockPoint L A o i with hZ
  set k := Z / ((n * L : ℕ) : ℤ) with hk
  have hmod : Z % ((n * L : ℕ) : ℤ) = Z - ((n * L : ℕ) : ℤ) * k := by
    rw [Int.emod_def]
  have hq : (Z % ((n * L : ℕ) : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) = A i - (n : ℤ) * k := by
    have := (Int.ediv_emod_unique (a := Z % ((n * L : ℕ) : ℤ) + ((L : ℤ) - 1) / 2) (b := (L : ℤ))
      (r := o i + H) (q := A i - (n : ℤ) * k) hLpos).mpr ⟨?_, by omega, ?_⟩
    · exact this.1
    · rw [hmod, hL, hZ]
      simp only [blockPoint]
      push_cast
      ring
    · subst hH
      push_cast
      omega
  rw [hq]
  exact intCast_sub_mul_of_eq _ n (period_one i) (A i) k
theorem cellCentre_siteOfCoords (A : Fin 4 → ℤ) :
    cellCentre (F := stepBlockFrame L n) 0 (siteOfCoords 1 A) = siteOfCoords 0 fun i => (L : ℤ) * A i := by
  funext i
  have hpow : ((stepBlockFrame L n).blockSide : ℤ) ^ ((stepBlockFrame L n).top - 0) = (L : ℤ) := by
    simp [stepBlockFrame, BlockFrame.top]
  simp only [cellCentre, siteOfCoords]
  rw [hpow]
  have hc : siteCoords (j := 1) (siteOfCoords (F := stepBlockFrame L n) 1 A) i = A i % (n : ℤ) :=
    siteCoords_siteOfCoords_one A i
  show (Int.cast ((L : ℤ) * siteCoords (j := 1) (siteOfCoords (F := stepBlockFrame L n) 1 A) i) :
    ZMod ((stepBlockFrame L n).period 0 i)) = Int.cast ((L : ℤ) * A i)
  rw [hc]
  have h1 : (L : ℤ) * (A i % (n : ℤ)) = (L : ℤ) * A i - ((n * L : ℕ) : ℤ) * (A i / (n : ℤ)) := by
    rw [Int.emod_def]
    push_cast
    ring
  have := intCast_sub_mul_of_eq _ (n * L) (period_zero (L := L) (n := n) i) ((L : ℤ) * A i) (A i / (n : ℤ))
  rw [h1]
  exact this
theorem cellOffset_blockPoint (hodd : Odd L) (A o : Fin 4 → ℤ) (ho : o ∈ centredCube L) :
    cellOffset (F := stepBlockFrame L n) (siteOfCoords 0 (blockPoint L A o)) = o := by
  funext i
  have hb := (mem_centredCube_iff o).mp ho i
  obtain ⟨H, hH⟩ := hodd
  have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
  rw [hL] at hb
  have hc := enclosingCell_blockPoint (n := n) ⟨H, hH⟩ A o ho
  show (((siteOfCoords (F := stepBlockFrame L n) 0 (blockPoint L A o)) -
    cellCentre (F := stepBlockFrame L n) 0
      (enclosingCell (siteOfCoords (F := stepBlockFrame L n) 0 (blockPoint L A o)))) i).valMinAbs = o i
  rw [hc, cellCentre_siteOfCoords]
  have hne : NeZero ((stepBlockFrame L n).period 0 i) := inferInstance
  rw [ZMod.valMinAbs_spec]
  constructor
  · simp [siteOfCoords, blockPoint]
  · rw [period_zero]
    have hn : (1 : ℤ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    have hLn : (L : ℤ) ≤ (n : ℤ) * L := by nlinarith [(show (0 : ℤ) ≤ L by positivity)]
    have hLH : (L : ℤ) = 2 * H + 1 := by subst hH; push_cast; ring
    constructor
    · push_cast; omega
    · push_cast; omega
theorem siteOfCoords_blockPoint_add_unitStep (A o : Fin 4 → ℤ) (i : Fin 4) :
    siteOfCoords (F := stepBlockFrame L n) 0 (blockPoint L A o) + BlockAverages.unitStep 0 i =
      siteOfCoords 0 (blockPoint L A (o + Pi.single i 1)) := by
  unfold BlockAverages.unitStep
  rw [← siteOfCoords_add]
  congr 1
  funext l
  simp only [blockPoint, Pi.add_apply]
  ring
theorem isCrossingBond_blockPoint_iff (hodd : Odd L) (hn : 2 ≤ n) (A o : Fin 4 → ℤ) (ho : o ∈ centredCube L)
    (i : Fin 4) :
    IsCrossingBond (F := stepBlockFrame L n) (siteOfCoords 0 (blockPoint L A o), i) ↔
      o + Pi.single i 1 ∉ centredCube L := by
  have hc := enclosingCell_blockPoint (n := n) hodd A o ho
  have hu : (siteOfCoords (F := stepBlockFrame L n) 0 (blockPoint L A o) + BlockAverages.unitStep 0 i) =
      siteOfCoords 0 (blockPoint L A (o + Pi.single i 1)) := siteOfCoords_blockPoint_add_unitStep A o i
  show @enclosingCell (stepBlockFrame L n) 0 (siteOfCoords (F := stepBlockFrame L n) 0 (blockPoint L A o) +
      BlockAverages.unitStep (F := stepBlockFrame L n) 0 i) ≠
    @enclosingCell (stepBlockFrame L n) 0 (siteOfCoords (F := stepBlockFrame L n) 0 (blockPoint L A o)) ↔ _
  rw [hc, hu]
  by_cases hin : o + Pi.single i 1 ∈ centredCube L
  · rw [enclosingCell_blockPoint hodd A _ hin]
    constructor
    · intro h
      exact absurd rfl h
    · intro h
      exact absurd hin h
  · simp only [hin, not_false_eq_true, iff_true]
    obtain ⟨H, hH⟩ := id hodd
    have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
    have hLH : (L : ℤ) = 2 * H + 1 := by subst hH; push_cast; ring
    have hb := (mem_centredCube_iff o).mp ho
    rw [hL] at hb
    have hoi : o i = H := by
      by_contra hne
      apply hin
      rw [mem_centredCube_iff, hL]
      intro l
      by_cases hl : l = i
      · subst hl
        have := hb l
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · have := hb l
        simpa [Pi.single_apply, hl] using this
    set o' : Fin 4 → ℤ := o + Pi.single i 1 - (L : ℤ) • Pi.single i 1 with ho'
    have ho'c : o' ∈ centredCube L := by
      rw [mem_centredCube_iff, hL]
      intro l
      by_cases hl : l = i
      · subst hl
        simp only [ho', Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        omega
      · have := hb l
        simpa [ho', Pi.single_apply, hl] using this
    have hpt : blockPoint L A (o + Pi.single i 1) = blockPoint L (A + Pi.single i 1) o' := by
      funext l
      simp only [blockPoint, ho', Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hpt, enclosingCell_blockPoint hodd _ _ ho'c]
    intro heq
    have h1 := congrFun heq i
    simp only [siteOfCoords, Pi.add_apply, Pi.single_eq_same] at h1
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_one] at h1
    have h2 : ((n : ℕ) : ℤ) ∣ 1 := by
      have : A i - (A i + 1) = -1 := by ring
      rw [this] at h1
      simpa using h1
    have h3 := Int.le_of_dvd one_pos h2
    omega
theorem isAxialTreeBond_blockPoint (hodd : Odd L) (hn : 2 ≤ n) (A o : Fin 4 → ℤ) (ho : o ∈ centredCube L)
    (i : Fin 4) (ho' : o + Pi.single i 1 ∈ centredCube L) (hz : ∀ l, i < l → o l = 0) :
    IsAxialTreeBond (F := stepBlockFrame L n) (siteOfCoords 0 (blockPoint L A o), i) := by
  refine ⟨fun h => ((isCrossingBond_blockPoint_iff hodd hn A o ho i).mp h) ho', fun l hl => ?_⟩
  have := cellOffset_blockPoint (n := n) hodd A o ho
  show cellOffset (F := stepBlockFrame L n) (siteOfCoords 0 (blockPoint L A o)) l = 0
  rw [this]
  exact hz l hl
def pathBonds : (Fin 4 → ℤ) → List PathStep → List ((Fin 4 → ℤ) × Fin 4)
  | _, [] => []
  | u, st :: r =>
    (if st.2 then (u, st.1) else (u - Pi.single st.1 1, st.1)) ::
      pathBonds (if st.2 then u + Pi.single st.1 1 else u - Pi.single st.1 1) r
theorem pathHolonomy_congr {n' : ℕ} [NeZero n'] (W : TorusField (n * L)) (W' : TorusField (n' * L))
    (Z Z' : Fin 4 → ℤ) :
    ∀ (l : List PathStep) (u : Fin 4 → ℤ),
      (∀ b ∈ pathBonds u l, W (siteOfInt (Z + b.1)) b.2 = W' (siteOfInt (Z' + b.1)) b.2) →
      pathHolonomy (readAtLevel (stepBlockFrame L n) 0 W) (siteOfCoords 0 (Z + u)) l =
        pathHolonomy (readAtLevel (stepBlockFrame L n') 0 W') (siteOfCoords 0 (Z' + u)) l := by
  intro l
  induction l with
  | nil => intro u _; rfl
  | cons st r ih =>
    intro u h
    obtain ⟨i, d⟩ := st
    cases d with
    | true =>
      have h0 := h (u, i) (by simp [pathBonds])
      have h1 := ih (u + Pi.single i 1) (fun b hb => h b (by simp [pathBonds, hb]))
      simp only [pathHolonomy, linkValue, stepDisplacement, if_true]
      rw [readAtLevel_siteOfCoords, readAtLevel_siteOfCoords, h0]
      congr 1
      have e : ∀ (m : ℕ) (Z : Fin 4 → ℤ),
          siteOfCoords (F := stepBlockFrame L m) 0 (Z + u) + BlockAverages.unitStep 0 i =
            siteOfCoords 0 (Z + (u + Pi.single i 1)) := by
        intro m Z
        unfold BlockAverages.unitStep
        rw [← siteOfCoords_add, add_assoc]
      rw [e, e]
      exact h1
    | false =>
      have h0 := h (u - Pi.single i 1, i) (by simp [pathBonds])
      have h1 := ih (u - Pi.single i 1) (fun b hb => h b (by simp [pathBonds, hb]))
      have e0 : ∀ (m : ℕ) (Z : Fin 4 → ℤ),
          siteOfCoords (F := stepBlockFrame L m) 0 (Z + u) - BlockAverages.unitStep 0 i =
            siteOfCoords 0 (Z + (u - Pi.single i 1)) := by
        intro m Z
        funext l
        simp [siteOfCoords, BlockAverages.unitStep]
        ring
      simp only [pathHolonomy, linkValue, stepDisplacement, Bool.false_eq_true, if_false]
      rw [e0, e0, readAtLevel_siteOfCoords, readAtLevel_siteOfCoords, h0]
      congr 1
      have e1 : ∀ (m : ℕ) (Z : Fin 4 → ℤ),
          siteOfCoords (F := stepBlockFrame L m) 0 (Z + u) + -BlockAverages.unitStep 0 i =
            siteOfCoords 0 (Z + (u - Pi.single i 1)) := by
        intro m Z
        rw [← sub_eq_add_neg]
        exact e0 m Z
      rw [e1, e1]
      exact h1
def IsAxialBond (H : ℤ) (b : (Fin 4 → ℤ) × Fin 4) : Prop :=
  (∀ l, -H ≤ b.1 l ∧ b.1 l ≤ H) ∧
    (∀ l, -H ≤ (b.1 + Pi.single b.2 (1 : ℤ) : Fin 4 → ℤ) l ∧ (b.1 + Pi.single b.2 (1 : ℤ) : Fin 4 → ℤ) l ≤ H) ∧
    ∀ l, b.2 < l → b.1 l = 0
theorem isAxialBond_of_mem_straight {H : ℤ} {o : Fin 4 → ℤ} (hc : ∀ l, -H ≤ o l ∧ o l ≤ H) (i : Fin 4)
    (d : Bool) (hd : d = decide (0 ≤ o i)) :
    ∀ (m : ℕ) (u : Fin 4 → ℤ), (∀ l, l < i → u l = o l) → (∀ l, i < l → u l = 0) →
      (u i + (if d then (m : ℤ) else -(m : ℤ)) = o i) → (if d then 0 ≤ u i else u i ≤ 0) →
      ∀ b ∈ pathBonds u (List.replicate m (i, d)), IsAxialBond H b := by
  have hH : 0 ≤ H := by
    have := hc i
    omega
  intro m
  induction m with
  | zero => intro u _ _ _ _ b hb; simp [pathBonds] at hb
  | succ m ih =>
    intro u hlo hhi hend hsgn b hb
    rw [List.replicate_succ] at hb
    cases d with
    | true =>
      have hp : 0 ≤ o i := by simpa using hd.symm
      simp only [if_true] at hend hsgn
      push_cast at hend
      simp only [pathBonds, if_true, List.mem_cons] at hb
      have hoi := hc i
      rcases hb with rfl | hb
      · refine ⟨fun l => ?_, fun l => ?_, fun l hl => hhi l hl⟩
        · rcases lt_trichotomy l i with h | h | h
          · have := hc l; show -H ≤ u l ∧ u l ≤ H; rw [hlo l h]; exact this
          · subst h; show -H ≤ u l ∧ u l ≤ H; omega
          · show -H ≤ u l ∧ u l ≤ H; rw [hhi l h]; omega
        · rcases lt_trichotomy l i with h | h | h
          · have := hc l
            simp only [Pi.add_apply, Pi.single_apply, if_neg (ne_of_lt h), add_zero]
            rw [hlo l h]; exact this
          · subst h; simp only [Pi.add_apply, Pi.single_eq_same]; omega
          · simp only [Pi.add_apply, Pi.single_apply, if_neg (ne_of_gt h), add_zero]
            rw [hhi l h]; omega
      · refine ih (u + Pi.single i 1) (fun l hl => ?_) (fun l hl => ?_) ?_ ?_ b hb
        · simp only [Pi.add_apply, Pi.single_apply, if_neg (ne_of_lt hl), add_zero]; exact hlo l hl
        · simp only [Pi.add_apply, Pi.single_apply, if_neg (ne_of_gt hl), add_zero]; exact hhi l hl
        · simp only [Pi.add_apply, Pi.single_eq_same, if_true] <;> omega
        · simp only [Pi.add_apply, Pi.single_eq_same, if_true] <;> omega
    | false =>
      have hp : o i < 0 := by
        have : ¬ 0 ≤ o i := by simpa using hd.symm
        omega
      simp only [Bool.false_eq_true, if_false] at hend hsgn
      push_cast at hend
      simp only [pathBonds, Bool.false_eq_true, if_false, List.mem_cons] at hb
      have hoi := hc i
      rcases hb with rfl | hb
      · refine ⟨fun l => ?_, fun l => ?_, fun l hl => ?_⟩
        · rcases lt_trichotomy l i with h | h | h
          · have := hc l
            simp only [Pi.sub_apply, Pi.single_apply, if_neg (ne_of_lt h), sub_zero]
            rw [hlo l h]; exact this
          · subst h; simp only [Pi.sub_apply, Pi.single_eq_same]; omega
          · simp only [Pi.sub_apply, Pi.single_apply, if_neg (ne_of_gt h), sub_zero]
            rw [hhi l h]; omega
        · simp only [sub_add_cancel]
          rcases lt_trichotomy l i with h | h | h
          · have := hc l; rw [hlo l h]; exact this
          · subst h; omega
          · rw [hhi l h]; omega
        · simp only [Pi.sub_apply, Pi.single_apply, if_neg (ne_of_gt hl), sub_zero]; exact hhi l hl
      · refine ih (u - Pi.single i 1) (fun l hl => ?_) (fun l hl => ?_) ?_ ?_ b hb
        · simp only [Pi.sub_apply, Pi.single_apply, if_neg (ne_of_lt hl), sub_zero]; exact hlo l hl
        · simp only [Pi.sub_apply, Pi.single_apply, if_neg (ne_of_gt hl), sub_zero]; exact hhi l hl
        · simp only [Pi.sub_apply, Pi.single_eq_same, Bool.false_eq_true, if_false] <;> omega
        · simp only [Pi.sub_apply, Pi.single_eq_same, Bool.false_eq_true, if_false] <;> omega
def straightEnd (u : Fin 4 → ℤ) (i : Fin 4) (d : Bool) (m : ℕ) : Fin 4 → ℤ :=
  u + (if d then (m : ℤ) else -(m : ℤ)) • Pi.single i 1
theorem pathBonds_replicate_append (i : Fin 4) (d : Bool) (r : List PathStep) :
    ∀ (m : ℕ) (u : Fin 4 → ℤ), pathBonds u (List.replicate m (i, d) ++ r) =
      pathBonds u (List.replicate m (i, d)) ++ pathBonds (straightEnd u i d m) r := by
  intro m
  induction m with
  | zero => intro u; simp [pathBonds, straightEnd]
  | succ m ih =>
    intro u
    rw [List.replicate_succ, List.cons_append]
    simp only [pathBonds, List.cons_append, List.cons.injEq, true_and]
    rw [ih]
    congr 2
    cases d <;> simp only [straightEnd, if_true, Bool.false_eq_true, if_false] <;> funext l <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> push_cast <;> ring
def truncate (o : Fin 4 → ℤ) (k : ℕ) : Fin 4 → ℤ := fun l => if l.val < k then o l else 0
theorem straightEnd_truncate (o : Fin 4 → ℤ) (k : Fin 4) :
    straightEnd (truncate o k.val) k (decide (0 ≤ o k)) (o k).natAbs = truncate o (k.val + 1) := by
  funext l
  simp only [straightEnd, truncate, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hl : l = k
  · subst hl
    by_cases h0 : 0 ≤ o l
    · simp [h0, abs_of_nonneg h0]
    · have : o l < 0 := not_le.mp h0
      simp [h0, abs_of_neg this]
  · have hne : l.val ≠ k.val := fun h => hl (Fin.ext h)
    have e : (l.val < k.val + 1) ↔ l.val < k.val := by omega
    simp [hl, e]
theorem isAxialBond_of_stage {H : ℤ} {o : Fin 4 → ℤ} (hc : ∀ l, -H ≤ o l ∧ o l ≤ H) (k : Fin 4)
    (r : List PathStep) (hr : ∀ b ∈ pathBonds (truncate o (k.val + 1)) r, IsAxialBond H b) :
    ∀ b ∈ pathBonds (truncate o k.val) (List.replicate (o k).natAbs (k, decide (0 ≤ o k)) ++ r),
      IsAxialBond H b := by
  intro b hb
  rw [pathBonds_replicate_append, straightEnd_truncate, List.mem_append] at hb
  rcases hb with hb | hb
  · refine isAxialBond_of_mem_straight hc k _ rfl _ _ (fun l hl => ?_) (fun l hl => ?_) ?_ ?_ b hb
    · simp [truncate, hl]
    · have : ¬ l.val < k.val := by
        have := Fin.lt_def.mp hl
        omega
      simp [truncate, this]
    · by_cases h0 : 0 ≤ o k
      · simp [truncate, h0, abs_of_nonneg h0]
      · have : o k < 0 := not_le.mp h0
        simp [truncate, h0, abs_of_neg this]
    · by_cases h0 : 0 ≤ o k <;> simp [truncate, h0]
  · exact hr b hb
theorem isAxialBond_of_mem_axisPath {H : ℤ} {o : Fin 4 → ℤ} (hc : ∀ l, -H ≤ o l ∧ o l ≤ H) :
    ∀ b ∈ pathBonds 0 (axisPath o 1), IsAxialBond H b := by
  have e : axisPath o 1 = List.replicate (o 0).natAbs (0, decide (0 ≤ o 0)) ++
      (List.replicate (o 1).natAbs (1, decide (0 ≤ o 1)) ++
        (List.replicate (o 2).natAbs (2, decide (0 ≤ o 2)) ++
          (List.replicate (o 3).natAbs (3, decide (0 ≤ o 3)) ++ []))) := by
    simp [axisPath, List.finRange_succ, List.flatMap_cons]
    rfl
  have h0 : (0 : Fin 4 → ℤ) = truncate o 0 := by
    funext l
    simp [truncate]
  rw [e, h0]
  refine isAxialBond_of_stage hc 0 _ (isAxialBond_of_stage hc 1 _
    (isAxialBond_of_stage hc 2 _ (isAxialBond_of_stage hc 3 _ ?_)))
  intro b hb
  simp [pathBonds] at hb
theorem parentBlock_blockPoint (hodd : Odd L) (A o : Fin 4 → ℤ) (ho : o ∈ centredCube L) :
    parentBlock L (siteOfInt (blockPoint L A o) : TorusSite (n * L)) = siteOfInt A := by
  obtain ⟨H, hH⟩ := hodd
  have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
  funext i
  have hb := (mem_centredCube_iff o).mp ho i
  rw [hL] at hb
  simp only [parentBlock, siteOfInt]
  have hc := ZMod.coe_intCast (n := n * L) (blockPoint L A o i)
  rw [hc]
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Z := blockPoint L A o i with hZ
  set k := Z / ((n * L : ℕ) : ℤ) with hk
  have hmod : Z % ((n * L : ℕ) : ℤ) = Z - ((n * L : ℕ) : ℤ) * k := by
    rw [Int.emod_def]
  have hq : (Z % ((n * L : ℕ) : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) = A i - (n : ℤ) * k := by
    have := (Int.ediv_emod_unique (a := Z % ((n * L : ℕ) : ℤ) + ((L : ℤ) - 1) / 2) (b := (L : ℤ))
      (r := o i + H) (q := A i - (n : ℤ) * k) hLpos).mpr ⟨?_, by omega, ?_⟩
    · exact this.1
    · rw [hmod, hL, hZ]
      simp only [blockPoint]
      push_cast
      ring
    · subst hH
      push_cast
      omega
  rw [hq]
  exact intCast_sub_mul_of_eq _ n rfl (A i) k
omit [NeZero n] in
theorem exists_block_offset (hodd : Odd L) (c : Fin 4 → ℤ) :
    ∃ (kk o : Fin 4 → ℤ), o ∈ centredCube L ∧ ∀ l, c l = (L : ℤ) * kk l + o l := by
  obtain ⟨H, hH⟩ := hodd
  have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨fun l => (c l + H) / L, fun l => (c l + H) % L - H, ?_, fun l => ?_⟩
  · rw [mem_centredCube_iff, hL]
    intro l
    have h1 := Int.emod_nonneg (c l + H) hLpos.ne'
    have h2 := Int.emod_lt_of_pos (c l + H) hLpos
    have hLH : (L : ℤ) = 2 * H + 1 := by subst hH; push_cast; ring
    show -(H : ℤ) ≤ (c l + H) % L - H ∧ (c l + H) % L - H ≤ H
    constructor <;> omega
  · have := Int.mul_ediv_add_emod (c l + H) (L : ℤ)
    simp only
    linarith
omit [NeZero L] in
theorem siteOfInt_cast_add (Y : TorusSite n) (kk : Fin 4 → ℤ) :
    (siteOfInt (fun i => ((Y i).cast : ℤ) + kk i) : TorusSite n) = Y + siteOfInt kk := by
  funext i
  simp [siteOfInt]
omit [NeZero L] [NeZero n] in
theorem siteOfInt_add (e e' : Fin 4 → ℤ) :
    (siteOfInt (e + e') : TorusSite n) = siteOfInt e + siteOfInt e' := by
  funext i
  simp [siteOfInt]
omit [NeZero L] [NeZero n] in
theorem unitStep_eq_siteOfInt (N : ℕ) (i : Fin 4) : TorusFields.unitStep N i = siteOfInt (Pi.single i 1) := by
  funext l
  by_cases h : l = i
  · subst h; simp [TorusFields.unitStep, siteOfInt]
  · simp [TorusFields.unitStep, siteOfInt, Pi.single_apply, h]
end
section
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
def CoordsAgreeNear (s : ChartSetting R n) (s' : ChartSetting R n') (Y : TorusSite n) (Y' : TorusSite n')
    (k : ℕ) (η : FreeCoords s.free) (η' : FreeCoords s'.free) : Prop :=
  ∀ q, IsNearIndex R.params.side k q → s.coordsByIndex Y η q = s'.coordsByIndex Y' η' q
theorem gaugeAt_blockPoint (hodd : Odd R.params.side) (W : TorusField (n * R.params.side)) (A o : Fin 4 → ℤ)
    (ho : o ∈ centredCube R.params.side) :
    gaugeAt (R := R) W (siteOfInt (blockPoint R.params.side A o)) =
      pathHolonomy (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (siteOfCoords 0 fun i => (R.params.side : ℤ) * A i) (axisPath o 1) := by
  unfold gaugeAt axialGauge
  rw [torusSiteInFrame_siteOfInt]
  have hc := enclosingCell_blockPoint (n := n) hodd A o ho
  have hf := cellOffset_blockPoint (n := n) hodd A o ho
  show pathHolonomy _ (cellCentre (F := stepBlockFrame R.params.side n) 0
      (@enclosingCell (stepBlockFrame R.params.side n) 0 (siteOfCoords 0 (blockPoint R.params.side A o))))
      (axisPath (cellOffset (F := stepBlockFrame R.params.side n)
        (siteOfCoords 0 (blockPoint R.params.side A o))) 1) = _
  rw [hc, cellCentre_siteOfCoords, hf]
theorem blockPoint_not_mem_free (s : ChartSetting R n) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (hf : s.free ⊆ chartBonds R.params.side n) (A o : Fin 4 → ℤ) (i : Fin 4) (ho : o ∈ centredCube R.params.side)
    (ho' : o + Pi.single i 1 ∈ centredCube R.params.side) (hz : ∀ l, i < l → o l = 0) :
    (siteOfInt (blockPoint R.params.side A o), i) ∉ s.free := by
  intro h
  have h1 := hf h
  simp only [chartBonds, Finset.mem_filter, Finset.mem_univ, true_and] at h1
  apply h1
  rw [torusSiteInFrame_siteOfInt]
  exact isAxialTreeBond_blockPoint hodd hn A o ho i ho' hz
theorem gaugeAt_fineSite_eq {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m : ℕ} (hodd : Odd R.params.side) (hn : 2 ≤ n) (hf : s.free ⊆ chartBonds R.params.side n)
    (hag : SettingsAgreeNear s s' Y Y' m) (kk o : Fin 4 → ℤ) (hkk : OffsetInBox m kk)
    (ho : o ∈ centredCube R.params.side) :
    gaugeAt (R := R) s.fine (fineSite R.params.side Y kk o) =
      gaugeAt (R := R) s'.fine (fineSite R.params.side Y' kk o) := by
  set A : Fin 4 → ℤ := fun i => ((Y i).cast : ℤ) + kk i with hA
  set A' : Fin 4 → ℤ := fun i => ((Y' i).cast : ℤ) + kk i with hA'
  show gaugeAt (R := R) s.fine (siteOfInt (blockPoint R.params.side A o)) =
    gaugeAt (R := R) s'.fine (siteOfInt (blockPoint R.params.side A' o))
  rw [gaugeAt_blockPoint hodd _ A o ho, gaugeAt_blockPoint hodd _ A' o ho]
  have hc := (mem_centredCube_iff o).mp ho
  have key := pathHolonomy_congr (L := R.params.side) s.fine s'.fine (fun i => (R.params.side : ℤ) * A i)
    (fun i => (R.params.side : ℤ) * A' i) (axisPath o 1) 0 ?_
  · simpa only [add_zero] using key
  · intro b hb
    obtain ⟨g1, g2, g3⟩ := isAxialBond_of_mem_axisPath hc b hb
    have hb1 : b.1 ∈ centredCube R.params.side := (mem_centredCube_iff _).mpr g1
    have hb2 : b.1 + Pi.single b.2 1 ∈ centredCube R.params.side := (mem_centredCube_iff _).mpr g2
    have nf := blockPoint_not_mem_free s hodd hn hf A b.1 b.2 hb1 hb2 g3
    exact hag.fine_eq (kk, b.1, b.2) ⟨hkk, hb1⟩ nf
theorem fineSite_add_unitStep (L : ℕ) (Y : TorusSite n) (kk o : Fin 4 → ℤ) (i : Fin 4) :
    fineSite L Y kk o + TorusFields.unitStep (n * L) i = fineSite L Y kk (o + Pi.single i 1) := by
  rw [unitStep_eq_siteOfInt]
  show siteOfInt _ + siteOfInt _ = siteOfInt _
  rw [← siteOfInt_add]
  congr 1
  funext l
  simp only [Pi.add_apply]
  ring
theorem fineSite_wrap (L : ℕ) (Y : TorusSite n) (kk o : Fin 4 → ℤ) (i : Fin 4) :
    fineSite L Y kk (o + Pi.single i 1) =
      fineSite L Y (kk + Pi.single i 1) (o + Pi.single i 1 - (L : ℤ) • Pi.single i 1) := by
  show siteOfInt _ = siteOfInt _
  congr 1
  funext l
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem field_fineSite_eq {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n} {Y' : TorusSite n'}
    {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free} (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (hn' : 2 ≤ n') (hf : s.free ⊆ chartBonds R.params.side n) (hag : SettingsAgreeNear s s' Y Y' m) (hk : k ≤ m)
    (hnear : CoordsAgreeNear s s' Y Y' k η η') (kk o : Fin 4 → ℤ) (i : Fin 4)
    (ho : o ∈ centredCube R.params.side) (hkk : ∀ l, |kk l| + 1 ≤ (k : ℤ)) :
    s.field η (fineSite R.params.side Y kk o) i = s'.field η' (fineSite R.params.side Y' kk o) i := by
  have hin : OffsetInBox k kk := fun l => by have := hkk l; omega
  have hinm : OffsetInBox m kk := fun l => by have := hkk l; omega
  have hin1 : OffsetInBox m (kk + Pi.single i 1) := fun l => by
    have h1 := hkk l
    have h2 : |(kk + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ |kk l| + 1 := by
      simp only [Pi.add_apply, Pi.single_apply]
      split_ifs
      · exact (abs_add_le _ _).trans (by simp)
      · simp
    omega
  have hnr : IsNearIndex R.params.side k (kk, o, i) := ⟨hin, ho⟩
  have hnm : IsNearIndex R.params.side m (kk, o, i) := ⟨hinm, ho⟩
  by_cases hfr : nearBond R.params.side Y (kk, o, i) ∈ s.free
  · have hfr' := (hag.free_iff _ hnm).mp hfr
    have h1 := hnear _ hnr
    simp only [ChartSetting.coordsByIndex] at h1
    rw [dif_pos hfr, dif_pos hfr'] at h1
    have hfm := hag.frame_eq _ hnm hfr
    have e1 : s.field η (fineSite R.params.side Y kk o) i = chartLink s (fineSite R.params.side Y kk o) i
        (s.frame (nearBond R.params.side Y (kk, o, i)) + toImaginary (η ⟨_, hfr⟩)) := dif_pos hfr
    have e2 : s'.field η' (fineSite R.params.side Y' kk o) i = chartLink s' (fineSite R.params.side Y' kk o) i
        (s'.frame (nearBond R.params.side Y' (kk, o, i)) + toImaginary (η' ⟨_, hfr'⟩)) := dif_pos hfr'
    rw [e1, e2, h1, hfm]
    unfold chartLink
    rw [gaugeAt_fineSite_eq hodd hn hf hag kk o hinm ho, fineSite_add_unitStep, fineSite_add_unitStep]
    have hcr : ∀ (N : ℕ) [NeZero N], 2 ≤ N → ∀ (Z : TorusSite N),
        IsCrossingBond (F := stepBlockFrame R.params.side N)
          (torusSiteInFrame (stepBlockFrame R.params.side N) 0 (fineSite R.params.side Z kk o), i) ↔
          o + Pi.single i 1 ∉ centredCube R.params.side := by
      intro N _ hN Z
      show IsCrossingBond (F := stepBlockFrame R.params.side N) (torusSiteInFrame (stepBlockFrame R.params.side N) 0
        (siteOfInt (blockPoint R.params.side (fun i => ((Z i).cast : ℤ) + kk i) o)), i) ↔ _
      rw [torusSiteInFrame_siteOfInt]
      exact isCrossingBond_blockPoint_iff hodd hN _ o ho i
    have hblock : ∀ (N : ℕ) [NeZero N] (Z : TorusSite N),
        parentBlock R.params.side (fineSite R.params.side Z kk o) = Z + siteOfInt kk := by
      intro N _ Z
      show parentBlock R.params.side (siteOfInt (blockPoint R.params.side (fun i => ((Z i).cast : ℤ) + kk i) o) :
        TorusSite (N * R.params.side)) = _
      rw [parentBlock_blockPoint hodd _ o ho, siteOfInt_cast_add]
    by_cases hcube : o + Pi.single i 1 ∈ centredCube R.params.side
    · rw [if_neg (fun h => ((hcr n hn Y).mp h) hcube), if_neg (fun h => ((hcr n' hn' Y').mp h) hcube),
        gaugeAt_fineSite_eq hodd hn hf hag kk _ hinm hcube]
    · have hV : s.coarse (parentBlock R.params.side (fineSite R.params.side Y kk o)) i =
          s'.coarse (parentBlock R.params.side (fineSite R.params.side Y' kk o)) i := by
        rw [hblock, hblock]
        exact hag.coarse_agree (kk, i) ⟨hinm, hin1⟩
      rw [if_pos ((hcr n hn Y).mpr hcube), if_pos ((hcr n' hn' Y').mpr hcube), hV, fineSite_wrap, fineSite_wrap]
      have hwrap : o + Pi.single i 1 - (R.params.side : ℤ) • Pi.single i 1 ∈ centredCube R.params.side := by
        obtain ⟨H, hH⟩ := hodd
        have hL : ((R.params.side : ℤ) - 1) / 2 = (H : ℤ) := by rw [hH]; push_cast; omega
        have hLH : (R.params.side : ℤ) = 2 * H + 1 := by rw [hH]; push_cast; ring
        have hb := (mem_centredCube_iff o).mp ho
        rw [hL] at hb
        have hoi : o i = H := by
          by_contra hne
          apply hcube
          rw [mem_centredCube_iff, hL]
          intro l
          by_cases hl : l = i
          · subst hl
            have := hb l
            simp only [Pi.add_apply, Pi.single_eq_same]
            omega
          · have := hb l
            simpa [Pi.single_apply, hl] using this
        rw [mem_centredCube_iff, hL]
        intro l
        by_cases hl : l = i
        · subst hl
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
          omega
        · have := hb l
          simpa [Pi.single_apply, hl] using this
      rw [gaugeAt_fineSite_eq hodd hn hf hag _ _ hin1 hwrap]
  · have hfr' : nearBond R.params.side Y' (kk, o, i) ∉ s'.free := fun h => hfr ((hag.free_iff _ hnm).mpr h)
    have e1 : s.field η (fineSite R.params.side Y kk o) i = s.fine (fineSite R.params.side Y kk o) i :=
      dif_neg hfr
    have e2 : s'.field η' (fineSite R.params.side Y' kk o) i = s'.fine (fineSite R.params.side Y' kk o) i :=
      dif_neg hfr'
    rw [e1, e2]
    exact hag.fine_eq _ hnm hfr
end
section
variable {L n : ℕ} [NeZero L] [NeZero n]
omit [NeZero L] in
theorem siteOfInt_cast_self {N : ℕ} [NeZero N] (x : TorusSite N) :
    (siteOfInt (fun i => ((x i).cast : ℤ)) : TorusSite N) = x := by
  funext i
  simp [siteOfInt]
theorem siteOfInt_blockPoint (hL : L ≠ 0) (kk o : Fin 4 → ℤ) :
    (siteOfInt (blockPoint L kk o) : TorusSite (n * L)) = fineSite L (siteOfInt kk : TorusSite n) 0 o := by
  funext i
  simp only [siteOfInt, fineSite, blockPoint, Pi.zero_apply, add_zero]
  have hc := ZMod.coe_intCast (n := n) (kk i)
  rw [hc, Int.emod_def]
  have e : (L : ℤ) * (kk i - (n : ℤ) * (kk i / (n : ℤ))) + o i =
      ((L : ℤ) * kk i + o i) - ((n * L : ℕ) : ℤ) * (kk i / (n : ℤ)) := by
    push_cast
    ring
  rw [e]
  exact (intCast_sub_mul_of_eq (n * L) (n * L) rfl _ _).symm
theorem parentBlock_fineSite (hodd : Odd L) (Y : TorusSite n) (h o : Fin 4 → ℤ) (ho : o ∈ centredCube L) :
    parentBlock L (fineSite L Y h o) = Y + siteOfInt h := by
  show parentBlock L (siteOfInt (blockPoint L (fun i => ((Y i).cast : ℤ) + h i) o) : TorusSite (n * L)) = _
  rw [parentBlock_blockPoint hodd _ o ho, siteOfInt_cast_add]
theorem exists_fineSite_of_parentBlock (hodd : Odd L) (Y : TorusSite n) (x : TorusSite (n * L))
    (hx : parentBlock L x = Y) : ∃ o ∈ centredCube L, x = fineSite L Y 0 o := by
  obtain ⟨kk, o, ho, hdec⟩ := exists_block_offset hodd (fun i => ((x i).cast : ℤ))
  have hne : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hx' : x = siteOfInt (blockPoint L kk o) := by
    conv_lhs => rw [← siteOfInt_cast_self x]
    congr 1
    funext i
    exact hdec i
  have hb : (siteOfInt kk : TorusSite n) = Y := by
    rw [← hx, hx', parentBlock_blockPoint hodd _ o ho]
  refine ⟨o, ho, ?_⟩
  rw [hx', siteOfInt_blockPoint (NeZero.ne L), hb]
theorem fineSite_injective (Y : TorusSite n) (h : Fin 4 → ℤ) (hodd : Odd L) {o o' : Fin 4 → ℤ}
    (ho : o ∈ centredCube L) (ho' : o' ∈ centredCube L)
    (e : (fineSite L Y h o : TorusSite (n * L)) = fineSite L Y h o') : o = o' := by
  funext i
  have h1 := congrFun e i
  simp only [fineSite, siteOfInt] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have h2 : ((n * L : ℕ) : ℤ) ∣ o' i - o i := by
    have : (L : ℤ) * (((Y i).cast : ℤ) + h i) + o' i - ((L : ℤ) * (((Y i).cast : ℤ) + h i) + o i) =
        o' i - o i := by
      ring
    rwa [this] at h1
  obtain ⟨H, hH⟩ := hodd
  have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
  have hb := (mem_centredCube_iff o).mp ho i
  have hb' := (mem_centredCube_iff o').mp ho' i
  rw [hL] at hb hb'
  have hn : (1 : ℤ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hLH : (L : ℤ) = 2 * H + 1 := by subst hH; push_cast; ring
  have hbig : (L : ℤ) ≤ ((n * L : ℕ) : ℤ) := by
    push_cast
    nlinarith [(show (0 : ℤ) ≤ L by positivity)]
  have h3 : |o' i - o i| < ((n * L : ℕ) : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd h2 h3
  omega
theorem sum_sitesInBlocks {M : Type} [AddCommMonoid M] (hodd : Odd L) (Y : TorusSite n)
    (f : TorusSite (n * L) → M) :
    ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ o ∈ centredCube L, f (fineSite L Y 0 o) := by
  symm
  refine Finset.sum_bij (fun o _ => fineSite L Y 0 o) ?_ ?_ ?_ ?_
  · intro o ho
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [parentBlock_fineSite hodd Y 0 o ho]
    have z : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
      funext i
      simp [siteOfInt]
    rw [z, add_zero]
  · intro o ho o' ho' e
    exact fineSite_injective Y 0 hodd ho ho' e
  · intro x hx
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hx
    obtain ⟨o, ho, e⟩ := exists_fineSite_of_parentBlock hodd Y x hx
    exact ⟨o, ho, e.symm⟩
  · intro o _
    rfl
omit [NeZero L] [NeZero n] in
theorem card_centredCube (hodd : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
omit [NeZero n] in
theorem exists_fineSite_add (hodd : Odd L) {k : ℕ} (hk1 : 1 ≤ k) {o e : Fin 4 → ℤ} (ho : o ∈ centredCube L)
    (he : OffsetInBox (L * k - L) e) :
    ∃ kk o' : Fin 4 → ℤ, o' ∈ centredCube L ∧ (∀ l, |kk l| + 1 ≤ (k : ℤ)) ∧
      ∀ (N : ℕ) (Z : TorusSite N), fineSite L Z 0 o + siteOfInt e = fineSite L Z kk o' := by
  obtain ⟨kk, o', ho', hdec⟩ := exists_block_offset hodd (o + e)
  obtain ⟨H, hH⟩ := id hodd
  have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by rw [hH]; push_cast; omega
  have hLH : (L : ℤ) = 2 * H + 1 := by rw [hH]; push_cast; ring
  have hb1 := (mem_centredCube_iff o).mp ho
  have hb2 := (mem_centredCube_iff o').mp ho'
  rw [hL] at hb1 hb2
  have hcast : ((L * k - L : ℕ) : ℤ) = (L : ℤ) * k - L := by
    have : L ≤ L * k := Nat.le_mul_of_pos_right _ hk1
    push_cast [Nat.cast_sub this]
    ring
  refine ⟨kk, o', ho', ?_, ?_⟩
  · intro l
    have h1 : |e l| ≤ (L : ℤ) * k - L := by rw [← hcast]; exact he l
    have h2 := hdec l
    simp only [Pi.add_apply] at h2
    have h3 := abs_le.mp h1
    have h4 := hb1 l
    have h5 := hb2 l
    have hLpos : (0 : ℤ) < L := by omega
    have hup : (L : ℤ) * kk l < (L : ℤ) * k := by nlinarith
    have hlo : (L : ℤ) * (-kk l) < (L : ℤ) * k := by nlinarith
    have a1 := lt_of_mul_lt_mul_left hup hLpos.le
    have a2 := lt_of_mul_lt_mul_left hlo hLpos.le
    rcases abs_cases (kk l) with ⟨h6, _⟩ | ⟨h6, _⟩ <;> omega
  · intro N Z
    show siteOfInt _ + siteOfInt _ = siteOfInt _
    rw [← siteOfInt_add]
    congr 1
    funext l
    have h2 := hdec l
    simp only [Pi.add_apply, Pi.zero_apply] at h2 ⊢
    linarith
theorem sameBlockPosition_fineSite (ℓ : StepParameters) {n n' : ℕ} [NeZero n] [NeZero n'] (Y : TorusSite n)
    (Y' : TorusSite n') (h o : Fin 4 → ℤ) :
    SameBlockPosition ℓ (fineSite ℓ.side Y h o) (fineSite ℓ.side Y' h o) := by
  intro i
  rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  simp only [fineSite, siteOfInt]
  rw [ZMod.coe_intCast, ZMod.coe_intCast]
  have d1 : (ℓ.side : ℤ) ∣ ((n * ℓ.side : ℕ) : ℤ) := by push_cast; exact Dvd.intro_left _ rfl
  have d2 : (ℓ.side : ℤ) ∣ ((n' * ℓ.side : ℕ) : ℤ) := by push_cast; exact Dvd.intro_left _ rfl
  rw [Int.emod_emod_of_dvd _ d1, Int.emod_emod_of_dvd _ d2, add_comm, Int.add_mul_emod_self_left, add_comm,
    Int.add_mul_emod_self_left]
end
section
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
theorem fieldsAgreeNear_of_settings {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free} {o : Fin 4 → ℤ}
    (hodd : Odd R.params.side) (hn : 2 ≤ n) (hn' : 2 ≤ n') (hf : s.free ⊆ chartBonds R.params.side n)
    (hag : SettingsAgreeNear s s' Y Y' m) (hk1 : 1 ≤ k) (hk : k ≤ m) (hnear : CoordsAgreeNear s s' Y Y' k η η')
    (ho : o ∈ centredCube R.params.side) :
    FieldsAgreeNear (s.field η) (s'.field η') (fineSite R.params.side Y 0 o) (fineSite R.params.side Y' 0 o)
      (R.params.side * k - R.params.side) := by
  intro b hb
  obtain ⟨e, i⟩ := b
  obtain ⟨kk, o', ho', hkk, hx⟩ := exists_fineSite_add hodd hk1 ho hb.1
  show s.field η (fineSite R.params.side Y 0 o + siteOfInt e) i =
    s'.field η' (fineSite R.params.side Y' 0 o + siteOfInt e) i
  rw [hx, hx]
  exact field_fineSite_eq hodd hn hn' hf hag hk hnear kk o' i ho' hkk
end
end YangMills.Construction.BlockOffsets
end
