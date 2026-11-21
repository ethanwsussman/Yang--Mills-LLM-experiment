import YangMills.Construction.ColdChainAtEveryLevel.SharesAcrossABond
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTopProof
import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.LinesOfAgreeingPairs
import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import YangMills.Construction.ColdChainAtEveryLevel.TopVectorsOfASite
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open GaugeMap LatticeFractionalIntegration
namespace BlockAverages
namespace AgreeingPairs
open LocalPartition
section Box
variable {F F' : BlockFrame} {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
theorem valMinAbs_intCast_of_withinRadius (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i) (i : Fin 4)
    {A : ℤ} (hA : |A| ≤ (r : ℤ) + 1) : ((A : ZMod (F.period F.top i))).valMinAbs = A := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.valMinAbs_of_withinRadius <;> assumption
theorem siteOfCoords_injOn_withinRadius (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i) {a b : Lattice4}
    (ha : WithinRadius r a) (hb : WithinRadius r b)
    (h : siteOfCoords (F := F) F.top a = siteOfCoords F.top b) : a = b := by
  funext i
  have h1 := congrArg ZMod.valMinAbs (congrFun h i)
  simp only [siteOfCoords] at h1
  rwa [valMinAbs_intCast_of_withinRadius hs i (by linarith [ha i]),
    valMinAbs_intCast_of_withinRadius hs i (by linarith [hb i])] at h1
theorem isOrthantClosedNear_of_agree (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    (hs' : ∀ i, F'.extent i = 0 ∨ 2 * r + 2 < F'.extent i)
    (hS : ∀ h, WithinRadius r h → (Y + siteOfCoords F.top h ∈ S ↔ Y' + siteOfCoords F'.top h ∈ S'))
    {d e : Lattice4} (hd : ∀ i, |d i| + 64 ≤ (r : ℤ))
    (hc : IsOrthantClosedNear S (Y + siteOfCoords F.top d) e) :
    IsOrthantClosedNear S' (Y' + siteOfCoords F'.top d) e := by
  intro q hq hdist h hh hb
  set u : Lattice4 := fun i => ((q - (Y' + siteOfCoords F'.top d) : F'.Cell) i).valMinAbs with hu
  have hu32 : ∀ i, |u i| ≤ 32 := by
    intro i
    have h1 : ((q i - (Y' + siteOfCoords F'.top d : F'.Cell) i).valMinAbs).natAbs ≤
        cellSupDist q (Y' + siteOfCoords F'.top d) :=
      Finset.le_sup (f := fun i => ((q i - (Y' + siteOfCoords F'.top d : F'.Cell) i).valMinAbs).natAbs)
        (Finset.mem_univ i)
    have h2 := h1.trans hdist
    simp only [hu, Pi.sub_apply]
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h2
  have hq' : q = Y' + siteOfCoords F'.top (d + u) := by
    funext i
    simp only [siteOfCoords_add, Pi.add_apply]
    have : (siteOfCoords (F := F') F'.top u) i = (q - (Y' + siteOfCoords F'.top d) : F'.Cell) i := by
      simp only [siteOfCoords, hu]
      exact ZMod.coe_valMinAbs _
    rw [this]
    simp only [Pi.sub_apply, Pi.add_apply]
    abel
  have hbox : ∀ (a : Lattice4), (∀ i, |a i| ≤ 32) → WithinRadius r (d + a) := by
    intro a ha i
    have := abs_add_le (d i) (a i)
    simp only [Pi.add_apply]
    linarith [hd i, ha i]
  have hm : Y + siteOfCoords F.top (d + u) ∈ S := (hS _ (hbox u hu32)).2 (hq' ▸ hq)
  have hr64 : (64 : ℤ) ≤ r := by linarith [hd 0, abs_nonneg (d 0)]
  have hdist' : cellSupDist (Y + siteOfCoords F.top (d + u)) (Y + siteOfCoords F.top d) ≤ 32 := by
    refine Finset.sup_le fun i _ => ?_
    have e1 : (Y + siteOfCoords F.top (d + u) : F.Cell) i - (Y + siteOfCoords F.top d : F.Cell) i =
        ((u i : ℤ) : ZMod (F.period F.top i)) := by
      simp [siteOfCoords]
    rw [e1, valMinAbs_intCast_of_withinRadius hs i (by linarith [hu32 i])]
    have := hu32 i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have h1 := hc _ hm hdist' h hh hb
  rw [add_assoc, ← siteOfCoords_add] at h1
  have hb2 : WithinRadius r (d + u + h) := by
    intro i
    have a1 := abs_add_le (d i + u i) (h i)
    have a2 := abs_add_le (d i) (u i)
    simp only [Pi.add_apply]
    linarith [hd i, hu32 i, hb i]
  have h2 := (hS _ hb2).1 h1
  rw [hq', add_assoc, ← siteOfCoords_add]
  exact h2
theorem closedOrthant_eq_of_agree (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    (hs' : ∀ i, F'.extent i = 0 ∨ 2 * r + 2 < F'.extent i)
    (hS : ∀ h, WithinRadius r h → (Y + siteOfCoords F.top h ∈ S ↔ Y' + siteOfCoords F'.top h ∈ S'))
    {d : Lattice4} (hd : ∀ i, |d i| + 64 ≤ (r : ℤ)) :
    closedOrthant S (Y + siteOfCoords F.top d) = closedOrthant S' (Y' + siteOfCoords F'.top d) := by
  classical
  have : (fun e => decide (IsOrthantClosedNear S (Y + siteOfCoords F.top d) e)) =
      fun e => decide (IsOrthantClosedNear S' (Y' + siteOfCoords F'.top d) e) := by
    funext e
    exact decide_eq_decide.2 ⟨isOrthantClosedNear_of_agree hs hs' hS hd,
      isOrthantClosedNear_of_agree hs' hs (fun h hh => (hS h hh).symm) hd⟩
  unfold closedOrthant
  rw [this]
def stepOffset (st : PathStep) : Lattice4 := if st.2 then basisVector st.1 else - basisVector st.1
theorem stepDisplacement_eq (st : PathStep) :
    stepDisplacement (F := F) F.top st = siteOfCoords F.top (stepOffset st) := by
  obtain ⟨i, b⟩ := st
  cases b
  · simp [stepDisplacement, stepOffset, unitStep_eq, siteOfCoords_neg]
  · simp [stepDisplacement, stepOffset, unitStep_eq]
theorem abs_basisVector_le (i k : Fin 4) : |basisVector i k| ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.abs_basisVector_le <;> assumption
theorem abs_stepOffset_le (st : PathStep) (k : Fin 4) : |stepOffset st k| ≤ 1 := by apply _root_.YangMills.Construction.BondShares.abs_stepOffset_le <;> assumption
theorem pathHolonomy_eq_of_agree
    (hV : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (l : List PathStep) (p : Lattice4) (hp : ∀ i, |p i| + l.length + 1 ≤ (r : ℤ)) :
    pathHolonomy V (Y + siteOfCoords F.top p) l = pathHolonomy V' (Y' + siteOfCoords F'.top p) l := by
  induction l generalizing p with
  | nil => rfl
  | cons st t ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hp
    have hnext : ∀ i, |(p + stepOffset st) i| + t.length + 1 ≤ (r : ℤ) := by
      intro i
      have a1 := abs_add_le (p i) (stepOffset st i)
      have a2 := abs_stepOffset_le st i
      simp only [Pi.add_apply]
      linarith [hp i]
    have hstep : linkValue V (Y + siteOfCoords F.top p) st = linkValue V' (Y' + siteOfCoords F'.top p) st := by
      obtain ⟨i, b⟩ := st
      have hin : ∀ k, |p k| + 1 ≤ (r : ℤ) := fun k => by
        have : (0 : ℤ) ≤ (t.length : ℤ) := by positivity
        linarith [hp k]
      cases b
      · have hb : BondWithinRadius r (p - basisVector i, i) := by
          constructor
          · intro k
            have a1 := abs_sub (p k) (basisVector i k)
            have a2 := abs_basisVector_le i k
            simp only [Pi.sub_apply]
            linarith [hin k]
          · intro k
            have : (p - basisVector i + Pi.single i 1) = p := by
              simp [basisVector]
            rw [this]
            linarith [hin k]
        have := hV _ hb
        simp only [linkValue, Bool.false_eq_true, if_false, unitStep_eq]
        simp only [siteOfCoords_sub] at this
        rw [add_sub_assoc, add_sub_assoc]
        rw [← add_sub_assoc, ← add_sub_assoc] at this
        rw [← add_sub_assoc, ← add_sub_assoc, this]
      · have hb : BondWithinRadius r (p, i) := by
          constructor
          · intro k
            linarith [hin k]
          · intro k
            have a1 := abs_add_le (p k) ((Pi.single i 1 : Lattice4) k)
            have a2 := abs_basisVector_le i k
            simp only [basisVector] at a2
            simp only [Pi.add_apply] at a1 ⊢
            linarith [hin k]
        simpa [linkValue] using hV _ hb
    have e1 : Y + siteOfCoords F.top p + siteOfCoords F.top (stepOffset st) =
        Y + siteOfCoords F.top (p + stepOffset st) := by
      rw [siteOfCoords_add, add_assoc]
    have e2 : Y' + siteOfCoords F'.top p + siteOfCoords F'.top (stepOffset st) =
        Y' + siteOfCoords F'.top (p + stepOffset st) := by
      rw [siteOfCoords_add, add_assoc]
    simp only [pathHolonomy]
    rw [hstep, stepDisplacement_eq, stepDisplacement_eq, e1, e2, ih _ hnext]
theorem axisPath_length_le (h : Lattice4) (B : ℕ) (hB : ∀ i, |h i| ≤ (B : ℤ)) :
    (axisPath h 1).length ≤ 4 * B := by
  have e : List.finRange 4 = [0, 1, 2, 3] := rfl
  have hn : ∀ i, (h i).natAbs ≤ B := fun i => by
    have := hB i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  unfold axisPath
  rw [e]
  simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_replicate, Equiv.Perm.coe_one,
    id_eq, List.length_nil, List.append_nil]
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  omega
theorem cellDisplacement_eq_of_withinRadius (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    {d d' : Lattice4} (h : ∀ i, |d' i - d i| ≤ (r : ℤ) + 1) :
    cellDisplacement (Y + siteOfCoords F.top d) (Y + siteOfCoords F.top d') = d' - d := by
  funext i
  have e1 : ((Y + siteOfCoords F.top d') - (Y + siteOfCoords F.top d) : F.Cell) i =
      ((d' i - d i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  simp only [cellDisplacement, e1, Pi.sub_apply]
  exact valMinAbs_intCast_of_withinRadius hs i (h i)
theorem cellParallelTransport_eq_of_agree (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    (hs' : ∀ i, F'.extent i = 0 ∨ 2 * r + 2 < F'.extent i)
    (hS : ∀ h, WithinRadius r h → (Y + siteOfCoords F.top h ∈ S ↔ Y' + siteOfCoords F'.top h ∈ S'))
    (hV : ∀ b, BondWithinRadius r b → V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    {d d' : Lattice4} (hd : ∀ i, |d i| + 90 ≤ (r : ℤ)) (hdd : ∀ i, |d' i - d i| ≤ 3) :
    cellParallelTransport S V (Y + siteOfCoords F.top d) (Y + siteOfCoords F.top d') =
      cellParallelTransport S' V' (Y' + siteOfCoords F'.top d) (Y' + siteOfCoords F'.top d') := by
  have hr1 : ∀ i, |d' i - d i| ≤ (r : ℤ) + 1 := fun i => by linarith [hdd i, hd i, abs_nonneg (d i)]
  unfold cellParallelTransport
  rw [closedOrthant_eq_of_agree hs hs' hS (fun i => by linarith [hd i]),
    cellDisplacement_eq_of_withinRadius hs hr1, cellDisplacement_eq_of_withinRadius hs' hr1]
  set e := closedOrthant S' (Y' + siteOfCoords F'.top d)
  set o : Lattice4 := d' - d with ho
  have ho3 : ∀ i, |o i| ≤ 3 := hdd
  have h1 : ∀ i, |orthantPart e o i| ≤ ((3 : ℕ) : ℤ) := by
    intro i
    simp only [orthantPart]
    split_ifs
    · exact_mod_cast ho3 i
    · simp
  have h2 : ∀ i, |(o - orthantPart e o) i| ≤ ((3 : ℕ) : ℤ) := by
    intro i
    simp only [orthantPart, Pi.sub_apply]
    split_ifs
    · simp
    · simpa using ho3 i
  have l1 := axisPath_length_le _ 3 h1
  have l2 := axisPath_length_le _ 3 h2
  apply pathHolonomy_eq_of_agree hV
  intro i
  rw [List.length_append]
  have : ((((axisPath (orthantPart e o) 1).length + (axisPath (o - orthantPart e o) 1).length : ℕ)) : ℤ) ≤ 24 := by
    exact_mod_cast (by omega : (axisPath (orthantPart e o) 1).length + (axisPath (o - orthantPart e o) 1).length ≤ 24)
  linarith [hd i]
end Box
section Local
variable {F F' : BlockFrame} {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
theorem cellSideLength_eq (hL : F'.blockSide = F.blockSide) (ht : F'.depth = F.depth) :
    cellSideLength F' = cellSideLength F := by
  simp only [cellSideLength, BlockFrame.top, hL, ht]
theorem localCutoff_eq (hL : F'.blockSide = F.blockSide) (ht : F'.depth = F.depth) (v x : Lattice4) :
    localCutoff F' v x = localCutoff F v x := by
  simp only [localCutoff, cellSideLength, BlockFrame.top, hL, ht]
theorem localCell_add_siteOfCoords (S : Finset F.Cell) (d v : Lattice4) :
    localCell S (Y + siteOfCoords F.top d) v =
      Y + siteOfCoords F.top (d + fun i => closedOrthant S (Y + siteOfCoords F.top d) i * v i) := by
  unfold localCell
  rw [siteOfCoords_add, add_assoc]
def transported (S : Finset F.Cell) (S' : Finset F'.Cell) (z : F.Cell) (z' : F'.Cell) (f : F.Cell → ℍ[ℝ]) :
    F'.Cell → ℍ[ℝ] := by
  classical exact fun y' => ∑ v ∈ localCellIndex S z, if localCell S' z' v = y' then f (localCell S z v) else 0
theorem abs_le_of_mem_centredCube {N : ℕ} {o : Lattice4} (ho : o ∈ centredCube N) (i : Fin 4) :
    |o i| ≤ ((N : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.withinBlock_of_mem_centredCube <;> assumption
theorem patchSite_eq_cellCentre_add {z : F.Cell}
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {a o : Lattice4}
    (ha : ∀ i, a i = closedOrthant S z i * o i + (cellSideLength F - 1) / 2) :
    patchSite S z a = cellCentre 0 z + siteOfCoords 0 o := by
  unfold patchSite
  congr 2
  funext i
  rw [ha i, add_sub_cancel_right, ← mul_assoc, closedOrthant_mul_self he i, one_mul]
theorem patchOffset_range (hodd : Odd F.blockSide) {z : F.Cell}
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {a o : Lattice4}
    (ho : ∀ i, |o i| ≤ (cellSideLength F - 1) / 2)
    (ha : ∀ i, a i = closedOrthant S z i * o i + (cellSideLength F - 1) / 2) :
    ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F := by
  intro i
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  have h1 := abs_le.1 (ho i)
  rw [ha i]
  rcases he i with h | h <;> rw [h] <;> constructor <;> omega
theorem localCell_zero (S : Finset F.Cell) (z : F.Cell) : localCell S z 0 = z := by
  have e : (fun i => closedOrthant S z i * (0 : Lattice4) i) = 0 := by
    funext i
    simp
  unfold localCell
  rw [e, siteOfCoords_zero, add_zero]
theorem zero_mem_localCellIndex {z : F.Cell} (hz : z ∈ S) : (0 : Lattice4) ∈ localCellIndex S z :=
  mem_localCellIndex.2 ⟨fun i => by simp, by rw [localCell_zero]; exact hz⟩
theorem localCutoff_zero_eq_one (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {z : F.Cell} (hz : z ∈ S)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {a o : Lattice4}
    (ho : o ∈ centredCube (F.blockSide ^ F.top))
    (ha : ∀ i, a i = closedOrthant S z i * o i + (cellSideLength F - 1) / 2)
    (hr : ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F) : localCutoff F 0 a = 1 := by
  have h1 := cellCutoff_patchSite_eq hamb hodd he hr (zero_mem_localCellIndex hz)
  rw [localCell_zero, patchSite_eq_cellCentre_add he ha, cellCutoff_self hamb hodd z ho] at h1
  exact h1.symm
end Local
section Carry
variable {F F' : BlockFrame} {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
structure AgreeOnBox (S : Finset F.Cell) (S' : Finset F'.Cell) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop where
  blockSide_eq : F'.blockSide = F.blockSide
  depth_eq : F'.depth = F.depth
  odd : Odd F.blockSide
  admissible : IsAdmissibleAmbient F
  admissible' : IsAdmissibleAmbient F'
  extent_large : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i
  extent_large' : ∀ i, F'.extent i = 0 ∨ 2 * r + 2 < F'.extent i
  cells_iff : ∀ h, WithinRadius r h → (Y + siteOfCoords F.top h ∈ S ↔ Y' + siteOfCoords F'.top h ∈ S')
  links_eq : ∀ b, BondWithinRadius r b →
    V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2
theorem AgreeOnBox.odd' (P : AgreeOnBox S S' V V' Y Y' r) : Odd F'.blockSide := P.blockSide_eq ▸ P.odd
theorem abs_sign_mul {e v : ℤ} (he : e = 1 ∨ e = -1) : |e * v| = |v| := by
  rcases he with h | h <;> rw [h] <;> simp
variable (P : AgreeOnBox S S' V V' Y Y' r) {d : Lattice4} (hd : ∀ i, |d i| + 100 ≤ (r : ℤ))
  (he : ∀ i, closedOrthant S (Y + siteOfCoords F.top d) i = 1 ∨ closedOrthant S (Y + siteOfCoords F.top d) i = -1)
  (he' : ∀ i, closedOrthant S' (Y' + siteOfCoords F'.top d) i = 1 ∨
    closedOrthant S' (Y' + siteOfCoords F'.top d) i = -1)
include P hd in
theorem closedOrthant_eq : closedOrthant S' (Y' + siteOfCoords F'.top d) = closedOrthant S (Y + siteOfCoords F.top d) :=
  (closedOrthant_eq_of_agree P.extent_large P.extent_large' P.cells_iff (fun i => by linarith [hd i])).symm
include P hd in
theorem localCell_eq (v : Lattice4) : localCell S' (Y' + siteOfCoords F'.top d) v =
    Y' + siteOfCoords F'.top (d + fun i => closedOrthant S (Y + siteOfCoords F.top d) i * v i) := by
  rw [localCell_add_siteOfCoords, closedOrthant_eq P hd]
include P hd he in
theorem localCellIndex_eq :
    localCellIndex S' (Y' + siteOfCoords F'.top d) = localCellIndex S (Y + siteOfCoords F.top d) := by
  ext v
  rw [mem_localCellIndex, mem_localCellIndex]
  refine and_congr_right fun hv => ?_
  rw [localCell_eq P hd, localCell_add_siteOfCoords]
  refine (P.cells_iff _ fun i => ?_).symm
  have a1 := abs_add_le (d i) (closedOrthant S (Y + siteOfCoords F.top d) i * v i)
  rw [abs_sign_mul (he i)] at a1
  have a2 := abs_le.2 (by constructor <;> linarith [(hv i).1, (hv i).2] : -21 ≤ v i ∧ v i ≤ 21)
  simp only [Pi.add_apply]
  linarith [hd i]
include P hd he in
theorem weight_eq (v x : Lattice4) :
    weight S' (Y' + siteOfCoords F'.top d) v x = weight S (Y + siteOfCoords F.top d) v x := by
  unfold weight sumSqCutoff
  rw [localCellIndex_eq P hd he]
  simp only [localCutoff_eq P.blockSide_eq P.depth_eq]
include P hd he he' in
theorem transported_localCell {f : F.Cell → ℍ[ℝ]} {v : Lattice4}
    (hv : v ∈ localCellIndex S (Y + siteOfCoords F.top d)) :
    transported S S' (Y + siteOfCoords F.top d) (Y' + siteOfCoords F'.top d) f
      (localCell S' (Y' + siteOfCoords F'.top d) v) = f (localCell S (Y + siteOfCoords F.top d) v) := by
  classical
  unfold transported
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hb hbv
    have : localCell S' (Y' + siteOfCoords F'.top d) b ≠ localCell S' (Y' + siteOfCoords F'.top d) v := fun h =>
      hbv (localCell_injective P.admissible' he' (mem_localCellIndex.1 hb).1 (mem_localCellIndex.1 hv).1 h)
    simp [this]
  · intro h
    exact absurd hv h
theorem transported_eq_zero {z : F.Cell} {z' : F'.Cell} {f : F.Cell → ℍ[ℝ]} {y' : F'.Cell}
    (h : ∀ v ∈ localCellIndex S z, localCell S' z' v ≠ y') : transported S S' z z' f y' = 0 := by
  classical
  unfold transported
  exact Finset.sum_eq_zero fun v hv => by simp [h v hv]
include P hd he he' in
theorem isLeadingEigenvector_transported {a : Lattice4}
    (hr : ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F)
    (hb0 : localCutoff F 0 a ≠ 0) {f : F.Cell → ℍ[ℝ]}
    (hf : IsLeadingEigenvector S V (patchSite S (Y + siteOfCoords F.top d) a) f) :
    IsLeadingEigenvector S' V' (patchSite S' (Y' + siteOfCoords F'.top d) a)
      (transported S S' (Y + siteOfCoords F.top d) (Y' + siteOfCoords F'.top d) f) := by
  classical
  have hodd' := P.odd'
  have hr' : ∀ i, -(10 * cellSideLength F') ≤ a i ∧ a i < 21 * cellSideLength F' := by
    rw [cellSideLength_eq P.blockSide_eq P.depth_eq]
    exact hr
  have hidx := localCellIndex_eq P hd he
  obtain ⟨hn, l, hl, hop⟩ := hf
  have l0 : l ≠ 0 := by
    intro h0
    rw [h0] at hl
    norm_num at hl
  have hzero : ∀ y ∈ S, cellCutoff (patchSite S (Y + siteOfCoords F.top d) a) y = 0 → f y = 0 := by
    intro y hy hb
    have h1 := hop y hy
    rw [localizationOperator_eq_zero_of_cellCutoff_eq_zero hb] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left l0
  have hbump : ∀ v ∈ localCellIndex S (Y + siteOfCoords F.top d),
      cellCutoff (patchSite S' (Y' + siteOfCoords F'.top d) a) (localCell S' (Y' + siteOfCoords F'.top d) v) =
        cellCutoff (patchSite S (Y + siteOfCoords F.top d) a) (localCell S (Y + siteOfCoords F.top d) v) := by
    intro v hv
    rw [cellCutoff_patchSite_eq P.admissible P.odd he hr hv,
      cellCutoff_patchSite_eq P.admissible' hodd' he' hr' (hidx ▸ hv), localCutoff_eq P.blockSide_eq P.depth_eq]
  have hcz : ∀ y', cellCutoff (patchSite S' (Y' + siteOfCoords F'.top d) a) y' = 0 →
      transported S S' (Y + siteOfCoords F.top d) (Y' + siteOfCoords F'.top d) f y' = 0 := by
    intro y' hb
    unfold transported
    refine Finset.sum_eq_zero fun v hv => ?_
    split_ifs with h
    · have : cellCutoff (patchSite S (Y + siteOfCoords F.top d) a) (localCell S (Y + siteOfCoords F.top d) v) = 0 := by
        rw [← hbump v hv, h]
        exact hb
      exact hzero _ (mem_localCellIndex.1 hv).2 this
    · rfl
  refine ⟨?_, l, hl, fun y' hy' => ?_⟩
  · rw [sum_eq_sum_localCellIndex P.admissible' hodd' he' hr'
      (fun y => ‖transported S S' (Y + siteOfCoords F.top d) (Y' + siteOfCoords F'.top d) f y‖ ^ 2)
      (fun y _ h0 => by simp [hcz y h0]), hidx, ← hn,
      sum_eq_sum_localCellIndex P.admissible P.odd he hr (fun y => ‖f y‖ ^ 2)
        (fun y hy h0 => by simp [hzero y hy h0])]
    exact Finset.sum_congr rfl fun v hv => by rw [transported_localCell P hd he he' hv]
  · by_cases hb : cellCutoff (patchSite S' (Y' + siteOfCoords F'.top d) a) y' = 0
    · rw [localizationOperator_eq_zero_of_cellCutoff_eq_zero hb, hcz y' hb, smul_zero]
    · obtain ⟨v, hvb, rfl⟩ := exists_localCell_of_cellCutoff_ne_zero P.admissible' hodd' he' hr' hb
      have hv' : v ∈ localCellIndex S' (Y' + siteOfCoords F'.top d) := mem_localCellIndex.2 ⟨hvb, hy'⟩
      have hv : v ∈ localCellIndex S (Y + siteOfCoords F.top d) := hidx ▸ hv'
      rw [transported_localCell P hd he he' hv, ← hop _ (mem_localCellIndex.1 hv).2,
        localizationOperator_patchSite_eq P.admissible' hodd' he' hr' hv',
        localizationOperator_patchSite_eq P.admissible P.odd he hr hv, hidx]
      refine Finset.sum_congr rfl fun v1 hv1 => Finset.sum_congr rfl fun v2 hv2 => ?_
      rw [weight_eq P hd he, weight_eq P hd he, weight_eq P hd he, transported_localCell P hd he he' hv2]
      by_cases hc : weight S (Y + siteOfCoords F.top d) v1 a * Real.sqrt (weight S (Y + siteOfCoords F.top d) v a) *
          Real.sqrt (weight S (Y + siteOfCoords F.top d) v2 a) = 0
      · rw [hc, zero_smul, zero_smul]
      · have h1 : weight S (Y + siteOfCoords F.top d) v1 a ≠ 0 := fun h0 => hc (by rw [h0]; simp)
        have h2 : weight S (Y + siteOfCoords F.top d) v a ≠ 0 := fun h0 => hc (by rw [h0]; simp)
        have h3 : weight S (Y + siteOfCoords F.top d) v2 a ≠ 0 := fun h0 => hc (by rw [h0]; simp)
        have b1 := localCutoff_ne_zero_of_weight_ne_zero h1
        have b2 := localCutoff_ne_zero_of_weight_ne_zero h2
        have b3 := localCutoff_ne_zero_of_weight_ne_zero h3
        have n1 := abs_sub_lt_two_of_localCutoff_ne_zero P.odd.pos hb0 b1
        have n2 := abs_sub_lt_two_of_localCutoff_ne_zero P.odd.pos hb0 b2
        have n3 := abs_sub_lt_two_of_localCutoff_ne_zero P.odd.pos hb0 b3
        have small : ∀ w : Lattice4, (∀ i, |w i - (0 : Lattice4) i| < 2) → ∀ i,
            |(d + fun i => closedOrthant S (Y + siteOfCoords F.top d) i * w i) i| + 90 ≤ (r : ℤ) := by
          intro w hw i
          have a1 := abs_add_le (d i) (closedOrthant S (Y + siteOfCoords F.top d) i * w i)
          rw [abs_sign_mul (he i)] at a1
          have a2 := hw i
          simp only [Pi.zero_apply, sub_zero] at a2
          simp only [Pi.add_apply]
          linarith [hd i]
        have close : ∀ w w' : Lattice4, (∀ i, |w i - (0 : Lattice4) i| < 2) →
            (∀ i, |w' i - (0 : Lattice4) i| < 2) → ∀ i,
            |(d + fun i => closedOrthant S (Y + siteOfCoords F.top d) i * w' i) i -
              (d + fun i => closedOrthant S (Y + siteOfCoords F.top d) i * w i) i| ≤ 3 := by
          intro w w' hw hw' i
          have e : (d + fun i => closedOrthant S (Y + siteOfCoords F.top d) i * w' i) i -
              (d + fun i => closedOrthant S (Y + siteOfCoords F.top d) i * w i) i =
              closedOrthant S (Y + siteOfCoords F.top d) i * (w' i - w i) := by
            simp only [Pi.add_apply]
            ring
          rw [e, abs_sign_mul (he i)]
          have a2 := hw i
          have a3 := hw' i
          simp only [Pi.zero_apply, sub_zero] at a2 a3
          have := abs_sub (w' i) (w i)
          linarith
        have t1 : cellParallelTransport S' V' (localCell S' (Y' + siteOfCoords F'.top d) v)
              (localCell S' (Y' + siteOfCoords F'.top d) v1) =
            cellParallelTransport S V (localCell S (Y + siteOfCoords F.top d) v)
              (localCell S (Y + siteOfCoords F.top d) v1) := by
          rw [localCell_eq P hd, localCell_eq P hd, localCell_add_siteOfCoords, localCell_add_siteOfCoords]
          exact (cellParallelTransport_eq_of_agree P.extent_large P.extent_large' P.cells_iff P.links_eq
            (small v n2) (close v v1 n2 n1)).symm
        have t2 : cellParallelTransport S' V' (localCell S' (Y' + siteOfCoords F'.top d) v2)
              (localCell S' (Y' + siteOfCoords F'.top d) v1) =
            cellParallelTransport S V (localCell S (Y + siteOfCoords F.top d) v2)
              (localCell S (Y + siteOfCoords F.top d) v1) := by
          rw [localCell_eq P hd, localCell_eq P hd, localCell_add_siteOfCoords, localCell_add_siteOfCoords]
          exact (cellParallelTransport_eq_of_agree P.extent_large P.extent_large' P.cells_iff P.links_eq
            (small v2 n3) (close v2 v1 n3 n1)).symm
        rw [t1, t2]
end Carry
section Lines
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top}
theorem leadingFrame_cellCentre (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) {y : F.Cell} (hy : y ∈ S)
    {s : F.Site 0} (hs : s = cellCentre 0 y) :
    leadingFrame S V s y = 1 ∧ ∀ y', y' ≠ y → leadingFrame S V s y' = 0 := by apply _root_.YangMills.Construction.BlockAverages.leadingFrame_at_cellCentre <;> assumption
theorem zero_mem_centredCube (M : ℕ) (hM : 0 < M) : (0 : Fin 4 → ℤ) ∈ centredCube M := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.zero_mem_centredCube <;> assumption
theorem not_exists_cellCentre_eq (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {z : F.Cell}
    {o : Lattice4} (ho : o ∈ centredCube (F.blockSide ^ (F.top - 0))) (ho0 : o ≠ 0) :
    ¬ ∃ y ∈ S, cellCentre 0 z + siteOfCoords 0 o = cellCentre 0 y := by
  rintro ⟨y, -, e⟩
  have hL := hodd.pos
  have c1 := enclosingCell_cellCentre_add hodd (j := 0) z o ho
  have c2 := enclosingCell_cellCentre_add hodd (j := 0) y 0 (zero_mem_centredCube _ (Nat.pow_pos hL))
  rw [siteOfCoords_zero, add_zero] at c2
  rw [e, c2] at c1
  subst c1
  have h0 : siteOfCoords (F := F) 0 o = 0 := by
    have := add_left_cancel (a := cellCentre 0 y) (b := siteOfCoords 0 o) (c := 0) (by rw [add_zero]; exact e)
    exact this
  apply ho0
  funext i
  have h1 := congrFun h0 i
  simp only [siteOfCoords, Pi.zero_apply] at h1
  have hc := cellSideLength_half (F := F) hodd
  have hb : |o i| < 32 * cellSideLength F := by
    have := abs_le_of_mem_centredCube ho i
    have e2 : (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ)) = cellSideLength F := by simp [cellSideLength]
    rw [e2] at this
    omega
  have h2 := valMinAbs_of_abs_lt hamb hL i hb
  rw [h1, ZMod.valMinAbs_zero] at h2
  exact h2.symm
theorem leadingFrame_eq_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {x : F.Site 0} {y : F.Cell}
    (hy : y ∈ S) (hb : cellCutoff x y = 0) : leadingFrame S V x y = 0 := by
  classical
  unfold leadingFrame
  by_cases hc : ∃ y ∈ S, x = cellCentre 0 y
  · rw [dif_pos hc]
    have h1 : y ≠ hc.choose := by
      intro h
      have hx := hc.choose_spec.2
      rw [← h] at hx
      have h2 := cellCutoff_self hamb hodd y (zero_mem_centredCube _ (Nat.pow_pos hodd.pos))
      rw [siteOfCoords_zero, add_zero, ← hx, hb] at h2
      norm_num at h2
    simp [h1]
  · rw [dif_neg hc]
    by_cases hex : ∃ f, IsLeadingEigenvector S V x f
    · rw [dif_pos hex]
      obtain ⟨-, l, hl, hop⟩ := hex.choose_spec
      have h1 := hop y hy
      rw [localizationOperator_eq_zero_of_cellCutoff_eq_zero hb] at h1
      have l0 : l ≠ 0 := by
        intro h0
        rw [h0] at hl
        norm_num at hl
      have := (smul_eq_zero.1 h1.symm).resolve_left l0
      simp only [this, zero_mul]
    · rw [dif_neg hex]
      rfl
theorem polarUnit_coe (g : UnitQuaternion) : polarUnit (g : ℍ[ℝ]) = g := by apply _root_.YangMills.Construction.BlockLines.polarUnit_coe <;> assumption
end Lines
section Final
variable {F F' : BlockFrame} {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top}
  {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
def HasLeadingLine (S : Finset F.Cell) (V : F.GaugeField F.top) (x : F.Site 0) : Prop :=
  (∃ f, IsLeadingEigenvector S V x f) ∧ ∀ f g, IsLeadingEigenvector S V x f → IsLeadingEigenvector S V x g →
    f (enclosingCell x) ≠ 0 ∧ ∃ q : UnitQuaternion, ∀ y ∈ S, g y = f y * (q : ℍ[ℝ])
theorem leadingFrame_eq_of_agree (P : AgreeOnBox S S' V V' Y Y' r) {d o h' : Lattice4}
    (hd : ∀ i, |d i| + 100 ≤ (r : ℤ))
    (he : ∀ i, closedOrthant S (Y + siteOfCoords F.top d) i = 1 ∨ closedOrthant S (Y + siteOfCoords F.top d) i = -1)
    (he' : ∀ i, closedOrthant S' (Y' + siteOfCoords F'.top d) i = 1 ∨
      closedOrthant S' (Y' + siteOfCoords F'.top d) i = -1)
    (hz : Y + siteOfCoords F.top d ∈ S) (ho : o ∈ centredCube (F.blockSide ^ (F.top - 0)))
    (hT : HasLeadingLine S V (cellCentre 0 (Y + siteOfCoords F.top d) + siteOfCoords 0 o))
    (hT' : HasLeadingLine S' V' (cellCentre 0 (Y' + siteOfCoords F'.top d) + siteOfCoords 0 o))
    (hh : WithinRadius r h') (hy : Y + siteOfCoords F.top h' ∈ S) :
    leadingFrame S V (cellCentre 0 (Y + siteOfCoords F.top d) + siteOfCoords 0 o) (Y + siteOfCoords F.top h') =
      leadingFrame S' V' (cellCentre 0 (Y' + siteOfCoords F'.top d) + siteOfCoords 0 o)
        (Y' + siteOfCoords F'.top h') := by
  classical
  have hodd' := P.odd'
  have hd0 : WithinRadius r d := fun i => by linarith [hd i]
  have hz' : Y' + siteOfCoords F'.top d ∈ S' := (P.cells_iff d hd0).1 hz
  have hy' := (P.cells_iff h' hh).1 hy
  have ho' : o ∈ centredCube (F'.blockSide ^ (F'.top - 0)) := by
    simpa only [BlockFrame.top, P.blockSide_eq, P.depth_eq] using ho
  by_cases ho0 : o = 0
  · subst ho0
    rw [siteOfCoords_zero, add_zero, siteOfCoords_zero, add_zero]
    obtain ⟨a1, a0⟩ := leadingFrame_cellCentre (V := V) P.admissible P.odd.pos hz rfl
    obtain ⟨b1, b0⟩ := leadingFrame_cellCentre (V := V') P.admissible' hodd'.pos hz' rfl
    by_cases hhd : h' = d
    · subst hhd
      rw [a1, b1]
    · have n1 : Y + siteOfCoords F.top h' ≠ Y + siteOfCoords F.top d := fun e =>
        hhd (siteOfCoords_injOn_withinRadius P.extent_large hh hd0 (add_left_cancel e))
      have n2 : Y' + siteOfCoords F'.top h' ≠ Y' + siteOfCoords F'.top d := fun e =>
        hhd (siteOfCoords_injOn_withinRadius P.extent_large' hh hd0 (add_left_cancel e))
      rw [a0 _ n1, b0 _ n2]
  · have nc := not_exists_cellCentre_eq (S := S) P.admissible P.odd (z := Y + siteOfCoords F.top d) ho ho0
    have nc' := not_exists_cellCentre_eq (S := S') P.admissible' hodd' (z := Y' + siteOfCoords F'.top d) ho' ho0
    obtain ⟨ex, hu⟩ := hT
    obtain ⟨ex', hu'⟩ := hT'
    unfold leadingFrame
    rw [dif_neg nc, dif_pos ex, dif_neg nc', dif_pos ex']
    have hf := ex.choose_spec
    have hf' := ex'.choose_spec
    set f := ex.choose with hfdef
    set f' := ex'.choose with hf'def
    have hoabs : ∀ i, |o i| ≤ (cellSideLength F - 1) / 2 := by
      intro i
      have := abs_le_of_mem_centredCube ho i
      have e2 : (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ)) = cellSideLength F := by simp [cellSideLength]
      rwa [e2] at this
    set a : Lattice4 := fun i => closedOrthant S (Y + siteOfCoords F.top d) i * o i + (cellSideLength F - 1) / 2
      with hadef
    have ha : ∀ i, a i = closedOrthant S (Y + siteOfCoords F.top d) i * o i + (cellSideLength F - 1) / 2 :=
      fun _ => rfl
    have hr := patchOffset_range P.odd he hoabs ha
    have hxa := patchSite_eq_cellCentre_add he ha
    have ha' : ∀ i, a i = closedOrthant S' (Y' + siteOfCoords F'.top d) i * o i + (cellSideLength F' - 1) / 2 := by
      intro i
      rw [closedOrthant_eq P hd, cellSideLength_eq P.blockSide_eq P.depth_eq]
    have hxa' := patchSite_eq_cellCentre_add he' ha'
    have ho1 : o ∈ centredCube (F.blockSide ^ F.top) := by simpa using ho
    have hb0 := localCutoff_zero_eq_one P.admissible P.odd hz he ho1 ha hr
    have hg := isLeadingEigenvector_transported P hd he he' hr (by rw [hb0]; norm_num) (f := f)
      (by rw [hxa]; exact hf)
    rw [hxa'] at hg
    obtain ⟨hg0, q, hq⟩ := hu' _ _ hg hf'
    have cell1 : enclosingCell (cellCentre 0 (Y + siteOfCoords F.top d) + siteOfCoords 0 o) =
        Y + siteOfCoords F.top d :=
      enclosingCell_cellCentre_add P.odd _ o ho
    have cell2 : enclosingCell (cellCentre 0 (Y' + siteOfCoords F'.top d) + siteOfCoords 0 o) =
        Y' + siteOfCoords F'.top d :=
      enclosingCell_cellCentre_add hodd' _ o ho'
    rw [cell2] at hg0
    rw [cell1, cell2]
    have hidx := localCellIndex_eq P hd he
    have g0 : transported S S' (Y + siteOfCoords F.top d) (Y' + siteOfCoords F'.top d) f
        (Y' + siteOfCoords F'.top d) = f (Y + siteOfCoords F.top d) := by
      have := transported_localCell P hd he he' (zero_mem_localCellIndex hz) (f := f)
      rwa [localCell_zero, localCell_zero] at this
    have inb : ∀ v ∈ localCellIndex S (Y + siteOfCoords F.top d),
        WithinRadius r (d + fun i => closedOrthant S (Y + siteOfCoords F.top d) i * v i) := by
      intro v hv i
      have a1 := abs_add_le (d i) (closedOrthant S (Y + siteOfCoords F.top d) i * v i)
      rw [abs_sign_mul (he i)] at a1
      have a2 := (mem_localCellIndex.1 hv).1 i
      have a3 : |v i| ≤ 21 := abs_le.2 (by constructor <;> linarith [a2.1, a2.2])
      simp only [Pi.add_apply]
      linarith [hd i]
    have gy : transported S S' (Y + siteOfCoords F.top d) (Y' + siteOfCoords F'.top d) f
        (Y' + siteOfCoords F'.top h') = f (Y + siteOfCoords F.top h') := by
      by_cases hex : ∃ v ∈ localCellIndex S (Y + siteOfCoords F.top d),
          Y + siteOfCoords F.top h' = localCell S (Y + siteOfCoords F.top d) v
      · obtain ⟨v, hv, e⟩ := hex
        have e1 : h' = d + fun i => closedOrthant S (Y + siteOfCoords F.top d) i * v i := by
          rw [localCell_add_siteOfCoords] at e
          exact siteOfCoords_injOn_withinRadius P.extent_large hh (inb v hv) (add_left_cancel e)
        have e2 : Y' + siteOfCoords F'.top h' = localCell S' (Y' + siteOfCoords F'.top d) v := by
          rw [localCell_eq P hd, ← e1]
        rw [e2, e, transported_localCell P hd he he' hv]
      · have hfy : f (Y + siteOfCoords F.top h') = 0 := by
          obtain ⟨-, l, hl, hop⟩ := hf
          have hbz : cellCutoff (patchSite S (Y + siteOfCoords F.top d) a) (Y + siteOfCoords F.top h') = 0 := by
            by_contra hb
            rw [hxa] at hb
            rw [← hxa] at hb
            obtain ⟨v, hvb, e⟩ := exists_localCell_of_cellCutoff_ne_zero P.admissible P.odd he hr hb
            exact hex ⟨v, mem_localCellIndex.2 ⟨hvb, e ▸ hy⟩, e⟩
          rw [hxa] at hbz
          have h1 := hop _ hy
          rw [localizationOperator_eq_zero_of_cellCutoff_eq_zero hbz] at h1
          have l0 : l ≠ 0 := by
            intro h0
            rw [h0] at hl
            norm_num at hl
          exact (smul_eq_zero.1 h1.symm).resolve_left l0
        rw [hfy]
        refine transported_eq_zero fun v hv e => hex ⟨v, hv, ?_⟩
        rw [localCell_eq P hd] at e
        have e1 := siteOfCoords_injOn_withinRadius P.extent_large' (inb v hv) hh (add_left_cancel e)
        rw [localCell_add_siteOfCoords, e1]
    rw [g0] at hg0
    rw [hq _ hy', hq _ hz', gy, g0, polarUnit_mul hg0 (coe_unitQuaternion_ne_zero q), polarUnit_coe, mul_inv_rev]
    have e3 : ((q : ℍ[ℝ])) * ((q⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel]
      rfl
    simp only [Submonoid.coe_mul]
    rw [mul_assoc, ← mul_assoc (q : ℍ[ℝ]), e3, one_mul]
theorem exists_cell_offset_decomposition (hodd : Odd F.blockSide) (b : Lattice4) :
    ∃ d o : Lattice4, o ∈ centredCube (F.blockSide ^ (F.top - 0)) ∧
      (∀ i, b i = cellSideLength F * d i + o i) := by
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  have hN := cellSideLength_pos (F := F) hodd.pos
  set m := (cellSideLength F - 1) / 2 with hm
  refine ⟨fun i => (b i + m) / cellSideLength F, fun i => (b i + m) % cellSideLength F - m, ?_, fun i => ?_⟩
  · refine Fintype.mem_piFinset.2 fun i => ?_
    have e2 : (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ)) = cellSideLength F := by simp [cellSideLength]
    rw [Finset.mem_Icc, e2, ← hm]
    have h1 := Int.emod_nonneg (b i + m) hN.ne'
    have h2 := Int.emod_lt_of_pos (b i + m) hN
    constructor <;> omega
  · have := Int.mul_ediv_add_emod (b i + m) (cellSideLength F)
    simp only
    linarith
theorem cellCentre_add_eq (d o b : Lattice4) (h : ∀ i, b i = cellSideLength F * d i + o i) :
    cellCentre 0 (Y + siteOfCoords F.top d) + siteOfCoords 0 o = cellCentre 0 Y + siteOfCoords 0 b := by
  rw [cellCentre_add 0 (Nat.zero_le _), add_assoc, ← siteOfCoords_add]
  congr 2
  funext i
  rw [h i]
  simp [cellSideLength]
theorem abs_cell_add_le (hodd : Odd F.blockSide) {b d o : Lattice4}
    (hb : IsInnerOffset F.blockSide F.top r 0 b) (ho : o ∈ centredCube (F.blockSide ^ (F.top - 0)))
    (h : ∀ i, b i = cellSideLength F * d i + o i) : ∀ i, |d i| + 100 ≤ (r : ℤ) := by
  intro i
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  have hN := cellSideLength_pos (F := F) hodd.pos
  have h1 := hb i
  have h2 := abs_le_of_mem_centredCube ho i
  have e2 : (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ)) = cellSideLength F := by simp [cellSideLength]
  rw [e2] at h2
  have e3 : ((F.blockSide : ℤ)) ^ F.top = cellSideLength F := rfl
  rw [pow_zero, one_mul, e3] at h1
  have h3 : cellSideLength F * |d i| ≤ |b i| + |o i| := by
    have : cellSideLength F * d i = b i - o i := by rw [h i]; ring
    have h4 : |cellSideLength F * d i| = cellSideLength F * |d i| := by rw [abs_mul, abs_of_pos hN]
    rw [← h4, this]
    exact abs_sub _ _
  have h5 : cellSideLength F * |d i| < cellSideLength F * ((r : ℤ) - 99) := by
    have : cellSideLength F * ((r : ℤ) - 99) = ((r : ℤ) - 100) * cellSideLength F + cellSideLength F := by ring
    rw [this]
    omega
  have h6 := lt_of_mul_lt_mul_left h5 hN.le
  omega
theorem baseSite_mem (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) : baseSite x ∈ sitesOfCells S 0 := by apply _root_.YangMills.Construction.ReferenceBounds.baseSite_mem_sitesOfCells <;> assumption
theorem leadingFrame_eq_of_innerOffset (P : AgreeOnBox S S' V V' Y Y' r)
    (he : ∀ z, ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (he' : ∀ z, ∀ i, closedOrthant S' z i = 1 ∨ closedOrthant S' z i = -1)
    (hl : ∀ x ∈ sitesOfCells S 0, HasLeadingLine S V x) (hl' : ∀ x ∈ sitesOfCells S' 0, HasLeadingLine S' V' x)
    {b h : Lattice4} (hb : IsInnerOffset F.blockSide F.top r 0 b)
    (hx : cellCentre 0 Y + siteOfCoords 0 b ∈ sitesOfCells S 0) (hh : WithinRadius r h)
    (hy : Y + siteOfCoords F.top h ∈ S) :
    leadingFrame S V (cellCentre 0 Y + siteOfCoords 0 b) (Y + siteOfCoords F.top h) =
      leadingFrame S' V' (cellCentre 0 Y' + siteOfCoords 0 b) (Y' + siteOfCoords F'.top h) := by
  obtain ⟨d, o, ho, hbo⟩ := exists_cell_offset_decomposition (F := F) P.odd b
  have hd := abs_cell_add_le P.odd hb ho hbo
  have hbo' : ∀ i, b i = cellSideLength F' * d i + o i := by
    rw [cellSideLength_eq P.blockSide_eq P.depth_eq]
    exact hbo
  have e1 := cellCentre_add_eq (Y := Y) d o b hbo
  have e2 := cellCentre_add_eq (Y := Y') d o b hbo'
  rw [← e1, ← e2]
  rw [← e1] at hx
  have hz : Y + siteOfCoords F.top d ∈ S := by
    have := enclosingCell_mem P.odd hx
    rwa [enclosingCell_cellCentre_add P.odd _ o ho] at this
  have hz' : Y' + siteOfCoords F'.top d ∈ S' := (P.cells_iff d fun i => by linarith [hd i]).1 hz
  have ho' : o ∈ centredCube (F'.blockSide ^ (F'.top - 0)) := by
    simpa only [BlockFrame.top, P.blockSide_eq, P.depth_eq] using ho
  exact leadingFrame_eq_of_agree P hd (he _) (he' _) hz ho (hl _ hx)
    (hl' _ (mem_sitesOfCells.2 ⟨_, hz', o, ho', rfl⟩)) hh hy
theorem quaternionPairing_eq (P : AgreeOnBox S S' V V' Y Y' r)
    (he : ∀ z, ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (he' : ∀ z, ∀ i, closedOrthant S' z i = 1 ∨ closedOrthant S' z i = -1)
    (hl : ∀ x ∈ sitesOfCells S 0, HasLeadingLine S V x) (hl' : ∀ x ∈ sitesOfCells S' 0, HasLeadingLine S' V' x)
    {b1 b2 : Lattice4} (hb1 : IsInnerOffset F.blockSide F.top r 0 b1) (hb2 : IsInnerOffset F.blockSide F.top r 0 b2)
    (hx1 : cellCentre 0 Y + siteOfCoords 0 b1 ∈ sitesOfCells S 0)
    (hx2 : cellCentre 0 Y + siteOfCoords 0 b2 ∈ sitesOfCells S 0) :
    quaternionPairing S (leadingFrame S V (cellCentre 0 Y + siteOfCoords 0 b1))
        (leadingFrame S V (cellCentre 0 Y + siteOfCoords 0 b2)) =
      quaternionPairing S' (leadingFrame S' V' (cellCentre 0 Y' + siteOfCoords 0 b1))
        (leadingFrame S' V' (cellCentre 0 Y' + siteOfCoords 0 b2)) := by
  classical
  have hodd' := P.odd'
  obtain ⟨d, o, ho, hbo⟩ := exists_cell_offset_decomposition (F := F) P.odd b1
  have hd := abs_cell_add_le P.odd hb1 ho hbo
  have hbo' : ∀ i, b1 i = cellSideLength F' * d i + o i := by
    rw [cellSideLength_eq P.blockSide_eq P.depth_eq]
    exact hbo
  have e1 := cellCentre_add_eq (Y := Y) d o b1 hbo
  have e2 := cellCentre_add_eq (Y := Y') d o b1 hbo'
  have hoabs : ∀ i, |o i| ≤ (cellSideLength F - 1) / 2 := by
    intro i
    have := abs_le_of_mem_centredCube ho i
    have e3 : (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ)) = cellSideLength F := by simp [cellSideLength]
    rwa [e3] at this
  set a : Lattice4 := fun i => closedOrthant S (Y + siteOfCoords F.top d) i * o i + (cellSideLength F - 1) / 2
    with hadef
  have ha : ∀ i, a i = closedOrthant S (Y + siteOfCoords F.top d) i * o i + (cellSideLength F - 1) / 2 :=
    fun _ => rfl
  have hr := patchOffset_range P.odd (he _) hoabs ha
  have hxa := patchSite_eq_cellCentre_add (he _) ha
  have ha' : ∀ i, a i = closedOrthant S' (Y' + siteOfCoords F'.top d) i * o i + (cellSideLength F' - 1) / 2 := by
    intro i
    rw [closedOrthant_eq P hd, cellSideLength_eq P.blockSide_eq P.depth_eq]
  have hxa' := patchSite_eq_cellCentre_add (he' _) ha'
  have hr' : ∀ i, -(10 * cellSideLength F') ≤ a i ∧ a i < 21 * cellSideLength F' := by
    rw [cellSideLength_eq P.blockSide_eq P.depth_eq]
    exact hr
  unfold quaternionPairing
  rw [sum_eq_sum_localCellIndex P.admissible P.odd (he (Y + siteOfCoords F.top d)) hr
      (fun w => star (leadingFrame S V (cellCentre 0 Y + siteOfCoords 0 b1) w) *
        leadingFrame S V (cellCentre 0 Y + siteOfCoords 0 b2) w)
      (fun w hw h0 => by
        rw [hxa, e1] at h0
        rw [leadingFrame_eq_zero P.admissible P.odd hw h0, star_zero, zero_mul]),
    sum_eq_sum_localCellIndex P.admissible' hodd' (he' (Y' + siteOfCoords F'.top d)) hr'
      (fun w => star (leadingFrame S' V' (cellCentre 0 Y' + siteOfCoords 0 b1) w) *
        leadingFrame S' V' (cellCentre 0 Y' + siteOfCoords 0 b2) w)
      (fun w hw h0 => by
        rw [hxa', e2] at h0
        rw [leadingFrame_eq_zero P.admissible' hodd' hw h0, star_zero, zero_mul]),
    localCellIndex_eq P hd (he _)]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hin : WithinRadius r (d + fun i => closedOrthant S (Y + siteOfCoords F.top d) i * v i) := by
    intro i
    have a1 := abs_add_le (d i) (closedOrthant S (Y + siteOfCoords F.top d) i * v i)
    rw [abs_sign_mul (he _ i)] at a1
    have a2 := (mem_localCellIndex.1 hv).1 i
    have a3 : |v i| ≤ 21 := abs_le.2 (by constructor <;> linarith [a2.1, a2.2])
    simp only [Pi.add_apply]
    linarith [hd i]
  have hm := (mem_localCellIndex.1 hv).2
  rw [localCell_add_siteOfCoords] at hm
  rw [localCell_eq P hd, localCell_add_siteOfCoords, leadingFrame_eq_of_innerOffset P he he' hl hl' hb1 hx1 hin hm,
    leadingFrame_eq_of_innerOffset P he he' hl hl' hb2 hx2 hin hm]
end Final
end AgreeingPairs
theorem agreeingPairsLocality_of_leadingEigenvectorLine (hTop : leadingEigenvectorLineStatement) :
    agreeingPairsLocalityStatement := by
  classical
  open AgreeingPairs LocalPartition in
  obtain ⟨c, hc, hT⟩ := hTop
  refine ⟨c, hc, ?_⟩
  intro F F' m S S' s V V' Y Y' r hL ht hodd hamb hamb' hm hreg hreg' hs hsc hcold hcold' hag
  obtain ⟨hs1, hs2, hS, hV⟩ := hag
  have P : AgreeingPairs.AgreeOnBox S S' V V' Y Y' r := ⟨hL, ht, hodd, hamb, hamb', hs1, hs2, hS, hV⟩
  have hodd' := P.odd'
  have hl : ∀ x ∈ sitesOfCells S 0, AgreeingPairs.HasLeadingLine S V x :=
    fun x hx => hT F m S hodd hamb hm hreg s V hs hsc hcold x hx
  have hl' : ∀ x ∈ sitesOfCells S' 0, AgreeingPairs.HasLeadingLine S' V' x :=
    fun x hx => hT F' m S' hodd' hamb' hm hreg' s V' hs hsc hcold' x hx
  have he : ∀ z, ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 :=
    fun z => (closedOrthant_spec hreg (by omega) z).1
  have he' : ∀ z, ∀ i, closedOrthant S' z i = 1 ∨ closedOrthant S' z i = -1 :=
    fun z => (closedOrthant_spec hreg' (by omega) z).1
  refine ⟨fun b h hb hx hh hy => AgreeingPairs.leadingFrame_eq_of_innerOffset P he he' hl hl' hb hx hh hy, ?_⟩
  intro j p i hj hp hp1 hbond
  have hnn : F'.top = F.top := by simp [BlockFrame.top, ht]
  have hj' : j ≤ F.top := hj.le
  have hj2 : j ≤ F'.top := hnn ▸ hj'
  have y1 := (Finset.mem_product.1 (Finset.mem_filter.1 hbond).1).1
  have y2 := (Finset.mem_filter.1 hbond).2
  simp only [] at y1 y2
  have t1 : baseSite (cellCentre j Y + siteOfCoords j p) =
      cellCentre 0 Y + siteOfCoords 0 (fun l => (F.blockSide : ℤ) ^ j * p l) := by
    rw [baseSite_add j hj', baseSite_cellCentre j hj']
  have t2 : baseSite (cellCentre j Y + siteOfCoords j p + unitStep j i) =
      cellCentre 0 Y + siteOfCoords 0 (fun l => (F.blockSide : ℤ) ^ j * (p + Pi.single i 1 : Lattice4) l) := by
    rw [unitStep_eq, add_assoc, ← siteOfCoords_add, baseSite_add j hj', baseSite_cellCentre j hj']
    rfl
  have t1' : baseSite (cellCentre j Y' + siteOfCoords j p) =
      cellCentre 0 Y' + siteOfCoords 0 (fun l => (F.blockSide : ℤ) ^ j * p l) := by
    rw [baseSite_add j hj2, baseSite_cellCentre j hj2, hL]
  have t2' : baseSite (cellCentre j Y' + siteOfCoords j p + unitStep j i) =
      cellCentre 0 Y' + siteOfCoords 0 (fun l => (F.blockSide : ℤ) ^ j * (p + Pi.single i 1 : Lattice4) l) := by
    rw [unitStep_eq, add_assoc, ← siteOfCoords_add, baseSite_add j hj2, baseSite_cellCentre j hj2, hL]
    rfl
  have b1 : IsInnerOffset F.blockSide F.top r 0 (fun l => (F.blockSide : ℤ) ^ j * p l) := by
    intro l
    have := hp l
    rw [pow_zero, one_mul, abs_mul, abs_of_nonneg (by positivity)]
    exact this
  have b2 : IsInnerOffset F.blockSide F.top r 0
      (fun l => (F.blockSide : ℤ) ^ j * (p + Pi.single i 1 : Lattice4) l) := by
    intro l
    have := hp1 l
    rw [pow_zero, one_mul, abs_mul, abs_of_nonneg (by positivity)]
    exact this
  have x1 := AgreeingPairs.baseSite_mem hodd hj' y1
  have x2 := AgreeingPairs.baseSite_mem hodd hj' y2
  rw [t1] at x1
  rw [t2] at x2
  unfold referenceGaugeField
  rw [t1, t2, t1', t2', AgreeingPairs.quaternionPairing_eq P he he' hl hl' b1 b2 x1 x2]
end BlockAverages
end YangMills.Construction
end
