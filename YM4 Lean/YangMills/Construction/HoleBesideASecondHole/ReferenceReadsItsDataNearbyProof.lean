import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCellProof
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfTheTopAverageProof
import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.TopVectorsOfASite
import YangMills.Construction.HoleBesideASecondHole.ReferenceReadsItsDataNearby
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CellTerms
open BlockAverages LumpContours
namespace ReferenceLocality
variable {F : BlockFrame}
theorem natAbs_valMinAbs_intCast_le (p : ℕ) (A : ℤ) : (((A : ZMod p)).valMinAbs).natAbs ≤ A.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem cellSupDist_triangle (x y w : F.Cell) : cellSupDist x w ≤ cellSupDist x y + cellSupDist y w := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_add_siteOfCoords_le (y : F.Cell) (a : Fin 4 → ℤ) (r : ℕ) (ha : ∀ i, |a i| ≤ r) :
    cellSupDist y (y + siteOfCoords F.top a) ≤ r := by
  rw [cellSupDist_comm]
  refine Finset.sup_le fun i _ => ?_
  have e : (y + siteOfCoords F.top a : F.Cell) i - y i = ((a i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e]
  refine (natAbs_valMinAbs_intCast_le _ _).trans ?_
  have := ha i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
theorem sum_eq_sum_of_support_iff {M : Type} [AddCommMonoid M] {S S' : Finset F.Cell} (g : F.Cell → M)
    (h : ∀ y, g y ≠ 0 → (y ∈ S ↔ y ∈ S')) : ∑ y ∈ S, g y = ∑ y ∈ S', g y := by
  classical
  have e : ∀ T : Finset F.Cell, ∑ y ∈ T, g y = ∑ y ∈ T.filter (fun y => g y ≠ 0), g y := fun T => by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : g y = 0 <;> simp [hy]
  rw [e S, e S']
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext y
  simp only [Finset.mem_filter]
  constructor
  · exact fun a => ⟨(h y a.2).1 a.1, a.2⟩
  · exact fun a => ⟨(h y a.2).2 a.1, a.2⟩
theorem cellSupDist_enclosingCell_le_one_of_cellCutoff_ne_zero (hL : Odd F.blockSide) {x : F.Site 0} {y : F.Cell}
    (hb : cellCutoff x y ≠ 0) : cellSupDist (enclosingCell x) y ≤ 1 := by
  classical
  set z := enclosingCell x with hz
  have hu := BlockLevels.mem_sitesBelow_enclosingCell (j := 0) (Nat.zero_le _) hL x
  rw [BlockLevels.sitesBelow_cell_eq] at hu
  obtain ⟨hh, hmem, hx⟩ := Finset.mem_image.1 hu
  set N : ℤ := (F.blockSide : ℤ) ^ F.top with hN
  have hN0 : 0 < N := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hL.pos
    positivity
  have hcs : ((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) = N := by simp [hN]
  have hhb : ∀ i, 2 * |hh i| < N := fun i => by
    have h1 := BlockLevels.mem_centredCube_iff.1 hmem i
    rw [hcs] at h1
    have : ((N - 1) / 2) * 2 ≤ N - 1 := Int.ediv_mul_le _ (by norm_num)
    omega
  refine Finset.sup_le fun i _ => ?_
  have hfac : cutoffProfile ((((x - cellCentre 0 y) i).valMinAbs : ℝ) / (F.blockSide : ℝ) ^ F.top) ≠ 0 :=
    (Finset.prod_ne_zero_iff.1 hb) i (Finset.mem_univ i)
  have hlt := abs_lt_of_cutoffProfile_ne_zero hfac
  set v := ((x - cellCentre 0 y) i).valMinAbs with hv
  have hNr : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
    positivity
  have hv2 : 10 * |v| < 9 * N := by
    rw [abs_div, abs_of_pos hNr, div_lt_iff₀ hNr] at hlt
    have : (10 : ℝ) * |(v : ℝ)| < 9 * ((F.blockSide : ℝ) ^ F.top) := by
      norm_num at hlt
      linarith
    have h2 : ((10 * |v| : ℤ) : ℝ) < ((9 * N : ℤ) : ℝ) := by
      push_cast
      rw [hN]
      push_cast
      exact this
    exact_mod_cast h2
  have hcast : ((v : ℤ) : ZMod (F.period 0 i)) = (x - cellCentre 0 y) i := ZMod.coe_valMinAbs _
  have hxi : x i = cellCentre 0 z i + ((hh i : ℤ) : ZMod (F.period 0 i)) := by
    rw [← hx]
    rfl
  have hcen : ∀ w : F.Cell, cellCentre 0 w i = ((N * siteCoords w i : ℤ) : ZMod (F.period 0 i)) := fun w => by
    simp [cellCentre, siteOfCoords, hN]
  have hrel : ((N * (siteCoords z i - siteCoords y i) + hh i - v : ℤ) : ZMod (F.period 0 i)) = 0 := by
    have h1 : ((v : ℤ) : ZMod (F.period 0 i)) = cellCentre 0 z i + ((hh i : ℤ) : ZMod (F.period 0 i)) - cellCentre 0 y i := by
      rw [hcast, ← hxi]
      rfl
    rw [hcen z, hcen y] at h1
    push_cast at h1 ⊢
    rw [h1]
    ring
  have hdvd : ((F.period 0 i : ℕ) : ℤ) ∣ N * (siteCoords z i - siteCoords y i) + hh i - v :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hrel
  have hper : ((F.period 0 i : ℕ) : ℤ) = (F.extent i : ℤ) * N := by simp [BlockFrame.period, hN]
  rw [hper] at hdvd
  obtain ⟨w, hw⟩ := hdvd
  set t : ℤ := (F.extent i : ℤ) * w - (siteCoords z i - siteCoords y i) with ht
  have ht' : hh i - v = N * t := by
    rw [ht]
    linarith
  have htb : |t| ≤ 1 := by
    have h1 : |N * t| < 2 * N := by
      rw [← ht']
      have a1 := abs_sub (hh i) v
      have a2 := hhb i
      omega
    rw [abs_mul, abs_of_pos hN0] at h1
    by_contra hcon
    push Not at hcon
    have : 2 ≤ |t| := by omega
    nlinarith
  have hzy : z i - y i = ((-(t) : ℤ) : ZMod (F.period F.top i)) := by
    have h1 : ((siteCoords z i : ℤ) : ZMod (F.period F.top i)) = z i := by simp [siteCoords]
    have h2 : ((siteCoords y i : ℤ) : ZMod (F.period F.top i)) = y i := by simp [siteCoords]
    have h3 : ((F.extent i : ℤ) : ZMod (F.period F.top i)) = 0 := by
      have : F.period F.top i = F.extent i := by simp [BlockFrame.period]
      rw [this]
      simp
    rw [← h1, ← h2, ht]
    push_cast
    have h4 : (((F.extent i : ℕ) : ZMod (F.period F.top i))) = 0 := by exact_mod_cast h3
    rw [h4]
    ring
  rw [hzy]
  refine (natAbs_valMinAbs_intCast_le _ _).trans ?_
  rw [Int.natAbs_neg]
  rw [Int.abs_eq_natAbs] at htb
  exact_mod_cast htb
section Agreement
variable {S S' : Finset F.Cell} {V V' : F.GaugeField F.top} {z : F.Cell}
theorem isOrthantClosedNear_iff_of_agreeNear (h : AgreeNear 100 S S' V V' z) {y : F.Cell} (hy : cellSupDist z y ≤ 36)
    (e : Fin 4 → ℤ) : IsOrthantClosedNear S y e ↔ IsOrthantClosedNear S' y e := by
  have hS := h.1
  have key : ∀ {A B : Finset F.Cell}, (∀ w, cellSupDist z w ≤ 100 → (w ∈ A ↔ w ∈ B)) → IsOrthantClosedNear A y e →
      IsOrthantClosedNear B y e := by
    intro A B hAB hc q hq hd k hk hk'
    have h1 : cellSupDist z q ≤ 68 := by
      have := cellSupDist_triangle z y q
      have h2 : cellSupDist y q ≤ 32 := by rw [cellSupDist_comm]; exact hd
      omega
    have h3 := hc q ((hAB q (by omega)).2 hq) hd k hk hk'
    have h4 : cellSupDist z (q + siteOfCoords F.top k) ≤ 100 := by
      have := cellSupDist_triangle z q (q + siteOfCoords F.top k)
      have h5 := cellSupDist_add_siteOfCoords_le q k 32 (by simpa using hk')
      omega
    exact (hAB _ h4).1 h3
  exact ⟨key hS, key fun w hw => (hS w hw).symm⟩
theorem closedOrthant_eq_of_agreeNear (h : AgreeNear 100 S S' V V' z) {y : F.Cell} (hy : cellSupDist z y ≤ 36) :
    closedOrthant S y = closedOrthant S' y := by
  classical
  unfold closedOrthant
  have e : (fun e => decide (IsOrthantClosedNear S y e)) = fun e => decide (IsOrthantClosedNear S' y e) := by
    funext e
    exact decide_eq_decide.2 (isOrthantClosedNear_iff_of_agreeNear h hy e)
  rw [e]
theorem cellPartition_eq_zero_of_cellCutoff_eq_zero {T : Finset F.Cell} {x : F.Site 0} {y : F.Cell}
    (h : cellCutoff x y = 0) : cellPartition T x y = 0 := by
  simp [cellPartition, h]
theorem cellPartition_eq_of_agreeNear (hL : Odd F.blockSide) (h : AgreeNear 100 S S' V V' z) {x : F.Site 0}
    (hx : enclosingCell x = z) (y : F.Cell) : cellPartition S x y = cellPartition S' x y := by
  unfold cellPartition
  congr 1
  refine sum_eq_sum_of_support_iff _ fun w hw => ?_
  have hb : cellCutoff x w ≠ 0 := fun h0 => hw (by simp [h0])
  have := cellSupDist_enclosingCell_le_one_of_cellCutoff_ne_zero hL hb
  rw [hx] at this
  exact h.1 w (by omega)
theorem cellSupDist_add_stepDisplacement_le (x : F.Cell) (st : PathStep) :
    cellSupDist z (x + stepDisplacement F.top st) ≤ cellSupDist z x + 1 := by
  refine (cellSupDist_triangle z x _).trans (Nat.add_le_add_left ?_ _)
  obtain ⟨d, b⟩ := st
  cases b
  · have := cellSupDist_add_siteOfCoords_le x (-(Pi.single d 1 : Fin 4 → ℤ)) 1 (fun i => by
      have := BlockLevels.abs_single_le_one d i
      simpa using this)
    have e : siteOfCoords (F := F) F.top (-(Pi.single d 1 : Fin 4 → ℤ)) = stepDisplacement F.top (d, false) := by
      funext k
      simp [siteOfCoords, stepDisplacement, unitStep]
    rwa [e] at this
  · have := cellSupDist_add_siteOfCoords_le x (Pi.single d 1 : Fin 4 → ℤ) 1 (fun i => by
      have := BlockLevels.abs_single_le_one d i
      simpa using this)
    have e : siteOfCoords (F := F) F.top (Pi.single d 1 : Fin 4 → ℤ) = stepDisplacement F.top (d, true) := by
      simp [stepDisplacement, unitStep]
    rwa [e] at this
theorem pathHolonomy_eq_of_agreeNear (h : AgreeNear 100 S S' V V' z) (l : List PathStep) :
    ∀ x : F.Cell, cellSupDist z x + l.length ≤ 100 → pathHolonomy V x l = pathHolonomy V' x l := by
  induction l with
  | nil => intro x _; rfl
  | cons st r ih =>
    intro x hx
    have hlen : (st :: r).length = r.length + 1 := rfl
    have h1 := cellSupDist_add_stepDisplacement_le (z := z) x st
    simp only [pathHolonomy]
    rw [ih _ (by omega)]
    congr 1
    obtain ⟨d, b⟩ := st
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      have e2 : x - unitStep F.top d + unitStep F.top d = x := by abel
      have h2 : cellSupDist z (x - unitStep F.top d) ≤ cellSupDist z x + 1 := by
        have := cellSupDist_add_stepDisplacement_le (z := z) x (d, false)
        simpa [stepDisplacement, sub_eq_add_neg] using this
      rw [h.2 (x - unitStep F.top d) d (by omega) (by rw [e2]; omega)]
    · simp only [linkValue, if_true]
      have h2 : cellSupDist z (x + unitStep F.top d) ≤ cellSupDist z x + 1 := by
        have := cellSupDist_add_stepDisplacement_le (z := z) x (d, true)
        simpa [stepDisplacement] using this
      rw [h.2 x d (by omega) (by omega)]
theorem length_axisPath_le_eight (o : Fin 4 → ℤ) (ho : ∀ i, |o i| ≤ 2) : (axisPath o 1).length ≤ 8 := by
  have e : List.finRange 4 = [0, 1, 2, 3] := by decide
  have hb : ∀ k, ((o k).natAbs : ℤ) ≤ 2 := fun k => by
    rw [Int.natCast_natAbs]
    exact ho k
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  simp only [axisPath, e, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_replicate,
    List.length_nil, List.append_nil, Equiv.Perm.coe_one, id_eq]
  omega
theorem cellParallelTransport_eq_of_agreeNear (h : AgreeNear 100 S S' V V' z) {y y' : F.Cell}
    (hy : cellSupDist z y ≤ 1) (hy' : cellSupDist z y' ≤ 1) :
    cellParallelTransport S V y y' = cellParallelTransport S' V' y y' := by
  unfold cellParallelTransport
  rw [closedOrthant_eq_of_agreeNear h (by omega : cellSupDist z y ≤ 36)]
  set o := cellDisplacement y y' with ho
  set e := closedOrthant S' y with he
  have hob : ∀ i, |o i| ≤ 2 := fun i => by
    have h1 : cellSupDist y' y ≤ 2 := by
      have := cellSupDist_triangle y' z y
      have h2 : cellSupDist y' z ≤ 1 := by rw [cellSupDist_comm]; exact hy'
      omega
    have h2 : ((y' i - y i).valMinAbs).natAbs ≤ cellSupDist y' y :=
      Finset.le_sup (f := fun i => ((y' i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h3 : |o i| = (((y' i - y i).valMinAbs).natAbs : ℤ) := by
      simp only [ho, cellDisplacement, Pi.sub_apply]
      rw [Int.natCast_natAbs]
    rw [h3]
    omega
  have h1 : ∀ i, |orthantPart e o i| ≤ 2 := fun i => by
    unfold orthantPart
    split_ifs
    · exact hob i
    · simp
  have h2 : ∀ i, |(o - orthantPart e o) i| ≤ 2 := fun i => by
    simp only [orthantPart, Pi.sub_apply]
    split_ifs
    · simp
    · simpa using hob i
  refine pathHolonomy_eq_of_agreeNear h _ _ ?_
  have l1 := length_axisPath_le_eight _ h1
  have l2 := length_axisPath_le_eight _ h2
  rw [List.length_append]
  omega
theorem localizationOperator_eq_of_agreeNear (hL : Odd F.blockSide) (h : AgreeNear 100 S S' V V' z) {x : F.Site 0}
    (hx : enclosingCell x = z) (v v' : F.Cell → ℍ[ℝ]) (hv : ∀ y, cellCutoff x y ≠ 0 → v y = v' y) (y : F.Cell) :
    localizationOperator S V x v y = localizationOperator S' V' x v' y := by
  classical
  have near : ∀ w, cellCutoff x w ≠ 0 → cellSupDist z w ≤ 1 := fun w hw => by
    have := cellSupDist_enclosingCell_le_one_of_cellCutoff_ne_zero hL hw
    rwa [hx] at this
  have hs := cellPartition_eq_of_agreeNear hL h hx
  unfold localizationOperator
  rw [sum_eq_sum_of_support_iff (S := S) (S' := S')]
  · refine Finset.sum_congr rfl fun y' _ => ?_
    rw [sum_eq_sum_of_support_iff (S := S) (S' := S')]
    · refine Finset.sum_congr rfl fun y'' _ => ?_
      rw [hs y', hs y, hs y'']
      by_cases hb : cellCutoff x y' = 0 ∨ cellCutoff x y = 0 ∨ cellCutoff x y'' = 0
      · rcases hb with hb | hb | hb
        · simp [cellPartition_eq_zero_of_cellCutoff_eq_zero (T := S') hb]
        · simp [cellPartition_eq_zero_of_cellCutoff_eq_zero (T := S') hb]
        · simp [cellPartition_eq_zero_of_cellCutoff_eq_zero (T := S') hb]
      · push Not at hb
        obtain ⟨b1, b2, b3⟩ := hb
        rw [cellParallelTransport_eq_of_agreeNear h (near y b2) (near y' b1),
          cellParallelTransport_eq_of_agreeNear h (near y'' b3) (near y' b1), hv y'' b3]
    · intro y'' hne
      have hb : cellCutoff x y'' ≠ 0 := by
        intro h0
        apply hne
        simp [cellPartition_eq_zero_of_cellCutoff_eq_zero (T := S) h0]
      exact h.1 y'' (by have := near y'' hb; omega)
  · intro y' hne
    have hb : cellCutoff x y' ≠ 0 := by
      intro h0
      apply hne
      simp [cellPartition_eq_zero_of_cellCutoff_eq_zero (T := S) h0]
    exact h.1 y' (by have := near y' hb; omega)
theorem leadingEigenvector_eq_zero_of_cellCutoff_eq_zero {T : Finset F.Cell} {W : F.GaugeField F.top} {x : F.Site 0}
    {f : F.Cell → ℍ[ℝ]} (hf : IsLeadingEigenvector T W x f) {y : F.Cell} (hy : y ∈ T) (hb : cellCutoff x y = 0) :
    f y = 0 := by
  obtain ⟨-, l, hl, hop⟩ := hf
  have h1 := hop y hy
  have h0 : localizationOperator T W x f y = 0 := by
    unfold localizationOperator
    simp [cellPartition_eq_zero_of_cellCutoff_eq_zero (T := T) hb]
  rw [h0] at h1
  have l0 : l ≠ 0 := by
    intro e
    rw [e] at hl
    norm_num at hl
  exact (smul_eq_zero.1 h1.symm).resolve_left l0
theorem exists_leadingEigenvector_of_agreeNear (hL : Odd F.blockSide) (h : AgreeNear 100 S S' V V' z) {x : F.Site 0}
    (hx : enclosingCell x = z) {f : F.Cell → ℍ[ℝ]} (hf : IsLeadingEigenvector S V x f) :
    ∃ f' : F.Cell → ℍ[ℝ], IsLeadingEigenvector S' V' x f' ∧ ∀ y, cellCutoff x y ≠ 0 → f' y = f y := by
  classical
  have near : ∀ w, cellCutoff x w ≠ 0 → cellSupDist z w ≤ 1 := fun w hw => by
    have := cellSupDist_enclosingCell_le_one_of_cellCutoff_ne_zero hL hw
    rwa [hx] at this
  set f' : F.Cell → ℍ[ℝ] := fun y => if cellCutoff x y = 0 then 0 else f y with hf'
  have h1 : ∀ y, cellCutoff x y ≠ 0 → f' y = f y := fun y hy => by simp [hf', hy]
  have h0 : ∀ y, cellCutoff x y = 0 → f' y = 0 := fun y hy => by simp [hf', hy]
  refine ⟨f', ?_, h1⟩
  obtain ⟨hn, l, hl, hop⟩ := id hf
  refine ⟨?_, l, hl, fun y hy => ?_⟩
  · rw [← hn]
    rw [← sum_eq_sum_of_support_iff (S := S) (S' := S') (fun y => ‖f' y‖ ^ 2) (fun y hy => ?_)]
    · refine Finset.sum_congr rfl fun y hy => ?_
      by_cases hb : cellCutoff x y = 0
      · rw [h0 y hb, leadingEigenvector_eq_zero_of_cellCutoff_eq_zero hf hy hb]
      · rw [h1 y hb]
    · have hb : cellCutoff x y ≠ 0 := by
        intro e
        apply hy
        simp [h0 y e]
      exact h.1 y (by have := near y hb; omega)
  · by_cases hb : cellCutoff x y = 0
    · rw [h0 y hb, smul_zero]
      unfold localizationOperator
      simp [cellPartition_eq_zero_of_cellCutoff_eq_zero (T := S') hb]
    · have hyS : y ∈ S := (h.1 y (by have := near y hb; omega)).2 hy
      rw [h1 y hb, ← hop y hyS]
      exact (localizationOperator_eq_of_agreeNear hL h hx f f' (fun w hw => (h1 w hw).symm) y).symm
def HasLeadingLines (T : Finset F.Cell) (W : F.GaugeField F.top) : Prop :=
  ∀ x ∈ sitesOfCells T 0, (∃ f, IsLeadingEigenvector T W x f) ∧ ∀ f g, IsLeadingEigenvector T W x f →
    IsLeadingEigenvector T W x g → f (enclosingCell x) ≠ 0 ∧ ∃ q : UnitQuaternion, ∀ y ∈ T, g y = f y * (q : ℍ[ℝ])
theorem zero_mem_centredCube (hL : Odd F.blockSide) (e : ℕ) : (0 : Fin 4 → ℤ) ∈ centredCube (F.blockSide ^ e) := by apply _root_.YangMills.Construction.BlockAverages.LowCostPatch.zero_mem_centredCube <;> assumption
theorem leadingFrame_eq_zero_of_cellCutoff_eq_zero (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    {T : Finset F.Cell} {W : F.GaugeField F.top} (hT : HasLeadingLines T W) {x : F.Site 0} (hx : x ∈ sitesOfCells T 0)
    {y : F.Cell} (hy : y ∈ T) (hb : cellCutoff x y = 0) : leadingFrame T W x y = 0 := by
  classical
  unfold leadingFrame
  by_cases hc : ∃ y ∈ T, x = cellCentre 0 y
  · rw [dif_pos hc]
    have hne : y ≠ hc.choose := by
      intro e
      have hxc : x = cellCentre 0 y := by
        rw [e]
        exact hc.choose_spec.2
      have h1 := cellCutoff_self hamb hL y (zero_mem_centredCube hL F.top)
      rw [BlockLevels.siteOfCoords_zero, add_zero, ← hxc] at h1
      rw [h1] at hb
      norm_num at hb
    simp [hne]
  · rw [dif_neg hc]
    have hex := (hT x hx).1
    rw [dif_pos hex]
    rw [leadingEigenvector_eq_zero_of_cellCutoff_eq_zero hex.choose_spec hy hb, zero_mul]
theorem enclosingCell_cellCentre (hL : Odd F.blockSide) (y : F.Cell) : enclosingCell (cellCentre 0 y) = y := by apply _root_.YangMills.Construction.TopAverageCurl.enclosingCell_cellCentre <;> assumption
theorem cellCutoff_enclosingCell_ne_zero (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide) (x : F.Site 0) :
    cellCutoff x (enclosingCell x) ≠ 0 := by
  have hu := BlockLevels.mem_sitesBelow_enclosingCell (j := 0) (Nat.zero_le _) hL x
  rw [BlockLevels.sitesBelow_cell_eq] at hu
  obtain ⟨h, hh, e⟩ := Finset.mem_image.1 hu
  have hn : F.top - 0 = F.top := by omega
  rw [hn] at hh
  have h1 := cellCutoff_self hamb hL (enclosingCell x) hh
  have e' : cellCentre 0 (enclosingCell x) + siteOfCoords 0 h = x := e
  rw [e'] at h1
  rw [h1]
  norm_num
theorem leadingFrame_eq_of_agreeNear (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide) (hT : HasLeadingLines S V)
    (hT' : HasLeadingLines S' V') (h : AgreeNear 100 S S' V V' z) (hzS : z ∈ S) {x : F.Site 0}
    (hx : enclosingCell x = z) {y : F.Cell} (hb : cellCutoff x y ≠ 0) (hy : y ∈ S') :
    leadingFrame S' V' x y = leadingFrame S V x y := by
  classical
  have hzS' : z ∈ S' := (h.1 z (by rw [cellSupDist_self]; omega)).1 hzS
  have hxS : x ∈ sitesOfCells S 0 := (BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) hL).2 (by rw [hx]; exact hzS)
  have hxS' : x ∈ sitesOfCells S' 0 := (BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) hL).2 (by rw [hx]; exact hzS')
  unfold leadingFrame
  by_cases hc : ∃ y ∈ S, x = cellCentre 0 y
  · have hxz : x = cellCentre 0 z := by
      obtain ⟨y0, -, e⟩ := hc
      have := enclosingCell_cellCentre hL y0
      rw [← e, hx] at this
      rw [this]
      exact e
    have hc' : ∃ y ∈ S', x = cellCentre 0 y := ⟨z, hzS', hxz⟩
    have e1 : hc.choose = z := cellCentre_injective hamb hL.pos (hc.choose_spec.2.symm.trans hxz)
    have e2 : hc'.choose = z := cellCentre_injective hamb hL.pos (hc'.choose_spec.2.symm.trans hxz)
    rw [dif_pos hc, dif_pos hc', e1, e2]
  · have hc' : ¬ ∃ y ∈ S', x = cellCentre 0 y := by
      rintro ⟨y0, -, e⟩
      have := enclosingCell_cellCentre hL y0
      rw [← e, hx] at this
      exact hc ⟨z, hzS, by rw [this]; exact e⟩
    have hex := (hT x hxS).1
    have hex' := (hT' x hxS').1
    rw [dif_neg hc, dif_neg hc', dif_pos hex, dif_pos hex']
    set f := hex.choose with hf
    set g := hex'.choose with hg
    obtain ⟨f', hf', hfe0⟩ := exists_leadingEigenvector_of_agreeNear hL h hx hex.choose_spec
    have hfe : ∀ y, cellCutoff x y ≠ 0 → f' y = f y := hfe0
    obtain ⟨hne, q, hq⟩ := (hT' x hxS').2 f' g hf' hex'.choose_spec
    have hcb := cellCutoff_enclosingCell_ne_zero hamb hL x
    have hcS' : enclosingCell x ∈ S' := by rw [hx]; exact hzS'
    have hgc : g (enclosingCell x) = f (enclosingCell x) * (q : ℍ[ℝ]) := by
      rw [hq _ hcS', hfe _ hcb]
    have hfc : f (enclosingCell x) ≠ 0 := by
      rw [← hfe _ hcb]
      exact hne
    have hu : polarUnit (g (enclosingCell x)) = polarUnit (f (enclosingCell x)) * q := by
      rw [hgc, polarUnit_mul hfc (coe_unitQuaternion_ne_zero q)]
      congr 1
      apply Subtype.ext
      rw [coe_polarUnit (coe_unitQuaternion_ne_zero q), _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion]
      simp
    rw [hu, hq y hy, hfe y hb, mul_inv_rev, BlockLevels.unitQuaternion_coe_mul, ← mul_assoc, mul_assoc (f y),
      BlockLevels.unitQuaternion_mul_inv, mul_one]
theorem quaternionPairing_leadingFrame_eq_of_agreeNear (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (hT : HasLeadingLines S V) (hT' : HasLeadingLines S' V') {z' : F.Cell} (h : AgreeNear 100 S S' V V' z)
    (h' : AgreeNear 100 S S' V V' z') (hzS : z ∈ S) (hzS' : z' ∈ S) {x x' : F.Site 0} (hx : enclosingCell x = z)
    (hx' : enclosingCell x' = z') :
    quaternionPairing S' (leadingFrame S' V' x) (leadingFrame S' V' x') =
      quaternionPairing S (leadingFrame S V x) (leadingFrame S V x') := by
  classical
  have near : ∀ w, cellCutoff x w ≠ 0 → cellSupDist z w ≤ 1 := fun w hw => by
    have := cellSupDist_enclosingCell_le_one_of_cellCutoff_ne_zero hL hw
    rwa [hx] at this
  have hiff : ∀ w, cellCutoff x w ≠ 0 → (w ∈ S ↔ w ∈ S') := fun w hw => h.1 w (by have := near w hw; omega)
  have hzT : z ∈ S' := (h.1 z (by rw [cellSupDist_self]; omega)).1 hzS
  have hzT' : z' ∈ S' := (h'.1 z' (by rw [cellSupDist_self]; omega)).1 hzS'
  have hxS : x ∈ sitesOfCells S 0 := (BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) hL).2 (by rw [hx]; exact hzS)
  have hxS' : x ∈ sitesOfCells S' 0 := (BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) hL).2 (by rw [hx]; exact hzT)
  have hx2S : x' ∈ sitesOfCells S 0 := (BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) hL).2 (by rw [hx']; exact hzS')
  have hx2S' : x' ∈ sitesOfCells S' 0 :=
    (BlockLevels.mem_sitesOfCells_iff (Nat.zero_le _) hL).2 (by rw [hx']; exact hzT')
  set G : F.Cell → ℍ[ℝ] := fun y => if cellCutoff x y = 0 then 0 else
    star (leadingFrame S V x y) * leadingFrame S V x' y with hG
  have e1 : quaternionPairing S (leadingFrame S V x) (leadingFrame S V x') = ∑ y ∈ S, G y := by
    unfold quaternionPairing
    refine Finset.sum_congr rfl fun y hy => ?_
    by_cases hb : cellCutoff x y = 0
    · simp [hG, hb, leadingFrame_eq_zero_of_cellCutoff_eq_zero hamb hL hT hxS hy hb]
    · simp [hG, hb]
  have e2 : quaternionPairing S' (leadingFrame S' V' x) (leadingFrame S' V' x') = ∑ y ∈ S', G y := by
    unfold quaternionPairing
    refine Finset.sum_congr rfl fun y hy => ?_
    by_cases hb : cellCutoff x y = 0
    · simp [hG, hb, leadingFrame_eq_zero_of_cellCutoff_eq_zero hamb hL hT' hxS' hy hb]
    · have hyS : y ∈ S := (hiff y hb).2 hy
      simp only [hG, if_neg hb]
      rw [leadingFrame_eq_of_agreeNear hamb hL hT hT' h hzS hx hb hy]
      congr 1
      by_cases hb' : cellCutoff x' y = 0
      · rw [leadingFrame_eq_zero_of_cellCutoff_eq_zero hamb hL hT' hx2S' hy hb',
          leadingFrame_eq_zero_of_cellCutoff_eq_zero hamb hL hT hx2S hyS hb']
      · exact leadingFrame_eq_of_agreeNear hamb hL hT hT' h' hzS' hx' hb' hy
  rw [e1, e2]
  refine (sum_eq_sum_of_support_iff G fun y hy => ?_).symm
  refine hiff y fun h0 => hy ?_
  simp [hG, h0]
end Agreement
theorem enclosingCell_baseSite (hL : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) (w : F.Site j) :
    enclosingCell (baseSite w) = enclosingCell w := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.enclosingCell_baseSite <;> assumption
theorem referenceLocalityStatement_of_leadingEigenvectorLineStatement
    (hTop : leadingEigenvectorLineStatement) : referenceLocalityStatement := by
  obtain ⟨c, hc, hTop⟩ := hTop
  refine ⟨c, 0, hc, ?_⟩
  intro F m S S' C s V V' hL _ hamb hm hreg hreg' hs hsc hcold hcold' hCS hsame
  have T1 : HasLeadingLines S V := hTop F m S hL hamb hm hreg s V hs hsc hcold
  have T2 : HasLeadingLines S' V' := hTop F m S' hL hamb hm hreg' s V' hs hsc hcold'
  refine ⟨fun z hz y hy => closedOrthant_eq_of_agreeNear (hsame z hz) hy, fun _ => 1, fun _ _ => rfl, ?_⟩
  intro j hj b hb
  have hb1 := hb.1
  have hb2 := hb.2
  have e1 : referenceFieldChain S' V' j = referenceGaugeField S' V' j := by
    unfold referenceFieldChain
    exact Function.update_of_ne hj.ne _ _
  have e2 : referenceFieldChain S V j = referenceGaugeField S V j := by
    unfold referenceFieldChain
    exact Function.update_of_ne hj.ne _ _
  rw [e1, e2]
  simp only [_root_.YangMills.Construction.BlockAverages.gaugeTransform, inv_one, one_mul, mul_one]
  unfold referenceGaugeField
  rw [quaternionPairing_leadingFrame_eq_of_agreeNear hamb hL T1 T2 (hsame _ hb1) (hsame _ hb2) (hCS hb1) (hCS hb2)
    (enclosingCell_baseSite hL hj.le b.1) (enclosingCell_baseSite hL hj.le _)]
end ReferenceLocality
end YangMills.Construction.CellTerms
end
