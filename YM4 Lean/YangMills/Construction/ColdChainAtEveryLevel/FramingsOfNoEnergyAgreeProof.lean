import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.FitsInCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.FramingsOfNoEnergyAgree
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.ZeroEnergyFramings
variable {F : BlockFrame}
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem closedOrthant_eq_one_or_neg_one (S : Finset F.Cell) (z : F.Cell) (i : Fin 4) :
    closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 := by apply _root_.YangMills.Construction.CellBumps.closedOrthant_eq_one_or_neg_one <;> assumption
theorem closedOrthant_mul_self (S : Finset F.Cell) (z : F.Cell) (i : Fin 4) :
    closedOrthant S z i * closedOrthant S z i = 1 := by
  rcases closedOrthant_eq_one_or_neg_one S z i with h | h <;> rw [h] <;> norm_num
theorem valMinAbs_eq_of_small (n : ℕ) (hn : n = 0 ∨ 64 ≤ n) (x : ZMod n) (v : ℤ) (hx : (v : ZMod n) = x)
    (hs : n = 0 ∨ 2 * |v| < n) : x.valMinAbs = v := by
  rcases hn with rfl | hn
  · subst hx
    rfl
  · haveI : NeZero n := ⟨by omega⟩
    rw [ZMod.valMinAbs_spec]
    refine ⟨hx.symm, ?_⟩
    rcases hs with h | h
    · omega
    · rw [Set.mem_Ioc]
      have := abs_lt.1 (show |v * 2| < n by rw [abs_mul]; simpa [mul_comm] using h)
      constructor
      · linarith [this.1]
      · linarith [this.2]
theorem cellSupDist_comm (a b : F.Cell) : cellSupDist a b = cellSupDist b a := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem intCast_siteCoords {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem period_cast (j : ℕ) (i : Fin 4) :
    ((F.period j i : ℕ) : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) := by
  simp [BlockFrame.period]
theorem baseSite_sub_cellCentre_valMinAbs (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide) (z y : F.Cell)
    (hd : cellSupDist y z ≤ 10) {j : ℕ} (hj : j ≤ F.top) (h' : Fin 4 → ℤ)
    (hh : h' ∈ centredCube (F.blockSide ^ (F.top - j))) (i : Fin 4) :
    ((baseSite (cellCentre j y + siteOfCoords j h' : F.Site j) - cellCentre 0 z) i).valMinAbs =
      GaugeMap.cellSideLength F * (y i - z i).valMinAbs + (F.blockSide : ℤ) ^ j * h' i := by
  set k : ℤ := (F.blockSide : ℤ) ^ j with hk
  set M : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hM
  set N : ℤ := GaugeMap.cellSideLength F with hN
  have hLpos : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hL.pos
  have hkpos : 0 < k := by positivity
  have hkM : k * M = N := by
    rw [hk, hM, hN, GaugeMap.cellSideLength, ← pow_add]
    congr 1
    omega
  have hNpos : 0 < N := by rw [← hkM]; positivity
  set x : F.Site j := cellCentre j y + siteOfCoords j h' with hx
  set cy : ℤ := siteCoords y i with hcy
  set cz : ℤ := siteCoords z i with hcz
  set c : ℤ := (y i - z i).valMinAbs with hc
  have hx1 : ((siteCoords x i : ℤ) : ZMod (F.period j i)) = ((M * cy + h' i : ℤ) : ZMod (F.period j i)) := by
    rw [intCast_siteCoords, hx]
    simp [cellCentre, siteOfCoords, hM, hcy]
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hx1
  rw [period_cast, ← hM] at he
  have hy1 : ((c : ℤ) : ZMod (F.period F.top i)) = ((cy - cz : ℤ) : ZMod (F.period F.top i)) := by
    rw [hc, ZMod.coe_valMinAbs, Int.cast_sub, hcy, hcz, intCast_siteCoords, intCast_siteCoords]
  obtain ⟨e2, he2⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hy1
  have hper : ((F.period F.top i : ℕ) : ℤ) = (F.extent i : ℤ) := by simp [BlockFrame.period]
  rw [hper] at he2
  have hnn : F.period 0 i = 0 ∨ 64 ≤ F.period 0 i := by
    rcases hamb with h0 | h64
    · left
      simp [BlockFrame.period, h0 i]
    · right
      have : 1 ≤ F.blockSide ^ (F.top - 0) := Nat.one_le_pow _ _ hL.pos
      calc 64 ≤ F.extent i := h64 i
        _ ≤ F.extent i * F.blockSide ^ (F.top - 0) := Nat.le_mul_of_pos_right _ this
  have hper0 : ((F.period 0 i : ℕ) : ℤ) = (F.extent i : ℤ) * N := by
    rw [period_cast, hN, GaugeMap.cellSideLength]
    simp
  have hcast : ((N * c + k * h' i : ℤ) : ZMod (F.period 0 i)) =
      (baseSite x - cellCentre 0 z) i := by
    have e1 : (baseSite x - cellCentre 0 z) i = ((k * siteCoords x i - N * cz : ℤ) : ZMod (F.period 0 i)) := by
      simp [baseSite, cellCentre, siteOfCoords, hk, hN, GaugeMap.cellSideLength, hcz]
    rw [e1]
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
    rw [hper0]
    refine ⟨e2 - e, ?_⟩
    have hv : siteCoords x i = M * cy + h' i - (F.extent i : ℤ) * M * e := by linarith
    rw [hv]
    have e3 : k * (M * cy + h' i - (F.extent i : ℤ) * M * e) =
        (k * M) * cy + k * h' i - (F.extent i : ℤ) * (k * M) * e := by ring
    rw [e3, hkM]
    linear_combination N * he2
  have hci : |c| ≤ 10 := by
    have h1 : (c.natAbs : ℕ) ≤ cellSupDist y z :=
      Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 : c.natAbs ≤ 10 := h1.trans hd
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h2
  have hh1 := Fintype.mem_piFinset.1 hh i
  have hMc : (((F.blockSide ^ (F.top - j) : ℕ) : ℤ)) = M := by
    rw [hM]
    push_cast
    rfl
  rw [Finset.mem_Icc, hMc] at hh1
  have hMo : Odd M := by
    rw [hM]
    exact Odd.pow (by exact_mod_cast hL)
  obtain ⟨m, hm⟩ := hMo
  have hmd : (M - 1) / 2 = m := by omega
  rw [hmd] at hh1
  have hkh : 2 * |k * h' i| ≤ N - 1 := by
    rw [abs_mul, abs_of_pos hkpos]
    have h3 : |h' i| ≤ m := abs_le.2 hh1
    have h4 : k * |h' i| ≤ k * m := mul_le_mul_of_nonneg_left h3 hkpos.le
    have h5 : 2 * (k * m) = N - k := by
      rw [← hkM, hm]
      ring
    linarith
  have hs : F.period 0 i = 0 ∨ 2 * |N * c + k * h' i| < ((F.period 0 i : ℕ) : ℤ) := by
    rcases hnn with h | h
    · exact Or.inl h
    · right
      have hside : (64 : ℤ) ≤ (F.extent i : ℤ) := by
        rcases hamb with h0 | h64
        · exfalso
          simp [BlockFrame.period, h0 i] at h
        · exact_mod_cast h64 i
      rw [hper0]
      have h6 : |N * c + k * h' i| ≤ N * 10 + |k * h' i| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos hNpos]
        have := mul_le_mul_of_nonneg_left hci hNpos.le
        linarith
      nlinarith
  exact valMinAbs_eq_of_small _ hnn _ _ hcast hs
theorem two_mul_abs_scaled_offset_le (hL : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) (h' : Fin 4 → ℤ)
    (hh : h' ∈ centredCube (F.blockSide ^ (F.top - j))) (i : Fin 4) :
    2 * |(F.blockSide : ℤ) ^ j * h' i| ≤ GaugeMap.cellSideLength F - 1 := by
  set k : ℤ := (F.blockSide : ℤ) ^ j with hk
  set M : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hM
  have hLpos : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hL.pos
  have hkpos : 0 < k := by positivity
  have hkM : k * M = GaugeMap.cellSideLength F := by
    rw [hk, hM, GaugeMap.cellSideLength, ← pow_add]
    congr 1
    omega
  have hh1 := Fintype.mem_piFinset.1 hh i
  have hMc : (((F.blockSide ^ (F.top - j) : ℕ) : ℤ)) = M := by
    rw [hM]
    push_cast
    rfl
  rw [Finset.mem_Icc, hMc] at hh1
  have hMo : Odd M := by
    rw [hM]
    exact Odd.pow (by exact_mod_cast hL)
  obtain ⟨m, hm⟩ := hMo
  have hmd : (M - 1) / 2 = m := by omega
  rw [hmd] at hh1
  rw [abs_mul, abs_of_pos hkpos]
  have h3 : |h' i| ≤ m := abs_le.2 hh1
  have h4 : k * |h' i| ≤ k * m := mul_le_mul_of_nonneg_left h3 hkpos.le
  have h5 : 2 * (k * m) = GaugeMap.cellSideLength F - k := by
    rw [← hkM, hm]
    ring
  linarith
theorem baseSite_mem_patchBaseSites (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide) {S : Finset F.Cell}
    {z y : F.Cell} (hy : y ∈ S) (hd : cellSupDist y z ≤ 10) {j : ℕ} (hj : j ≤ F.top) (h' : Fin 4 → ℤ)
    (hh : h' ∈ centredCube (F.blockSide ^ (F.top - j))) :
    baseSite (cellCentre j y + siteOfCoords j h' : F.Site j) ∈ patchBaseSites S z := by
  classical
  set b : F.Site 0 := baseSite (cellCentre j y + siteOfCoords j h' : F.Site j) with hb
  have hoff := fun i => baseSite_sub_cellCentre_valMinAbs hamb hL z y hd hj h' hh i
  have hsm := fun i => two_mul_abs_scaled_offset_le hL hj h' hh i
  have hNo : Odd (GaugeMap.cellSideLength F) := by
    unfold GaugeMap.cellSideLength
    exact Odd.pow (by exact_mod_cast hL)
  obtain ⟨n2, hn2⟩ := hNo
  have hNd : (GaugeMap.cellSideLength F - 1) / 2 = n2 := by omega
  have hNpos : 0 < GaugeMap.cellSideLength F := by
    have : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hL.pos
    unfold GaugeMap.cellSideLength
    positivity
  have hc10 : ∀ i, |(y i - z i).valMinAbs| ≤ 10 := by
    intro i
    have h1 : ((y i - z i).valMinAbs).natAbs ≤ cellSupDist y z :=
      Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1.trans hd
  refine Finset.mem_image.2 ⟨GaugeMap.patchChart S z b, ?_, ?_⟩
  · have hsgn : ∀ i, ∀ u : ℤ, |closedOrthant S z i * u| = |u| := by
      intro i u
      rcases closedOrthant_eq_one_or_neg_one S z i with h | h <;> rw [h] <;> simp
    have hkey : ∀ i, closedOrthant S z i * (y i - z i).valMinAbs * GaugeMap.cellSideLength F ≤
          GaugeMap.patchChart S z b i ∧
        GaugeMap.patchChart S z b i ≤ closedOrthant S z i * (y i - z i).valMinAbs * GaugeMap.cellSideLength F +
          (GaugeMap.cellSideLength F - 1) := by
      intro i
      have e : GaugeMap.patchChart S z b i = closedOrthant S z i * (y i - z i).valMinAbs * GaugeMap.cellSideLength F +
          (closedOrthant S z i * ((F.blockSide : ℤ) ^ j * h' i) + n2) := by
        show closedOrthant S z i * ((b - cellCentre 0 z) i).valMinAbs + (GaugeMap.cellSideLength F - 1) / 2 = _
        rw [hoff i, hNd]
        ring
      have h1 := hsgn i ((F.blockSide : ℤ) ^ j * h' i)
      have h2 := hsm i
      rw [← h1] at h2
      have h3 := abs_le.1 (show |closedOrthant S z i * ((F.blockSide : ℤ) ^ j * h' i)| ≤ n2 by omega)
      rw [e]
      constructor <;> linarith [h3.1, h3.2]
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, ?_⟩
    · rw [Finset.mem_Icc]
      have h1 := hkey i
      have h2 : |closedOrthant S z i * (y i - z i).valMinAbs| ≤ 10 := by
        rw [hsgn]
        exact hc10 i
      have h3 := abs_le.1 h2
      have l1 := mul_le_mul_of_nonneg_right h3.1 hNpos.le
      have l2 := mul_le_mul_of_nonneg_right h3.2 hNpos.le
      constructor <;> linarith [h1.1, h1.2]
    · refine ⟨fun i => closedOrthant S z i * cellDisplacement z y i * GaugeMap.cellSideLength F, ?_,
        fun i => (hkey i).1⟩
      refine Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hy, ?_⟩, rfl⟩
      rw [cellSupDist_comm]
      exact hd
  · funext i
    have e1 : closedOrthant S z i * (GaugeMap.patchChart S z b i - (GaugeMap.cellSideLength F - 1) / 2) =
        ((b - cellCentre 0 z) i).valMinAbs := by
      show closedOrthant S z i * (closedOrthant S z i * ((b - cellCentre 0 z) i).valMinAbs +
        (GaugeMap.cellSideLength F - 1) / 2 - (GaugeMap.cellSideLength F - 1) / 2) = _
      rw [add_sub_cancel_right, ← mul_assoc, closedOrthant_mul_self, one_mul]
    show (cellCentre 0 z + siteOfCoords 0 (fun i => closedOrthant S z i *
      (GaugeMap.patchChart S z b i - (GaugeMap.cellSideLength F - 1) / 2)) : F.Site 0) i = b i
    rw [Pi.add_apply]
    simp only [siteOfCoords]
    rw [e1, ZMod.coe_valMinAbs]
    simp
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
def PathStaysIn {j : ℕ} (P : F.Site j → Prop) : F.Site j → List PathStep → Prop
  | x, [] => P x
  | x, st :: r => P x ∧ PathStaysIn P (x + stepDisplacement j st) r
theorem pathStaysIn_start {j : ℕ} {P : F.Site j → Prop} {x : F.Site j} {l : List PathStep}
    (h : PathStaysIn P x l) : P x := by
  cases l with
  | nil => exact h
  | cons st r => exact h.1
theorem pathStaysIn_append {j : ℕ} (P : F.Site j → Prop) (l₁ l₂ : List PathStep) : ∀ x : F.Site j,
    PathStaysIn P x l₁ → PathStaysIn P (x + pathDisplacement j l₁) l₂ → PathStaysIn P x (l₁ ++ l₂) := by
  induction l₁ with
  | nil =>
    intro x _ h
    simpa [pathDisplacement] using h
  | cons st r ih =>
    intro x h1 h2
    refine ⟨h1.1, ih _ h1.2 ?_⟩
    have e : x + stepDisplacement j st + pathDisplacement j r = x + pathDisplacement j (st :: r) := by
      simp [pathDisplacement, add_assoc]
    rwa [e]
theorem pathDisplacement_append (j : ℕ) (l₁ l₂ : List PathStep) :
    (pathDisplacement j (l₁ ++ l₂) : F.Site j) = pathDisplacement j l₁ + pathDisplacement j l₂ := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
def stepVector (st : PathStep) : Fin 4 → ℤ := if st.2 then Pi.single st.1 1 else - Pi.single st.1 1
theorem stepDisplacement_eq (j : ℕ) (st : PathStep) :
    (stepDisplacement j st : F.Site j) = siteOfCoords j (stepVector st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem pathStaysIn_replicate {j : ℕ} (P : (Fin 4 → ℤ) → Prop) (base : F.Site j) (st : PathStep) (n : ℕ) :
    ∀ o : Fin 4 → ℤ, (∀ r : ℕ, r ≤ n → P (o + (r : ℤ) • stepVector st)) →
    PathStaysIn (fun x : F.Site j => ∃ o', P o' ∧ x = base + siteOfCoords j o') (base + siteOfCoords j o)
        (List.replicate n st) ∧
      (pathDisplacement j (List.replicate n st) : F.Site j) = siteOfCoords j ((n : ℤ) • stepVector st) := by
  induction n with
  | zero =>
    intro o h
    refine ⟨⟨o, by simpa using h 0 le_rfl, rfl⟩, ?_⟩
    funext i
    simp [pathDisplacement, siteOfCoords]
  | succ n ih =>
    intro o h
    have h0 := h 0 (Nat.zero_le _)
    have hn := ih (o + stepVector st) (fun r hr => by
      have := h (r + 1) (by omega)
      have e : o + stepVector st + (r : ℤ) • stepVector st = o + ((r + 1 : ℕ) : ℤ) • stepVector st := by
        push_cast
        rw [add_smul, one_smul]
        abel
      rwa [e])
    have e1 : base + siteOfCoords j o + stepDisplacement j st = base + siteOfCoords j (o + stepVector st) := by
      rw [stepDisplacement_eq, siteOfCoords_add, add_assoc]
    refine ⟨⟨⟨o, by simpa using h0, rfl⟩, ?_⟩, ?_⟩
    · rw [e1]
      exact hn.1
    · have e2 : (pathDisplacement j (st :: List.replicate n st) : F.Site j) =
          stepDisplacement j st + pathDisplacement j (List.replicate n st) := by
        simp [pathDisplacement]
      rw [List.replicate_succ, e2, hn.2, stepDisplacement_eq, ← siteOfCoords_add]
      congr 1
      push_cast
      rw [add_smul, one_smul]
      abel
def axisSteps (h : Fin 4 → ℤ) (ds : List (Fin 4)) : List PathStep :=
  ds.flatMap fun d => List.replicate (h d).natAbs (d, decide (0 ≤ h d))
theorem natAbs_smul_stepVector (h : Fin 4 → ℤ) (d : Fin 4) :
    (((h d).natAbs : ℕ) : ℤ) • stepVector (d, decide (0 ≤ h d)) = Pi.single d (h d) := by
  funext i
  by_cases hi : i = d
  · subst hi
    by_cases h0 : 0 ≤ h i
    · simp [stepVector, h0, abs_of_nonneg h0]
    · simp [stepVector, h0, abs_of_neg (not_le.1 h0)]
  · by_cases h0 : 0 ≤ h d <;> simp [stepVector, h0, hi]
theorem pathStaysIn_axisSteps {j : ℕ} (m : ℤ) (base : F.Site j) (h : Fin 4 → ℤ) (hh : ∀ i, |h i| ≤ m)
    (ds : List (Fin 4)) :
    ds.Nodup → ∀ o : Fin 4 → ℤ, (∀ i, |o i| ≤ m) → (∀ d ∈ ds, o d = 0) →
    PathStaysIn (fun x : F.Site j => ∃ o', (∀ i, |o' i| ≤ m) ∧ x = base + siteOfCoords j o')
        (base + siteOfCoords j o) (axisSteps h ds) ∧
      (pathDisplacement j (axisSteps h ds) : F.Site j) = siteOfCoords j (fun i => if i ∈ ds then h i else 0) := by
  induction ds with
  | nil =>
    intro _ o ho _
    refine ⟨⟨o, ho, rfl⟩, ?_⟩
    funext i
    simp [axisSteps, pathDisplacement, siteOfCoords]
  | cons d ds ih =>
    intro hnd o ho hz
    have hd0 : o d = 0 := hz d (List.mem_cons_self)
    have hdn : d ∉ ds := (List.nodup_cons.1 hnd).1
    have hnd' : ds.Nodup := (List.nodup_cons.1 hnd).2
    have hline := pathStaysIn_replicate (F := F) (j := j) (fun o' => ∀ i, |o' i| ≤ m) base
      (d, decide (0 ≤ h d)) (h d).natAbs o (fun r hr i => by
        by_cases hi : i = d
        · subst hi
          have hstep : |(r : ℤ) • stepVector (i, decide (0 ≤ h i)) i| = r := by
            by_cases h0 : 0 ≤ h i <;> simp [stepVector, h0]
          have h1 : (r : ℤ) ≤ |h i| := by
            rw [Int.abs_eq_natAbs]
            exact_mod_cast hr
          have e : (o + (r : ℤ) • stepVector (i, decide (0 ≤ h i))) i =
              ((r : ℤ) • stepVector (i, decide (0 ≤ h i))) i := by
            simp [hd0]
          rw [e]
          have e2 : ((r : ℤ) • stepVector (i, decide (0 ≤ h i))) i =
              (r : ℤ) • stepVector (i, decide (0 ≤ h i)) i := rfl
          rw [e2, hstep]
          exact h1.trans (hh i)
        · have e : (o + (r : ℤ) • stepVector (d, decide (0 ≤ h d))) i = o i := by
            by_cases h0 : 0 ≤ h d <;> simp [stepVector, h0, hi]
          rw [e]
          exact ho i)
    set o' : Fin 4 → ℤ := o + Pi.single d (h d) with ho'
    have hoe : o + (((h d).natAbs : ℕ) : ℤ) • stepVector (d, decide (0 ≤ h d)) = o' := by
      rw [natAbs_smul_stepVector]
    have hbound : ∀ i, |o' i| ≤ m := by
      intro i
      by_cases hi : i = d
      · subst hi
        simp [ho', hd0, hh i]
      · simpa [ho', hi] using ho i
    have hzero : ∀ d' ∈ ds, o' d' = 0 := by
      intro d' hd'
      have hne : d' ≠ d := fun e => hdn (e ▸ hd')
      simp [ho', hne, hz d' (List.mem_cons_of_mem _ hd')]
    obtain ⟨s1, s2⟩ := ih hnd' o' hbound hzero
    have hsplit : axisSteps h (d :: ds) =
        List.replicate (h d).natAbs (d, decide (0 ≤ h d)) ++ axisSteps h ds := by
      simp [axisSteps]
    have hend : base + siteOfCoords j o + pathDisplacement j (List.replicate (h d).natAbs (d, decide (0 ≤ h d))) =
        base + siteOfCoords j o' := by
      rw [hline.2, natAbs_smul_stepVector, add_assoc, ← siteOfCoords_add]
    rw [hsplit]
    refine ⟨pathStaysIn_append _ _ _ _ hline.1 (by rw [hend]; exact s1), ?_⟩
    rw [pathDisplacement_append, hline.2, s2, ← siteOfCoords_add, natAbs_smul_stepVector]
    congr 1
    funext i
    by_cases hi : i = d
    · subst hi
      simp [hdn]
    · simp [hi]
theorem pathStaysIn_axisPath {j : ℕ} (m : ℤ) (hm : 0 ≤ m) (base : F.Site j) (h : Fin 4 → ℤ)
    (hh : ∀ i, |h i| ≤ m) (π : Equiv.Perm (Fin 4)) :
    PathStaysIn (fun x : F.Site j => ∃ o', (∀ i, |o' i| ≤ m) ∧ x = base + siteOfCoords j o') base
        (axisPath h π) ∧
      (pathDisplacement j (axisPath h π) : F.Site j) = siteOfCoords j h := by
  have hl : axisPath h π = axisSteps h ((List.finRange 4).map π) := by
    simp [axisPath, axisSteps, List.flatMap_map]
  have hnd : ((List.finRange 4).map π).Nodup := (List.nodup_finRange 4).map π.injective
  have hz : siteOfCoords j (0 : Fin 4 → ℤ) = (0 : F.Site j) := by
    funext i
    simp [siteOfCoords]
  have := pathStaysIn_axisSteps (F := F) m base h hh _ hnd (fun _ => 0) (fun i => by simpa using hm)
    (fun _ _ => rfl)
  have hz' : siteOfCoords j (fun _ : Fin 4 => (0 : ℤ)) = (0 : F.Site j) := hz
  rw [hz', add_zero] at this
  rw [hl]
  refine ⟨this.1, this.2.trans ?_⟩
  congr 1
  funext i
  have : i ∈ (List.finRange 4).map π := by
    refine List.mem_map.2 ⟨π.symm i, List.mem_finRange _, by simp⟩
  simp [this]
theorem pathHolonomy_congr {j : ℕ} (P : F.Site j → Prop) (X X' : F.GaugeField j)
    (hX : ∀ x i, P x → P (x + unitStep j i) → X x i = X' x i) (l : List PathStep) :
    ∀ x, PathStaysIn P x l → pathHolonomy X x l = pathHolonomy X' x l := by
  induction l with
  | nil =>
    intro x _
    rfl
  | cons st r ih =>
    intro x h
    simp only [pathHolonomy]
    rw [ih _ h.2]
    congr 1
    obtain ⟨i, b⟩ := st
    have h2 := pathStaysIn_start h.2
    cases b
    · simp only [stepDisplacement, Bool.false_eq_true, if_false] at h2
      simp only [linkValue, Bool.false_eq_true, if_false]
      have e : x + -unitStep j i = x - unitStep j i := by abel
      rw [e] at h2
      have h3 : P (x - unitStep j i + unitStep j i) := by
        rw [sub_add_cancel]
        exact h.1
      rw [hX _ i h2 h3]
    · simp only [stepDisplacement, if_true] at h2
      simp only [linkValue, if_true]
      exact hX _ i h.1 h2
theorem gauge_eq_along_path {j : ℕ} (P : F.Site j → Prop) (X W : F.GaugeField j)
    (γ₁ γ₂ : F.Site j → UnitQuaternion)
    (h1 : ∀ x i, P x → P (x + unitStep j i) → γ₁ x * X x i * (γ₁ (x + unitStep j i))⁻¹ = W x i)
    (h2 : ∀ x i, P x → P (x + unitStep j i) → γ₂ x * X x i * (γ₂ (x + unitStep j i))⁻¹ = W x i)
    (l : List PathStep) : ∀ x, PathStaysIn P x l → γ₁ x = γ₂ x →
      γ₁ (x + pathDisplacement j l) = γ₂ (x + pathDisplacement j l) := by
  induction l with
  | nil =>
    intro x _ h
    simpa [pathDisplacement] using h
  | cons st r ih =>
    intro x h hx
    have hs : x + pathDisplacement j (st :: r) = x + stepDisplacement j st + pathDisplacement j r := by
      simp [pathDisplacement, add_assoc]
    rw [hs]
    refine ih _ h.2 ?_
    obtain ⟨i, b⟩ := st
    have hp := pathStaysIn_start h.2
    cases b
    · simp only [stepDisplacement, Bool.false_eq_true, if_false] at hp ⊢
      have e : x + -unitStep j i = x - unitStep j i := by abel
      rw [e] at hp ⊢
      have hq : P (x - unitStep j i + unitStep j i) := by
        rw [sub_add_cancel]
        exact h.1
      have a1 := h1 _ i hp hq
      have a2 := h2 _ i hp hq
      rw [sub_add_cancel] at a1 a2
      rw [hx] at a1
      have := a1.trans a2.symm
      exact mul_right_cancel (mul_right_cancel this)
    · simp only [stepDisplacement, if_true] at hp ⊢
      have a1 := h1 _ i h.1 hp
      have a2 := h2 _ i h.1 hp
      rw [hx] at a1
      have := a1.trans a2.symm
      exact inv_injective (mul_left_cancel this)
theorem top_sub_depth (F : BlockFrame) : F.top - F.depth = 1 := by apply _root_.YangMills.Construction.GaugeFixing.top_sub_depth <;> assumption
theorem cellCentre_top (z : F.Cell) : (cellCentre F.top z : F.Cell) = z := by apply _root_.YangMills.Construction.BlockAverages.cellCentre_top <;> assumption
theorem refineSite_eq_cellCentre (y : F.Cell) : (refineSite (j := F.depth) y : F.Site F.depth) = cellCentre F.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
theorem mem_centredCube_of_abs_le {o : Fin 4 → ℤ} (ho : ∀ i, |o i| ≤ ((F.blockSide : ℤ) - 1) / 2) :
    o ∈ centredCube (F.blockSide ^ (F.top - F.depth)) := by
  refine Fintype.mem_piFinset.2 fun i => ?_
  rw [top_sub_depth, pow_one, Finset.mem_Icc]
  exact abs_le.1 (ho i)
theorem abs_le_of_mem_centredCube {o : Fin 4 → ℤ} (ho : o ∈ centredCube (F.blockSide ^ (F.top - F.depth)))
    (i : Fin 4) : |o i| ≤ ((F.blockSide : ℤ) - 1) / 2 := by
  have h := Fintype.mem_piFinset.1 ho i
  rw [top_sub_depth, pow_one, Finset.mem_Icc] at h
  exact abs_le.2 h
theorem card_centredCube (M : ℕ) (hM : Odd M) : (centredCube M).card = M ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem polarUnit_one : polarUnit (1 : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartFits.polarUnit_one <;> assumption
theorem balancingGauge_eq_one_of_holonomy_eq {j : ℕ} (hL : Odd F.blockSide) (X R : F.GaugeField j)
    (y : F.Site (j + 1))
    (h : ∀ o ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      pathHolonomy X (refineSite y) (axisPath o π) = pathHolonomy R (refineSite y) (axisPath o π)) :
    balancingGauge X R y = 1 := by
  have hLpos : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hL.pos
  have hs : ∑ o ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy X (refineSite y) (axisPath o π) * (pathHolonomy R (refineSite y) (axisPath o π))⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) =
      (24 * (F.blockSide : ℝ) ^ 4) • (1 : ℍ[ℝ]) := by
    have e : ∀ o ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy X (refineSite y) (axisPath o π) * (pathHolonomy R (refineSite y) (axisPath o π))⁻¹ :
          UnitQuaternion) : ℍ[ℝ]) =
        (24 : ℝ) • (1 : ℍ[ℝ]) := by
      intro o ho
      have e2 : ∀ π : Equiv.Perm (Fin 4),
          ((pathHolonomy X (refineSite y) (axisPath o π) * (pathHolonomy R (refineSite y) (axisPath o π))⁻¹ :
            UnitQuaternion) : ℍ[ℝ]) = 1 := by
        intro π
        rw [h o ho π, mul_inv_cancel]
        rfl
      simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      rw [show Nat.factorial 4 = 24 from rfl, ← Nat.cast_smul_eq_nsmul ℝ]
      norm_num
    rw [Finset.sum_congr rfl e, Finset.sum_const, card_centredCube _ hL, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    push_cast
    ring
  unfold balancingGauge relativePathAverage
  rw [hs, smul_smul]
  have e3 : 1 / (24 * (F.blockSide : ℝ) ^ 4) * (24 * (F.blockSide : ℝ) ^ 4) = 1 := by
    field_simp
  rw [e3, one_smul, polarUnit_one, inv_one]
theorem eq_of_norm_mul_inv_sub_one_eq_zero {g w : UnitQuaternion}
    (h : ‖((g * w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = 0) : g = w := by
  have h1 : ((g * w⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := sub_eq_zero.1 (norm_eq_zero.1 h)
  have h2 : g * w⁻¹ = 1 := Subtype.ext h1
  exact mul_inv_eq_one.1 h2
theorem gaugedChainFields_eq_on_patch (a C : ℝ) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain)
    (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge) (hP : IsPinnedGauge a C S z W kW X k Γ)
    (hE : relativeEnergy a S z W kW X k Γ = 0)
    (b : F.Site F.depth × Fin 4) (hb : b ∈ innerBonds S F.depth) (h1 : baseSite b.1 ∈ patchBaseSites S z)
    (h2 : baseSite (b.1 + unitStep F.depth b.2) ∈ patchBaseSites S z) :
    gaugedChainFields X Γ F.depth b.1 b.2 = W F.depth b.1 b.2 := by
  classical
  obtain ⟨-, -, hrel, -⟩ := hP
  have h3 := hrel F.depth (by show F.depth < F.depth + 1; omega)
  rw [hE, Real.sqrt_zero, mul_zero] at h3
  have h4 : ∑ b ∈ innerBonds S F.depth, (if baseSite b.1 ∈ patchBaseSites S z ∧
      baseSite (b.1 + unitStep F.depth b.2) ∈ patchBaseSites S z then
        ‖((gaugedChainFields X Γ F.depth b.1 b.2 * (W F.depth b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4
      else 0) = 0 := by
    refine le_antisymm (by simpa using h3) (Finset.sum_nonneg fun c _ => ?_)
    split_ifs <;> positivity
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => by split_ifs <;> positivity)).1 h4 b hb
  rw [if_pos ⟨h1, h2⟩] at h5
  exact eq_of_norm_mul_inv_sub_one_eq_zero (pow_eq_zero_iff (by norm_num) |>.1 h5)
theorem gauge_refineSite_eq_inv (a C : ℝ) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain)
    (kW : F.SiteGauge) (X : F.FieldChain) (Γ : F.SiteGauge) (hL : Odd F.blockSide)
    (hP : IsPinnedGauge a C S z W kW X (fun _ _ => 1) Γ)
    (hE : relativeEnergy a S z W kW X (fun _ _ => 1) Γ = 0) (y : F.Cell) (hy : baseSite y ∈ patchBaseSites S z)
    (hleg : ∀ o ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      pathHolonomy (gaugedChainFields X Γ F.depth) (refineSite y) (axisPath o π) =
        pathHolonomy (W F.depth) (refineSite y) (axisPath o π)) :
    Γ F.depth (refineSite y) = (kW F.top y)⁻¹ := by
  obtain ⟨hn, -, -, htop⟩ := hP
  have h1 := htop y hy
  rw [hE, Real.sqrt_zero, mul_zero] at h1
  have h2 : ‖((topCorrection W kW X (fun _ _ => 1) Γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ = 0 :=
    le_antisymm h1 (norm_nonneg _)
  have h3 : topCorrection W kW X (fun _ _ => 1) Γ y = 1 :=
    Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 h2))
  have h4 : balancingGauge (gaugedChainFields X Γ F.depth) (W F.depth) y = 1 :=
    balancingGauge_eq_one_of_holonomy_eq hL _ _ y hleg
  unfold topCorrection balancedLinkAgainst gaugedLink at h3
  rw [h4, mul_one] at h3
  have h5 : Γ (F.depth + 1) y = 1 := hn y
  rw [h5, one_mul, one_mul, inv_inv] at h3
  exact eq_inv_of_mul_eq_one_right h3
theorem cellSupDist_enclosingCell_neighbour_le (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (x : F.Site F.depth) (i : Fin 4) (o o' : Fin 4 → ℤ) (z z' : F.Cell)
    (hx : x = cellCentre F.depth z + siteOfCoords F.depth o)
    (hx' : x + unitStep F.depth i = cellCentre F.depth z' + siteOfCoords F.depth o')
    (ho : ∀ l, |o l| ≤ ((F.blockSide : ℤ) - 1) / 2) (ho' : ∀ l, |o' l| ≤ ((F.blockSide : ℤ) - 1) / 2) :
    cellSupDist z' z ≤ 10 := by
  refine Finset.sup_le fun l _ => ?_
  set Lz : ℤ := (F.blockSide : ℤ) with hLz
  have hLpos : 0 < Lz := by
    rw [hLz]
    exact_mod_cast hL.pos
  obtain ⟨w, hw⟩ : Odd Lz := by
    rw [hLz]
    exact_mod_cast hL
  have hmd : (Lz - 1) / 2 = w := by omega
  have h1 := abs_le.1 (ho l)
  have h2 := abs_le.1 (ho' l)
  rw [hmd] at h1 h2
  set δ : ℤ := (Pi.single i 1 : Fin 4 → ℤ) l with hδ
  have hδb : 0 ≤ δ ∧ δ ≤ 1 := by
    rw [hδ]
    by_cases hi : l = i
    · subst hi
      simp
    · simp [hi]
  set cz : ℤ := siteCoords z l with hcz
  set cz' : ℤ := siteCoords z' l with hcz'
  have hc : ((Lz * cz + o l + δ : ℤ) : ZMod (F.period F.depth l)) =
      ((Lz * cz' + o' l : ℤ) : ZMod (F.period F.depth l)) := by
    have e := congrFun hx' l
    rw [hx] at e
    simpa [cellCentre, siteOfCoords, unitStep, top_sub_depth, hLz, hcz, hcz', hδ] using e
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hc
  rw [period_cast, top_sub_depth, pow_one, ← hLz] at he
  set u : ℤ := cz' - cz - (F.extent l : ℤ) * e with hu
  have hub : |u| ≤ 1 := by
    rw [abs_le]
    constructor
    · by_contra hno
      have : u ≤ -2 := by omega
      nlinarith [hδb.1, hδb.2, h1.1, h1.2, h2.1, h2.2]
    · by_contra hno
      have : 2 ≤ u := by omega
      nlinarith [hδb.1, hδb.2, h1.1, h1.2, h2.1, h2.2]
  have hper : ((F.period F.top l : ℕ) : ℤ) = (F.extent l : ℤ) := by simp [BlockFrame.period]
  have hcast : ((u : ℤ) : ZMod (F.period F.top l)) = z' l - z l := by
    have hs : ((((F.extent l : ℤ) * e : ℤ)) : ZMod (F.period F.top l)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hper]
      exact dvd_mul_right _ _
    rw [hu, Int.cast_sub, hs, sub_zero, Int.cast_sub, hcz, hcz', intCast_siteCoords, intCast_siteCoords]
  have hnn : F.period F.top l = 0 ∨ 64 ≤ F.period F.top l := by
    rcases hamb with h0 | h64
    · left
      simp [BlockFrame.period, h0 l]
    · right
      have := h64 l
      simpa [BlockFrame.period] using this
  have hs : F.period F.top l = 0 ∨ 2 * |u| < ((F.period F.top l : ℕ) : ℤ) := by
    rcases hnn with h | h
    · exact Or.inl h
    · right
      have : (64 : ℤ) ≤ ((F.period F.top l : ℕ) : ℤ) := by exact_mod_cast h
      linarith
  have hv := valMinAbs_eq_of_small _ hnn _ _ hcast hs
  show ((z' l - z l).valMinAbs).natAbs ≤ 10
  rw [hv]
  have : u.natAbs ≤ 1 := by
    have := Int.abs_eq_natAbs u
    omega
  omega
theorem zero_mem_centredCube (M : ℕ) (hM : 0 < M) : (0 : Fin 4 → ℤ) ∈ centredCube M := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.zero_mem_centredCube <;> assumption
theorem siteOfCoords_zero (j : ℕ) : (siteOfCoords j (0 : Fin 4 → ℤ) : F.Site j) = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem enclosingCell_cellCentre (hL : Odd F.blockSide) (j : ℕ) (z : F.Cell) :
    enclosingCell (cellCentre j z : F.Site j) = z := by
  have h := enclosingCell_cellCentre_add hL (j := j) z 0 (zero_mem_centredCube _ (Nat.pow_pos hL.pos))
  rwa [siteOfCoords_zero, add_zero] at h
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem zeroEnergyFramingsAgree : zeroEnergyFramingsAgreeStatement := by
  classical
  intro a θ del Ca ha hθ hθ8 hd hd8 hCa
  refine ⟨0, fun L hL _ C₁ C hC₁ hC => ⟨1, one_pos, ?_⟩⟩
  intro F m S hFL hamb hm hreg s V hs hsσ hcold U hU X Γ hXn hP hE
  have hLF : Odd F.blockSide := hFL ▸ hL
  set R := referenceFieldChain S V with hR
  set W := chartChain R U V with hW
  set kW := chartGauge R U with hkW
  have hWt : W F.depth = chartField R U F.depth := by
    rw [hW]
    unfold chartChain
    exact Function.update_of_ne (by show F.depth ≠ F.depth + 1; omega) _ _
  set mm : ℤ := ((F.blockSide : ℤ) - 1) / 2 with hmm
  have hmm0 : 0 ≤ mm := by
    have : (1 : ℤ) ≤ (F.blockSide : ℤ) := by exact_mod_cast hLF.pos
    omega
  let Bk : F.Cell → F.Site F.depth → Prop := fun y x =>
    ∃ o : Fin 4 → ℤ, (∀ i, |o i| ≤ mm) ∧ x = refineSite (j := F.depth) y + siteOfCoords F.depth o
  have hBkS : ∀ y ∈ S, ∀ x, Bk y x → x ∈ sitesOfCells S F.depth := by
    intro y hy x ⟨o, ho, hx⟩
    refine Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_image.2 ⟨o, mem_centredCube_of_abs_le ho, ?_⟩⟩
    rw [hx, refineSite_eq_cellCentre]
  have hBkP : ∀ y ∈ S, ∀ z, cellSupDist y z ≤ 10 → ∀ x, Bk y x → baseSite x ∈ patchBaseSites S z := by
    intro y hy z hdz x ⟨o, ho, hx⟩
    rw [hx, refineSite_eq_cellCentre]
    exact baseSite_mem_patchBaseSites hamb hLF hy hdz (by show F.depth ≤ F.depth + 1; omega) o
      (mem_centredCube_of_abs_le ho)
  have hbondS : ∀ y ∈ S, ∀ x i, Bk y x → Bk y (x + unitStep F.depth i) → (x, i) ∈ innerBonds S F.depth := by
    intro y hy x i h1 h2
    simp [innerBonds, hBkS y hy x h1, hBkS y hy _ h2]
  have hturn : ∀ y ∈ S, ∀ z ∈ S, cellSupDist y z ≤ 10 → ∀ x i, Bk y x → Bk y (x + unitStep F.depth i) →
      gaugedChainFields X (Γ z) F.depth x i = W F.depth x i := by
    intro y hy z hz hdz x i h1 h2
    exact gaugedChainFields_eq_on_patch a C S z W kW X _ (Γ z) (hP z hz) (hE z hz) (x, i)
      (hbondS y hy x i h1 h2) (hBkP y hy z hdz x h1) (hBkP y hy z hdz _ h2)
  have hcube : ∀ o ∈ centredCube F.blockSide, ∀ i, |o i| ≤ mm := by
    intro o ho i
    have := Fintype.mem_piFinset.1 ho i
    rw [Finset.mem_Icc] at this
    exact abs_le.2 this
  have hcent : ∀ y ∈ S, ∀ z ∈ S, cellSupDist y z ≤ 10 →
      Γ z F.depth (refineSite (j := F.depth) y) = (kW F.top y)⁻¹ := by
    intro y hy z hz hdz
    refine gauge_refineSite_eq_inv a C S z W kW X (Γ z) hLF (hP z hz) (hE z hz) y ?_ ?_
    · have h0 := baseSite_mem_patchBaseSites hamb hLF hy hdz (j := F.top) le_rfl 0
        (zero_mem_centredCube _ (Nat.pow_pos hLF.pos))
      rwa [siteOfCoords_zero, add_zero, cellCentre_top] at h0
    · intro o ho π
      refine pathHolonomy_congr (Bk y) _ _ (fun x i h1 h2 => hturn y hy z hz hdz x i h1 h2) _ _ ?_
      exact (pathStaysIn_axisPath mm hmm0 (refineSite (j := F.depth) y) o (hcube o ho) π).1
  have hagree : ∀ y ∈ S, ∀ z ∈ S, ∀ z' ∈ S, cellSupDist y z ≤ 10 → cellSupDist y z' ≤ 10 → ∀ x, Bk y x →
      Γ z F.depth x = Γ z' F.depth x := by
    intro y hy z hz z' hz' h1 h2 x ⟨o, ho, hx⟩
    have st := pathStaysIn_axisPath mm hmm0 (refineSite (j := F.depth) y) o ho 1
    have := gauge_eq_along_path (Bk y) (X F.depth) (W F.depth) (Γ z F.depth) (Γ z' F.depth)
      (fun x i a b => hturn y hy z hz h1 x i a b) (fun x i a b => hturn y hy z' hz' h2 x i a b)
      (axisPath o 1) (refineSite (j := F.depth) y) st.1 (by rw [hcent y hy z hz h1, hcent y hy z' hz' h2])
    rwa [st.2, ← hx] at this
  have hsite : ∀ x ∈ sitesOfCells S F.depth, enclosingCell x ∈ S ∧ Bk (enclosingCell x) x ∧
      ∃ o, (∀ i, |o i| ≤ mm) ∧ x = cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth o := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.1 hxz
    have hc := enclosingCell_cellCentre_add hLF z o ho
    rw [hc]
    have ho' := abs_le_of_mem_centredCube ho
    exact ⟨hz, ⟨o, ho', by rw [refineSite_eq_cellCentre]⟩, o, ho', rfl⟩
  refine ⟨fun x => (Γ (enclosingCell x) F.depth x)⁻¹, fun z hz => ?_, fun b hb => ?_⟩
  · have h1 := hcent z hz z hz (by rw [cellSupDist_self]; omega)
    rw [refineSite_eq_cellCentre] at h1
    simp only [enclosingCell_cellCentre hLF, h1, inv_inv]
  · have s1 : b.1 ∈ sitesOfCells S F.depth := (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
    have s2 : b.1 + unitStep F.depth b.2 ∈ sitesOfCells S F.depth := (Finset.mem_filter.1 hb).2
    obtain ⟨z1, B1, o1, ho1, hx1⟩ := hsite _ s1
    obtain ⟨z2, B2, o2, ho2, hx2⟩ := hsite _ s2
    have hdist : cellSupDist (enclosingCell (b.1 + unitStep F.depth b.2)) (enclosingCell b.1) ≤ 10 :=
      cellSupDist_enclosingCell_neighbour_le hamb hLF b.1 b.2 o1 o2 _ _ hx1 hx2 ho1 ho2
    have hself : ∀ z : F.Cell, cellSupDist z z ≤ 10 := fun z => by rw [cellSupDist_self]; omega
    have h1 := gaugedChainFields_eq_on_patch a C S (enclosingCell b.1) W kW X _ (Γ (enclosingCell b.1))
      (hP _ z1) (hE _ z1) b hb (hBkP _ z1 _ (hself _) _ B1) (hBkP _ z2 _ hdist _ B2)
    have h2 := hagree _ z2 _ z1 _ z2 hdist (hself _) _ B2
    unfold gaugedChainFields gaugeTransform at h1
    show X F.depth b.1 b.2 = gaugeTransform _ (chartField R U F.depth) b.1 b.2
    unfold gaugeTransform
    rw [← hWt, ← h1, inv_inv, ← h2]
    group
end YangMills.Construction.BlockAverages.ZeroEnergyFramings
end
