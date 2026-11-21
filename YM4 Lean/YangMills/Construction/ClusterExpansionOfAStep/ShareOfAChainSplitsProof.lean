import YangMills.Construction.ClusterExpansionOfAStep.AdmissionEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfAChainSplits
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.TorusFrame
open YangMills.Construction.StepCosts YangMills.Construction.TopLevelSites
namespace YangMills.Construction.ClusterExpansionOfAStep
namespace LevelShare
section Cells
variable {F : BlockFrame}
theorem half_pred_odd {M : ℕ} (k : ℕ) (hk : M = 2 * k + 1) : ((M : ℤ) - 1) / 2 = k := by
  subst hk
  push_cast
  omega
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (z : F.Cell)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by
  funext i
  obtain ⟨k, hk⟩ : Odd (F.blockSide ^ (F.top - j)) := hL.pow
  have hk2 := half_pred_odd k hk
  have hper1 : F.period F.top i = F.extent i := by simp [BlockFrame.period]
  have hper0 : F.period j i = F.extent i * F.blockSide ^ (F.top - j) := rfl
  have hMpos : 0 < F.blockSide ^ (F.top - j) := by omega
  have : NeZero (F.period F.top i) := ⟨by rw [hper1]; exact (hs i).ne'⟩
  have : NeZero (F.period j i) := ⟨by rw [hper0]; exact (Nat.mul_pos (hs i) hMpos).ne'⟩
  have hh' := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hh i)
  rw [hk2] at hh'
  have hcast : (cellCentre j z + siteOfCoords j h : F.Site j) i =
      (((F.blockSide : ℤ) ^ (F.top - j) * siteCoords z i + h i : ℤ) : ZMod (F.period j i)) := by
    simp only [cellCentre, siteOfCoords, Pi.add_apply]
    push_cast
    rfl
  set w : ℤ := (F.blockSide : ℤ) ^ (F.top - j) * siteCoords z i + h i with hw
  set M : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hM
  have hMz : M = ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) := by simp [hM]
  have hMpos' : 0 < M := by rw [hMz]; exact_mod_cast hMpos
  have hval : siteCoords (cellCentre j z + siteOfCoords j h : F.Site j) i = w % ((F.extent i : ℤ) * M) := by
    unfold siteCoords
    rw [hcast, ZMod.coe_intCast, hper0]
    push_cast
    rw [hM]
  change (((siteCoords (cellCentre j z + siteOfCoords j h : F.Site j) i + (M - 1) / 2) / M : ℤ) :
    ZMod (F.period F.top i)) = z i
  have hb : (M - 1) / 2 = k := by rw [hMz]; exact hk2
  rw [hval, hb]
  set P : ℤ := (F.extent i : ℤ) * M with hP
  have e1 : w % P = w - P * (w / P) := by
    have := Int.emod_add_mul_ediv w P
    linarith
  have e2 : w - P * (w / P) + k = (h i + k) + M * (siteCoords z i - (F.extent i : ℤ) * (w / P)) := by
    rw [hw, hP]
    ring
  rw [e1, e2, Int.add_mul_ediv_left _ _ hMpos'.ne']
  have e3 : (h i + k) / M = 0 := by
    apply Int.ediv_eq_zero_of_lt (by linarith [hh'.1])
    have : M = 2 * k + 1 := by rw [hMz, hk]; push_cast; ring
    linarith [hh'.2]
  rw [e3, zero_add]
  have hz : ((F.extent i : ℕ) : ZMod (F.period F.top i)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (by rw [hper1])
  push_cast
  rw [hz, zero_mul, sub_zero]
  exact ZMod.intCast_zmod_cast (z i)
theorem exists_cellCentre_add (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (j : ℕ) (hj : j ≤ F.top)
    (x : F.Site j) :
    ∃ (z : F.Cell) (h : Fin 4 → ℤ), h ∈ centredCube (F.blockSide ^ (F.top - j)) ∧
      cellCentre j z + siteOfCoords j h = x := by
  obtain ⟨k, hk⟩ : Odd (F.blockSide ^ (F.top - j)) := hL.pow
  have hk2 := half_pred_odd k hk
  set M := F.blockSide ^ (F.top - j) with hM
  have hMpos : 0 < M := by omega
  have hper1 : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
  have hper0 : ∀ i, F.period j i = F.extent i * M := fun i => rfl
  have hne1 : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [hper1]; exact (hs i).ne'⟩
  have hne0 : ∀ i, NeZero (F.period j i) := fun i =>
    ⟨by rw [hper0]; exact (Nat.mul_pos (hs i) hMpos).ne'⟩
  set c : Fin 4 → ℤ := siteCoords x with hc
  set q : Fin 4 → ℤ := fun i => (c i + k) / (M : ℤ) with hq
  set h : Fin 4 → ℤ := fun i => c i - (M : ℤ) * q i with hh
  have hMz : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hMpos
  refine ⟨siteOfCoords F.top q, h, ?_, ?_⟩
  · unfold centredCube
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc, hk2]
    have e1 := Int.emod_add_mul_ediv (c i + k) (M : ℤ)
    have e2 := Int.emod_nonneg (c i + k) hMz.ne'
    have e3 := Int.emod_lt_of_pos (c i + k) hMz
    simp only [hh, hq]
    constructor <;> nlinarith
  · funext i
    have := hne1 i
    have := hne0 i
    have e0 : (cellCentre j (siteOfCoords F.top q : F.Cell) : F.Site j) i =
        (((M : ℤ) * siteCoords (siteOfCoords F.top q : F.Cell) i : ℤ) : ZMod (F.period j i)) := by
      simp only [cellCentre, siteOfCoords, hM]
      push_cast
      rfl
    rw [Pi.add_apply, e0]
    have e1 : (((M : ℤ) * siteCoords (siteOfCoords F.top q : F.Cell) i : ℤ) : ZMod (F.period j i)) =
        (((M : ℤ) * q i : ℤ) : ZMod (F.period j i)) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      have e2 := Int.emod_add_mul_ediv (q i) (F.period F.top i : ℤ)
      refine ⟨q i / (F.period F.top i : ℤ), ?_⟩
      have e3 : siteCoords (siteOfCoords F.top q : F.Cell) i = q i % (F.period F.top i : ℤ) := by
        show ZMod.cast ((q i : ZMod (F.period F.top i))) = _
        rw [ZMod.coe_intCast]
      rw [e3, hper0]
      rw [hper1] at e2 ⊢
      push_cast
      linear_combination (-(M : ℤ)) * e2
    rw [e1]
    show (((M : ℤ) * q i : ℤ) : ZMod (F.period j i)) + ((h i : ℤ) : ZMod (F.period j i)) = x i
    rw [← Int.cast_add]
    have e3 : (M : ℤ) * q i + h i = c i := by
      simp only [hh]
      ring
    rw [e3]
    simp only [hc, siteCoords]
    exact ZMod.intCast_zmod_cast (x i)
theorem mem_sitesOfCells_iff (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j ≤ F.top)
    (S : Finset F.Cell) (x : F.Site j) : x ∈ sitesOfCells S j ↔ enclosingCell x ∈ S := by
  constructor
  · intro hx
    obtain ⟨z, hz, hx'⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx'
    rw [enclosingCell_cellCentre_add hL hs z h hh]
    exact hz
  · intro hx
    obtain ⟨z, h, hh, rfl⟩ := exists_cellCentre_add hL hs j hj x
    rw [enclosingCell_cellCentre_add hL hs z h hh] at hx
    exact Finset.mem_biUnion.2 ⟨z, hx, Finset.mem_image.2 ⟨h, hh, rfl⟩⟩
theorem ediv_ediv_round {L M : ℤ} {a b : ℤ} (hL : L = 2 * a + 1) (hM : M = 2 * b + 1) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (c : ℤ) : ((c + b) / M + a) / L = (c + (b + M * a)) / (M * L) := by
  have hMpos : 0 < M := by omega
  have e : (c + b) / M + a = (c + (b + M * a)) / M := by
    have : c + (b + M * a) = (c + b) + a * M := by ring
    rw [this, Int.add_mul_ediv_right _ _ hMpos.ne']
  rw [e]
  exact Int.ediv_ediv_of_nonneg hMpos.le
end Cells
section Block
variable {L t n : ℕ}
theorem parentBlock_ancestorSite [NeZero n] [NeZero L] (hL : Odd L) {j : ℕ} (hj : j ≤ t)
    (x : (torusFrame L t n).Site j) :
    parentBlock L (toTorusSite (n * L) (ancestorSite (F := torusFrame L t n) t x)) =
      siteOfCell (enclosingCell x) := by
  funext i
  obtain ⟨b, hb⟩ : Odd (L ^ (t - j)) := hL.pow
  obtain ⟨a, ha⟩ := hL
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hL0 : 0 < L := by omega
  have hperT : (torusFrame L t n).period t i = n * L := by
    show n * L ^ (t + 1 - t) = n * L
    simp
  have hperN : (torusFrame L t n).period (torusFrame L t n).top i = n := by
    show n * L ^ (t + 1 - (t + 1)) = n
    simp
  have : NeZero ((torusFrame L t n).period t i) := ⟨by rw [hperT]; exact (Nat.mul_pos hn0 hL0).ne'⟩
  have : NeZero ((torusFrame L t n).period (torusFrame L t n).top i) := ⟨by rw [hperN]; exact hn0.ne'⟩
  set c : ℤ := siteCoords x i with hc
  set M : ℤ := (L : ℤ) ^ (t - j) with hM
  have hMz : M = 2 * b + 1 := by rw [hM]; exact_mod_cast hb
  have hLz : (L : ℤ) = 2 * a + 1 := by exact_mod_cast ha
  have hhalfM : (M - 1) / 2 = b := by rw [hMz]; omega
  have hhalfL : ((L : ℤ) - 1) / 2 = a := by rw [hLz]; omega
  set u : ℤ := (c + b) / M with hu
  have hpow : (L : ℤ) ^ (t + 1 - j) = M * L := by
    rw [hM, ← pow_succ]
    congr 1
    omega
  have hhalfN : ((L : ℤ) ^ (t + 1 - j) - 1) / 2 = b + M * a := by
    rw [hpow, hMz, hLz]
    have : (2 * (b : ℤ) + 1) * (2 * a + 1) - 1 = 2 * (b + (2 * b + 1) * a) := by ring
    rw [this]
    omega
  set v : ℤ := (c + (b + M * a)) / (M * L) with hv
  have hvu : (u + a) / (L : ℤ) = v := by
    rw [hu, hv]
    exact ediv_ediv_round hLz hMz (by positivity) (by positivity) c
  have e1 : (ancestorSite (F := torusFrame L t n) t x) i =
      ((u : ℤ) : ZMod ((torusFrame L t n).period t i)) := by
    show ((((c + ((L : ℤ) ^ (t - j) - 1) / 2) / (L : ℤ) ^ (t - j)) : ℤ) :
      ZMod ((torusFrame L t n).period t i)) = _
    rw [← hM, hhalfM]
  have e2 : toTorusSite (n * L) (ancestorSite (F := torusFrame L t n) t x) i = (u : ZMod (n * L)) := by
    show ((siteCoords (ancestorSite (F := torusFrame L t n) t x) i : ℤ) : ZMod (n * L)) = _
    unfold siteCoords
    rw [e1, ZMod.coe_intCast, hperT, ZMod.intCast_mod]
  have e3 : (enclosingCell x : (torusFrame L t n).Cell) i =
      ((v : ℤ) : ZMod ((torusFrame L t n).period (torusFrame L t n).top i)) := by
    show ((((c + ((L : ℤ) ^ (t + 1 - j) - 1) / 2) / (L : ℤ) ^ (t + 1 - j)) : ℤ) :
      ZMod ((torusFrame L t n).period (torusFrame L t n).top i)) = _
    rw [hhalfN, hpow]
  have e4 : siteOfCell (enclosingCell x : (torusFrame L t n).Cell) i = (v : ZMod n) := by
    show ((siteCoords (enclosingCell x : (torusFrame L t n).Cell) i : ℤ) : ZMod n) = _
    unfold siteCoords
    rw [e3, ZMod.coe_intCast, hperN, ZMod.intCast_mod]
  rw [e4]
  show ((((((toTorusSite (n * L) (ancestorSite (F := torusFrame L t n) t x)) i).cast : ℤ) +
    ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) = _
  rw [e2, ZMod.coe_intCast, hhalfL]
  have hNL : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL0
  set P : ℤ := ((n * L : ℕ) : ℤ) with hP
  have hPe : P = (n : ℤ) * L := by simp [hP]
  have e5 : u % P = u - P * (u / P) := by
    have := Int.emod_add_mul_ediv u P
    linarith
  have e6 : u - P * (u / P) + a = (u + a) + (L : ℤ) * (- (n : ℤ) * (u / P)) := by
    rw [hPe]
    ring
  rw [e5, e6, Int.add_mul_ediv_left _ _ hNL.ne', hvu]
  push_cast
  simp
end Block
section Carry
theorem cast_cast_int_of_eq (P Q : ℕ) (h : P = Q) (a : ZMod P) :
    ((((a.cast : ℤ) : ZMod Q)).cast : ℤ) = (a.cast : ℤ) := by apply _root_.YangMills.Construction.FrameTorusAction.cast_intCast_cast <;> assumption
theorem cast_cast_of_eq (P Q : ℕ) (h : P = Q) (a : ZMod P) :
    (((((a.cast : ℤ) : ZMod Q)).cast : ℤ) : ZMod P) = a := by
  subst h; simp
theorem cast_intCast_of_eq (P Q : ℕ) (h : P = Q) (z : ℤ) :
    ((((z : ZMod P)).cast : ℤ) : ZMod Q) = (z : ZMod Q) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
theorem cast_add_of_eq (P Q : ℕ) (h : P = Q) (a b : ZMod P) :
    (((a + b).cast : ℤ) : ZMod Q) = ((a.cast : ℤ) : ZMod Q) + ((b.cast : ℤ) : ZMod Q) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_add <;> assumption
variable (L k n : ℕ)
abbrev lowerFrame : BlockFrame := torusFrame L (k + 1) n
abbrev upperFrame : BlockFrame := torusFrame L k (n * L)
variable {L k n}
theorem period_upper_eq {j : ℕ} (hj : j ≤ k + 1) (i : Fin 4) :
    (upperFrame L k n).period j i = (lowerFrame L k n).period j i := by
  have h : (k + 1 + 1 - j) = (k + 1 - j) + 1 := by omega
  show n * L * L ^ (k + 1 - j) = n * L ^ (k + 1 + 1 - j)
  rw [h, pow_succ]
  ring
def toLower (j : ℕ) (x : (upperFrame L k n).Site j) : (lowerFrame L k n).Site j :=
  siteOfCoords j (siteCoords x)
def toUpper (j : ℕ) (x : (lowerFrame L k n).Site j) : (upperFrame L k n).Site j :=
  siteOfCoords j (siteCoords x)
theorem toLower_toUpper {j : ℕ} (hj : j ≤ k + 1) (x : (lowerFrame L k n).Site j) :
    toLower j (toUpper j x) = x := by
  funext i
  exact cast_cast_of_eq _ _ (period_upper_eq hj i).symm (x i)
theorem toUpper_toLower {j : ℕ} (hj : j ≤ k + 1) (x : (upperFrame L k n).Site j) :
    toUpper j (toLower j x) = x := by
  funext i
  exact cast_cast_of_eq _ _ (period_upper_eq hj i) (x i)
theorem siteCoords_toLower {j : ℕ} (hj : j ≤ k + 1) (x : (upperFrame L k n).Site j) :
    siteCoords (toLower j x) = siteCoords x := by
  funext i
  exact cast_cast_int_of_eq _ _ (period_upper_eq hj i) (x i)
theorem siteCoords_toUpper {j : ℕ} (hj : j ≤ k + 1) (x : (lowerFrame L k n).Site j) :
    siteCoords (toUpper j x) = siteCoords x := by
  funext i
  exact cast_cast_int_of_eq _ _ (period_upper_eq hj i).symm (x i)
theorem toLower_add {j : ℕ} (hj : j ≤ k + 1) (x y : (upperFrame L k n).Site j) :
    toLower j (x + y) = toLower j x + toLower j y := by
  funext i
  exact cast_add_of_eq _ _ (period_upper_eq hj i) (x i) (y i)
theorem toLower_siteOfCoords {j : ℕ} (hj : j ≤ k + 1) (z : Fin 4 → ℤ) :
    toLower j (siteOfCoords (F := upperFrame L k n) j z) = siteOfCoords j z := by
  funext i
  exact cast_intCast_of_eq _ _ (period_upper_eq hj i) (z i)
theorem toLower_unitStep {j : ℕ} (hj : j ≤ k + 1) (i : Fin 4) :
    toLower j (BlockAverages.unitStep (F := upperFrame L k n) j i) = BlockAverages.unitStep j i :=
  toLower_siteOfCoords hj _
theorem toLower_neg {j : ℕ} (hj : j ≤ k + 1) (x : (upperFrame L k n).Site j) :
    toLower j (-x) = - toLower j x := by
  have h := toLower_add hj x (-x)
  have h0 : toLower j (0 : (upperFrame L k n).Site j) = 0 := by
    have := toLower_add hj (0 : (upperFrame L k n).Site j) 0
    simpa using this
  rw [add_neg_cancel, h0] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm
theorem toLower_sub {j : ℕ} (hj : j ≤ k + 1) (x y : (upperFrame L k n).Site j) :
    toLower j (x - y) = toLower j x - toLower j y := by
  rw [sub_eq_add_neg, toLower_add hj, toLower_neg hj, sub_eq_add_neg]
def liftField {j : ℕ} (X : (lowerFrame L k n).GaugeField j) : (upperFrame L k n).GaugeField j :=
  fun s i => X (toLower j s) i
def lowerField {j : ℕ} (X : (upperFrame L k n).GaugeField j) : (lowerFrame L k n).GaugeField j :=
  fun s i => X (toUpper j s) i
theorem pathHolonomy_liftField {j : ℕ} (hj : j ≤ k + 1) (X : (lowerFrame L k n).GaugeField j)
    (x : (upperFrame L k n).Site j) (l : List PathStep) :
    pathHolonomy (liftField X) x l = pathHolonomy X (toLower j x) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have hv : toLower j (x + stepDisplacement j st) = toLower j x + stepDisplacement j st := by
      rw [toLower_add hj]
      rcases st with ⟨i, b⟩
      cases b
      · simp [stepDisplacement, toLower_neg hj, toLower_unitStep hj]
      · simp [stepDisplacement, toLower_unitStep hj]
    simp only [pathHolonomy]
    rw [ih, hv]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false, liftField]
      rw [toLower_sub hj, toLower_unitStep hj]
    · simp only [linkValue, if_true, liftField]
theorem plaquetteHolonomy_liftField {j : ℕ} (hj : j ≤ k + 1) (X : (lowerFrame L k n).GaugeField j)
    (p : (upperFrame L k n).Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy (liftField X) p = plaquetteHolonomy X (toLower j p.1, p.2) :=
  pathHolonomy_liftField hj X p.1 _
theorem toLower_refineSite {j : ℕ} (hj : j + 1 ≤ k + 1) (y : (upperFrame L k n).Site (j + 1)) :
    toLower j (refineSite y) = refineSite (toLower (j + 1) y) := by
  have h1 := toLower_siteOfCoords (L := L) (k := k) (n := n) (j := j) (by omega)
    (fun i => (L : ℤ) * siteCoords y i)
  have h2 := siteCoords_toLower hj y
  show toLower j (siteOfCoords j fun i => (L : ℤ) * siteCoords y i) =
    siteOfCoords j fun i => (L : ℤ) * siteCoords (toLower (j + 1) y) i
  rw [h1, h2]
theorem contourAverage_liftField {j : ℕ} (hj : j + 1 ≤ k + 1) (X : (lowerFrame L k n).GaugeField j)
    (c : (upperFrame L k n).Site (j + 1) × Fin 4) :
    contourAverage (j := j) (liftField X) c = contourAverage (j := j) X (toLower (j + 1) c.1, c.2) := by
  unfold BlockAverages.contourAverage
  have hj' : j ≤ k + 1 := by omega
  simp only [pathHolonomy_liftField hj', toLower_refineSite hj]
  rfl
theorem blockFit_liftField {j : ℕ} (hj : j + 1 ≤ k + 1) (X : (lowerFrame L k n).GaugeField j)
    (X' : (lowerFrame L k n).GaugeField (j + 1)) (c : (upperFrame L k n).Site (j + 1) × Fin 4) :
    blockFit (j := j) (liftField X) (liftField X') c = blockFit (j := j) X X' (toLower (j + 1) c.1, c.2) := by
  unfold blockFit
  rw [contourAverage_liftField hj]
  rfl
def liftChain (X : (lowerFrame L k n).FieldChain) : (upperFrame L k n).FieldChain := fun _ => liftField (X _)
def lowerChain (Z : (upperFrame L k n).FieldChain) : (lowerFrame L k n).FieldChain := fun _ => lowerField (Z _)
theorem liftChain_lowerChain (Z : (upperFrame L k n).FieldChain) {j : ℕ} (hj : j ≤ k + 1) :
    liftChain (lowerChain Z) j = Z j := by
  funext s i
  show Z j (toUpper j (toLower j s)) i = Z j s i
  rw [toUpper_toLower hj]
def siteEquiv {j : ℕ} (hj : j ≤ k + 1) : (upperFrame L k n).Site j ≃ (lowerFrame L k n).Site j :=
  ⟨toLower j, toUpper j, toUpper_toLower hj, toLower_toUpper hj⟩
def SitesCorrespond (Sa : Finset (lowerFrame L k n).Cell) (Sb : Finset (upperFrame L k n).Cell) : Prop :=
  ∀ j, j ≤ k + 1 → ∀ x : (upperFrame L k n).Site j, x ∈ sitesOfCells Sb j ↔ toLower j x ∈ sitesOfCells Sa j
theorem plaquetteCorners_toLower (p : (upperFrame L k n).Site 0 × Fin 4 × Fin 4) :
    plaquetteCorners ((toLower 0 p.1, p.2) : (lowerFrame L k n).Site 0 × Fin 4 × Fin 4) =
      (plaquetteCorners p).image (toLower 0) := by
  have h0 : 0 ≤ k + 1 := by omega
  simp [plaquetteCorners, Finset.image_insert, toLower_add h0, toLower_unitStep h0]
section Sets
variable {Sa : Finset (lowerFrame L k n).Cell} {Sb : Finset (upperFrame L k n).Cell}
theorem mem_innerPlaquettes_iff (hm : SitesCorrespond Sa Sb) (p : (upperFrame L k n).Site 0 × Fin 4 × Fin 4) :
    p ∈ innerPlaquettes Sb 0 ↔
      ((toLower 0 p.1, p.2) : (lowerFrame L k n).Site 0 × Fin 4 × Fin 4) ∈ innerPlaquettes Sa 0 := by
  have h0 : 0 ≤ k + 1 := by omega
  unfold innerPlaquettes
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  rw [plaquetteCorners_toLower, Finset.image_subset_iff, hm 0 h0 p.1]
  have : plaquetteCorners p ⊆ sitesOfCells Sb 0 ↔ ∀ x ∈ plaquetteCorners p, toLower 0 x ∈ sitesOfCells Sa 0 :=
    ⟨fun h x hx => (hm 0 h0 x).1 (h hx), fun h x hx => (hm 0 h0 x).2 (h x hx)⟩
  rw [this]
theorem mem_innerBonds_iff (hm : SitesCorrespond Sa Sb) {j : ℕ} (hj : j ≤ k + 1)
    (c : (upperFrame L k n).Site j × Fin 4) :
    c ∈ innerBonds Sb j ↔ ((toLower j c.1, c.2) : (lowerFrame L k n).Site j × Fin 4) ∈ innerBonds Sa j := by
  unfold innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  rw [hm j hj, hm j hj, toLower_add hj, toLower_unitStep hj]
theorem sum_innerPlaquettes_toLower (hm : SitesCorrespond Sa Sb)
    (g : (lowerFrame L k n).Site 0 × Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ innerPlaquettes Sb 0, g (toLower 0 p.1, p.2) = ∑ p ∈ innerPlaquettes Sa 0, g p :=
  Finset.sum_equiv ((siteEquiv (by omega)).prodCongr (Equiv.refl _)) (fun p => mem_innerPlaquettes_iff hm p)
    (fun _ _ => rfl)
theorem sum_innerBonds_toLower (hm : SitesCorrespond Sa Sb) {j : ℕ} (hj : j ≤ k + 1)
    (g : (lowerFrame L k n).Site j × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds Sb j, g (toLower j c.1, c.2) = ∑ c ∈ innerBonds Sa j, g c :=
  Finset.sum_equiv ((siteEquiv hj).prodCongr (Equiv.refl _)) (fun c => mem_innerBonds_iff hm hj c)
    (fun _ _ => rfl)
theorem chainAction_liftChain (hm : SitesCorrespond Sa Sb) (a : ℝ) (X : (lowerFrame L k n).FieldChain) :
    chainAction a Sb (liftChain X) = chainActionBelow a Sa X := by
  have a1 : ∑ p ∈ innerPlaquettes Sb 0,
      (1 - ((plaquetteHolonomy (liftChain X 0) p : UnitQuaternion) : ℍ[ℝ]).re) =
      ∑ p ∈ innerPlaquettes Sa 0, (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) := by
    rw [← sum_innerPlaquettes_toLower hm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show liftChain X 0 = liftField (X 0) from rfl, plaquetteHolonomy_liftField (by omega)]
  have a2 : ∀ j ∈ Finset.range (k + 1), ∑ c ∈ innerBonds Sb (j + 1),
      blockFit (j := j) (liftChain X j) (liftChain X (j + 1)) c =
      ∑ c ∈ innerBonds Sa (j + 1), blockFit (j := j) (X j) (X (j + 1)) c := by
    intro j hj
    have hj' : j + 1 ≤ k + 1 := Finset.mem_range.1 hj
    rw [← sum_innerBonds_toLower hm hj']
    refine Finset.sum_congr rfl fun c _ => ?_
    exact blockFit_liftField hj' _ _ c
  show ∑ p ∈ innerPlaquettes Sb 0, (1 - ((plaquetteHolonomy (liftChain X 0) p : UnitQuaternion) : ℍ[ℝ]).re) +
    a * ∑ j ∈ Finset.range (k + 1), ∑ c ∈ innerBonds Sb (j + 1),
      blockFit (j := j) (liftChain X j) (liftChain X (j + 1)) c = _
  rw [a1, Finset.sum_congr rfl a2]
  rfl
theorem chainAction_congr (a : ℝ) (Z Z' : (upperFrame L k n).FieldChain) (h : ∀ j, j ≤ k + 1 → Z j = Z' j) :
    chainAction a Sb Z = chainAction a Sb Z' := by
  have a2 : ∀ j ∈ Finset.range (k + 1), ∑ c ∈ innerBonds Sb (j + 1), blockFit (j := j) (Z j) (Z (j + 1)) c =
      ∑ c ∈ innerBonds Sb (j + 1), blockFit (j := j) (Z' j) (Z' (j + 1)) c := by
    intro j hj
    have hj' : j + 1 ≤ k + 1 := Finset.mem_range.1 hj
    rw [h j (by omega), h (j + 1) hj']
  show wilsonAction Sb (Z 0) + a * ∑ j ∈ Finset.range (k + 1), ∑ c ∈ innerBonds Sb (j + 1),
      blockFit (j := j) (Z j) (Z (j + 1)) c = _
  rw [Finset.sum_congr rfl a2, h 0 (by omega)]
  rfl
theorem chainActionBelow_lowerChain (hm : SitesCorrespond Sa Sb) (a : ℝ) (Z : (upperFrame L k n).FieldChain) :
    chainActionBelow a Sa (lowerChain Z) = chainAction a Sb Z := by
  rw [← chainAction_liftChain hm]
  exact chainAction_congr a _ _ fun j hj => liftChain_lowerChain Z hj
theorem enclosingCell_eq_toUpper_ancestorSite {j : ℕ} (hj : j ≤ k + 1) (x : (upperFrame L k n).Site j) :
    (enclosingCell x : (upperFrame L k n).Cell) =
      toUpper (k + 1) (ancestorSite (F := lowerFrame L k n) (k + 1) (toLower j x)) := by
  have hc := siteCoords_toLower hj x
  funext i
  have h := cast_intCast_of_eq _ _ (period_upper_eq (L := L) (k := k) (n := n) (j := k + 1) le_rfl i).symm
    ((siteCoords x i + ((L : ℤ) ^ (k + 1 - j) - 1) / 2) / (L : ℤ) ^ (k + 1 - j))
  change (((siteCoords x i + ((L : ℤ) ^ (k + 1 - j) - 1) / 2) / (L : ℤ) ^ (k + 1 - j) : ℤ) :
      ZMod ((upperFrame L k n).period (k + 1) i)) =
    ((ZMod.cast (((siteCoords (toLower j x) i + ((L : ℤ) ^ (k + 1 - j) - 1) / 2) / (L : ℤ) ^ (k + 1 - j) : ℤ) :
      ZMod ((lowerFrame L k n).period (k + 1) i)) : ℤ) : ZMod ((upperFrame L k n).period (k + 1) i))
  rw [hc]
  exact h.symm
theorem toUpper_inj {j : ℕ} (hj : j ≤ k + 1) {x y : (lowerFrame L k n).Site j} (h : toUpper j x = toUpper j y) :
    x = y := by
  rw [← toLower_toUpper hj x, h, toLower_toUpper hj y]
theorem enclosingCell_eq_toUpper_iff {j : ℕ} (hj : j ≤ k + 1) (x : (upperFrame L k n).Site j)
    (y : (lowerFrame L k n).Site (k + 1)) :
    (enclosingCell x : (upperFrame L k n).Cell) = toUpper (k + 1) y ↔
      ancestorSite (F := lowerFrame L k n) (k + 1) (toLower j x) = y := by
  rw [enclosingCell_eq_toUpper_ancestorSite hj]
  exact ⟨fun h => toUpper_inj le_rfl h, fun h => by rw [h]⟩
open Classical in
theorem cornerWeights_toLower (p : (upperFrame L k n).Site 0 × Fin 4 × Fin 4)
    (y : (lowerFrame L k n).Site (k + 1)) :
    (∑ x ∈ plaquetteCorners p,
        if (enclosingCell x : (upperFrame L k n).Cell) = toUpper (k + 1) y then (1 / 4 : ℝ) else 0) =
      ∑ x ∈ plaquetteCorners ((toLower 0 p.1, p.2) : (lowerFrame L k n).Site 0 × Fin 4 × Fin 4),
        if ancestorSite (F := lowerFrame L k n) (k + 1) x = y then (1 / 4 : ℝ) else 0 := by
  have h0 : 0 ≤ k + 1 := by omega
  have hi : Set.InjOn (toLower (L := L) (k := k) (n := n) 0) (plaquetteCorners p : Set _) :=
    fun x _ x' _ h => (siteEquiv h0).injective h
  rw [plaquetteCorners_toLower, Finset.sum_image hi]
  exact Finset.sum_congr rfl fun x _ => if_congr (enclosingCell_eq_toUpper_iff h0 x y) rfl rfl
open Classical in
theorem cellShare_liftChain (hm : SitesCorrespond Sa Sb) (a : ℝ) (X : (lowerFrame L k n).FieldChain)
    (y : (lowerFrame L k n).Site (k + 1)) :
    cellShare a Sb (toUpper (k + 1) y) (liftChain X) = chainSiteShare a Sa y X := by
  have a1 : ∑ p ∈ innerPlaquettes Sb 0,
      (∑ x ∈ plaquetteCorners p,
        if (enclosingCell x : (upperFrame L k n).Cell) = toUpper (k + 1) y then (1 / 4 : ℝ) else 0) *
        (1 - ((plaquetteHolonomy (liftChain X 0) p : UnitQuaternion) : ℍ[ℝ]).re) =
      ∑ p ∈ innerPlaquettes Sa 0,
        (∑ x ∈ plaquetteCorners p,
          if ancestorSite (F := lowerFrame L k n) (k + 1) x = y then (1 / 4 : ℝ) else 0) *
          (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) := by
    rw [← sum_innerPlaquettes_toLower hm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cornerWeights_toLower, show liftChain X 0 = liftField (X 0) from rfl,
      plaquetteHolonomy_liftField (by omega)]
  have a2 : ∀ j ∈ Finset.range (k + 1), ∑ c ∈ innerBonds Sb (j + 1),
      ((if (enclosingCell c.1 : (upperFrame L k n).Cell) = toUpper (k + 1) y then (1 / 2 : ℝ) else 0) +
        (if (enclosingCell (c.1 + BlockAverages.unitStep (j + 1) c.2) : (upperFrame L k n).Cell) =
          toUpper (k + 1) y then (1 / 2 : ℝ) else 0)) *
        blockFit (j := j) (liftChain X j) (liftChain X (j + 1)) c =
      ∑ c ∈ innerBonds Sa (j + 1),
        ((if ancestorSite (F := lowerFrame L k n) (k + 1) c.1 = y then (1 / 2 : ℝ) else 0) +
          (if ancestorSite (F := lowerFrame L k n) (k + 1) (c.1 + BlockAverages.unitStep (j + 1) c.2) = y
            then (1 / 2 : ℝ) else 0)) *
          blockFit (j := j) (X j) (X (j + 1)) c := by
    intro j hj
    have hj' : j + 1 ≤ k + 1 := Finset.mem_range.1 hj
    rw [← sum_innerBonds_toLower hm hj']
    refine Finset.sum_congr rfl fun c _ => ?_
    have e1 := enclosingCell_eq_toUpper_iff hj' c.1 y
    have e2 := enclosingCell_eq_toUpper_iff hj' (c.1 + BlockAverages.unitStep (j + 1) c.2) y
    rw [toLower_add hj', toLower_unitStep hj'] at e2
    rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]
    congr 1
    exact blockFit_liftField hj' _ _ c
  unfold cellShare chainSiteShare
  convert congrArg₂ (· + ·) a1 (congrArg (a * ·) (Finset.sum_congr rfl a2)) using 1
  all_goals congr!
theorem cellShare_congr (a : ℝ) (y : (upperFrame L k n).Cell) (Z Z' : (upperFrame L k n).FieldChain)
    (h : ∀ j, j ≤ k + 1 → Z j = Z' j) :
    cellShare a Sb y Z = cellShare a Sb y Z' := by
  have h0 : Z 0 = Z' 0 := h 0 (by omega)
  unfold cellShare
  refine congrArg₂ (· + ·) ?_ (congrArg (a * ·) ?_)
  · exact Finset.sum_congr rfl fun p _ => by rw [h0]
  · refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c _ => ?_
    have hj' : j + 1 ≤ k + 1 := Finset.mem_range.1 hj
    have e1 : Z j = Z' j := h j (by omega)
    have e2 : Z (j + 1) = Z' (j + 1) := h (j + 1) hj'
    rw [e1, e2]
end Sets
theorem sitesCorrespond_sitesInBlocks [NeZero n] [NeZero L] (hL : Odd L) (S : Finset (TorusSite n)) :
    SitesCorrespond (cellsOfSites (lowerFrame L k n) S) (cellsOfSites (upperFrame L k n) (sitesInBlocks L S)) := by
  intro j hj x
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsa : ∀ i, 0 < (lowerFrame L k n).extent i := fun _ => hn0
  have hsb : ∀ i, 0 < (upperFrame L k n).extent i := fun _ => Nat.mul_pos hn0 hL.pos
  rw [mem_sitesOfCells_iff (F := upperFrame L k n) hL hsb hj,
    mem_sitesOfCells_iff (F := lowerFrame L k n) hL hsa (by show j ≤ k + 1 + 1; omega),
    mem_cellsOfSites_torusFrame, mem_cellsOfSites_torusFrame]
  have e : siteOfCell (enclosingCell x : (upperFrame L k n).Cell) =
      toTorusSite (n * L) (ancestorSite (F := lowerFrame L k n) (k + 1) (toLower j x)) := by
    rw [enclosingCell_eq_toUpper_ancestorSite hj]
    funext i
    show ((siteCoords (toUpper (k + 1) (ancestorSite (F := lowerFrame L k n) (k + 1) (toLower j x))) i : ℤ) :
        ZMod (n * L)) =
      ((siteCoords (ancestorSite (F := lowerFrame L k n) (k + 1) (toLower j x)) i : ℤ) : ZMod (n * L))
    rw [siteCoords_toUpper le_rfl]
  have hb : siteOfCell (enclosingCell x : (upperFrame L k n).Cell) ∈ sitesInBlocks L S ↔
      parentBlock L (siteOfCell (enclosingCell x : (upperFrame L k n).Cell)) ∈ S := by
    simp [sitesInBlocks]
  rw [hb, e, parentBlock_ancestorSite (t := k + 1) hL hj]
end Carry
section Minimal
variable {F : BlockFrame}
theorem exists_chain_minimalAction (hLV : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) (j : ℕ) : ∀ W : F.GaugeField j, ∃ X : F.FieldChain, X j = W ∧
      wilsonAction S (X 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1), blockFit (X i) (X (i + 1)) c =
        minimalAction a S j W ∧
      ∀ X' : F.FieldChain, X' j = W → minimalAction a S j W ≤
        wilsonAction S (X' 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
          blockFit (X' i) (X' (i + 1)) c := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.exists_minimizing_chain_below <;> assumption
theorem chainAction_eq_below_add (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) :
    chainAction a S X = chainActionBelow a S X +
      a * ∑ c ∈ innerBonds S (F.depth + 1), blockFit (X F.depth) (X (F.depth + 1)) c := by
  unfold chainAction chainActionBelow
  have hr : Finset.range F.top = Finset.range (F.depth + 1) := rfl
  rw [hr, Finset.sum_range_succ, mul_add, add_assoc]
theorem chainActionBelow_congr (a : ℝ) (S : Finset F.Cell) (X X' : F.FieldChain)
    (h : ∀ j, j ≤ F.depth → X j = X' j) :
    chainActionBelow a S X = chainActionBelow a S X' := by
  have h0 : X 0 = X' 0 := h 0 (by omega)
  unfold chainActionBelow
  refine congrArg₂ (· + ·) (by rw [h0]) (congrArg (a * ·) ?_)
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c _ => ?_
  have hj' : j + 1 ≤ F.depth := Finset.mem_range.1 hj
  have e1 : X j = X' j := h j (by omega)
  have e2 : X (j + 1) = X' (j + 1) := h (j + 1) hj'
  rw [e1, e2]
open Classical in
theorem chainSiteShare_congr (a : ℝ) (S : Finset F.Cell) (y : F.Site F.depth) (X X' : F.FieldChain)
    (h : ∀ j, j ≤ F.depth → X j = X' j) : chainSiteShare a S y X = chainSiteShare a S y X' := by
  have h0 : X 0 = X' 0 := h 0 (by omega)
  unfold chainSiteShare
  refine congrArg₂ (· + ·) ?_ (congrArg (a * ·) ?_)
  · exact Finset.sum_congr rfl fun p _ => by rw [h0]
  · refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c _ => ?_
    have hj' : j + 1 ≤ F.depth := Finset.mem_range.1 hj
    have e1 : X j = X' j := h j (by omega)
    have e2 : X (j + 1) = X' (j + 1) := h (j + 1) hj'
    rw [e1, e2]
theorem update_top_of_le_depth (Z : F.FieldChain) (V : F.GaugeField F.top) {j : ℕ} (hj : j ≤ F.depth) :
    Function.update Z F.top V j = Z j :=
  Function.update_of_ne (by show j ≠ F.depth + 1; omega) _ _
theorem isMinimalChain_of_below (hLV : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset F.Cell) (V : F.GaugeField F.top) (Wc : F.GaugeField F.depth)
    (hW : ∀ W', blockEnergy a S F.depth Wc V ≤ blockEnergy a S F.depth W' V)
    (Z : F.FieldChain) (hZ : Z F.depth = Wc) (hlow : chainActionBelow a S Z ≤ minimalAction a S F.depth Wc) :
    IsMinimalChain a S V (Function.update Z F.top V) := by
  refine ⟨Function.update_self _ _ _, fun X' hX' => ?_⟩
  have hlo : ∀ j, j ≤ F.depth → Function.update Z F.top V j = Z j :=
    fun j hj => update_top_of_le_depth Z V hj
  rw [chainAction_eq_below_add, chainAction_eq_below_add, chainActionBelow_congr a S _ Z hlo]
  have e1 : Function.update Z F.top V F.depth = Wc := by rw [hlo _ le_rfl, hZ]
  have e2 : Function.update Z F.top V (F.depth + 1) = V := Function.update_self _ _ _
  have e3 : X' (F.depth + 1) = V := hX'
  rw [e1, e2, e3]
  obtain ⟨_, _, _, hm⟩ := exists_chain_minimalAction hLV a ha S F.depth (X' F.depth)
  have h1 : minimalAction a S F.depth (X' F.depth) ≤ chainActionBelow a S X' := hm X' rfl
  have h2 := hW (X' F.depth)
  unfold blockEnergy at h2
  linarith
end Minimal
section Split
variable {L t n : ℕ}
theorem period_depth (i : Fin 4) : (torusFrame L t n).period t i = n * L := by apply _root_.YangMills.Construction.CongruentAdmission.torusFrame_period_depth <;> assumption
open Classical in
theorem sum_sitesInBlocks_ancestorSite [NeZero n] [NeZero L] (hL : Odd L) {j : ℕ} (hj : j ≤ t)
    (x : (torusFrame L t n).Site j) (Y : TorusSite n) (c : ℝ) :
    ∑ y ∈ sitesInBlocks L {Y},
        (if ancestorSite (F := torusFrame L t n) t x = torusSiteInFrame (torusFrame L t n) t y then c else 0) =
      if (enclosingCell x : (torusFrame L t n).Cell) =
        torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y then c else 0 := by
  have hp : ∀ i, (torusFrame L t n).period t i = n * L := period_depth
  set y0 : TorusSite (n * L) := toTorusSite (n * L) (ancestorSite (F := torusFrame L t n) t x) with hy0
  have e : ∀ y : TorusSite (n * L),
      ancestorSite (F := torusFrame L t n) t x = torusSiteInFrame (torusFrame L t n) t y ↔ y0 = y := by
    intro y
    constructor
    · intro h
      rw [hy0, h, toTorusSite_torusSiteInFrame hp]
    · intro h
      rw [← h, hy0, torusSiteInFrame_toTorusSite hp]
  have hm : y0 ∈ sitesInBlocks L {Y} ↔
      (enclosingCell x : (torusFrame L t n).Cell) = torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y := by
    have h1 : y0 ∈ sitesInBlocks L {Y} ↔ parentBlock L y0 = Y := by simp [sitesInBlocks]
    rw [h1, hy0, parentBlock_ancestorSite hL hj]
    constructor
    · intro h
      rw [← h, torusSiteInFrame_siteOfCell]
    · intro h
      rw [h, siteOfCell_torusSiteInFrame]
  have e2 : ∀ y : TorusSite (n * L),
      (if ancestorSite (F := torusFrame L t n) t x = torusSiteInFrame (torusFrame L t n) t y then c else 0) =
        if y0 = y then c else 0 := fun y => if_congr (e y) rfl rfl
  rw [Finset.sum_congr rfl fun y _ => e2 y, Finset.sum_ite_eq]
  exact if_congr hm rfl rfl
open Classical in
theorem cellShare_eq_sum_add [NeZero n] [NeZero L] (hL : Odd L) (a : ℝ) (S : Finset (torusFrame L t n).Cell)
    (X : (torusFrame L t n).FieldChain) (Y : TorusSite n) :
    cellShare a S (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y) X =
      ∑ y ∈ sitesInBlocks L {Y}, chainSiteShare a S (torusSiteInFrame (torusFrame L t n) t y) X +
      a * ∑ c ∈ innerBonds S (t + 1),
        ((if (enclosingCell c.1 : (torusFrame L t n).Cell) =
            torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y then (1 / 2 : ℝ) else 0) +
          (if (enclosingCell (c.1 + BlockAverages.unitStep (t + 1) c.2) : (torusFrame L t n).Cell) =
            torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y then (1 / 2 : ℝ) else 0)) *
        blockFit (j := t) (X t) (X (t + 1)) c := by
  set Yc := torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y with hYc
  have a1 : ∑ p ∈ innerPlaquettes S 0,
        (∑ x ∈ plaquetteCorners p,
          if (enclosingCell x : (torusFrame L t n).Cell) = Yc then (1 / 4 : ℝ) else 0) *
        (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) =
      ∑ y ∈ sitesInBlocks L {Y}, ∑ p ∈ innerPlaquettes S 0,
        (∑ x ∈ plaquetteCorners p,
          if ancestorSite (F := torusFrame L t n) t x = torusSiteInFrame (torusFrame L t n) t y
          then (1 / 4 : ℝ) else 0) * (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_mul, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun x _ => (sum_sitesInBlocks_ancestorSite hL (Nat.zero_le t) x Y _).symm
  have a2 : ∀ j ∈ Finset.range t, ∑ c ∈ innerBonds S (j + 1),
      ((if (enclosingCell c.1 : (torusFrame L t n).Cell) = Yc then (1 / 2 : ℝ) else 0) +
        (if (enclosingCell (c.1 + BlockAverages.unitStep (j + 1) c.2) : (torusFrame L t n).Cell) = Yc
          then (1 / 2 : ℝ) else 0)) *
        blockFit (j := j) (X j) (X (j + 1)) c =
      ∑ y ∈ sitesInBlocks L {Y}, ∑ c ∈ innerBonds S (j + 1),
        ((if ancestorSite (F := torusFrame L t n) t c.1 = torusSiteInFrame (torusFrame L t n) t y
            then (1 / 2 : ℝ) else 0) +
          (if ancestorSite (F := torusFrame L t n) t (c.1 + BlockAverages.unitStep (j + 1) c.2) =
              torusSiteInFrame (torusFrame L t n) t y
            then (1 / 2 : ℝ) else 0)) * blockFit (j := j) (X j) (X (j + 1)) c := by
    intro j hj
    have hj' : j + 1 ≤ t := Finset.mem_range.1 hj
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul, Finset.sum_add_distrib, sum_sitesInBlocks_ancestorSite hL hj' c.1 Y,
      sum_sitesInBlocks_ancestorSite hL hj' (c.1 + BlockAverages.unitStep (j + 1) c.2) Y]
  have hr1 : Finset.range (torusFrame L t n).top = Finset.range (t + 1) := rfl
  have hr2 : Finset.range (torusFrame L t n).depth = Finset.range t := rfl
  unfold cellShare chainSiteShare
  rw [hr1, hr2, Finset.sum_range_succ, a1, Finset.sum_congr rfl a2, Finset.sum_comm (s := Finset.range t),
    Finset.sum_add_distrib, ← Finset.mul_sum, mul_add, add_assoc]
  rfl
end Split
section Top
variable {L t n : ℕ}
theorem enclosingCell_top (x : (torusFrame L t n).Cell) : (enclosingCell x : (torusFrame L t n).Cell) = x := by
  funext i
  show (((siteCoords x i + ((L : ℤ) ^ (t + 1 - (t + 1)) - 1) / 2) / (L : ℤ) ^ (t + 1 - (t + 1)) : ℤ) :
    ZMod ((torusFrame L t n).period (torusFrame L t n).top i)) = x i
  simp only [Nat.sub_self, pow_zero, sub_self, Int.zero_ediv, add_zero, Int.ediv_one]
  exact ZMod.intCast_zmod_cast (x i)
theorem mem_innerBonds {F : BlockFrame} (S : Finset F.Cell) {j : ℕ} (c : F.Site j × Fin 4) :
    c ∈ innerBonds S j ↔ c.1 ∈ sitesOfCells S j ∧ c.1 + BlockAverages.unitStep j c.2 ∈ sitesOfCells S j := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.mem_innerBonds <;> assumption
theorem siteOfCell_add_unitStep [NeZero n] (c : (torusFrame L t n).Cell) (i : Fin 4) :
    siteOfCell (c + BlockAverages.unitStep (torusFrame L t n).top i) = siteOfCell c + TorusFields.unitStep n i :=
  (siteOfCell_add _ _).trans (congrArg (siteOfCell c + ·) (siteOfCell_unitStep i))
def cellEquiv [NeZero n] : (torusFrame L t n).Cell ≃ TorusSite n :=
  ⟨siteOfCell, torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top, torusSiteInFrame_siteOfCell,
    siteOfCell_torusSiteInFrame⟩
open Classical in
theorem sum_half_weights [NeZero n] (S : Finset (TorusSite n)) (Y : TorusSite n) (hY : Y ∈ S) (e : TorusSite n)
    (he : e ≠ 0) (g : TorusSite n → ℝ) :
    ∑ x : TorusSite n, (if x ∈ S ∧ x + e ∈ S then
        ((if x = Y then (1 / 2 : ℝ) else 0) + (if x + e = Y then (1 / 2 : ℝ) else 0)) * g x else 0) =
      1 / 2 * ((if Y + e ∈ S then g Y else 0) + (if Y - e ∈ S then g (Y - e) else 0)) := by
  have hx : ∀ x : TorusSite n, (if x ∈ S ∧ x + e ∈ S then
        ((if x = Y then (1 / 2 : ℝ) else 0) + (if x + e = Y then (1 / 2 : ℝ) else 0)) * g x else 0) =
      (if x = Y then 1 / 2 * (if Y + e ∈ S then g Y else 0) else 0) +
        (if x = Y - e then 1 / 2 * (if Y - e ∈ S then g (Y - e) else 0) else 0) := by
    intro x
    have hc : x + e = Y ↔ x = Y - e := eq_sub_iff_add_eq.symm
    by_cases h1 : x = Y
    · subst h1
      have h2 : ¬ x = x - e := fun h => he (sub_eq_self.1 h.symm)
      have h3 : ¬ x + e = x := fun h => h2 (hc.1 h)
      by_cases h4 : x + e ∈ S
      · simp [hY, h4, h2, h3]
      · simp [h4, h2]
    · by_cases h2 : x = Y - e
      · have h3 : x + e = Y := hc.2 h2
        subst h2
        by_cases h4 : Y - e ∈ S
        · simp [hY, h4, h1]
        · simp [h4, h1]
      · have h3 : ¬ x + e = Y := fun h => h2 (hc.1 h)
        simp [h1, h2, h3]
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring
open Classical in
theorem sum_top_bonds [NeZero n] (hn : 2 ≤ n) (S : Finset (TorusSite n)) (Y : TorusSite n) (hY : Y ∈ S)
    (g : TorusBond n → ℝ) (f : (torusFrame L t n).Cell × Fin 4 → ℝ)
    (hf : ∀ b : TorusBond n, f (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top b.1, b.2) = g b) :
    ∑ c ∈ innerBonds (cellsOfSites (torusFrame L t n) S) (t + 1),
        ((if (enclosingCell c.1 : (torusFrame L t n).Cell) =
            torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y then (1 / 2 : ℝ) else 0) +
          (if (enclosingCell (c.1 + BlockAverages.unitStep (t + 1) c.2) : (torusFrame L t n).Cell) =
            torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y then (1 / 2 : ℝ) else 0)) * f c =
      1 / 2 * ∑ i : Fin 4, ((if Y + TorusFields.unitStep n i ∈ S then g (Y, i) else 0) +
        (if Y - TorusFields.unitStep n i ∈ S then g (Y - TorusFields.unitStep n i, i) else 0)) := by
  have hback : ∀ (x : (torusFrame L t n).Cell) (y : TorusSite n),
      x = torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y ↔ siteOfCell x = y := by
    intro x y
    constructor
    · intro h
      rw [h, siteOfCell_torusSiteInFrame]
    · intro h
      rw [← h, torusSiteInFrame_siteOfCell]
  have hbond : ∀ c : (torusFrame L t n).Cell × Fin 4, c ∈ innerBonds (cellsOfSites (torusFrame L t n) S) (t + 1) ↔
      siteOfCell c.1 ∈ S ∧ siteOfCell c.1 + TorusFields.unitStep n c.2 ∈ S := by
    intro c
    have m1 : ∀ x : (torusFrame L t n).Cell,
        x ∈ sitesOfCells (cellsOfSites (torusFrame L t n) S) (t + 1) ↔ siteOfCell x ∈ S :=
      fun x => (mem_sitesOfCells_torusFrame _ x).trans mem_cellsOfSites_torusFrame
    refine (mem_innerBonds (F := torusFrame L t n) (j := t + 1) _ c).trans ?_
    refine and_congr (m1 c.1) ((m1 _).trans ?_)
    exact iff_of_eq (congrArg (· ∈ S) (siteOfCell_add_unitStep c.1 c.2))
  have step : ∑ c ∈ innerBonds (cellsOfSites (torusFrame L t n) S) (t + 1),
        ((if (enclosingCell c.1 : (torusFrame L t n).Cell) =
            torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y then (1 / 2 : ℝ) else 0) +
          (if (enclosingCell (c.1 + BlockAverages.unitStep (t + 1) c.2) : (torusFrame L t n).Cell) =
            torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y then (1 / 2 : ℝ) else 0)) * f c =
      ∑ b ∈ (Finset.univ : Finset (TorusBond n)).filter
          (fun b => b.1 ∈ S ∧ b.1 + TorusFields.unitStep n b.2 ∈ S),
        ((if b.1 = Y then (1 / 2 : ℝ) else 0) +
          (if b.1 + TorusFields.unitStep n b.2 = Y then (1 / 2 : ℝ) else 0)) * g b := by
    refine Finset.sum_equiv ((cellEquiv (L := L) (t := t)).prodCongr (Equiv.refl _))
      (fun (c : (torusFrame L t n).Cell × Fin 4) => ?_)
      (fun (c : (torusFrame L t n).Site (t + 1) × Fin 4) _ => ?_)
    · exact (hbond c).trans
        ⟨fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, fun h => (Finset.mem_filter.1 h).2⟩
    · have e1 : c.1 = torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y ↔ siteOfCell c.1 = Y :=
        hback c.1 Y
      have e2 : c.1 + BlockAverages.unitStep (t + 1) c.2 =
          torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y ↔
          siteOfCell c.1 + TorusFields.unitStep n c.2 = Y :=
        (hback (c.1 + BlockAverages.unitStep (t + 1) c.2) Y).trans
          (iff_of_eq (congrArg (· = Y) (siteOfCell_add_unitStep c.1 c.2)))
      have t1 : (enclosingCell c.1 : (torusFrame L t n).Cell) = c.1 := enclosingCell_top c.1
      have t2 : (enclosingCell (c.1 + BlockAverages.unitStep (t + 1) c.2) : (torusFrame L t n).Cell) =
          c.1 + BlockAverages.unitStep (t + 1) c.2 :=
        enclosingCell_top (c.1 + BlockAverages.unitStep (t + 1) c.2)
      have e0 : ((torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (siteOfCell c.1), c.2) :
          (torusFrame L t n).Cell × Fin 4) = c := Prod.ext (torusSiteInFrame_siteOfCell c.1) rfl
      have ef : f c = g (siteOfCell c.1, c.2) := (congrArg f e0).symm.trans (hf (siteOfCell c.1, c.2))
      show ((if (enclosingCell c.1 : (torusFrame L t n).Cell) =
            torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y then (1 / 2 : ℝ) else 0) +
          (if (enclosingCell (c.1 + BlockAverages.unitStep (t + 1) c.2) : (torusFrame L t n).Cell) =
            torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y then (1 / 2 : ℝ) else 0)) * f c =
        ((if siteOfCell c.1 = Y then (1 / 2 : ℝ) else 0) +
          (if siteOfCell c.1 + TorusFields.unitStep n c.2 = Y then (1 / 2 : ℝ) else 0)) *
            g (siteOfCell c.1, c.2)
      refine congrArg₂ (· * ·) (congrArg₂ (· + ·) (if_congr ?_ rfl rfl) (if_congr ?_ rfl rfl)) ef
      · rw [t1]
        exact e1
      · rw [t2]
        exact e2
  rw [step, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he : TorusFields.unitStep n i ≠ 0 := by
    intro h
    have h1 := congrFun h i
    have : Fact (1 < n) := ⟨hn⟩
    simp [TorusFields.unitStep] at h1
  exact sum_half_weights S Y hY (TorusFields.unitStep n i) he fun x => g (x, i)
end Top
section Read
variable {G H : BlockFrame} {j j' N : ℕ} [NeZero N]
theorem toTorusSite_sub (hp : ∀ i, G.period j i = N) (x y : G.Site j) :
    toTorusSite N (x - y) = toTorusSite N x - toTorusSite N y := by
  rw [sub_eq_add_neg, toTorusSite_add hp, toTorusSite_neg hp, sub_eq_add_neg]
theorem pathHolonomy_readAtLevel (hG : ∀ i, G.period j i = N) (hH : ∀ i, H.period j' i = N)
    (W : TorusField N) (x : G.Site j) (x' : H.Site j') (hx : toTorusSite N x = toTorusSite N x')
    (l : List PathStep) :
    pathHolonomy (readAtLevel G j W) x l = pathHolonomy (readAtLevel H j' W) x' l := by
  have hr : ∀ (F : BlockFrame) (k : ℕ) (z : F.Site k) (i : Fin 4),
      readAtLevel F k W z i = W (toTorusSite N z) i :=
    fun _ _ _ _ => rfl
  induction l generalizing x x' with
  | nil => rfl
  | cons st r ih =>
    simp only [pathHolonomy]
    have hv : toTorusSite N (x + stepDisplacement j st) = toTorusSite N (x' + stepDisplacement j' st) := by
      rw [toTorusSite_add hG, toTorusSite_add hH, hx]
      rcases st with ⟨i, b⟩
      cases b
      · simp only [stepDisplacement, Bool.false_eq_true, if_false]
        rw [toTorusSite_neg hG, toTorusSite_neg hH, toTorusSite_unitStep hG, toTorusSite_unitStep hH]
      · simp only [stepDisplacement, if_true]
        rw [toTorusSite_unitStep hG, toTorusSite_unitStep hH]
    rw [ih _ _ hv]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false, hr]
      rw [toTorusSite_sub hG, toTorusSite_sub hH, toTorusSite_unitStep hG, toTorusSite_unitStep hH, hx]
    · simp only [linkValue, if_true, hr]
      rw [hx]
theorem plaquetteHolonomy_readAtLevel (hp : ∀ i, G.period j i = N) (W : TorusField N) (x : G.Site j)
    (μ ν : Fin 4) :
    plaquetteHolonomy (readAtLevel G j W) (x, μ, ν) = TorusFields.holonomy W (toTorusSite N x) μ ν := by
  unfold TorusFields.holonomy
  have a1 : x + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν - BlockAverages.unitStep j μ =
      x + BlockAverages.unitStep j ν := by abel
  have a2 : x + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν + -BlockAverages.unitStep j μ -
      BlockAverages.unitStep j ν = x := by abel
  have hr : ∀ (z : G.Site j) (i : Fin 4), readAtLevel G j W z i = W (toTorusSite N z) i := fun _ _ => rfl
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
    mul_one, a1, a2, hr, toTorusSite_add hp, toTorusSite_unitStep hp, mul_assoc]
end Read
section PlainFit
variable {L t n : ℕ}
theorem blockFit_readAtLevel [NeZero n] [NeZero L] (W : TorusField (n * L)) (V : TorusField n)
    (b : TorusBond n) :
    blockFit (F := torusFrame L t n) (j := t) (readAtLevel (torusFrame L t n) t W)
        (readAtLevel (torusFrame L t n) (t + 1) V)
      (torusSiteInFrame (torusFrame L t n) (t + 1) b.1, b.2) = blockFitAt L W V b := by
  have hG0 : ∀ i, (stepBlockFrame L n).period 0 i = n * L := fun i => by
    show n * L ^ (0 + 1 - 0) = n * L
    simp
  have hH0 : ∀ i, (torusFrame L t n).period t i = n * L := period_depth
  have hG1 : ∀ i, (stepBlockFrame L n).period 1 i = n := fun i => by
    show n * L ^ (0 + 1 - 1) = n
    simp
  have hH1 : ∀ i, (torusFrame L t n).period (t + 1) i = n := fun i => by
    show n * L ^ (t + 1 - (t + 1)) = n
    simp
  have hd : toTorusSite (n * L)
        (refineSite (F := stepBlockFrame L n) (j := 0) (torusSiteInFrame (stepBlockFrame L n) 1 b.1)) =
      toTorusSite (n * L)
        (refineSite (F := torusFrame L t n) (j := t) (torusSiteInFrame (torusFrame L t n) (t + 1) b.1)) := by
    unfold refineSite
    rw [toTorusSite_siteOfCoords hG0, toTorusSite_siteOfCoords hH0]
    congr 1
    funext i
    show (L : ℤ) * siteCoords (torusSiteInFrame (stepBlockFrame L n) 1 b.1) i =
      (L : ℤ) * siteCoords (torusSiteInFrame (torusFrame L t n) (t + 1) b.1) i
    rw [siteCoords_torusSiteInFrame hG1, siteCoords_torusSiteInFrame hH1]
  have hc : contourAverage (F := torusFrame L t n) (j := t) (readAtLevel (torusFrame L t n) t W)
        (torusSiteInFrame (torusFrame L t n) (t + 1) b.1, b.2) =
      contourAverage (F := stepBlockFrame L n) (j := 0) (readAtLevel (stepBlockFrame L n) 0 W)
        (torusSiteInFrame (stepBlockFrame L n) 1 b.1, b.2) := by
    unfold BlockAverages.contourAverage
    exact congrArg ((1 / (24 * (L : ℝ) ^ 4)) • ·) (Finset.sum_congr rfl fun h _ =>
      Finset.sum_congr rfl fun π _ => congrArg Subtype.val (pathHolonomy_readAtLevel hH0 hG0 W _ _ hd.symm _))
  have hv1 : readAtLevel (torusFrame L t n) (t + 1) V (torusSiteInFrame (torusFrame L t n) (t + 1) b.1) b.2 =
      V b.1 b.2 :=
    readAtLevel_torusSiteInFrame hH1 V b.1 b.2
  have hv2 : readAtLevel (stepBlockFrame L n) 1 V (torusSiteInFrame (stepBlockFrame L n) 1 b.1) b.2 =
      V b.1 b.2 :=
    readAtLevel_torusSiteInFrame hG1 V b.1 b.2
  unfold blockFitAt blockFit
  simp only [hc, hv1]
  rw [show readAtLevel (stepBlockFrame L n) 1 V (torusSiteInFrame (stepBlockFrame L n) 1 b.1) b.2 = V b.1 b.2
    from hv2]
end PlainFit
section Zero
variable {L n : ℕ}
theorem ancestorSite_self {F : BlockFrame} {j : ℕ} (x : F.Site j) : ancestorSite j x = x := by
  funext i
  show (((siteCoords x i + ((F.blockSide : ℤ) ^ (j - j) - 1) / 2) / (F.blockSide : ℤ) ^ (j - j) : ℤ) :
    ZMod (F.period j i)) = x i
  simp only [Nat.sub_self, pow_zero, sub_self, Int.zero_ediv, add_zero, Int.ediv_one]
  exact ZMod.intCast_zmod_cast (x i)
theorem mem_sitesOfCells_zero [NeZero n] [NeZero L] (hL : Odd L) (S : Finset (TorusSite n))
    (x : (torusFrame L 0 n).Site 0) :
    x ∈ sitesOfCells (cellsOfSites (torusFrame L 0 n) S) 0 ↔ toTorusSite (n * L) x ∈ sitesInBlocks L S := by
  have hs : ∀ i, 0 < (torusFrame L 0 n).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : toTorusSite (n * L) x ∈ sitesInBlocks L S ↔ parentBlock L (toTorusSite (n * L) x) ∈ S := by
    simp [sitesInBlocks]
  have h2 := parentBlock_ancestorSite (t := 0) (n := n) hL (le_refl 0) x
  rw [ancestorSite_self] at h2
  rw [mem_sitesOfCells_iff (F := torusFrame L 0 n) hL hs (Nat.zero_le _), mem_cellsOfSites_torusFrame, h1, h2]
theorem mem_plaquetteCorners_iff [NeZero n] [NeZero L] (x : TorusSite (n * L)) (μ ν : Fin 4)
    (z : (torusFrame L 0 n).Site 0) :
    z ∈ plaquetteCorners ((torusSiteInFrame (torusFrame L 0 n) 0 x, μ, ν) :
        (torusFrame L 0 n).Site 0 × Fin 4 × Fin 4) ↔
      toTorusSite (n * L) z ∈ plaquetteVertices x μ ν := by
  have hp : ∀ i, (torusFrame L 0 n).period 0 i = n * L := period_depth
  have conv : ∀ q : (torusFrame L 0 n).Site 0, z = q ↔ toTorusSite (n * L) z = toTorusSite (n * L) q :=
    fun q => ⟨congrArg _, toTorusSite_injective hp⟩
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton, plaquetteVertices, List.mem_cons,
    List.not_mem_nil, or_false]
  rw [conv, conv, conv, conv]
  simp only [toTorusSite_add hp, toTorusSite_unitStep hp, toTorusSite_torusSiteInFrame hp]
theorem mem_plaquettesIn_iff [NeZero n] [NeZero L] (hL : Odd L) (S : Finset (TorusSite n))
    (p : TorusPlaquette (n * L)) :
    p ∈ plaquettesIn (sitesInBlocks L S) ↔
      ((torusSiteInFrame (torusFrame L 0 n) 0 p.1, p.2) : (torusFrame L 0 n).Site 0 × Fin 4 × Fin 4) ∈
        innerPlaquettes (cellsOfSites (torusFrame L 0 n) S) 0 := by
  obtain ⟨x, μ, ν⟩ := p
  have hp : ∀ i, (torusFrame L 0 n).period 0 i = n * L := period_depth
  constructor
  · intro h
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨hlt, hc⟩ := h
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, by simp⟩, hlt, fun z hz => ?_⟩
    · show torusSiteInFrame (torusFrame L 0 n) 0 x ∈ _
      rw [mem_sitesOfCells_zero hL, toTorusSite_torusSiteInFrame hp]
      exact hc x (by simp [plaquetteVertices])
    · rw [mem_sitesOfCells_zero hL]
      exact hc _ ((mem_plaquetteCorners_iff x μ ν z).1 hz)
  · intro h
    obtain ⟨-, hlt, hc⟩ := Finset.mem_filter.1 h
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hlt, fun z hz => ?_⟩
    have hz' : torusSiteInFrame (torusFrame L 0 n) 0 z ∈
        plaquetteCorners ((torusSiteInFrame (torusFrame L 0 n) 0 x, μ, ν) :
          (torusFrame L 0 n).Site 0 × Fin 4 × Fin 4) :=
      (mem_plaquetteCorners_iff x μ ν _).2 (by rw [toTorusSite_torusSiteInFrame hp]; exact hz)
    have h3 := (mem_sitesOfCells_zero hL S _).1 (hc hz')
    rwa [toTorusSite_torusSiteInFrame hp] at h3
theorem nodup_plaquetteVertices {N : ℕ} (hN : 2 ≤ N) (x : TorusSite N) {μ ν : Fin 4} (h : μ < ν) :
    (plaquetteVertices x μ ν).Nodup := by
  have : Fact (1 < N) := ⟨hN⟩
  have hne : ν ≠ μ := (ne_of_lt h).symm
  have a1 : TorusFields.unitStep N μ μ = 1 := by simp [TorusFields.unitStep]
  have a2 : TorusFields.unitStep N ν ν = 1 := by simp [TorusFields.unitStep]
  have a3 : TorusFields.unitStep N ν μ = 0 := by simp [TorusFields.unitStep, hne.symm]
  have a4 : TorusFields.unitStep N μ ν = 0 := by simp [TorusFields.unitStep, hne]
  simp only [plaquetteVertices, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro e
    have := congrFun e μ
    simp [a1] at this
  · intro e
    have := congrFun e ν
    simp [a2] at this
  · intro e
    have := congrFun e μ
    simp [a1, a3] at this
  · intro e
    have := congrFun e μ
    simp [a1, a3] at this
  · intro e
    have := congrFun e ν
    simp [a2, a4] at this
  · intro e
    have := congrFun e μ
    simp [a1, a3] at this
theorem sum_ite_eq_of_mem {β : Type} (C : Finset β) (q : β) (P : β → Prop) {d : DecidablePred P}
    (hP : ∀ x, P x ↔ x = q) (c : ℝ) (hq : q ∈ C) : ∑ x ∈ C, (if P x then c else 0) = c := by
  rw [Finset.sum_eq_single_of_mem q hq (fun b _ hb => if_neg (fun h => hb ((hP b).1 h)))]
  exact if_pos ((hP q).2 rfl)
theorem sum_ite_eq_of_not_mem {β : Type} (C : Finset β) (q : β) (P : β → Prop) {d : DecidablePred P}
    (hP : ∀ x, P x ↔ x = q) (c : ℝ) (hq : q ∉ C) : ∑ x ∈ C, (if P x then c else 0) = 0 :=
  Finset.sum_eq_zero fun x hx => if_neg (fun h => hq (((hP x).1 h) ▸ hx))
open Classical in
theorem levelShare_zero [NeZero n] [NeZero L] (hL : Odd L) (hN : 2 ≤ n * L) (a : ℝ) (S : Finset (TorusSite n))
    (W : TorusField (n * L)) (Z : (torusFrame L 0 n).FieldChain) (hZ : Z 0 = readAtLevel (torusFrame L 0 n) 0 W)
    (y : TorusSite (n * L)) :
    levelShare a L 0 (sitesInBlocks L S) y W =
      chainSiteShare a (cellsOfSites (torusFrame L 0 n) S) (torusSiteInFrame (torusFrame L 0 n) 0 y) Z := by
  have hp : ∀ i, (torusFrame L 0 n).period 0 i = n * L := period_depth
  let e : TorusSite (n * L) ≃ (torusFrame L 0 n).Site 0 :=
    ⟨torusSiteInFrame (torusFrame L 0 n) 0, toTorusSite (n * L), toTorusSite_torusSiteInFrame hp,
      torusSiteInFrame_toTorusSite hp⟩
  have h2 : Finset.range (torusFrame L 0 n).depth = ∅ := rfl
  unfold chainSiteShare
  rw [h2, Finset.sum_empty, mul_zero, add_zero]
  show ∑ p ∈ plaquettesIn (sitesInBlocks L S),
      (((plaquetteVertices p.1 p.2.1 p.2.2).count y : ℕ) : ℝ) / 4 * plaquetteEnergy W p.1 p.2.1 p.2.2 = _
  refine Finset.sum_equiv (e.prodCongr (Equiv.refl _)) (fun p => mem_plaquettesIn_iff hL S p) ?_
  rintro ⟨x, μ, ν⟩ hpl
  have hlt : μ < ν := by
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hpl
    exact hpl.1
  refine congrArg₂ (· * ·) ?_ ?_
  · have hb : ∀ x' : (torusFrame L 0 n).Site 0,
        (ancestorSite (F := torusFrame L 0 n) (torusFrame L 0 n).depth x' =
          torusSiteInFrame (torusFrame L 0 n) 0 y) ↔
          x' = torusSiteInFrame (torusFrame L 0 n) 0 y :=
      fun x' => iff_of_eq (congrArg (· = _) (ancestorSite_self x'))
    have hm : torusSiteInFrame (torusFrame L 0 n) 0 y ∈
        plaquetteCorners ((torusSiteInFrame (torusFrame L 0 n) 0 x, μ, ν) :
          (torusFrame L 0 n).Site 0 × Fin 4 × Fin 4) ↔
          y ∈ plaquetteVertices x μ ν := by
      rw [mem_plaquetteCorners_iff, toTorusSite_torusSiteInFrame hp]
    show (((plaquetteVertices x μ ν).count y : ℕ) : ℝ) / 4 = _
    rw [(nodup_plaquetteVertices hN x hlt).count]
    by_cases hy : y ∈ plaquetteVertices x μ ν
    · rw [if_pos hy]
      refine Eq.trans ?_ (sum_ite_eq_of_mem _ _ _ hb (1 / 4) (hm.2 hy)).symm
      norm_num
    · rw [if_neg hy]
      refine Eq.trans ?_ (sum_ite_eq_of_not_mem _ _ _ hb (1 / 4) (fun h => hy (hm.1 h))).symm
      norm_num
  · show plaquetteEnergy W x μ ν = 1 - ((plaquetteHolonomy (Z 0) ((torusSiteInFrame (torusFrame L 0 n) 0 x, μ, ν) :
        (torusFrame L 0 n).Site 0 × Fin 4 × Fin 4) : UnitQuaternion) : ℍ[ℝ]).re
    rw [hZ, plaquetteHolonomy_readAtLevel hp, toTorusSite_torusSiteInFrame hp]
    rfl
end Zero
section Lower
variable {L n : ℕ}
theorem readAtLevel_toLower {k : ℕ} (W : TorusField (n * L)) (s : (upperFrame L k n).Site (k + 1)) (i : Fin 4) :
    readAtLevel (lowerFrame L k n) (k + 1) W (toLower (k + 1) s) i = readAtLevel (upperFrame L k n) (k + 1) W s i := by
  have hc := siteCoords_toLower (L := L) (k := k) (n := n) le_rfl s
  show W (fun j => ((siteCoords (toLower (k + 1) s) j : ℤ) : ZMod (n * L))) i =
    W (fun j => ((siteCoords s j : ℤ) : ZMod (n * L))) i
  rw [hc]
theorem torusSiteInFrame_upper {k : ℕ} (y : TorusSite (n * L)) :
    torusSiteInFrame (upperFrame L k n) (k + 1) y = toUpper (k + 1) (torusSiteInFrame (lowerFrame L k n) (k + 1) y) := by
  funext i
  exact (cast_intCast_of_eq _ _ (period_upper_eq (L := L) (k := k) (n := n) (j := k + 1) le_rfl i).symm _).symm
theorem exists_chain_levelShare [NeZero n] [NeZero L] (hlv : minimalChainExistenceStatement) (hL : Odd L)
    (hN : 2 ≤ n * L) (a : ℝ) (ha : 0 ≤ a) (S : Finset (TorusSite n)) (W : TorusField (n * L)) (t : ℕ) :
    ∃ Z : (torusFrame L t n).FieldChain, Z t = readAtLevel (torusFrame L t n) t W ∧
      chainActionBelow a (cellsOfSites (torusFrame L t n) S) Z ≤
        minimalAction a (cellsOfSites (torusFrame L t n) S) t (readAtLevel (torusFrame L t n) t W) ∧
      ∀ y : TorusSite (n * L), levelShare a L t (sitesInBlocks L S) y W =
        chainSiteShare a (cellsOfSites (torusFrame L t n) S) (torusSiteInFrame (torusFrame L t n) t y) Z := by
  cases t with
  | zero =>
    obtain ⟨Z, hZ, ht, _⟩ := exists_chain_minimalAction hlv a ha (cellsOfSites (torusFrame L 0 n) S) 0
      (readAtLevel (torusFrame L 0 n) 0 W)
    exact ⟨Z, hZ, ht.le, fun y => levelShare_zero hL hN a S W Z hZ y⟩
  | succ k =>
    have hm := sitesCorrespond_sitesInBlocks (k := k) hL S
    have hex : ∃ X, IsMinimalChain a (cellsOfSites (upperFrame L k n) (sitesInBlocks L S))
        (readAtLevel (upperFrame L k n) (k + 1) W) X := by
      obtain ⟨X, hX, -⟩ := (hlv (upperFrame L k n) a (cellsOfSites (upperFrame L k n) (sitesInBlocks L S)) ha).2.2.2
        (readAtLevel (upperFrame L k n) (k + 1) W)
      exact ⟨X, hX⟩
    have hX₀ := hex.choose_spec
    set X₀ := hex.choose with hX₀d
    have hA : lowerChain X₀ (k + 1) = readAtLevel (lowerFrame L k n) (k + 1) W := by
      funext s i
      have h1 : X₀ (k + 1) = readAtLevel (upperFrame L k n) (k + 1) W := hX₀.1
      show X₀ (k + 1) (toUpper (k + 1) s) i = _
      rw [h1, ← readAtLevel_toLower, toLower_toUpper le_rfl]
    refine ⟨lowerChain X₀, hA, ?_, fun y => ?_⟩
    · rw [chainActionBelow_lowerChain hm]
      obtain ⟨Z1, hZ1, ht, _⟩ := exists_chain_minimalAction hlv a ha (cellsOfSites (lowerFrame L k n) S) (k + 1)
        (readAtLevel (lowerFrame L k n) (k + 1) W)
      have hB : liftChain Z1 (upperFrame L k n).top = readAtLevel (upperFrame L k n) (k + 1) W := by
        funext s i
        show Z1 (k + 1) (toLower (k + 1) s) i = _
        rw [hZ1]
        exact readAtLevel_toLower W s i
      have h1 := hX₀.2 (liftChain Z1) hB
      rw [chainAction_liftChain hm] at h1
      exact h1.trans ht.le
    · have e1 : levelShare a L (k + 1) (sitesInBlocks L S) y W =
          cellShare a (cellsOfSites (upperFrame L k n) (sitesInBlocks L S))
            (torusSiteInFrame (upperFrame L k n) (k + 1) y) X₀ :=
        dif_pos hex
      rw [e1, torusSiteInFrame_upper]
      exact (cellShare_congr a _ X₀ (liftChain (lowerChain X₀))
        (fun j hj => (liftChain_lowerChain X₀ hj).symm)).trans (cellShare_liftChain hm a (lowerChain X₀) _)
end Lower
end LevelShare
open LevelShare in
theorem levelShareSplits_holds (hlv : minimalChainExistenceStatement) : LevelShareSplits := by
  intro a δ L _ lam ρ σA cg N ha hL hch t n _ S V s Y hn hs hsσ hS hc hY
  obtain ⟨-, -, -, -, -, -, -, -, main⟩ := hch
  have hn2 : 2 ≤ n := by omega
  have hN : 2 ≤ n * L := by
    have : 0 < L := hL.pos
    nlinarith
  have hall := main (torusFrame L t n) 1024 (cellsOfSites (torusFrame L t n) S) rfl
    (isAdmissibleAmbient_torusFrame hn) le_rfl (isOrthantRegular_torusFrame hS) s
    (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) hs hsσ (isCold_torusFrame hc)
  obtain ⟨h1, -, h3, -⟩ := hall
  obtain ⟨w0, hw0, -⟩ := h1
  have hw : ∃ w, IsMinimizingChart a (cellsOfSites (torusFrame L t n) S)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ w :=
    ⟨w0, hw0.1, fun b hb => (hw0.2.1 b hb).trans (min_le_left _ _), hw0.2.2⟩
  have hcoord : minimizingCoordinates a (cellsOfSites (torusFrame L t n) S)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ = hw.choose := dif_pos hw
  have hspec := hw.choose_spec
  rw [← hcoord] at hspec
  have hp : ∀ i, (torusFrame L t n).period t i = n * L := LevelShare.period_depth
  have hread : readAtLevel (torusFrame L t n) t (minimizingField a ρ L t S V) =
      chartedField (minimizingCoordinates a (cellsOfSites (torusFrame L t n) S)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by
    funext x i
    exact congrArg (fun z => chartedField (minimizingCoordinates a (cellsOfSites (torusFrame L t n) S)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) z i)
      (torusSiteInFrame_toTorusSite hp x)
  have hW : ∀ W', blockEnergy a (cellsOfSites (torusFrame L t n) S) (torusFrame L t n).depth
        (readAtLevel (torusFrame L t n) t (minimizingField a ρ L t S V))
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ≤
      blockEnergy a (cellsOfSites (torusFrame L t n) S) (torusFrame L t n).depth W'
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by
    rw [hread]
    exact hspec.2.2
  obtain ⟨Z, hZ, hlow, hsh⟩ := exists_chain_levelShare hlv hL hN a ha.le S (minimizingField a ρ L t S V) t
  have hmin := isMinimalChain_of_below (F := torusFrame L t n) hlv a ha.le (cellsOfSites (torusFrame L t n) S)
    (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
    (readAtLevel (torusFrame L t n) t (minimizingField a ρ L t S V)) hW Z hZ hlow
  have hlo : ∀ j, j ≤ (torusFrame L t n).depth →
      Function.update Z (torusFrame L t n).top (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) j = Z j :=
    fun j hj => update_top_of_le_depth Z _ hj
  have e1 : levelShare a L (t + 1) S Y V = cellShare a (cellsOfSites (torusFrame L t n) S)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y)
      (Function.update Z (torusFrame L t n).top (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)) :=
    (h3.2.2.1 _ hmin _).symm
  rw [e1, cellShare_eq_sum_add hL]
  have s1 : ∑ y ∈ sitesInBlocks L {Y}, chainSiteShare a (cellsOfSites (torusFrame L t n) S)
        (torusSiteInFrame (torusFrame L t n) t y)
        (Function.update Z (torusFrame L t n).top (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)) =
      ∑ y ∈ sitesInBlocks L {Y}, levelShare a L t (sitesInBlocks L S) y (minimizingField a ρ L t S V) :=
    Finset.sum_congr rfl fun y _ => (chainSiteShare_congr a _ _ _ Z hlo).trans (hsh y).symm
  rw [s1]
  congr 2
  have hf : ∀ b : TorusBond n,
      (fun c : (torusFrame L t n).Cell × Fin 4 => blockFit (j := t)
        (Function.update Z (torusFrame L t n).top (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) t)
        (Function.update Z (torusFrame L t n).top (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) (t + 1))
          c)
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top b.1, b.2) =
        blockFitAt L (minimizingField a ρ L t S V) V b := by
    intro b
    have g1 : Function.update Z (torusFrame L t n).top
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) t =
        readAtLevel (torusFrame L t n) t (minimizingField a ρ L t S V) := (hlo t le_rfl).trans hZ
    have g2 : Function.update Z (torusFrame L t n).top
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) (t + 1) =
        readAtLevel (torusFrame L t n) (t + 1) V := Function.update_self _ _ _
    show blockFit (j := t) _ _ _ = _
    rw [g1, g2]
    exact blockFit_readAtLevel _ V b
  exact sum_top_bonds hn2 S Y hY _ _ hf
end YangMills.Construction.ClusterExpansionOfAStep
end
