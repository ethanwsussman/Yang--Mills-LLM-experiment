import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfTheSharesProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets
variable {F : BlockFrame}
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem period_depth (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by simp [BlockFrame.period]
theorem mem_finiteCells (hext : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
def halfSide (L : ℕ) : ℤ := ((L : ℤ) - 1) / 2
theorem mem_centredCube_iff {L : ℕ} (h : Fin 4 → ℤ) :
    h ∈ centredCube L ↔ ∀ i, -halfSide L ≤ h i ∧ h i ≤ halfSide L := by apply _root_.YangMills.Construction.LatticePaths.mem_centredCube_iff <;> assumption
theorem siteCoords_offset (hL : Odd F.blockSide) (hext : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (i : Fin 4) :
    ∃ e : ℤ, siteCoords (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) i =
      (F.blockSide : ℤ) * siteCoords z i + h i + (F.extent i : ℤ) * F.blockSide * e ∧ (e = 0 ∨ e = 1) := by
  obtain ⟨k, hk⟩ := hL
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hn : (2 : ℤ) ≤ F.extent i := by exact_mod_cast hext i
  have hne1 : NeZero (F.period F.top i) := ⟨by
    rw [period_top]
    have := hext i
    omega⟩
  have hh' := ((mem_centredCube_iff h).mp hh) i
  have hk2 : halfSide F.blockSide = k := by
    unfold halfSide
    rw [hLz]
    omega
  rw [hk2] at hh'
  set c : ℤ := siteCoords z i with hc
  have hv : c = ((z i).val : ℤ) := (ZMod.natCast_val (z i)).symm
  have hc1 : c < F.extent i := by
    rw [hv]
    have h1 := ZMod.val_lt (z i)
    have h2 := period_top (F := F) i
    omega
  set w : ℤ := (F.blockSide : ℤ) * c + h i with hw
  set P : ℤ := (F.extent i : ℤ) * F.blockSide with hP
  have hcast : (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) i =
      (w : ZMod (F.period F.depth i)) := by
    simp only [cellCentre, siteOfCoords, Pi.add_apply, top_sub_depth, pow_one, hw, hc, siteCoords]
    push_cast
    rfl
  have hval : siteCoords (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) i = w % P := by
    unfold siteCoords
    rw [hcast, ZMod.coe_intCast, period_depth]
    push_cast
    rfl
  rcases lt_or_ge w 0 with hneg | hnn
  · refine ⟨1, ?_, Or.inr rfl⟩
    rw [hval]
    have e1 : w % P = w + P := by
      have hb : 0 ≤ w + P ∧ w + P < P := by
        constructor
        · simp only [hP, hw]
          nlinarith
        · linarith
      have := Int.emod_eq_of_lt hb.1 hb.2
      rw [← this, Int.add_emod_right]
    rw [e1]
    simp only [hw, hP]
    ring
  · refine ⟨0, ?_, Or.inl rfl⟩
    rw [hval]
    have hlt : w < P := by
      simp only [hw, hP]
      nlinarith
    rw [Int.emod_eq_of_lt hnn hlt]
    simp only [hw]
    ring
theorem extent_cast_eq_zero (i : Fin 4) : ((F.extent i : ℕ) : ZMod (F.period F.top i)) = 0 :=
  (ZMod.natCast_eq_zero_iff _ _).mpr (by rw [period_top])
theorem enclosingCell_offset (hL : Odd F.blockSide) (hext : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = z := by
  funext i
  obtain ⟨e, he, _⟩ := siteCoords_offset hL hext z h hh i
  obtain ⟨k, hk⟩ := hL
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hk2 : halfSide F.blockSide = k := by
    unfold halfSide
    rw [hLz]
    omega
  have hh' := ((mem_centredCube_iff h).mp hh) i
  rw [hk2] at hh'
  have hLpos : (0 : ℤ) < F.blockSide := by omega
  change (((siteCoords (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) i +
    ((F.blockSide : ℤ) ^ (F.top - F.depth) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - F.depth) : ℤ) :
      ZMod (F.period F.top i)) = z i
  rw [top_sub_depth, pow_one, he]
  have e1 : ((F.blockSide : ℤ) - 1) / 2 = k := by
    rw [hLz]
    omega
  rw [e1]
  have e2 : ((F.blockSide : ℤ) * siteCoords z i + h i + (F.extent i : ℤ) * F.blockSide * e + k) /
      (F.blockSide : ℤ) = siteCoords z i + (F.extent i : ℤ) * e := by
    have e3 : (F.blockSide : ℤ) * siteCoords z i + h i + (F.extent i : ℤ) * F.blockSide * e + k =
        (h i + k) + (F.blockSide : ℤ) * (siteCoords z i + (F.extent i : ℤ) * e) := by ring
    rw [e3, Int.add_mul_ediv_left _ _ hLpos.ne']
    have : (h i + k) / (F.blockSide : ℤ) = 0 :=
      Int.ediv_eq_zero_of_lt (by linarith [hh'.1]) (by linarith [hh'.2])
    rw [this, zero_add]
  rw [e2]
  push_cast
  rw [extent_cast_eq_zero, zero_mul, add_zero]
  exact ZMod.intCast_zmod_cast (z i)
theorem cellOffset_offset (hL : Odd F.blockSide) (hext : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) :
    cellOffset (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = h := by
  funext i
  unfold cellOffset
  rw [enclosingCell_offset hL hext z h hh, add_sub_cancel_left]
  obtain ⟨k, hk⟩ := hL
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hk2 : halfSide F.blockSide = k := by
    unfold halfSide
    rw [hLz]
    omega
  have hh' := ((mem_centredCube_iff h).mp hh) i
  rw [hk2] at hh'
  have hne0 : NeZero (F.period F.depth i) := ⟨by
    rw [period_depth]
    have := hext i
    have h1 : 0 < F.blockSide := by omega
    have h2 : 0 < F.extent i := by omega
    exact (Nat.mul_pos h2 h1).ne'⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  rw [period_depth]
  have hn : (2 : ℤ) ≤ F.extent i := by exact_mod_cast hext i
  have h5 : (2 : ℤ) * (2 * k + 1) ≤ (F.extent i : ℤ) * (F.blockSide : ℤ) := by
    rw [hLz]
    nlinarith
  simp only [Set.mem_Ioc]
  push_cast
  constructor <;> linarith [hh'.1, hh'.2]
theorem unitStep_top_ne_zero (hext : ∀ i, 2 ≤ F.extent i) (i : Fin 4) : (unitStep F.top i : F.Cell) ≠ 0 := by apply _root_.YangMills.Construction.GaugeFixing.unitStep_top_ne_zero <;> assumption
theorem offset_add_unitStep (z : F.Cell) (h : Fin 4 → ℤ) (i : Fin 4) :
    (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i : F.Site F.depth) =
      cellCentre F.depth z + siteOfCoords F.depth (h + Pi.single i 1) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem cellCentre_add_unitStep (hext : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (i : Fin 4) :
    (cellCentre F.depth (z + unitStep F.top i) : F.Site F.depth) =
      cellCentre F.depth z + siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ)) := by
  funext l
  simp only [cellCentre, siteOfCoords, Pi.add_apply, top_sub_depth, pow_one]
  rw [← Int.cast_add, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have e0 : ((siteCoords (z + unitStep F.top i) l : ℤ) : ZMod (F.period F.top l)) =
      ((siteCoords z l + (Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod (F.period F.top l)) := by
    simp only [siteCoords, unitStep, siteOfCoords, Pi.add_apply]
    rw [ZMod.intCast_zmod_cast]
    push_cast
    first | rfl | rw [ZMod.intCast_zmod_cast]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at e0
  obtain ⟨w, hw⟩ := e0
  refine ⟨w, ?_⟩
  have hsingle : (Pi.single i (F.blockSide : ℤ) : Fin 4 → ℤ) l =
      (F.blockSide : ℤ) * (Pi.single i 1 : Fin 4 → ℤ) l := by
    by_cases hl : l = i
    · subst hl
      simp
    · simp [Pi.single_eq_of_ne hl]
  rw [hsingle, period_depth]
  rw [period_top] at hw
  push_cast
  linear_combination (F.blockSide : ℤ) * hw
theorem isCrossingBond_iff (hL : Odd F.blockSide) (hext : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (i : Fin 4) :
    IsCrossingBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), i) ↔
      h i = halfSide F.blockSide := by
  unfold IsCrossingBond
  simp only
  rw [enclosingCell_offset hL hext z h hh]
  have hc := (mem_centredCube_iff h).mp hh
  constructor
  · intro hcr
    by_contra hne
    apply hcr
    have hin : h + Pi.single i 1 ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro l
      by_cases hl : l = i
      · subst hl
        simp only [Pi.add_apply, Pi.single_eq_same]
        have := hc l
        omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        exact hc l
    rw [offset_add_unitStep, enclosingCell_offset hL hext z _ hin]
  · intro he hcell
    set h' : Fin 4 → ℤ := h + Pi.single i (1 - (F.blockSide : ℤ)) with hh'
    obtain ⟨k, hk⟩ := hL
    have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    have hk2 : halfSide F.blockSide = k := by
      unfold halfSide
      rw [hLz]
      omega
    have hin : h' ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro l
      by_cases hl : l = i
      · subst hl
        simp only [hh', Pi.add_apply, Pi.single_eq_same, he]
        rw [hk2, hLz]
        constructor <;> linarith
      · simp only [hh', Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        exact hc l
    have e : (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i : F.Site F.depth) =
        cellCentre F.depth (z + unitStep F.top i) + siteOfCoords F.depth h' := by
      rw [cellCentre_add_unitStep hext, offset_add_unitStep]
      have e2 : (siteOfCoords F.depth (h + Pi.single i 1) : F.Site F.depth) =
          siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ)) + siteOfCoords F.depth h' := by
        funext l
        by_cases hl : l = i
        · subst hl
          simp [siteOfCoords, hh']
          ring
        · simp [siteOfCoords, hh', Pi.single_eq_of_ne hl]
      rw [e2, add_assoc]
    rw [e, enclosingCell_offset ⟨k, hk⟩ hext _ h' hin] at hcell
    have : (unitStep F.top i : F.Cell) = 0 := by
      have h2 : z + unitStep F.top i = z + 0 := by
        rw [add_zero]
        exact hcell
      exact add_left_cancel h2
    exact unitStep_top_ne_zero hext i this
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
def distFromOne (g : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - 1‖
theorem distFromOne_nonneg (g : UnitQuaternion) : 0 ≤ distFromOne g := norm_nonneg _
theorem distFromOne_one : distFromOne (1 : UnitQuaternion) = 0 := by simp [distFromOne]
theorem distFromOne_mul (g h : UnitQuaternion) : distFromOne (g * h) ≤ distFromOne g + distFromOne h := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
theorem distFromOne_inv (g : UnitQuaternion) : distFromOne g⁻¹ = distFromOne g := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem distFromOne_conj (v g : UnitQuaternion) : distFromOne (v * g * v⁻¹) = distFromOne g := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem exp_imaginary_eq (w : imaginaryQuaternions) : NormedSpace.exp (w : ℍ[ℝ]) =
    ((Real.cos ‖(w : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) + (Real.sin ‖(w : ℍ[ℝ])‖ / ‖(w : ℍ[ℝ])‖) • (w : ℍ[ℝ]) :=
  Quaternion.exp_of_re_eq_zero _ w.2
theorem distFromOne_expUnit_le (w : imaginaryQuaternions) : distFromOne (expUnit w) ≤ ‖w‖ := by
  unfold distFromOne
  have hn : ‖w‖ = ‖(w : ℍ[ℝ])‖ := rfl
  rw [hn]
  set q : ℍ[ℝ] := (w : ℍ[ℝ]) with hq
  set n : ℝ := ‖q‖ with hnn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hre : q.re = 0 := w.2
  change ‖NormedSpace.exp q - 1‖ ≤ n
  have hsq : ‖NormedSpace.exp q - 1‖ ^ 2 = 2 - 2 * Real.cos n := by
    have hu : ‖NormedSpace.exp q‖ = 1 := by
      rw [Quaternion.norm_exp, hre]
      simp
    have hr : (NormedSpace.exp q).re = Real.cos n := by
      rw [exp_imaginary_eq w]
      simp [hre, ← hq, ← hnn]
    have e1 : ‖NormedSpace.exp q - 1‖ ^ 2 = Quaternion.normSq (NormedSpace.exp q - 1) := by
      rw [Quaternion.normSq_eq_norm_mul_self, sq]
    have e2 : ‖NormedSpace.exp q‖ ^ 2 = Quaternion.normSq (NormedSpace.exp q) := by
      rw [Quaternion.normSq_eq_norm_mul_self, sq]
    rw [hu] at e2
    rw [e1]
    have e3 : Quaternion.normSq (NormedSpace.exp q - 1) =
        Quaternion.normSq (NormedSpace.exp q) - 2 * (NormedSpace.exp q).re + 1 := by
      simp only [Quaternion.normSq_def', Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub,
        Quaternion.imK_sub, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
      ring
    rw [e3, ← e2, hr]
    ring
  have hc : 1 - n ^ 2 / 2 ≤ Real.cos n := Real.one_sub_sq_div_two_le_cos
  have h2 : ‖NormedSpace.exp q - 1‖ ^ 2 ≤ n ^ 2 := by
    rw [hsq]
    linarith
  exact abs_le_of_sq_le_sq' h2 hn0 |>.2
theorem expUnit_inj_of_norm_le_one {w w' : imaginaryQuaternions} (h : expUnit w = expUnit w')
    (hw : ‖w‖ ≤ 1) (hw' : ‖w'‖ ≤ 1) : w = w' := by
  have h0 : NormedSpace.exp (w : ℍ[ℝ]) = NormedSpace.exp (w' : ℍ[ℝ]) := congrArg Subtype.val h
  rw [exp_imaginary_eq w, exp_imaginary_eq w'] at h0
  have hn : ‖w‖ = ‖(w : ℍ[ℝ])‖ := rfl
  have hn' : ‖w'‖ = ‖(w' : ℍ[ℝ])‖ := rfl
  rw [← hn, ← hn'] at h0
  have hre := congrArg (fun q : ℍ[ℝ] => q.re) h0
  have hw0 : (w : ℍ[ℝ]).re = 0 := w.2
  have hw0' : (w' : ℍ[ℝ]).re = 0 := w'.2
  simp [hw0, hw0'] at hre
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have heq : ‖w‖ = ‖w'‖ :=
    Real.injOn_cos ⟨norm_nonneg _, hw.trans hpi⟩ ⟨norm_nonneg _, hw'.trans hpi⟩ hre
  rw [heq] at h0
  rcases eq_or_lt_of_le (norm_nonneg w') with h00 | hpos
  · have a1 : w = 0 := by
      rw [← norm_eq_zero, heq]
      exact h00.symm
    have a2 : w' = 0 := by
      rw [← norm_eq_zero]
      exact h00.symm
    rw [a1, a2]
  · have hs : 0 < Real.sin ‖w'‖ :=
      Real.sin_pos_of_pos_of_lt_pi hpos (lt_of_le_of_lt hw' (by linarith [Real.pi_gt_three]))
    have hc : Real.sin ‖w'‖ / ‖w'‖ ≠ 0 := (div_pos hs hpos).ne'
    have h1 := add_left_cancel h0
    have h2 := smul_right_injective _ hc h1
    exact Subtype.ext h2
def stepShift (st : PathStep) : Fin 4 → ℤ := if st.2 then Pi.single st.1 1 else - Pi.single st.1 1
def walkTarget (u : Fin 4 → ℤ) : List PathStep → Fin 4 → ℤ
  | [] => u
  | st :: r => walkTarget (u + stepShift st) r
def WalkStaysIn (M : ℕ) (u : Fin 4 → ℤ) : List PathStep → Prop
  | [] => True
  | st :: r => u + stepShift st ∈ centredCube M ∧ WalkStaysIn M (u + stepShift st) r
theorem walkTarget_append (u : Fin 4 → ℤ) (l l' : List PathStep) :
    walkTarget u (l ++ l') = walkTarget (walkTarget u l) l' := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih => exact ih _
theorem walkStaysIn_append {M : ℕ} {u : Fin 4 → ℤ} {l l' : List PathStep} (h : WalkStaysIn M u l)
    (h' : WalkStaysIn M (walkTarget u l) l') : WalkStaysIn M u (l ++ l') := by
  induction l generalizing u with
  | nil => exact h'
  | cons st r ih => exact ⟨h.1, ih h.2 h'⟩
theorem stepShift_flip (st : PathStep) : stepShift (st.1, !st.2) = - stepShift st := by apply _root_.YangMills.Construction.LatticePaths.stepDisplacement_flip <;> assumption
theorem reversePath_cons (st : PathStep) (r : List PathStep) :
    reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
  simp [reversePath]
theorem walkStaysIn_reversePath {M : ℕ} {u : Fin 4 → ℤ} {l : List PathStep} (hu : u ∈ centredCube M)
    (h : WalkStaysIn M u l) :
    WalkStaysIn M (walkTarget u l) (reversePath l) ∧ walkTarget (walkTarget u l) (reversePath l) = u := by
  induction l generalizing u with
  | nil => exact ⟨trivial, rfl⟩
  | cons st r ih =>
    obtain ⟨h1, h2⟩ := ih h.1 h.2
    have hend : walkTarget (u + stepShift st) r = walkTarget u (st :: r) := rfl
    rw [← hend, reversePath_cons]
    refine ⟨walkStaysIn_append h1 ?_, ?_⟩
    · rw [h2]
      refine ⟨?_, trivial⟩
      rw [stepShift_flip]
      simpa using hu
    · rw [walkTarget_append, h2]
      simp [walkTarget, stepShift_flip]
theorem walkStaysIn_replicate {M : ℕ} (d : Fin 4) (b : Bool) (n : ℕ) {u : Fin 4 → ℤ}
    (hu : u ∈ centredCube M) (hv : u + (n : ℤ) • stepShift (d, b) ∈ centredCube M) :
    WalkStaysIn M u (List.replicate n (d, b)) ∧
      walkTarget u (List.replicate n (d, b)) = u + (n : ℤ) • stepShift (d, b) := by
  induction n generalizing u with
  | zero => exact ⟨trivial, by simp [walkTarget]⟩
  | succ n ih =>
    have hmem : u + stepShift (d, b) ∈ centredCube M := by
      unfold centredCube at hu hv ⊢
      rw [Fintype.mem_piFinset] at hu hv ⊢
      intro l
      have h1 := hu l
      have h2 := hv l
      simp only [Finset.mem_Icc, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
      by_cases hl : l = d
      · subst hl
        cases b <;> simp [stepShift] at h2 ⊢ <;> constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
      · cases b <;> simp [stepShift, Pi.single_eq_of_ne hl] at h2 ⊢ <;> exact h1
    have e : u + ((n + 1 : ℕ) : ℤ) • stepShift (d, b) =
        (u + stepShift (d, b)) + (n : ℤ) • stepShift (d, b) := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e] at hv
    obtain ⟨a1, a2⟩ := ih hmem hv
    refine ⟨⟨hmem, a1⟩, ?_⟩
    rw [e]
    exact a2
end YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets
end
