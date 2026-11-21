import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import YangMills.Construction.ClusterExpansionOfAStep.LumpsAreFibres
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOverContoursOfAFormForm
import YangMills.Construction.HoleBesideASecondHole.MeansAtABondProof
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusContours
open BlockAverages LumpContours TorusLumps
section Paths
variable {F : BlockFrame} {j : ℕ}
def pathEndpoint : F.Site j → List PathStep → F.Site j
  | x, [] => x
  | x, st :: r => pathEndpoint (x + stepDisplacement j st) r
theorem pathEndpoint_append (x : F.Site j) (l l' : List PathStep) :
    pathEndpoint x (l ++ l') = pathEndpoint (pathEndpoint x l) l' := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih => exact ih _
theorem stepDisplacement_flip (st : PathStep) :
    (stepDisplacement j (st.1, !st.2) : F.Site j) = - stepDisplacement j st := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.stepDisplacement_flip <;> assumption
theorem pathEndpoint_reversePath (x : F.Site j) (l : List PathStep) :
    pathEndpoint (pathEndpoint x l) (reversePath l) = x := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    rw [this, pathEndpoint_append]
    simp only [pathEndpoint]
    rw [ih]
    simp [stepDisplacement_flip]
theorem pathEndpoint_replicate (x : F.Site j) (m : ℕ) (st : PathStep) :
    pathEndpoint x (List.replicate m st) = x + m • stepDisplacement j st := by
  induction m generalizing x with
  | zero => simp [pathEndpoint]
  | succ m ih =>
    simp only [List.replicate_succ, pathEndpoint]
    rw [ih, succ_nsmul]
    abel
theorem siteOfCoords_add (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_neg (a : Fin 4 → ℤ) : (siteOfCoords j (-a) : F.Site j) = - siteOfCoords j a := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_map_neg <;> assumption
theorem siteOfCoords_zero : (siteOfCoords j 0 : F.Site j) = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem nsmul_siteOfCoords (m : ℕ) (a : Fin 4 → ℤ) :
    m • (siteOfCoords j a : F.Site j) = siteOfCoords j (fun i => (m : ℤ) * a i) := by
  funext i
  simp [siteOfCoords]
theorem axisSegment_eq (k : Fin 4) (c : ℤ) :
    (c.natAbs • stepDisplacement j (k, decide (0 ≤ c)) : F.Site j) = siteOfCoords j (Pi.single k c) := by
  by_cases hc : 0 ≤ c
  · have hc' : ((c.natAbs : ℕ) : ℤ) = c := Int.natAbs_of_nonneg hc
    simp only [hc, decide_true, stepDisplacement, if_true, BlockAverages.unitStep, nsmul_siteOfCoords]
    congr 1
    funext i
    by_cases h : i = k
    · subst h
      simp [hc']
    · simp [h]
  · have hc' : ((c.natAbs : ℕ) : ℤ) = - c := by omega
    simp only [hc, decide_false, stepDisplacement, Bool.false_eq_true, if_false, BlockAverages.unitStep,
      smul_neg, nsmul_siteOfCoords]
    rw [← siteOfCoords_neg]
    congr 1
    funext i
    by_cases h : i = k
    · subst h
      simp [hc']
    · simp [Pi.single_apply, h]
theorem siteOfCoords_sum_single (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    (siteOfCoords j (Pi.single (π 0) (h (π 0))) + siteOfCoords j (Pi.single (π 1) (h (π 1))) +
      siteOfCoords j (Pi.single (π 2) (h (π 2))) + siteOfCoords j (Pi.single (π 3) (h (π 3))) : F.Site j) =
      siteOfCoords j h := by
  simp only [← siteOfCoords_add]
  congr 1
  funext i
  have : ∑ k : Fin 4, (Pi.single (π k) (h (π k)) : Fin 4 → ℤ) i = h i := by
    rw [Equiv.sum_comp π fun k => (Pi.single k (h k) : Fin 4 → ℤ) i]
    simp [Pi.single_apply]
  rw [← this, Fin.sum_univ_four]
  simp
theorem axisPath_eq (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π = List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0))) ++
      (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1))) ++
      (List.replicate (h (π 2)).natAbs (π 2, decide (0 ≤ h (π 2))) ++
      List.replicate (h (π 3)).natAbs (π 3, decide (0 ≤ h (π 3))))) := by apply _root_.YangMills.Construction.LatticePaths.axisPath_eq <;> assumption
theorem pathEndpoint_axisPath (x : F.Site j) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathEndpoint x (axisPath h π) = x + siteOfCoords j h := by
  rw [axisPath_eq]
  simp only [pathEndpoint_append, pathEndpoint_replicate, axisSegment_eq]
  rw [← siteOfCoords_sum_single h π]
  abel
theorem pathHolonomy_gaugeTransform (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (x : F.Site j)
    (l : List PathStep) :
    pathHolonomy (gaugeTransform γ X) x l = γ x * pathHolonomy X x l * (γ (pathEndpoint x l))⁻¹ := by
  induction l generalizing x with
  | nil => simp [pathHolonomy, pathEndpoint]
  | cons st r ih =>
    simp only [pathHolonomy, pathEndpoint]
    rw [ih]
    rcases st with ⟨i, b⟩
    cases b
    · simp [linkValue, stepDisplacement, gaugeTransform, mul_assoc, sub_eq_add_neg]
    · simp [linkValue, stepDisplacement, gaugeTransform, mul_assoc]
theorem norm_coe_unitQuaternion (u : UnitQuaternion) : ‖((u : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem plaquetteDefect_gaugeTransform (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (gaugeTransform γ X) p = plaquetteDefect X p := by apply _root_.YangMills.Construction.GaugeFixing.plaquetteDefect_gaugeTransform <;> assumption
end Paths
section EvaluationMaps
variable {F : BlockFrame} {j m : ℕ}
theorem intCast_cast_add_of_eq {p q : ℕ} (h : p = q) [NeZero p] (a b : ZMod p) :
    ((((a + b : ZMod p)).cast : ℤ) : ZMod q) = ((a.cast : ℤ) : ZMod q) + ((b.cast : ℤ) : ZMod q) := by apply _root_.YangMills.Construction.TorusLumps.castInt_add <;> assumption
theorem intCast_cast_intCast_of_eq {p q : ℕ} (h : p = q) [NeZero p] (z : ℤ) :
    ((((z : ZMod p)).cast : ℤ) : ZMod q) = (z : ZMod q) := by apply _root_.YangMills.Construction.TorusLumps.castInt_intCast <;> assumption
theorem toTorusSite_add [∀ i, NeZero (F.period j i)] (hp : ∀ i, F.period j i = m) (x x' : F.Site j) :
    (toTorusSite m (x + x') : TorusFields.TorusSite m) = toTorusSite m x + toTorusSite m x' := by
  funext k
  exact intCast_cast_add_of_eq (hp k) (x k) (x' k)
theorem toTorusSite_siteOfCoords [∀ i, NeZero (F.period j i)] (hp : ∀ i, F.period j i = m)
    (z : Fin 4 → ℤ) :
    (toTorusSite m (siteOfCoords j z : F.Site j) : TorusFields.TorusSite m) = TorusFields.siteOfInt z := by
  funext k
  exact intCast_cast_intCast_of_eq (hp k) (z k)
theorem siteOfInt_single (i : Fin 4) :
    (TorusFields.siteOfInt (Pi.single i 1) : TorusFields.TorusSite m) = TorusFields.unitStep m i := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
theorem toTorusSite_unitStep [∀ i, NeZero (F.period j i)] (hp : ∀ i, F.period j i = m) (i : Fin 4) :
    (toTorusSite m (BlockAverages.unitStep j i : F.Site j) : TorusFields.TorusSite m) =
      TorusFields.unitStep m i := by
  rw [BlockAverages.unitStep, toTorusSite_siteOfCoords hp, siteOfInt_single]
theorem intCast_siteCoords (x : F.Site j) [∀ i, NeZero (F.period j i)] (k : Fin 4) :
    ((siteCoords x k : ℤ) : ZMod (F.period j k)) = x k := by
  simp [siteCoords, ZMod.intCast_zmod_cast]
theorem siteOfCoords_siteCoords [∀ i, NeZero (F.period j i)] (x : F.Site j) :
    siteOfCoords j (siteCoords x) = x := by
  funext k
  exact intCast_siteCoords x k
end EvaluationMaps
section Frames
variable {F : BlockFrame} [∀ j i, NeZero (F.period j i)]
omit [∀ j i, NeZero (F.period j i)] in
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
omit [∀ j i, NeZero (F.period j i)] in
theorem period_depth (i : Fin 4) : F.period F.depth i = F.period F.top i * F.blockSide := by
  simp [BlockFrame.period, BlockFrame.top]
omit [∀ j i, NeZero (F.period j i)] in
theorem cellCentre_eq (y : F.Cell) :
    (cellCentre F.depth y : F.Site F.depth) =
      siteOfCoords F.depth fun i => (F.blockSide : ℤ) * siteCoords y i := by
  simp only [cellCentre, top_sub_depth, pow_one]
theorem cellCentre_siteOfCoords (z : Fin 4 → ℤ) :
    (cellCentre F.depth (siteOfCoords F.top z : F.Cell) : F.Site F.depth) =
      siteOfCoords F.depth fun i => (F.blockSide : ℤ) * z i := by
  rw [cellCentre_eq]
  funext k
  simp only [siteOfCoords]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_depth]
  have h1 : (((siteCoords (siteOfCoords F.top z : F.Cell) k : ℤ)) : ZMod (F.period F.top k)) =
      (z k : ZMod (F.period F.top k)) :=
    intCast_siteCoords _ k
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨c, ?_⟩
  push_cast
  linear_combination (F.blockSide : ℤ) * hc
theorem cellCentre_add_unitStep (y : F.Cell) (i : Fin 4) :
    (cellCentre F.depth (y + BlockAverages.unitStep F.top i) : F.Site F.depth) =
      cellCentre F.depth y + siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ)) := by
  have h : (y + BlockAverages.unitStep F.top i : F.Cell) = siteOfCoords F.top (siteCoords y + Pi.single i 1) := by
    rw [siteOfCoords_add, siteOfCoords_siteCoords]
    rfl
  rw [h, cellCentre_siteOfCoords, cellCentre_eq, ← siteOfCoords_add]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp [mul_add]
  · simp [hk]
omit [∀ j i, NeZero (F.period j i)] in
theorem siteOfCoords_minimalOffset {j : ℕ} (x x' : F.Site j) :
    siteOfCoords j (minimalOffset x x') = x' - x := by apply _root_.YangMills.Construction.BondMeans.siteOfCoords_minimalOffset <;> assumption
theorem pathEndpoint_contourPath (b : F.Cell → F.Site F.depth) (c : F.Cell × Fin 4) (ξ : Fin 4 → ℤ)
    (π : Equiv.Perm (Fin 4)) :
    pathEndpoint (b c.1) (contourPath b c ξ π) = b (c.1 + BlockAverages.unitStep F.top c.2) := by
  have h2 := pathEndpoint_reversePath (b (c.1 + BlockAverages.unitStep F.top c.2))
    (axisPath (minimalOffset (b (c.1 + BlockAverages.unitStep F.top c.2))
      (cellCentre F.depth (c.1 + BlockAverages.unitStep F.top c.2) + siteOfCoords F.depth ξ)) π)
  rw [pathEndpoint_axisPath, siteOfCoords_minimalOffset, add_sub_cancel] at h2
  have h3 : (F.blockSide • stepDisplacement F.depth (c.2, true) : F.Site F.depth) =
      siteOfCoords F.depth (Pi.single c.2 (F.blockSide : ℤ)) := by
    have := axisSegment_eq (F := F) (j := F.depth) c.2 (F.blockSide : ℤ)
    simpa using this
  unfold contourPath
  rw [pathEndpoint_append, pathEndpoint_append, pathEndpoint_axisPath, siteOfCoords_minimalOffset,
    add_sub_cancel, pathEndpoint_replicate, h3]
  rw [cellCentre_add_unitStep] at h2 ⊢
  convert h2 using 2
  abel
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_centredCube_iff {M : ℕ} {z : Fin 4 → ℤ} :
    z ∈ centredCube M ↔ ∀ i, -(((M : ℤ) - 1) / 2) ≤ z i ∧ z i ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem zero_mem_centredCube {M : ℕ} (hM : 1 ≤ M) : (0 : Fin 4 → ℤ) ∈ centredCube M := by
  rw [mem_centredCube_iff]
  intro i
  simp only [Pi.zero_apply]
  omega
omit [∀ j i, NeZero (F.period j i)] in
theorem siteAtOffset_eq (y : F.Cell) (z : Fin 4 → ℤ) :
    (siteAtOffset y z : F.Site F.depth) =
      siteOfCoords F.depth fun i => (F.blockSide : ℤ) * siteCoords y i + z i := by
  unfold siteAtOffset
  rw [cellCentre_eq]
  funext k
  simp [siteOfCoords]
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_sitesBelow_iff (y : F.Cell) (x : F.Site F.depth) :
    x ∈ sitesBelow F.depth y ↔ ∃ z ∈ centredCube F.blockSide, x = siteAtOffset y z := by
  simp only [sitesBelow, top_sub_depth, pow_one, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (siteAtOffset_eq y z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (siteAtOffset_eq y z).symm⟩
theorem exists_centredCube_of_isBaseChoice (hL : 1 ≤ F.blockSide) {J₀ : ℕ}
    {h : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth}
    (hb : IsBaseChoice J₀ h b) (y : F.Cell) : ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z := by
  by_cases hh : nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y
  · refine ⟨0, zero_mem_centredCube hL, ?_⟩
    rw [(hb y).1 hh, siteAtOffset, siteOfCoords_zero, add_zero]
  · exact (mem_sitesBelow_iff y _).mp ((hb y).2 hh).1
theorem contourMean_gaugeTransform (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth)))
    (γ : F.Site F.depth → UnitQuaternion) (b : F.Cell → F.Site F.depth)
    (W : F.GaugeField F.depth) (c : F.Cell × Fin 4) :
    contourMean J₀ h b (gaugeTransform γ W) c =
      ((γ (b c.1) : UnitQuaternion) : ℍ[ℝ]) * contourMean J₀ h b W c *
        (((γ (b (c.1 + BlockAverages.unitStep F.top c.2)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  unfold contourMean
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pathHolonomy_gaugeTransform, pathEndpoint_contourPath]
  simp only [Submonoid.coe_mul]
end Frames
section Step
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem stepBlockFrame_period_zero (i : Fin 4) : (stepBlockFrame L n).period 0 i = n * L := by
  show n * L ^ (0 + 1 - 0) = n * L
  simp
theorem stepBlockFrame_period_one (i : Fin 4) : (stepBlockFrame L n).period 1 i = n := by
  show n * L ^ (0 + 1 - 1) = n
  simp
theorem parentBlock_siteAtOffset (y : (stepBlockFrame L n).Cell) {z : Fin 4 → ℤ} (hz : z ∈ centredCube L) :
    parentBlock L (toTorusSite (n * L) (siteAtOffset y z : (stepBlockFrame L n).Site 0)) =
      toTorusSite n y := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [siteAtOffset_eq, toTorusSite_siteOfCoords (F := stepBlockFrame L n) (j := (stepBlockFrame L n).depth)
    (fun i => stepBlockFrame_period_zero i)]
  funext k
  have hzk := mem_centredCube_iff.mp hz k
  set Y : ℤ := siteCoords y k with hY
  set u : ℤ := (L : ℤ) * Y + z k with hu
  have hmod : ((((u : ZMod (n * L))).cast : ℤ)) = u % ((n * L : ℕ) : ℤ) := ZMod.coe_intCast u
  have hdiv : u % ((n * L : ℕ) : ℤ) = u - ((n * L : ℕ) : ℤ) * (u / ((n * L : ℕ) : ℤ)) := by
    have := Int.emod_add_mul_ediv u ((n * L : ℕ) : ℤ)
    linarith
  set q := u / ((n * L : ℕ) : ℤ) with hq
  have hblock : (u % ((n * L : ℕ) : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) = Y - (n : ℤ) * q := by
    rw [hdiv, hu]
    push_cast
    have hw : (L : ℤ) * Y + z k - (n : ℤ) * (L : ℤ) * q + ((L : ℤ) - 1) / 2 =
        (z k + ((L : ℤ) - 1) / 2) + (L : ℤ) * (Y - (n : ℤ) * q) := by ring
    rw [hw, Int.add_mul_ediv_left _ _ (ne_of_gt hLpos)]
    have h0 : (z k + ((L : ℤ) - 1) / 2) / (L : ℤ) = 0 := by
      apply Int.ediv_eq_zero_of_lt <;> omega
    rw [h0, zero_add]
  exact show (((((((u : ZMod (n * L))).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ)) : ZMod n) =
      ((Y : ℤ) : ZMod n) from by
    rw [hmod, hblock]
    push_cast
    simp
end Step
section Kernels
variable {ℓ : StepParameters} {n : ℕ}
def meanKernel (s : ℝ) (q : ℍ[ℝ]) (g : UnitQuaternion) : ℝ :=
  Real.exp (s * (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) / partitionFn (s * ‖q‖)
theorem bondKernel_eq_meanKernel (ℓ : StepParameters) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    bondKernel ℓ x W V b c =
      meanKernel (ℓ.coupling * x) (contourMean ℓ.baseDepth (fineHotLumps ℓ W) b W c) (V c.1 c.2) := rfl
open Classical in
def baseChoicesOf (ℓ : StepParameters) (n : ℕ) [NeZero n]
    (H : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0))) :
    Finset ((stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) :=
  Finset.univ.filter fun b => IsBaseChoice ℓ.baseDepth H b
theorem baseChoices_eq [NeZero n] (ℓ : StepParameters) (W : (stepBlockFrame ℓ.side n).GaugeField 0) :
    baseChoices ℓ W = baseChoicesOf ℓ n (fineHotLumps ℓ W) := rfl
end Kernels
end YangMills.Construction.TorusContours
end
