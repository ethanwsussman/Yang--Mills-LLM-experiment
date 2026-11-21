import YangMills.Construction.ColdStepAtMirrorFrames.ContourOfAChartField
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ChartedFieldContour
open BlockOffsets
variable {F : BlockFrame}
def offsetSite (z : F.Cell) (u : Fin 4 → ℤ) : F.Site F.depth := cellCentre F.depth z + siteOfCoords F.depth u
theorem offsetSite_add_stepDisplacement (z : F.Cell) (u : Fin 4 → ℤ) (st : PathStep) :
    offsetSite z u + stepDisplacement F.depth st = offsetSite z (u + stepShift st) := by
  rcases st with ⟨i, b⟩
  unfold offsetSite
  rw [add_assoc]
  congr 1
  funext l
  cases b <;> simp [stepDisplacement, stepShift, unitStep, siteOfCoords]
theorem offsetSite_zero (z : F.Cell) : offsetSite z 0 = refineSite z := by
  unfold offsetSite
  funext l
  simp [cellCentre, refineSite, siteOfCoords]
theorem mem_chordBonds_finiteCells (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    {b : F.Site F.depth × Fin 4} (hb : ¬ IsAxialTreeBond b) : b ∈ chordBonds (finiteCells F) := by
  classical
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hs i
    omega
  unfold chordBonds innerBonds
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hcover F hL hpos _, Finset.mem_univ _⟩, hcover F hL hpos _⟩, hb⟩
section walks
variable (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
  {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top) {ε : ℝ} (hε : 0 ≤ ε)
  (hw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ ε)
include hcover hL hs hε hw
theorem distFromOne_forward_link_le (z : F.Cell) {u : Fin 4 → ℤ} (hu : u ∈ centredCube F.blockSide)
    (i : Fin 4) (hne : u i ≠ halfSide F.blockSide) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (chartedField w V (offsetSite z u) i) ≤ ε := by
  have hcr : ¬ IsCrossingBond (offsetSite z u, i) := fun h =>
    hne ((isCrossingBond_iff hL hs z u hu i).mp h)
  unfold chartedField
  rw [if_neg hcr]
  by_cases ht : IsAxialTreeBond (offsetSite z u, i)
  · rw [if_pos ht, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_one]
    exact hε
  · rw [if_neg ht]
    have h1 := hw (offsetSite z u, i) (mem_chordBonds_finiteCells hcover hL hs ht)
    exact (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le (w (offsetSite z u) i)).trans h1
theorem distFromOne_linkValue_le (z : F.Cell) {u : Fin 4 → ℤ} (hu : u ∈ centredCube F.blockSide)
    {st : PathStep} (hv : u + stepShift st ∈ centredCube F.blockSide) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (linkValue (chartedField w V) (offsetSite z u) st) ≤ ε := by
  rcases st with ⟨i, b⟩
  cases b with
  | true =>
    have hne : u i ≠ halfSide F.blockSide := by
      intro h
      have := ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff _).mp hv i).2
      simp [stepShift, h] at this
    simpa [linkValue] using _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.distFromOne_forward_link_le hcover hL hs V hε hw z hu i hne
  | false =>
    have hne : (u + stepShift (i, false)) i ≠ halfSide F.blockSide := by
      intro h
      have := ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff _).mp hu i).2
      simp [stepShift] at h
      omega
    have e : offsetSite z u - unitStep F.depth i = offsetSite z (u + stepShift (i, false)) := by
      rw [← offsetSite_add_stepDisplacement z u (i, false)]
      simp [stepDisplacement, sub_eq_add_neg]
    simp only [linkValue, Bool.false_eq_true, if_false]
    rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_inv, e]
    exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.distFromOne_forward_link_le hcover hL hs V hε hw z hv i hne
theorem distFromOne_pathHolonomy_le (z : F.Cell) {u : Fin 4 → ℤ} (hu : u ∈ centredCube F.blockSide)
    {l : List PathStep} (h : WalkStaysIn F.blockSide u l) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (pathHolonomy (chartedField w V) (offsetSite z u) l) ≤ l.length * ε := by
  induction l generalizing u with
  | nil => simp [pathHolonomy, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_one]
  | cons st r ih =>
    simp only [pathHolonomy]
    rw [offsetSite_add_stepDisplacement]
    refine (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul _ _).trans ?_
    have a1 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.distFromOne_linkValue_le hcover hL hs V hε hw z hu h.1
    have a2 := ih h.1 h.2
    simp only [List.length_cons]
    push_cast
    linarith
end walks
theorem pathHolonomy_append (X : F.GaugeField F.depth) (z : F.Cell) (u : Fin 4 → ℤ) (l l' : List PathStep) :
    pathHolonomy X (offsetSite z u) (l ++ l') =
      pathHolonomy X (offsetSite z u) l * pathHolonomy X (offsetSite z (walkTarget u l)) l' := by
  induction l generalizing u with
  | nil => simp [pathHolonomy, walkTarget]
  | cons st r ih =>
    simp only [List.cons_append, pathHolonomy]
    rw [offsetSite_add_stepDisplacement, ih, mul_assoc]
    rfl
def axisSegment (h : Fin 4 → ℤ) (d : Fin 4) : List PathStep :=
  List.replicate (h d).natAbs (d, decide (0 ≤ h d))
theorem add_axisSegment_shift (h u : Fin 4 → ℤ) (d : Fin 4) (hd : u d = 0) :
    u + ((h d).natAbs : ℤ) • stepShift (d, decide (0 ≤ h d)) = Function.update u d (h d) := by
  funext l
  by_cases hl : l = d
  · subst hl
    by_cases h0 : 0 ≤ h l
    · simp [stepShift, h0, hd, abs_of_nonneg h0]
    · have h1 : h l < 0 := not_le.mp h0
      simp [stepShift, h0, hd, abs_of_neg h1]
  · by_cases h0 : 0 ≤ h d <;> simp [stepShift, h0, Pi.single_eq_of_ne hl, Function.update_of_ne hl]
theorem axisSegments_walk {M : ℕ} (h : Fin 4 → ℤ) (hh : h ∈ centredCube M) (D : List (Fin 4))
    (hD : D.Nodup) (u : Fin 4 → ℤ) (hu : ∀ l, (u l = 0 ∨ u l = h l))
    (h0 : (0 : Fin 4 → ℤ) ∈ centredCube M) (hz : ∀ d ∈ D, u d = 0) :
    WalkStaysIn M u (D.flatMap (axisSegment h)) ∧
      (∀ l, walkTarget u (D.flatMap (axisSegment h)) l = if l ∈ D then h l else u l) ∧
      (((D.flatMap (axisSegment h)).length : ℤ) ≤ D.length * halfSide M) := by
  have hmem : ∀ x : Fin 4 → ℤ, (∀ l, x l = 0 ∨ x l = h l) → x ∈ centredCube M := by
    intro x hx
    rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff]
    intro l
    rcases hx l with e | e
    · rw [e]
      have := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff _).mp h0 l
      simpa using this
    · rw [e]
      exact (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff _).mp hh l
  induction D generalizing u with
  | nil => exact ⟨trivial, fun l => by simp [walkTarget], by simp⟩
  | cons d D ih =>
    have hnd := List.nodup_cons.mp hD
    have hud : u d = 0 := hz d (by simp)
    set u' := Function.update u d (h d) with hu'
    have hu'c : ∀ l, u' l = 0 ∨ u' l = h l := by
      intro l
      by_cases hl : l = d
      · subst hl
        right
        simp [hu']
      · simp only [hu', Function.update_of_ne hl]
        exact hu l
    obtain ⟨a1, a2⟩ := walkStaysIn_replicate (M := M) d (decide (0 ≤ h d)) (h d).natAbs (hmem u hu)
      (by rw [add_axisSegment_shift h u d hud]; exact hmem _ hu'c)
    rw [add_axisSegment_shift h u d hud] at a2
    obtain ⟨b1, b2, b3⟩ := ih hnd.2 u' hu'c (fun e he => by
      have hne : e ≠ d := fun hh' => hnd.1 (hh' ▸ he)
      simp only [hu', Function.update_of_ne hne]
      exact hz e (by simp [he]))
    have ef : (d :: D).flatMap (axisSegment h) = axisSegment h d ++ D.flatMap (axisSegment h) := by simp
    have ew : walkTarget u (axisSegment h d) = u' := a2
    refine ⟨?_, ?_, ?_⟩
    · rw [ef]
      refine walkStaysIn_append a1 ?_
      rw [ew]
      exact b1
    · intro l
      rw [ef, walkTarget_append, ew, b2 l]
      by_cases hl : l = d
      · subst hl
        simp [hnd.1, hu']
      · simp [hl, hu']
    · rw [ef, List.length_append]
      have hl : ((axisSegment h d).length : ℤ) ≤ halfSide M := by
        have := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff _).mp hh d
        simp only [axisSegment, List.length_replicate]
        omega
      simp only [List.length_cons]
      push_cast
      linarith
theorem axisPath_eq_flatMap (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π = ((List.finRange 4).map π).flatMap (axisSegment h) := by
  unfold axisPath axisSegment
  rw [List.flatMap_map]
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
end ChartedFieldContour
open ChartedFieldContour BlockOffsets in
theorem chartedFieldContourBound_holds (hcover : BlocksCoverLowerLevel) :
    ChartedFieldContourBound := by
  intro F w V ε hL hs hε hw c h π hh
  set z : F.Cell := c.1 with hz
  set i : Fin 4 := c.2 with hi
  set l : List PathStep := axisPath h π with hl
  obtain ⟨k, hk⟩ := id hL
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hhalf : halfSide F.blockSide = k := by
    unfold halfSide
    rw [hLz]
    omega
  have hc := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff h).mp hh
  rw [hhalf] at hc
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
    rw [mem_centredCube_iff, hhalf]
    intro l
    simp only [Pi.zero_apply]
    omega
  obtain ⟨w1, w2, w3⟩ := axisSegments_walk h hh ((List.finRange 4).map π)
    ((List.nodup_finRange 4).map π.injective) 0 (fun _ => Or.inl rfl) h0 (fun _ _ => rfl)
  rw [← axisPath_eq_flatMap] at w1 w2 w3
  have hend : walkTarget 0 l = h := funext fun x => by
    rw [w2 x, if_pos (List.mem_map.mpr ⟨π.symm x, List.mem_finRange _, π.apply_symm_apply x⟩)]
  have hlen : (l.length : ℤ) ≤ 4 * k := by
    have : (((List.finRange 4).map π).length : ℤ) = 4 := by simp
    rw [this, hhalf] at w3
    exact w3
  set j₀ : ℕ := (k - h i).toNat with hj₀
  set j₁ : ℕ := (k + h i).toNat with hj₁
  have ej₀ : (j₀ : ℤ) = k - h i := Int.toNat_of_nonneg (by have := hc i; omega)
  have ej₁ : (j₁ : ℤ) = k + h i := Int.toNat_of_nonneg (by have := hc i; omega)
  have hLj : F.blockSide = j₀ + (1 + j₁) := by
    have : (F.blockSide : ℤ) = (j₀ : ℤ) + (1 + j₁) := by
      rw [ej₀, ej₁, hLz]
      ring
    exact_mod_cast this
  have hs1 : stepShift (i, true) = Pi.single i 1 := by simp [stepShift]
  set u₁ : Fin 4 → ℤ := h + (j₀ : ℤ) • stepShift (i, true) with hu₁
  have hu₁i : u₁ i = k := by
    simp only [hu₁, hs1, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ej₀]
    ring
  have hu₁l : ∀ x, x ≠ i → u₁ x = h x := fun x hx => by
    simp [hu₁, hs1, Pi.single_eq_of_ne hx]
  have hu₁c : u₁ ∈ centredCube F.blockSide := by
    rw [mem_centredCube_iff, hhalf]
    intro x
    by_cases hx : x = i
    · subst hx
      rw [hu₁i]
      omega
    · rw [hu₁l x hx]
      exact hc x
  obtain ⟨r1, r2⟩ := walkStaysIn_replicate (M := F.blockSide) i true j₀ hh hu₁c
  set pre : List PathStep := l ++ List.replicate j₀ (i, true) with hpre
  have wpre : WalkStaysIn F.blockSide 0 pre := walkStaysIn_append w1 (by rw [hend]; exact r1)
  have epre : walkTarget 0 pre = u₁ := by
    rw [hpre, walkTarget_append, hend, r2]
  set z' : F.Cell := z + unitStep F.top i with hz'
  set u₂ : Fin 4 → ℤ := u₁ + Pi.single i (1 - (F.blockSide : ℤ)) with hu₂
  have hu₂i : u₂ i = -k := by
    simp only [hu₂, Pi.add_apply, Pi.single_eq_same, hu₁i, hLz]
    ring
  have hu₂l : ∀ x, x ≠ i → u₂ x = h x := fun x hx => by
    simp [hu₂, Pi.single_eq_of_ne hx, hu₁l x hx]
  have hu₂c : u₂ ∈ centredCube F.blockSide := by
    rw [mem_centredCube_iff, hhalf]
    intro x
    by_cases hx : x = i
    · subst hx
      rw [hu₂i]
      omega
    · rw [hu₂l x hx]
      exact hc x
  have hsite : offsetSite z u₁ + stepDisplacement F.depth (i, true) = offsetSite z' u₂ := by
    rw [offsetSite_add_stepDisplacement]
    unfold offsetSite
    rw [hz', cellCentre_add_unitStep hs z i, add_assoc (cellCentre F.depth z), ← _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.siteOfCoords_add]
    congr 2
    funext x
    by_cases hx : x = i
    · subst hx
      simp only [Pi.add_apply, hs1, hu₂, Pi.single_eq_same]
      ring
    · simp only [Pi.add_apply, hs1, hu₂, Pi.single_eq_of_ne hx]
      ring
  have etarget : u₂ + (j₁ : ℤ) • stepShift (i, true) = h := by
    funext x
    by_cases hx : x = i
    · subst hx
      simp only [hs1, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hu₂i, ej₁]
      ring
    · simp [hs1, Pi.single_eq_of_ne hx, hu₂l x hx]
  obtain ⟨r3, r4⟩ := walkStaysIn_replicate (M := F.blockSide) i true j₁ hu₂c (by rw [etarget]; exact hh)
  rw [etarget] at r4
  obtain ⟨v1, -⟩ := walkStaysIn_reversePath h0 w1
  rw [hend] at v1
  set post : List PathStep := List.replicate j₁ (i, true) ++ reversePath l with hpost
  have wpost : WalkStaysIn F.blockSide u₂ post := walkStaysIn_append r3 (by rw [r4]; exact v1)
  have econt : bondContour F.blockSide h π i = pre ++ (i, true) :: post := by
    unfold bondContour
    rw [← hl, hLj, List.replicate_add, List.replicate_add]
    simp [hpre, hpost, List.append_assoc]
  have hcr : IsCrossingBond (offsetSite z u₁, i) :=
    (isCrossingBond_iff hL hs z u₁ hu₁c i).mpr (by rw [hhalf]; exact hu₁i)
  have hcell : enclosingCell (offsetSite z u₁) = z := enclosingCell_offset hL hs z u₁ hu₁c
  have hval : chartedField w V (offsetSite z u₁) i = expUnit (w (offsetSite z u₁) i) * V z i := by
    unfold chartedField
    rw [if_pos hcr, hcell]
  have hhol : pathHolonomy (chartedField w V) (refineSite c.1) (bondContour F.blockSide h π c.2) =
      pathHolonomy (chartedField w V) (offsetSite z 0) pre *
        (expUnit (w (offsetSite z u₁) i) * V z i * pathHolonomy (chartedField w V) (offsetSite z' u₂) post) := by
    rw [offsetSite_zero, ← hz, ← hi, econt, ← offsetSite_zero, pathHolonomy_append, epre]
    simp only [pathHolonomy, linkValue, if_true, hsite, hval]
  rw [hhol]
  set A : UnitQuaternion := pathHolonomy (chartedField w V) (offsetSite z 0) pre with hA
  set E : UnitQuaternion := expUnit (w (offsetSite z u₁) i) with hE
  set C : UnitQuaternion := pathHolonomy (chartedField w V) (offsetSite z' u₂) post with hC
  have hgroup : A * (E * V z i * C) * (V z i)⁻¹ = A * (E * (V z i * C * (V z i)⁻¹)) := by group
  change _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (A * (E * V z i * C) * (V z i)⁻¹) ≤ _
  rw [hgroup]
  have hA' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne A ≤ pre.length * ε :=
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.distFromOne_pathHolonomy_le hcover hL hs V hε hw z h0 wpre
  have hC' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne C ≤ post.length * ε :=
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.distFromOne_pathHolonomy_le hcover hL hs V hε hw z' hu₂c wpost
  have hE' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne E ≤ ε := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le _).trans
    (hw (offsetSite z u₁, i) (mem_chordBonds_finiteCells hcover hL hs fun ht => ht.1 hcr))
  have hlpre : pre.length = l.length + j₀ := by simp [hpre]
  have hlpost : post.length = j₁ + l.length := by simp [hpost, reversePath]
  have hcount : (pre.length : ℝ) + 1 + post.length ≤ 5 * (F.blockSide : ℝ) := by
    have : ((pre.length : ℤ) + 1 + post.length) ≤ 5 * (F.blockSide : ℤ) := by
      rw [hlpre, hlpost]
      push_cast
      rw [ej₀, ej₁, hLz]
      omega
    exact_mod_cast this
  have h1 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul A (E * (V z i * C * (V z i)⁻¹))
  have h2 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul E (V z i * C * (V z i)⁻¹)
  rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_conj] at h2
  calc _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (A * (E * (V z i * C * (V z i)⁻¹))) ≤ pre.length * ε + ε + post.length * ε := by linarith
    _ = ((pre.length : ℝ) + 1 + post.length) * ε := by ring
    _ ≤ 5 * (F.blockSide : ℝ) * ε := mul_le_mul_of_nonneg_right hcount hε
end YangMills.Construction.ColdStepAtMirrorFrames
end
