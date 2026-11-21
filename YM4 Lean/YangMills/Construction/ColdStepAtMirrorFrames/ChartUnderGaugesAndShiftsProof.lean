import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShifts
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace ChartSymmetries
open BlockAverages TopLevelSites ColdStepAtMirrorFrames
open TorusFields hiding wilsonAction gaugeTransform unitStep
section Adjoint
def adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) : imaginaryQuaternions :=
  ⟨(g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]), by
    have hw : (w : ℍ[ℝ]).re = 0 := w.2
    have hs : star (w : ℍ[ℝ]) = -(w : ℍ[ℝ]) := by
      ext <;> simp [hw]
    set q : ℍ[ℝ] := (g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hq
    have h1 : star q = -q := by
      rw [hq, coe_inv_unitQuaternion, star_mul, star_mul, star_star, hs]
      noncomm_ring
    have h2 : (star q).re = q.re := by simp
    rw [h1] at h2
    show q.re = 0
    simp only [Quaternion.re_neg] at h2
    linarith⟩
theorem norm_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ‖((adjointAction g w : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(w : ℍ[ℝ])‖ := by
  change ‖(g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = _
  rw [norm_mul, norm_mul, norm_unitQuaternion, norm_unitQuaternion, one_mul, mul_one]
theorem expUnit_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    expUnit (adjointAction g w) = g * expUnit w * g⁻¹ := by
  apply Subtype.ext
  have hgg : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul]
    simp
  have hc : ∀ c : ℝ, ((c : ℝ) : ℍ[ℝ]) = c • (1 : ℍ[ℝ]) := fun c => by ext <;> simp
  change NormedSpace.exp ((adjointAction g w : imaginaryQuaternions) : ℍ[ℝ]) =
    (g : ℍ[ℝ]) * NormedSpace.exp (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
  rw [exp_imaginary, exp_imaginary, norm_adjointAction, hc]
  change _ + _ • ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) = _
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, hgg]
end Adjoint
section Energy
variable {F : BlockFrame} {a : ℝ} {S : Finset F.Cell}
theorem minimalAction_gaugeTransform (hcov : gaugeCovarianceStatement) (hL : 0 < F.blockSide) :
    ∀ (j : ℕ), j ≤ F.top → ∀ (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j),
      minimalAction a S j (gaugeTransform γ X) = minimalAction a S j X := by
  intro j
  induction j with
  | zero =>
    intro _ γ X
    have h := (hcov F 0 (by simp [BlockFrame.top]) hL).2.2.1
    change wilsonAction S (gaugeTransform γ X) = wilsonAction S X
    unfold wilsonAction
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [h, re_unitQuaternion_conj]
  | succ j ih =>
    intro hj γ X
    have h := hcov F j (by omega) hL
    set γ' : F.Site j → UnitQuaternion := Function.extend refineSite γ 1 with hγ'
    have hext : ∀ y, γ' (refineSite y) = γ y := fun y => h.1.extend_apply γ 1 y
    have hsurj : Function.Surjective (gaugeTransform γ' : F.GaugeField j → F.GaugeField j) := by
      intro W
      refine ⟨gaugeTransform (fun x => (γ' x)⁻¹) W, ?_⟩
      funext x i
      simp only [gaugeTransform]
      group
    change (⨅ W : F.GaugeField j, (minimalAction a S j W +
        a * ∑ c ∈ innerBonds S (j + 1), blockFit W (gaugeTransform γ X) c)) =
      ⨅ W : F.GaugeField j, (minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W X c)
    rw [← hsurj.iInf_comp]
    refine iInf_congr fun W => ?_
    rw [ih (by omega)]
    congr 2
    exact Finset.sum_congr rfl fun c _ => h.2.2.2 γ' γ W X c (hext _) (hext _)
theorem enclosingCell_refineSite (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (y : F.Cell) :
    enclosingCell (refineSite (j := F.depth) y : F.Site F.depth) = y := by
  have e : (refineSite (j := F.depth) y : F.Site F.depth) =
      cellCentre F.depth y + siteOfCoords F.depth 0 := by
    rw [siteOfCoords_zero, add_zero]
    unfold refineSite cellCentre
    simp only [top_sub_depth, pow_one]
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
    rw [mem_centredCube_iff]
    intro i
    have : 0 ≤ halfWidth F.blockSide := by
      unfold halfWidth
      have := hL.pos
      omega
    simpa using this
  rw [e]
  exact enclosingCell_centre_add hL hs y 0 h0
theorem blockEnergy_gaugeTransform (hcov : gaugeCovarianceStatement) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (γ : F.Cell → UnitQuaternion) (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) :
    blockEnergy a S F.depth (gaugeTransform (fun x => γ (enclosingCell x)) W) (gaugeTransform γ V) =
      blockEnergy a S F.depth W V := by
  unfold blockEnergy
  rw [minimalAction_gaugeTransform hcov hL.pos _ (by simp [BlockFrame.top])]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (hcov F F.depth (by simp [BlockFrame.top]) hL.pos).2.2.2 _ γ W V c
    (by simp only [enclosingCell_refineSite hL hs]) (by simp only [enclosingCell_refineSite hL hs])
theorem gaugeTransform_chartedField (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (γ : F.Cell → UnitQuaternion) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) :
    gaugeTransform (fun x => γ (enclosingCell x)) (chartedField w V) x i =
      chartedField (fun x i => adjointAction (γ (enclosingCell x)) (w x i)) (gaugeTransform γ V) x i := by
  unfold chartedField gaugeTransform
  beta_reduce
  by_cases hc : IsCrossingBond (x, i)
  · rw [if_pos hc, if_pos hc, enclosingCell_add_unitStep hL hs x i hc, expUnit_adjointAction]
    group
  · have e : enclosingCell (x + unitStep F.depth i) = enclosingCell x := by
      by_contra hne
      exact hc hne
    rw [if_neg hc, if_neg hc, e]
    by_cases ht : IsAxialTreeBond (x, i)
    · rw [if_pos ht, if_pos ht]
      group
    · rw [if_neg ht, if_neg ht, expUnit_adjointAction]
end Energy
section Shift
variable {F : BlockFrame} (u : Fin 4 → ℤ)
def latticeTranslation (j : ℕ) : F.Site j := siteOfCoords j fun i => (F.blockSide : ℤ) ^ (F.top - j) * u i
def translateBy {j : ℕ} (X : F.GaugeField j) : F.GaugeField j := fun x i => X (x + latticeTranslation u j) i
theorem latticeTranslation_neg (j : ℕ) :
    (latticeTranslation (-u) j : F.Site j) = - latticeTranslation u j := by
  funext i
  simp [latticeTranslation, siteOfCoords]
theorem translateBy_translateBy_neg {j : ℕ} (X : F.GaugeField j) :
    translateBy u (translateBy (-u) X) = X := by
  funext x i
  simp only [translateBy, latticeTranslation_neg]
  rw [add_neg_cancel_right]
theorem pathHolonomy_translateBy {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (l : List PathStep) :
    pathHolonomy (translateBy u X) x l = pathHolonomy X (x + latticeTranslation u j) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have e : linkValue (translateBy u X) x st = linkValue X (x + latticeTranslation u j) st := by
      unfold linkValue translateBy
      split_ifs
      · rfl
      · have e1 : x - unitStep j st.1 + latticeTranslation u j =
            x + latticeTranslation u j - unitStep j st.1 := by abel
        rw [e1]
    have e2 : x + stepDisplacement j st + latticeTranslation u j =
        x + latticeTranslation u j + stepDisplacement j st := by abel
    simp only [pathHolonomy, e, ih, e2]
theorem refineSite_add_latticeTranslation {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) :
    refineSite (y + latticeTranslation u (j + 1)) = refineSite y + latticeTranslation u j := by
  unfold latticeTranslation
  rw [refineSite_add j hj]
  congr 2
  funext i
  have e : F.top - j = F.top - (j + 1) + 1 := by omega
  rw [e, pow_succ]
  ring
theorem contourAverage_translateBy {j : ℕ} (hj : j + 1 ≤ F.top) (X : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) :
    contourAverage (translateBy u X) c = contourAverage X (c.1 + latticeTranslation u (j + 1), c.2) := by
  unfold contourAverage
  simp only [pathHolonomy_translateBy, refineSite_add_latticeTranslation u hj]
theorem blockFit_translateBy {j : ℕ} (hj : j + 1 ≤ F.top) (W : F.GaugeField j) (V : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) :
    blockFit (translateBy u W) (translateBy u V) c = blockFit W V (c.1 + latticeTranslation u (j + 1), c.2) := by
  unfold blockFit
  rw [contourAverage_translateBy u hj]
  rfl
theorem add_latticeTranslation_mem_sitesOfCells (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j ≤ F.top)
    {x : F.Site j} (hx : x ∈ sitesOfCells (finiteCells F) j) :
    x + latticeTranslation u j ∈ sitesOfCells (finiteCells F) j := by
  obtain ⟨y, _, h, hh, rfl⟩ := mem_sitesOfCells.mp hx
  refine mem_sitesOfCells.mpr ⟨y + siteOfCoords F.top u, mem_finiteCells hs _, h, hh, ?_⟩
  rw [cellCentre_add j hj]
  unfold latticeTranslation
  abel
theorem add_latticeTranslation_mem_sitesOfCells_iff (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j ≤ F.top)
    (x : F.Site j) :
    x + latticeTranslation u j ∈ sitesOfCells (finiteCells F) j ↔ x ∈ sitesOfCells (finiteCells F) j := by
  refine ⟨fun h => ?_, add_latticeTranslation_mem_sitesOfCells u hs hj⟩
  have := add_latticeTranslation_mem_sitesOfCells (-u) hs hj h
  rwa [latticeTranslation_neg, add_neg_cancel_right] at this
theorem sum_innerBonds_translate (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j ≤ F.top)
    (f : F.Site j × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells F) j, f (c.1 + latticeTranslation u j, c.2) =
      ∑ c ∈ innerBonds (finiteCells F) j, f c := by
  have hmem : ∀ c : F.Site j × Fin 4, c ∈ innerBonds (finiteCells F) j ↔
      c.1 ∈ sitesOfCells (finiteCells F) j ∧ c.1 + unitStep j c.2 ∈ sitesOfCells (finiteCells F) j := by
    intro c
    unfold innerBonds
    simp [Finset.mem_filter, Finset.mem_product]
  refine Finset.sum_nbij' (fun c => (c.1 + latticeTranslation u j, c.2))
    (fun c => (c.1 - latticeTranslation u j, c.2)) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    obtain ⟨h1, h2⟩ := (hmem c).mp hc
    refine (hmem _).mpr ⟨add_latticeTranslation_mem_sitesOfCells u hs hj h1, ?_⟩
    have e : c.1 + latticeTranslation u j + unitStep j c.2 =
        c.1 + unitStep j c.2 + latticeTranslation u j := by abel
    simp only
    rw [e]
    exact add_latticeTranslation_mem_sitesOfCells u hs hj h2
  · intro c hc
    obtain ⟨h1, h2⟩ := (hmem c).mp hc
    refine (hmem _).mpr ⟨?_, ?_⟩
    · simp only
      rw [← add_latticeTranslation_mem_sitesOfCells_iff u hs hj, sub_add_cancel]
      exact h1
    · simp only
      rw [← add_latticeTranslation_mem_sitesOfCells_iff u hs hj]
      have e : c.1 - latticeTranslation u j + unitStep j c.2 + latticeTranslation u j =
          c.1 + unitStep j c.2 := by abel
      rw [e]
      exact h2
  · intro c _
    simp
  · intro c _
    simp
  · intro c _
    rfl
theorem sum_innerPlaquettes_translate (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j ≤ F.top)
    (f : F.Site j × Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ innerPlaquettes (finiteCells F) j, f (p.1 + latticeTranslation u j, p.2) =
      ∑ p ∈ innerPlaquettes (finiteCells F) j, f p := by
  have hcorn : ∀ (p : F.Site j × Fin 4 × Fin 4) (v : F.Site j),
      plaquetteCorners (p.1 + v, p.2) = (plaquetteCorners p).image (· + v) := by
    intro p v
    unfold plaquetteCorners
    simp only [Finset.image_insert, Finset.image_singleton]
    congr 1
    · congr 1
      · abel_nf
      · congr 1
        · abel_nf
        · congr 1
          abel_nf
  have hmem : ∀ p : F.Site j × Fin 4 × Fin 4, p ∈ innerPlaquettes (finiteCells F) j ↔
      p.1 ∈ sitesOfCells (finiteCells F) j ∧ p.2.1 < p.2.2 ∧
        plaquetteCorners p ⊆ sitesOfCells (finiteCells F) j := by
    intro p
    unfold innerPlaquettes
    simp [Finset.mem_filter, Finset.mem_product]
  have hkeep : ∀ (w : Fin 4 → ℤ) (p : F.Site j × Fin 4 × Fin 4), p ∈ innerPlaquettes (finiteCells F) j →
      (p.1 + latticeTranslation w j, p.2) ∈ innerPlaquettes (finiteCells F) j := by
    intro w p hp
    obtain ⟨h1, h2, h3⟩ := (hmem p).mp hp
    refine (hmem _).mpr ⟨add_latticeTranslation_mem_sitesOfCells w hs hj h1, h2, ?_⟩
    rw [hcorn]
    intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    exact add_latticeTranslation_mem_sitesOfCells w hs hj (h3 hd)
  refine Finset.sum_nbij' (fun p => (p.1 + latticeTranslation u j, p.2))
    (fun p => (p.1 + latticeTranslation (-u) j, p.2)) (hkeep u) (hkeep (-u)) ?_ ?_ ?_
  · intro p _
    simp [latticeTranslation_neg]
  · intro p _
    simp [latticeTranslation_neg]
  · intro p _
    rfl
theorem minimalAction_translateBy (hs : ∀ i, 0 < F.extent i) {a : ℝ} :
    ∀ (j : ℕ), j ≤ F.top → ∀ X : F.GaugeField j,
      minimalAction a (finiteCells F) j (translateBy u X) = minimalAction a (finiteCells F) j X := by
  intro j
  induction j with
  | zero =>
    intro hj X
    change wilsonAction (finiteCells F) (translateBy u X) = wilsonAction (finiteCells F) X
    unfold wilsonAction
    have e : ∀ p : F.Site 0 × Fin 4 × Fin 4, plaquetteHolonomy (translateBy u X) p =
        plaquetteHolonomy X (p.1 + latticeTranslation u 0, p.2) := fun p => pathHolonomy_translateBy u X p.1 _
    simp only [e]
    exact sum_innerPlaquettes_translate u hs hj
      (fun p => 1 - ((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]).re)
  | succ j ih =>
    intro hj V
    have hsurj : Function.Surjective (translateBy u : F.GaugeField j → F.GaugeField j) :=
      fun W => ⟨translateBy (-u) W, translateBy_translateBy_neg u W⟩
    change (⨅ W : F.GaugeField j, (minimalAction a (finiteCells F) j W +
        a * ∑ c ∈ innerBonds (finiteCells F) (j + 1), blockFit W (translateBy u V) c)) =
      ⨅ W : F.GaugeField j, (minimalAction a (finiteCells F) j W +
        a * ∑ c ∈ innerBonds (finiteCells F) (j + 1), blockFit W V c)
    rw [← hsurj.iInf_comp]
    refine iInf_congr fun W => ?_
    rw [ih (by omega)]
    congr 2
    simp only [blockFit_translateBy u hj]
    exact sum_innerBonds_translate u hs hj (fun c => blockFit W V c)
theorem blockEnergy_translateBy (hs : ∀ i, 0 < F.extent i) {a : ℝ} (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) :
    blockEnergy a (finiteCells F) F.depth (translateBy u W) (translateBy u V) =
      blockEnergy a (finiteCells F) F.depth W V := by
  unfold blockEnergy
  rw [minimalAction_translateBy u hs _ (by simp [BlockFrame.top])]
  congr 2
  have hj : F.depth + 1 ≤ F.top := le_rfl
  have e : ∀ c : F.Site (F.depth + 1) × Fin 4, blockFit (translateBy u W) (translateBy u V) c =
      blockFit W V (c.1 + latticeTranslation u (F.depth + 1), c.2) := fun c => blockFit_translateBy u hj W V c
  simp only [e]
  exact sum_innerBonds_translate u hs (j := F.depth + 1) hj (fun c => blockFit W V c)
theorem latticeTranslation_top : (latticeTranslation u F.top : F.Cell) = siteOfCoords F.top u := by
  unfold latticeTranslation
  simp
theorem cellCentre_add_latticeTranslation (z : F.Cell) (h : Fin 4 → ℤ) :
    cellCentre F.depth z + siteOfCoords F.depth h + latticeTranslation u F.depth =
      cellCentre F.depth (z + siteOfCoords F.top u) + siteOfCoords F.depth h := by
  rw [cellCentre_add F.depth (by simp [BlockFrame.top])]
  unfold latticeTranslation
  abel
theorem enclosingCell_add_latticeTranslation (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) :
    enclosingCell (x + latticeTranslation u F.depth) = enclosingCell x + siteOfCoords F.top u := by
  obtain ⟨z, h, hh, rfl⟩ := exists_centre_add hL hs x
  rw [cellCentre_add_latticeTranslation, enclosingCell_centre_add hL hs _ _ hh,
    enclosingCell_centre_add hL hs _ _ hh]
theorem isCrossingBond_add_latticeTranslation (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) :
    IsCrossingBond (x + latticeTranslation u F.depth, i) ↔ IsCrossingBond (x, i) := by
  obtain ⟨z, h, hh, rfl⟩ := exists_centre_add hL hs x
  rw [cellCentre_add_latticeTranslation, isCrossingBond_iff hL hs _ _ hh, isCrossingBond_iff hL hs _ _ hh]
theorem isAxialTreeBond_add_latticeTranslation (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) :
    IsAxialTreeBond (x + latticeTranslation u F.depth, i) ↔ IsAxialTreeBond (x, i) := by
  obtain ⟨z, h, hh, rfl⟩ := exists_centre_add hL hs x
  rw [cellCentre_add_latticeTranslation, isAxialTreeBond_iff hL hs _ _ hh, isAxialTreeBond_iff hL hs _ _ hh]
theorem chartedField_translateBy (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    chartedField (fun x i => w (x + latticeTranslation u F.depth) i) (translateBy u V) =
      translateBy u (chartedField w V) := by
  funext x i
  simp only [translateBy]
  unfold chartedField
  by_cases hc : IsCrossingBond (x, i)
  · rw [if_pos hc, if_pos ((isCrossingBond_add_latticeTranslation u hL hs x i).mpr hc),
      enclosingCell_add_latticeTranslation u hL hs]
    simp only [translateBy, latticeTranslation_top]
  · rw [if_neg hc, if_neg (fun h => hc ((isCrossingBond_add_latticeTranslation u hL hs x i).mp h))]
    by_cases ht : IsAxialTreeBond (x, i)
    · rw [if_pos ht, if_pos ((isAxialTreeBond_add_latticeTranslation u hL hs x i).mpr ht)]
    · rw [if_neg ht, if_neg (fun h => ht ((isAxialTreeBond_add_latticeTranslation u hL hs x i).mp h))]
theorem add_latticeTranslation_mem_chordBonds_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (b : F.Site F.depth × Fin 4) :
    (b.1 + latticeTranslation u F.depth, b.2) ∈ chordBonds (finiteCells F) ↔ b ∈ chordBonds (finiteCells F) := by
  classical
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hj : F.depth ≤ F.top := by simp [BlockFrame.top]
  have hmem : ∀ c : F.Site F.depth × Fin 4, c ∈ chordBonds (finiteCells F) ↔
      c.1 ∈ sitesOfCells (finiteCells F) F.depth ∧
        c.1 + unitStep F.depth c.2 ∈ sitesOfCells (finiteCells F) F.depth ∧ ¬ IsAxialTreeBond c := by
    intro c
    unfold chordBonds innerBonds
    simp [Finset.mem_filter, Finset.mem_product, and_assoc]
  rw [hmem, hmem]
  simp only
  have e : b.1 + latticeTranslation u F.depth + unitStep F.depth b.2 =
      b.1 + unitStep F.depth b.2 + latticeTranslation u F.depth := by abel
  rw [e, add_latticeTranslation_mem_sitesOfCells_iff u hs0 hj, add_latticeTranslation_mem_sitesOfCells_iff u hs0 hj,
    isAxialTreeBond_add_latticeTranslation u hL hs]
end Shift
end ChartSymmetries
namespace ColdStepAtMirrorFrames
open BlockAverages TopLevelSites ChartSymmetries
open TorusFields hiding wilsonAction gaugeTransform unitStep
variable {F : BlockFrame}
private theorem latticeTranslation_siteCoords (h : F.Cell) (j : ℕ) :
    (latticeTranslation (F := F) (siteCoords h) j : F.Site j) = cellCentre j h := rfl
private theorem latticeTranslation_neg_siteCoords (h : F.Cell) (j : ℕ) :
    (latticeTranslation (F := F) (-siteCoords h) j : F.Site j) = - cellCentre j h := by
  rw [latticeTranslation_neg, latticeTranslation_siteCoords]
private theorem translateBy_neg_eq (h : F.Cell) {j : ℕ} (X : F.GaugeField j) :
    translateBy (-siteCoords h) X = translateField (cellCentre j h) X := by
  funext x i
  simp only [translateBy, translateField, latticeTranslation_neg_siteCoords, sub_eq_add_neg]
private theorem cellCentre_top_eq (h : F.Cell) : cellCentre F.top h = h := cellCentre_top h
private theorem translateBy_neg_top (h : F.Cell) (V : F.GaugeField F.top) :
    translateBy (-siteCoords h) V = translateField h V := by
  rw [translateBy_neg_eq, cellCentre_top_eq]
theorem chartEquivarianceStatement_holds (hcov : gaugeCovarianceStatement) :
    chartEquivarianceStatement := by
  intro F a hL hs
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hjt : F.depth ≤ F.top := by simp [BlockFrame.top]
  have hall : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth := fun x => by
    obtain ⟨z, h, hh, rfl⟩ := exists_centre_add hL hs x
    exact mem_sitesOfCells.mpr ⟨z, mem_finiteCells hs0 z, h, by simpa [BlockFrame.top] using hh, rfl⟩
  refine ⟨fun γ W V => blockEnergy_gaugeTransform hcov hL hs γ W V, fun γ w V => ?_, fun γ W c => ?_,
    fun h W V => ?_, fun h w V => ?_, fun h W c => ?_, fun h b => ?_, fun h x => ?_, fun h x => ?_,
    fun h c => ?_, fun b hb => ?_⟩
  · funext x i
    exact (gaugeTransform_chartedField hL hs γ w V x i).symm
  · have := (hcov F F.depth (by simp [BlockFrame.top]) hL.pos).2.1 (blockConstantGauge γ) W c
    rw [this, norm_mul, norm_mul, norm_unitQuaternion, norm_unitQuaternion, one_mul, mul_one]
  · have e := blockEnergy_translateBy (-siteCoords h) hs0 (a := a) W V
    rwa [translateBy_neg_eq, translateBy_neg_top] at e
  · have e := chartedField_translateBy (-siteCoords h) hL hs w V
    rw [translateBy_neg_top, translateBy_neg_eq] at e
    simpa only [latticeTranslation_neg_siteCoords, sub_eq_add_neg] using e
  · have e := contourAverage_translateBy (-siteCoords h) (j := F.depth) le_rfl W c
    rw [translateBy_neg_eq] at e
    rw [e]
    have : (latticeTranslation (F := F) (-siteCoords h) (F.depth + 1) : F.Site (F.depth + 1)) = - h := by
      rw [latticeTranslation_neg_siteCoords]
      exact congrArg Neg.neg (cellCentre_top_eq h)
    simp only [this, sub_eq_add_neg]
  · exact add_latticeTranslation_mem_chordBonds_iff (siteCoords h) hL hs b
  · have e := enclosingCell_add_latticeTranslation (siteCoords h) hL hs x
    rwa [latticeTranslation_siteCoords, siteOfCoords_siteCoords] at e
  · have e := add_latticeTranslation_mem_sitesOfCells_iff (siteCoords h) hs0 hjt x
    rwa [latticeTranslation_siteCoords] at e
  · have hmem : ∀ c : F.Site F.top × Fin 4, c ∈ innerBonds (finiteCells F) F.top ↔
        c.1 ∈ sitesOfCells (finiteCells F) F.top ∧
          c.1 + unitStep F.top c.2 ∈ sitesOfCells (finiteCells F) F.top := by
      intro c
      unfold innerBonds
      simp [Finset.mem_filter, Finset.mem_product]
    have ht : (latticeTranslation (F := F) (siteCoords h) F.top : F.Site F.top) = h := by
      rw [latticeTranslation_siteCoords]
      exact cellCentre_top_eq h
    rw [hmem, hmem]
    simp only
    have e : c.1 + h + unitStep F.top c.2 = c.1 + unitStep F.top c.2 + h := by abel
    rw [e]
    have i1 := add_latticeTranslation_mem_sitesOfCells_iff (siteCoords h) hs0 (le_refl F.top) c.1
    have i2 := add_latticeTranslation_mem_sitesOfCells_iff (siteCoords h) hs0 (le_refl F.top)
      (c.1 + unitStep F.top c.2)
    rw [ht] at i1 i2
    rw [i1, i2]
  · classical
    unfold chordBonds innerBonds
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨⟨hall _, hall _⟩, hb⟩
end ColdStepAtMirrorFrames
end YangMills.Construction
end
