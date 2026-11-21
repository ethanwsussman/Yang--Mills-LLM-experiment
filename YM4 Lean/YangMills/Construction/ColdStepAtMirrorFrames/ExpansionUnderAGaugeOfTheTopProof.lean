import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopForm
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace GaugeCovariance
open YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets
variable {F : BlockFrame}
theorem adjointAction_coe (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X : imaginaryQuaternions) : ℍ[ℝ]) =
      (g : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
theorem coe_mul_coe_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (X + Y) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Y := by
  apply Subtype.ext
  simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_coe, Submodule.coe_add, mul_add, add_mul]
theorem adjointAction_zero (g : UnitQuaternion) : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g 0 = 0 := by
  apply Subtype.ext
  simp [_root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_coe]
theorem adjointAction_smul (g : UnitQuaternion) (r : ℝ) (X : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (r • X) = r • _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X := by
  apply Subtype.ext
  simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_coe, Submodule.coe_smul, mul_smul_comm, smul_mul_assoc]
theorem adjointAction_sum {ι : Type} (g : UnitQuaternion) (s : Finset ι) (f : ι → imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (∑ l ∈ s, f l) = ∑ l ∈ s, _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [_root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add, ih]
theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X‖ = ‖X‖ := by
  show ‖(g : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(X : ℍ[ℝ])‖
  rw [norm_mul, norm_mul, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion]
  simp
theorem expUnit_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    expUnit (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g w) = g * expUnit w * g⁻¹ := by
  apply Subtype.ext
  show NormedSpace.exp ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g w : imaginaryQuaternions) : ℍ[ℝ]) =
    (g : ℍ[ℝ]) * NormedSpace.exp (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
  have hn : ‖((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g w : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(w : ℍ[ℝ])‖ :=
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction g w
  rw [exp_imaginary_eq (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g w), exp_imaginary_eq w, hn, _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_coe]
  set r := Real.cos ‖(w : ℍ[ℝ])‖
  set u := Real.sin ‖(w : ℍ[ℝ])‖ / ‖(w : ℍ[ℝ])‖
  have hc : (g : ℍ[ℝ]) * (r : ℍ[ℝ]) = (r : ℍ[ℝ]) * (g : ℍ[ℝ]) := (Quaternion.coe_commutes r _).symm
  rw [mul_add, add_mul, hc, mul_assoc (r : ℍ[ℝ]), coe_mul_coe_inv, mul_one, mul_smul_comm, smul_mul_assoc]
theorem imaginaryCoords_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : imaginaryCoords (toImaginary v) = v := by
  ext i
  fin_cases i <;> rfl
theorem toImaginary_imaginaryCoords (X : imaginaryQuaternions) : toImaginary (imaginaryCoords X) = X := by
  apply Subtype.ext
  have hX : (X : ℍ[ℝ]).re = 0 := X.2
  ext
  · exact hX.symm
  · rfl
  · rfl
  · rfl
theorem norm_imaginaryCoords (X : imaginaryQuaternions) : ‖imaginaryCoords X‖ = ‖X‖ := by
  have hX : (X : ℍ[ℝ]).re = 0 := X.2
  have h1 : ‖(X : ℍ[ℝ])‖ ^ 2 = (X : ℍ[ℝ]).imI ^ 2 + (X : ℍ[ℝ]).imJ ^ 2 + (X : ℍ[ℝ]).imK ^ 2 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', hX]
    ring
  have h2 : ‖imaginaryCoords X‖ ^ 2 = (X : ℍ[ℝ]).imI ^ 2 + (X : ℍ[ℝ]).imJ ^ 2 + (X : ℍ[ℝ]).imK ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [imaginaryCoords]
  have h3 : ‖X‖ = ‖(X : ℍ[ℝ])‖ := rfl
  rw [h3]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h2.trans h1.symm)
theorem enclosingCell_crossing_step (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell)
    (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) (i : Fin 4)
    (hc : IsCrossingBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), i)) :
    enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i : F.Site F.depth) =
      z + unitStep F.top i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.enclosingCell_next_of_crossing <;> assumption
end GaugeCovariance
open YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets
open GaugeCovariance
theorem gaugeCovarianceOfFrame_holds (hcover : BlocksCoverLowerLevel) :
    GaugeCovarianceOfFrame := by
  refine ⟨?_, ?_, ?_⟩
  · intro F w V γ η hL hs hcov
    have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
    funext x i
    have hx : x ∈ sitesOfCells (finiteCells F) F.depth := hcover F hL hpos x
    have hx2 : x + unitStep F.depth i ∈ sitesOfCells (finiteCells F) F.depth := hcover F hL hpos _
    have hcoord : ¬ IsAxialTreeBond (x, i) →
        w (x, i) (gaugeTransform γ V) + stepCoordinates (adjointStepVariable γ η) x i =
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell x)) (w (x, i) V + stepCoordinates η x i) := by
      intro ht
      have hb : (x, i) ∈ chordBonds (finiteCells F) := by
        simp only [chordBonds, innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
        exact ⟨⟨hx, hx2⟩, ht⟩
      simp only [stepCoordinates, dif_pos hb]
      rw [hcov _ hb, _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add]
      congr 1
      simp only [adjointStepVariable]
      rw [toImaginary_imaginaryCoords]
    simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image, top_sub_depth, pow_one] at hx
    obtain ⟨z, -, h, hh, rfl⟩ := hx
    have hcell : enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) = z :=
      enclosingCell_offset hL hs z h hh
    by_cases hc : IsCrossingBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), i)
    · have ht : ¬ IsAxialTreeBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), i) :=
        fun q => q.1 hc
      have hn := enclosingCell_crossing_step hL hs z h hh i hc
      simp only [fieldOverFrameAt, chartedField, gaugeTransform, if_pos hc]
      rw [hcoord ht, expUnit_adjointAction, hcell, hn]
      group
    · have hn : enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h + unitStep F.depth i :
            F.Site F.depth) =
          enclosingCell (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth) := not_not.mp hc
      by_cases ht : IsAxialTreeBond ((cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth), i)
      · simp only [fieldOverFrameAt, chartedField, gaugeTransform, if_neg hc, if_pos ht, hn]
        group
      · simp only [fieldOverFrameAt, chartedField, gaugeTransform, if_neg hc, if_neg ht, hn]
        rw [hcoord ht, expUnit_adjointAction]
  · intro F j k G G' V γ c X hev
    have hg : ∀ τ, gaugeTransform γ (leftTranslate (bondSpread c X τ) V) =
        leftTranslate (bondSpread c (fun l => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (c l).1) (X l)) τ) (gaugeTransform γ V) := by
      intro τ
      funext z i
      have hS : bondSpread c (fun l => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (c l).1) (X l)) τ z i =
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ z) (bondSpread c X τ z i) := by
        unfold bondSpread
        rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases e : c l = (z, i)
        · have : (c l).1 = z := by rw [e]
          simp only [e, if_true, _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_smul, this]
        · simp only [e, if_false, _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero]
      simp only [gaugeTransform, leftTranslate]
      rw [hS, expUnit_adjointAction]
      group
    unfold bondDeriv
    have e : (fun τ => G' (leftTranslate (bondSpread c (fun l => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (c l).1) (X l)) τ)
        (gaugeTransform γ V))) =ᶠ[𝓝 0] fun τ => G (leftTranslate (bondSpread c X τ) V) :=
      hev.mono fun τ h => by
        show G' _ = _
        rw [← hg]
        exact h
    have e2 := (Filter.EventuallyEq.iteratedFDeriv ℝ e k).self_of_nhds
    rw [e2]
  · intro F γ η b
    have h1 : ‖toImaginary (η b)‖ = ‖η b‖ := by
      rw [← norm_imaginaryCoords, imaginaryCoords_toImaginary]
    simp only [adjointStepVariable]
    rw [norm_imaginaryCoords, _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction, h1]
end YangMills.Construction.ColdStepAtMirrorFrames
end
