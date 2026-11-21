import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShifts
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtTheFrameIsADensity
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoToriProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace LocalDensityAtFrame
variable {F : BlockFrame}
private theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (hw : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) : chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
private theorem stepCoordinates_zero (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  split_ifs
  · apply Subtype.ext
    ext <;> simp [toImaginary]
  · rfl
private theorem fieldAboveFrame_zero (star : Bool) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    fieldAboveFrame star a ρ m V 0 = chartedField (frameCoordField star a ρ m V) V := by
  unfold fieldAboveFrame
  congr 1
  funext x i
  simp [coordsAboveFrame, frameCoordField, stepCoordinates_zero]
abbrev _root_.YangMills.SharedProofs.p2150 := @fieldAboveFrame_zero
private theorem fieldAboveFrame_zero_gaugeTransform {star : Bool} {a ρ : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hM : ChartEquivariance F a) (γ : F.Cell → UnitQuaternion)
    (hg : ∀ b ∈ chordBonds (finiteCells F),
      (stepFrame star a ρ m b (gaugeTransform γ V) : ℍ[ℝ]) =
        (γ (enclosingCell b.1) : ℍ[ℝ]) * (stepFrame star a ρ m b V : ℍ[ℝ]) * ((γ (enclosingCell b.1))⁻¹ : UnitQuaternion)) :
    fieldAboveFrame star a ρ m (gaugeTransform γ V) 0 =
      gaugeTransform (blockConstantGauge γ) (fieldAboveFrame star a ρ m V 0) := by
  rw [fieldAboveFrame_zero, fieldAboveFrame_zero, ← hM.chartedField_gaugeTransform]
  refine chartedField_congr _ fun x i hnt => ?_
  exact Subtype.ext (hg (x, i) (hM.mem_chordBonds_of_not_tree _ hnt))
private theorem fieldAboveFrame_zero_translate {star : Bool} {a ρ : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hM : ChartEquivariance F a) (h : F.Cell)
    (hc : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame star a ρ m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = stepFrame star a ρ m b V) :
    fieldAboveFrame star a ρ m (translateField h V) 0 =
      translateField (cellCentre F.depth h) (fieldAboveFrame star a ρ m V 0) := by
  rw [fieldAboveFrame_zero, fieldAboveFrame_zero, ← hM.chartedField_translate]
  refine chartedField_congr _ fun x i hnt => ?_
  have hb : (x, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  have hb0 : (x - cellCentre F.depth h, i) ∈ chordBonds (finiteCells F) :=
    (hM.chordBonds_translate h (x - cellCentre F.depth h, i)).mp (by simpa using hb)
  have hf := hc _ hb0
  simp only [sub_add_cancel] at hf
  exact hf
end LocalDensityAtFrame
open LocalDensityAtFrame in
theorem expansionAtFrameIsLocalDensity_of_chartEquivariance (hCh : chartEquivarianceStatement) :
    expansionAtFrameIsLocalDensityStatement := by
  intro T hT h64 hTr hFS t x f star hx hf
  have hσ := hT.σ_pos
  have hρ : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have top : ∀ F, IsCubicTopTorus T.L t T.n₀ F →
      IsCubicTorusAbove T.L t T.n₀ F ∧ Odd F.blockSide ∧ ∀ i, 2 ≤ F.extent i := by
    rintro F ⟨hL, ht, n, hs, hn⟩
    have hLp : 1 ≤ T.L := hT.odd_L.pos
    exact ⟨⟨hL, ht, n, hs, hn.trans (Nat.le_mul_of_pos_right _ hLp)⟩, hL ▸ hT.odd_L, fun i => by
      rw [hs]
      omega⟩
  have hcold : ∀ (F : BlockFrame) (V : F.GaugeField F.top) (C : ℝ),
      FrameSmallness star T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.κ₂ C T.σ T.chainParams.Kk (frameRadius x) V →
      IsSmallCurvature T.σ (fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) V 0) := by
    intro F V C hs p hp
    rw [fieldAboveFrame_zero]
    refine lt_of_lt_of_le (hs.small_curvature p hp) ?_
    split_ifs <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · intro F hF Y V hV
    exact (hTr t x f F V hx hf hF hV star).1.smooth Y 0 fun b => by simpa using hρ
  · intro F hF Y V γ hV
    obtain ⟨hlow, hodd, hs2⟩ := top F hF
    obtain ⟨C, hs⟩ := hFS t x F V star hx hF hV
    have hM := hCh F T.a hodd hs2
    have hstep := fieldAboveFrame_zero_gaugeTransform hM γ fun b hb => hs.gauge_covariant b hb γ
    show cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y 0 (gaugeTransform γ V) =
      cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y 0 V
    unfold cellCentredExpansion centredExpansion
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold subtractTrivial
    rw [hstep, hf.gauge_invariant F hlow y _ _ (hcold F V C hs)]
  · intro F hF Y h V hV
    obtain ⟨hlow, hodd, hs2⟩ := top F hF
    obtain ⟨C, hs⟩ := hFS t x F V star hx hF hV
    have hM := hCh F T.a hodd hs2
    have hstep := fieldAboveFrame_zero_translate hM h (fun b hb => hs.translation_invariant b hb h)
    have hflat : translateField (cellCentre F.depth h) (uniformField F F.depth) = uniformField F F.depth := rfl
    have hcf : IsSmallCurvature T.σ (uniformField F F.depth) := by
      intro p _
      have hh : ∀ (l : List PathStep) (z : F.Site F.depth), pathHolonomy (uniformField F F.depth) z l = 1 := by
        intro l
        induction l with
        | nil => intro z; rfl
        | cons st r ih =>
          intro z
          have h1 : linkValue (uniformField F F.depth) z st = 1 := by
            unfold linkValue uniformField
            split_ifs <;> simp
          simp [pathHolonomy, h1, ih]
      simpa [plaquetteDefect, plaquetteHolonomy, hh] using hσ
    show cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f (Y + h) 0 (translateField h V) =
      cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y 0 V
    unfold cellCentredExpansion centredExpansion
    refine Finset.sum_nbij' (fun y => y - cellCentre F.depth h) (fun y => y + cellCentre F.depth h) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨(hM.sitesOfCells_translate h _).mp (by simpa using h1), ?_⟩
      have h3 := hM.enclosingCell_translate h (y - cellCentre F.depth h)
      rw [sub_add_cancel, h2] at h3
      exact (add_right_cancel h3).symm
    · intro y hy
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨(hM.sitesOfCells_translate h _).mpr h1, ?_⟩
      rw [hM.enclosingCell_translate, h2]
    · intro y _
      simp
    · intro y _
      simp
    · intro y _
      unfold subtractTrivial
      rw [hstep]
      have h1 := hf.translation_invariant F hlow (y - cellCentre F.depth h) (cellCentre F.depth h) _ (hcold F V C hs)
      have h2 := hf.translation_invariant F hlow (y - cellCentre F.depth h) (cellCentre F.depth h) _ hcf
      rw [sub_add_cancel] at h1 h2
      rw [h1]
      rw [hflat] at h2
      rw [h2]
end YangMills.Construction.ColdStepAtMirrorFrames
end
