import YangMills.Construction.ColdStepAtMirrorFrames.StepInFixedVariables
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace FixedVariables
def imaginaryCoords (w : imaginaryQuaternions) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK]
theorem toImaginary_imaginaryCoords (w : imaginaryQuaternions) :
    toImaginary (_root_.YangMills.Construction.ColdStepAtMirrorFrames.FixedVariables.imaginaryCoords w) = w := by
  apply Subtype.ext
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  ext <;> simp [toImaginary, _root_.YangMills.Construction.ColdStepAtMirrorFrames.FixedVariables.imaginaryCoords, hre]
theorem toImaginary_add (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem stepKernel_eq_exp (a x : ℝ) (W : F.GaugeField F.depth) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4) :
    stepKernel a x W V c =
      Real.exp (- (a * x) * blockFit W V c + haarGap (a * x * ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖)) := by apply _root_.YangMills.Construction.FrameInterpolationProof.stepKernel_eq_exp <;> assumption
theorem haarRadialDensity_zero_pos : 0 < haarRadialDensity 0 := by apply _root_.YangMills.Construction.FrameInterpolationProof.haarRadialDensity_zero_pos <;> assumption
theorem haarRadialDensity_pos {u : ℝ} (hu : 0 ≤ u) (hpi : u < Real.pi) :
    0 < haarRadialDensity u := by apply _root_.YangMills.Construction.FrameInterpolationProof.haarRadialDensity_pos <;> assumption
end FixedVariables
open FixedVariables in
theorem stepIntegralInFixedVariables_holds (hcover : BlocksCoverLowerLevel) :
    stepIntegralInFixedVariables := by
  classical
  intro F a ρA ρ x m p f V hodd hside hframe
  set fr : StepVariable (finiteCells F) :=
    fun b => _root_.YangMills.Construction.ColdStepAtMirrorFrames.FixedVariables.imaginaryCoords (stepFrame false a ρA m b.1 V) with hfr
  have hcov := hcover F hodd hside
  have hchord : ∀ b : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond b → b ∈ chordBonds (finiteCells F) := by
    intro b hb
    unfold chordBonds innerBonds
    rw [Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨Finset.mem_product.mpr ⟨hcov _, Finset.mem_univ _⟩, hcov _⟩, hb⟩
  have hpt : ∀ η : StepVariable (finiteCells F),
      stepIntegrand a ρA ρ x m p f (finiteCells F) V (η + fr) =
      (Real.exp (∑ _c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x)) *
        (∏ _b : ↥(chordBonds (finiteCells F)), haarRadialDensity 0) *
        Real.exp (- x * chartedEnergy a (coordsAboveFrame false a ρA m V 0) V)) *
      (cutoffWeight ρ p η * Real.exp (- stepExponent false a ρA x m f 1 V η)) := by
    intro η
    have hW : chartedField (stepCoordinates (η + fr)) V = fieldAboveFrame false a ρA m V η := by
      funext z i
      unfold fieldAboveFrame chartedField
      have key : ¬ IsAxialTreeBond (z, i) → stepCoordinates (η + fr) z i =
          coordsAboveFrame false a ρA m V η z i := by
        intro ht
        have hb := hchord (z, i) ht
        simp only [stepCoordinates, coordsAboveFrame, dif_pos hb, Pi.add_apply, toImaginary_add,
          hfr, toImaginary_imaginaryCoords]
        rw [add_comm]
      by_cases hc : IsCrossingBond (z, i)
      · rw [if_pos hc, if_pos hc, key fun ht => ht.1 hc]
      · rw [if_neg hc, if_neg hc]
        by_cases ht : IsAxialTreeBond (z, i)
        · rw [if_pos ht, if_pos ht]
        · rw [if_neg ht, if_neg ht, key ht]
    have hcut : ∀ b : ↥(chordBonds (finiteCells F)),
        ‖((toImaginary ((η + fr) b) : imaginaryQuaternions) : ℍ[ℝ]) -
          (bondFrameCoord a ρA m b.1 V : imaginaryQuaternions)‖ = ‖η b‖ := by
      intro b
      have e : ((toImaginary ((η + fr) b) : imaginaryQuaternions) : ℍ[ℝ]) -
          (bondFrameCoord a ρA m b.1 V : imaginaryQuaternions) =
          ((toImaginary (η b) : imaginaryQuaternions) : ℍ[ℝ]) := by
        simp only [Pi.add_apply, toImaginary_add, hfr, toImaginary_imaginaryCoords, stepFrame]
        simp
      rw [e, ← norm_toImaginary]
      rfl
    unfold stepIntegrand
    rw [hW]
    simp only [hcut]
    change lowerBoltzmann a x f (finiteCells F) (fieldAboveFrame false a ρA m V η) *
      cutoffWeight ρ p η * _ * _ = _
    by_cases hR : ∀ b : ↥(chordBonds (finiteCells F)), ‖η b‖ < ρ
    · set W := fieldAboveFrame false a ρA m V η with hWdef
      have hk : ∏ c ∈ innerBonds (finiteCells F) F.top, stepKernel a x W V c =
          Real.exp (- (a * x) * (∑ c ∈ innerBonds (finiteCells F) F.top, blockFit W V c) +
            ∑ c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x * ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, Real.exp_sum]
        exact Finset.prod_congr rfl fun c _ => stepKernel_eq_exp a x W V c
      have hJ : ∏ b : ↥(chordBonds (finiteCells F)), haarLogDensity ((η + fr) b) =
          (∏ _b : ↥(chordBonds (finiteCells F)), haarRadialDensity 0) *
            Real.exp (∑ b : ↥(chordBonds (finiteCells F)),
              haarLogRatio (coordsAboveFrame false a ρA m V η b.1.1 b.1.2)) := by
        rw [Real.exp_sum, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro b _
        have e1 : coordsAboveFrame false a ρA m V η b.1.1 b.1.2 = toImaginary ((η + fr) b) := by
          have hb : (b.1.1, b.1.2) ∈ chordBonds (finiteCells F) := b.2
          simp only [coordsAboveFrame, stepCoordinates, dif_pos hb, Pi.add_apply, toImaginary_add,
            hfr, toImaginary_imaginaryCoords]
          rw [add_comm]
        have hlt : ‖(η + fr) b‖ < Real.pi := by
          have h1 : ‖(η + fr) b‖ ≤ ‖η b‖ + ‖fr b‖ := norm_add_le _ _
          have h2 : ‖fr b‖ = ‖stepFrame false a ρA m b.1 V‖ := by
            rw [← norm_toImaginary, hfr]
            simp only [toImaginary_imaginaryCoords]
          have h3 := hframe b.1 b.2
          have h4 := hR b
          linarith
        have hpos := haarRadialDensity_pos (norm_nonneg ((η + fr) b)) hlt
        have h0 := haarRadialDensity_zero_pos
        unfold haarLogRatio
        rw [e1, norm_toImaginary, Real.exp_log (div_pos hpos h0)]
        have e2 : haarLogDensity ((η + fr) b) = haarRadialDensity ‖(η + fr) b‖ := rfl
        rw [e2]
        field_simp
      rw [hk, hJ]
      set A := minimalAction a (finiteCells F) F.depth W with hA
      set Sf := ∑ c ∈ innerBonds (finiteCells F) F.top, blockFit W V c with hSf
      set Om := ∑ c ∈ innerBonds (finiteCells F) F.top,
        haarGap (a * x * ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖) with hOm
      set Om0 := ∑ _c ∈ innerBonds (finiteCells F) F.top, haarGap (a * x) with hOm0
      set Hx := ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (coordsAboveFrame false a ρA m V η b.1.1 b.1.2) with hHx
      set Ff := ∑ y ∈ sitesOfCells (finiteCells F) F.depth, subtractTrivial f F y W with hFf
      set S0 := chartedEnergy a (coordsAboveFrame false a ρA m V 0) V with hS0
      set J := ∏ _b : ↥(chordBonds (finiteCells F)), haarRadialDensity 0 with hJ0
      set R := cutoffWeight ρ p η with hRw
      have hΨ : stepExponent false a ρA x m f 1 V η =
          x * (A + a * Sf - S0) - (Om - Om0) - Hx - 1 * Ff := by
        have e1 : chartedEnergy a (coordsAboveFrame false a ρA m V η) V = A + a * Sf := rfl
        have e2 : ∑ c ∈ innerBonds (finiteCells F) F.top,
            haarGapExcess a x (fieldAboveFrame false a ρA m V η) c = Om - Om0 := by
          simp only [haarGapExcess]
          rw [Finset.sum_sub_distrib]
        unfold stepExponent
        rw [e1, e2]
        rfl
      have hlw : lowerBoltzmann a x f (finiteCells F) W = Real.exp (- x * A + Ff) := rfl
      rw [hΨ, hlw]
      have hsum : - x * A + Ff + (- (a * x) * Sf + Om) + Hx =
          Om0 + - x * S0 + -(x * (A + a * Sf - S0) - (Om - Om0) - Hx - 1 * Ff) := by ring
      calc Real.exp (- x * A + Ff) * R * Real.exp (- (a * x) * Sf + Om) * (J * Real.exp Hx)
          = R * J * (Real.exp (- x * A + Ff) * Real.exp (- (a * x) * Sf + Om) * Real.exp Hx) := by
            ring
        _ = R * J * Real.exp (- x * A + Ff + (- (a * x) * Sf + Om) + Hx) := by
            rw [Real.exp_add (- x * A + Ff + (- (a * x) * Sf + Om)) Hx,
              Real.exp_add (- x * A + Ff) (- (a * x) * Sf + Om)]
        _ = R * J * Real.exp (Om0 + - x * S0 +
              -(x * (A + a * Sf - S0) - (Om - Om0) - Hx - 1 * Ff)) := by rw [hsum]
        _ = Real.exp Om0 * J * Real.exp (- x * S0) *
              (R * Real.exp (-(x * (A + a * Sf - S0) - (Om - Om0) - Hx - 1 * Ff))) := by
            rw [Real.exp_add (Om0 + - x * S0), Real.exp_add Om0 (- x * S0)]
            ring
    · push Not at hR
      obtain ⟨b, hb⟩ := hR
      have h0 : cutoffWeight ρ p η = 0 := by
        unfold cutoffWeight
        apply Finset.prod_eq_zero (Finset.mem_univ b)
        unfold cutoffFactor
        rw [if_neg (not_lt.mpr hb)]
      rw [h0]
      simp
  unfold stepIntegral
  rw [← integral_add_right_eq_self
    (fun w => stepIntegrand a ρA ρ x m p f (finiteCells F) V w) fr]
  simp_rw [hpt]
  rw [integral_const_mul]
end YangMills.Construction.ColdStepAtMirrorFrames
end
