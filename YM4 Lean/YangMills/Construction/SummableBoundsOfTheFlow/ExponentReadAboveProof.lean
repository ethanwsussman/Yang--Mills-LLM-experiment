import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open Set
set_option linter.unusedSectionVars false
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames IteratedDerivative
namespace Interpolation
variable {F : BlockFrame}
theorem toImaginary_add (v w : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (v + w) = toImaginary v + toImaginary w := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
theorem toImaginary_smul (r : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : toImaginary (r • v) = r • toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_smul <;> assumption
open Classical in
theorem stepCoordinates_add_single (ζ : StepVariable (finiteCells F)) (t : ℝ)
    (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) (z : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (ζ + t • (Pi.single b e : StepVariable (finiteCells F))) z i =
      if (z, i) = b.1 then stepCoordinates ζ z i + t • toImaginary e else stepCoordinates ζ z i := by
  unfold stepCoordinates
  by_cases h : (z, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h, dif_pos h]
    by_cases hb : (z, i) = b.1
    · have e1 : (⟨(z, i), h⟩ : ↥(chordBonds (finiteCells F))) = b := Subtype.ext hb
      rw [if_pos hb, e1]
      simp [toImaginary_add, toImaginary_smul]
    · have e1 : (⟨(z, i), h⟩ : ↥(chordBonds (finiteCells F))) ≠ b := fun e2 => hb (congrArg Subtype.val e2)
      rw [if_neg hb]
      simp [Pi.single_eq_of_ne e1]
  · rw [dif_neg h, dif_neg h]
    have hb : (z, i) ≠ b.1 := fun e2 => h (e2 ▸ b.2)
    rw [if_neg hb]
theorem interpolatedCoords_add_single (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) (t : ℝ)
    (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)) : open Classical in
    interpolatedCoords s a ρA m V (ζ + t • (Pi.single b e : StepVariable (finiteCells F))) =
      Function.update (interpolatedCoords s a ρA m V ζ) b.1.1
        (Function.update (interpolatedCoords s a ρA m V ζ b.1.1) b.1.2
          (interpolatedCoords s a ρA m V ζ b.1.1 b.1.2 + t • toImaginary e)) := by
  classical
  funext z i
  by_cases hz : z = b.1.1
  · subst hz
    by_cases hi : i = b.1.2
    · subst hi
      simp only [Function.update_self]
      simp only [interpolatedCoords]
      rw [stepCoordinates_add_single, if_pos rfl, add_assoc]
    · simp only [Function.update_self]
      rw [Function.update_of_ne hi]
      simp only [interpolatedCoords]
      rw [stepCoordinates_add_single, if_neg (fun h => hi (congrArg Prod.snd h))]
  · rw [Function.update_of_ne hz]
    simp only [interpolatedCoords]
    rw [stepCoordinates_add_single, if_neg (fun h => hz (congrArg Prod.fst h))]
open Classical in
theorem chartedSlope_eq_fderiv (s a ρA : ℝ) (m k : ℕ) (V : F.GaugeField F.top)
    (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (p : StepVariable (finiteCells F) × (Fin k → ℝ))
    (b : ↥(chordBonds (finiteCells F)))
    (e : EuclideanSpace ℝ (Fin 3))
    (hd : DifferentiableAt ℝ (rotatedEval (interpolatedEnergy s a ρA m) V c X) p) :
    chartedSlope a (interpolatedCoords s a ρA m (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X p.2) V) p.1)
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X p.2) V) b.1 (toImaginary e) =
      fderiv ℝ (rotatedEval (interpolatedEnergy s a ρA m) V c X) p (Pi.single b e, 0) := by
  set W := leftTranslate (ColdStepAtMirrorFrames.bondSpread c X p.2) V
  have e1 : (fun t : ℝ => chartedEnergy a (Function.update
      (interpolatedCoords s a ρA m W p.1) b.1.1
      (Function.update (interpolatedCoords s a ρA m W p.1 b.1.1) b.1.2
        (interpolatedCoords s a ρA m W p.1 b.1.1 b.1.2 + t • toImaginary e))) W) =
      fun t : ℝ => rotatedEval (interpolatedEnergy s a ρA m) V c X (p + t • ((Pi.single b e, 0) :
        StepVariable (finiteCells F) × (Fin k → ℝ))) := by
    funext t
    simp only [rotatedEval, interpolatedEnergy, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_zero, add_zero]
    rw [interpolatedCoords_add_single]
  unfold chartedSlope
  rw [e1]
  have hl : HasDerivAt (fun t : ℝ => p + t • ((Pi.single b e, 0) :
      StepVariable (finiteCells F) × (Fin k → ℝ))) (Pi.single b e, 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((Pi.single b e, 0) :
      StepVariable (finiteCells F) × (Fin k → ℝ))).const_add p
  have hd' : HasFDerivAt (rotatedEval (interpolatedEnergy s a ρA m) V c X)
      (fderiv ℝ (rotatedEval (interpolatedEnergy s a ρA m) V c X) p)
      (p + (0 : ℝ) • ((Pi.single b e, 0) : StepVariable (finiteCells F) × (Fin k → ℝ))) := by
    simpa using hd.hasFDerivAt
  exact (hd'.comp_hasDerivAt (0 : ℝ) hl).deriv
theorem cellExponentRotatedEval_holds : cellExponentRotatedEvalStatement := by
  classical
  refine ⟨?_, ?_⟩
  swap
  · intro F s a ρA m k V c X τ b e hd
    have h1 := chartedSlope_eq_fderiv s a ρA m k V c X (0, τ) b e hd
    have h0 : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
      apply Subtype.ext
      ext <;> simp [toImaginary]
    have hz : ∀ (V' : F.GaugeField F.top), interpolatedCoords s a ρA m V' (0 : StepVariable (finiteCells F)) =
        fun z i => interpolatedFrame s a ρA m (z, i) V' := by
      intro V'
      funext z i
      have h2 : stepCoordinates (0 : StepVariable (finiteCells F)) z i = 0 := by
        unfold stepCoordinates
        split_ifs with hh
        · exact h0
        · rfl
      simp [interpolatedCoords, h2]
    have h3 := hz (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)
    simp only at h1
    rw [h3] at h1
    exact h1
  intro F s a ρA x m Y V η k c X hs
  have hn : ∀ᶠ p in 𝓝 ((η, 0) : StepVariable (finiteCells F) × (Fin k → ℝ)), ∀ v ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (rotatedEval (interpolatedEnergy s a ρA m) V c X) (v • p.1, p.2) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro v hv
    have h := (hs v hv).eventually (by simp)
    have hc : Filter.Tendsto (fun z : (StepVariable (finiteCells F) × (Fin k → ℝ)) × ℝ => (z.2 • z.1.1, z.1.2))
        (𝓝 ((η, 0), v)) (𝓝 (v • η, 0)) :=
      (by fun_prop : Continuous fun z : (StepVariable (finiteCells F) × (Fin k → ℝ)) × ℝ =>
        (z.2 • z.1.1, z.1.2)).tendsto ((η, 0), v)
    exact hc.eventually h
  filter_upwards [hn] with p hp
  simp only [rotatedEval, interpolatedBlockExponent, rayGradientSum, cellChordBonds, contourHaarGap,
    haarGapExcess, interpolatedHaarLogRatio]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 2
  congr 1
  refine Finset.sum_congr rfl fun b _ => intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le zero_le_one] at hv
  have h1 := chartedSlope_eq_fderiv s a ρA m k V c X (v • p.1, p.2) b (p.1 b)
    ((hp v hv).differentiableAt (by simp))
  exact h1
end Interpolation
end YangMills.Construction
end
