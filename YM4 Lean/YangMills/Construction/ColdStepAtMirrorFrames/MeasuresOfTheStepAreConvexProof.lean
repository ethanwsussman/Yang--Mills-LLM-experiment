import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPoint
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsOfTheChartEnergy
import YangMills.Construction.ColdStepAtMirrorFrames.FramesOnTheParameters
import YangMills.Construction.ColdStepAtMirrorFrames.TermsInFixedVariables
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames.ExponentConvexity
def imaginaryCLM : BondVector →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => toImaginary v
      map_add' := fun u v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = 0 + 0
          simp
        · change (u + v) 0 = u 0 + v 0
          simp
        · change (u + v) 1 = u 1 + v 1
          simp
        · change (u + v) 2 = u 2 + v 2
          simp
      map_smul' := fun c v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = c * 0
          simp
        · change (c • v) 0 = c * v 0
          simp
        · change (c • v) 1 = c * v 1
          simp
        · change (c • v) 2 = c * v 2
          simp }
theorem imaginaryCLM_apply (v : BondVector) : imaginaryCLM v = toImaginary v := rfl
theorem norm_imaginaryCLM (v : BondVector) : ‖imaginaryCLM v‖ = ‖v‖ := by
  have h1 : ‖imaginaryCLM v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := Quaternion.normSq_eq_norm_mul_self ((imaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])
    rw [Quaternion.normSq_def'] at h
    have h2 : ‖(imaginaryCLM v : imaginaryQuaternions)‖ =
        ‖((imaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
    rw [h2, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, pow_two]
    simp only [imaginaryCLM_apply, toImaginary, Real.norm_eq_abs, sq_abs] at h ⊢
    linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
theorem stepCoordinates_smul_bondVariation (b : ChordBond F) (e : BondVector) (u : ℝ)
    (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (u • (bondVariation b e : StepVariable (finiteCells F))) x i =
      if (x, i) = b.1 then u • imaginaryCLM e else 0 := by
  classical
  unfold stepCoordinates
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h]
    by_cases hb : (x, i) = b.1
    · have hbb : (⟨(x, i), h⟩ : ChordBond F) = b := Subtype.ext hb
      rw [if_pos hb, hbb, ← imaginaryCLM_apply]
      simp [bondVariation]
    · have hbb : (⟨(x, i), h⟩ : ChordBond F) ≠ b := fun hc => hb (congrArg Subtype.val hc)
      have h0 : (bondVariation b e : StepVariable (finiteCells F)) ⟨(x, i), h⟩ = 0 :=
        Pi.single_eq_of_ne hbb _
      rw [if_neg hb, ← imaginaryCLM_apply]
      simp [h0]
  · rw [dif_neg h, if_neg]
    intro hc
    exact h (hc ▸ b.2)
theorem bondPartialDeriv_eq_chartedSlope {a : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (hA : DifferentiableAt ℝ (chartedEnergyAt a w V) 0) (b : ChordBond F) (e : BondVector) :
    bondPartialDeriv (chartedEnergyAt a w V) b 0 e = chartedSlope a w V b.1 (imaginaryCLM e) := by
  have hline : (fun u : ℝ => chartedEnergy a (Function.update w b.1.1 (Function.update (w b.1.1) b.1.2
      (w b.1.1 b.1.2 + u • imaginaryCLM e))) V) =
      fun u : ℝ => chartedEnergyAt a w V (u • (bondVariation b e : StepVariable (finiteCells F))) := by
    funext u
    unfold chartedEnergyAt
    congr 1
    funext x i
    rw [stepCoordinates_smul_bondVariation]
    by_cases hx : x = b.1.1
    · subst hx
      by_cases hi : i = b.1.2
      · subst hi
        simp
      · have hne : (b.1.1, i) ≠ b.1 := fun h => hi (congrArg Prod.snd h)
        simp [hi, hne]
    · have hne : (x, i) ≠ b.1 := fun h => hx (congrArg Prod.fst h)
      simp [hx, hne]
  unfold chartedSlope
  rw [hline]
  have h1 : HasDerivAt (fun u : ℝ => u • (bondVariation b e : StepVariable (finiteCells F)))
      (bondVariation b e) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (bondVariation b e : StepVariable (finiteCells F))
  have h2 : HasFDerivAt (chartedEnergyAt a w V) (fderiv ℝ (chartedEnergyAt a w V) 0)
      ((0 : ℝ) • (bondVariation b e : StepVariable (finiteCells F))) := by
    simpa using hA.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  exact h3.deriv.symm
theorem exponentConvexity_holds (hA : ConvexAboveChartPoint) (hFr : FrameBoundsEventually)
    (hR : ChartEnergyHessianRowsEventually) (hJ : EventuallyInParametersCombines) :
    exponentConvexityStatement := by
  refine hJ.2 _ _ ?_ (hJ.1 _ _ hA (hJ.1 _ _ hFr hR))
  rintro T hT ⟨hAt, hfr, hRt⟩
  intro t x f F V star ν hx hrow hF hV hν0 hν1
  obtain ⟨Cf, C, _, _, _, _, hL40, hn64, hκ1, hσ1, hsz, hcn, hσA, hy1, hay, hframes⟩ := hfr
  obtain ⟨_, hsm, hst, _⟩ := hframes t x F V hx hF hV
  have hs := hsm star
  have hn := hst star
  have hFcopy := hF
  obtain ⟨hFL, hFt, n, hside, hnn⟩ := hFcopy
  have hn0 : 64 ≤ n := hn64.trans hnn
  have hCT : IsBlockTorus T.L F := ⟨hFL, n, hn0, hside⟩
  have hσ0 : 0 < T.σ := hT.σ_pos
  have hρ : T.ballRadius = T.σ / 64 := rfl
  set m : ℕ := frameRadius x with hm
  set w : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    frameCoordField star T.a T.chainParams.ρA m V with hw
  have hpt : IsChartBasePoint T w V := by
    refine ⟨fun b hb => hs.norm_add_le b hb, fun b hb => ?_, fun p hp => ?_, fun c h π hh => ?_⟩
    · have h1 := hs.norm_le b hb
      have h2 : ‖w b.1 b.2‖ ≤ C * T.σ := h1
      rw [hρ]
      linarith
    · have h1 := hs.small_curvature p hp
      refine h1.trans_le ?_
      by_cases hc : star = true
      · simp only [hc, if_true]
        nlinarith
      · simp only [hc, Bool.false_eq_true, if_false]
        exact le_rfl
    · have h1 := hs.holonomy_ratio c h π (hFL ▸ hh)
      have h2 : ‖contourHolonomyDefect (chartedField w V) V c h π - 1‖ ≤ C * T.σ := h1
      rw [hρ]
      linarith
  have hsmallpt : IsAdmissibleChartPoint T.L T.chainParams.σA w V := by
    refine ⟨fun b hb => ?_, fun p hp => ?_⟩
    · have h1 := hpt.small b hb
      have h2 : 0 < T.ballRadius := by rw [hρ]; positivity
      linarith
    · have h1 := hpt.curvature_small p hp
      have h2 : (41 / 64 : ℝ) * T.σ ≤ T.chainParams.σA := by nlinarith
      exact h1.trans_le h2
  obtain ⟨K, _, hKp, _, _⟩ := hRt F V hCT
  have hAd : DifferentiableAt ℝ (chartedEnergyAt T.a w V) 0 :=
    (hKp w hsmallpt).1.differentiableAt (by norm_num)
  have hslope : ∀ (b : ChordBond F) (e : BondVector), ‖e‖ = 1 →
      x * |bondPartialDeriv (chartedEnergyAt T.a w V) b 0 e| ≤ 1 := by
    intro b e he
    rw [bondPartialDeriv_eq_chartedSlope hAd]
    have h1 := hn.firstDeriv_bound b.1 b.2 (imaginaryCLM e) (by rw [norm_imaginaryCLM, he])
    exact h1
  have hmem := (hAt t x f F V w ν hx ⟨hrow.smooth, hrow.decay⟩ hF hV hpt hslope hν0 hν1).1
  exact hmem
end ColdStepAtMirrorFrames.ExponentConvexity
end YangMills.Construction
end
