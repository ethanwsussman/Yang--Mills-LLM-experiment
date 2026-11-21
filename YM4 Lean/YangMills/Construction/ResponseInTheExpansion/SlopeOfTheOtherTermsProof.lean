import YangMills.Construction.ColdStepAtMirrorFrames.OtherTermsOfTheExponentProof
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfSitesAndCells
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTermsOfTheExponent
import YangMills.Construction.ColdStepAtMirrorFrames.GapTermsOfTheExponent
import YangMills.Construction.ColdStepAtMirrorFrames.HaarTermsOfTheExponent
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOverTheCells
import YangMills.Construction.ResponseInTheExpansion.SlopeOfTheOtherTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.ResponseInTheExpansion.RemainderSlope
variable {F : BlockFrame}
theorem stepCoordinates_add (η ζ : StepVariable (finiteCells F)) (s : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (η + ζ) s i = stepCoordinates η s i + stepCoordinates ζ s i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_add <;> assumption
def shiftCoords (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (η : StepVariable (finiteCells F)) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun s i => w s i + stepCoordinates η s i
theorem readInChart_add {E : Type} (G : F.GaugeField F.depth → E) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (η ζ : StepVariable (finiteCells F)) :
    readInChart G w V (η + ζ) = readInChart G (shiftCoords w η) V ζ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.RemainderExponent.readInChart_add <;> assumption
theorem haarExcessSum_add (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (η ζ : StepVariable (finiteCells F)) :
    haarExcessSum w (η + ζ) = haarExcessSum (shiftCoords w η) ζ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.RemainderExponent.haarExcessSum_add <;> assumption
section Calculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
theorem contDiffAt_of_translate {f : P → ℝ} {η : P} (h : ContDiffAt ℝ 3 (fun ζ => f (η + ζ)) 0) :
    ContDiffAt ℝ 3 f η := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.contDiffAt_of_comp_add_left <;> assumption
theorem fderiv_translate_zero (f : P → ℝ) (η u : P) :
    fderiv ℝ (fun ζ => f (η + ζ)) 0 u = fderiv ℝ f η u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.fderiv_comp_add_left_zero_apply <;> assumption
theorem contDiffAt_fderiv_linearCombination {g₁ g₂ g₃ : P → ℝ} (c₀ c₁ c₂ c₃ : ℝ) (h₁ : ContDiffAt ℝ 3 g₁ 0)
    (h₂ : ContDiffAt ℝ 3 g₂ 0) (h₃ : ContDiffAt ℝ 3 g₃ 0) (u : P) :
    ContDiffAt ℝ 3 (fun ζ => c₀ + c₁ * g₁ ζ + c₂ * g₂ ζ + c₃ * g₃ ζ) 0 ∧
    fderiv ℝ (fun ζ => c₀ + c₁ * g₁ ζ + c₂ * g₂ ζ + c₃ * g₃ ζ) 0 u =
      c₁ * fderiv ℝ g₁ 0 u + c₂ * fderiv ℝ g₂ 0 u + c₃ * fderiv ℝ g₃ 0 u := by
  have d₁ : DifferentiableAt ℝ g₁ 0 := h₁.differentiableAt (by norm_num)
  have d₂ : DifferentiableAt ℝ g₂ 0 := h₂.differentiableAt (by norm_num)
  have d₃ : DifferentiableAt ℝ g₃ 0 := h₃.differentiableAt (by norm_num)
  have h : HasFDerivAt (fun ξ => c₀ + c₁ * g₁ ξ + c₂ * g₂ ξ + c₃ * g₃ ξ)
      (c₁ • fderiv ℝ g₁ 0 + c₂ • fderiv ℝ g₂ 0 + c₃ • fderiv ℝ g₃ 0) 0 :=
    (((d₁.hasFDerivAt.const_mul c₁).const_add c₀).add (d₂.hasFDerivAt.const_mul c₂)).add
      (d₃.hasFDerivAt.const_mul c₃)
  refine ⟨((contDiffAt_const.add (contDiffAt_const.mul h₁)).add (contDiffAt_const.mul h₂)).add
      (contDiffAt_const.mul h₃), ?_⟩
  rw [h.fderiv]
  simp
end Calculus
set_option maxHeartbeats 2000000 in
theorem remainderSlopeBound_of_chartBounds (hFr : FrameBoundsEventually) (hJ : EventuallyInParametersCombines)
    (hG : GapTermsChartBounds) (hH : HaarExcessSumDiagonalBounds)
    (hR : ExpansionTermsChartBounds) (hM : ChartShiftLipschitz)
    (hS : ExpDecaySumBounded) (hD : SupDistCellComparison) :
    RemainderSlopeBound := by
  classical
  choose! Cgf hCgf using hG
  choose! Sf hSf using hS
  obtain ⟨CH, hCH, hH⟩ := hH
  obtain ⟨Cr, hCr, hR⟩ := hR
  refine hJ.2 _ _ ?_ hFr
  rintro T hT hfr
  obtain ⟨Cf, C, _, _, _, _, hL40, hn64, hκ1, hσ1, _, _, _, hy1, hay, _⟩ := hfr
  have hOdd : Odd T.L := hT.odd_L
  have hκ0 : 0 < T.κ := hT.κ_pos
  have hσ0 : 0 < T.σ := hT.σ_pos
  have hρ0 : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hδ0 : 0 < T.decayRate := by
    unfold StepParameters.decayRate
    positivity
  have hE0 : 0 ≤ T.E := by linarith [hT.one_le_E]
  have ha0 : 0 < T.a := by linarith [hT.one_le_a]
  have hSδ := hSf T.decayRate hδ0
  obtain ⟨hCg0, hGt⟩ := hCgf T.L hOdd
  refine ⟨Cgf T.L + CH + Cr * T.E * Sf T.decayRate, by
    have := hSδ.1
    positivity, ?_⟩
  intro t x f F V w ν hx hrow hF hp hν0 hν1
  have hx1 : 1 ≤ x := hy1.trans hx
  have hx0 : 0 < x := by linarith
  have hA : 2 ≤ T.a * x := hay.trans (mul_le_mul_of_nonneg_left hx ha0.le)
  obtain ⟨hFL, hFt, n, hside, hn⟩ := hF
  have hn0 : 0 < n := by omega
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside]; exact hn0
  have hLpos : 0 < T.L := hOdd.pos
  have hlow : IsCubicTorusAbove T.L t T.n₀ F :=
    ⟨hFL, hFt, n, hside, hn.trans (Nat.le_mul_of_pos_right n hLpos)⟩
  have hOddF : Odd F.blockSide := hFL ▸ hOdd
  intro η hη
  have hsz : ∀ b ∈ chordBonds (finiteCells F), ‖shiftCoords w η b.1 b.2‖ ≤ 1 := by
    intro b hb
    have h1 := (hM F V w η T.ballRadius hOddF hη hρ0.le).1 b.1 b.2
    have h2 := hp.small b hb
    have h3 : 1 / (64 * (T.L : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ T.L := by exact_mod_cast hLpos
      linarith
    calc ‖shiftCoords w η b.1 b.2‖ ≤ ‖w b.1 b.2‖ + ‖stepCoordinates η b.1 b.2‖ := norm_add_le _ _
      _ ≤ ‖w b.1 b.2‖ + T.ballRadius := by linarith
      _ ≤ 1 := h2.trans h3
  have hcold : IsSmallCurvature T.σ (chartedField (shiftCoords w η) V) := by
    intro p hp'
    have h1 := (hM F V w η T.ballRadius hOddF hη hρ0.le).2.1 p
    have h2 := hp.curvature_small p hp'
    have h3 : T.ballRadius = T.σ / 64 := rfl
    have h4 : plaquetteDefect (chartedField (shiftCoords w η) V) p ≤
        plaquetteDefect (chartedField w V) p + 4 * T.ballRadius := h1
    linarith
  have hcon : ∀ (c : F.Site F.top × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube T.L →
      ‖contourHolonomyDefect (chartedField (shiftCoords w η) V) V c h π - 1‖ ≤ 1 / 2 := by
    intro c h π hh
    have h1 := (hM F V w η T.ballRadius hOddF hη hρ0.le).2.2 c h π (hFL ▸ hh)
    have h2 := hp.contour_near_one c h π hh
    rw [hFL] at h1
    have h4 : ‖contourHolonomyDefect (chartedField (shiftCoords w η) V) V c h π - 1‖ ≤
        ‖contourHolonomyDefect (chartedField w V) V c h π - 1‖ + 5 * (T.L : ℝ) * T.ballRadius := h1
    linarith
  set A : ℝ := T.a * x with hAd
  have Gt := hGt F V (shiftCoords w η) A hFL hpos hA hsz hcon
  have Ht := hH F (shiftCoords w η) hsz
  have Rt := hR T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f F V (shiftCoords w η) hδ0.le hE0 hrow hlow hsz hcold
  set c₀ : ℝ := -(x * chartedEnergyAt T.a w V 0) with hc₀
  have hform : ∀ ζ, exponentMinusEnergy T.a x w f ν V ζ = c₀ + (-1) * readInChart (gapExcessSum A) w V ζ +
      (-1) * haarExcessSum w ζ + (-ν) * readInChart (centredExpansionSum f) w V ζ := by
    intro ζ
    unfold exponentMinusEnergy exponentInChart
    rw [hc₀]
    ring
  have hshift : (fun ζ => exponentMinusEnergy T.a x w f ν V (η + ζ)) =
      fun ζ => c₀ + (-1) * readInChart (gapExcessSum A) (shiftCoords w η) V ζ +
        (-1) * haarExcessSum (shiftCoords w η) ζ +
        (-ν) * readInChart (centredExpansionSum f) (shiftCoords w η) V ζ := by
    funext ζ
    rw [hform, readInChart_add, readInChart_add, haarExcessSum_add]
  have hlin := fun u : StepVariable (finiteCells F) =>
    contDiffAt_fderiv_linearCombination c₀ (-1) (-1) (-ν) Gt.1 Ht.1 Rt.1 u
  refine ⟨?_, ?_⟩
  · have : ContDiffAt ℝ 3 (exponentMinusEnergy T.a x w f ν V) η := by
      apply contDiffAt_of_translate
      rw [hshift]
      exact (hlin 0).1
    exact this.differentiableAt (by norm_num)
  · intro b e
    have hfst := (hlin (bondVariation b e)).2
    have e1 : bondPartialDeriv (exponentMinusEnergy T.a x w f ν V) b η e =
        fderiv ℝ (fun ζ => exponentMinusEnergy T.a x w f ν V (η + ζ)) 0 (bondVariation b e) := by
      rw [fderiv_translate_zero]
      rfl
    rw [e1, hshift, hfst]
    have g1 := (Gt.2 b b e e).1
    have h1 := (Ht.2 b b e e).1
    have r1 := (Rt.2 b b e e).1
    have hν : |ν| ≤ 1 := by
      rw [abs_of_nonneg hν0]
      exact hν1
    have hsymm : ∀ y z : F.Site F.depth, siteSupDist y z = siteSupDist z y :=
      fun y z => (hD.1 F F.depth y z y).2.1
    have hsum : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        Real.exp (-(T.decayRate * (siteSupDist y b.1.1 : ℝ))) ≤ Sf T.decayRate := by
      have := hSδ.2 F F.depth b.1.1 (sitesOfCells (finiteCells F) F.depth)
      simpa only [hsymm b.1.1] using this
    have hr1 : |fderiv ℝ (readInChart (centredExpansionSum f) (shiftCoords w η) V) 0 (bondVariation b e)| ≤
        Cr * T.E * Sf T.decayRate * ‖e‖ := by
      refine r1.trans ?_
      have : 0 ≤ Cr * T.E := by positivity
      gcongr
    have hne := norm_nonneg e
    set X₁ := fderiv ℝ (readInChart (gapExcessSum A) (shiftCoords w η) V) 0 (bondVariation b e)
    set X₂ := fderiv ℝ (haarExcessSum (shiftCoords w η)) 0 (bondVariation b e)
    set X₃ := fderiv ℝ (readInChart (centredExpansionSum f) (shiftCoords w η) V) 0 (bondVariation b e)
    have hνX : |(-ν) * X₃| ≤ Cr * T.E * Sf T.decayRate * ‖e‖ := by
      rw [abs_mul, abs_neg]
      calc |ν| * |X₃| ≤ 1 * |X₃| := mul_le_mul_of_nonneg_right hν (abs_nonneg _)
        _ = |X₃| := one_mul _
        _ ≤ _ := hr1
    calc |(-1) * X₁ + (-1) * X₂ + (-ν) * X₃| ≤ |(-1) * X₁| + |(-1) * X₂| + |(-ν) * X₃| :=
          abs_add_three _ _ _
      _ = |X₁| + |X₂| + |(-ν) * X₃| := by simp
      _ ≤ (Cgf T.L + CH + Cr * T.E * Sf T.decayRate) * ‖e‖ := by nlinarith
end YangMills.Construction.ResponseInTheExpansion.RemainderSlope
end
