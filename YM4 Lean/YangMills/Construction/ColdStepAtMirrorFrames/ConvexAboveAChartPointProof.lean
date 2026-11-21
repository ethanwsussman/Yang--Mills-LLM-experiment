import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPoint
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexityFromAFloorAndRows
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsOfTheChartEnergy
import YangMills.Construction.ColdStepAtMirrorFrames.FramesOnTheParameters
import YangMills.Construction.ColdStepAtMirrorFrames.MovingTheChartCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace HessianConvexity
section Calculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
theorem contDiffAt_of_comp_add_left {f : P → ℝ} {η : P} (h : ContDiffAt ℝ 3 (fun ζ => f (η + ζ)) 0) :
    ContDiffAt ℝ 3 f η := by
  have h1 : ContDiffAt ℝ 3 (fun ξ : P => ξ - η) η := (contDiff_id.sub contDiff_const).contDiffAt
  have h2 : ContDiffAt ℝ 3 (fun ζ => f (η + ζ)) ((fun ξ : P => ξ - η) η) := by simpa using h
  have h3 := ContDiffAt.comp (f := fun ξ : P => ξ - η) η h2 h1
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ξ => ?_)
  simp
theorem fderiv_comp_add_left_zero_apply (f : P → ℝ) (η u : P) :
    fderiv ℝ (fun ζ => f (η + ζ)) 0 u = fderiv ℝ f η u := by
  rw [fderiv_comp_add_left]
  simp
theorem fderiv_fderiv_comp_add_left_zero (f : P → ℝ) (η u v : P) :
    fderiv ℝ (fun ζ => fderiv ℝ (fun ξ => f (η + ξ)) ζ u) 0 v =
      fderiv ℝ (fun ζ => fderiv ℝ f ζ u) η v := by
  have h1 : (fun ζ => fderiv ℝ (fun ξ => f (η + ξ)) ζ u) = fun ζ => fderiv ℝ f (η + ζ) u := by
    funext ζ
    rw [fderiv_comp_add_left]
  rw [h1]
  exact fderiv_comp_add_left_zero_apply (fun ζ => fderiv ℝ f ζ u) η v
theorem deriv_deriv_line_eq {f : P → ℝ} {η : P} (hf : ContDiffAt ℝ 3 f η) (u : P) :
    deriv (deriv fun τ : ℝ => f (η + τ • u)) 0 = fderiv ℝ (fun ζ => fderiv ℝ f ζ u) η u := by
  have hl : ∀ τ : ℝ, HasDerivAt (fun s : ℝ => η + s • u) u τ := fun τ => by
    simpa using ((hasDerivAt_id τ).smul_const u).const_add η
  have hc : ContinuousAt (fun s : ℝ => η + s • u) 0 := (hl 0).continuousAt
  have hc0 : (fun s : ℝ => η + s • u) 0 = η := by simp
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), ContDiffAt ℝ 3 f (η + τ • u) := by
    have h1 : ∀ᶠ ζ in 𝓝 ((fun s : ℝ => η + s • u) 0), ContDiffAt ℝ 3 f ζ := by
      rw [hc0]
      exact hf.eventually (by simp)
    exact hc.eventually h1
  have hd : (deriv fun τ : ℝ => f (η + τ • u)) =ᶠ[𝓝 0] fun τ => fderiv ℝ f (η + τ • u) u := by
    filter_upwards [hev] with τ hτ
    have h1 : DifferentiableAt ℝ f (η + τ • u) := hτ.differentiableAt (by norm_num)
    exact (h1.hasFDerivAt.comp_hasDerivAt τ (hl τ)).deriv
  rw [hd.deriv_eq]
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) η := hf.fderiv_right (by norm_num)
  have h3 : DifferentiableAt ℝ (fun ζ => fderiv ℝ f ζ u) η :=
    (h2.differentiableAt (by norm_num)).clm_apply (differentiableAt_const u)
  have h4 : DifferentiableAt ℝ (fun ζ => fderiv ℝ f ζ u) ((fun s : ℝ => η + s • u) 0) := by
    rw [hc0]
    exact h3
  have h5 := h4.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hl 0)
  have h6 := h5.deriv
  simpa [Function.comp_def, hc0] using h6
end Calculus
def toImaginaryCLM : BondVector →L[ℝ] imaginaryQuaternions :=
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
theorem toImaginaryCLM_apply (v : BondVector) : toImaginaryCLM v = toImaginary v := rfl
theorem norm_toImaginaryCLM (v : BondVector) : ‖toImaginaryCLM v‖ = ‖v‖ := by
  have h1 : ‖toImaginaryCLM v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := Quaternion.normSq_eq_norm_mul_self ((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])
    rw [Quaternion.normSq_def'] at h
    have h2 : ‖(toImaginaryCLM v : imaginaryQuaternions)‖ =
        ‖((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
    rw [h2, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, pow_two]
    simp only [toImaginaryCLM_apply, toImaginary, Real.norm_eq_abs, sq_abs] at h ⊢
    linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
theorem stepCoordinates_add (η ζ : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (η + ζ) x i = stepCoordinates η x i + stepCoordinates ζ x i := by
  classical
  unfold stepCoordinates
  split_ifs with h
  · rw [← toImaginaryCLM_apply, ← toImaginaryCLM_apply, ← toImaginaryCLM_apply, ← map_add]
    rfl
  · simp
theorem stepCoordinates_smul (r : ℝ) (η : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (r • η) x i = r • stepCoordinates η x i := by
  classical
  unfold stepCoordinates
  split_ifs with h
  · rw [← toImaginaryCLM_apply, ← toImaginaryCLM_apply, ← map_smul]
    rfl
  · simp
theorem stepCoordinates_of_not_mem (η : StepVariable (finiteCells F)) {b : F.Site F.depth × Fin 4}
    (hb : b ∉ chordBonds (finiteCells F)) : stepCoordinates η b.1 b.2 = 0 := by
  classical
  unfold stepCoordinates
  rw [dif_neg hb]
theorem stepCoordinates_chordBond (η : StepVariable (finiteCells F)) (b : ChordBond F) :
    stepCoordinates η b.1.1 b.1.2 = toImaginaryCLM (η b) := by
  classical
  unfold stepCoordinates
  rw [dif_pos b.2]
  rfl
def shiftedCoords (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (η : StepVariable (finiteCells F)) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => w x i + stepCoordinates η x i
theorem chartedEnergyAt_add (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (η ζ : StepVariable (finiteCells F)) :
    chartedEnergyAt a w V (η + ζ) = chartedEnergyAt a (shiftedCoords w η) V ζ := by
  unfold chartedEnergyAt
  congr 1
  funext x i
  simp only [shiftedCoords, stepCoordinates_add, add_assoc]
theorem chartedField_congr (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (h : ∀ b ∈ chordBonds (finiteCells F), w b.1 b.2 = w' b.1 b.2) :
    chartedField w V = chartedField w' V := by
  classical
  funext x i
  by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
  · have := h _ hb
    simp only [chartedField] at *
    rw [this]
  · have hbond : (x, i) ∈ innerBonds (finiteCells F) F.depth := by
      unfold innerBonds
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hB F hL hs x, Finset.mem_univ _⟩, hB F hL hs _⟩
    have htree : IsAxialTreeBond (x, i) := by
      by_contra hn
      exact hb (Finset.mem_filter.2 ⟨hbond, hn⟩)
    have hnc : ¬ IsCrossingBond (x, i) := htree.1
    simp only [chartedField, hnc, htree, if_true, if_false]
set_option maxHeartbeats 2000000 in
theorem convexAboveChartPoint_holds (hC : ConvexityOfHessianFloorPlusSmallRows) (hO : RemainderExponentBounds)
    (hR : ChartEnergyHessianRowsEventually) (hFr : FrameBoundsEventually)
    (hJ : EventuallyInParametersCombines) (hM : ChartShiftLipschitz)
    (hB : BlocksCoverLowerLevel) : ConvexAboveChartPoint := by
  classical
  refine hJ.2 _ _ ?_ (hJ.1 _ _ hO (hJ.1 _ _ hR hFr))
  rintro T hT ⟨hOt, hRt, hfr⟩
  obtain ⟨Cf, C, _, _, hCfT, hCT', hL40, hn64, hκ1, hσ1, _, _, hσA, hy1, hay, _⟩ := hfr
  have hρ0 : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    have := hT.σ_pos
    positivity
  have hlam : 0 < T.chainParams.lam := hT.chain_admissible.positivity.2.2.1
  have hCt0 : 0 < T.Ct := by linarith
  intro t x f F V w ν hx hrow hF hV hp hsl hν0 hν1
  have hOdd : Odd T.L := hT.odd_L
  have hκ0 : 0 < T.κ := hT.κ_pos
  have hσ0 : 0 < T.σ := hT.σ_pos
  have hx1 : 1 ≤ x := hy1.trans hx
  have hx0 : 0 < x := by linarith
  have hFcopy := hF
  obtain ⟨hFL, hFt, n, hside, hn⟩ := hFcopy
  have hn0 : 64 ≤ n := hn64.trans hn
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside]; omega
  have hOddF : Odd F.blockSide := hFL ▸ hOdd
  have hCT : IsBlockTorus T.L F := ⟨hFL, n, hn0, hside⟩
  obtain ⟨KR, hKR0, hKRs, hRsm, hRker, hRrow, hRsl⟩ := hOt t x f F V w ν hx hrow hF hp hν0 hν1
  obtain ⟨KA, hKAs, hKAp, hKArow, hKAM⟩ := hRt F V hCT
  have hclauses := hT.chain_admissible.estimates F (5 / 4 * T.σ) V hCT (by positivity) hσA hV
  have hfloor := hclauses.hessian
  have hcoord : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) → ∀ x i,
      ‖stepCoordinates η x i‖ ≤ T.ballRadius := fun η hη => (hM F V w η T.ballRadius hOddF hη hρ0.le).1
  have hcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature T.σ (chartedField (shiftedCoords w η) V) := by
    intro η hη p hp'
    have h1 := (hM F V w η T.ballRadius hOddF hη hρ0.le).2.1 p
    have h2 := hp.curvature_small p hp'
    have h3 : T.ballRadius = T.σ / 64 := rfl
    have h4 : plaquetteDefect (chartedField (shiftedCoords w η) V) p ≤
        plaquetteDefect (chartedField w V) p + 4 * T.ballRadius := h1
    linarith
  have hσσ : T.σ ≤ T.chainParams.σA := by linarith
  have hsmall : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsAdmissibleChartPoint T.L T.chainParams.σA (shiftedCoords w η) V := by
    intro η hη
    refine ⟨fun b hb => ?_, fun p hp' => (hcold η hη p hp').trans_le hσσ⟩
    have h1 := hcoord η hη b.1 b.2
    have h2 := hp.small b hb
    calc ‖shiftedCoords w η b.1 b.2‖ ≤ ‖w b.1 b.2‖ + ‖stepCoordinates η b.1 b.2‖ := norm_add_le _ _
      _ ≤ ‖w b.1 b.2‖ + T.ballRadius := by linarith
      _ ≤ _ := h2
  set A : StepVariable (finiteCells F) → ℝ := chartedEnergyAt T.a w V with hA
  have hshift : ∀ η : StepVariable (finiteCells F),
      (fun ζ => A (η + ζ)) = chartedEnergyAt T.a (shiftedCoords w η) V :=
    fun η => funext fun ζ => chartedEnergyAt_add T.a w V η ζ
  have hAsm : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ 3 A η := by
    intro η hη
    apply contDiffAt_of_comp_add_left
    rw [hshift]
    exact (hKAp _ (hsmall η hη)).1
  have hAker : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      ∀ (b b' : ChordBond F) (e e' : BondVector),
      |secondDerivAlong A η (bondVariation b e) (bondVariation b' e')| ≤ KA b b' * ‖e‖ * ‖e'‖ := by
    intro η hη b b' e e'
    have h1 := (hKAp _ (hsmall η fun b => (hη b).le)).2 b b' e e'
    have h2 : secondDerivAlong A η (bondVariation b e) (bondVariation b' e') =
        secondDerivAlong (chartedEnergyAt T.a (shiftedCoords w η) V) 0
          (bondVariation b e) (bondVariation b' e') := by
      unfold secondDerivAlong
      rw [← hshift, fderiv_fderiv_comp_add_left_zero]
    rw [h2]
    exact h1
  have hAfl : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      ∀ u : StepVariable (finiteCells F),
      T.chainParams.lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong A η u u := by
    intro η hη u
    have hη' : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
    set wm : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
      fun x i => if (x, i) ∈ chordBonds (finiteCells F) then shiftedCoords w η x i else 0 with hwm
    have h1 := hfloor wm (stepCoordinates u)
      (fun b hb => by simp only [hwm]; rw [if_neg hb])
      (fun b hb => stepCoordinates_of_not_mem u hb)
      (fun b hb => by
        simp only [hwm]
        rw [if_pos hb]
        have h2 := hcoord η hη' b.1 b.2
        have h3 := hp.room b hb
        calc ‖shiftedCoords w η b.1 b.2‖ ≤ ‖w b.1 b.2‖ + ‖stepCoordinates η b.1 b.2‖ := norm_add_le _ _
          _ ≤ ‖w b.1 b.2‖ + T.ballRadius := by linarith
          _ ≤ _ := h3)
      (by
        have e : chartedField wm V = chartedField (shiftedCoords w η) V :=
          chartedField_congr hB hOddF hpos V fun b hb => by simp only [hwm]; rw [if_pos hb]
        rw [e]
        intro p hp'
        have hlt : p.2.1 < p.2.2 := (Finset.mem_filter.1 hp').2.1
        exact (hcold η hη' p hlt).trans_le hσσ)
    have hsum : ∑ b ∈ chordBonds (finiteCells F), ‖stepCoordinates u b.1 b.2‖ ^ 2 =
        ∑ b : ChordBond F, ‖u b‖ ^ 2 := by
      rw [← Finset.sum_coe_sort]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [stepCoordinates_chordBond, norm_toImaginaryCLM]
    have hfun : (fun τ : ℝ => blockEnergy T.a (finiteCells F) F.depth
        (chartedField (fun x i => wm x i + τ • stepCoordinates u x i) V) V) =
        fun τ : ℝ => A (η + τ • u) := by
      funext τ
      have e : chartedField (fun x i => wm x i + τ • stepCoordinates u x i) V =
          chartedField (fun x i => w x i + stepCoordinates (η + τ • u) x i) V := by
        refine chartedField_congr hB hOddF hpos V fun b hb => ?_
        simp only [hwm]
        rw [if_pos hb, stepCoordinates_add, stepCoordinates_smul]
        simp only [shiftedCoords, add_assoc]
      rw [e]
      rfl
    rw [hsum, hfun, deriv_deriv_line_eq (hAsm η hη') u] at h1
    exact h1
  obtain ⟨Ψ, hΨe, hΨc, hΨp⟩ := hC (ChordBond F) T.ballRadius x T.chainParams.lam T.κ (chordBondDist F) A
    (exponentMinusEnergy T.a x w f ν V) KA KR hρ0 hx0 hlam hκ0.le (fun b b' => Nat.cast_nonneg _) hAsm hRsm hAfl
    hAker hRker hKAs hKRs hKR0 hKArow hRrow
  have hs1 : ∀ (b : ChordBond F) (e : BondVector), x * |bondPartialDeriv A b 0 e| ≤ ‖e‖ := by
    intro b e
    by_cases he : e = 0
    · subst he
      have : bondPartialDeriv A b 0 0 = 0 := by
        unfold bondPartialDeriv bondVariation
        simp
      simp [this]
    · have hn' : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
      have hu : ‖(‖e‖⁻¹ • e : BondVector)‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn']
      have h1 := hsl b _ hu
      have e1 : bondPartialDeriv A b 0 e = ‖e‖ * bondPartialDeriv A b 0 (‖e‖⁻¹ • e) := by
        have e2 : (bondVariation b e : StepVariable (finiteCells F)) =
            ‖e‖ • bondVariation b (‖e‖⁻¹ • e) := by
          unfold bondVariation
          rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hn', one_smul]
        change fderiv ℝ A 0 (bondVariation b e) = ‖e‖ * fderiv ℝ A 0 (bondVariation b (‖e‖⁻¹ • e))
        conv_lhs => rw [e2]
        rw [map_smul, smul_eq_mul]
      rw [e1, abs_mul, abs_norm]
      have hp' := norm_nonneg e
      calc x * (‖e‖ * |bondPartialDeriv A b 0 (‖e‖⁻¹ • e)|) =
          ‖e‖ * (x * |bondPartialDeriv A b 0 (‖e‖⁻¹ • e)|) := by ring
        _ ≤ ‖e‖ * 1 := mul_le_mul_of_nonneg_left h1 hp'
        _ = ‖e‖ := mul_one _
  have hexp : exponentInChart T.a x w f ν V =
      fun η => x * A η + exponentMinusEnergy T.a x w f ν V η := by
    funext η
    unfold exponentMinusEnergy
    rw [hA]
    ring
  refine ⟨⟨Ψ, fun b b' => x * KA b b' + KR b b', ?_, hΨc, ?_⟩, ?_⟩
  · intro η hη
    rw [hΨe η hη, hexp]
  · intro b e
    rw [hΨp]
    have h2 := hRsl 0 (fun b => by simpa using hρ0.le) b e
    calc _ ≤ |x * bondPartialDeriv A b 0 e| +
          |bondPartialDeriv (exponentMinusEnergy T.a x w f ν V) b 0 e| := abs_add_le _ _
      _ = x * |bondPartialDeriv A b 0 e| +
          |bondPartialDeriv (exponentMinusEnergy T.a x w f ν V) b 0 e| := by
          rw [abs_mul, abs_of_pos hx0]
      _ ≤ ‖e‖ + (Real.sqrt (x * T.chainParams.lam / 4) - 1) * ‖e‖ := add_le_add (hs1 b e) h2
      _ = _ := by ring
  · intro η hη b e
    have hη' : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
    have hne := norm_nonneg e
    set u : StepVariable (finiteCells F) := bondVariation b e with hu
    have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ b', ‖(t • η) b'‖ < T.ballRadius := by
      intro t h0 h1 b'
      have : ‖(t • η) b'‖ = |t| * ‖η b'‖ := by
        rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
      rw [this, abs_of_nonneg h0]
      have h2 := norm_nonneg (η b')
      have h3 := hη b'
      nlinarith
    have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
        ‖fderiv ℝ (fun ζ => fderiv ℝ A ζ u) (t • η) η‖ ≤ T.Ct * T.ballRadius * ‖e‖ := by
      intro t ht
      have hb := hseg t ht.1 ht.2.le
      have hd2 : ContDiffAt ℝ 2 (fderiv ℝ A) (t • η) :=
        (hAsm _ fun b' => (hb b').le).fderiv_right (by norm_num)
      have hsum : η = ∑ b' : ChordBond F, (bondVariation b' (η b') : StepVariable (finiteCells F)) := by
        funext d
        rw [Finset.sum_apply, Finset.sum_eq_single d]
        · simp [bondVariation]
        · intro b' _ hb'
          exact Pi.single_eq_of_ne (Ne.symm hb') _
        · intro h
          exact absurd (Finset.mem_univ d) h
      have hlin : fderiv ℝ (fun ζ => fderiv ℝ A ζ u) (t • η) η =
          ∑ b' : ChordBond F, secondDerivAlong A (t • η) u (bondVariation b' (η b')) := by
        have e3 : fderiv ℝ (fun ζ => fderiv ℝ A ζ u) (t • η)
            (∑ b' : ChordBond F, (bondVariation b' (η b') : StepVariable (finiteCells F))) =
            ∑ b' : ChordBond F, fderiv ℝ (fun ζ => fderiv ℝ A ζ u) (t • η) (bondVariation b' (η b')) :=
          map_sum _ _ _
        rw [← hsum] at e3
        exact e3
      rw [hlin, Real.norm_eq_abs]
      calc _ ≤ ∑ b' : ChordBond F, |secondDerivAlong A (t • η) u (bondVariation b' (η b'))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ b' : ChordBond F, KA b b' * ‖e‖ * T.ballRadius := by
            refine Finset.sum_le_sum fun b' _ => ?_
            have h1 := hAker (t • η) hb b b' e (η b')
            refine h1.trans ?_
            have hK : 0 ≤ KA b b' * ‖e‖ := by
              have h2 := abs_nonneg (secondDerivAlong A 0 (bondVariation b (EuclideanSpace.single 0 1))
                (bondVariation b' (EuclideanSpace.single 0 1)))
              have h3 := hAker 0 (fun b => by simpa using hρ0) b b' (EuclideanSpace.single 0 1)
                (EuclideanSpace.single 0 1)
              have h4 : ‖(EuclideanSpace.single 0 1 : BondVector)‖ = 1 := by simp
              rw [h4] at h3
              have h5 : 0 ≤ KA b b' := by linarith
              positivity
            exact mul_le_mul_of_nonneg_left (hη' b') hK
        _ = (∑ b' : ChordBond F, KA b b') * ‖e‖ * T.ballRadius := by
            rw [Finset.sum_mul, Finset.sum_mul]
        _ ≤ T.Ct * ‖e‖ * T.ballRadius := by
            have := hKAM b
            gcongr
        _ = _ := by ring
    have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => fderiv ℝ A (s • η) u)
        (fderiv ℝ (fun ζ => fderiv ℝ A ζ u) (t • η) η) (Set.Icc 0 1) t := by
      intro t ht
      have hb := hseg t ht.1 ht.2
      have hd2 : ContDiffAt ℝ 2 (fderiv ℝ A) (t • η) :=
        (hAsm _ fun b' => (hb b').le).fderiv_right (by norm_num)
      have hd : DifferentiableAt ℝ (fun ζ => fderiv ℝ A ζ u) (t • η) :=
        (hd2.differentiableAt (by norm_num)).clm_apply (differentiableAt_const u)
      have hl : HasDerivAt (fun s : ℝ => s • η) η t := by
        simpa using (hasDerivAt_id t).smul_const η
      exact (hd.hasFDerivAt.comp_hasDerivAt t hl).hasDerivWithinAt
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun s : ℝ => fderiv ℝ A (s • η) u)
      (f' := fun t => fderiv ℝ (fun ζ => fderiv ℝ A ζ u) (t • η) η) hderiv hbound
    simp only [one_smul, zero_smul] at hmv
    have hAη : |bondPartialDeriv A b η e| ≤ |bondPartialDeriv A b 0 e| + T.Ct * T.ballRadius * ‖e‖ := by
      have : bondPartialDeriv A b η e - bondPartialDeriv A b 0 e = fderiv ℝ A η u - fderiv ℝ A 0 u := rfl
      have h1 : |bondPartialDeriv A b η e - bondPartialDeriv A b 0 e| ≤ T.Ct * T.ballRadius * ‖e‖ := by
        rw [this, ← Real.norm_eq_abs]
        exact hmv
      have h2 := abs_sub_abs_le_abs_sub (bondPartialDeriv A b η e) (bondPartialDeriv A b 0 e)
      linarith
    have hdA : DifferentiableAt ℝ A η := (hAsm η hη').differentiableAt (by norm_num)
    have hdR : DifferentiableAt ℝ (exponentMinusEnergy T.a x w f ν V) η :=
      (hRsm η hη').differentiableAt (by norm_num)
    have hpart : bondPartialDeriv (exponentInChart T.a x w f ν V) b η e =
        x * bondPartialDeriv A b η e + bondPartialDeriv (exponentMinusEnergy T.a x w f ν V) b η e := by
      rw [hexp]
      have h1 : HasFDerivAt (fun ζ => x * A ζ + exponentMinusEnergy T.a x w f ν V ζ)
          (x • fderiv ℝ A η + fderiv ℝ (exponentMinusEnergy T.a x w f ν V) η) η :=
        (hdA.hasFDerivAt.const_mul x).add hdR.hasFDerivAt
      unfold bondPartialDeriv
      rw [h1.fderiv]
      simp
    rw [hpart]
    have h3 := hRsl η hη' b e
    have hsq : Real.sqrt (x * T.chainParams.lam / 4) ≤ (T.chainParams.lam + 1) * x := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [mul_pos hlam hx0, sq_nonneg (x * T.chainParams.lam), mul_pos hx0 hx0]
    have h4 : x * |bondPartialDeriv A b η e| ≤ ‖e‖ + x * (T.Ct * T.ballRadius * ‖e‖) := by
      have := mul_le_mul_of_nonneg_left hAη hx0.le
      have h5 := hs1 b e
      nlinarith
    calc _ ≤ |x * bondPartialDeriv A b η e| +
          |bondPartialDeriv (exponentMinusEnergy T.a x w f ν V) b η e| := abs_add_le _ _
      _ = x * |bondPartialDeriv A b η e| +
          |bondPartialDeriv (exponentMinusEnergy T.a x w f ν V) b η e| := by
          rw [abs_mul, abs_of_pos hx0]
      _ ≤ (‖e‖ + x * (T.Ct * T.ballRadius * ‖e‖)) + (Real.sqrt (x * T.chainParams.lam / 4) - 1) * ‖e‖ :=
          add_le_add h4 h3
      _ = (x * (T.Ct * T.ballRadius) + Real.sqrt (x * T.chainParams.lam / 4)) * ‖e‖ := by ring
      _ ≤ (T.Ct * T.ballRadius + T.chainParams.lam + 1) * x * ‖e‖ := by
          refine mul_le_mul_of_nonneg_right ?_ hne
          nlinarith
end HessianConvexity
end YangMills.Construction.ColdStepAtMirrorFrames
end
