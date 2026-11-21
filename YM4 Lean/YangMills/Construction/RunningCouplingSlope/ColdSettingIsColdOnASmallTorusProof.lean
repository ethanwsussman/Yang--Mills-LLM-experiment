import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsColdProof
import YangMills.Construction.ClusterExpansionOfAStep.FrameOnASmallTorus
import YangMills.Construction.RunningCouplingSlope.ColdSettingIsColdOnASmallTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open MeasureTheory BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings
  StepCosts StepMarks RenormalizationStepParameters ColdChain
namespace ColdChartOnSmallTorus
section Chart
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem chartCoord_coldField (hcov : BlocksCoverLowerLevel) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free) (b : ↥(coldChartSetting R V).free)
    (hw : ‖(((coldChartSetting R V).frame b.1 + toImaginary (η b) : imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi) :
    chartCoord R.params V ((coldChartSetting R V).field η) b.1 =
      (coldChartSetting R V).frame b.1 + toImaginary (η b) := by apply _root_.YangMills.Construction.ColdChartFields.chartCoord_coldField <;> assumption
end Chart
end ColdChartOnSmallTorus
namespace ColdChartOnSmallTorus
theorem norm_bondFrameCoord_le {F : BlockFrame} (a ρ : ℝ) (hρ : 0 ≤ ρ) (m : ℕ) (b : F.Site F.depth × Fin 4)
    (V : F.GaugeField F.top) : ‖bondFrameCoord a ρ m b V‖ ≤ ρ := by apply _root_.YangMills.Construction.LogJacobian.norm_bondFrameCoord_le <;> assumption
theorem rangesAdmissible_clusterRange (T : ParameterAssignment) (hT : T.Admissible) (y x : ℝ) (hy : T.floorMin ≤ y)
    (hx : y ≤ x) : RangesAdmissible (clusterRange x) (clusterRange x) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TorusTransfer.rangesAdmissible_clusterRange <;> assumption
theorem curvature_lt_of_frame_eq_minimizer (hc : ComplementOfThickenedLumpsRegular)
    (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (δ lam ρA σA cg : ℝ) (N : ℕ → ℝ) (hfit : ℓ.Admissible)
    (hch : ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N) (hσ : 2 * ℓ.threshold ≤ σA)
    (t r r' n : ℕ) [NeZero n] (V : TorusField n) (S C : Finset (TorusSite n)) (s : ℝ) (hr : RangesAdmissible r r')
    (hsit : IsStepSituation ℓ r' V S C s)
    (hfr : ∀ b : TorusBond (n * ℓ.side),
      frameCoord ℓ ρA t (r / 2 ^ 11) V b = minimizerCoord ℓ.coupling ρA ℓ.side t S V b)
    (W : TorusField (n * ℓ.side)) (x : TorusSite (n * ℓ.side)) (μ ν : Fin 4) (hlt : μ < ν)
    (hoff : ∀ z ∈ plaquetteVertices x μ ν, parentBlock ℓ.side z ∉ C)
    (hgood : ∀ b ∈ StepCosts.chartBonds ℓ.side n,
      (∃ z ∈ plaquetteVertices x μ ν, parentBlock ℓ.side b.1 = parentBlock ℓ.side z) →
      ‖(YangMills.Construction.StepMarks.frameDeviation ℓ ρA t (r / 2 ^ 11) V W b : ℍ[ℝ])‖ ≤ ℓ.threshold / 64) :
    curvature W x μ ν < ℓ.threshold / 4 := by
  obtain ⟨δpos, _, _, _, ρle, _, _, Npos, hbody⟩ := hch
  have hπ : ρA < Real.pi := lt_of_le_of_lt ρle (by linarith [Real.pi_gt_three])
  obtain ⟨spos, sle, n4096, hF⟩ := TopLevelSites.stepSituation_regular_and_cold hc hfit hsit
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  have hn₀ : ∀ i, (stepBlockFrame ℓ.side n).extent i = n := fun _ => rfl
  obtain ⟨hreg, hcold⟩ := hF (torusFrame ℓ.side t n) hn
  have hodd : Odd (torusFrame ℓ.side t n).blockSide := hfit.L_odd
  have hodd₀ : Odd (stepBlockFrame ℓ.side n).blockSide := hfit.L_odd
  have h2 : 2 ≤ n := by omega
  have hs2 : ∀ i, 2 ≤ (torusFrame ℓ.side t n).extent i := fun i => by rw [hn]; omega
  have hs₀ : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n).extent i := fun i => by rw [hn₀]; omega
  have hLpos : 0 < ℓ.side := hfit.L_odd.pos
  haveI hne0 : NeZero (n * ℓ.side) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  haveI : NeZero (n * (torusFrame ℓ.side t n).blockSide) := hne0
  haveI : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := hne0
  have hamb : IsAdmissibleAmbient (torusFrame ℓ.side t n) := Or.inr fun i => by rw [hn]; omega
  have one := (hbody (torusFrame ℓ.side t n) 2047 (cellsOfSites (torusFrame ℓ.side t n) S) rfl hamb (by norm_num)
    hreg s (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) spos (sle.trans hσ) hcold).1
  obtain ⟨w, hw, hcw, hlc⟩ :=
    TopLevelSites.minimizingCoordinates_eq (ρ := ρA) hfit.L_odd hs2 hπ le_rfl one
  have hp₀ : ∀ i, (stepBlockFrame ℓ.side n).period 0 i = n * ℓ.side :=
    fun i => TopLevelSites.period_depth_of_extent (F := stepBlockFrame ℓ.side n) hn₀ i
  have hpF : ∀ i, (torusFrame ℓ.side t n).period (torusFrame ℓ.side t n).depth i = n * ℓ.side :=
    fun i => TopLevelSites.period_depth_of_extent (F := torusFrame ℓ.side t n) hn i
  set Wr := readAtLevel (stepBlockFrame ℓ.side n) 0 W with hWr
  set V₀ := readAtLevel (stepBlockFrame ℓ.side n) 1 V with hV₀
  set VF := readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V with hVF
  let G : TorusField (n * ℓ.side) := fun z i =>
    BlockAverages.gaugeTransform (axialGauge 1 Wr) Wr (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z) i
  let Ws : TorusField (n * ℓ.side) := fun z i =>
    chartedField w VF (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z) i
  have hG : curvature G x μ ν = curvature W x μ ν := by
    have e : G = TorusFields.gaugeTransform
        (fun z => axialGauge 1 Wr (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z)) W := by
      funext z i
      simp only [G, TorusFields.gaugeTransform, BlockAverages.gaugeTransform]
      rw [show Wr (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z) i = W z i from
        TopLevelSites.readAtLevel_torusSiteInFrame hp₀ W z i]
      have hun : (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z +
          BlockAverages.unitStep (stepBlockFrame ℓ.side n).depth i : (stepBlockFrame ℓ.side n).Site 0) =
          torusSiteInFrame (stepBlockFrame ℓ.side n) 0 (z + TorusFields.unitStep (n * ℓ.side) i) := by
        apply TopLevelSites.toTorusSite_injective hp₀
        rw [TopLevelSites.toTorusSite_torusSiteInFrame hp₀]
        exact (TopLevelSites.toTorusSite_add hp₀ _ _).trans
          (congrArg₂ (· + ·) (TopLevelSites.toTorusSite_torusSiteInFrame hp₀ z)
            (TopLevelSites.toTorusSite_unitStep hp₀ i))
      exact congrArg (fun q : (stepBlockFrame ℓ.side n).Site 0 =>
        axialGauge 1 Wr (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z) * W z i * (axialGauge 1 Wr q)⁻¹) hun
    rw [e, TorusFields.curvature_gaugeTransform]
  have hmemS : ∀ z ∈ plaquetteVertices x μ ν, parentBlock ℓ.side z ∈ S := by
    intro z hz
    have h0 := (TopLevelSites.stepSituation_box_of_not_mem hfit hr hsit (hoff z hz)).1 0 fun i => by
      simp only [Pi.zero_apply, abs_zero]
      positivity
    have e0 : (siteOfInt 0 : TorusSite n) = 0 := by
      funext i
      simp [siteOfInt]
    rwa [e0, add_zero] at h0
  have hWs : curvature Ws x μ ν < s / 8 := by
    have hread : chartedField w VF = readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth Ws := by
      funext c i
      change _ = chartedField w VF
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth (toTorusSite _ c)) i
      rw [TopLevelSites.torusSiteInFrame_toTorusSite hpF]
    have hsite : ∀ z ∈ plaquetteVertices x μ ν,
        torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z ∈
          sitesOfCells (cellsOfSites (torusFrame ℓ.side t n) S) (torusFrame ℓ.side t n).depth :=
      fun z hz => TopLevelSites.torusSiteInFrame_mem_sitesOfCells (F := torusFrame ℓ.side t n) hn hodd h2 z
        (hmemS z hz)
    have hup : ∀ (z : TorusSite (n * ℓ.side)) (i : Fin 4),
        torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
            (z + TorusFields.unitStep (n * ℓ.side) i) =
          torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z +
            BlockAverages.unitStep (torusFrame ℓ.side t n).depth i := by
      intro z i
      apply TopLevelSites.toTorusSite_injective hpF
      rw [TopLevelSites.toTorusSite_torusSiteInFrame hpF, TopLevelSites.toTorusSite_add hpF,
        TopLevelSites.toTorusSite_torusSiteInFrame hpF, TopLevelSites.toTorusSite_unitStep hpF]
    have hp : ((torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth x, μ, ν) :
        (torusFrame ℓ.side t n).Site (torusFrame ℓ.side t n).depth × Fin 4 × Fin 4) ∈
        innerPlaquettes (cellsOfSites (torusFrame ℓ.side t n) S) (torusFrame ℓ.side t n).depth := by
      unfold innerPlaquettes
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hsite x (by simp [plaquetteVertices]), by simp⟩, hlt, ?_⟩
      intro c hc'
      simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
      rcases hc' with rfl | rfl | rfl | rfl
      · exact hsite x (by simp [plaquetteVertices])
      · rw [← hup]
        exact hsite _ (by simp [plaquetteVertices])
      · rw [← hup]
        exact hsite _ (by simp [plaquetteVertices])
      · rw [← hup, ← hup]
        exact hsite _ (by simp [plaquetteVertices])
    have h1 := hcw _ hp
    rw [hread, TopLevelSites.plaquetteDefect_readAtLevel_eq hpF, TopLevelSites.toTorusSite_torusSiteInFrame hpF] at h1
    exact h1
  have hbond : ∀ (z : TorusSite (n * ℓ.side)) (i : Fin 4), z ∈ plaquetteVertices x μ ν →
      ‖(G z i : ℍ[ℝ]) - Ws z i‖ ≤ ℓ.threshold / 64 + ℓ.threshold / 128 := by
    intro z i hz
    have hσpos := hfit.σ_pos
    have e1 : G z i = chartedField (fun x i => bondCoordinate 1 V₀ Wr (x, i)) V₀
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z) i :=
      TopLevelSites.axialGauge_eq_chartedField hodd₀ hs₀ V₀ Wr _ i
    have hcr : IsCrossingBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z, i) ↔
        IsCrossingBond (F := torusFrame ℓ.side t n)
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z, i) :=
      (TopLevelSites.isCrossingBond_torusSiteInFrame_iff (F := stepBlockFrame ℓ.side n) hn₀ hodd₀ h2 z i).trans
        (TopLevelSites.isCrossingBond_torusSiteInFrame_iff (F := torusFrame ℓ.side t n) hn hodd h2 z i).symm
    have htr : IsAxialTreeBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z, i) ↔
        IsAxialTreeBond (F := torusFrame ℓ.side t n)
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z, i) :=
      (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame ℓ.side n) hn₀ hodd₀ h2 z i).trans
        (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame ℓ.side t n) hn hodd h2 z i).symm
    have hVV : V₀ (enclosingCell (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z)) i =
        VF (enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z)) i := by
      have c0 : enclosingCell (torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth z) =
          torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top (parentBlock ℓ.side z) :=
        TopLevelSites.enclosingCell_torusSiteInFrame hn₀ z
      have c1 : enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z) =
          torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side z) :=
        TopLevelSites.enclosingCell_torusSiteInFrame hn z
      have r0 := TopLevelSites.readAtLevel_torusSiteInFrame
        (TopLevelSites.period_top_of_extent (F := stepBlockFrame ℓ.side n) hn₀) V (parentBlock ℓ.side z) i
      have r1 := TopLevelSites.readAtLevel_torusSiteInFrame
        (TopLevelSites.period_top_of_extent (F := torusFrame ℓ.side t n) hn) V (parentBlock ℓ.side z) i
      rw [c1, hVF, r1]
      exact (congrArg (fun c => readAtLevel (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top V c i) c0).trans r0
    by_cases ht : IsAxialTreeBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z, i)
    · have ht' := htr.mp ht
      have a1 : G z i = 1 := by
        rw [e1]
        unfold chartedField
        rw [if_neg ht.1, if_pos ht]
      have a2 : Ws z i = 1 := by
        simp only [Ws]
        unfold chartedField
        rw [if_neg ht'.1, if_pos ht']
      rw [a1, a2, sub_self, norm_zero]
      positivity
    · have hb : (z, i) ∈ StepCosts.chartBonds ℓ.side n := by
        classical
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
      have hgm := hgood (z, i) hb ⟨z, hz, rfl⟩
      have hnz : ‖((frameCoord ℓ ρA t (r / 2 ^ 11) V (z, i) : imaginaryQuaternions) : ℍ[ℝ]) -
          ((minimizerCoord ℓ.coupling ρA ℓ.side t S V (z, i) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
            ℓ.threshold / 128 := by
        rw [hfr (z, i), sub_self, norm_zero]
        positivity
      have hle : minimizerCoord ℓ.coupling ρA ℓ.side t S V (z, i) =
          w (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z) i := by
        unfold minimizerCoord minimizingBondCoordinate
        simp only
        rw [hlc]
      rw [hle] at hnz
      set c₁ : imaginaryQuaternions := bondCoordinate 1 V₀ Wr (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z, i)
        with hc₁
      set c₂ : imaginaryQuaternions :=
        w (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z) i with hc₂
      have hdist : ‖(c₁ : ℍ[ℝ]) - (c₂ : ℍ[ℝ])‖ ≤ ℓ.threshold / 64 + ℓ.threshold / 128 := by
        have e : (c₁ : ℍ[ℝ]) - (c₂ : ℍ[ℝ]) =
            ((YangMills.Construction.StepMarks.frameDeviation ℓ ρA t (r / 2 ^ 11) V W (z, i) : imaginaryQuaternions) : ℍ[ℝ]) +
            (((frameCoord ℓ ρA t (r / 2 ^ 11) V (z, i) : imaginaryQuaternions) : ℍ[ℝ]) - (c₂ : ℍ[ℝ])) := by
          have e' : ((YangMills.Construction.StepMarks.frameDeviation ℓ ρA t (r / 2 ^ 11) V W (z, i) : imaginaryQuaternions) : ℍ[ℝ]) =
              (c₁ : ℍ[ℝ]) - ((frameCoord ℓ ρA t (r / 2 ^ 11) V (z, i) : imaginaryQuaternions) : ℍ[ℝ]) := rfl
          rw [e']
          abel
        rw [e]
        refine (norm_add_le _ _).trans ?_
        linarith
      have hexp := TopLevelSites.norm_expUnit_sub_le c₁ c₂
      by_cases hcross : IsCrossingBond (F := stepBlockFrame ℓ.side n)
          (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z, i)
      · have a1 : G z i = expUnit c₁ * V₀ (enclosingCell (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z)) i := by
          rw [e1]
          unfold chartedField
          rw [if_pos hcross]
          rfl
        have a2 : Ws z i = expUnit c₂ *
            VF (enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z)) i := by
          simp only [Ws]
          unfold chartedField
          rw [if_pos (hcr.mp hcross)]
        rw [a1, a2, hVV]
        have := TopLevelSites.norm_mul_sub_mul_le (expUnit c₁) (expUnit c₂)
          (VF (enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z)) i)
          (VF (enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z)) i)
        rw [sub_self, norm_zero, add_zero] at this
        linarith
      · have a1 : G z i = expUnit c₁ := by
          rw [e1]
          unfold chartedField
          rw [if_neg hcross, if_neg ht]
        have a2 : Ws z i = expUnit c₂ := by
          simp only [Ws]
          unfold chartedField
          rw [if_neg (fun h => hcross (hcr.mpr h)), if_neg (fun h => ht (htr.mpr h))]
        rw [a1, a2]
        linarith
  have hmain := TopLevelSites.curvature_le_add G Ws x μ ν
  have b1 := hbond x μ (by simp [plaquetteVertices])
  have b2 := hbond (x + TorusFields.unitStep (n * ℓ.side) μ) ν (by simp [plaquetteVertices])
  have b3 := hbond (x + TorusFields.unitStep (n * ℓ.side) ν) μ (by simp [plaquetteVertices])
  have b4 := hbond x ν (by simp [plaquetteVertices])
  rw [hG] at hmain
  have hs98 : s ≤ 9 / 8 * ℓ.threshold := by
    have hσp := hfit.σ_pos
    rcases hsit with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> linarith
  have hσp := hfit.σ_pos
  linarith
end ColdChartOnSmallTorus
open ColdChartOnSmallTorus in
theorem Slope.coldChartFieldIsColdOnSmallTorus
    (hc : ComplementOfThickenedLumpsRegular) (hframe : FrameCoordOnSmallTorus)
    (hcov : BlocksCoverLowerLevel) : Slope.ColdChartFieldIsColdOnSmallTorus := by
  intro T hT y hy0 R hR n _ hn hside V hV η hη x μ ν hμ
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hx : y ≤ R.coupling := hR.le_coupling
  have hσ0 : 0 < R.params.threshold := by rw [hσ]; exact hT.σ_pos
  have hodd : Odd R.params.side := by rw [hLe]; exact hT.L_odd
  have hn₀ : R.params.n₀ ≤ n := by
    have : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
    omega
  have h4096 : 4096 ≤ T.n₀ := hT.n₀_ge
  have hn2 : 2 ≤ n := by omega
  have hfit : RangesAdmissible R.range R.range := rangesAdmissible_clusterRange T hT y R.coupling hy0 hx
  have hsit : IsStepSituation R.params R.range V Finset.univ ∅ (9 / 8 * R.params.threshold) :=
    Or.inr ⟨hn₀, by rw [hσ]; exact hV, rfl, rfl, rfl⟩
  have hfits : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y hy0
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [hR.params_eq, hR.anchorRadius_eq]
    exact hT.chain
  have h2σ : 2 * R.params.threshold ≤ T.σA := by rw [hσ]; exact hT.σ_le
  have hρ : 0 < R.anchorRadius := by rw [hR.anchorRadius_eq]; exact hT.chain.2.2.2.1
  have hρ1 : R.anchorRadius ≤ 1 := by rw [hR.anchorRadius_eq]; exact hT.chain.2.2.2.2.1
  have hσ1 : R.params.threshold ≤ 1 := by rw [hσ]; exact hT.σ_one
  have hb : ∀ b ∈ StepCosts.chartBonds R.params.side n,
      ‖(YangMills.Construction.StepMarks.frameDeviation R.params R.anchorRadius R.depth (R.range / 2 ^ 11) V ((coldChartSetting R V).field η) b :
        ℍ[ℝ])‖ ≤ R.params.threshold / 64 := by
    intro b hbm
    have hηb : ‖toImaginary (η ⟨b, hbm⟩)‖ ≤ R.ballRadius := hη ⟨b, hbm⟩
    have hfr : ‖(coldChartSetting R V).frame b‖ ≤ R.anchorRadius := norm_bondFrameCoord_le _ _ hρ.le _ _ _
    have hw : ‖(((coldChartSetting R V).frame b + toImaginary (η ⟨b, hbm⟩) : imaginaryQuaternions) : ℍ[ℝ])‖ <
        Real.pi := by
      have h3 : ‖(((coldChartSetting R V).frame b + toImaginary (η ⟨b, hbm⟩) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
          ‖(coldChartSetting R V).frame b‖ + ‖toImaginary (η ⟨b, hbm⟩)‖ := norm_add_le _ _
      have h4 : R.ballRadius = R.params.threshold / 64 := rfl
      have h5 := Real.pi_gt_three
      linarith
    have he := chartCoord_coldField (R := R) hcov hodd hn2 V η ⟨b, hbm⟩ hw
    have heta : YangMills.Construction.StepMarks.frameDeviation R.params R.anchorRadius R.depth (R.range / 2 ^ 11) V ((coldChartSetting R V).field η) b =
        toImaginary (η ⟨b, hbm⟩) := by
      unfold YangMills.Construction.StepMarks.frameDeviation
      rw [he]
      show (coldChartSetting R V).frame b + _ - (coldChartSetting R V).frame b = _
      abel
    rw [heta]
    exact hηb
  have hfinal := curvature_lt_of_frame_eq_minimizer hc R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfits
    hchain h2σ R.depth R.range R.range n V Finset.univ ∅ (9 / 8 * R.params.threshold) hfit hsit
    (fun b => hframe R.params R.anchorRadius R.depth (R.range / 2 ^ 11) n V b (by
      have : R.frameReach = R.range / 2 ^ 11 := rfl
      omega))
    ((coldChartSetting R V).field η) x μ ν hμ
    (fun _ _ => Finset.notMem_empty _) (fun b hbm _ => hb b hbm)
  rw [hσ] at hfinal
  exact hfinal
end YangMills.Construction
end
