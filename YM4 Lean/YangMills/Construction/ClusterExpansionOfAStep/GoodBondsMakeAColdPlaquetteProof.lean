import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FrameAgainstTheLeastFieldOfTheCut
import YangMills.Construction.ClusterExpansionOfAStep.GoodBondsMakeAColdPlaquette
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StepFrames
open BlockAverages LumpContours ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps StepCosts StepMarks
theorem coldPlaquette_of_small_frameDeviation_holds (hc : ComplementOfThickenedLumpsRegular)
    (hnear : FrameNearMinimizer) : coldPlaquette_of_small_frameDeviation := by
  intro ℓ δ lam ρA σA cg N hfit hch hσ t r r' n _ V S C s hr hsit hgap W x μ ν hlt hoff hgood
  have hnr := (hnear ℓ δ lam ρA σA cg N hfit hch hσ).2 t r r' n V S C s hr hsit
  obtain ⟨δpos, _, _, _, ρle, _, _, Npos, hbody⟩ := hch
  have hπ : ρA < Real.pi := lt_of_le_of_lt ρle (by linarith [Real.pi_gt_three])
  obtain ⟨spos, sle, n4096, hF⟩ := stepSituation_regular_and_cold hc hfit hsit
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
  have one := (hbody (torusFrame ℓ.side t n) 2047 (cellsOfSites (torusFrame ℓ.side t n) S) rfl hamb (by norm_num) hreg s
    (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) spos (sle.trans hσ) hcold).1
  obtain ⟨w, hw, hcw, hlc⟩ := minimizingCoordinates_eq (ρ := ρA) hfit.L_odd hs2 hπ le_rfl one
  have hp₀ : ∀ i, (stepBlockFrame ℓ.side n).period 0 i = n * ℓ.side :=
    fun i => period_depth_of_extent (F := stepBlockFrame ℓ.side n) hn₀ i
  have hpF : ∀ i, (torusFrame ℓ.side t n).period (torusFrame ℓ.side t n).depth i = n * ℓ.side :=
    fun i => period_depth_of_extent (F := torusFrame ℓ.side t n) hn i
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
        readAtLevel_torusSiteInFrame hp₀ W z i]
      have hun : (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z +
            BlockAverages.unitStep (stepBlockFrame ℓ.side n).depth i : (stepBlockFrame ℓ.side n).Site 0) =
          torusSiteInFrame (stepBlockFrame ℓ.side n) 0 (z + TorusFields.unitStep (n * ℓ.side) i) := by
        apply toTorusSite_injective hp₀
        rw [toTorusSite_torusSiteInFrame hp₀]
        exact (toTorusSite_add hp₀ _ _).trans
          (congrArg₂ (· + ·) (toTorusSite_torusSiteInFrame hp₀ z) (toTorusSite_unitStep hp₀ i))
      exact congrArg (fun q : (stepBlockFrame ℓ.side n).Site 0 =>
        axialGauge 1 Wr (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z) * W z i * (axialGauge 1 Wr q)⁻¹) hun
    rw [e, curvature_gaugeTransform]
  have hmemS : ∀ z ∈ plaquetteVertices x μ ν, parentBlock ℓ.side z ∈ S := by
    intro z hz
    have h0 := (stepSituation_box_of_not_mem hfit hr hsit (hoff z hz)).1 0 fun i => by
      simp only [Pi.zero_apply, abs_zero]
      positivity
    have e0 : (siteOfInt 0 : TorusSite n) = 0 := by
      funext i
      simp [siteOfInt]
    rwa [e0, add_zero] at h0
  have hWs : curvature Ws x μ ν < s / 8 := by
    have hread : chartedField w VF =
        readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth Ws := by
      funext c i
      change _ = chartedField w VF
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth (toTorusSite _ c)) i
      rw [torusSiteInFrame_toTorusSite hpF]
    have hsite : ∀ z ∈ plaquetteVertices x μ ν,
        torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z ∈
        sitesOfCells (cellsOfSites (torusFrame ℓ.side t n) S) (torusFrame ℓ.side t n).depth :=
      fun z hz => torusSiteInFrame_mem_sitesOfCells (F := torusFrame ℓ.side t n) hn hodd h2 z (hmemS z hz)
    have hup : ∀ (z : TorusSite (n * ℓ.side)) (i : Fin 4),
        torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
            (z + TorusFields.unitStep (n * ℓ.side) i) =
          torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z +
            BlockAverages.unitStep (torusFrame ℓ.side t n).depth i := by
      intro z i
      apply toTorusSite_injective hpF
      rw [toTorusSite_torusSiteInFrame hpF, toTorusSite_add hpF, toTorusSite_torusSiteInFrame hpF,
        toTorusSite_unitStep hpF]
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
    rw [hread, TopLevelSites.plaquetteDefect_readAtLevel_eq hpF, toTorusSite_torusSiteInFrame hpF] at h1
    exact h1
  have hbond : ∀ (z : TorusSite (n * ℓ.side)) (i : Fin 4), z ∈ plaquetteVertices x μ ν →
      ‖(G z i : ℍ[ℝ]) - Ws z i‖ ≤ ℓ.threshold / 64 + ℓ.threshold / 128 := by
    intro z i hz
    have hσpos := hfit.σ_pos
    have e1 : G z i = chartedField (fun x i => bondCoordinate 1 V₀ Wr (x, i)) V₀
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z) i :=
      axialGauge_eq_chartedField hodd₀ hs₀ V₀ Wr _ i
    have hcr : IsCrossingBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z, i) ↔
        IsCrossingBond (F := torusFrame ℓ.side t n)
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z, i) :=
      (isCrossingBond_torusSiteInFrame_iff (F := stepBlockFrame ℓ.side n) hn₀ hodd₀ h2 z i).trans
        (isCrossingBond_torusSiteInFrame_iff (F := torusFrame ℓ.side t n) hn hodd h2 z i).symm
    have htr : IsAxialTreeBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z, i) ↔
        IsAxialTreeBond (F := torusFrame ℓ.side t n)
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z, i) :=
      (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame ℓ.side n) hn₀ hodd₀ h2 z i).trans
        (isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame ℓ.side t n) hn hodd h2 z i).symm
    have hVV : V₀ (enclosingCell (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z)) i =
        VF (enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z)) i := by
      have c0 : enclosingCell (torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth z) =
          torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top (parentBlock ℓ.side z) :=
        enclosingCell_torusSiteInFrame hn₀ z
      have c1 : enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z) =
          torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side z) :=
        enclosingCell_torusSiteInFrame hn z
      have r0 := readAtLevel_torusSiteInFrame (period_top_of_extent (F := stepBlockFrame ℓ.side n) hn₀) V
        (parentBlock ℓ.side z) i
      have r1 := readAtLevel_torusSiteInFrame (period_top_of_extent (F := torusFrame ℓ.side t n) hn) V
        (parentBlock ℓ.side z) i
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
    · have hb : (z, i) ∈ chartBonds ℓ.side n := by
        classical
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
      have hy : parentBlock ℓ.side z ∉ C := hoff z hz
      have hgm := hgood (z, i) hb ⟨z, hz, rfl⟩
      have hnz := (hnr (z, i) hb hy).2
      have hle : minimizerCoord ℓ.coupling ρA ℓ.side t S V (z, i) =
          w (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z) i := by
        unfold minimizerCoord minimizingBondCoordinate
        simp only
        rw [hlc]
      rw [hle] at hnz
      set c₁ : imaginaryQuaternions := bondCoordinate 1 V₀ Wr (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 z, i)
        with hc₁
      set c₂ : imaginaryQuaternions := w (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth z) i
        with hc₂
      have hdist : ‖(c₁ : ℍ[ℝ]) - (c₂ : ℍ[ℝ])‖ ≤ ℓ.threshold / 64 + ℓ.threshold / 128 := by
        have e : (c₁ : ℍ[ℝ]) - (c₂ : ℍ[ℝ]) =
            ((frameDeviation ℓ ρA t (r / 2 ^ 11) V W (z, i) : imaginaryQuaternions) : ℍ[ℝ]) +
            (((frameCoord ℓ ρA t (r / 2 ^ 11) V (z, i) : imaginaryQuaternions) : ℍ[ℝ]) - (c₂ : ℍ[ℝ])) := by
          have e' : ((frameDeviation ℓ ρA t (r / 2 ^ 11) V W (z, i) : imaginaryQuaternions) : ℍ[ℝ]) =
              (c₁ : ℍ[ℝ]) - ((frameCoord ℓ ρA t (r / 2 ^ 11) V (z, i) : imaginaryQuaternions) : ℍ[ℝ]) := rfl
          rw [e']
          abel
        rw [e]
        refine (norm_add_le _ _).trans ?_
        linarith
      have hexp := norm_expUnit_sub_le c₁ c₂
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
        have := norm_mul_sub_mul_le (expUnit c₁) (expUnit c₂)
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
  have hmain := curvature_le_add G Ws x μ ν
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
end YangMills.Construction.StepFrames
end
