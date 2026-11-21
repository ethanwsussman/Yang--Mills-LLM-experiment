import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtTheLeastFieldOfTheChain
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionOfTheCurvedChain
import YangMills.Construction.ColdStepAtMirrorFrames.LinearFieldIsCold
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields
namespace ColdStepAtMirrorFrames
private theorem stepCoordinates_zero {F : BlockFrame} {S : Finset F.Cell} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by apply _root_.YangMills.SharedProofs.p7539 <;> assumption
theorem expansionAtMinimizingChainField_holds (hminAction : ConstantCurvatureMinimalAction)
    (habel : ConstantCurvatureChainAbelian) (hsmall : LinearFieldCurvatureBound)
    (hcover : BlocksCoverLowerLevel) : ExpansionAtMinimizingChainField := by
  classical
  intro a L c σ δ E E₃ t n₀ m f ha hodd hc hσ hrow
  obtain ⟨γ₀, hγ₀, hleast⟩ := hminAction a L c ha hodd hc
  have hσA : 0 < c.σA := hc.positivity.2.2.2.1
  set s : ℝ := min c.σA σ with hs
  have hspos : 0 < s := lt_min hσA hσ
  refine ⟨min γ₀ (min (s / 2) 1), lt_min hγ₀ (lt_min (by positivity) one_pos), ?_⟩
  intro X μ ν n l hsize hn₀ hX hμν hl
  set F := torusFrame L t n with hF
  intro y
  have hoddF : Odd F.blockSide := hodd
  have hn : ∀ i, F.extent i = n := fun _ => rfl
  have hn0 : 0 < n := by omega
  have hl1 : 2 * Real.pi * l / (n : ℝ) ^ 2 ≤ 1 := hl.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hchain := hleast F X μ ν n l rfl hn hsize hX hμν (hl.trans (min_le_left _ _))
  have hmin := (hchain.1 F.depth (by simp [BlockFrame.top])).1
  have hab := (habel F X μ ν n l hoddF hn hn0 hX hμν hl1 F.top le_rfl).1
  set V := constantCurvatureChain F X μ ν l F.top with hV
  have hflux : levelFlux F μ l F.top = 2 * Real.pi * l / (n : ℝ) ^ 2 := by
    unfold levelFlux BlockFrame.period
    simp [hn]
  have hsmallV : IsSmallCurvature s V := by
    intro p hp
    have h1 := (hsmall F F.top V X _ μ ν hX hμν hab).2 p hp
    rw [hflux, abs_of_nonneg (by positivity)] at h1
    have h2 : 2 * Real.pi * l / (n : ℝ) ^ 2 ≤ s / 2 := hl.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  obtain ⟨w, hw, hcw, huniq⟩ :=
    (hc.estimates F s V ⟨rfl, n, hsize, hn⟩ hspos (min_le_left _ _) hsmallV).minimizer
  have hsite : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth :=
    fun x => hcover F hoddF (fun i => by rw [hn]; exact hn0) x
  have hbond : ∀ b : F.Site F.depth × Fin 4, b ∈ innerBonds (finiteCells F) F.depth := by
    intro b
    unfold innerBonds
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hsite _, Finset.mem_univ _⟩, hsite _⟩
  have hplaq : ∀ p : F.Site F.depth × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      p ∈ innerPlaquettes (finiteCells F) F.depth := by
    intro p hp
    unfold innerPlaquettes
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    exact ⟨⟨hsite _, Finset.mem_univ _, Finset.mem_univ _⟩, hp, fun x _ => hsite x⟩
  have hlow : IsCubicTorusAbove L t n₀ F := ⟨rfl, rfl, n, hn, hn₀⟩
  have hsmallσ : IsSmallCurvature σ (chartedField w V) := by
    intro p hp
    have h1 := hcw p (hplaq p hp)
    have h2 : s ≤ σ := min_le_right _ _
    linarith
  have hlc : IsMinimizingChart a (finiteCells F) V c.ρA (minimizingCoordinates a (finiteCells F) V c.ρA) := by
    have hex : ∃ w', IsMinimizingChart a (finiteCells F) V c.ρA w' :=
      ⟨w, hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact hex.choose_spec
  have hstep : fieldAboveFrame true a c.ρA m V (0 : StepVariable (finiteCells F)) =
      chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V := by
    unfold fieldAboveFrame
    congr 1
    funext x i
    unfold coordsAboveFrame
    rw [stepCoordinates_zero, add_zero]
    rfl
  obtain ⟨γ₁, _, hs₁⟩ := huniq _ hlc.2.2
  obtain ⟨γ₂, _, hs₂⟩ := huniq _ hmin
  have e₁ : chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V =
      gaugeTransform γ₁ (chartedField w V) := by
    funext x i
    exact hs₁ (x, i) (hbond _)
  have e₂ : constantCurvatureChain F X μ ν l F.depth = gaugeTransform γ₂ (chartedField w V) := by
    funext x i
    exact hs₂ (x, i) (hbond _)
  unfold centredExpansion subtractTrivial
  rw [hstep, e₁, e₂, hrow.gauge_invariant F hlow y _ γ₁ hsmallσ, hrow.gauge_invariant F hlow y _ γ₂ hsmallσ]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
