import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmallProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheLimitsOfTheDensitiesAreSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.StepDensities
open BlockAverages ColdStepAtMirrorFrames ScaledVariables ReferenceDensity MeasureTheory Set
variable {F : BlockFrame}
private theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hF : ∀ i, F.extent i ≠ 0) (s : ℝ)
    (V : F.GaugeField F.top) (hV : IsSmallCurvature s V) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := by apply _root_.YangMills.SharedProofs.p8866 <;> assumption
theorem limitDensitiesSmoothStatement_proof (hS : rescaledPartsSmoothStatement)
    (hW : meansDifferentiableInWeightStatement) (hZ : DensitiesAtScaleZero)
    (hR : localReferenceBoundedFamily) : limitDensitiesSmoothStatement := by
  refine EventuallyOrdered.mono (((hS.and hW).and hZ).and hR) ?_
  rintro T hT hn ⟨⟨⟨cS, cW⟩, cZ⟩, cR⟩ hroom t F Y V hF hV
  obtain ⟨e, he⟩ := cR hroom
  obtain ⟨l₂, K, hl₂, hK, gS⟩ := cS e
  obtain ⟨l₃, hl₃, gW⟩ := cW e
  have hl₀ : 0 < min l₂ l₃ := lt_min hl₂ hl₃
  have hext : ∀ i, F.extent i ≠ 0 := by
    obtain ⟨_, _, n, hn', hn₀⟩ := hF
    intro i
    rw [hn' i]
    omega
  set f : LocalFamily := T.localReference t with hf
  have hs₁ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (min l₂ l₃) K Y
      (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) :=
    fun V' hV' => (gS (min l₂ l₃) hl₀ (min_le_left _ _) t f F V' Y (he t) hF hV').1
  have hs₂ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (min l₂ l₃) K Y
      (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) :=
    fun V' hV' => (gS (min l₂ l₃) hl₀ (min_le_left _ _) t f F V' Y (he t) hF hV').2
  have hX₀ : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun l => l.elim0
  obtain ⟨-, v₁⟩ := (gW (min l₂ l₃) hl₀ (min_le_right _ _) t f F V Y StepLaw.interpolated K _ 0 Fin.elim0
    Fin.elim0 (he t) hF hV (Or.inr rfl) hK hs₁ hX₀).1 (by norm_num)
  obtain ⟨-, v₂⟩ := (gW (min l₂ l₃) hl₀ (min_le_right _ _) t f F V Y StepLaw.tilted K _ 0 Fin.elim0
    Fin.elim0 (he t) hF hV (Or.inl rfl) hK hs₂ hX₀).1 (by norm_num)
  constructor
  · intro k c X
    refine ContDiffAt.congr_of_eventuallyEq (v₁.contDiff k c X).neg ?_
    filter_upwards [eventually_isSmallCurvature_leftTranslate hext _ V hV c X] with τ hτ
    exact ((cZ t f F _ Y hF hτ).1).symm
  · intro k c X
    refine ContDiffAt.congr_of_eventuallyEq (v₂.contDiff k c X) ?_
    filter_upwards [eventually_isSmallCurvature_leftTranslate hext _ V hV c X] with τ hτ
    exact ((cZ t f F _ Y hF hτ).2).symm
end YangMills.Construction.StepDensities
end
