import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Towers.FactsOfAbelianFields
import YangMills.Construction.Towers.TheCoefficientAsAResponseToAConstantField
import YangMills.Construction.Towers.TheExpansionOfTheDensityInAFieldOfBoundedAngles
import YangMills.Construction.Towers.TheMassiveFunctionalAndTheFunctionOfTheMassiveJets
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityAtTheLinearField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem linearAbelianAngle_hasBoundedAngles {L : ℕ}
    (hAngles : AbelianFieldFacts.LinearFieldAngles L) :
    HasBoundedAngles
      (FullSpace.linearAbelianAngle : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) := by
  refine ⟨fun b => ?_, fun p => ?_⟩
  · have hn : 0 ≤ TorusMetric.euclidNormVec (b.1.initial : InfiniteLattice.AmbientSpace) :=
      Real.sqrt_nonneg _
    unfold FullSpace.linearAbelianAngle
    split_ifs
    · have := abs_apply_le_euclidNormVec (b.1.initial : InfiniteLattice.AmbientSpace) 0
      linarith
    · simp only [abs_zero]
      linarith
  · have h := hAngles 1 p
    have hone : (fun b => (1 : ℝ) * FullSpace.linearAbelianAngle b) =
        (FullSpace.linearAbelianAngle : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) := by
      funext b
      exact one_mul _
    rw [hone] at h
    rw [h]
    split_ifs <;> norm_num
theorem quadraticResponseToConstantField_holds
    (hExpansion : QuadraticExpansionOfDensity)
    (hValue : SecondDerivativeSumAtLinearAngle)
    (hMassive : FullSpace.BackgroundJets.MassiveFunctionalAndJets.Claim)
    (hFacts : AbelianFieldFacts.AllFacts) :
    QuadraticResponseToConstantField := by
  intro z hz
  obtain ⟨C, hC⟩ := hExpansion z hz
  refine ⟨1 / 4 * min (Real.pi / 2) (z / 48), by positivity, C, fun L hL hs => ?_⟩
  refine ⟨((hMassive L hL hs).1 z hz).2, fun f hf => ?_⟩
  have hb := linearAbelianAngle_hasBoundedAngles
    (hFacts.2.2 L hs z hz).2.2.1
  obtain ⟨hformed, -, hbound⟩ := hC L hs _ hb f (by linarith)
  refine ⟨hformed, ?_⟩
  rw [hValue z hz L hL hs] at hbound
  have hterm : ((1 / 2 * f ^ 2 : ℝ) : ℂ) * (massiveStiffness hL z : ℂ) =
      ((1 / 2 * massiveStiffness hL z * f ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hterm] at hbound
  exact hbound
end YangMills.Construction.Tower.AbelianFieldDensity
end
