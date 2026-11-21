import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusIsFaithful
import YangMills.Construction.InfiniteLattice.WilsonMeasureOfAPeriodLatticeAndItsExtensionAreStates
import YangMills.Construction.InfiniteLattice.WilsonMeasuresOfATorusAreProbabilities
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LiftedGibbsStates
variable {a : ℝ}
instance : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  haveI : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
theorem continuous_pullbackField (g : LatticeSymmetry a) : Continuous g.pullbackField := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetry.continuous_pullbackField <;> assumption
theorem isBoundedObservable_actOn (g : LatticeSymmetry a) {A : GaugeField a → ℂ}
    (hA : IsBoundedObservable A) : IsBoundedObservable (g.actOn A) := by
  obtain ⟨hm, C, hC⟩ := hA
  exact ⟨hm.comp (continuous_pullbackField g).measurable, C, fun U => hC _⟩
theorem periodicGibbsMeasuresAreStates_holds (h₁ : QuotientGibbsMeasuresProbability.Statement)
    (h₂ : PeriodicLiftIsFaithful) : PeriodicGibbsMeasuresAreStates := by
  intro a β ha hβ Γ
  have hW := h₁ β hβ a ha Γ
  have hE := h₂ a ha Γ
  have hm : Measurable Γ.lift := hE.isEmbedding_lift.continuous.measurable
  have hi : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      ∫ U, F U ∂Γ.liftedGibbsMeasure β = ∫ U, Γ.periodize F U ∂Γ.gibbsMeasure β := fun F hF => by
    rw [PeriodSublattice.liftedGibbsMeasure,
      integral_map hm.aemeasurable hF.1.aestronglyMeasurable]
    rfl
  refine ⟨(Real.exp_pos _).trans_le hW.exp_le_partitionFunction, hW.partitionFunction_le_one,
    hW.isProbabilityMeasure_gibbs, hW.isProbabilityMeasure_lifted, hi, fun γ hγ A hA => ?_⟩
  rw [hi _ (isBoundedObservable_actOn _ hA), hi A hA]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  have hU : Γ.lift U ∈ Γ.invariantFields :=
    hE.range_lift ▸ Set.mem_range_self U
  change A ((shift γ).pullbackField (Γ.lift U)) = A (Γ.lift U)
  rw [hU γ hγ]
end YangMills.Construction.InfiniteLattice.LiftedGibbsStates
