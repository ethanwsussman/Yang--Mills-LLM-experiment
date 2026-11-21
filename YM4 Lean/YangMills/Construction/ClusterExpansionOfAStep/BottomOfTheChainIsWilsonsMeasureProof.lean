import YangMills.Construction.ClusterExpansionOfAStep.BottomOfTheChainIsWilsonsMeasure
import YangMills.Construction.ClusterExpansionOfAStep.WilsonsMeasureOnTheFieldsOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
private theorem measurable_wilsonWeight (β : ℝ) (N : ℕ) [NeZero N] :
    Measurable (TorusLumps.wilsonWeight β N) := by
  have hcont : Continuous fun U : TorusFields.TorusField N => TorusFields.wilsonAction Finset.univ U := by
    refine continuous_finsetSum _ fun p _ => ?_
    refine continuous_const.sub (Quaternion.continuous_re.comp (continuous_subtype_val.comp ?_))
    unfold TorusFields.holonomy
    fun_prop
  have hform : TorusLumps.wilsonWeight β N = fun U => Real.exp (-β * TorusFields.wilsonAction Finset.univ U) := by
    funext U
    rw [TorusLumps.wilsonWeight, dif_neg (NeZero.ne N)]
  rw [hform]
  exact (Real.continuous_exp.comp (continuous_const.mul hcont)).measurable
abbrev _root_.YangMills.SharedProofs.p419 := @measurable_wilsonWeight
private theorem wilsonWeight_nonneg (β : ℝ) (N : ℕ) [NeZero N] (U : TorusFields.TorusField N) :
    0 ≤ TorusLumps.wilsonWeight β N U := by
  rw [TorusLumps.wilsonWeight, dif_neg (NeZero.ne N)]
  exact (Real.exp_pos _).le
theorem bottomChainLaw_eq_wilsonGibbs (h : WilsonMeasureOnTorusFields) :
    bottomChainLawIsWilsonGibbsStatement := by
  intro ℓ β x t n m K _ D hs h2 hD
  have F := h ℓ.side m K (WeightedResponses.fineSide ℓ.side t n) hs h2
  have hpart : wilsonPartition β (WeightedResponses.fineSide ℓ.side t n) =
      PeriodicLattice.partitionFunction ℓ.side m K β := (F.partitionFunction_eq β).symm
  refine ⟨hpart, fun G hG => ?_⟩
  obtain ⟨hGm, C, hC⟩ := hG
  have hG' : IsBoundedMeasurable fun U : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side t n) =>
      G (gaugeFieldOfTorusField ℓ.side m (K : ℤ) U) :=
    ⟨hGm.comp F.measurable_gaugeField, C, fun u => hC _⟩
  have hZ : 0 ≤ ∫ U, TorusLumps.wilsonWeight β (WeightedResponses.fineSide ℓ.side t n) U
      ∂(TorusFields.fieldHaar (WeightedResponses.fineSide ℓ.side t n)) := hD.partition_pos.le
  have hf : Measurable fun U : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side t n) =>
      ENNReal.ofReal (TorusLumps.wilsonWeight β (WeightedResponses.fineSide ℓ.side t n) U) :=
    (measurable_wilsonWeight β _).ennreal_ofReal
  have hinv : (ENNReal.ofReal (∫ U, TorusLumps.wilsonWeight β (WeightedResponses.fineSide ℓ.side t n) U
      ∂(TorusFields.fieldHaar (WeightedResponses.fineSide ℓ.side t n))))⁻¹.toReal =
      (wilsonPartition β (WeightedResponses.fineSide ℓ.side t n))⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ]
    rfl
  have hint : ∫ U, (ENNReal.ofReal (TorusLumps.wilsonWeight β (WeightedResponses.fineSide ℓ.side t n) U)).toReal •
        G (gaugeFieldOfTorusField ℓ.side m (K : ℤ) U) ∂(TorusFields.fieldHaar (WeightedResponses.fineSide ℓ.side t n)) =
      ∫ U, G (gaugeFieldOfTorusField ℓ.side m (K : ℤ) U) *
        TorusLumps.wilsonWeight β (WeightedResponses.fineSide ℓ.side t n) U
        ∂(TorusFields.fieldHaar (WeightedResponses.fineSide ℓ.side t n)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    show (ENNReal.ofReal _).toReal • _ = _
    rw [ENNReal.toReal_ofReal (wilsonWeight_nonneg β _ U), smul_eq_mul, mul_comm]
  rw [hD.initial_integral _ hG', F.wilsonGibbsMeasure_eq β, integral_smul_measure,
    integral_map F.measurable_gaugeField.aemeasurable hGm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hf (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), hinv, hint,
    smul_eq_mul, div_eq_inv_mul]
end ClusterExpansionOfAStep
end YangMills.Construction
end
