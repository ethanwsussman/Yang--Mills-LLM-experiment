import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.Cumulants.GeneratingFunctionOfATupleAndItsLogarithm
import YangMills.Construction.Lattice.IsometryInvarianceOfWilsonMeasure
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.WilsonCumulantWellPosedness
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice.WilsonCumulantWellPosedness
theorem integrable_cexp_sum_mul (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (n : ℕ) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Probability.IsBoundedRealRV (X i)) (t : Fin n → ℂ) :
    Integrable (fun ω => Complex.exp (∑ i, t i * (X i ω : ℂ))) ν := by
  choose C hC using fun i => (hX i).bounded
  have hm : Measurable fun ω => Complex.exp (∑ i, t i * (X i ω : ℂ)) := by
    refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ => ?_)
    exact measurable_const.mul (Complex.measurable_ofReal.comp (hX i).measurable)
  refine Integrable.of_bound hm.aestronglyMeasurable (Real.exp (∑ i, ‖t i‖ * C i)) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (t i * (X i ω : ℂ)).re ≤ ‖t i * (X i ω : ℂ)‖ := Complex.re_le_norm _
    _ = ‖t i‖ * |X i ω| := by simp
    _ ≤ ‖t i‖ * C i := mul_le_mul_of_nonneg_left (hC i ω) (norm_nonneg _)
theorem statement_holds (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hI : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (hG : RandomTuple.TupleLaplaceLog.LaplaceAndLogTheorem) : statement := by
  refine ⟨fun L m K β hL hm hK => ?_, fun L m K hL hm hK σ hσ l => ?_,
    fun Ω _ ν _ n X hn hX => ?_⟩
  · obtain ⟨-, -, -, hint, hZ, -, -, hprob, -⟩ := hW L m K β hL hm hK
    refine ⟨fun U => ?_, hint, hZ, hprob⟩
    have : Finite (PeriodicLattice.Site L m (K : ℤ)) :=
      SeparatedSequences.BaseParameters.site_finite (by omega) m (K : ℤ)
    have := PeriodicLattice.ConjugationReality.finite_plaquette L m (K : ℤ)
    exact Set.toFinite _
  · obtain ⟨-, -, h⟩ := hI L m K 0 hL hm hK
    exact ⟨PeriodicLattice.bondPreimage σ l, (h σ hσ).1 l⟩
  · obtain ⟨h1, h2, -⟩ := hG Ω ν n X hn hX
    exact ⟨integrable_cexp_sum_mul Ω ν n X hX, h1.value_at_zero, h2.formed⟩
end YangMills.Construction.PeriodicLattice.WilsonCumulantWellPosedness
