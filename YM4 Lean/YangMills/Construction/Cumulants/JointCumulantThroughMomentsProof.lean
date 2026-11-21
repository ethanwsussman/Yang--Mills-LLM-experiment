import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.Cumulants.JointCumulantThroughMoments
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants
open YangMills.Construction.SetPartition (PartitionsFin)
theorem finsetMoment_eq_integral {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) {p : ℕ}
    (X : Fin p → Ω → ℝ) {J : Finset (Fin p)} (hJ : J.Nonempty) :
    Cumulants.finsetMoment ν X J = ((∫ ω, ∏ l ∈ J, X l ω ∂ν : ℝ) : ℂ) := by
  rw [Cumulants.finsetMoment, if_neg hJ.ne_empty, Probability.complexExpectation]
  exact integral_complex_ofReal
theorem mixedCumulantMomentExpansion_holds (hRel : Cumulants.CumulantMomentRelations) :
    Cumulants.MixedCumulantMomentExpansion := by
  intro Ω _ ν _ p X hp hX
  rw [(hRel Ω ν p X hX).2.2.2.2.2.2 hp]
  refine Finset.sum_congr rfl fun π _ => ?_
  refine congrArg _ (Finset.prod_congr rfl fun J hJ => ?_)
  exact finsetMoment_eq_integral ν X (π.nonempty_of_mem_parts hJ)
end YangMills.Construction.Cumulants
