import YangMills.Construction.Continuum.ConnectedFunctionsAndCentredFunctionalOfAFunctional
import YangMills.Construction.Cumulants.JointCumulantThroughMoments
import YangMills.Construction.Cumulants.MultilinearityShiftsAndMomentsOfJointCumulants
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.MomentsAndObservablesAreFormed
import YangMills.Construction.TotalDensitiesGiveASystem.AConnectedFunctionReadsTheCentredMeans
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem.CentredMeansConnected
open InfiniteLattice (GaugeField IsBoundedBorelCompactlySupported AmbientSpace smearedEnergyCumulant
  smearedEnergy)
open TestSpaces (SepTupleOfCard sepRestrict)
open SetPartition (PartitionsFin blockCount)
open Probability (IsBoundedRealRV)
private theorem prod_orderEmbOfFin {M : Type*} [CommMonoid M] {n : ℕ} (J : Finset (Fin n))
    (g : Fin n → M) : ∏ l : Fin J.card, g (J.orderEmbOfFin rfl l) = ∏ i ∈ J, g i := by
  rw [← Finset.prod_coe_sort J g]
  exact Fintype.prod_equiv (J.orderIsoOfFin rfl).toEquiv _ _ fun l => by simp
private theorem isBoundedBorelCompactlySupported_of_mem {f : AmbientSpace → ℝ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    IsBoundedBorelCompactlySupported f := by
  obtain ⟨h₁, h₂, -⟩ := hf
  exact ⟨h₁.continuous.measurable, h₂.exists_bound_of_continuous h₁.continuous, h₂⟩
private def subBlock {n : ℕ} (X : SepTupleOfCard n) (J : Finset (Fin n)) : SeparatedTuples.SepTuple :=
  TupleLists.toList ⟨J.card, sepRestrict X J⟩
private def signedPartitionSum {n : ℕ} (v : Finset (Fin n) → ℝ) : ℝ :=
  ∑ π : PartitionsFin n, (-1 : ℝ) ^ (blockCount π - 1) *
    ((blockCount π - 1).factorial : ℝ) * ∏ B ∈ π.parts, v B
private theorem centeredRep_subBlock (L K : ℕ)
    (ν : Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) {n : ℕ} (X : SepTupleOfCard n)
    (J : Finset (Fin n)) (U : GaugeField (PeriodicLattice.meshSize L (K : ℤ))) :
    CenteredRepresentatives.centeredRep L K ν (subBlock X J) U =
      ∏ i ∈ J, (smearedEnergy (X.1 i) U + -∫ V, smearedEnergy (X.1 i) V ∂ν) := by
  rw [← prod_orderEmbOfFin J]
  simp [CenteredRepresentatives.centeredRep, subBlock, TupleLists.toList, List.map_ofFn,
    sepRestrict, SchwingerFunctions.restrictTuple, List.prod_ofFn, sub_eq_add_neg]
theorem connectedOfCentredMeans_holds (hT : Cumulants.MixedCumulantMomentExpansion)
    (hS : Cumulants.MomentCumulantRelations.Holds)
    (hM : PeriodicGibbsLimits.ObservablesAndMomentsDefined.Statement) :
    connectedOfCentredMeansStatement := by
  intro n hn X
  let e : Finset (Fin n) ≃ Fin (Fintype.card (Finset (Fin n))) := Fintype.equivFin _
  refine ⟨_, fun i => subBlock X (e.symm i), fun v => signedPartitionSum fun B => v (e B), ?_, ?_, ?_⟩
  · unfold signedPartitionSum
    fun_prop
  · intro σ
    simp only [signedPartitionSum, Equiv.symm_apply_apply]
    simp only [LimitTheorem.connectedFn, TestSpaces.cumulant_eq_sum_partitions,
      LimitTheorem.evalOnMap, subBlock]
  · intro L K hL ν ρ hρ
    have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) :=
      zpow_pos (Nat.cast_pos.mpr (by have := hL.2; omega)) _
    have hb : ∀ i, IsBoundedRealRV
        (fun U : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) => smearedEnergy (X.1 i) U) :=
      fun i => ((hM.1 _ ha).1 (X.1 i) (isBoundedBorelCompactlySupported_of_mem (X.2.1 i))).2
    have hc : ∀ i, IsBoundedRealRV
        (fun U : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
          smearedEnergy (X.1 i) U + -∫ V, smearedEnergy (X.1 i) V ∂ν) := fun i => by
      obtain ⟨hm, C, hC⟩ := hb i
      refine ⟨hm.add_const _, C + |∫ V, smearedEnergy (X.1 i) V ∂ν|, fun U => ?_⟩
      exact (abs_add_le _ _).trans (add_le_add (hC U) (abs_neg _).le)
    have hshift := (hS _ ρ).2.2.1 n (fun i U => smearedEnergy (X.1 i) U)
      (fun i => -∫ V, smearedEnergy (X.1 i) V ∂ν) hn hb
    rw [smearedEnergyCumulant, ← hshift, hT _ ρ n _ (by omega) hc]
    beta_reduce
    rw [signedPartitionSum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    push_cast
    refine congrArg _ (Finset.prod_congr rfl fun J _ => ?_)
    simp only [Equiv.symm_apply_apply, centeredRep_subBlock]
end YangMills.Construction.TotalDensitiesGiveASystem.CentredMeansConnected
end
