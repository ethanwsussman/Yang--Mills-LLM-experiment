import Formulation.WilsonModelProof
import YangMills.Construction.TheStatementsProvedTogether.FromCumulantsOfBoundedVariablesProof
import YangMills.Construction.FamiliesOfLimits.VolumeLimitPointsAreLimitsAlongGrowingToriProof
import YangMills.Construction.Continuum.CentredMomentsOfTheCumulantsAndOfTheirLimitsProof

open Filter MeasureTheory
open scoped Topology
namespace YangMills.Wilson
open Construction

/-- One volume subsequence at this cutoff gives every separated centered moment of
the prescribed infinite-volume Gibbs limit. -/
theorem volume_moments_at_state {L : ℕ} [NeZero L] (hL : Conventions.IsAdmissibleBlockingFactor L)
    (K : ℕ+) {β : ℝ} (hb : 0 < β)
    {ν : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K:ℤ)))}
    (hν : InfiniteLattice.IsInfiniteVolumeLimit L K β ν) :
    ∃ m : ℕ → ℕ+, Tendsto (fun j => physicalSide L (m j)) atTop atTop ∧
      ∀ n (X : TestSpaces.SepTupleOfCard n), Tendsto (fun j => (centeredMoment su2Model L (m j) K β X.1:ℂ))
         atTop (𝓝 (InfiniteLattice.centeredMoment ν X.1)) := by
  obtain ⟨u,hu,ht,hconn⟩ := TheStatementsProvedTogether.torus_states_tendsto_of_tori L hL K β hb ν (Or.inr hν)
  let m (j : ℕ) : ℕ+ := ⟨u j,hu j⟩
  let s : Conventions.StandingParameters := ⟨L,hL,K,1⟩
  have hL2 : 2 ≤ L := by have := hL.2; omega
  refine ⟨m, ht, ?_⟩
  intro n X
  have limit (k : ℕ) (hk : 2 ≤ k) (Y : TestSpaces.SepTupleOfCard k) :=
    hconn k Y.1 hk (fun i => FamiliesOfLimits.GrowingToriProof.isLipschitzFor_of_isC1c
      ⟨(Y.2.1 i).1,(Y.2.1 i).2.1⟩) (fun i => (Y.2.1 i).2.1) (fun _ _ hij => Y.2.2 hij)
  have hh := (TheStatementsProvedTogether.gibbsState_centered_identity s ν hν.1).2.2 n X.1
    (CumulantLimits.CentredMoments.apply_mem_compactTestFunctions
      ((AmbientPoints.mem_separatedTuples_r4_iff (s:=s) X.1).2 X.2))
  rw [hh,CumulantLimits.CentredMoments.ursellPartitionSum_eq_sum]
  let F (j : ℕ) (J : Finset (Fin n)) :=
    SchwingerFunctions.connectedSchwingerR4 L (u j) K β (TestSpaces.sepRestrict X J).1
  have hlim : Tendsto (fun j => ∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts, F j J)
      atTop (𝓝 (∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts,
        InfiniteLattice.smearedEnergyCumulant ν fun k => X.1 (J.orderEmbOfFin rfl k))) := by
    refine tendsto_finsetSum _ fun π hπ => tendsto_finsetProd _ fun J hJ => ?_
    exact limit _ (AmbientPoints.two_le_card_of_mem_singletonFree hπ hJ) (TestSpaces.sepRestrict X J)
  apply hlim.congr
  intro j
  apply Eq.trans _ (centeredMoment_eq (K:=(K:ℕ)) (m:=(m j:ℕ)) β hL2 (m j).pos X).symm
  let D : ConnectedFunctions.CouplingData := ⟨⟨L,hL,K,m j⟩,β,hb⟩
  exact (CumulantLimits.CentredMoments.centredMomentFn_ofRealTuple_eq_sum
    TheStatementsProvedTogether.connected_functions_centred_identity D
    (SchwingerFunctions.periodizeAll L (u j) X.1)).symm

end YangMills.Wilson
