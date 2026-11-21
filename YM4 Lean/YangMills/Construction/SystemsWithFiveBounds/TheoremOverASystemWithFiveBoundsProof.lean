import YangMills.Construction.FamiliesOfLimits.VolumeLimitPointsAreLimitsAlongGrowingTori
import YangMills.Construction.InfiniteLattice.LimitPointsOfTheTorusMeasuresArePeriodicGibbsStates
import YangMills.Construction.SystemsWithFiveBounds.ConditionsOfALimitAtConstantsForm
import YangMills.Construction.SystemsWithFiveBounds.LimitsAlongThePairs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open BoundsOnEverySide (SideFamily)
open TestSpaces (SepTupleOfCard)
open SeparatedTuples
namespace MainTheorem
def limitConstantsOf (K : LimitTheorem.ExistentialConstants) : LimitConstants where
  localBound := K.perBall
  globalPrefactor := K.A
  globalBase := K.B
  globalExp := K.κStar
  schwartzOrder := K.kE
  schwartzPrefactor := K.cE
  schwartzBase := K.CE
  schwartzExp := K.κ
  clusterConst := K.clusterConst
  clusterRadius := K.clusterRadius
theorem limitConstantsOf_admissible {K : LimitTheorem.ExistentialConstants}
    (hK : K.SideConditions) : (limitConstantsOf K).Valid :=
  ⟨hK.κStar_nonneg, hK.perBall_antitoneOn, hK.perBall_pos, hK.A_pos, hK.B_pos, hK.kE_pos, hK.cE_pos,
    hK.CE_pos, hK.κ_pos, hK.clusterConst_pos, hK.clusterRadius_pos⟩
section Translation
variable {M ϑ : ℝ} {K : LimitTheorem.ExistentialConstants} {E : LimitTheorem.LawConstants}
  {sigma : TupleFunctional}
theorem localCumulantBounds_of_perBallBoundsAt (h : PerBallBoundsAt M (K.toConditionConstants E) sigma) :
    LocalCumulantBounds M (limitConstantsOf K) sigma := h
theorem schwingerGrowth_of_growthBound (h : LimitTheorem.GrowthBound (K.toConditionConstants E) sigma) :
    SchwingerGrowth (limitConstantsOf K) sigma := h
theorem twoPointLawHolds_of_at (h : TwoPointLawHoldsAt ϑ (K.toConditionConstants E) sigma) :
    TwoPointLawHolds ϑ E.d₀ E.ηBar sigma := h
theorem reconstructionConditions_of (h : LimitTheorem.ReconstructionProperties sigma) :
    ReconstructionConditions sigma := by
  obtain ⟨a, b, hab, r, s, c, k, U, hU⟩ := h
  exact ⟨a, b, hab, r, s, c, k, U, ⟨hU.acts, hU.isUnitary, hU.fixes_vacuum, hU.comm_hamiltonian⟩⟩
theorem latticeSymmetries_of {S : LimitTheorem.CumulantFamily} (h : LimitTheorem.LatticeSymmetries S) :
    LatticeSymmetries S :=
  ⟨h.shift_invariant, h.hyperoctahedral_invariant, h.perm_symmetric, h.centred_motion_invariant,
    h.centred_perm_invariant⟩
theorem componentOS_of (h : LimitTheorem.ComponentOSAt K sigma) :
    ∀ T, HasSchwingerSequence sigma T → OSAxioms (limitConstantsOf K) T := fun T hT => by
  obtain ⟨⟨g, i, rp, sy, cl, re⟩, -⟩ := h.1 T hT
  exact ⟨g, i, rp, sy, cl, re⟩
theorem permutesComponents_rotationMap {A : DecompositionData}
    (h₁ : LimitTheorem.LatticeSymmetriesPermute A)
    (h₂ : LimitTheorem.NonLatticeRotationsPermute A) (R : Orthogonal.orthogonalGroupFour) :
    PermutesComponents A (rotationMap R) := by
  by_cases hR : LimitTheorem.IsHyperoctahedral R
  · obtain ⟨w, hw⟩ := hR
    have e : rotationMap R = w.1 := by
      funext x
      have := hw x
      simpa [rotationMap, LimitTheorem.ofOrthogonal, Motions.RigidMotion.toFun] using this
    rw [e]
    exact h₁.2 w
  · exact h₂ R hR
theorem decompositionProperties_of (h₁ : LimitTheorem.DecompositionProperties sigma)
    (h₂ : ∀ A : DecompositionData, A.IsCanonical sigma →
      LimitTheorem.NonLatticeRotationsPermute A) :
    DecompositionProperties sigma :=
  ⟨h₁.exists_canonical, h₁.canonical_isomorphic, h₁.groundStates, h₁.transported,
    fun A hA v => (h₁.latticePermute A hA).1 v, fun A hA w => (h₁.latticePermute A hA).2 w,
    fun A hA R => permutesComponents_rotationMap (h₁.latticePermute A hA) (h₂ A hA) R⟩
theorem componentSymmetries_of (h₁ : LimitTheorem.ComponentSymmetries sigma)
    (h₂ : LimitTheorem.IsO4InvariantFunctional sigma) : ComponentSymmetries sigma :=
  ⟨h₁.shift_invariant, h₁.hyperoctahedral_invariant, h₂, h₁.axialPositive, h₁.diagonalPositive,
    h₁.permInvariant, h₁.regular⟩
theorem componentReconstruction_of (h₁ : LimitTheorem.ComponentReconstruction sigma)
    (h₂ : LimitTheorem.JointSpectrumInForwardCone sigma)
    (h₃ : LimitTheorem.HasSpatialRotationRep sigma) : ComponentReconstruction sigma :=
  ⟨reconstructionConditions_of h₁.reconstruction, h₁.kernel_eq, h₁.hamiltonianBounds, h₂, h₃⟩
end Translation
section OverASystem
variable (Y : FiveBoundSystem) {g : ℝ} (hg : g ∈ Ioc 0 Y.top)
def approximatingSequenceOfPairs (hP : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs)
    (Q : PairSequence Y.L (Y.IsPair g)) : ApproximatingSequence (FiveBoundSystem.statedSideFamily Y g hg) where
  cutoff := Q.cutoff
  tendsto_cutoff := Q.tendsto_cutoff
  coupling := Q.coupling
  isDatum := Q.pair
  state := Q.state
  isLimit := Q.isLimit
  mem_gibbs k := (hP Y.L (Q.cutoff k) Y.admissibleL (Q.cutoff k).pos (Q.coupling k)
    (Y.β_pos g hg _ _ (Q.pair k))).2 (Q.isLimit k)
variable {Y}
include hg
theorem periodicShiftInvariant_of (hP : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs)
    (Q : PairSequence Y.L (Y.IsPair g)) : Q.PeriodicInvariantStates := fun k => by
  have h := hP Y.L (Q.cutoff k) Y.admissibleL (Q.cutoff k).pos (Q.coupling k)
    (Y.β_pos g hg _ _ (Q.pair k))
  exact ⟨h.2 (Q.isLimit k), (h.1 _ (Q.isLimit k)).2.1⟩
theorem isTorusLimit_of (hT : FamiliesOfLimits.InfiniteVolumeLimitsAlongGrowingTori)
    {Q : PairSequence Y.L (Y.IsPair g)} {S : LimitTheorem.CumulantFamily} (hQ : Q.Defines S) :
    Q.LimitOfGrowingTori S := by
  obtain ⟨m, -, hm₂, hm₃⟩ := hT Y.L Y.admissibleL univ 0 (fun _ _ _ => mem_univ _) Q.cutoff Q.coupling
    Q.state (fun k => Y.β_pos g hg _ _ (Q.pair k)) Q.isLimit
  refine ⟨m, hm₂, fun n hn X => ⟨(hm₃ n hn X).1, ?_⟩⟩
  simpa using (hm₃ n hn X).2.add (hQ n hn X)
theorem conclusion_of (hP : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs)
    (hT : FamiliesOfLimits.InfiniteVolumeLimitsAlongGrowingTori)
    {K : LimitTheorem.ExistentialConstants} {E : LimitTheorem.LawConstants}
    {Q : PairSequence Y.L (Y.IsPair g)} {S : LimitTheorem.CumulantFamily} (hQ : Q.Defines S)
    (c : BaseLimitConditions Y.M K E S)
    (l : LimitLawConditions Y.ϑ (K.toConditionConstants E) S)
    (r : LimitTheorem.RotationAssertionsAt K S) :
    ErgodicDecompositionConclusion Y.M Y.ϑ E.d₀ E.ηBar (limitConstantsOf K) Q S where
  limit :=
    { states := periodicShiftInvariant_of hg hP Q
      tori := isTorusLimit_of hg hT hQ
      symmetries := latticeSymmetries_of c.symmetries
      axialPositive := c.axialPositive
      distributions := c.distributions
      conditions :=
        { localBounds := localCumulantBounds_of_perBallBoundsAt c.perBall
          growth := schwingerGrowth_of_growthBound c.growth
          reconstruction := reconstructionConditions_of c.reconstruction
          twoPointLaw := twoPointLawHolds_of_at l.law
          cumulants_eq := c.cumulants_eq
          twoPoint_pos := l.twoPoint_pos
          two_le_rank := l.two_le_rank }
      diagonalPositive := c.diagonalPositive
      energyBound := c.hamiltonian_ge
      rotationInv := r.o4Invariant }
  decomposition := decompositionProperties_of c.decomposition r.permute
  onePoint := c.componentOnePoint
  components A hA ξ :=
    { symmetries := componentSymmetries_of (c.componentSymmetries A hA ξ) (r.componentsO4 A hA ξ)
      localBounds := localCumulantBounds_of_perBallBoundsAt (c.componentPerBall A hA ξ)
      growth := schwingerGrowth_of_growthBound (c.componentGrowth A hA ξ)
      twoPointLaw := twoPointLawHolds_of_at (l.componentLaw A hA ξ)
      reconstruction := componentReconstruction_of (c.componentReconstruction A hA ξ)
        (r.jointSpectrum A hA ξ) (r.spatialRotations A hA ξ)
      clustering := c.componentClustering A hA ξ
      componentOS := componentOS_of (r.componentOS A hA ξ)
      fieldData := (r.componentOS A hA ξ).2 }
end OverASystem
theorem mainTheorem (hC : LimitConditionsExist) (hL : SubsequentialLimitsAlongPairs)
    (hP : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs)
    (hT : FamiliesOfLimits.InfiniteVolumeLimitsAlongGrowingTori) : Statement := by
  intro Y
  have hK : ∀ g : ℝ, ∃ K : LimitConstants, g ∈ Ioc 0 Y.top →
      K.Valid ∧
      (∃ (Q : PairSequence Y.L (Y.IsPair g)) (S : LimitTheorem.CumulantFamily), Q.Defines S) ∧
      (∀ Q : PairSequence Y.L (Y.IsPair g), ∃ (φ : ℕ+ → ℕ+) (hφ : Tendsto φ atTop atTop)
        (S : LimitTheorem.CumulantFamily), (Q.subseq φ hφ).Defines S) ∧
      ∀ (Q : PairSequence Y.L (Y.IsPair g)) (S : LimitTheorem.CumulantFamily), Q.Defines S →
        ErgodicDecompositionConclusion Y.M Y.ϑ (Y.consts g).lawScale (Y.consts g).lawError K Q S := by
    intro g
    by_cases hg : g ∈ Ioc 0 Y.top
    · obtain ⟨K, hs, hc, hl, hr⟩ := hC Y.M (Y.consts g) Y.one_le_M (Y.consts_admissible g hg)
      obtain ⟨he, hsub⟩ := hL Y g hg
      refine ⟨limitConstantsOf K, fun _ => ⟨limitConstantsOf_admissible hs, he, hsub, fun Q S hQ => ?_⟩⟩
      let Qf := approximatingSequenceOfPairs Y hg hP Q
      have hQf : Qf.Defines S := hQ
      exact conclusion_of hg hP hT (E := lawConstantsOf (Y.consts g)) hQ
        (hc _ rfl (FiveBoundSystem.boundsHoldAt_statedSideFamily Y hg) Qf S hQf)
        (hl _ rfl (FiveBoundSystem.boundsHoldAt_statedSideFamily Y hg) Y.ϑ Y.ϑ_mem Y.ϑ_le
          (FiveBoundSystem.twoPointLawAt_statedSideFamily Y hg) Qf S hQf)
        (hr _ rfl (FiveBoundSystem.boundsHoldAt_statedSideFamily Y hg) Y.ϑ Y.ϑ_mem Y.ϑ_le
          (FiveBoundSystem.twoPointLawAt_statedSideFamily Y hg) Qf S hQf)
    · exact ⟨limitConstantsOf ⟨fun _ _ _ => 0, fun _ _ => 0, fun _ => 0, 0, 0, 0, 0, 0,
        fun _ _ => 0, fun _ _ => 0⟩, fun h => absurd h hg⟩
  choose K hK using hK
  exact ⟨K, fun g hg => hK g hg⟩
end MainTheorem
end YangMills.Construction.SystemsWithFiveBounds
end
