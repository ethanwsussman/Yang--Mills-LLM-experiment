import YangMills.Construction.BoundsOnEverySide.SeparatedLimitsUnderABound
import YangMills.Construction.Continuum.SharpNormOfATestFunctionAndNeighbourhoodsOfDisjointCompactSetsProof
import YangMills.Construction.InfiniteLattice.InfiniteVolumeLimitPointsOfTheTorusStates
import YangMills.Construction.InfiniteLattice.LimitPointsOfTheTorusMeasuresArePeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.TorusConfigurationsAndMeasuresThroughTheCoveringMapOfACutoff
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfTheFamilyAreLimitsAlongSequences
import YangMills.Construction.SystemsWithFiveBounds.LimitsAlongThePairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter Set
open scoped Topology
open InfiniteLattice
namespace SystemsWithFiveBounds
open LimitTheorem
open LimitGrowthFromCutoffBound (restrictToTestTuples)
namespace LimitsAlongPairs
structure Prerequisites : Prop where
  separatedLimits : BoundsOnEverySide.SeparatedLimitsExist
  periodicGibbs : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs
  torusLimits : InfiniteLattice.TorusStateLimitPoints
  coveringIdent : InfiniteLattice.CutoffCovering.CoveringIdentification
  sequentialLimits : InfiniteLattice.PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits
private theorem isLipschitzFor_of_contDiff {f : (Fin 4 → ℝ) → ℝ} (h₁ : ContDiff ℝ 1 f)
    (h₂ : HasCompactSupport f) : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f := by apply _root_.YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings.isLipschitzFor_of_contDiff <;> assumption
variable (P : Prerequisites) (Y : FiveBoundSystem) {g : ℝ} (hg : g ∈ Ioc 0 Y.top)
include P hg in
theorem state_mem_periodicGibbsSet (Q : PairSequence Y.L (Y.IsPair g)) (j : ℕ+) :
    Q.state j ∈ periodicGibbsSet Y.L (Q.cutoff j) (Q.coupling j) :=
  (P.periodicGibbs Y.L (Q.cutoff j) Y.admissibleL (Q.cutoff j).pos (Q.coupling j)
    (Y.β_pos g hg _ _ (Q.pair j))).2 (Q.isLimit j)
def toGibbsStateSequence (Q : PairSequence Y.L (Y.IsPair g)) :
    BoundsOnEverySide.GibbsStateSequence Y.L where
  K := Q.cutoff
  β := Q.coupling
  gibbs := Q.state
  gibbs_mem := state_mem_periodicGibbsSet P Y hg Q
theorem cumulantsBoundedBy (Q : PairSequence Y.L (Y.IsPair g)) :
    (toGibbsStateSequence P Y hg Q).CumulantsBoundedBy Y.M (Y.consts g).cumulantBound := by
  intro j n hn R d hR hd X hX
  refine Y.cumulant_bound g hg _ _ (Q.pair j) _
    (Y.limits_mem g hg _ _ (Q.pair j) _ (Q.isLimit j)) n hn R d hR hd X.1
    (fun i => isLipschitzFor_of_contDiff (X.2.1 i).1 (X.2.1 i).2.1) hX.1 ⟨hd, fun i k hik => ?_⟩
  exact hX.2.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le_of_le hik le_rfl)))
include P hg in
theorem exists_convergent_subseq (Q : PairSequence Y.L (Y.IsPair g)) :
    ∃ (φ : ℕ+ → ℕ+) (hφ : Tendsto φ atTop atTop) (S : CumulantFamily),
      (Q.subseq φ hφ).Defines S := by
  obtain ⟨φ, S, hS⟩ := P.separatedLimits Y.L Y.admissibleL Y.M Y.one_le_M
    (toGibbsStateSequence P Y hg Q) _ (cumulantsBoundedBy P Y hg Q)
    ⟨Y.L, Y.admissibleL, 1, ⟨1, one_pos⟩⟩
  have hge : Tendsto φ atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => ha.trans hS.strictMono.le_apply⟩
  exact ⟨φ, hge, restrictToTestTuples S, fun n hn X => hS.tendsto n hn ⟨X.1, _⟩⟩
include P in
theorem exists_infiniteVolumeLimit (K : ℕ+) {β : ℝ} (hβ : 0 < β) :
    ∃ ν : MeasureTheory.Measure (GaugeField (PeriodicLattice.meshSize Y.L ((K : ℕ) : ℤ))),
      IsInfiniteVolumeLimit Y.L K β ν := by
  obtain ⟨p, m, ρ, hm, hside, hρ, hconv⟩ :=
    (P.torusLimits Y.L Y.admissibleL K K.pos β hβ).1.1
  have h₁ := (P.coveringIdent ⟨⟨Y.L, Y.admissibleL, K, ⟨1, one_pos⟩⟩, β, hβ⟩).2.2.2
  have h₂ := (P.sequentialLimits Y.L K Y.admissibleL K.pos β hβ).2.1
  have hmem : IsInfiniteVolumeLimit Y.L K β p.1 ↔ p.1 ∈ weakLimitsAlongSides Y.L K β :=
    Set.ext_iff.1 (h₁.trans h₂.symm) p.1
  refine ⟨p.1, hmem.2 ⟨p.2, m, hm, hside, fun F hF' => ?_⟩⟩
  refine (hconv F hF').congr fun i => ?_
  show ∫ U, F U ∂(ρ i).1 = _
  rw [hρ i]
include P hg in
theorem nonempty_pairSequence : Nonempty (PairSequence Y.L (Y.IsPair g)) := by
  have hK : ∀ j : ℕ+, ∃ K : ℕ+, j < K ∧ ∃ β, Y.IsPair g K β := fun j => by
    obtain ⟨K, hK, hj⟩ := (Y.infinite_cutoffs g hg).exists_gt j
    exact ⟨K, hj, hK⟩
  choose K hKgt hKW using hK
  choose β hβ using hKW
  have hstate := fun j => exists_infiniteVolumeLimit P Y (K j) (Y.β_pos g hg _ _ (hβ j))
  choose ν hν using hstate
  refine ⟨⟨K, ?_, β, hβ, ν, hν⟩⟩
  refine tendsto_atTop_atTop.2 fun b => ⟨b.succPNat, fun j hj => ?_⟩
  have h₁ : (b.succPNat : ℕ) ≤ (j : ℕ) := hj
  have h₂ : (j : ℕ) < (K j : ℕ) := hKgt j
  have h₃ : (b.succPNat : ℕ) = b + 1 := rfl
  omega
theorem of_prerequisites (P : Prerequisites) : SubsequentialLimitsAlongPairs := by
  intro Y g hg
  refine ⟨?_, exists_convergent_subseq P Y hg⟩
  obtain ⟨Q⟩ := nonempty_pairSequence P Y hg
  obtain ⟨φ, hφ, S, hS⟩ := exists_convergent_subseq P Y hg Q
  exact ⟨Q.subseq φ hφ, S, hS⟩
theorem subsequentialLimitsAlongPairs_holds
    (hSeparated : BoundsOnEverySide.SeparatedLimitsExist)
    (hStates : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs)
    (hTorusStates : InfiniteLattice.TorusStateLimitPoints)
    (hCovering : InfiniteLattice.CutoffCovering.CoveringIdentification)
    (hSequences : InfiniteLattice.PeriodicLiftAtCutoff.ClusterPointsAreSequentialLimits) :
    SubsequentialLimitsAlongPairs :=
  of_prerequisites ⟨hSeparated, hStates, hTorusStates, hCovering, hSequences⟩
end LimitsAlongPairs
end SystemsWithFiveBounds
end YangMills.Construction
end
