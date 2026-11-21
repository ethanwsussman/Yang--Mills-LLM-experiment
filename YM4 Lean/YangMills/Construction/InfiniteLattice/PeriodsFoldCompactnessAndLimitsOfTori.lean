import YangMills.Construction.InfiniteLattice.LatticeMirrorsAsHyperplanesAndToriOfAnyShape
import YangMills.Construction.InfiniteLattice.PeriodGroupsOfOneFamily
import YangMills.Construction.InfiniteLattice.SlabOfALadder
import YangMills.Construction.InfiniteLattice.StatesFunctionsAndTheWeakTopologyOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder NNReal
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open YangMills.Construction.NormalFamilies
namespace PeriodicGibbsFoldAndCompactness
def SinglePeriodGroup (β : ℝ) : Prop :=
  periodicGibbsClass one_pos β =
    subgroupInvariantGibbsClass one_pos β (evenLattice.addSubgroupOf (latticeSubgroup 1))
def FoldBound (β : ℝ) : Prop :=
  ∀ R : MirrorLadder, ∀ A ∈ continuousLocalFunctions 1, (∀ U, (A U).im = 0) →
    IsSupportedIn A R.slabSet →
    ∀ ν ∈ subgroupInvariantGibbsClass one_pos β
        ((axialPeriodLattice R.normal R.spacing).addSubgroupOf (latticeSubgroup 1)),
      ∃ ν₀ ∈ subgroupInvariantGibbsClass one_pos β
          ((normalPeriodLattice R.normal R.spacing).addSubgroupOf (latticeSubgroup 1)),
        stateEval ν A ≤ stateEval ν₀ A ∧
        ∀ M ∈ R.rungs,
          (∀ G : GaugeField 1 → ℂ, IsBoundedObservable G →
            stateEval ν₀ (M.reflectObservable G) = stateEval ν₀ G) ∧
          ∀ G, (G ∈ halfSpaceObservables 1 M.normal M.level 1 ∨
              G ∈ halfSpaceObservables 1 M.normal M.level (-1)) →
            0 ≤ stateEval ν₀ (M.conjReflectObservable G * G)
def ConvexAndCompact (β : ℝ) : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (H : AddSubgroup (LatticePoint a)),
    (Convex ℝ≥0 (gibbsClass ha β) ∧ IsWeakCompact (gibbsClass ha β)) ∧
      Convex ℝ≥0 (subgroupInvariantGibbsClass ha β H) ∧
        IsWeakCompact (subgroupInvariantGibbsClass ha β H)
def TorusLimits (β : ℝ) : Prop :=
  (∀ Λ : PeriodSublattice 1, IsLatticeState (Λ.liftedGibbsMeasure β)) ∧
    ∀ Λ : ℕ → PeriodSublattice 1, MinNonzeroNormTendsToInfinity Λ →
      ∀ μ : Measure (GaugeField 1), IsLatticeState μ →
        IsWeakClusterPoint (fun i => (Λ i).liftedGibbsMeasure β) μ →
        μ ∈ subgroupInvariantGibbsClass one_pos β ⊤
def ContinuousLocalToBounded : Prop :=
  ∀ (M : NormalLevelPair 1) (μ : Measure (GaugeField 1)), IsLatticeState μ →
    IsSymmetricUnder μ M.reflectSymmetry →
    (∀ G ∈ halfSpaceContinuousLocal 1 M.normal M.level 1,
      0 ≤ stateEval μ (M.conjReflectObservable G * G)) →
    ∀ G, (G ∈ halfSpaceObservables 1 M.normal M.level 1 ∨
        G ∈ halfSpaceObservables 1 M.normal M.level (-1)) →
      0 ≤ stateEval μ (M.conjReflectObservable G * G)
def Statement : Prop :=
  ∀ β : ℝ, 0 < β →
    SinglePeriodGroup β ∧ FoldBound β ∧ ConvexAndCompact β ∧ TorusLimits β ∧
      ContinuousLocalToBounded
end PeriodicGibbsFoldAndCompactness
end InfiniteLattice
end YangMills.Construction
end
