import YangMills.Construction.InfiniteLattice.CubesDomainsAndEdgeTreesOfTheWholeLattice
import YangMills.Construction.InfiniteLattice.MapsThatALatticeIsometryInducesOnATorus
import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.NormalFamilies
def PeriodSublattice.minSupPeriod (Γ : PeriodSublattice 1) : ℝ :=
  sInf {s | ∃ γ ∈ Γ.periods, γ ≠ 0 ∧ s = YangMills.Construction.WholeSpace.maxNorm (γ : AmbientSpace)}
def PeriodsDiverge (Γ : ℕ → PeriodSublattice 1) : Prop :=
  Tendsto (fun i => (Γ i).minSupPeriod) atTop atTop
def TorusMeasureWeakLimits : Prop :=
  ∀ β : ℝ, 0 < β →
    (∀ Γ : ℕ → PeriodSublattice 1, PeriodsDiverge Γ →
      ∀ ν : Measure (GaugeField 1), IsProbabilityMeasure ν →
        IsWeakClusterPointUnitSpacing (fun i => (Γ i).liftedGibbsMeasure β) ν →
        ν ∈ subgroupInvariantGibbsClass one_pos β ⊤) ∧
    (∀ (𝔸 : LocalObservableArray) (t : ℕ → ℝ) (ν : ℕ → Measure (GaugeField 1))
        (ν₀ : Measure (GaugeField 1)), IsProbabilityMeasure ν₀ →
      Tendsto t atTop (𝓝 0) → (∀ k, 1 ≤ k → ν k ∈ 𝔸.tiltedGibbsClass β (t k)) →
      WeakConvergesUnitSpacing ν ν₀ → ν₀ ∈ gibbsClass one_pos β) ∧
    (∀ (P : NormalLevelPair 1) (ν : Measure (GaugeField 1)), IsProbabilityMeasure ν →
      IsSymmetricUnder ν P.reflectSymmetry →
      (∀ F ∈ halfSpaceContinuousLocal 1 P.normal P.level 1,
        0 ≤ stateEval ν (P.conjReflectObservable F * F)) →
      ∀ F, (F ∈ halfSpaceObservables 1 P.normal P.level 1 ∨
          F ∈ halfSpaceObservables 1 P.normal P.level (-1)) →
        0 ≤ stateEval ν (P.conjReflectObservable F * F)) ∧
    ∀ (𝔸 : LocalObservableArray) (t : ℝ) (Γ : ℕ → PeriodSublattice 1),
      (∀ i, 1 ≤ i → 𝔸.FitsPeriods (Γ i)) → PeriodsDiverge Γ →
      (∀ ν : Measure (GaugeField 1), IsProbabilityMeasure ν →
        IsWeakClusterPointUnitSpacing (fun i => 𝔸.tiltedLiftMeasure (Γ i) β t) ν →
        ν ∈ 𝔸.tiltedGibbsClass β t ∧ ∀ v ∈ 𝔸.sublattice, IsSymmetricUnder ν (shift v)) ∧
      (∀ r : LatticeSymmetry 1, (∀ i, 1 ≤ i → (Γ i).OrthogonalPartPreserves r) →
        (∀ i, 1 ≤ i →
          (Γ i).IsDescendedMap r ((Γ i).descendedMap r) ∧
          Function.Bijective ((Γ i).descendedMap r) ∧
          (Γ i).IsDescendedPullback r ((Γ i).descendedPullback r)) ∧
        ((∀ i, 1 ≤ i → PeriodSublattice.IsHomeomorphInvariant (𝔸.tiltedMeasure (Γ i) β t)
            ((Γ i).descendedPullback r)) →
          ∀ ν : Measure (GaugeField 1), IsProbabilityMeasure ν →
            IsWeakClusterPointUnitSpacing (fun i => 𝔸.tiltedLiftMeasure (Γ i) β t) ν →
            IsSymmetricUnder ν r)) ∧
      ∀ P : NormalLevelPair 1,
        (∀ F ∈ halfSpaceContinuousLocal 1 P.normal P.level 1, ∃ i₀ : ℕ,
          ∀ i, 1 ≤ i → i₀ ≤ i →
            0 ≤ PeriodSublattice.integralOf (𝔸.tiltedMeasure (Γ i) β t)
              ((Γ i).periodize (P.conjReflectObservable F * F))) →
        ∀ ν : Measure (GaugeField 1), IsProbabilityMeasure ν →
          IsWeakClusterPointUnitSpacing (fun i => 𝔸.tiltedLiftMeasure (Γ i) β t) ν →
          ∀ F ∈ halfSpaceContinuousLocal 1 P.normal P.level 1,
            0 ≤ stateEval ν (P.conjReflectObservable F * F)
end YangMills.Construction.InfiniteLattice
