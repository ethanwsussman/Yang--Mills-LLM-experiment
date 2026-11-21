import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import YangMills.Construction.InfiniteLattice.ConnectedFourPointFunctionOfAStateAtOneSpacing
import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.FourPointMoments
open PeriodicExtensions SetPartition
structure IsBallQuadruple (r : ℝ) (f : Fin 4 → AmbientSpace → ℝ) : Prop where
  measurable : ∀ k, Measurable (f k)
  bounded : ∀ k, TestFunctions.IsBoundedFun (f k)
  supports_subset_ball : ∃ c : AmbientSpace, ∀ k, tsupport (f k) ⊆ TestFunctions.closedBallR4 c r
  separated : ∃ d : ℝ, TestFunctions.HasSeparatedSupportsR4 f d
def momentCumulantSum (M : Finset (Fin 4) → ℝ) : ℂ :=
  ∑ P : PartitionsFin 4, (-1 : ℂ) ^ (blockCount P - 1) *
    ((blockCount P - 1).factorial : ℂ) * ∏ J ∈ P.parts, (M J : ℂ)
def MomentFormulaOnTori (L K : ℕ) (β : ℝ) : Prop :=
  ∀ (m : ℕ) (_ : 0 < m) (h : Fin 4 → PeriodicLattice.FourTorus L m → ℝ),
    SchwingerFunctions.IsTorusTestFamily h →
    SchwingerFunctions.connectedSchwinger L m K β h = momentCumulantSum fun J =>
      PeriodicLattice.gibbsExpectation L m K β
        fun U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2 =>
          ∏ i ∈ J, PeriodicLattice.smearedObservable (h i) U
def MomentFormulaForStates (L K : ℕ) (f : Fin 4 → AmbientSpace → ℝ) : Prop :=
  ∀ ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)),
    fourPointUrsell ν.measure f = momentCumulantSum fun J =>
      ν.value fun U => ∏ i ∈ J, smearedEnergy (f i) U
def IsPeriodizedObservable (L K : ℕ) (β r : ℝ) (f : Fin 4 → AmbientSpace → ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → 4 * r ≤ PeriodicLattice.torusSide L m →
    (∃ A : Set AmbientSpace, ∀ k,
      TestFunctions.IsPeriodizable (PeriodicLattice.torusSide L m) A (f k)) ∧
    (∃ d : ℝ, TestFunctions.HasSeparatedSupportsTorus (SchwingerFunctions.periodizeAll L m f) d) ∧
    (∀ (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) (k : Fin 4),
      smearedEnergy (f k) (liftCompactField U) =
        PeriodicLattice.smearedObservable (SchwingerFunctions.periodizeAll L m f k) U.1) ∧
    fourPointUrsell (liftedWilsonMeasure L m K β) f =
      SchwingerFunctions.connectedSchwingerR4 L m K β f
def ContinuousInState (L K : ℕ) (f : Fin 4 → AmbientSpace → ℝ) : Prop :=
  (∀ k, Continuous fun U : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
    smearedEnergy (f k) U) ∧
  Continuous fun ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) =>
    fourPointUrsell ν.measure f
def BoundsPassToLimits (L K : ℕ) (β r : ℝ) (f : Fin 4 → AmbientSpace → ℝ) : Prop :=
  ∀ c C s₀ : ℝ, 0 < s₀ →
    (∀ m : ℕ, 0 < m → max s₀ (4 * r) ≤ PeriodicLattice.torusSide L m →
      c ≤ (SchwingerFunctions.connectedSchwingerR4 L m K β f).re ∧
        (SchwingerFunctions.connectedSchwingerR4 L m K β f).re ≤ C) →
    ∀ ν ∈ limitsOfLiftedMeasures L K β,
      c ≤ (fourPointUrsell ν.measure f).re ∧
        (fourPointUrsell ν.measure f).re ≤ C
def LimitsInGibbsSet (L K : ℕ) (β : ℝ) : Prop :=
  (∀ m : ℕ, 0 < m → IsProbabilityMeasure (liftedWilsonMeasure L m K β)) ∧
  ∀ ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)),
    (∀ m : ℕ → ℕ+, SidesTendToInfinity L (fun i => PeriodicLattice.torusSide L (m i)) →
      CutoffLattice.WeaklyConvergent (fun i => liftedWilsonMeasure L (m i) K β) ν.measure →
      ν ∈ limitsOfLiftedMeasures L K β) ∧
    (IsLimitOfLiftedMeasures L K β ν → ν ∈ limitsOfLiftedMeasures L K β) ∧
    (IsInfiniteVolumeLimit L K β ν.measure → ν ∈ limitsOfLiftedMeasures L K β)
def MomentsExtensionsAndLimits : Prop :=
  ∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K → ∀ β : ℝ, 0 < β →
    MomentFormulaOnTori L K β ∧ LimitsInGibbsSet L K β ∧
    ∀ (r : ℝ) (f : Fin 4 → AmbientSpace → ℝ), 0 < r → IsBallQuadruple r f →
      MomentFormulaForStates L K f ∧ IsPeriodizedObservable L K β r f ∧ ContinuousInState L K f ∧
        BoundsPassToLimits L K β r f
end YangMills.Construction.InfiniteLattice.FourPointMoments
end
