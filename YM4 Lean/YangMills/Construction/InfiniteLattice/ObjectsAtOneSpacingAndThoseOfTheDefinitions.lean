import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import YangMills.Construction.InfiniteLattice.PeriodicExtensionIsFormed
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfTheTorusFamily
import YangMills.Construction.Lattice.ActionAndFlatDistanceOfATorusLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.FixedSpacing
def TorusAndLatticeIdentification (L m K : ℕ) : Prop :=
  TorusMetric.Torus4 (PeriodicLattice.torusSide L m) = PeriodicLattice.FourTorus L m ∧
    Function.Surjective (PeriodicLattice.torusProjHom L m) ∧
    (PeriodicLattice.torusProjHom L m).ker = latticeSubgroup (2 * (L : ℝ) ^ m) ∧
    (∀ x y : AmbientSpace,
      IsLeast (range fun k : Fin 4 → ℤ =>
          TorusMetric.euclidNormVec
            (x - y - TestFunctions.latticeTranslate (PeriodicLattice.torusSide L m) k))
        (TorusMetric.torusEuclidNorm
          (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x -
            TorusMetric.torusProj (PeriodicLattice.torusSide L m) y)) ∧
      TorusMetric.torusEuclidNorm
          (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x -
            TorusMetric.torusProj (PeriodicLattice.torusSide L m) y) =
        PeriodicLattice.torusDist L m (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x)
          (TorusMetric.torusProj (PeriodicLattice.torusSide L m) y)) ∧
    (PeriodicLattice.sublattice L m (K : ℤ) : Set (PeriodicLattice.FourTorus L m)) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) ''
        (latticeSubgroup (PeriodicLattice.meshSize L (K : ℤ)) : Set AmbientSpace)
def TorusUrsellIdentification (L m K : ℕ) (β : ℝ) : Prop :=
  (∀ (n : ℕ) (h : Fin n → PeriodicLattice.FourTorus L m → ℝ), PeriodicLattice.IsBoundedFamily h →
    PeriodicLattice.torusUrsellFunction L m K β h =
      Cumulants.mixedCumulant (PeriodicLattice.wilsonGibbsMeasure L m K β) fun i U =>
        PeriodicLattice.observableExpanded (h i) U) ∧
    ∀ (n : ℕ) (h : Fin n → PeriodicLattice.FourTorus L m → ℝ), 2 ≤ n →
      (∀ i, TestFunctions.IsLipschitzFor (PeriodicLattice.torusDist L m) (h i)) →
      (∃ d : ℝ, TestFunctions.HasSeparatedSupportsTorus h d) →
      SchwingerFunctions.IsTorusTestFamily h ∧
        PeriodicLattice.torusUrsellFunction L m K β h =
          SchwingerFunctions.connectedSchwinger L m K β h
def InfiniteLatticeSpaceIdentification (L K : ℕ) : Prop :=
  RefinedGaugeField L K = GaugeField (PeriodicLattice.meshSize L (K : ℤ)) ∧
    Topology.IsEmbedding (fun U : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
      (U : Link (PeriodicLattice.meshSize L (K : ℤ)) → Matrices.ComplexMatrix2.specialUnitary)) ∧
    range (fun U : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
      (U : Link (PeriodicLattice.meshSize L (K : ℤ)) → Matrices.ComplexMatrix2.specialUnitary)) =
        {U | ∀ b, U b.opposite = (U b)⁻¹} ∧
    ∀ (ν : ℕ → GibbsAtFixedSpacing.BorelProb (PeriodicLattice.meshSize L (K : ℤ)))
      (ν₀ : GibbsAtFixedSpacing.BorelProb (PeriodicLattice.meshSize L (K : ℤ))),
      Tendsto ν atTop (𝓝 ν₀) ↔ GibbsAtFixedSpacing.BorelProb.TendstoWeak ν ν₀
def LiftedWilsonMeasureIdentification (L m K : ℕ) (β : ℝ) : Prop :=
  (∀ (U : PeriodicLattice.CompactGaugeField L m (K : ℤ))
      (b : Link (PeriodicLattice.meshSize L (K : ℤ))),
    liftCompactField U b = U.linkValue (projectLink L m (K : ℤ) b)) ∧
    (LiftFormation.torusWilson L m K β).map liftCompactField = liftedWilsonMeasure L m K β ∧
    BijOn (liftCompactField : PeriodicLattice.CompactGaugeField L m (K : ℤ) → _) univ
      (periodicFields L m (K : ℤ)) ∧
    IsProbabilityMeasure (liftedWilsonMeasure L m K β)
def mixedLogDerivative {L K n : ℕ} (ν : Measure (RefinedGaugeField L K))
    (f : Fin n → AmbientSpace → ℝ) : ℂ :=
  iteratedFDeriv ℂ n (fun z : Fin n → ℂ => Cumulants.principalLog
      (Cumulants.expectationC ν fun U =>
        Complex.exp (∑ i, z i * cutoffSmearedEnergy (fun x => (f i x : ℂ)) U))) 0
    fun i => Pi.single i 1
def ObservableAndUrsellIdentification (L K : ℕ) : Prop :=
  (∀ f : AmbientSpace → ℂ, (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
    (IsBoundedOfBoundedSupport f ↔ HasCompactSupport f)) ∧
    (∀ f : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported f →
      ∀ U : GaugeField (PeriodicLattice.meshSize L (K : ℤ)),
        cutoffSmearedEnergy (L := L) (K := K) f U = smearedEnergy f U) ∧
    ∀ (ν : GibbsAtFixedSpacing.BorelProb (PeriodicLattice.meshSize L (K : ℤ))) (n : ℕ)
      (f : Fin n → AmbientSpace → ℝ), 1 ≤ n →
      (∀ j, (∃ C : ℝ, ∀ x, |f j x| ≤ C) ∧ HasCompactSupport (f j)) →
      ursellFunctionOfFamily (L := L) (K := K) (ν : GaugeFieldProbability _).1 f =
          mixedLogDerivative (L := L) (K := K) (ν : GaugeFieldProbability _).1 f ∧
        mixedLogDerivative (L := L) (K := K) (ν : GaugeFieldProbability _).1 f =
          smearedEnergyCumulant (ν : GaugeFieldProbability _).1 f
def IsWeakLimitAlongTorusSides (L K : ℕ) (β : ℝ)
    (ν : GibbsAtFixedSpacing.BorelProb (PeriodicLattice.meshSize L (K : ℤ))) : Prop :=
  ∃ (ℓ : ℕ → ℝ) (ρ : ℕ → GibbsAtFixedSpacing.BorelProb (PeriodicLattice.meshSize L (K : ℤ))),
    TendstoInfinityThroughSides L ℓ ∧
    (∀ i, ∃ m : ℕ, 0 < m ∧ ℓ i = PeriodicLattice.torusSide L m ∧
      (ρ i : GaugeFieldProbability _).1 = liftedWilsonMeasure L m K β) ∧
    GibbsAtFixedSpacing.BorelProb.TendstoWeak ρ ν
def ClusterPointsAreSequentialLimits (L K : ℕ) (β : ℝ) : Prop :=
  (∀ ν : GibbsAtFixedSpacing.BorelProb (PeriodicLattice.meshSize L (K : ℤ)),
    IsTorusWeakClusterPoint L K β ν ↔ IsWeakLimitAlongTorusSides L K β ν) ∧
    torusWeakClusterPoints L K β = {ν | IsWeakLimitAlongTorusSides L K β ν}
def FixedSpacingDictionary : Prop :=
  ∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K → ∀ β : ℝ, 0 < β →
    ((∀ m : ℕ, 0 < m → TorusAndLatticeIdentification L m K ∧ TorusUrsellIdentification L m K β) ∧
      BijOn (PeriodicLattice.torusSide L) {m | 0 < m} (PeriodicLattice.torusSides L)) ∧
    (InfiniteLatticeSpaceIdentification L K ∧
      (∀ m : ℕ, 0 < m → LiftedWilsonMeasureIdentification L m K β) ∧
      ObservableAndUrsellIdentification L K) ∧
    ClusterPointsAreSequentialLimits L K β
end YangMills.Construction.InfiniteLattice.FixedSpacing
end
