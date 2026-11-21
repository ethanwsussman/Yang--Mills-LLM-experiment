import YangMills.Construction.Continuum.RingsRingTracesAndLifts
import YangMills.Construction.Lattice.PlaquetteFunctionsAndTwoNotionsOfSupport
import YangMills.Construction.Torus.DistanceBallsIntegralAndVolumeInPhysicalUnits
import YangMills.Construction.Torus.IntegralOverTheTorus
import YangMills.Construction.Torus.LiftsOfBallsFunctionsAndTuples
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.FreeRingKernels.RingIntegrals
def FixesZero {n : ℕ} (σ : Fin n → Fin n) : Prop :=
  ∀ i : Fin n, (i : ℕ) = 0 → (σ i : ℕ) = 0
def reverseTail {n : ℕ} {J : Type*} (σ : Fin n → J) : Fin n → J :=
  fun i => σ ⟨(n - (i : ℕ)) % n, Nat.mod_lt _ i.pos⟩
def DistinctOnEdges {n : ℕ} (σ : Fin n → Fin n) (x : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ i j : Fin n, s(i, j) ∈ Tuples.cyclicEdges σ → x i ≠ x j
def RingMembership : Prop :=
  ∀ (J : Type) [Finite J] (n : ℕ), 2 ≤ n → Nat.card J = n →
    (∀ R : Set (Fin n → J), Tuples.IsRingOfTuples R → ∀ σ ∈ R, Tuples.ringClass σ = R) ∧
      (∀ R R' : Set (Fin n → J), Tuples.IsRingOfTuples R → Tuples.IsRingOfTuples R' →
        R = R' ∨ Disjoint R R') ∧
        ∀ R : Set (Fin n → J), Tuples.IsRingOfTuples R → ∀ σ ∈ R, ∀ σ' ∈ R,
          Tuples.cyclicEdges σ = Tuples.cyclicEdges σ'
def RingTuplesFixingZero : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ R : Set (Fin n → Fin n), Tuples.IsRingOfTuples R → ∀ σ ∈ R, FixesZero σ →
    {σ' | σ' ∈ R ∧ FixesZero σ'} = {σ, reverseTail σ}
def RingsOnThreeAndFour : Prop :=
  (∃! R : Set (Fin 3 → Fin 3), Tuples.IsRingOfTuples R) ∧
    {R : Set (Fin 4 → Fin 4) | Tuples.IsRingOfTuples R}.ncard = 3 ∧
      {R : Set (Fin 4 → Fin 4) | Tuples.IsRingOfTuples R} = range Tuples.standardFourRing ∧
        Tuples.cyclicEdges (Tuples.standardFourTuple 0) = {s(0, 1), s(1, 2), s(2, 3), s(3, 0)} ∧
          Tuples.cyclicEdges (Tuples.standardFourTuple 1) = {s(0, 1), s(1, 3), s(3, 2), s(2, 0)} ∧
            Tuples.cyclicEdges (Tuples.standardFourTuple 2) = {s(0, 2), s(2, 1), s(1, 3), s(3, 0)}
def CyclicTraceInvariance : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ σ : Fin n → Fin n, Tuples.IsBijectiveTuple σ →
    ∀ x : Fin n → Fin 4 → ℝ, DistinctOnEdges σ x →
      (∀ σ' ∈ Tuples.ringClass σ, cyclicTrace σ' x = cyclicTrace σ x) ∧
        ∀ v : Fin 4 → ℝ, cyclicTrace σ (fun i => x i + v) = cyclicTrace σ x
def CyclicTraceOnSupportBox : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ σ : Fin n → Fin n, Tuples.IsBijectiveTuple σ →
    ∀ f : Fin n → (Fin 4 → ℝ) → ℝ, IsAdmissibleTestFamily f →
      IsCompact (PropagatorRings.supportBox f) ∧
        (∀ x ∈ PropagatorRings.supportBox f, DistinctOnEdges σ x) ∧
          ContinuousOn (cyclicTrace σ) (PropagatorRings.supportBox f) ∧
            (∃ C : ℝ, ∀ x ∈ PropagatorRings.supportBox f, |cyclicTrace σ x| ≤ C) ∧
              Integrable (weightedOnSupports f (cyclicTrace σ))
def BallLiftIsometric (p : Conventions.StandingParameters) : Prop :=
  ∀ (z : p.Torus) (r : ℝ) (c : Fin 4 → ℝ), TestFunctions.IsAdmissibleRadius p.L p.m r →
    c ∈ PeriodicLattice.liftsOf z →
    BijOn (TorusMetric.torusProj (PeriodicLattice.torusSide p.L p.m))
        (TestFunctions.closedBallR4 c r) (TestFunctions.closedBallTorus z r) ∧
      (∀ y ∈ TestFunctions.closedBallR4 c r, ∀ y' ∈ TestFunctions.closedBallR4 c r,
        TestFunctions.euclidDistTorus (ℓ := PeriodicLattice.torusSide p.L p.m)
            (TorusMetric.torusProj (PeriodicLattice.torusSide p.L p.m) y)
            (TorusMetric.torusProj (PeriodicLattice.torusSide p.L p.m) y') =
          TorusMetric.euclidNormVec (y - y')) ∧
        @IsCompact _ (PeriodicLattice.metricTopology p.L p.m) (TestFunctions.closedBallTorus z r) ∧
          @IsClosed _ (PeriodicLattice.metricTopology p.L p.m) (TestFunctions.closedBallTorus z r)
def LiftSupport (p : Conventions.StandingParameters) : Prop :=
  ∀ (z : p.Torus) (r : ℝ) (c : Fin 4 → ℝ) (f : p.Torus → ℝ) (g : (Fin 4 → ℝ) → ℝ),
    TestFunctions.IsFunctionLift z r c f g →
      PeriodicLattice.euclidSupport g = TestFunctions.closedBallR4 c r ∩
          TorusMetric.torusProj (PeriodicLattice.torusSide p.L p.m) ⁻¹'
            PeriodicLattice.metricSupport f ∧
        IsCompact (PeriodicLattice.euclidSupport g)
def LiftsOfFamilyAgree (p : Conventions.StandingParameters) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (f : Fin n → p.Torus → ℝ) (z z' : p.Torus) (r r' : ℝ),
    TestFunctions.SupportsInBall z r f → TestFunctions.SupportsInBall z' r' f →
      ∀ c ∈ PeriodicLattice.liftsOf z, ∀ c' ∈ PeriodicLattice.liftsOf z',
        (∃ k : Fin 4 → ℤ, ∀ i, TestFunctions.ballIndicatorLift c' r' (f i) =
          fun y => TestFunctions.ballIndicatorLift c r (f i)
            (fun α => y α - PeriodicLattice.torusSide p.L p.m * (k α : ℝ))) ∧
        ((∀ j, PeriodicLattice.IsBoundedBorel (f j)) →
          (Pairwise fun i j => Disjoint (PeriodicLattice.metricSupport (f i))
            (PeriodicLattice.metricSupport (f j))) →
            IsAdmissibleTestFamily (fun i => TestFunctions.ballIndicatorLift c r (f i)) ∧
              IsAdmissibleTestFamily (fun i => TestFunctions.ballIndicatorLift c' r' (f i)) ∧
                ∀ σ : Fin n → Fin n, Tuples.IsBijectiveTuple σ →
                  ∫ x, weightedOnSupports (fun i => TestFunctions.ballIndicatorLift c' r' (f i))
                      (cyclicTrace σ) x =
                    ∫ x, weightedOnSupports (fun i => TestFunctions.ballIndicatorLift c r (f i))
                      (cyclicTrace σ) x)
def TorusConventionsAgree (p : Conventions.StandingParameters) : Prop :=
  TorusMeasure.proj p = TorusMetric.torusProj (PeriodicLattice.torusSide p.L p.m) ∧
    (∀ (u : p.Torus) (t : Fin 4 → ℝ), TorusMeasure.IsLift p u t ↔ t ∈ PeriodicLattice.liftsOf u) ∧
      (∀ u w : p.Torus, TorusMeasure.pointDist u w =
        TestFunctions.euclidDistTorus (ℓ := PeriodicLattice.torusSide p.L p.m) u w) ∧
        TorusMeasure.euclidTopology p = PeriodicLattice.metricTopology p.L p.m ∧
          (∀ f : p.Torus → ℝ, PlaquetteSupports.torusTSupport f = PeriodicLattice.metricSupport f) ∧
            ∀ f : (Fin 4 → ℝ) → ℝ,
              PlaquetteSupports.euclideanTSupport f = PeriodicLattice.euclidSupport f
def Statement : Prop :=
  RingMembership ∧ RingTuplesFixingZero ∧ RingsOnThreeAndFour ∧
    CyclicTraceInvariance ∧ CyclicTraceOnSupportBox ∧
      ∀ p : Conventions.StandingParameters, BallLiftIsometric p ∧ LiftSupport p ∧
        LiftsOfFamilyAgree p ∧ TorusConventionsAgree p
end YangMills.Construction.FreeRingKernels.RingIntegrals
end
