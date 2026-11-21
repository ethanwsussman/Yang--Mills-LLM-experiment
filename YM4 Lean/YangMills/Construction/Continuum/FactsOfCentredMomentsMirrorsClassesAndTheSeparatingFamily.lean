import YangMills.Construction.Continuum.ClassesOfTuplesMomentConstantsAndApproximants
import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import YangMills.Construction.InfiniteLattice.RepresentativeCentredAtAStateAndCentredMoment
import YangMills.Construction.Lattice.AdicRationalsPositive
import YangMills.Construction.ReflectionPositivity.PositionsAndKindsOfMirrors
import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.AmbientPoints
open YangMills.Construction.TorusFunctionals (sharpNormAt)
noncomputable section
namespace YangMills.Construction.ContinuumSetting
section Torus
variable (D : ConnectedFunctions.CouplingData)
def TorusMomentPartitionExpansion (X : FunctionTuple D.toStandingParameters .torus) : Prop :=
  ((TorusFunctionals.Periodic.centredProductExpectation D X.2 : ℝ) : ℂ) =
    ∑ π ∈ SetPartition.singletonFree X.1, ∏ J ∈ π.parts,
      D.cumulantReal (restrictTuple X.2 J)
def IsTorusCumulantFamily (S : ConnectedFamily D.toStandingParameters .torus) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : separatedTuples D.toStandingParameters .torus n),
    ((S.fn n hn f : ℝ) : ℂ) = D.cumulantReal f.1
def TorusMomentFacts : Prop :=
  (∀ X ∈ separatedTuplesSmoothOrLip D.toStandingParameters .torus, 1 ≤ X.1 →
    TorusMomentPartitionExpansion D X) ∧
  ∃ S : ConnectedFamily D.toStandingParameters .torus, IsTorusCumulantFamily D S ∧
    ∀ X : allSeparatedTuples D.toStandingParameters .torus,
      TorusFunctionals.Periodic.centredProductExpectation D X.1.2 = S.centred X
end Torus
abbrev LatticeState (s : Conventions.StandingParameters) : Type :=
  InfiniteLattice.GaugeFieldProbability (PeriodicLattice.meshSize s.L (s.K : ℕ))
section InAState
variable {s : Conventions.StandingParameters} (ν : LatticeState s)
def StateMomentPartitionExpansion (X : FunctionTuple s .euclidean) : Prop :=
  ((CentredRepresentative.centredMoment ν X : ℝ) : ℂ) =
    ∑ π ∈ SetPartition.singletonFree X.1, ∏ J ∈ π.parts,
      InfiniteLattice.ursellFunction ν.1 J.card (restrictTuple X.2 J)
def StateCumulantMobiusExpansion (X : FunctionTuple s .euclidean) : Prop :=
  InfiniteLattice.ursellFunction ν.1 X.1 X.2 =
    ∑ π : SetPartition.PartitionsFin X.1,
      (-1 : ℂ) ^ (SetPartition.blockCount π - 1) *
        ((SetPartition.blockCount π - 1).factorial : ℂ) *
          ∏ J ∈ π.parts,
            ((CentredRepresentative.centredMoment ν (restrictSigmaTuple X J) : ℝ) : ℂ)
def IsStateCumulantFamily (S : ConnectedFamily s .euclidean) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : separatedTuples s .euclidean n),
    ((S.fn n hn f : ℝ) : ℂ) = InfiniteLattice.ursellFunction ν.1 n f.1
def separatedCentredMoment (X : allSeparatedTuples s .euclidean) : ℝ :=
  CentredRepresentative.centredMoment ν X.1
def StateMomentFacts : Prop :=
  (∀ X ∈ separatedTuplesSmoothOrLip s .euclidean, 1 ≤ X.1 →
    StateMomentPartitionExpansion ν X) ∧
  (∀ X ∈ separatedTuplesSmoothOrLip s .euclidean, X.1 = 1 →
    CentredRepresentative.centredMoment ν X = 0) ∧
  (∀ X ∈ separatedTuplesSmoothOrLip s .euclidean, 2 ≤ X.1 →
    StateCumulantMobiusExpansion ν X) ∧
  (∃ S : ConnectedFamily s .euclidean, IsStateCumulantFamily ν S ∧
    ∀ X, separatedCentredMoment ν X = S.centred X) ∧
  IsTupleFunctional (separatedCentredMoment ν) ∧
  ∀ (n : ℕ), 2 ≤ n → ∀ f : separatedTuples s .euclidean n,
    ((connectedOf (separatedCentredMoment ν) n f : ℝ) : ℂ) =
      InfiniteLattice.ursellFunction ν.1 n f.1
end InAState
def TorusHyperplaneAvoidsSites (s : Conventions.StandingParameters) (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ x : PeriodicLattice.Site s.L s.m (s.K : ℕ),
    x.1 ∉ TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) ''
      ReflectionPositivity.AxisMirror.coordSet μ fun t => t = c
section SeparatingFamily
variable (s : Conventions.StandingParameters)
def MemSeparatingTuples (X : FunctionTuple s .euclidean) : Prop :=
  List.ofFn X.2 ∈ SeparatingFamily.separatingTuples s.L
def SeparatingTuplesFacts (M : ℕ) : Prop :=
  (SeparatingFamily.separatingTuples s.L).Countable ∧
  (∀ X, MemSeparatingTuples s X → ∀ w : InfiniteLattice.hyperoctahedralLinearGroup,
    MemSeparatingTuples s (signedPermTuple w X)) ∧
  (∀ X, MemSeparatingTuples s X → ∀ v ∈ SeparatingFamily.adicLatticeVectors s.L,
    MemSeparatingTuples s (translateTuple v X)) ∧
  (∀ X Y, MemSeparatingTuples s X → MemSeparatingTuples s Y →
    (Pairwise fun i j => Disjoint (tsupport ((tupleAppend X Y).2 i))
      (tsupport ((tupleAppend X Y).2 j))) →
    MemSeparatingTuples s (tupleAppend X Y)) ∧
  ∀ X ∈ allSeparatedTuples s .euclidean, 1 ≤ X.1 →
    ∀ O : Fin X.1 → Set (Pt s .euclidean), (∀ i, IsOpen (O i)) →
      (∀ i, tsupport (X.2 i) ⊆ O i) →
      ∃ φ, SeparatedClasses.IsApproxSeqOn s M X O φ
end SeparatingFamily
def SettingFacts : Prop :=
  (∀ D : ConnectedFunctions.CouplingData, TorusMomentFacts D) ∧
  (∀ (s : Conventions.StandingParameters) (ν : LatticeState s), StateMomentFacts ν) ∧
  (∀ (s : Conventions.StandingParameters) (μ : Fin 4) (c : ℝ),
    c ∈ ReflectionPositivity.AxisMirror.linkLevels (PeriodicLattice.meshSize s.L (s.K : ℕ)) →
      TorusHyperplaneAvoidsSites s μ c ∧ TorusHyperplaneAvoidsSites s μ (c + s.side / 2)) ∧
  (∀ (s : Conventions.StandingParameters) (ν : LatticeState s),
    ∀ X ∈ allSeparatedTuples s .euclidean,
    ∀ Y ∈ allSeparatedTuples s .euclidean,
      tupleAppend X Y ∈ allSeparatedTuples s .euclidean →
        ∀ U, CentredRepresentative.centredProduct ν (tupleAppend X Y) U =
          CentredRepresentative.centredProduct ν X U *
            CentredRepresentative.centredProduct ν Y U) ∧
  (∀ s : Conventions.StandingParameters, ∀ X ∈ allSeparatedTuples s .euclidean,
    ∃ ϖ ∈ PeriodicLattice.adicRationalsPositive s.L, ∃ d R : ℝ,
      0 < d ∧ d ≤ ϖ ∧ 0 < R ∧ X ∈ SeparatedClasses.classOf s ϖ d R) ∧
  ∀ (s : Conventions.StandingParameters) (M : ℕ), LatticeLimits.IsBlockScale s M →
    SeparatingTuplesFacts s M
end YangMills.Construction.ContinuumSetting
