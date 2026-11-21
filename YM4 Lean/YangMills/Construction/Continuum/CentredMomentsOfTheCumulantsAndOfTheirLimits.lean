import YangMills.Construction.Continuum.LimitsOfTheCumulantsAlongToriAndAlongPeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.RefinedLattices
import YangMills.Construction.Lattice.ConnectedFunctionsAndTheCentredIdentityAtArbitraryFunctions
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction
open AmbientPoints
namespace CumulantLimits
variable {D : GrowingTori.GrowthParameters} {g : ℝ} {s : Conventions.StandingParameters} {n : ℕ}
def IsRealValuedAndSlotLinear {X : Type*} (R : Set (X → ℝ)) (c : (Fin n → X → ℝ) → ℂ) : Prop :=
  ∀ f : Fin n → X → ℝ, (∀ k, f k ∈ R) →
    (c f).im = 0 ∧
    (∀ (i : Fin n) (u v : X → ℝ), u ∈ R → v ∈ R →
      c (Function.update f i (u + v)) =
        c (Function.update f i u) + c (Function.update f i v)) ∧
    ∀ (i : Fin n) (u : X → ℝ) (t : ℝ), u ∈ R →
      c (Function.update f i (t • u)) = (t : ℂ) * c (Function.update f i u)
def CentredMomentsOnTorus (X : ConnectedFunctions.CouplingData) : Prop :=
  (∀ (n : ℕ) (f : Fin n → X.Torus → ℝ), (∀ i, f i ∈ X.boundedRealFuns) →
    X.centredMomentFn (X.ofRealTuple f) =
      ∑ π ∈ SetPartition.singletonFree n, ∏ J ∈ π.parts,
        X.cumulantReal fun k => f (J.orderEmbOfFin rfl k)) ∧
  ∀ n : ℕ, 2 ≤ n →
    IsRealValuedAndSlotLinear X.boundedRealFuns (X.cumulantReal (n := n))
def CentredMomentsInState {a : ℝ} (ν : Measure (InfiniteLattice.GaugeField a)) : Prop :=
  (∀ (n : ℕ) (f : Fin n → InfiniteLattice.AmbientSpace → ℝ),
    (∀ i, f i ∈ InfiniteLattice.compactTestFunctions) →
      InfiniteLattice.centeredMoment ν f =
        InfiniteLattice.ursellPartitionSum ν f) ∧
  ∀ n : ℕ, 2 ≤ n →
    IsRealValuedAndSlotLinear InfiniteLattice.compactTestFunctions
      (InfiniteLattice.ursellFunction ν n)
def ToralSequence.couplingDataAt (hg : 0 < g) (Q : ToralSequence D g)
    (j : ℕ+) : ConnectedFunctions.CouplingData :=
  { D.standingParams (Q.passage j).K (Q.sideExponent j) with
    coupling := (Q.passage j).β
    coupling_pos := lt_of_lt_of_le (FlowConstants.passageLevel_pos hg D.width_pos)
      (Q.passage j).mem_window.1 }
def ToralSequence.centredMomentAt (hg : 0 < g)
    (Q : ToralSequence D g) (j : ℕ+) (f : Fin n → Pt s .euclidean → ℝ) : ℂ :=
  (Q.couplingDataAt hg j).centredMomentFn
    ((Q.couplingDataAt hg j).ofRealTuple (SchwingerFunctions.periodizeAll D.L (Q.sideExponent j) f))
def PeriodicGibbsSequence.centredMomentAt
    (Q : PeriodicGibbsSequence D g) (j : ℕ+) (f : Fin n → Pt s .euclidean → ℝ) : ℂ :=
  InfiniteLattice.centeredMoment (Q.measure j) f
def IsConnectedFamily (S : TupleMapFamily s .euclidean) : Prop :=
  (∀ (n : ℕ) (hn : 2 ≤ n), IsTupleMultilinear (S n hn)) ∧
    ∃ F : ConnectedFamily s .euclidean, F.fn = S
def ToralSequence.MomentsTendTo (hg : 0 < g) (Q : ToralSequence D g)
    (S : TupleMapFamily s .euclidean) : Prop :=
  (∀ (n : ℕ) (f : separatedTuples s .euclidean n),
    Tendsto (fun j => Q.centredMomentAt hg j f.1) atTop
      (𝓝 (moments S (toAllSeparated f) : ℂ))) ∧
  IsConnectedFamily S
def PeriodicGibbsSequence.MomentsTendTo (Q : PeriodicGibbsSequence D g)
    (S : TupleMapFamily s .euclidean) : Prop :=
  (∀ (n : ℕ) (f : separatedTuples s .euclidean n),
    Tendsto (fun j => Q.centredMomentAt j f.1) atTop
      (𝓝 (moments S (toAllSeparated f) : ℂ))) ∧
  IsConnectedFamily S
def MomentsIsFunctional (S : ConnectedFamily s .euclidean) : Prop :=
  (∀ n : ℕ, 1 ≤ n → IsTupleMultilinear (ofLength (moments S.fn) n)) ∧
    IsTupleFunctional (moments S.fn)
def CentredMomentsAndTheirLimits : Prop :=
  (∀ X : ConnectedFunctions.CouplingData, CentredMomentsOnTorus X) ∧
  (∀ (s : Conventions.StandingParameters) (β : ℝ), 0 < β →
    ∀ ν : Measure (InfiniteLattice.GaugeField (InfiniteLattice.refinedSpacing s.L s.K)),
      InfiniteLattice.IsGibbs β ν → CentredMomentsInState ν) ∧
  (∀ (D : GrowingTori.GrowthParameters) (g : ℝ) (hg : 0 < g) (s : Conventions.StandingParameters)
    (S : TupleMapFamily s .euclidean),
    (∀ Q : ToralSequence D g, Q.Defines S → Q.MomentsTendTo hg S) ∧
    ∀ Q : PeriodicGibbsSequence D g, Q.Defines S → Q.MomentsTendTo S) ∧
  ∀ (s : Conventions.StandingParameters) (S : ConnectedFamily s .euclidean), MomentsIsFunctional S
end CumulantLimits
end YangMills.Construction
end
