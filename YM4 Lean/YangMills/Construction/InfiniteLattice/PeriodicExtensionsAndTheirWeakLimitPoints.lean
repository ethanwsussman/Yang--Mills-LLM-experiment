import YangMills.Construction.InfiniteLattice.CoveringPeriodicExtensionsAndTheTwoSetsOfStates
import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice.PeriodicExtensions
def SidesTendToInfinity (L : ℕ) (sides : ℕ → ℝ) : Prop :=
  (∀ i, 1 ≤ i → sides i ∈ PeriodicLattice.torusSides L) ∧
    ∀ s : ℝ, {i : ℕ | 1 ≤ i ∧ ¬ s ≤ sides i}.Finite
section Edges
variable {a : ℝ}
def firstEdge (p : ElementaryPlaquette a) : Link a := Link.forwardFrom p.corner p.lowAxis
def secondEdge (p : ElementaryPlaquette a) : Link a :=
  Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis
def thirdEdge (p : ElementaryPlaquette a) : Link a :=
  Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis
def fourthEdge (p : ElementaryPlaquette a) : Link a := Link.forwardFrom p.corner p.highAxis
theorem faceHolonomy_eq_edges (U : Link a → Matrices.ComplexMatrix2.specialUnitary)
    (p : ElementaryPlaquette a) :
    faceHolonomy U p =
      U (firstEdge p) * U (secondEdge p) * (U (thirdEdge p))⁻¹ * (U (fourthEdge p))⁻¹ :=
  rfl
variable {L m : ℕ} {j : ℤ}
def torusFirstEdge (p : PeriodicLattice.Plaquette L m j) : PeriodicLattice.Bond L m j :=
  PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis
def torusSecondEdge (p : PeriodicLattice.Plaquette L m j) : PeriodicLattice.Bond L m j :=
  PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L m j p.firstAxis)
    p.secondAxis
def torusThirdEdge (p : PeriodicLattice.Plaquette L m j) : PeriodicLattice.Bond L m j :=
  PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L m j p.secondAxis)
    p.firstAxis
def torusFourthEdge (p : PeriodicLattice.Plaquette L m j) : PeriodicLattice.Bond L m j :=
  PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis
def TorusPlaquetteHasEdgeIn (p : PeriodicLattice.Plaquette L m j)
    (S : Set (PeriodicLattice.Bond L m j)) : Prop :=
  torusFirstEdge p ∈ S ∨ torusSecondEdge p ∈ S ∨ torusThirdEdge p ∈ S ∨ torusFourthEdge p ∈ S
end Edges
section Observables
variable {a : ℝ}
theorem borel_linkVariables (S : Set (Link a)) [Countable S] :
    borel (LinkVariables S) = MeasurableSpace.pi := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact (Pi.borelSpace (ι := S) (X := fun _ => Matrices.ComplexMatrix2.specialUnitary)).measurable_eq.symm
def haarWithDensity (S : Set (Link a)) [Finite S] (q : LinkVariables S → ℝ) :
    Measure (LinkVariables S) :=
  (LinkVariables.haarMeasure S).withDensity fun V => ENNReal.ofReal (q V)
end Observables
section WeakStates
variable {a : ℝ}
def RealWeakState (a : ℝ) : Type := GaugeFieldProbability a
namespace RealWeakState
def measure (ν : RealWeakState a) : Measure (GaugeField a) := ν.1
instance (ν : RealWeakState a) : IsProbabilityMeasure ν.measure := ν.2
def value (ν : RealWeakState a) (F : GaugeField a → ℝ) : ℝ :=
  CutoffLattice.integralAgainst ν.measure F
instance weakTopology : TopologicalSpace (RealWeakState a) :=
  ⨅ F : C(GaugeField a, ℝ),
    TopologicalSpace.induced (fun ν : RealWeakState a => ν.value F) inferInstance
def TendstoWeakly (ν : ℕ → RealWeakState a) (μ : RealWeakState a) : Prop :=
  CutoffLattice.WeaklyConvergent (fun i => (ν i).measure) μ.measure
theorem tendstoWeakly_iff_tendsto (ν : ℕ → RealWeakState a) (μ : RealWeakState a) :
    TendstoWeakly ν μ ↔ Tendsto ν atTop (𝓝 μ) := by
  simp only [nhds_iInf, nhds_induced, tendsto_iInf, tendsto_comap_iff]
  rfl
end RealWeakState
end WeakStates
def IsLimitOfLiftedMeasures (L K : ℕ) (β : ℝ)
    (ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ))) : Prop :=
  ∀ N ∈ 𝓝 ν, ∀ s : ℝ, ∃ m : ℕ, 0 < m ∧ s ≤ PeriodicLattice.torusSide L m ∧
    ∃ ρ ∈ N, ρ.measure = liftedWilsonMeasure L m K β
def limitsOfLiftedMeasures (L K : ℕ) (β : ℝ) :
    Set (RealWeakState (PeriodicLattice.meshSize L (K : ℤ))) :=
  {ν | IsLimitOfLiftedMeasures L K β ν}
end InfiniteLattice.PeriodicExtensions
end YangMills.Construction
