import YangMills.Construction.Lattice.GaugeFieldSpacesAndRealAnalyticMaps
import YangMills.Construction.Matrices.SpecialUnitaryPowerCharts
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower.FullSpace
variable {L k j : ℕ}
def IsFinitePositiveEdgeSet (F : Finset (Edge L k j)) : Prop :=
  F.Nonempty ∧ ∀ e ∈ F, e.IsPositivelyOriented
def fieldsValuedIn (L k j : ℕ) (S : Set Matrices.ComplexMatrix2) :
    Set (Edge L k j → Matrices.ComplexMatrix2) :=
  {U | IsFieldIn S U}
def edgeProduct (S : Set Matrices.ComplexMatrix2) (F : Finset (Edge L k j)) :
    Set (F → Matrices.ComplexMatrix2) :=
  {w | ∀ e, w e ∈ S}
def restrictToEdges (F : Finset (Edge L k j)) (U : Edge L k j → Matrices.ComplexMatrix2) :
    F → Matrices.ComplexMatrix2 :=
  fun e => U e
def IsFinitelyOpen (S : Set Matrices.ComplexMatrix2)
    (D : Set (Edge L k j → Matrices.ComplexMatrix2)) : Prop :=
  D ⊆ fieldsValuedIn L k j S ∧
    ∀ U ∈ D, ∀ F : Finset (Edge L k j), IsFinitePositiveEdgeSet F →
      ∃ ε : ℝ, 0 < ε ∧ ∀ V ∈ fieldsValuedIn L k j S,
        (∀ e : Edge L k j, e.IsPositivelyOriented → e ∉ F → V e = U e) →
        (∀ e ∈ F, Matrices.ComplexMatrix2.operatorNorm (V e - U e) < ε) → V ∈ D
def IsLocalPresentation {E : Type} (S : Set Matrices.ComplexMatrix2)
    (D : Set (Edge L k j → Matrices.ComplexMatrix2))
    (h : (Edge L k j → Matrices.ComplexMatrix2) → E) (U : Edge L k j → Matrices.ComplexMatrix2)
    (F : Finset (Edge L k j)) (O : Set (F → Matrices.ComplexMatrix2))
    (f : (F → Matrices.ComplexMatrix2) → E) : Prop :=
  IsFinitePositiveEdgeSet F ∧ Matrices.ComplexMatrix2.IsRelativelyOpen (edgeProduct S F) O ∧
    restrictToEdges F U ∈ O ∧
    ∀ V ∈ D, restrictToEdges F V ∈ O → h V = f (restrictToEdges F V)
def IsFinitelyDifferentiable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set (Edge L k j → Matrices.ComplexMatrix2))
    (h : (Edge L k j → Matrices.ComplexMatrix2) → E) : Prop :=
  D ⊆ fieldSpace L k j ∧
    ∀ U ∈ D, ∃ (F : Finset (Edge L k j)) (O : Set (F → Matrices.ComplexMatrix2))
      (f : (F → Matrices.ComplexMatrix2) → E),
      IsLocalPresentation PeriodicLattice.compactGaugeGroup D h U F O f ∧
        Matrices.EmbeddedSubmanifold.DifferentiableOnOpen (Matrices.specialUnitaryPower F) O f
def IsFinitelyHolomorphic {E : Type} {n : ℕ}
    (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (φ : E ≃ Coordinates.ComplexCoordinates n) (D : Set (Edge L k j → Matrices.ComplexMatrix2))
    (h : (Edge L k j → Matrices.ComplexMatrix2) → E) : Prop :=
  D ⊆ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup ∧
    ∀ U ∈ D, ∃ (F : Finset (Edge L k j)) (O : Set (F → Matrices.ComplexMatrix2))
      (f : (F → Matrices.ComplexMatrix2) → E),
      IsLocalPresentation PeriodicLattice.complexGaugeGroup D h U F O f ∧
        Matrices.GroupLieProduct.IsHolomorphicToCoords β φ
          (Matrices.GroupLieProduct.asGroupFactors '' O) fun p => f fun e => p (.inl e)
end Tower.FullSpace
end YangMills.Construction
end
