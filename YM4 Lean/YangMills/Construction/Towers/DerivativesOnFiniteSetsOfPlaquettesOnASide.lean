import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra.FiniteFaceDerivatives
open FaceEdgeFinsets (facesMeeting)
variable {L n k j : ℕ}
def faceSetAction (Ω : Finset (Face L n k j)) (V : Edge L n k j → Matrices.ComplexMatrix2) : ℂ :=
  ∑ p ∈ Ω, complexFaceTerm V p
def faceSetEdges (Ω : Finset (Face L n k j)) : Finset (Edge L n k j) :=
  open Classical in Ω.biUnion fun p => (faceEdges p).toFinset
def faceSetCoords (Ω : Finset (Face L n k j)) (C : Edge L n k j → Matrices.ComplexMatrix2) :
    Fin 3 × faceSetEdges Ω → ℂ :=
  toPauliCoeffs fun b : faceSetEdges Ω => C b
def HasFirstAndMixedDerivAt {E : Type*} [AddCommGroup E] [Module ℂ E] (φ : E → ℂ) (x x' : E)
    (D D' : ℂ) : Prop :=
  HasDerivAt (fun t : ℂ => φ (t • x)) D 0 ∧
    HasDerivAt (fun s : ℂ => deriv (fun t : ℂ => φ (s • x + t • x')) 0) D' 0
def HoldsOnTorus (L n k j : ℕ) : Prop :=
  ∀ Ω : Finset (Face L n k j), Ω.Nonempty →
    (∀ C ∈ complexEdgeForms L n k j, ∀ C' ∈ complexEdgeForms L n k j, ∀ s t : ℂ,
      faceSetCoords Ω (s • C + t • C') =
        s • faceSetCoords Ω C + t • faceSetCoords Ω C') ∧
    ∀ U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      ∃ Φ : (Fin 3 × faceSetEdges Ω → ℂ) → ℂ, AnalyticOnNhd ℂ Φ univ ∧
        (∀ C ∈ complexEdgeForms L n k j,
          Φ (faceSetCoords Ω C) = faceSetAction Ω (PeriodicLattice.expTwist C U)) ∧
        ∀ B ∈ complexEdgeForms L n k j, ∀ B' ∈ complexEdgeForms L n k j,
          facesMeeting (edgeSupport B ∪ edgeSupport B') ⊆ (Ω : Set (Face L n k j)) →
            HasFirstAndMixedDerivAt (fun C => faceSetAction Ω (PeriodicLattice.expTwist C U)) B B'
                (complexActionDeriv U B) (complexActionHessian U B B') ∧
              HasFirstAndMixedDerivAt Φ (faceSetCoords Ω B) (faceSetCoords Ω B')
                (complexActionDeriv U B) (complexActionHessian U B B')
def ReadOnFiniteFaceSets : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k → HoldsOnTorus L n k j
end YangMills.Construction.Tower.LeftChartAlgebra.FiniteFaceDerivatives
end
