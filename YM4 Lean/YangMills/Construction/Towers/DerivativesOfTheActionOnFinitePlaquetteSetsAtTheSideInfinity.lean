import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ActionDerivsOnFiniteFaces
open YangMills.Construction.Tower.FaceEdgeFinsets.Unbounded (facesMeeting)
variable {L k j : ℕ}
def actionAtExpTwist (Ω : Set (FullSpace.Face L k j))
    (U C : FullSpace.Edge L k j → Matrices.ComplexMatrix2) : ℂ :=
  FullSpace.faceTermSum Ω (FullSpace.expTwist C U)
def DerivsMatchFaceSum (Ω : Set (FullSpace.Face L k j))
    (U : FullSpace.Edge L k j → Matrices.ComplexMatrix2) : Prop :=
  ∀ B B' : FullSpace.Edge L k j → Matrices.ComplexMatrix2,
    B ∈ FullSpace.complexEdgeForms (meshAt L k j) → B' ∈ FullSpace.complexEdgeForms (meshAt L k j) →
    FullSpace.HasFiniteEdgeSupport B → FullSpace.HasFiniteEdgeSupport B' →
    facesMeeting (FullSpace.edgeSupport B ∪ FullSpace.edgeSupport B') ⊆ Ω →
      FullSpace.complexActionDeriv U B = directionalDeriv ℂ (actionAtExpTwist Ω U) B ∧
      FullSpace.complexActionHessian U B B' =
        mixedDirectionalDeriv ℂ (actionAtExpTwist Ω U) B B'
def IsEntireRepresentation (Ω : Set (FullSpace.Face L k j))
    (U : FullSpace.Edge L k j → Matrices.ComplexMatrix2)
    (F : Finset (FullSpace.Edge L k j)) (Φ : (F → Matrices.ComplexMatrix2) → ℂ) : Prop :=
  FullSpace.IsFinitePositiveEdgeSet F ∧ (∀ b, b ∈ F ↔ ∃ p ∈ Ω, b ∈ FullSpace.faceEdges p) ∧
    Differentiable ℂ Φ ∧
    ∀ C ∈ FullSpace.complexEdgeForms (meshAt L k j), Φ (fun b => C b) = actionAtExpTwist Ω U C
def OnLevel (L k j : ℕ) : Prop :=
  ∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
    ∀ Ω : Set (FullSpace.Face L k j), Ω.Finite → Ω.Nonempty →
      DerivsMatchFaceSum Ω U ∧
        ∃ (F : Finset (FullSpace.Edge L k j)) (Φ : (F → Matrices.ComplexMatrix2) → ℂ),
          IsEntireRepresentation Ω U F Φ
def Claim : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k → OnLevel L k j
end YangMills.Construction.Tower.FullSpace.ActionDerivsOnFiniteFaces
end
