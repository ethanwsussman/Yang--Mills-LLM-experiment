import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FunctionsOfFiniteBondSets
import YangMills.Construction.Towers.TheFourBondsOfAPlaquette
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FaceSum
variable {E Q : Type}
def extendByOne (S : Finset E) (X : S → Matrices.ComplexMatrix2) (e : E) :
    Matrices.ComplexMatrix2 :=
  open Classical in if he : e ∈ S then X ⟨e, he⟩ else 1
def faceTerm : List Matrices.ComplexMatrix2 → ℂ
  | [A₁, A₂, A₃, A₄] =>
      1 - (1 / 2) * Matrices.ComplexMatrix2.fullTrace (A₁ * A₂ * A₃⁻¹ * A₄⁻¹)
  | _ => 0
def faceSum (edgesOf : Q → List E) (Φ : Finset Q) (w : E → Matrices.ComplexMatrix2) : ℂ :=
  ∑ q ∈ Φ, faceTerm ((edgesOf q).map w)
def faceSumOfFamily (edgesOf : Q → List E) (S : Finset E) (Φ : Finset Q)
    (X : S → Matrices.ComplexMatrix2) : ℂ :=
  faceSum edgesOf Φ (extendByOne S X)
def IsHolomorphicOnGroupPower (edgesOf : Q → List E) (S : Finset E) (Φ : Finset Q) : Prop :=
  (∀ X ∈ Matrices.GroupLieProduct.unimodularPi S, ∀ e, IsUnit (X e)) ∧
    Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct.unimodularPi S)
      (Matrices.GroupLieProduct.unimodularPi S) ∧
    ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Matrices.GroupLieProduct.IsHolomorphicToCoords β (Equiv.funUnique (Fin 1) ℂ).symm
        (Matrices.GroupLieProduct.asGroupFactors '' Matrices.GroupLieProduct.unimodularPi S)
        fun x => faceSumOfFamily edgesOf S Φ fun e => x (.inl e)
def AgreesAtField (edgesOf : Q → List E) (S : Finset E) (Φ : Finset Q)
    (V : E → Matrices.ComplexMatrix2) : Prop :=
  (fun e : S => V e) ∈ Matrices.GroupLieProduct.unimodularPi S ∧
    faceSumOfFamily edgesOf S Φ (fun e : S => V e) = faceSum edgesOf Φ V
def HoldsOnTorus (L n k j : ℕ) : Prop :=
  ∀ S : Finset (Edge L n k j), S.Nonempty → (∀ e ∈ S, e.IsPositivelyOriented) →
    ∀ Φ : Finset (Face L n k j), (∀ q ∈ Φ, ∀ e ∈ faceEdges q, e ∈ S) →
      IsHolomorphicOnGroupPower faceEdges S Φ ∧
        ∀ V : Edge L n k j → Matrices.ComplexMatrix2,
          PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ V →
            AgreesAtField faceEdges S Φ V
def HoldsOnFullSpace (L k j : ℕ) : Prop :=
  ∀ S : Finset (FullSpace.Edge L k j), FullSpace.IsFinitePositiveEdgeSet S →
    ∀ Φ : Finset (FullSpace.Face L k j), (∀ q ∈ Φ, ∀ e ∈ FullSpace.faceEdges q, e ∈ S) →
      IsHolomorphicOnGroupPower FullSpace.faceEdges S Φ ∧
        (∀ V ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
          AgreesAtField FullSpace.faceEdges S Φ V) ∧
        FullSpace.IsFinitelyOpen PeriodicLattice.complexGaugeGroup
          (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) ∧
        (∀ V ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
          FullSpace.IsLocalPresentation PeriodicLattice.complexGaugeGroup
            (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
            (faceSum FullSpace.faceEdges Φ) V S
            (FullSpace.edgeProduct PeriodicLattice.complexGaugeGroup S)
            (faceSumOfFamily FullSpace.faceEdges S Φ)) ∧
        ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
          FullSpace.IsFinitelyHolomorphic β (Equiv.funUnique (Fin 1) ℂ).symm
            (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
            (faceSum FullSpace.faceEdges Φ)
def holomorphy_statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    (∀ n : ℕ, 0 < n → HoldsOnTorus L n k j) ∧ HoldsOnFullSpace L k j
end YangMills.Construction.Tower.FaceSum
end
