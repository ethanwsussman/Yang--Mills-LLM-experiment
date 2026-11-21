import YangMills.Construction.Matrices.RealAnalyticMapsOnSubspacesOfProducts
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction
namespace Geometry
structure CurveData (X T : Type*) where
  IsCurve : Set ℝ → (ℝ → X) → Prop
  IsTwiceDiffCurve : Set ℝ → (ℝ → X) → Prop
  tangent : (ℝ → X) → T
namespace CurveData
variable {X T : Type*} (C : CurveData X T)
def tangentSpan [AddCommGroup T] [Module ℝ T] (N : Set X) (x : X) : Submodule ℝ T :=
  Submodule.span ℝ {v | ∃ (I : Set ℝ) (γ : ℝ → X), C.IsCurve I γ ∧ MapsTo γ I N ∧ γ 0 = x ∧
    C.tangent γ = v}
def IsCriticalOn (N : Set X) (F : X → ℝ) (x : X) : Prop :=
  x ∈ N ∧ ∀ (I : Set ℝ) (γ : ℝ → X), C.IsCurve I γ → MapsTo γ I N → γ 0 = x →
    deriv (fun t => F (γ t)) 0 = 0
def IsHessianFormAt {S : Type*} (ι : S → T) (N : Set X) (F : X → ℝ) (x : X) (Q : S → ℝ) : Prop :=
  ∀ (I : Set ℝ) (γ : ℝ → X) (v : S), C.IsTwiceDiffCurve I γ → MapsTo γ I N → γ 0 = x →
    C.tangent γ = ι v → Q v = deriv (deriv fun t => F (γ t)) 0
def hessianForm {S : Type*} [AddCommGroup S] [Module ℝ S] (ι : S → T) (N : Set X) (F : X → ℝ)
    (x : X) : QuadraticForm ℝ S :=
  Classical.epsilon fun Q : QuadraticForm ℝ S => C.IsHessianFormAt ι N F x Q
end CurveData
end Geometry
namespace Matrices.EmbeddedSubmanifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def vectorCurveData (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Geometry.CurveData E E where
  IsCurve I γ := Tower.IsOpenIntervalAroundZero I ∧ DifferentiableOn ℝ γ I
  IsTwiceDiffCurve I γ := Tower.IsOpenIntervalAroundZero I ∧
    DifferentiableOn ℝ γ I ∧ DifferentiableOn ℝ (deriv γ) I
  tangent γ := deriv γ 0
def IsChartedSubset (M : Set E) : Prop :=
  ∀ x ∈ M, ∃ (c : Chart M) (u : Fin c.dim → ℝ), u ∈ c.source ∧ c.param u = x
def IsChartedSubsetOf (N 𝒳 : Set E) : Prop := N ⊆ 𝒳 ∧ IsChartedSubset N
def IsC2OnCharted (M : Set E) (F : E → ℝ) : Prop :=
  ∀ c : Chart M, ContDiffOn ℝ 2 (c.pullback F) c.source
def IsC2Parametrization {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (N : Set E) (O : Set P) (φ : P → E) : Prop :=
  IsOpen O ∧ ContDiffOn ℝ 2 φ O ∧ InjOn φ O ∧ MapsTo φ O N ∧
    (∀ z ∈ O, Function.Injective (fderiv ℝ φ z)) ∧
    ∀ W ⊆ O, IsOpen W → ComplexMatrix2.IsRelativelyOpen N (φ '' W)
end Matrices.EmbeddedSubmanifold
namespace Tower
variable {L n k j j' : ℕ}
def fieldCurveData (L n k j : ℕ) :
    Geometry.CurveData (Edge L n k j → Matrices.ComplexMatrix2) (Edge L n k j → Matrices.ComplexMatrix2) where
  IsCurve I γ := IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ
  IsTwiceDiffCurve I γ := IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ ∧
    ∀ b : Edge L n k j, b.IsPositivelyOriented → DifferentiableOn ℝ (deriv fun t => γ t b) I
  tangent := curveTangent
def axialFunctionDomain (L n k i : ℕ) : Set (Edge L n k i → Matrices.ComplexMatrix2) :=
  {V | V ∈ fieldSpace L n k i ∧ PeriodicLattice.HasOffCenterContours k i univ V}
def contourLogDeriv (L n k i : ℕ) (V B : Edge L n k i → Matrices.ComplexMatrix2) :
    FineOnlyVertex L n k i → Matrices.ComplexMatrix2 :=
  fun x => Complex.I⁻¹ • deriv (fun t : ℝ => Matrices.ComplexMatrix2.logSeries
    (PeriodicLattice.meanContourHolonomy
      (PeriodicLattice.expTwist ((t : ℂ) • B) V) (cubeCentre x) x.1)) 0
abbrev trivialField (L n k j : ℕ) : Edge L n k j → Matrices.ComplexMatrix2 := fun _ => 1
def IsOpenNhdOfOne (𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2)) : Prop :=
  IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ∧ trivialField L n k j ∈ 𝒰
def IsAnalyticFieldFunction (𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2))
    (F : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ) : Prop :=
  IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ∧ ∃ _ : Fintype (PositiveEdge L n k j),
    Matrices.GroupLieProduct.Subspaces.IsSubspaceAnalyticToCoords (R := PositiveEdge L n k j)
      (S := Empty) (l := 1) ⊥
      {q | fieldOfPositiveValues (Matrices.GroupLieProduct.Subspaces.groupComponent q) ∈ 𝒰}
      fun q _ => (F (fieldOfPositiveValues (Matrices.GroupLieProduct.Subspaces.groupComponent q)) : ℂ)
def IsAnalyticFieldMap (𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2))
    (m : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2) : Prop :=
  IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ∧ MapsTo m 𝒰 (fieldSpace L n k j') ∧
    ∃ (_ : Fintype (PositiveEdge L n k j)) (_ : Fintype (PositiveEdge L n k j')),
      Matrices.GroupLieProduct.Subspaces.IsSubspaceAnalyticToProduct (R := PositiveEdge L n k j)
        (S := Empty) (R' := PositiveEdge L n k j') (S' := Empty) ⊥ ⊥
        {q | fieldOfPositiveValues (Matrices.GroupLieProduct.Subspaces.groupComponent q) ∈ 𝒰}
        fun q => Matrices.GroupLieProduct.Subspaces.ofParts (restrictToPositiveEdges
          (m (fieldOfPositiveValues (Matrices.GroupLieProduct.Subspaces.groupComponent q))))
          Empty.elim
def edgeFormOfPositiveValues (w : PositiveEdge L n k j → Matrices.ComplexMatrix2) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  open Classical in fun b =>
    if h : b.IsPositivelyOriented then w ⟨b, h⟩
    else if h' : b.opposite.IsPositivelyOriented then -w ⟨b.opposite, h'⟩
    else 0
def IsFieldSubmanifold (N : Set (Edge L n k j → Matrices.ComplexMatrix2)) : Prop :=
  N ⊆ fieldSpace L n k j ∧ ∃ _ : Fintype (PositiveEdge L n k j),
    Matrices.EmbeddedSubmanifold.IsChartedSubset (restrictToPositiveEdges '' N)
def IsAnalyticFieldSubmanifold (N : Set (Edge L n k j → Matrices.ComplexMatrix2)) : Prop :=
  IsFieldSubmanifold N ∧ ∃ _ : Fintype (PositiveEdge L n k j), ∀ x ∈ N,
    ∃ (𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2)) (p : Edge L n k j → Matrices.ComplexMatrix2)
      (E E' : Submodule ℝ (PositiveEdge L n k j → Matrices.ComplexMatrix2))
      (O O' : Set (PositiveEdge L n k j → Matrices.ComplexMatrix2))
      (f : (PositiveEdge L n k j → Matrices.ComplexMatrix2) → PositiveEdge L n k j → Matrices.ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ∧ x ∈ 𝒰 ∧ p ∈ fieldSpace L n k j ∧
        E ⊔ E' = Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k j) ∧
        E ⊓ E' = ⊥ ∧
        Matrices.ComplexMatrix2.IsRelativelyOpen
          (E : Set (PositiveEdge L n k j → Matrices.ComplexMatrix2)) O ∧
        Matrices.ComplexMatrix2.IsRelativelyOpen
          (E' : Set (PositiveEdge L n k j → Matrices.ComplexMatrix2)) O' ∧
        Matrices.GroupLieProduct.Subspaces.IsAnalyticOnSubspace E E' O f ∧
        ∀ U ∈ 𝒰, (∃! P : (PositiveEdge L n k j → Matrices.ComplexMatrix2) ×
              (PositiveEdge L n k j → Matrices.ComplexMatrix2),
            P.1 ∈ O ∧ P.2 ∈ O' ∧
              U = PeriodicLattice.expTwist (edgeFormOfPositiveValues (P.1 + P.2)) p) ∧
          ∀ X ∈ O, ∀ X' ∈ O', U = PeriodicLattice.expTwist (edgeFormOfPositiveValues (X + X')) p →
            (U ∈ N ↔ X' = f X)
def leftDifferentialLinear
    (m : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2)
    (U : Edge L n k j → Matrices.ComplexMatrix2) : edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j' :=
  Classical.epsilon fun T : edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j' =>
    ∀ B : edgeFormSpace L n k j, (T B : Edge L n k j' → Matrices.ComplexMatrix2) = leftDifferential m U B
end Tower
end YangMills.Construction
end
