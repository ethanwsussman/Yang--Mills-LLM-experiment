import YangMills.Construction.Matrices.RealAnalyticMapsOnSubspacesOfProducts
import YangMills.Construction.OneLoopLaw.AffineMapsOfTheTorus
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace OneLoopLaw
structure AxialBranchSetting where
  params : Conventions.StandingParameters
  level : ℕ
  one_le_level : 1 ≤ level
  level_le_cutoff : level ≤ (params.K : ℕ)
namespace AxialBranchSetting
variable (D : AxialBranchSetting)
abbrev L : ℕ := D.params.L
abbrev m : ℕ := D.params.m
abbrev K : ℕ := D.params.K
abbrev Vertex (j : ℕ) : Type := Tower.Vertex D.L D.m D.K j
abbrev Edge (j : ℕ) : Type := Tower.Edge D.L D.m D.K j
abbrev Face (j : ℕ) : Type := Tower.Face D.L D.m D.K j
abbrev PositiveEdge (j : ℕ) : Type := Tower.PositiveEdge D.L D.m D.K j
abbrev fieldSpace (j : ℕ) : Set (D.Edge j → Matrices.ComplexMatrix2) :=
  Tower.fieldSpace D.L D.m D.K j
def wilsonAction : (D.Edge 0 → Matrices.ComplexMatrix2) → ℝ := Tower.plaquetteAction D.L D.m D.K
variable {D} {j : ℕ}
def oddExtension (w : D.PositiveEdge j → Matrices.ComplexMatrix2) :
    D.Edge j → Matrices.ComplexMatrix2 :=
  open Classical in fun b =>
    if h : b.IsPositivelyOriented then w ⟨b, h⟩
    else if h' : b.opposite.IsPositivelyOriented then -w ⟨b.opposite, h'⟩
    else 0
def expTwistPositive (X : D.PositiveEdge j → Matrices.ComplexMatrix2)
    (p : D.Edge j → Matrices.ComplexMatrix2) : D.Edge j → Matrices.ComplexMatrix2 :=
  PeriodicLattice.expTwist (oddExtension X) p
def IsOpenFieldSubset (U : Set (D.Edge j → Matrices.ComplexMatrix2)) : Prop :=
  Tower.IsOpenFieldSet PeriodicLattice.compactGaugeGroup U
def IsChartSubmanifold (U N : Set (D.Edge j → Matrices.ComplexMatrix2)) : Prop :=
  IsOpenFieldSubset U ∧ N ⊆ U ∧ ∃ _ : Fintype (D.PositiveEdge j), ∀ x ∈ N,
    ∃ (c : Matrices.EmbeddedSubmanifold.Chart (Matrices.specialUnitaryPower (D.PositiveEdge j)))
      (W : Submodule ℝ (Fin c.dim → ℝ)) (u : Fin c.dim → ℝ),
      u ∈ c.source ∧ c.param u = Tower.restrictToPositiveEdges x ∧
        ∀ v ∈ c.source,
          (c.param v ∈ Tower.restrictToPositiveEdges '' N ↔ v ∈ W)
def IsAnalyticSubmanifold (U N : Set (D.Edge j → Matrices.ComplexMatrix2)) : Prop :=
  IsChartSubmanifold U N ∧ ∃ _ : Fintype (D.PositiveEdge j), ∀ x ∈ N,
    ∃ (U' : Set (D.Edge j → Matrices.ComplexMatrix2)) (p : D.Edge j → Matrices.ComplexMatrix2)
      (E E' : Submodule ℝ (D.PositiveEdge j → Matrices.ComplexMatrix2))
      (O O' : Set (D.PositiveEdge j → Matrices.ComplexMatrix2))
      (f : (D.PositiveEdge j → Matrices.ComplexMatrix2) → D.PositiveEdge j → Matrices.ComplexMatrix2),
      IsOpenFieldSubset U' ∧ x ∈ U' ∧ p ∈ D.fieldSpace j ∧
        E ⊔ E' = Matrices.GroupLieProduct.hermitianTracelessFunctions (D.PositiveEdge j) ∧
        E ⊓ E' = ⊥ ∧
        Matrices.ComplexMatrix2.IsRelativelyOpen (E : Set (D.PositiveEdge j → Matrices.ComplexMatrix2)) O ∧
        Matrices.ComplexMatrix2.IsRelativelyOpen (E' : Set (D.PositiveEdge j → Matrices.ComplexMatrix2)) O' ∧
        Matrices.GroupLieProduct.Subspaces.IsAnalyticOnSubspace E E' O f ∧
        ∀ V ∈ U', (∃! P : (D.PositiveEdge j → Matrices.ComplexMatrix2) ×
              (D.PositiveEdge j → Matrices.ComplexMatrix2),
            P.1 ∈ O ∧ P.2 ∈ O' ∧ V = expTwistPositive (P.1 + P.2) p) ∧
          ∀ X ∈ O, ∀ X' ∈ O', V = expTwistPositive (X + X') p → (V ∈ N ↔ X' = f X)
def blockLift (j' : ℕ) (w : D.Vertex j → Matrices.ComplexMatrix2) :
    D.Vertex j' → Matrices.ComplexMatrix2 :=
  fun x => w (Classical.epsilon fun y : D.Vertex j =>
    (x : PeriodicLattice.FourTorus D.L D.m) ∈ PeriodicLattice.refinedBlock (j - j') y)
def IsConstantGaugeTransform (w : D.Vertex j → Matrices.ComplexMatrix2) : Prop :=
  ∀ x x', w x = w x'
def levelIsometries (D : AxialBranchSetting) (i : ℕ) (hi : i ≤ D.level) :
    Set (D.params.Torus ≃ D.params.Torus) :=
  D.params.affineTorusMaps (((D.params.K : ℕ) : ℤ) - (i : ℤ)) (by
    have h := D.level_le_cutoff
    omega)
def isometryField (s : D.params.Torus ≃ D.params.Torus) (V : D.Edge j → Matrices.ComplexMatrix2) :
    D.Edge j → Matrices.ComplexMatrix2 :=
  Tower.pushField s V
def blockingIter (D : AxialBranchSetting) (n : ℕ) :
    (D.Edge 0 → Matrices.ComplexMatrix2) → D.Edge n → Matrices.ComplexMatrix2 :=
  Tower.smoothingIter D.L D.m D.K n
def smallFaceDomain (D : AxialBranchSetting) (n : ℕ) : Set (D.Edge n → Matrices.ComplexMatrix2) :=
  {V | V ∈ D.fieldSpace n ∧ ∀ p : D.Face n,
    Matrices.ComplexMatrix2.operatorNorm (PeriodicLattice.plaquetteHolonomy V p - 1) <
      Averaging.smoothingRadius D.L}
def iteratedSmallDomain (D : AxialBranchSetting) (i : ℕ) : Set (D.Edge 0 → Matrices.ComplexMatrix2) :=
  {U | U ∈ D.fieldSpace 0 ∧ ∀ n < i, D.blockingIter n U ∈ D.smallFaceDomain n}
def axialGaugeFixing (D : AxialBranchSetting) (n : ℕ) (V : D.Edge n → Matrices.ComplexMatrix2) : ℝ :=
  Tower.axialFunction D.L D.m D.K n V
def AxialGaugeFixingDefined (D : AxialBranchSetting) (n : ℕ)
    (V : D.Edge n → Matrices.ComplexMatrix2) : Prop :=
  PeriodicLattice.HasOffCenterContours D.K n univ V
def axialGaugeFixingSum (D : AxialBranchSetting) (i : ℕ) (U : D.Edge 0 → Matrices.ComplexMatrix2) : ℝ :=
  ∑ n ∈ Finset.range i, D.axialGaugeFixing n (D.blockingIter n U)
def AxialGaugeFixingSumDefined (D : AxialBranchSetting) (i : ℕ)
    (U : D.Edge 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ n < i, D.AxialGaugeFixingDefined n (D.blockingIter n U)
def residualGaugeGroup (D : AxialBranchSetting) (i : ℕ) : Set (D.Vertex 0 → Matrices.ComplexMatrix2) :=
  {u | u ∈ Tower.gaugeGroupAt D.L D.m D.K 0 ∧
    ∀ y : D.Vertex i, u (y.toSublattice (PeriodicLattice.levelDepth D.K 0)) = 1}
def residualGaugeOrbit (D : AxialBranchSetting) (i : ℕ) (U : D.Edge 0 → Matrices.ComplexMatrix2) :
    Set (D.Edge 0 → Matrices.ComplexMatrix2) :=
  {V | ∃ u ∈ D.residualGaugeGroup i, V = PeriodicLattice.gaugeTransform u U}
def IsContDiffTwo (U : Set (D.Edge j → Matrices.ComplexMatrix2))
    (F : (D.Edge j → Matrices.ComplexMatrix2) → ℝ) : Prop :=
  IsOpenFieldSubset U ∧ ∃ _ : Fintype (D.PositiveEdge j),
    ∀ c : Matrices.EmbeddedSubmanifold.Chart (Matrices.specialUnitaryPower (D.PositiveEdge j)),
      ContDiffOn ℝ 2 (c.pullback fun w => F (Tower.fieldOfPositiveValues w))
        (c.coords (Tower.restrictToPositiveEdges '' U))
def IsCurveInto (N : Set (D.Edge j → Matrices.ComplexMatrix2)) (I : Set ℝ)
    (γ : ℝ → D.Edge j → Matrices.ComplexMatrix2) : Prop :=
  Tower.IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ ∧ MapsTo γ I N
def IsTwiceDiffCurveInto (N : Set (D.Edge j → Matrices.ComplexMatrix2)) (I : Set ℝ)
    (γ : ℝ → D.Edge j → Matrices.ComplexMatrix2) : Prop :=
  IsCurveInto N I γ ∧
    ∀ b : D.Edge j, b.IsPositivelyOriented → DifferentiableOn ℝ (deriv fun t => γ t b) I
def tangentSubspace (N : Set (D.Edge j → Matrices.ComplexMatrix2))
    (x : D.Edge j → Matrices.ComplexMatrix2) :
    Submodule ℝ (D.Edge j → Matrices.ComplexMatrix2) :=
  Submodule.span ℝ {B | ∃ (I : Set ℝ) (γ : ℝ → D.Edge j → Matrices.ComplexMatrix2),
    IsCurveInto N I γ ∧ γ 0 = x ∧ Tower.curveTangent γ = B}
def IsCriticalPointOn (N : Set (D.Edge j → Matrices.ComplexMatrix2))
    (F : (D.Edge j → Matrices.ComplexMatrix2) → ℝ) (x : D.Edge j → Matrices.ComplexMatrix2) : Prop :=
  x ∈ N ∧ ∀ (I : Set ℝ) (γ : ℝ → D.Edge j → Matrices.ComplexMatrix2), IsCurveInto N I γ → γ 0 = x →
    deriv (fun t => F (γ t)) 0 = 0
def IsHessianOn (N : Set (D.Edge j → Matrices.ComplexMatrix2))
    (F : (D.Edge j → Matrices.ComplexMatrix2) → ℝ) (x : D.Edge j → Matrices.ComplexMatrix2)
    (Q : QuadraticForm ℝ (tangentSubspace N x)) : Prop :=
  ∀ (I : Set ℝ) (γ : ℝ → D.Edge j → Matrices.ComplexMatrix2)
    (h : Tower.curveTangent γ ∈ tangentSubspace N x),
    IsTwiceDiffCurveInto N I γ → γ 0 = x →
      Q ⟨Tower.curveTangent γ, h⟩ = deriv (deriv fun t => F (γ t)) 0
def hessianOn (N : Set (D.Edge j → Matrices.ComplexMatrix2))
    (F : (D.Edge j → Matrices.ComplexMatrix2) → ℝ) (x : D.Edge j → Matrices.ComplexMatrix2) :
    QuadraticForm ℝ (tangentSubspace N x) :=
  Classical.epsilon (IsHessianOn N F x)
end AxialBranchSetting
end OneLoopLaw
end YangMills.Construction
