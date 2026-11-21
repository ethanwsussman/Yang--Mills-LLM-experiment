import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
section Periodic
variable {L n k j : ℕ}
def IsAnalyticMatrixValuedOn (U : Set (Edge L n k j → Matrices.ComplexMatrix2))
    (F : (Edge L n k j → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop :=
  IsOpenFieldSet PeriodicLattice.compactGaugeGroup U ∧ ∃ _ : Fintype (PositiveEdge L n k j),
    Matrices.ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : PositiveEdge L n k j => Matrices.ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => Matrices.ComplexMatrix2.FactorKind.group) (restrictToPositiveEdges '' U)
      fun v _ => F (fieldOfPositiveValues v)
def nearIdentityPolydisc (ρ : ℝ) (c : Edge L n k (j + 1)) :
    Set (Edge L n k j → Matrices.ComplexMatrix2) :=
  {V | PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup
      (PeriodicLattice.bondsInDoubleBlock c) V ∧
    ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ρ}
structure PolydiscIsAdmissible (ρ : ℝ) (c : Edge L n k (j + 1)) : Prop where
  subset_complexDomain : nearIdentityPolydisc ρ c ⊆
    (PeriodicLattice.complexAveragingDomainNearOne c : Set (Edge L n k j → Matrices.ComplexMatrix2))
  holomorphic_smoothing : PeriodicLattice.IsHolomorphicOnFields
    (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (nearIdentityPolydisc ρ c)
    fun V => PeriodicLattice.complexBlockAverage V c
  holomorphic_contourMean : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      PeriodicLattice.IsHolomorphicOnFields
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (nearIdentityPolydisc ρ c)
        fun V => PeriodicLattice.complexMeanContourHolonomy V y x
  smoothing_near_one : ∀ V ∈ nearIdentityPolydisc ρ c,
    Matrices.ComplexMatrix2.operatorNorm (PeriodicLattice.complexBlockAverage V c - 1) < 1 / 2
  contourMean_near_one : ∀ V ∈ nearIdentityPolydisc ρ c,
    ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      Matrices.ComplexMatrix2.operatorNorm (PeriodicLattice.complexMeanContourHolonomy V y x - 1)
        < 1 / 2
  gauge_covariant : ∀ V ∈ nearIdentityPolydisc ρ c, ∀ u ∈ gaugeGroupAt L n k j,
    PeriodicLattice.gaugeTransform u V ∈
        (PeriodicLattice.complexAveragingDomainNearOne c :
          Set (Edge L n k j → Matrices.ComplexMatrix2)) ∧
      PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform u V) c =
        PeriodicLattice.gaugeTransform (restrictVertexFunction (j + 1) u)
          (PeriodicLattice.complexBlockAverage V) c ∧
      ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
        ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
          PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform u V) y x =
            u (y.toSublattice (PeriodicLattice.levelDepth k j)) *
              PeriodicLattice.complexMeanContourHolonomy V y x * (u x)⁻¹
structure SmoothingAnalyticCovariant (L n k j : ℕ) : Prop where
  analytic : ∃ U : Set (Edge L n k j → Matrices.ComplexMatrix2), IsOpenNhdOfOne U ∧
    IsAnalyticFieldMap U (smoothingStep L n k j) ∧
    ∀ (y : Vertex L n k (j + 1)), ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      (∀ V ∈ U, PeriodicLattice.HasContourMean V y x) ∧
        IsAnalyticMatrixValuedOn U fun V => PeriodicLattice.meanContourHolonomy V y x
  gauge_covariant : EventuallyNearIdentity (fieldSpace L n k j) fun V =>
    ∀ u ∈ gaugeGroupAt L n k j,
      smoothingStep L n k j (PeriodicLattice.gaugeTransform u V) =
          PeriodicLattice.gaugeTransform (restrictVertexFunction (j + 1) u)
            (smoothingStep L n k j V) ∧
        ∀ (y : Vertex L n k (j + 1)),
          ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
          PeriodicLattice.meanContourHolonomy (PeriodicLattice.gaugeTransform u V) y x =
            u (y.toSublattice (PeriodicLattice.levelDepth k j)) *
              PeriodicLattice.meanContourHolonomy V y x * (u x)⁻¹
structure SmoothingDerivAtOne (L n k j : ℕ) : Prop where
  deriv_eq_linear : ∃ U : Set (Edge L n k j → Matrices.ComplexMatrix2), IsOpenNhdOfOne U ∧
    IsDifferentiableFieldMap U (smoothingStep L n k j) ∧
    ∀ B ∈ edgeFormSpace L n k j,
      leftDifferential (smoothingStep L n k j) (trivialField L n k j) B =
        linearSmoothing L n k j B
  deriv_contour : ∀ B ∈ edgeFormSpace L n k j, ∀ (y : Vertex L n k (j + 1)),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      Complex.I⁻¹ • deriv (fun t : ℝ => Matrices.ComplexMatrix2.logSeries
          (PeriodicLattice.meanContourHolonomy
            (PeriodicLattice.expTwist ((t : ℂ) • B) (trivialField L n k j)) y x)) 0 =
        PeriodicLattice.contourFormAverage B y x
def SmoothingEquivariant (L n k j : ℕ) : Prop :=
  ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsDistancePreserving f →
    MapsSublatticeOnto k (j + 1) f → EventuallyNearIdentity (fieldSpace L n k j) fun V =>
      (∀ (y : Vertex L n k (j + 1)),
        ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        PeriodicLattice.meanContourHolonomy (pushField f V) (vertexImage f y) (vertexImage f x) =
          PeriodicLattice.meanContourHolonomy V y x) ∧
      smoothingStep L n k j (pushField f V) = pushField f (smoothingStep L n k j V)
end Periodic
namespace FullSpace
section SingleLattice
variable {a : ℝ}
abbrev PositiveEdgeOf (S : Set (InfiniteLattice.Link a)) : Type :=
  {b : InfiniteLattice.Link a // b ∈ S ∧ b.IsPositivelyOriented}
def restrictPositive (S : Set (InfiniteLattice.Link a))
    (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2) :
    PositiveEdgeOf S → Matrices.ComplexMatrix2 :=
  fun b => U b.1
def extendFromPositive (S : Set (InfiniteLattice.Link a))
    (v : PositiveEdgeOf S → Matrices.ComplexMatrix2)
    (b : InfiniteLattice.Link a) : Matrices.ComplexMatrix2 :=
  open Classical in
  if h : b ∈ S ∧ b.IsPositivelyOriented then v ⟨b, h⟩
  else if h' : b.opposite ∈ S ∧ b.opposite.IsPositivelyOriented then (v ⟨b.opposite, h'⟩)⁻¹
  else 1
def IsHolomorphicOnFields (S : Set (InfiniteLattice.Link a))
    (O : Set (InfiniteLattice.Link a → Matrices.ComplexMatrix2))
    (Φ : (InfiniteLattice.Link a → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) :
    Prop :=
  (∃ _ : Fintype (PositiveEdgeOf S),
    Matrices.ComplexMatrix2.IsHolomorphicBetween
      (fun _ : PositiveEdgeOf S => Matrices.ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => Matrices.ComplexMatrix2.FactorKind.group) (restrictPositive S '' O)
      fun v _ => Φ (extendFromPositive S v)) ∧
    ∀ (N : ℕ) (ν : PositiveEdgeOf S ≃ Fin N)
      (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless),
      Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power β
        ((fun v => v ∘ ν.symm) '' (restrictPositive S '' O))
        fun X => Φ (extendFromPositive S (X ∘ ν))
end SingleLattice
section Levels
variable (L k j : ℕ)
def smoothingDomain : Set (Edge L k j → Matrices.ComplexMatrix2) :=
  {V | V ∈ fieldSpace L k j ∧ ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    V ∈ (complexDomainNearOne L c : Set (Edge L k j → Matrices.ComplexMatrix2)) ∧
      complexSmoothingPositive L V c ∈ PeriodicLattice.compactGaugeGroup}
def smoothingMap (V : Edge L k j → Matrices.ComplexMatrix2) :
    Edge L k (j + 1) → Matrices.ComplexMatrix2 :=
  complexSmoothing L V
def smoothingBall (ε : ℝ) : Set (Edge L k j → Matrices.ComplexMatrix2) :=
  {V | V ∈ smoothingDomain L k j ∧ supDistOne V < ENNReal.ofReal ε}
abbrev CubePair : Type :=
  Σ y : Vertex L k (j + 1), cubeVertices L (meshAt L k j) y
def nearIdentityPolydisc (ρ : ℝ) (c : Edge L k (j + 1)) :
    Set (Edge L k j → Matrices.ComplexMatrix2) :=
  {V | IsFieldOn PeriodicLattice.complexGaugeGroup (doubleCubeLinks L (meshAt L k j) c) V ∧
    ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ρ}
structure PolydiscIsAdmissible (ρ : ℝ) (c : Edge L k (j + 1)) : Prop where
  subset_complexDomain : nearIdentityPolydisc L k j ρ c ⊆
    (complexDomainNearOne L c : Set (Edge L k j → Matrices.ComplexMatrix2))
  holomorphic_smoothing : IsHolomorphicOnFields
    (doubleCubeLinks L (meshAt L k j) c) (nearIdentityPolydisc L k j ρ c)
    fun V => complexSmoothing L V c
  holomorphic_contourMean : ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
    ∀ x ∈ cubeVertices L (meshAt L k j) y,
      IsHolomorphicOnFields (doubleCubeLinks L (meshAt L k j) c)
        (nearIdentityPolydisc L k j ρ c) fun V => complexContourMean L V y x
  smoothing_near_one : ∀ V ∈ nearIdentityPolydisc L k j ρ c,
    Matrices.ComplexMatrix2.operatorNorm (complexSmoothing L V c - 1) < 1 / 2
  contourMean_near_one : ∀ V ∈ nearIdentityPolydisc L k j ρ c,
    ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
      ∀ x ∈ cubeVertices L (meshAt L k j) y,
        Matrices.ComplexMatrix2.operatorNorm (complexContourMean L V y x - 1) < 1 / 2
  gauge_covariant : ∀ V ∈ nearIdentityPolydisc L k j ρ c, ∀ u ∈ gaugeGroupAt L k j,
    gaugeAct u V ∈ (complexDomainNearOne L c : Set (Edge L k j → Matrices.ComplexMatrix2)) ∧
      complexSmoothing L (gaugeAct u V) c =
        gaugeAct (restrictVertexFunction (meshAt L k (j + 1)) u) (complexSmoothing L V) c ∧
      ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
        ∀ x ∈ cubeVertices L (meshAt L k j) y,
          complexContourMean L (gaugeAct u V) y x =
            u (toFiner (meshAt L k j) y) * complexContourMean L V y x * (u x)⁻¹
structure SmoothingAnalyticCovariant : Prop where
  analytic : ∃ ε : ℝ, 0 < ε ∧
    IsAnalyticMap (smoothingBall L k j ε) (smoothingMap L k j) ∧
    IsAnalyticMap (smoothingBall L k j ε)
      fun V (p : CubePair L k j) => complexContourMean L V p.1 p.2
  gauge_covariant : EventuallyNearIdentity (smoothingDomain L k j) fun V =>
    ∀ u ∈ gaugeGroupAt L k j,
      gaugeAct u V ∈ smoothingDomain L k j ∧
        smoothingMap L k j (gaugeAct u V) =
          gaugeAct (restrictVertexFunction (meshAt L k (j + 1)) u) (smoothingMap L k j V) ∧
        ∀ (y : Vertex L k (j + 1)), ∀ x ∈ cubeVertices L (meshAt L k j) y,
          complexContourMean L (gaugeAct u V) y x =
            u (toFiner (meshAt L k j) y) * complexContourMean L V y x * (u x)⁻¹
structure SmoothingDerivAtOne : Prop where
  deriv_eq_linear : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    IsDifferentiableFieldMap (smoothingBall L k j ε) (smoothingMap L k j) ∧
      ∀ B ∈ edgeFormSpace (meshAt L k j),
        leftDifferential (smoothingBall L k j ε) (smoothingMap L k j) (fun _ => 1) B =
          (linearSmoothing L B : Edge L k (j + 1) → Matrices.ComplexMatrix2)
  deriv_contour : ∀ B ∈ edgeFormSpace (meshAt L k j), ∀ (y : Vertex L k (j + 1)),
    ∀ x ∈ cubeVertices L (meshAt L k j) y,
      Complex.I⁻¹ • deriv (fun t : ℝ => Matrices.ComplexMatrix2.logSeries (complexContourMean L
          (expTwist ((t : ℂ) • B) (fun _ => 1)) y x)) 0 =
        contourAverage L B y x
def SmoothingEquivariant : Prop :=
  ∀ f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace, IsDistancePreserving f →
    MapsSublatticeOnto (meshAt L k (j + 1)) f → EventuallyNearIdentity (smoothingDomain L k j) fun V =>
      pushField f V ∈ smoothingDomain L k j ∧
        (∀ (y : Vertex L k (j + 1)), ∀ x ∈ cubeVertices L (meshAt L k j) y,
          complexContourMean L (pushField f V) (vertexImage f y) (vertexImage f x) =
            complexContourMean L V y x) ∧
        smoothingMap L k j (pushField f V) = pushField f (smoothingMap L k j V)
end Levels
end FullSpace
structure IsAdmissiblePolydiscRadius (L : ℕ) (ρ : ℝ) : Prop where
  pos : 0 < ρ
  le_one : ρ ≤ 1
  periodic : ∀ n k j : ℕ, 0 < n → j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    PolydiscIsAdmissible ρ c
  fullSpace : ∀ k j : ℕ, j < k → ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
    FullSpace.PolydiscIsAdmissible L k j ρ c
end Tower
end YangMills.Construction
end
