import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Matrices.SpecialUnitaryTwoNotation
import YangMills.Construction.Towers.TermOfTheSecondOrderAndCommutatorTerm
import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower
theorem lie_eq_mul_sub_mul (X Y : ComplexMatrix2) : ⁅X, Y⁆ = X * Y - Y * X := Ring.lie_def X Y
def halfTraceProduct (X Y : ComplexMatrix2) : ℂ :=
  ComplexMatrix2.halfTrace (ComplexMatrix2.adjointMatrix X * Y)
def IsL2Traceless {ι : Type*} (f : ι → ComplexMatrix2) : Prop :=
  (∀ i, f i ∈ ComplexMatrix2.traceless) ∧ Summable fun i => (halfTraceProduct (f i) (f i)).re
def hermitianInner {ι : Type*} (f g : ι → ComplexMatrix2) : ℂ := ∑' i, halfTraceProduct (f i) (g i)
structure IsUnitaryOnSet {α ι : Type*} [AddCommGroup α] [Module ℂ α] (S : Set α)
    (r : α → ι → ComplexMatrix2) (T : α → α) : Prop where
  bijOn : BijOn T S S
  map_add : ∀ f ∈ S, ∀ f' ∈ S, T (f + f') = T f + T f'
  map_smul : ∀ c : ℂ, ∀ f ∈ S, T (c • f) = c • T f
  inner_eq : ∀ f ∈ S, ∀ f' ∈ S,
    hermitianInner (r (T f)) (r (T f')) = hermitianInner (r f) (r f')
def HermitianSeriesAbsConv (ι : Type*) : Prop :=
  ∀ f f' : ι → ComplexMatrix2, IsL2Traceless f → IsL2Traceless f' →
    Summable fun i => ‖halfTraceProduct (f i) (f' i)‖
def logRemainder (W : ℂ → ℂ → ComplexMatrix2) (V : ComplexMatrix2) (P : ℂ → ℂ → ComplexMatrix2)
    (s t : ℂ) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (W s t * V⁻¹) - P s t
open Coordinates.ComplexCoordinates.PowerSeriesHolomorphy in
def VanishesToOrderThree (O : Set (Coordinates.ComplexCoordinates 2))
    (f : Coordinates.ComplexCoordinates 2 → Coordinates.ComplexCoordinates 4) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → closedPolydisk 0 ρ ⊆ O →
    ∀ c : (Fin 2 → ℕ) → Coordinates.ComplexCoordinates 4,
    (∀ z ∈ openPolydisk 0 ρ, HasSum (monomialTerm c 0 z) (f z)) →
      ∀ m : Fin 2 → ℕ, m 0 + m 1 < 3 → c m = 0
def HasLocalExpExpansion (W : ℂ → ℂ → ComplexMatrix2) (V : ComplexMatrix2)
    (P : ℂ → ℂ → ComplexMatrix2) : Prop :=
  ∃ O : Set (Coordinates.ComplexCoordinates 2), IsOpen O ∧
    (0 : Coordinates.ComplexCoordinates 2) ∈ O ∧
    (∀ z ∈ O, W (z 0) (z 1) * V⁻¹ ∈ ComplexMatrix2.logBall ∧
      W (z 0) (z 1) =
        ComplexMatrix2.matExp (Complex.I • (P (z 0) (z 1) + logRemainder W V P (z 0) (z 1))) * V ∧
      logRemainder W V P (z 0) (z 1) ∈ ComplexMatrix2.traceless) ∧
    Coordinates.ComplexCoordinates.IsHolomorphicIn O
      (fun z => Coordinates.ComplexCoordinates.matrixEquiv (logRemainder W V P (z 0) (z 1))) ∧
    VanishesToOrderThree O
      (fun z => Coordinates.ComplexCoordinates.matrixEquiv (logRemainder W V P (z 0) (z 1)))
section FiniteSide
variable {L n k j : ℕ}
def levelBracketTerm (U : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2)
    (B : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  extendOddly fun b =>
    (Complex.I / 2) • ⁅l b.source + ComplexMatrix2.conjugateBy (U b) (l b.target), B b⁆
theorem levelBracketTerm_zero (U : Edge L n k 0 → ComplexMatrix2)
    (l : Vertex L n k 0 → ComplexMatrix2) (B : Edge L n k 0 → ComplexMatrix2) :
    levelBracketTerm U l B = bracketTerm U l B := rfl
def gaugeQuadTerm (U : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2)
    (b : Edge L n k j) : ComplexMatrix2 :=
  -((Complex.I / 2) • ⁅l b.source, ComplexMatrix2.conjugateBy (U b) (l b.target)⁆)
def vertexExp (l : Vertex L n k j → ComplexMatrix2) : Vertex L n k j → ComplexMatrix2 :=
  fun x => ComplexMatrix2.matExp (Complex.I • l x)
def twistedField (U : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2)
    (B : Edge L n k j → ComplexMatrix2) (s t : ℂ) : Edge L n k j → ComplexMatrix2 :=
  PeriodicLattice.gaugeTransform (vertexExp (t • l)) (PeriodicLattice.expTwist (s • B) U)
def principalExponent (U : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2)
    (B : Edge L n k j → ComplexMatrix2) (s t : ℂ) (b : Edge L n k j) : ComplexMatrix2 :=
  s • B b - t • covDiff U l b + (s * t) • levelBracketTerm U l B b +
    t ^ 2 • gaugeQuadTerm U l b
def expansionRemainder (U : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2)
    (B : Edge L n k j → ComplexMatrix2) (s t : ℂ) (b : Edge L n k j) : ComplexMatrix2 :=
  logRemainder (fun s t => twistedField U l B s t b) (U b)
    (fun s t => principalExponent U l B s t b) s t
def l2Forms (L n k j : ℕ) : Set (Edge L n k j → ComplexMatrix2) :=
  {B | B ∈ complexEdgeForms L n k j ∧ IsL2Traceless (restrictToPositiveEdges B)}
def IsImageFace (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (p p' : Face L n k j) : Prop :=
  Subtype.val '' p'.vertices = f '' (Subtype.val '' p.vertices)
end FiniteSide
namespace FullSpace
section OneLattice
variable {a : ℝ}
def levelBracketTerm (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) : InfiniteLattice.Link a → ComplexMatrix2 :=
  extendOddly fun b =>
    (Complex.I / 2) • ⁅l b.initial + ComplexMatrix2.conjugateBy (U b) (l b.terminal), B b⁆
def gaugeQuadTerm (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) (b : InfiniteLattice.Link a) :
    ComplexMatrix2 :=
  -((Complex.I / 2) • ⁅l b.initial, ComplexMatrix2.conjugateBy (U b) (l b.terminal)⁆)
def vertexExp (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    InfiniteLattice.LatticePoint a → ComplexMatrix2 :=
  fun x => ComplexMatrix2.matExp (Complex.I • l x)
def twistedField (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) (s t : ℂ) :
    InfiniteLattice.Link a → ComplexMatrix2 :=
  gaugeAct (vertexExp (t • l)) (expTwist (s • B) U)
def principalExponent (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) (s t : ℂ) (b : InfiniteLattice.Link a) :
    ComplexMatrix2 :=
  s • B b - t • covDiff U l b + (s * t) • levelBracketTerm U l B b +
    t ^ 2 • gaugeQuadTerm U l b
def expansionRemainder (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) (s t : ℂ) (b : InfiniteLattice.Link a) :
    ComplexMatrix2 :=
  logRemainder (fun s t => twistedField U l B s t b) (U b)
    (fun s t => principalExponent U l B s t b) s t
def l2Forms (a : ℝ) : Set (InfiniteLattice.Link a → ComplexMatrix2) :=
  {B | B ∈ complexEdgeForms a ∧ IsL2Traceless (restrictToPositiveEdges B)}
def IsImageFace (f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace)
    (p p' : InfiniteLattice.ElementaryPlaquette a) : Prop :=
  Subtype.val '' faceCorners p' = f '' (Subtype.val '' faceCorners p)
end OneLattice
end FullSpace
namespace LeftChartAlgebra
def InvTraceIdentity : Prop :=
  (∀ g ∈ PeriodicLattice.complexGaugeGroup,
    g⁻¹ = ComplexMatrix2.fullTrace g • (1 : ComplexMatrix2) - g ∧
      ComplexMatrix2.fullTrace g⁻¹ = ComplexMatrix2.fullTrace g) ∧
  ∀ g ∈ PeriodicLattice.compactGaugeGroup, (ComplexMatrix2.fullTrace g).im = 0
def HalfTraceInPauliCoords : Prop :=
  ∀ (X Y : ComplexMatrix2.traceless) (x y : Fin 3 → ℂ),
    (X : ComplexMatrix2) = ∑ c, x c • ComplexMatrix2.pauliFamily c →
    (Y : ComplexMatrix2) = ∑ c, y c • ComplexMatrix2.pauliFamily c →
      halfTraceProduct X Y = ∑ c, star (x c) * y c
section FiniteSide
def ActionAsFaceSum (L n k j : ℕ) : Prop :=
  ∀ U ∈ fieldSpace L n k j,
    complexAction U =
      ((∑ᶠ p : Face L n k j, PeriodicLattice.plaquetteCost U p : ℝ) : ℂ)
def ActionAsFaceSumBase (L n k : ℕ) : Prop :=
  ∀ U ∈ fieldSpace L n k 0, complexAction U = ((plaquetteAction L n k U : ℝ) : ℂ)
def GaugeCovariance (L n k j : ℕ) : Prop :=
  ∀ (U : Edge L n k j → ComplexMatrix2) (u : Vertex L n k j → ComplexMatrix2),
    U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
    PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup u →
      (∀ l : Vertex L n k j → ComplexMatrix2,
        PeriodicLattice.IsSiteField PeriodicLattice.complexLieAlgebra l →
        covDiff (PeriodicLattice.gaugeTransform u U) (adjointVertexFn u l) =
          adjointForm u (covDiff U l)) ∧
      ∀ p : Face L n k j,
        PeriodicLattice.plaquetteHolonomy (PeriodicLattice.gaugeTransform u U) p =
          u p.origin * PeriodicLattice.plaquetteHolonomy U p * (u p.origin)⁻¹ ∧
        complexFaceTerm (PeriodicLattice.gaugeTransform u U) p = complexFaceTerm U p
def GaugeUnitarity (L n k j : ℕ) : Prop :=
  HermitianSeriesAbsConv (PositiveEdge L n k j) ∧ HermitianSeriesAbsConv (Vertex L n k j) ∧
  ∀ u ∈ gaugeGroupAt L n k j,
    (∀ B ∈ edgeFormSpace L n k j, adjointForm u B ∈ edgeFormSpace L n k j) ∧
    (∀ l ∈ vertexFunctionSpace L n k j, adjointVertexFn u l ∈ vertexFunctionSpace L n k j) ∧
    IsUnitaryOnSet (l2Forms L n k j) restrictToPositiveEdges (adjointForm u) ∧
    IsUnitaryOnSet {l : Vertex L n k j → ComplexMatrix2 | IsL2Traceless l} id (adjointVertexFn u)
def TwistExpansion (L n k j : ℕ) : Prop :=
  ∀ (U : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2)
    (B : Edge L n k j → ComplexMatrix2),
    U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
    PeriodicLattice.IsSiteField PeriodicLattice.complexLieAlgebra l →
    B ∈ complexEdgeForms L n k j →
      (∀ s : ℂ, PeriodicLattice.expTwist (s • B) U ∈
        fieldsIn L n k j PeriodicLattice.complexGaugeGroup) ∧
      (∀ t : ℂ, PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup
        (vertexExp (t • l))) ∧
      ∀ b : Edge L n k j, b.IsPositivelyOriented →
        HasLocalExpExpansion (fun s t => twistedField U l B s t b) (U b)
          (fun s t => principalExponent U l B s t b)
def DerivativeIdentities (L n k j : ℕ) : Prop :=
  ∀ (U : Edge L n k j → ComplexMatrix2) (u l : Vertex L n k j → ComplexMatrix2)
    (B B' : Edge L n k j → ComplexMatrix2),
    U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
    PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup u →
    PeriodicLattice.IsSiteField PeriodicLattice.complexLieAlgebra l →
    B ∈ complexEdgeForms L n k j → B' ∈ complexEdgeForms L n k j →
      complexActionDeriv (PeriodicLattice.gaugeTransform u U) (adjointForm u B) =
        complexActionDeriv U B ∧
      complexActionHessian (PeriodicLattice.gaugeTransform u U) (adjointForm u B)
          (adjointForm u B') = complexActionHessian U B B' ∧
      ((¬ ∃ p : Face L n k j, (∃ b ∈ edgeSupport B, b ∈ faceEdges p) ∧
          ∃ b ∈ edgeSupport B', b ∈ faceEdges p) →
        complexActionHessian U B B' = 0) ∧
      complexActionHessian U B (covDiff U l) =
        complexActionDeriv U (levelBracketTerm U l B)
def SymmetryCovariance (L n k j : ℕ) : Prop :=
  ∀ (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (U : Edge L n k j → ComplexMatrix2),
    IsDistancePreserving f → MapsSublatticeOnto k j f →
    U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
      (∀ B ∈ complexEdgeForms L n k j,
        PeriodicLattice.expTwist (isometryOnTangent f U B) (pushField (k := k) (j := j) f U) =
          pushField (k := k) (j := j) f (PeriodicLattice.expTwist B U)) ∧
      (∀ p : Face L n k j, (∃! p' : Face L n k j, IsImageFace f p p') ∧
        ∀ p' : Face L n k j, IsImageFace f p p' →
          complexFaceTerm (pushField (k := k) (j := j) f U) p' = complexFaceTerm U p) ∧
      (∀ B ∈ complexEdgeForms L n k j, ∀ B' ∈ complexEdgeForms L n k j,
        edgeFormPairing (isometryOnTangent f U B) (isometryOnTangent f U B') =
          edgeFormPairing B B' ∧
        complexActionHessian (pushField (k := k) (j := j) f U)
            (isometryOnTangent f U B) (isometryOnTangent f U B') =
          complexActionHessian U B B')
def OnPeriodic (L n k j : ℕ) : Prop :=
  ActionAsFaceSum L n k j ∧ GaugeCovariance L n k j ∧ GaugeUnitarity L n k j ∧
    TwistExpansion L n k j ∧ DerivativeIdentities L n k j ∧ SymmetryCovariance L n k j
end FiniteSide
end LeftChartAlgebra
namespace FullSpace
namespace LeftChartAlgebra
def GaugeCovariance (L k j : ℕ) : Prop :=
  ∀ (U : Edge L k j → ComplexMatrix2) (u : Vertex L k j → ComplexMatrix2),
    U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
    (∀ x, u x ∈ PeriodicLattice.complexGaugeGroup) →
      (∀ l : Vertex L k j → ComplexMatrix2, (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) →
        covDiff (gaugeAct u U) (adjointVertexFn u l) = adjointForm u (covDiff U l)) ∧
      ∀ p : Face L k j,
        faceVariable (gaugeAct u U) p = u p.corner * faceVariable U p * (u p.corner)⁻¹ ∧
        complexFaceTerm (gaugeAct u U) p = complexFaceTerm U p
def GaugeUnitarity (L k j : ℕ) : Prop :=
  HermitianSeriesAbsConv (PositiveEdge (meshAt L k j)) ∧
  HermitianSeriesAbsConv (Vertex L k j) ∧
  ∀ u ∈ gaugeGroupAt L k j,
    (∀ B ∈ edgeFormSpace (meshAt L k j), adjointForm u B ∈ edgeFormSpace (meshAt L k j)) ∧
    (∀ l ∈ vertexFunctionSpace (meshAt L k j),
      adjointVertexFn u l ∈ vertexFunctionSpace (meshAt L k j)) ∧
    IsUnitaryOnSet (l2Forms (meshAt L k j)) restrictToPositiveEdges (adjointForm u) ∧
    IsUnitaryOnSet {l : Vertex L k j → ComplexMatrix2 | IsL2Traceless l} id (adjointVertexFn u)
def TwistExpansion (L k j : ℕ) : Prop :=
  ∀ (U : Edge L k j → ComplexMatrix2) (l : Vertex L k j → ComplexMatrix2)
    (B : Edge L k j → ComplexMatrix2),
    U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
    (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) → B ∈ complexEdgeForms (meshAt L k j) →
      (∀ s : ℂ, expTwist (s • B) U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) ∧
      (∀ t : ℂ, ∀ x, vertexExp (t • l) x ∈ PeriodicLattice.complexGaugeGroup) ∧
      ∀ b : Edge L k j, b.IsPositivelyOriented →
        HasLocalExpExpansion (fun s t => twistedField U l B s t b) (U b)
          (fun s t => principalExponent U l B s t b)
def DerivativeIdentities (L k j : ℕ) : Prop :=
  ∀ (U : Edge L k j → ComplexMatrix2) (u l : Vertex L k j → ComplexMatrix2)
    (B B' : Edge L k j → ComplexMatrix2),
    U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
    (∀ x, u x ∈ PeriodicLattice.complexGaugeGroup) →
    (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) →
    HasFiniteSupp l →
    B ∈ complexEdgeForms (meshAt L k j) → B' ∈ complexEdgeForms (meshAt L k j) →
    HasFiniteEdgeSupport B → HasFiniteEdgeSupport B' →
      complexActionDeriv (gaugeAct u U) (adjointForm u B) = complexActionDeriv U B ∧
      complexActionHessian (gaugeAct u U) (adjointForm u B) (adjointForm u B') =
        complexActionHessian U B B' ∧
      ((¬ ∃ p : Face L k j, (∃ b ∈ edgeSupport B, b ∈ faceEdges p) ∧
          ∃ b ∈ edgeSupport B', b ∈ faceEdges p) →
        complexActionHessian U B B' = 0) ∧
      complexActionHessian U B (covDiff U l) = complexActionDeriv U (levelBracketTerm U l B)
def SymmetryCovariance (L k j : ℕ) : Prop :=
  ∀ (f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace)
    (U : Edge L k j → ComplexMatrix2),
    IsDistancePreserving f → MapsSublatticeOnto (meshAt L k j) f →
    U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
      (∀ B ∈ complexEdgeForms (meshAt L k j),
        expTwist (isometryOnTangent f U B) (pushField f U) = pushField f (expTwist B U)) ∧
      (∀ p : Face L k j, (∃! p' : Face L k j, IsImageFace f p p') ∧
        ∀ p' : Face L k j, IsImageFace f p p' →
          complexFaceTerm (pushField f U) p' = complexFaceTerm U p) ∧
      (∀ B ∈ complexEdgeForms (meshAt L k j), ∀ B' ∈ complexEdgeForms (meshAt L k j),
        (HasFiniteSupp (restrictToPositiveEdges B) ∨ HasFiniteSupp (restrictToPositiveEdges B') →
          finiteEdgePairing (isometryOnTangent f U B) (isometryOnTangent f U B') =
            finiteEdgePairing B B') ∧
        (HasFiniteEdgeSupport B → HasFiniteEdgeSupport B' →
          complexActionHessian (pushField f U)
              (isometryOnTangent f U B) (isometryOnTangent f U B') =
            complexActionHessian U B B'))
end LeftChartAlgebra
end FullSpace
namespace LeftChartAlgebra
def OnFull (L k j : ℕ) : Prop :=
  FullSpace.LeftChartAlgebra.GaugeCovariance L k j ∧
    FullSpace.LeftChartAlgebra.GaugeUnitarity L k j ∧
    FullSpace.LeftChartAlgebra.TwistExpansion L k j ∧
    FullSpace.LeftChartAlgebra.DerivativeIdentities L k j ∧
    FullSpace.LeftChartAlgebra.SymmetryCovariance L k j
def DerivativeCovariance (L n k j : ℕ) : Prop :=
  ∀ (U : Edge L n k j → ComplexMatrix2) (u : Vertex L n k j → ComplexMatrix2)
    (B B' : Edge L n k j → ComplexMatrix2),
    U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
    PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup u →
    B ∈ complexEdgeForms L n k j → B' ∈ complexEdgeForms L n k j →
      complexActionDeriv (PeriodicLattice.gaugeTransform u U) (adjointForm u B) =
        complexActionDeriv U B ∧
      complexActionHessian (PeriodicLattice.gaugeTransform u U) (adjointForm u B)
          (adjointForm u B') = complexActionHessian U B B'
def HessianDisjointVanish (L n k j : ℕ) : Prop :=
  ∀ (U : Edge L n k j → ComplexMatrix2) (B B' : Edge L n k j → ComplexMatrix2),
    U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
    B ∈ complexEdgeForms L n k j → B' ∈ complexEdgeForms L n k j →
      (¬ ∃ p : Face L n k j, (∃ b ∈ edgeSupport B, b ∈ faceEdges p) ∧
          ∃ b ∈ edgeSupport B', b ∈ faceEdges p) →
        complexActionHessian U B B' = 0
def HessianGaugeDirection (L n k j : ℕ) : Prop :=
  ∀ (U : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2)
    (B : Edge L n k j → ComplexMatrix2),
    U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
    PeriodicLattice.IsSiteField PeriodicLattice.complexLieAlgebra l →
    B ∈ complexEdgeForms L n k j →
      complexActionHessian U B (covDiff U l) = complexActionDeriv U (levelBracketTerm U l B)
def SymmetryExpFace (L n k j : ℕ) : Prop :=
  ∀ (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (U : Edge L n k j → ComplexMatrix2),
    IsDistancePreserving f → MapsSublatticeOnto k j f →
    U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
      (∀ B ∈ complexEdgeForms L n k j,
        PeriodicLattice.expTwist (isometryOnTangent f U B) (pushField (k := k) (j := j) f U) =
          pushField (k := k) (j := j) f (PeriodicLattice.expTwist B U)) ∧
      (∀ p : Face L n k j, (∃! p' : Face L n k j, IsImageFace f p p') ∧
        ∀ p' : Face L n k j, IsImageFace f p p' →
          complexFaceTerm (pushField (k := k) (j := j) f U) p' = complexFaceTerm U p)
def SymmetryPairingHessian (L n k j : ℕ) : Prop :=
  ∀ (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (U : Edge L n k j → ComplexMatrix2),
    IsDistancePreserving f → MapsSublatticeOnto k j f →
    U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup →
      ∀ B ∈ complexEdgeForms L n k j, ∀ B' ∈ complexEdgeForms L n k j,
        edgeFormPairing (isometryOnTangent f U B) (isometryOnTangent f U B') =
          edgeFormPairing B B' ∧
        complexActionHessian (pushField (k := k) (j := j) f U)
            (isometryOnTangent f U B) (isometryOnTangent f U B') =
          complexActionHessian U B B'
end LeftChartAlgebra
namespace FullSpace
namespace LeftChartAlgebra
def DerivativeCovariance (L k j : ℕ) : Prop :=
  ∀ (U : Edge L k j → ComplexMatrix2) (u : Vertex L k j → ComplexMatrix2)
    (B B' : Edge L k j → ComplexMatrix2),
    U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
    (∀ x, u x ∈ PeriodicLattice.complexGaugeGroup) →
    B ∈ complexEdgeForms (meshAt L k j) → B' ∈ complexEdgeForms (meshAt L k j) →
    HasFiniteEdgeSupport B → HasFiniteEdgeSupport B' →
      complexActionDeriv (gaugeAct u U) (adjointForm u B) = complexActionDeriv U B ∧
      complexActionHessian (gaugeAct u U) (adjointForm u B) (adjointForm u B') =
        complexActionHessian U B B'
def HessianDisjointVanish (L k j : ℕ) : Prop :=
  ∀ (U : Edge L k j → ComplexMatrix2) (B B' : Edge L k j → ComplexMatrix2),
    U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
    B ∈ complexEdgeForms (meshAt L k j) → B' ∈ complexEdgeForms (meshAt L k j) →
    HasFiniteEdgeSupport B → HasFiniteEdgeSupport B' →
      (¬ ∃ p : Face L k j, (∃ b ∈ edgeSupport B, b ∈ faceEdges p) ∧
          ∃ b ∈ edgeSupport B', b ∈ faceEdges p) →
        complexActionHessian U B B' = 0
def HessianGaugeDirection (L k j : ℕ) : Prop :=
  ∀ (U : Edge L k j → ComplexMatrix2) (l : Vertex L k j → ComplexMatrix2)
    (B : Edge L k j → ComplexMatrix2),
    U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
    (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) → HasFiniteSupp l →
    B ∈ complexEdgeForms (meshAt L k j) → HasFiniteEdgeSupport B →
      complexActionHessian U B (covDiff U l) = complexActionDeriv U (levelBracketTerm U l B)
def SymmetryExpFace (L k j : ℕ) : Prop :=
  ∀ (f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace)
    (U : Edge L k j → ComplexMatrix2),
    IsDistancePreserving f → MapsSublatticeOnto (meshAt L k j) f →
    U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
      (∀ B ∈ complexEdgeForms (meshAt L k j),
        expTwist (isometryOnTangent f U B) (pushField f U) = pushField f (expTwist B U)) ∧
      (∀ p : Face L k j, (∃! p' : Face L k j, IsImageFace f p p') ∧
        ∀ p' : Face L k j, IsImageFace f p p' →
          complexFaceTerm (pushField f U) p' = complexFaceTerm U p)
def SymmetryPairingHessian (L k j : ℕ) : Prop :=
  ∀ (f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace)
    (U : Edge L k j → ComplexMatrix2),
    IsDistancePreserving f → MapsSublatticeOnto (meshAt L k j) f →
    U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
      ∀ B ∈ complexEdgeForms (meshAt L k j), ∀ B' ∈ complexEdgeForms (meshAt L k j),
        (HasFiniteSupp (restrictToPositiveEdges B) ∨ HasFiniteSupp (restrictToPositiveEdges B') →
          finiteEdgePairing (isometryOnTangent f U B) (isometryOnTangent f U B') =
            finiteEdgePairing B B') ∧
        (HasFiniteEdgeSupport B → HasFiniteEdgeSupport B' →
          complexActionHessian (pushField f U)
              (isometryOnTangent f U B) (isometryOnTangent f U B') =
            complexActionHessian U B B')
end LeftChartAlgebra
end FullSpace
end Tower
end YangMills.Construction
end
