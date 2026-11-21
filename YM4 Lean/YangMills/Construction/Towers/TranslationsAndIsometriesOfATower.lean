import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace Translations
section FiniteSide
def torusShift (L n : ℕ) (v : InfiniteLattice.AmbientSpace) :
    PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n :=
  fun z => z + TorusMetric.torusProj (PeriodicLattice.torusSide L n) v
def faceEdges {L n k i : ℕ} (p : Tower.Face L n k i) : Fin 4 → Tower.Edge L n k i :=
  ![PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis,
    PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis) p.secondAxis,
    PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis) p.firstAxis,
    PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis]
def ShiftRespectsLevels (L n k j : ℕ) (v : InfiniteLattice.AmbientSpace) : Prop :=
  (∀ x : InfiniteLattice.AmbientSpace,
    torusShift L n v (TorusMetric.torusProj (PeriodicLattice.torusSide L n) x) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L n) (x + v)) ∧
  Tower.IsDistancePreserving (torusShift L n v) ∧
  (∀ i ≤ j, Tower.MapsSublatticeOnto k i (torusShift L n v)) ∧
  Function.LeftInverse (torusShift L n (-v)) (torusShift L n v) ∧
  Function.RightInverse (torusShift L n (-v)) (torusShift L n v) ∧
  ∀ i ≤ j, ∀ x : Tower.Vertex L n k i,
    ((Tower.vertexImage (torusShift L n v) x : Tower.Vertex L n k i) :
        PeriodicLattice.FourTorus L n) = torusShift L n v x ∧
    (∀ μ : Fin 4, Tower.edgeImage (k := k) (j := i) (torusShift L n v)
        (PeriodicLattice.Bond.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (Tower.vertexImage (torusShift L n v) x) μ) ∧
    ∀ (μ ν : Fin 4) (h : μ < ν),
      Tower.vertexImage (torusShift L n v) ''
          PeriodicLattice.Plaquette.vertices (⟨x, μ, ν, h⟩ : Tower.Face L n k i) =
        PeriodicLattice.Plaquette.vertices
          (⟨Tower.vertexImage (torusShift L n v) x, μ, ν, h⟩ : Tower.Face L n k i) ∧
      ∀ r : Fin 4, Tower.edgeImage (k := k) (j := i) (torusShift L n v)
          (faceEdges (⟨x, μ, ν, h⟩ : Tower.Face L n k i) r) =
        faceEdges (⟨Tower.vertexImage (torusShift L n v) x, μ, ν, h⟩ : Tower.Face L n k i) r
def CovDiffEquivariant (L n k j : ℕ) : Prop :=
  (∀ v ∈ InfiniteLattice.latticeSubgroup (Tower.meshAt L k j),
    Tower.IsDistancePreserving (torusShift L n v) ∧
      Tower.MapsSublatticeOnto k j (torusShift L n v)) ∧
  (∀ N : Fin 4 → ℤ, PeriodicOperators.castVec N ∈
    InfiniteLattice.latticeSubgroup (Tower.meshAt L k j)) ∧
  (∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
    Tower.IsDistancePreserving f → Tower.MapsSublatticeOnto k j f →
    ∀ U ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      Tower.pushField (k := k) (j := j) f U ∈
        Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
      ∀ φ : Tower.Vertex L n k j → Matrices.ComplexMatrix2,
        (∀ x, φ x ∈ Matrices.ComplexMatrix2.traceless) →
        Tower.covDiff (Tower.pushField f U) (Tower.pushSiteFunction f φ) =
          Tower.isometryOnTangent f U (Tower.covDiff U φ)) ∧
  ∀ v ∈ InfiniteLattice.latticeSubgroup (Tower.meshAt L k j), ∀ e : Tower.Edge L n k j,
    PeriodicLattice.Bond.IsPositivelyOriented e →
    PeriodicLattice.Bond.IsPositivelyOriented
        (Tower.edgePreimage (k := k) (j := j) (torusShift L n v) e) ∧
    ∀ U ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      ∀ A ∈ Tower.complexEdgeForms L n k j,
        Tower.isometryOnTangent (torusShift L n v) U A e =
          A (Tower.edgePreimage (torusShift L n v) e)
end FiniteSide
end Translations
namespace FullSpace.Translations
def spaceShift (v : InfiniteLattice.AmbientSpace) :
    InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace := fun x => x + v
def faceEdges {a : ℝ} (p : InfiniteLattice.ElementaryPlaquette a) :
    Fin 4 → InfiniteLattice.Link a :=
  ![InfiniteLattice.Link.forwardFrom p.corner p.lowAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis) p.lowAxis,
    InfiniteLattice.Link.forwardFrom p.corner p.highAxis]
def ShiftRespectsLevels (L k j : ℕ) (v : InfiniteLattice.AmbientSpace) : Prop :=
  Tower.FullSpace.IsDistancePreserving (spaceShift v) ∧
  (∀ i ≤ j, Tower.FullSpace.MapsSublatticeOnto (Tower.meshAt L k i) (spaceShift v)) ∧
  Function.LeftInverse (spaceShift (-v)) (spaceShift v) ∧
  Function.RightInverse (spaceShift (-v)) (spaceShift v) ∧
  ∀ i ≤ j, ∀ x : Tower.FullSpace.Vertex L k i,
    ((Tower.FullSpace.vertexImage (spaceShift v) x : Tower.FullSpace.Vertex L k i) :
        InfiniteLattice.AmbientSpace) = spaceShift v x ∧
    (∀ μ : Fin 4, Tower.FullSpace.edgeImage (spaceShift v)
        (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (Tower.FullSpace.vertexImage (spaceShift v) x) μ) ∧
    ∀ (μ ν : Fin 4) (h : μ < ν),
      Tower.FullSpace.vertexImage (spaceShift v) ''
          Tower.FullSpace.faceCorners (⟨x, μ, ν, h⟩ : Tower.FullSpace.Face L k i) =
        Tower.FullSpace.faceCorners
          (⟨Tower.FullSpace.vertexImage (spaceShift v) x, μ, ν, h⟩ : Tower.FullSpace.Face L k i) ∧
      ∀ r : Fin 4, Tower.FullSpace.edgeImage (spaceShift v)
          (faceEdges (⟨x, μ, ν, h⟩ : Tower.FullSpace.Face L k i) r) =
        faceEdges
          (⟨Tower.FullSpace.vertexImage (spaceShift v) x, μ, ν, h⟩ : Tower.FullSpace.Face L k i) r
def CovDiffEquivariant (L k j : ℕ) : Prop :=
  (∀ v ∈ InfiniteLattice.latticeSubgroup (Tower.meshAt L k j),
    Tower.FullSpace.IsDistancePreserving (spaceShift v) ∧
      Tower.FullSpace.MapsSublatticeOnto (Tower.meshAt L k j) (spaceShift v)) ∧
  (∀ N : Fin 4 → ℤ, PeriodicOperators.castVec N ∈
    InfiniteLattice.latticeSubgroup (Tower.meshAt L k j)) ∧
  (∀ f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace,
    Tower.FullSpace.IsDistancePreserving f →
    Tower.FullSpace.MapsSublatticeOnto (Tower.meshAt L k j) f →
    ∀ U : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2,
      Tower.FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup U →
      Tower.FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (Tower.FullSpace.pushField f U) ∧
      ∀ φ : Tower.FullSpace.Vertex L k j → Matrices.ComplexMatrix2,
        (∀ x, φ x ∈ Matrices.ComplexMatrix2.traceless) →
        Tower.FullSpace.covDiff (Tower.FullSpace.pushField f U)
            (Tower.FullSpace.pushSiteFunction f φ) =
          Tower.FullSpace.isometryOnTangent f U (Tower.FullSpace.covDiff U φ)) ∧
  ∀ v ∈ InfiniteLattice.latticeSubgroup (Tower.meshAt L k j), ∀ e : Tower.FullSpace.Edge L k j,
    InfiniteLattice.Link.IsPositivelyOriented e →
    InfiniteLattice.Link.IsPositivelyOriented (Tower.FullSpace.edgePreimage (spaceShift v) e) ∧
    ∀ U : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2,
      Tower.FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup U →
      ∀ A ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k j),
        Tower.FullSpace.isometryOnTangent (spaceShift v) U A e =
          A (Tower.FullSpace.edgePreimage (spaceShift v) e)
def ActionPreservesColourAndAxes (L k i : ℕ) : Prop :=
  ∀ N : Fin 4 → ℤ,
    (∀ (c : Fin 3) (x : Tower.FullSpace.Vertex L k i),
      ((PeriodicOperators.colourVertices L k i).translate N (c, x) :
        Fin 3 × Tower.FullSpace.Vertex L k i).1 = c) ∧
    (∀ (c : Fin 3) (e : PeriodicOperators.PosEdge L k i) (μ : Fin 4),
      e.1.terminal - e.1.initial = InfiniteLattice.axisStep (Tower.meshAt L k i) μ →
      ((PeriodicOperators.colourEdges L k i).translate N (c, e) :
        Fin 3 × PeriodicOperators.PosEdge L k i).1 = c ∧
      ((PeriodicOperators.colourEdges L k i).translate N (c, e) :
        Fin 3 × PeriodicOperators.PosEdge L k i).2.1.terminal -
        ((PeriodicOperators.colourEdges L k i).translate N (c, e) :
          Fin 3 × PeriodicOperators.PosEdge L k i).2.1.initial =
          InfiniteLattice.axisStep (Tower.meshAt L k i) μ) ∧
    ∀ (c : Fin 3) (p : Tower.FullSpace.Face L k i),
      ((PeriodicOperators.colourFaces L k i).translate N (c, p) :
        Fin 3 × Tower.FullSpace.Face L k i).1 = c ∧
      ((PeriodicOperators.colourFaces L k i).translate N (c, p) :
        Fin 3 × Tower.FullSpace.Face L k i).2.lowAxis = p.lowAxis ∧
      ((PeriodicOperators.colourFaces L k i).translate N (c, p) :
        Fin 3 × Tower.FullSpace.Face L k i).2.highAxis = p.highAxis
end FullSpace.Translations
namespace Translations
def TranslationProperties : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    Tower.meshAt L k k = 1 ∧
    (∀ n : ℕ, 0 < n →
      (∀ v ∈ InfiniteLattice.latticeSubgroup (Tower.meshAt L k j), ShiftRespectsLevels L n k j v) ∧
      (∀ N : Fin 4 → ℤ, ShiftRespectsLevels L n k k (PeriodicOperators.castVec N)) ∧
      CovDiffEquivariant L n k j) ∧
    (∀ v ∈ InfiniteLattice.latticeSubgroup (Tower.meshAt L k j),
      Tower.FullSpace.Translations.ShiftRespectsLevels L k j v) ∧
    (∀ N : Fin 4 → ℤ,
      Tower.FullSpace.Translations.ShiftRespectsLevels L k k (PeriodicOperators.castVec N)) ∧
    Tower.FullSpace.Translations.CovDiffEquivariant L k j ∧
    ∀ i ≤ k, Tower.FullSpace.Translations.ActionPreservesColourAndAxes L k i
end Translations
end YangMills.Construction.Tower
end
