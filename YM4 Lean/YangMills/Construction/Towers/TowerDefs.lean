import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.Towers.ObjectsUnderTheDilation
import YangMills.Construction.Towers.QuotientMapOnBonds
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (torusProj)
noncomputable section
namespace YangMills.Construction.Tower
variable {L : ℕ}
structure IsTowerPair (hL : 0 < L) (m : ℕ) {K k : ℕ} (hk : k ≤ K) : Prop where
  scaling_eq : ∀ x : Fin 4 → ℝ,
    scaling hL m K k (fun μ => (x μ : AddCircle (PeriodicLattice.torusSide L m))) =
      fun μ => ((PeriodicLattice.toLevelUnits L K k (x μ) : ℝ) :
        AddCircle (PeriodicLattice.torusSide L (scaledExponent m K k)))
  image_sublattice : ∀ j ≤ k,
    scaling hL m K k ''
        (PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth K j) :
          Set (PeriodicLattice.FourTorus L m)) =
      PeriodicLattice.sublattice L (scaledExponent m K k) (PeriodicLattice.levelDepth k j)
  image_fieldSpace : transportTotal (scaleEdge hL hk 0) ''
      PeriodicLattice.gaugeFieldsAtLevel L m K 0 = fieldSpace L (scaledExponent m K k) k 0
  wilsonAction_eq : ∀ U ∈ PeriodicLattice.gaugeFieldsAtLevel L m K 0,
    PeriodicLattice.wilsonAction U =
      plaquetteAction L (scaledExponent m K k) k (transportTotal (scaleEdge hL hk 0) U)
  preserves : 1 ≤ k → ScalingPreservesStructures hL hk m
def TowerPairs (hL : 0 < L) (k : ℕ) : Prop :=
  (∀ n m K : ℕ, 0 < n → 0 < m → 0 < K → ∀ hk : k ≤ K,
    PeriodicLattice.torusSide L m * (L : ℝ) ^ (K - k) = PeriodicLattice.torusSide L n →
      n = scaledExponent m K k ∧ IsTowerPair hL m hk) ∧
  ∀ n : ℕ, 0 < n → 1 ≤ k →
    PeriodicLattice.torusSide L n ∈ PeriodicLattice.torusSides L ∧ (∃ K : ℕ+, (K : ℕ) = k) ∧
      PeriodicLattice.torusSide L n * (L : ℝ) ^ (k - k) = PeriodicLattice.torusSide L n
def SublatticeCounts (L n k : ℕ) : Prop :=
  (∀ i j : ℕ, i ≤ j → j ≤ k →
    PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) ≤
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i)) ∧
  (∀ j ≤ k, ∀ (y : Vertex L n k j) (μ : Fin 4),
    (PeriodicLattice.axisLine y μ).ncard =
      QuotientLattices.sitesPerAxis L n k j) ∧
  (∀ i < k, ∀ (y : Vertex L n k i) (μ : Fin 4), 2 * L ^ 2 ≤ (PeriodicLattice.axisLine y μ).ncard) ∧
  ∀ i < k, ∀ c : Edge L n k (i + 1), ∀ x ∈ PeriodicLattice.bondDoubleBlock c,
    ∀ x' ∈ PeriodicLattice.bondDoubleBlock c, ∃ a b : AmbientSpace,
      torusProj (PeriodicLattice.torusSide L n) a = x ∧
        torusProj (PeriodicLattice.torusSide L n) b = x' ∧
        ∀ μ, |a μ - b μ| < 2 * (L : ℝ) * meshAt L k i
section OnTorus
variable {n : ℕ}
def MapsEdgesOnto (k i : ℕ) (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) :
    Prop :=
  (∀ b : Edge L n k i, ∃ b' : Edge L n k i,
    (b'.source : PeriodicLattice.FourTorus L n) = f b.source ∧
      (b'.target : PeriodicLattice.FourTorus L n) = f b.target) ∧
  ∀ b' : Edge L n k i, ∃ b : Edge L n k i,
    (b'.source : PeriodicLattice.FourTorus L n) = f b.source ∧
      (b'.target : PeriodicLattice.FourTorus L n) = f b.target
def MapsFacesOnto (k i : ℕ) (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) :
    Prop :=
  (∀ p : Face L n k i, ∃ p' : Face L n k i,
    Subtype.val '' p'.vertices = f '' (Subtype.val '' p.vertices)) ∧
  ∀ p' : Face L n k i, ∃ p : Face L n k i,
    Subtype.val '' p'.vertices = f '' (Subtype.val '' p.vertices)
end OnTorus
def TorusSymmetries (L n k : ℕ) : Prop :=
  ∀ j ≤ k, ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
    IsDistancePreserving f → MapsSublatticeOnto k j f →
    (∃ w ∈ InfiniteLattice.hyperoctahedralLinearGroup,
      ∃ v ∈ InfiniteLattice.latticeSubgroup (meshAt L k j),
      ∀ x : AmbientSpace,
        f (torusProj (PeriodicLattice.torusSide L n) x) =
          torusProj (PeriodicLattice.torusSide L n) (w x + v)) ∧
    ∀ i ≤ j, MapsSublatticeOnto k i f ∧ MapsEdgesOnto k i f ∧ MapsFacesOnto k i f
structure ScalingPreservesSublattices (hL : 0 < L) {k j : ℕ} (hj : j ≤ k) (n : ℕ) : Prop where
  image_sublattice : ∀ i ≤ j,
    scaling hL n k j ''
        (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
          Set (PeriodicLattice.FourTorus L n)) =
      PeriodicLattice.sublattice L (scaledExponent n k j) (PeriodicLattice.levelDepth j i)
  vertex_surjective : ∀ i ≤ j, Function.Surjective (scaleVertex (n := n) hL hj i)
  edge_surjective : ∀ i ≤ j, Function.Surjective (scaleEdge (n := n) hL hj i)
  face_surjective : ∀ i ≤ j, Function.Surjective (scaleFace (n := n) hL hj i)
  bijOn_symmetries : ∀ i ≤ j,
    BijOn (conjMap (scaling hL n k j).toEquiv)
      {f | IsDistancePreserving f ∧ MapsSublatticeOnto k i f}
      {g | IsDistancePreserving g ∧ MapsSublatticeOnto j i g}
structure ScalingPreservesAction (hL : 0 < L) {k j : ℕ} (hj : j ≤ k) (n : ℕ) : Prop where
  image_fieldSpace : transportTotal (scaleEdge hL hj 0) '' fieldSpace L n k 0 =
    fieldSpace L (scaledExponent n k j) j 0
  action_eq : ∀ U ∈ fieldSpace L n k 0,
    plaquetteAction L (scaledExponent n k j) j (transportTotal (scaleEdge hL hj 0) U) =
      plaquetteAction L n k U
structure ScalingPreservesTower (hL : 0 < L) {k j : ℕ} (hj : j ≤ k) (n : ℕ) : Prop
    extends ScalingPreservesSublattices hL hj n, ScalingPreservesAction hL hj n where
  preserves : 1 ≤ j → ScalingPreservesStructures hL hj n
namespace FullSpace
def MapsLinksOnto (a : ℝ) (f : AmbientSpace → AmbientSpace) : Prop :=
  (∀ b : InfiniteLattice.Link a, ∃ b' : InfiniteLattice.Link a,
    (b'.initial : AmbientSpace) = f b.initial ∧ (b'.terminal : AmbientSpace) = f b.terminal) ∧
  ∀ b' : InfiniteLattice.Link a, ∃ b : InfiniteLattice.Link a,
    (b'.initial : AmbientSpace) = f b.initial ∧ (b'.terminal : AmbientSpace) = f b.terminal
def MapsFacesOnto (a : ℝ) (f : AmbientSpace → AmbientSpace) : Prop :=
  (∀ p : InfiniteLattice.ElementaryPlaquette a, ∃ p' : InfiniteLattice.ElementaryPlaquette a,
    Subtype.val '' faceCorners p' = f '' (Subtype.val '' faceCorners p)) ∧
  ∀ p' : InfiniteLattice.ElementaryPlaquette a, ∃ p : InfiniteLattice.ElementaryPlaquette a,
    Subtype.val '' faceCorners p' = f '' (Subtype.val '' faceCorners p)
def SublatticesNested (L k : ℕ) : Prop :=
  ∀ i j : ℕ, i ≤ j → j ≤ k →
    InfiniteLattice.latticeSubgroup (meshAt L k j) ≤ InfiniteLattice.latticeSubgroup (meshAt L k i)
def SpaceSymmetries (L k : ℕ) : Prop :=
  ∀ j ≤ k, ∀ f : AmbientSpace → AmbientSpace, IsDistancePreserving f →
    MapsSublatticeOnto (meshAt L k j) f →
    (∃ w ∈ InfiniteLattice.hyperoctahedralLinearGroup,
      ∃ v ∈ InfiniteLattice.latticeSubgroup (meshAt L k j),
      ∀ x : AmbientSpace, f x = w x + v) ∧
    (∀ i ≤ j, MapsSublatticeOnto (meshAt L k i) f ∧ MapsLinksOnto (meshAt L k i) f ∧
      MapsFacesOnto (meshAt L k i) f) ∧
    ∀ n : ℕ, 0 < n → ∃ g : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      (∀ x : AmbientSpace,
        g (torusProj (PeriodicLattice.torusSide L n) x) =
          torusProj (PeriodicLattice.torusSide L n) (f x)) ∧
      Tower.IsDistancePreserving g ∧ Tower.MapsSublatticeOnto k j g
def cubeLinks (L : ℕ) {a : ℝ} (a' : ℝ) (y : InfiniteLattice.LatticePoint a) :
    Set (InfiniteLattice.Link a') :=
  {b | (b.initial : AmbientSpace) ∈ cube L a' y ∧ (b.terminal : AmbientSpace) ∈ cube L a' y}
variable {k j : ℕ}
structure PreservesAtLevel (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Prop where
  cubeOfOrder_image : ∀ r ≤ i, ∀ y : Vertex L k i,
    scaling hL k j '' FullSpace.cubeOfOrder L (meshAt L k (i - r)) r y =
      FullSpace.cubeOfOrder L (meshAt L j (i - r)) r (scaleVertex hL hj i y)
  axisPath_image : ∀ (x x' : Vertex L k i) (μ : Fin 4) (c : ℤ),
    IsAxisDisplacement x x' μ c →
      scalePath hL hj i (FullSpace.axisPath x x') =
        FullSpace.axisPath (scaleVertex hL hj i x) (scaleVertex hL hj i x')
structure PreservesSetsAtStep (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Prop where
  doubleCube_image : ∀ c : Edge L k (i + 1),
    scaling hL k j '' FullSpace.doubleCube L (meshAt L k i) c =
      FullSpace.doubleCube L (meshAt L j i) (scaleEdge hL hj (i + 1) c)
  linkCorridor_image : ∀ c : Edge L k (i + 1),
    scaleEdge hL hj i '' FullSpace.linkCorridor L (meshAt L k i) c =
      FullSpace.linkCorridor L (meshAt L j i) (scaleEdge hL hj (i + 1) c)
  pivotLink_eq : ∀ c : Edge L k (i + 1),
    scaleEdge hL hj i (FullSpace.pivotLink L (meshAt L k i) c) =
      FullSpace.pivotLink L (meshAt L j i) (scaleEdge hL hj (i + 1) c)
  contourSet_image : ∀ (y : Vertex L k (i + 1)) (x : Vertex L k i),
    x ∈ cubeVertices L (meshAt L k i) y →
      scalePath hL hj i '' FullSpace.contourSet L y x =
        FullSpace.contourSet L (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x)
  doubleCubeLinks_image : ∀ c : Edge L k (i + 1),
    scaleEdge hL hj i '' FullSpace.doubleCubeLinks L (meshAt L k i) c =
      FullSpace.doubleCubeLinks L (meshAt L j i) (scaleEdge hL hj (i + 1) c)
structure PreservesValuesAtStep (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Prop where
  mem_complexDomain_iff : ∀ (c : Edge L k (i + 1)) (U : Edge L k i → Matrices.ComplexMatrix2),
    U ∈ FullSpace.complexDomainNearOne L c ↔
      transportTotal (scaleEdge hL hj i) U ∈
        FullSpace.complexDomainNearOne L (scaleEdge hL hj (i + 1) c)
  contourAverage_eq : ∀ (y : Vertex L k (i + 1)) (x : Vertex L k i)
      (B : Edge L k i → Matrices.ComplexMatrix2),
    x ∈ cubeVertices L (meshAt L k i) y →
      FullSpace.contourAverage L (transportTotal (scaleEdge hL hj i) B)
          (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) =
        FullSpace.contourAverage L B y x
  linearSmoothing_eq : ∀ B : Edge L k i → Matrices.ComplexMatrix2,
    transportTotal (scaleEdge hL hj (i + 1)) (FullSpace.linearSmoothing L B) =
      FullSpace.linearSmoothing L (transportTotal (scaleEdge hL hj i) B)
  complexContourMean_eq : ∀ (y : Vertex L k (i + 1)) (x : Vertex L k i)
      (U : Edge L k i → Matrices.ComplexMatrix2), x ∈ cubeVertices L (meshAt L k i) y →
    IsFieldOn PeriodicLattice.complexGaugeGroup (cubeLinks L (meshAt L k i) y) U →
    Matrices.ComplexMatrix2.familyDiameter (contourHolonomies L U y x) <
        Averaging.centreOfMassDiameter →
      FullSpace.complexContourMean L (transportTotal (scaleEdge hL hj i) U)
          (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) =
        FullSpace.complexContourMean L U y x
  complexSmoothing_eq : ∀ (c : Edge L k (i + 1)) (U : Edge L k i → Matrices.ComplexMatrix2),
    c.IsPositivelyOriented →
    U ∈ FullSpace.complexDomainNearOne L c →
      FullSpace.complexSmoothing L (transportTotal (scaleEdge hL hj i) U)
          (scaleEdge hL hj (i + 1) c) =
        FullSpace.complexSmoothing L U c
structure PreservesAtStep (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Prop
    extends PreservesSetsAtStep hL hj i, PreservesValuesAtStep hL hj i
structure PreservesStructures (hL : 0 < L) (hj : j ≤ k) : Prop where
  atLevel : ∀ i ≤ j, PreservesAtLevel hL hj i
  atStep : ∀ i < j, PreservesAtStep hL hj i
structure ScalingPreservesSublattices (hL : 0 < L) (hj : j ≤ k) : Prop where
  image_sublattice : ∀ i ≤ j,
    scaling hL k j '' (InfiniteLattice.latticeSubgroup (meshAt L k i) : Set AmbientSpace) =
      InfiniteLattice.latticeSubgroup (meshAt L j i)
  vertex_surjective : ∀ i ≤ j, Function.Surjective (scaleVertex hL hj i)
  edge_surjective : ∀ i ≤ j, Function.Surjective (scaleEdge hL hj i)
  face_surjective : ∀ i ≤ j, Function.Surjective (scaleFace hL hj i)
  bijOn_symmetries : ∀ i ≤ j,
    BijOn (conjMap (scaling hL k j).toEquiv)
      {f | IsDistancePreserving f ∧ MapsSublatticeOnto (meshAt L k i) f}
      {g | IsDistancePreserving g ∧ MapsSublatticeOnto (meshAt L j i) g}
structure ScalingPreservesTower (hL : 0 < L) (hj : j ≤ k) : Prop
    extends FullSpace.ScalingPreservesSublattices hL hj where
  preserves : 1 ≤ j → FullSpace.PreservesStructures hL hj
def projPath (L n k i : ℕ) (Γ : List (Edge L k i)) : List (Tower.Edge L n k i) :=
  Γ.map (projEdge L n k i)
structure ProjPreservesSets (L n k i : ℕ) (c : Edge L k (i + 1)) : Prop where
  injOn_doubleCube : InjOn (torusProj (PeriodicLattice.torusSide L n)) (doubleCube L (meshAt L k i) c)
  cube_initial : torusProj (PeriodicLattice.torusSide L n) '' cube L (meshAt L k i) c.initial =
    PeriodicLattice.unitBlock (projEdge L n k (i + 1) c).source
  cube_terminal : torusProj (PeriodicLattice.torusSide L n) '' cube L (meshAt L k i) c.terminal =
    PeriodicLattice.unitBlock (projEdge L n k (i + 1) c).target
  contourSet_image : ∀ y : Vertex L k (i + 1), y = c.initial ∨ y = c.terminal →
    ∀ x ∈ cubeVertices L (meshAt L k i) y,
      projPath L n k i '' FullSpace.contourSet L y x =
        PeriodicLattice.contourSet (projVertex L n k (i + 1) y) (projVertex L n k i x)
  shifted_eq : ∀ x ∈ cubeVertices L (meshAt L k i) c.initial,
    projVertex L n k i (FullSpace.shifted c x) =
      PeriodicLattice.shiftAcross (projEdge L n k (i + 1) c) (projVertex L n k i x)
  crossingPath_eq : ∀ x ∈ cubeVertices L (meshAt L k i) c.initial,
    projPath L n k i (FullSpace.crossingPath c x) =
      PeriodicLattice.crossingPath (projEdge L n k (i + 1) c) (projVertex L n k i x)
  axisPath_eq : projPath L n k i
      (FullSpace.axisPath (toFiner (meshAt L k i) c.initial)
        (toFiner (meshAt L k i) c.terminal)) =
    PeriodicLattice.axialPath
      ((projEdge L n k (i + 1) c).source.toSublattice (PeriodicLattice.levelDepth k i))
      ((projEdge L n k (i + 1) c).target.toSublattice (PeriodicLattice.levelDepth k i))
  pivotLink_eq : projEdge L n k i (FullSpace.pivotLink L (meshAt L k i) c) =
    PeriodicLattice.pivot (projEdge L n k (i + 1) c)
  doubleCubeLinks_image : projEdge L n k i '' FullSpace.doubleCubeLinks L (meshAt L k i) c =
    PeriodicLattice.bondsInDoubleBlock (projEdge L n k (i + 1) c)
structure ProjPreservesFields (L n k i : ℕ) (c : Edge L k (i + 1)) : Prop where
  projField_spec : ∀ V : Edge L k i → Matrices.ComplexMatrix2,
    IsFieldOn PeriodicLattice.complexGaugeGroup
        (FullSpace.doubleCubeLinks L (meshAt L k i) c) V →
      (∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k i) c,
        projField L n k i (FullSpace.doubleCubeLinks L (meshAt L k i) c) V
          (projEdge L n k i b) = V b) ∧
      PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup
        (PeriodicLattice.bondsInDoubleBlock (projEdge L n k (i + 1) c))
        (projField L n k i (FullSpace.doubleCubeLinks L (meshAt L k i) c) V)
  mem_complexDomain_iff : ∀ V : Edge L k i → Matrices.ComplexMatrix2,
    IsFieldOn PeriodicLattice.complexGaugeGroup
        (FullSpace.doubleCubeLinks L (meshAt L k i) c) V →
      (V ∈ FullSpace.complexDomainNearOne L c ↔
        projField L n k i (FullSpace.doubleCubeLinks L (meshAt L k i) c) V ∈
          PeriodicLattice.complexAveragingDomainNearOne (projEdge L n k (i + 1) c))
  complexContourMean_eq : ∀ V ∈ FullSpace.complexDomainNearOne L c,
    ∀ y : Vertex L k (i + 1), y = c.initial ∨ y = c.terminal →
      ∀ x ∈ cubeVertices L (meshAt L k i) y,
        FullSpace.complexContourMean L V y x =
          PeriodicLattice.complexMeanContourHolonomy
            (projField L n k i (FullSpace.doubleCubeLinks L (meshAt L k i) c) V)
            (projVertex L n k (i + 1) y) (projVertex L n k i x)
  complexSmoothing_eq : ∀ V ∈ FullSpace.complexDomainNearOne L c,
    FullSpace.complexSmoothing L V c =
      PeriodicLattice.complexBlockAverage
        (projField L n k i (FullSpace.doubleCubeLinks L (meshAt L k i) c) V)
        (projEdge L n k (i + 1) c)
structure ProjPreservesStructures (L n k i : ℕ) (c : Edge L k (i + 1)) : Prop
    extends ProjPreservesSets L n k i c, ProjPreservesFields L n k i c
def ProjSublattices (L n k : ℕ) : Prop :=
  ∀ i ≤ k, torusProj (PeriodicLattice.torusSide L n) ''
      (InfiniteLattice.latticeSubgroup (meshAt L k i) : Set AmbientSpace) =
    PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i)
def ProjOfTower (L n k : ℕ) : Prop :=
  ProjSublattices L n k ∧
  ∀ i < k, ∀ c : Edge L k (i + 1), c.IsPositivelyOriented → ProjPreservesStructures L n k i c
end FullSpace
end YangMills.Construction.Tower
end
