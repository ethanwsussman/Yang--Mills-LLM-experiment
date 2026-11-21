import YangMills.Construction.Towers.MapsOfOneStepAndTheirInputsDefs
import YangMills.Construction.Towers.MapsOfOneStepOfATower
import YangMills.Construction.Towers.SignsOfTheLinearMapsOfOneStep
import YangMills.Construction.Towers.TowerDefs
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Tower.UnitScale.OneStep (DependsOnlyOn)
noncomputable section
namespace YangMills.Construction.Tower
structure DependsOnlyWhereDefined {ι κ : Type*} (S : Set ι)
    (defined : (ι → Matrices.ComplexMatrix2) → Prop)
    (f : (ι → Matrices.ComplexMatrix2) → κ) : Prop where
  domain : DependsOnlyOn univ S defined
  value : DependsOnlyOn univ S f
namespace OneStep
section PeriodicSide
variable (L n k j : ℕ)
abbrev blockInnerEdges {L n k j : ℕ} (y : Vertex L n k (j + 1)) : Set (Edge L n k j) :=
  PeriodicLattice.bondsInside (PeriodicLattice.unitBlock y)
def facesOfFaceMean {L n k j : ℕ} (p : Face L n k (j + 1)) : Set (Face L n k j) :=
  {q | ∃ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) p.origin, ∃ s t : Fin L,
    q = ⟨x + (s : ℕ) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis +
        (t : ℕ) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.secondAxis,
      p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩}
structure VertexLocality (y : Vertex L n k (j + 1)) : Prop where
  contour : DependsOnlyOn univ (blockInnerEdges y) fun B =>
    StepMaps.stepContourAverage L n k j B y
  cube : DependsOnlyOn univ (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    fun l => StepMaps.cubeMean L n k j l y
  factor : DependsOnlyWhereDefined (blockInnerEdges y) (fun V => GaugeFactorDefinedAt V y)
    fun V => gaugeFactor V y
  holonomy : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
    DependsOnlyOn univ (blockInnerEdges y) fun V : Edge L n k j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.complexMeanContourHolonomy V y x
  axial : ∀ x : FineOnlyVertex L n k j,
    x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      DependsOnlyOn univ (blockInnerEdges y) fun B =>
        StepMaps.linearAxialFunction L n k j B x
structure EdgeLocality (c : Edge L n k (j + 1)) : Prop where
  straight : DependsOnlyOn univ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
    fun B => StepMaps.straightFormAverage L n k j B c
  linear : DependsOnlyOn univ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
    fun B => Tower.linearSmoothing L n k j B c
  complex : DependsOnlyWhereDefined (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
    (fun V => V ∈ PeriodicLattice.complexAveragingDomainNearOne c)
    fun V => PeriodicLattice.complexBlockAverageStep j V c
  straightened : DependsOnlyWhereDefined (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
    (fun V => StraightenedMeanDefinedAt V c) fun V => straightenedMean V c
  chart : DependsOnlyWhereDefined (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
    (fun B => ChartMeanDefinedAt B c) fun B => chartMean B c
  straightenedChart :
    DependsOnlyWhereDefined (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
      (fun B => StraightenedChartMeanDefinedAt B c)
      fun B => straightenedChartMean B c
structure StepLocality : Prop where
  atVertex : ∀ y, VertexLocality L n k j y
  atEdge : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented → EdgeLocality L n k j c
  atFace : ∀ p : Face L n k (j + 1),
    DependsOnlyOn univ (facesOfFaceMean p) fun F => faceMean F p
end PeriodicSide
end OneStep
namespace FullSpace.OneStep
variable (L k j : ℕ)
def facesOfFaceMean {L k j : ℕ} (p : Face L k (j + 1)) : Set (Face L k j) :=
  {q | ∃ x ∈ cubeVertices L (meshAt L k j) p.corner, ∃ s t : Fin L,
    q = ⟨x + (s : ℕ) • InfiniteLattice.axisStep (meshAt L k j) p.lowAxis +
        (t : ℕ) • InfiniteLattice.axisStep (meshAt L k j) p.highAxis,
      p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩}
structure VertexLocality (y : Vertex L k (j + 1)) : Prop where
  contour : DependsOnlyOn univ (cubeLinks L (meshAt L k j) y)
    fun B => StepMaps.stepContourAverage L k j B y
  cube : DependsOnlyOn univ (cubeVertices L (meshAt L k j) y)
    fun l => StepMaps.cubeMean L k j l y
  factor : DependsOnlyWhereDefined (cubeLinks L (meshAt L k j) y)
    (fun V => GaugeFactorDefinedAt V y) fun V => gaugeFactor V y
  holonomy : ∀ x ∈ cubeVertices L (meshAt L k j) y,
    DependsOnlyOn univ (cubeLinks L (meshAt L k j) y) fun V : Edge L k j → Matrices.ComplexMatrix2 =>
      complexContourMean L V y x
  axial : ∀ x : FineOnlyVertex (meshAt L k (j + 1)) (meshAt L k j),
    x.1 ∈ cubeVertices L (meshAt L k j) y →
      DependsOnlyOn univ (cubeLinks L (meshAt L k j) y) fun B =>
        StepMaps.linearAxialFunction L k j B x
structure EdgeLocality (c : Edge L k (j + 1)) : Prop where
  straight : DependsOnlyOn univ (doubleCubeLinks L (meshAt L k j) c)
    fun B => StepMaps.straightFormAverage L k j B c
  linear : DependsOnlyOn univ (doubleCubeLinks L (meshAt L k j) c)
    fun B : Edge L k j → Matrices.ComplexMatrix2 => FullSpace.linearSmoothing L B c
  complex : DependsOnlyWhereDefined (doubleCubeLinks L (meshAt L k j) c)
    (fun V => V ∈ complexDomainNearOne L c) fun V => complexMean L k j V c
  straightened : DependsOnlyWhereDefined (doubleCubeLinks L (meshAt L k j) c)
    (fun V => StraightenedMeanDefinedAt V c) fun V => straightenedMean V c
  chart : DependsOnlyWhereDefined (doubleCubeLinks L (meshAt L k j) c)
    (fun B => ChartMeanDefinedAt B c) fun B => chartMean B c
  straightenedChart : DependsOnlyWhereDefined (doubleCubeLinks L (meshAt L k j) c)
    (fun B => StraightenedChartMeanDefinedAt B c)
    fun B => straightenedChartMean B c
structure StepLocality : Prop where
  atVertex : ∀ y, VertexLocality L k j y
  atEdge : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented → EdgeLocality L k j c
  atFace : ∀ p : Face L k (j + 1),
    DependsOnlyOn univ (facesOfFaceMean p) fun F => faceMean F p
end FullSpace.OneStep
def StepMapsLocalityStatement : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j < k →
    (∀ n : ℕ, 0 < n → OneStep.StepLocality L n k j) ∧
      FullSpace.OneStep.StepLocality L k j
end YangMills.Construction.Tower
end
