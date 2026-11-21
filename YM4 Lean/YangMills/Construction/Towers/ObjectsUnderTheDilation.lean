import YangMills.Construction.Towers.DilationOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
variable {L k j : ℕ}
structure ScalingPreservesAtLevel (hL : 0 < L) (hj : j ≤ k) (n i : ℕ) : Prop where
  refinedBlock_image : ∀ r ≤ i, ∀ y : Vertex L n k i,
    scaling hL n k j '' PeriodicLattice.refinedBlock r y =
      PeriodicLattice.refinedBlock r (scaleVertex hL hj i y)
  isAxialDisplacement_iff : ∀ (x x' : Vertex L n k i) (μ : Fin 4) (c : ℤ),
    PeriodicLattice.IsAxialDisplacement x x' μ c ↔
      PeriodicLattice.IsAxialDisplacement (scaleVertex hL hj i x)
        (scaleVertex hL hj i x') μ c
  axialPath_image : ∀ (x x' : Vertex L n k i) (μ : Fin 4) (c : ℤ),
    PeriodicLattice.IsAxialDisplacement x x' μ c →
      scalePath hL hj i (PeriodicLattice.axialPath x x') =
        PeriodicLattice.axialPath (scaleVertex hL hj i x) (scaleVertex hL hj i x')
structure ScalingPreservesAtStep (hL : 0 < L) (hj : j ≤ k) (n i : ℕ) : Prop where
  bondDoubleBlock_image : ∀ c : Edge L n k (i + 1),
    scaling hL n k j '' PeriodicLattice.bondDoubleBlock c =
      PeriodicLattice.bondDoubleBlock (scaleEdge hL hj (i + 1) c)
  doubleBlockPlaquettes_image : ∀ c : Edge L n k (i + 1),
    scaleFace hL hj i ''
        (PeriodicLattice.doubleBlockPlaquettes c : Set (Face L n k i)) =
      PeriodicLattice.doubleBlockPlaquettes (scaleEdge hL hj (i + 1) c)
  bondCorridor_image : ∀ c : Edge L n k (i + 1),
    scaleEdge hL hj i '' (PeriodicLattice.bondCorridor c : Set (Edge L n k i)) =
      PeriodicLattice.bondCorridor (scaleEdge hL hj (i + 1) c)
  pivot_image : ∀ c : Edge L n k (i + 1),
    scaleEdge hL hj i (PeriodicLattice.pivot c) =
      PeriodicLattice.pivot (scaleEdge hL hj (i + 1) c)
  contourSet_image : ∀ (y : Vertex L n k (i + 1)) (x : Vertex L n k i),
    x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
      scalePath hL hj i '' PeriodicLattice.contourSet y x =
        PeriodicLattice.contourSet (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x)
  bondsInDoubleBlock_image : ∀ c : Edge L n k (i + 1),
    scaleEdge hL hj i '' (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i)) =
      PeriodicLattice.bondsInDoubleBlock (scaleEdge hL hj (i + 1) c)
  mem_complexDomain_iff : ∀ (c : Edge L n k (i + 1)) (U : Edge L n k i → Matrices.ComplexMatrix2),
    U ∈ PeriodicLattice.complexAveragingDomainNearOne c ↔
      transportTotal (scaleEdge hL hj i) U ∈
        PeriodicLattice.complexAveragingDomainNearOne (scaleEdge hL hj (i + 1) c)
  hasContourMean_iff : ∀ (y : Vertex L n k (i + 1)) (x : Vertex L n k i)
      (U : Edge L n k i → Matrices.ComplexMatrix2),
    x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
      (PeriodicLattice.HasContourMean U y x ↔
        PeriodicLattice.HasContourMean (transportTotal (scaleEdge hL hj i) U)
          (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x))
  meanContourHolonomy_eq : ∀ (y : Vertex L n k (i + 1)) (x : Vertex L n k i)
      (U : Edge L n k i → Matrices.ComplexMatrix2),
    x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
      PeriodicLattice.HasContourMean U y x →
      PeriodicLattice.meanContourHolonomy (transportTotal (scaleEdge hL hj i) U)
          (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) =
        PeriodicLattice.meanContourHolonomy U y x
  complexMeanContourHolonomy_eq : ∀ (y : Vertex L n k (i + 1)) (x : Vertex L n k i)
      (U : Edge L n k i → Matrices.ComplexMatrix2),
    x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
      PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup
        (PeriodicLattice.blockBonds (PeriodicLattice.levelDepth k i) {y}) U →
      Matrices.ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies U y x) <
        Averaging.centreOfMassDiameter →
      PeriodicLattice.complexMeanContourHolonomy (transportTotal (scaleEdge hL hj i) U)
          (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) =
        PeriodicLattice.complexMeanContourHolonomy U y x
  contourFormAverage_eq : ∀ (y : Vertex L n k (i + 1)) (x : Vertex L n k i)
      (B : Edge L n k i → Matrices.ComplexMatrix2),
    x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y →
      PeriodicLattice.contourFormAverage (transportTotal (scaleEdge hL hj i) B)
          (scaleVertex hL hj (i + 1) y) (scaleVertex hL hj i x) =
        PeriodicLattice.contourFormAverage B y x
  linearSmoothing_eq : ∀ B : Edge L n k i → Matrices.ComplexMatrix2,
    transportTotal (scaleEdge hL hj (i + 1)) (PeriodicLattice.scaledLinearBlockStep i B) =
      Tower.linearSmoothing L (scaledExponent n k j) j i
        (transportTotal (scaleEdge hL hj i) B)
  smoothingStep_eq : ∀ V ∈ PeriodicLattice.gaugeFieldsAtLevel L n k i,
    transportTotal (scaleEdge hL hj (i + 1))
        (PeriodicLattice.blockAverageStep (Averaging.smoothingRadius L) i V) =
      Tower.smoothingStep L (scaledExponent n k j) j i
        (transportTotal (scaleEdge hL hj i) V)
  isAxialGauge_iff : ∀ V : Edge L n k i → Matrices.ComplexMatrix2,
    PeriodicLattice.IsBlockAxialGauge k i univ V ↔
      IsAxialGaugeAt L (scaledExponent n k j) j i (transportTotal (scaleEdge hL hj i) V)
  axialFunction_eq : ∀ V : Edge L n k i → Matrices.ComplexMatrix2,
    PeriodicLattice.HasOffCenterContours k i univ V →
      PeriodicLattice.axialGaugeFunction k i univ V =
        Tower.axialFunction L (scaledExponent n k j) j i
          (transportTotal (scaleEdge hL hj i) V)
structure ScalingPreservesStructures (hL : 0 < L) (hj : j ≤ k) (n : ℕ) : Prop where
  atLevel : ∀ i ≤ j, ScalingPreservesAtLevel hL hj n i
  atStep : ∀ i < j, ScalingPreservesAtStep hL hj n i
end Tower
end YangMills.Construction
end
