import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
section FiniteSide
variable {L n k j : ℕ}
def ComplexSmoothingCovariantOnDomain (c : Edge L n k (j + 1)) : Prop :=
  ∀ V ∈ (PeriodicLattice.complexAveragingDomainNearOne c :
      Set (Edge L n k j → Matrices.ComplexMatrix2)),
    ∀ g : Vertex L n k j → Matrices.ComplexMatrix2,
      (∀ x : Vertex L n k j, (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.bondDoubleBlock c →
        g x ∈ PeriodicLattice.compactGaugeGroup) →
      PeriodicLattice.gaugeTransform g V ∈
          (PeriodicLattice.complexAveragingDomainNearOne c :
            Set (Edge L n k j → Matrices.ComplexMatrix2)) ∧
        PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform g V) c =
          g (c.source.toSublattice (PeriodicLattice.levelDepth k j)) *
            PeriodicLattice.complexBlockAverage V c *
            (g (c.target.toSublattice (PeriodicLattice.levelDepth k j)))⁻¹ ∧
        ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
          ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
            PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform g V) y x =
              g (y.toSublattice (PeriodicLattice.levelDepth k j)) *
                PeriodicLattice.complexMeanContourHolonomy V y x * (g x)⁻¹
end FiniteSide
namespace FullSpace
variable (L k j : ℕ)
def ComplexSmoothingCovariantOnDomain (c : Edge L k (j + 1)) : Prop :=
  ∀ V ∈ (complexDomainNearOne L c : Set (Edge L k j → Matrices.ComplexMatrix2)),
    ∀ g : Vertex L k j → Matrices.ComplexMatrix2,
      (∀ x : Vertex L k j, (x : InfiniteLattice.AmbientSpace) ∈ doubleCube L (meshAt L k j) c →
        g x ∈ PeriodicLattice.compactGaugeGroup) →
      gaugeAct g V ∈ (complexDomainNearOne L c : Set (Edge L k j → Matrices.ComplexMatrix2)) ∧
        complexSmoothing L (gaugeAct g V) c =
          g (toFiner (meshAt L k j) c.initial) * complexSmoothing L V c *
            (g (toFiner (meshAt L k j) c.terminal))⁻¹ ∧
        ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
          ∀ x ∈ cubeVertices L (meshAt L k j) y,
            complexContourMean L (gaugeAct g V) y x =
              g (toFiner (meshAt L k j) y) * complexContourMean L V y x * (g x)⁻¹
end FullSpace
def SmoothingCovariantOnComplexDomain.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ n k j : ℕ, 0 < n → j < k →
      SmoothingAnalyticCovariant L n k j ∧ SmoothingDerivAtOne L n k j ∧
        SmoothingEquivariant L n k j ∧
        ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented → ComplexSmoothingCovariantOnDomain c) ∧
    (∀ k j : ℕ, j < k →
      FullSpace.SmoothingAnalyticCovariant L k j ∧ FullSpace.SmoothingDerivAtOne L k j ∧
        FullSpace.SmoothingEquivariant L k j ∧
        ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
          FullSpace.ComplexSmoothingCovariantOnDomain L k j c) ∧
    IsAdmissiblePolydiscRadius L (polydiscRadius L)
end YangMills.Construction.Tower
end
