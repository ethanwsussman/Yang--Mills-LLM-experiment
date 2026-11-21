import YangMills.Construction.Towers.ChartAtTheTrivialConfigurationDefs
import YangMills.Construction.Towers.SignsOfTheLeftChartAndOfTheDifferentialsOfTheAverages
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open IdentityExpChart
namespace Tower
namespace OneStep
section PeriodicSide
variable {L n k j : ℕ}
def faceMean (F : Face L n k j → Matrices.ComplexMatrix2) : Face L n k (j + 1) → Matrices.ComplexMatrix2 :=
  fun p => PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) p.origin,
      ∑ s : Fin L, ∑ s' : Fin L,
        F ⟨x + (s : ℕ) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis +
            (s' : ℕ) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.secondAxis,
          p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
def gaugeFactor (V : Edge L n k j → Matrices.ComplexMatrix2) (y : Vertex L n k (j + 1)) :
    Matrices.ComplexMatrix2 :=
  Matrices.ComplexMatrix2.matExp (-(PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      Matrices.ComplexMatrix2.logSeries (PeriodicLattice.complexMeanContourHolonomy V y x)))
def straightenedMean (V : Edge L n k j → Matrices.ComplexMatrix2) (c : Edge L n k (j + 1)) :
    Matrices.ComplexMatrix2 :=
  gaugeFactor V c.source * PeriodicLattice.complexBlockAverageStep j V c *
    (gaugeFactor V c.target)⁻¹
def chartMean (B : Edge L n k j → Matrices.ComplexMatrix2) (c : Edge L n k (j + 1)) :
    Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries
    (PeriodicLattice.complexBlockAverageStep j (expForm B) c)
def straightenedChartMean (B : Edge L n k j → Matrices.ComplexMatrix2) (c : Edge L n k (j + 1)) :
    Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (straightenedMean (expForm B) c)
def GaugeFactorDefinedAt (V : Edge L n k j → Matrices.ComplexMatrix2) (y : Vertex L n k (j + 1)) : Prop :=
  ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
    PeriodicLattice.complexMeanContourHolonomy V y x ∈ Matrices.ComplexMatrix2.logBall
def StraightenedMeanDefinedAt (V : Edge L n k j → Matrices.ComplexMatrix2) (c : Edge L n k (j + 1)) : Prop :=
  V ∈ PeriodicLattice.complexAveragingDomainNearOne c ∧ GaugeFactorDefinedAt V c.source ∧
    GaugeFactorDefinedAt V c.target
def ChartMeanDefinedAt (B : Edge L n k j → Matrices.ComplexMatrix2) (c : Edge L n k (j + 1)) : Prop :=
  expForm B ∈ PeriodicLattice.complexAveragingDomainNearOne c ∧
    PeriodicLattice.complexBlockAverageStep j (expForm B) c ∈ Matrices.ComplexMatrix2.logBall
def StraightenedChartMeanDefinedAt (B : Edge L n k j → Matrices.ComplexMatrix2)
    (c : Edge L n k (j + 1)) : Prop :=
  StraightenedMeanDefinedAt (expForm B) c ∧
    straightenedMean (expForm B) c ∈ Matrices.ComplexMatrix2.logBall
end PeriodicSide
end OneStep
namespace FullSpace.OneStep
open Tower.OneStep
variable {L k j : ℕ}
def faceMean (F : Face L k j → Matrices.ComplexMatrix2) : Face L k (j + 1) → Matrices.ComplexMatrix2 :=
  fun p => PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (meshAt L k j) p.corner,
    ∑ s : Fin L, ∑ s' : Fin L,
      F ⟨x + (s : ℕ) • InfiniteLattice.axisStep (meshAt L k j) p.lowAxis +
          (s' : ℕ) • InfiniteLattice.axisStep (meshAt L k j) p.highAxis,
        p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
def gaugeFactor (V : Edge L k j → Matrices.ComplexMatrix2) (y : Vertex L k (j + 1)) :
    Matrices.ComplexMatrix2 :=
  Matrices.ComplexMatrix2.matExp (-(PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ cubeVertices L (meshAt L k j) y,
      Matrices.ComplexMatrix2.logSeries (complexContourMean L V y x)))
abbrev complexMean (L k j : ℕ) (V : Edge L k j → Matrices.ComplexMatrix2) :
    Edge L k (j + 1) → Matrices.ComplexMatrix2 :=
  complexSmoothing L V
def straightenedMean (V : Edge L k j → Matrices.ComplexMatrix2) (c : Edge L k (j + 1)) :
    Matrices.ComplexMatrix2 :=
  gaugeFactor V c.initial * complexMean L k j V c * (gaugeFactor V c.terminal)⁻¹
def chartMean (B : Edge L k j → Matrices.ComplexMatrix2) (c : Edge L k (j + 1)) :
    Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (complexMean L k j (FullSpace.expForm B) c)
def straightenedChartMean (B : Edge L k j → Matrices.ComplexMatrix2) (c : Edge L k (j + 1)) :
    Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (straightenedMean (FullSpace.expForm B) c)
def GaugeFactorDefinedAt (V : Edge L k j → Matrices.ComplexMatrix2) (y : Vertex L k (j + 1)) : Prop :=
  ∀ x ∈ cubeVertices L (meshAt L k j) y,
    complexContourMean L V y x ∈ Matrices.ComplexMatrix2.logBall
def StraightenedMeanDefinedAt (V : Edge L k j → Matrices.ComplexMatrix2) (c : Edge L k (j + 1)) : Prop :=
  V ∈ complexDomainNearOne L c ∧ GaugeFactorDefinedAt V c.initial ∧ GaugeFactorDefinedAt V c.terminal
def ChartMeanDefinedAt (B : Edge L k j → Matrices.ComplexMatrix2) (c : Edge L k (j + 1)) : Prop :=
  FullSpace.expForm B ∈ complexDomainNearOne L c ∧
    complexMean L k j (FullSpace.expForm B) c ∈ Matrices.ComplexMatrix2.logBall
def StraightenedChartMeanDefinedAt (B : Edge L k j → Matrices.ComplexMatrix2)
    (c : Edge L k (j + 1)) : Prop :=
  StraightenedMeanDefinedAt (FullSpace.expForm B) c ∧
    straightenedMean (FullSpace.expForm B) c ∈ Matrices.ComplexMatrix2.logBall
end FullSpace.OneStep
end Tower
end YangMills.Construction
end
