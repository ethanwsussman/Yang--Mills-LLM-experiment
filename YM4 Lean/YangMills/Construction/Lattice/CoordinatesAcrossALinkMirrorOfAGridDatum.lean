import YangMills.Construction.Lattice.SidesOfALinkMirrorOfAGridDatum
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.GridMirror
open BoxTorus TorusDescent Matrices Conventions
def MirrorCoordinates : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (d : CellGrid L κ) (g : d.GridSymmetry) (μ : Fin 4) (c : ℝ),
    IsMirrorReflection g μ c →
      ∃ ι : (HalfEdge d (posHalf d μ c) → StandingParameters.gaugeGroup) ×
          (HalfEdge d (posHalf d μ c) → StandingParameters.gaugeGroup) ×
          (MirrorPairedPoint g (posHalf d μ c) → StandingParameters.gaugeGroup) → d.GaugeConfig,
        Measurable ι ∧
        Measure.map ι ((ComplexMatrix2.haarPi _).prod
            ((ComplexMatrix2.haarPi _).prod (ComplexMatrix2.haarPi _))) =
          haarConfigMeasure L κ d.sideLengths ∧
        ∀ x, (∀ b : HalfEdge d (posHalf d μ c), edgeVariable (ι x) b.1.1 = x.1 b) ∧
          (∀ b : HalfEdge d (posHalf d μ c), edgeVariable (ι x) (g.edgeImage b.1.1) = x.2.1 b) ∧
          ∀ y : MirrorPairedPoint g (posHalf d μ c), edgeVariable (ι x) (mirrorEdge y) = x.2.2 y
end YangMills.Construction.GridMirror
end
