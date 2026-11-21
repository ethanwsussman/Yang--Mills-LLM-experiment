import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.PropertiesOfTheLeftChart
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
def GaugeImageCurvesInFibre : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L m k k) fun W =>
      ∀ (κ : vertexFunctionsVanishingAtTop L m k) (I : Set ℝ) (γ : ℝ → Edge L m k 0 → Matrices.ComplexMatrix2),
        (fieldCurveData L m k 0).IsTwiceDiffCurve I γ →
        MapsTo γ I (smoothingIterFibre (smoothingFibreNhd L m k) W) → γ 0 = chainBottom W →
        ∃ J : Set ℝ, J ⊆ I ∧
          (fieldCurveData L m k 0).IsTwiceDiffCurve J (fun t : ℝ =>
            PeriodicLattice.gaugeTransform (expVertexFn (((-t : ℝ) : ℂ) •
              (κ : Vertex L m k 0 → Matrices.ComplexMatrix2))) (γ t)) ∧
          MapsTo (fun t : ℝ => PeriodicLattice.gaugeTransform (expVertexFn (((-t : ℝ) : ℂ) •
              (κ : Vertex L m k 0 → Matrices.ComplexMatrix2))) (γ t)) J
            (smoothingIterFibre (smoothingFibreNhd L m k) W) ∧
          PeriodicLattice.gaugeTransform (expVertexFn (((-(0 : ℝ) : ℝ) : ℂ) •
              (κ : Vertex L m k 0 → Matrices.ComplexMatrix2))) (γ 0) = chainBottom W ∧
          (fieldCurveData L m k 0).tangent (fun t : ℝ =>
            PeriodicLattice.gaugeTransform (expVertexFn (((-t : ℝ) : ℂ) •
              (κ : Vertex L m k 0 → Matrices.ComplexMatrix2))) (γ t)) =
            (fieldCurveData L m k 0).tangent γ + covDiff (chainBottom W) κ ∧
          ∀ t ∈ J, plaquetteAction L m k (PeriodicLattice.gaugeTransform (expVertexFn (((-t : ℝ) : ℂ) •
              (κ : Vertex L m k 0 → Matrices.ComplexMatrix2))) (γ t)) = plaquetteAction L m k (γ t)
end YangMills.Construction.Tower
end
