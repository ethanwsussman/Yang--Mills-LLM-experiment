import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Topology
noncomputable section
namespace YangMills.Construction
namespace Tower
def AnalyticAlongC2CurveStatement : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    ∀ (S : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (g : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction S g → ∀ U ∈ S, ∀ (T : Set ℝ)
        (c : ℝ → Edge L n k j → Matrices.ComplexMatrix2),
        (fieldCurveData L n k j).IsTwiceDiffCurve T c → c 0 = U →
          (∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun s => g (c s)) t) ∧
            DifferentiableAt ℝ (deriv fun s => g (c s)) 0
end Tower
end YangMills.Construction
end
