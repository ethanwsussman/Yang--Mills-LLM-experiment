import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheBlockEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace WeightedResponses
variable {F : BlockFrame}
def siteShareAlong (a : ℝ) (y : F.Site F.depth) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {k : ℕ} (q : Fin k → ChartDirection F) (s : Fin k → ℝ) : ℝ :=
  minimalSiteShare a y (chartedField (fun x i => w x i + ∑ l, s l • directionCoordinate (q l) x i)
    (leftTranslate (fun z i => ∑ l, s l • directionMove (q l) z i) V))
def siteShareMixedDeriv (a : ℝ) (y : F.Site F.depth) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {k : ℕ} (q : Fin k → ChartDirection F) : ℝ :=
  iteratedFDeriv ℝ k (siteShareAlong a y w V q) 0 fun l => Pi.single l 1
def SiteShareKernelBound : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ Ck : ℕ → ℝ, (∀ k, 0 < Ck k) ∧
      ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
        IsBlockTorus L F →
        IsAdmissibleChartPoint L c.σA w V → ∀ (y : F.Site F.depth) (k : ℕ) (q : Fin k → ChartDirection F),
          AnalyticAt ℝ (siteShareAlong a y w V q) 0 ∧
          (1 ≤ k → (∀ l, ‖directionVector (q l)‖ = 1) →
            |siteShareMixedDeriv a y w V q| ≤ Ck k * Real.exp (-(c.δ₁ * directionReach (enclosingCell y) q)))
end WeightedResponses
end YangMills.Construction
end
