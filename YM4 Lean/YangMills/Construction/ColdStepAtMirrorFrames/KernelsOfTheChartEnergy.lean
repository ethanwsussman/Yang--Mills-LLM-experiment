import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
abbrev ChartDirection (F : BlockFrame) : Type :=
  (F.Site F.depth × Fin 4 × imaginaryQuaternions) ⊕ (F.Site F.top × Fin 4 × imaginaryQuaternions)
def directionCell : ChartDirection F → F.Cell
  | .inl p => enclosingCell p.1
  | .inr p => p.1
def directionVector : ChartDirection F → imaginaryQuaternions
  | .inl p => p.2.2
  | .inr p => p.2.2
def directionCoordinate (q : ChartDirection F) (x : F.Site F.depth) (i : Fin 4) : imaginaryQuaternions :=
  match q with
  | .inl p => if p.1 = x ∧ p.2.1 = i then p.2.2 else 0
  | .inr _ => 0
def directionMove (q : ChartDirection F) (y : F.Site F.top) (i : Fin 4) : imaginaryQuaternions :=
  match q with
  | .inl _ => 0
  | .inr p => if p.1 = y ∧ p.2.1 = i then p.2.2 else 0
def chartRestriction (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) {k : ℕ}
    (q : Fin k → ChartDirection F) (σ : Fin k → ℝ) : ℝ :=
  chartedEnergy a (fun x i => w x i + ∑ l, σ l • directionCoordinate (q l) x i)
    (leftTranslate (fun y i => ∑ l, σ l • directionMove (q l) y i) V)
def chartMixedDeriv (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) {k : ℕ}
    (q : Fin k → ChartDirection F) : ℝ :=
  iteratedFDeriv ℝ k (chartRestriction a w V q) 0 fun l => Pi.single l 1
def directionDiameter {k : ℕ} (q : Fin k → ChartDirection F) : ℕ :=
  Finset.univ.sup fun l : Fin k => Finset.univ.sup fun l' : Fin k =>
    cellSupDist (directionCell (q l)) (directionCell (q l'))
structure IsAdmissibleChartPoint (L : ℕ) (σ : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) : Prop where
  coord_small : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1 / (64 * (L : ℝ))
  small_curvature : IsSmallCurvature σ (chartedField w V)
def ChartEnergyKernelBound : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
        IsBlockTorus L F → IsAdmissibleChartPoint L c.σA w V → ∀ (k : ℕ) (q : Fin k → ChartDirection F),
          AnalyticAt ℝ (chartRestriction a w V q) 0 ∧
          (2 ≤ k → (∀ l, ‖directionVector (q l)‖ = 1) →
            |chartMixedDeriv a w V q| ≤ C k * Real.exp (-(c.δ₁ * directionDiameter q)))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
