import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace DirectionalDerivatives
variable {F : BlockFrame}
def evalAlong (Φ : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → F.GaugeField F.top → ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) {k : ℕ}
    (q : Fin k → ChartDirection F) (σ : Fin k → ℝ) : ℝ :=
  Φ (fun x i => w x i + ∑ l, σ l • directionCoordinate (q l) x i)
    (leftTranslate (fun y i => ∑ l, σ l • directionMove (q l) y i) V)
def mixedDerivAlong (Φ : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → F.GaugeField F.top → ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) {k : ℕ}
    (q : Fin k → ChartDirection F) : ℝ :=
  iteratedFDeriv ℝ k (evalAlong Φ w V q) 0 fun l => Pi.single l 1
def shiftCoordinates (r : ChartDirection F) (θ : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => w x i + θ • directionCoordinate r x i
def shiftField (r : ChartDirection F) (θ : ℝ) (V : F.GaugeField F.top) : F.GaugeField F.top :=
  leftTranslate (fun y i => θ • directionMove r y i) V
def MixedDerivLipschitzAndSecondDifference : Prop :=
  (∀ (F : BlockFrame) (Φ : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → F.GaugeField F.top → ℝ)
      (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
      (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions) (r : ChartDirection F) (B t : ℝ), 0 ≤ t →
      (∀ θ, 0 ≤ θ → θ ≤ t →
        AnalyticAt ℝ (evalAlong Φ (shiftCoordinates r θ w) (shiftField r θ V) ![r, Sum.inl p, Sum.inl q]) 0 ∧
        |mixedDerivAlong Φ (shiftCoordinates r θ w) (shiftField r θ V) ![r, Sum.inl p, Sum.inl q]| ≤ B) →
      |mixedDerivAlong Φ (shiftCoordinates r t w) (shiftField r t V) ![Sum.inl p, Sum.inl q] -
        mixedDerivAlong Φ w V ![Sum.inl p, Sum.inl q]| ≤ B * t) ∧
    ∀ (f : (Fin 2 → ℝ) → ℝ) (h B E : ℝ), 0 ≤ h →
      (∀ s u, 0 ≤ s → s ≤ h → 0 ≤ u → u ≤ h → AnalyticAt ℝ f ![s, u] ∧
        |fderiv ℝ (fderiv ℝ f) ![s, u] (Pi.single 0 1) (Pi.single 1 1) - E| ≤ B) →
      |f ![h, h] - f ![h, 0] - f ![0, h] + f ![0, 0] - h ^ 2 * E| ≤ B * h ^ 2
end DirectionalDerivatives
end YangMills.Construction
end
