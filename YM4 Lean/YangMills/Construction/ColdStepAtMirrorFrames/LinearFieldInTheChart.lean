import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import YangMills.Construction.ColdStepAtMirrorFrames.CurvedChainIsAbelian
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def IsLinearFluxPair (X : imaginaryQuaternions) (g : ℝ) (μ ν : Fin 4) (U : F.GaugeField F.depth)
    (V : F.GaugeField F.top) : Prop :=
  ∃ φ : (Fin 4 → ℤ) → ℝ, (∀ z i, U (siteOfCoords F.depth z) i = expUnit (linearFluxAngle g μ ν φ z i • X)) ∧
    ∀ z i, V (siteOfCoords F.top z) i =
      expUnit (linearFluxAngle ((F.blockSide : ℝ) ^ 2 * g) μ ν (fun z => φ fun k => (F.blockSide : ℤ) * z k) z i • X)
def LinearFieldChartGauge : Prop :=
  ∀ (F : BlockFrame) (X : imaginaryQuaternions) (g : ℝ) (μ ν : Fin 4) (n : ℕ), Odd F.blockSide →
    (∀ i, F.extent i = n) → 3 ≤ n → ‖X‖ = 1 → μ < ν →
    ∀ (U : F.GaugeField F.depth) (V : F.GaugeField F.top), IsLinearFluxPair X g μ ν U V →
      ∃ (γ : F.Site F.depth → UnitQuaternion) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions),
        (∀ z, γ (cellCentre F.depth z) = 1) ∧
        (∀ x, ∃ β : ℝ, γ x = expUnit (β • X)) ∧ (∀ x i, gaugeTransform γ U x i = chartedField w V x i) ∧
        (∀ b, IsAxialTreeBond b → w b.1 b.2 = 0) ∧ ∀ x i, ‖w x i‖ ≤ (F.blockSide : ℝ) ^ 2 * |g|
end YangMills.Construction.ColdStepAtMirrorFrames
end
