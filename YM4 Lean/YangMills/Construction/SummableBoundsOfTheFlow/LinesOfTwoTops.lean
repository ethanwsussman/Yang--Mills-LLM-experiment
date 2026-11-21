import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import YangMills.Construction.SummableBoundsOfTheFlow.TwoTopsAlongLines
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction
namespace DerivativeInterpolation
def SmallCurvatureAlongLineAndAgreeOn : Prop :=
  (∀ (F : BlockFrame) (V : F.GaugeField F.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (s u : ℝ),
    (∀ l, ‖X l‖ ≤ 1) → IsSmallCurvature u V → IsSmallCurvature (u + 4 * k * |s|) (alongLine c X s V)) ∧
  ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r k : ℕ)
    (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions) (s : ℝ),
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → (∀ l, BondWithinRadius r (h l)) →
    AgreeOnBall (finiteCells F) (alongLine (bondsAt Y h) X s V) (finiteCells F')
      (alongLine (bondsAt Y' h) X s V') Y Y' r
end DerivativeInterpolation
end YangMills.Construction
end
