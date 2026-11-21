import YangMills.Construction.ResponseInTheExpansion.MixedDerivativesAlongSlots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames DirectionalDerivatives
namespace ChartResponse
def shiftTwice {F : BlockFrame} (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions) (s u : ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  shiftCoordinates (Sum.inl q : ChartDirection F) u (shiftCoordinates (Sum.inl p : ChartDirection F) s w)
def HessianEntryAgreeOnTwoTori : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L → ∀ ϱ : ℝ, 0 < ϱ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
        (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
        (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ)
        (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions)
        (p' q' : F'.Site F'.depth × Fin 4 × imaginaryQuaternions), 1 ≤ r → IsBlockTorus L F → IsBlockTorus L F' →
        F'.depth = F.depth →
        ‖p.2.2‖ = 1 → ‖q.2.2‖ = 1 → ‖p'.2.2‖ = 1 → ‖q'.2.2‖ = 1 →
        (∀ s u, 0 ≤ s → s ≤ ϱ → 0 ≤ u → u ≤ ϱ →
          IsAdmissibleChartPoint L c.σA (shiftTwice p q s u w) V ∧
            IsAdmissibleChartPoint L c.σA (shiftTwice p' q' s u w') V') →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
        (∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube L →
          fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
          w (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i ∧
          directionCoordinate (Sum.inl p) (fineBondAt Y h o i).1 i =
            directionCoordinate (Sum.inl p') (fineBondAt Y' h o i).1 i ∧
          directionCoordinate (Sum.inl q) (fineBondAt Y h o i).1 i =
            directionCoordinate (Sum.inl q') (fineBondAt Y' h o i).1 i) →
        8 * cellSupDist (enclosingCell p.1) Y ≤ r → 8 * cellSupDist (enclosingCell p'.1) Y' ≤ r →
        |chartMixedDeriv a w V ![Sum.inl p, Sum.inl q] - chartMixedDeriv a w' V' ![Sum.inl p', Sum.inl q']| ≤
          C * Real.exp (-(c.δ₁ / 16 * r))
end ChartResponse
end YangMills.Construction
end
