import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ChartLipschitz
def ChartedFieldLipschitz : Prop :=
  (∀ u v : imaginaryQuaternions,
    ‖((expUnit u : UnitQuaternion) : ℍ[ℝ]) - ((expUnit v : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖u - v‖) ∧
  ∀ (F : BlockFrame) (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (ε : ℝ),
    (∀ z i, ‖w z i - w' z i‖ ≤ ε) → 0 ≤ ε →
    (∀ (x : F.Site F.depth) (l : List PathStep),
      ‖((pathHolonomy (chartedField w V) x l : UnitQuaternion) : ℍ[ℝ]) -
          ((pathHolonomy (chartedField w' V) x l : UnitQuaternion) : ℍ[ℝ])‖ ≤
        l.length * ε) ∧
    ∀ p : F.Site F.depth × Fin 4 × Fin 4,
      plaquetteDefect (chartedField w V) p ≤ plaquetteDefect (chartedField w' V) p + 4 * ε
end ChartLipschitz
end YangMills.Construction
end
