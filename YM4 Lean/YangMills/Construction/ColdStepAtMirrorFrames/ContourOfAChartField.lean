import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def ChartedFieldContourBound : Prop :=
  ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (ε : ℝ),
    Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → 0 ≤ ε → (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ ε) →
    ∀ (c : F.Site F.top × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
      ‖((pathHolonomy (chartedField w V) (refineSite c.1) (bondContour F.blockSide h π c.2) *
          (V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        5 * (F.blockSide : ℝ) * ε
end ColdStepAtMirrorFrames
end YangMills.Construction
end
