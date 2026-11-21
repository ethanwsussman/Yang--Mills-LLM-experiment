import YangMills.Construction.RunningCouplingSlope.CoefficientOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SlopeCoefficient
open scoped Topology Quaternion
def HasMixedSecondMoment (l : Filter ℕ) (H : GaugeTotal) (b : ℝ) : Prop :=
  ∃ P : Fin 4 → Fin 4 → (Fin 4 → ℤ) → ℝ,
    (∀ (c c' : TorusLumps.LatticeBond) (X X' : BlockAverages.imaginaryQuaternions),
      Filter.Tendsto (fun n => hessianAtTrivial H n (TorusLumps.bondFrom 0 c) (TorusLumps.bondFrom 0 c') X X') l
        (𝓝 (inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * P c.2 c'.2 (c'.1 - c.1)))) ∧
    ∀ μ ν : Fin 4, μ ≠ ν →
      HasSum (fun u : Fin 4 → ℤ => P μ ν u * ((u μ : ℤ) : ℝ) * ((u ν : ℤ) : ℝ)) b
def SlopeIsMixedMoment : Prop :=
  ∀ (l : Filter ℕ) [l.NeBot], l ≤ Filter.atTop → ∀ (H : GaugeTotal) (b : ℝ),
    HasSlopeCoefficient l H b → HasMixedSecondMoment l H b
end SlopeCoefficient
end YangMills.Construction
end
