import YangMills.Construction.Towers.OperatorsDependingLocallyOnAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open OneLoopNotation
variable {J B : Type}
def diagTrace (S : BddOp (IndexL2 J)) : ℂ := ∑' i, Tower.UnitLatticeL2.matrixEntry S i i
def variationTrace (T : (B → ℝ) → BddOp (IndexL2 J)) (z : ℝ) (b b' : B) : ℂ :=
  diagTrace ((baseResolvent T z 0).comp (secondVar T b b')) -
    diagTrace ((baseResolvent T z 0).comp ((firstVar T b).comp
      ((baseResolvent T z 0).comp (firstVar T b'))))
def LogDensityHessianSum : Prop :=
  ∀ (J B : Type) (pos : J → InfiniteLattice.AmbientSpace) (src : B → InfiniteLattice.AmbientSpace)
    (m m' : ℕ) (z C : ℝ) (T : (B → ℝ) → BddOp (IndexL2 J)),
    0 < z → 0 < C → IsLocalExpansionSetting pos src m m' z C T →
    ∀ b b' : B,
      HasSum (fun x : Fin 4 → ℤ =>
          logTraceHessian pos T z (PeriodicOperators.castVec x) b b')
        (variationTrace T z b b')
end YangMills.Construction.Tower.LocalFamilies
end
