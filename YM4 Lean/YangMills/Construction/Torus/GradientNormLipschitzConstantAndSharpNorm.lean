import YangMills.Construction.Torus.FormsThatObeyABoundFunction
import YangMills.Construction.Torus.GradientNormOfAFunctionOfOnePoint
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
def lipConst {p : YangMills.Construction.Conventions.StandingParameters} :
    (X : Ambient) → (Pt p X → ℝ) → ℝ
  | .euclidean, f => YangMills.Construction.TestFunctions.lipConstR4 f
  | .torus, f => YangMills.Construction.TestFunctions.lipConstTorus
      (ℓ := YangMills.Construction.PeriodicLattice.torusSide p.L p.m) f
theorem lipConst_eq_bestLipschitzConstant
    {p : YangMills.Construction.Conventions.StandingParameters} (X : Ambient) (f : Pt p X → ℝ) :
    lipConst X f = YangMills.Construction.TestFunctions.bestLipschitzConstant (pointDist p X) f := by
  cases X <;> rfl
def GradientC1Bounds.Statement : Prop :=
  ∀ (p : YangMills.Construction.Conventions.StandingParameters) (X : Ambient),
    (∀ g h : Pt p X → ℂ, IsCnAtPoint 1 g → IsCnAtPoint 1 h →
      (∀ x, gradNorm g x ≤ 2 * ⨆ μ, ‖partialAt μ g x‖) ∧
      IsCnAtPoint 1 (fun x => g x * h x) ∧
      (∀ x, gradNorm (fun y => g y * h y) x ≤
        ‖g x‖ * gradNorm h x + ‖h x‖ * gradNorm g x) ∧
      IsCnAtPoint 1 (fun x => ((g x).re : ℂ)) ∧
      IsCnAtPoint 1 (fun x => ((g x).im : ℂ)) ∧
      c1GradNorm (fun x => ((g x).re : ℂ)) ≤ c1GradNorm g ∧
      c1GradNorm (fun x => ((g x).im : ℂ)) ≤ c1GradNorm g) ∧
    ∀ (M : Set.Ici (1 : ℝ)) (u : Pt p X → ℝ),
      IsCnAtPoint 1 (fun x => (u x : ℂ)) →
      IsCompact (closedSupport (ofSinglePoint fun x => (u x : ℂ))) →
      c1GradNorm (fun x => (u x : ℂ)) < ⊤ ∧
      YangMills.Construction.TestFunctions.IsLipschitzFor (pointDist p X) u ∧
      ENNReal.ofReal (lipConst X u) ≤ gradSupNorm (fun x => (u x : ℂ)) ∧
      ENNReal.ofReal (ambientSharpNorm p M X u) ≤
        ENNReal.ofReal (40 * (M : ℝ)) * c1GradNorm (fun x => (u x : ℂ))
end YangMills.Construction.AmbientPoints
