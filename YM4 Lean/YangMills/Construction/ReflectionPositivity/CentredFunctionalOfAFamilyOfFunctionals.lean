import YangMills.Construction.ReflectionPositivity.CentredObservableAndFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
variable (D : MirrorData) (E : Ambient)
abbrev FunctionalFamily : Type := (n : ℕ) → 2 ≤ n → separatedN D E n → ℝ
namespace FunctionalFamily
variable {D E} (S : FunctionalFamily D E)
def eval (n : ℕ) (Y : FnList D E) : ℝ :=
  open Classical in if h : 2 ≤ n then evalOrZero (S n h) Y else 0
theorem eval_of_mem {n : ℕ} (h : 2 ≤ n) {Y : FnList D E} (hY : Y ∈ separatedN D E n) :
    S.eval n Y = S n h ⟨Y, hY⟩ := by
  simp [eval, h, evalOrZero, hY]
def centeredFunctional (X : separatedAll D E) : ℝ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions X.1.length, ∏ J ∈ π.parts, S.eval J.card (subList X.1 J)
end FunctionalFamily
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
