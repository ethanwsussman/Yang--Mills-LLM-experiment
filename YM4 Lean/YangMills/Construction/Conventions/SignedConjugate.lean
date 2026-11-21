import Mathlib
set_option autoImplicit false
universe u
namespace YangMills.Construction
namespace Conventions
noncomputable def signedConj (s : ℤˣ) (z : ℂ) : ℂ :=
  if s = 1 then z else starRingEnd ℂ z
noncomputable def signedConjFun {X : Type u} (s : ℤˣ) (f : X → ℂ) : X → ℂ :=
  fun x => signedConj s (f x)
def onesVector : Fin 4 → ℝ := fun _ => 1
end Conventions
end YangMills.Construction
