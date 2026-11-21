import YangMills.Construction.Continuum.OrderZeroTestFunctionsOnCoordinateSpacesAndGenerators
import YangMills.Construction.GrowingTori.TensorsAndCentredLatticePolynomials
import Mathlib
set_option autoImplicit false
open YangMills.Construction.TorusTransport.TestFunctionOrders YangMills.Construction.ToriLimits
noncomputable section
namespace YangMills.Construction.ReflectionSpaces
instance addCommGroupOrderedTestFun : (q : ℕ) → AddCommGroup (OrderedTestFun q)
  | 0 => inferInstanceAs (AddCommGroup ℂ)
  | _ + 1 => Pi.addCommGroup
instance moduleOrderedTestFun : (q : ℕ) → Module ℂ (OrderedTestFun q)
  | 0 => inferInstanceAs (Module ℂ ℂ)
  | _ + 1 => Pi.module _ _ _
def sepTensorsUpper (P : PeriodicSpace.Params) : (q : ℕ) → Submodule ℂ (OrderedTestFun q)
  | 0 => ⊤
  | q + 1 => sepTensorSpanOn P (q + 1) (upperHalfOpen : Set (Fin 4 → ℝ))
def finiteUpperSequences (P : PeriodicSpace.Params) : Submodule ℂ TestFamily where
  carrier := {f | (∀ q, f q ∈ sepTensorsUpper P q) ∧ ∃ n, ∀ q, n ≤ q → f q = 0}
  add_mem' := by
    rintro f g ⟨hf, n, hn⟩ ⟨hg, m, hm⟩
    refine ⟨fun q => (sepTensorsUpper P q).add_mem (hf q) (hg q), max n m, fun q hq => ?_⟩
    rw [Pi.add_apply, hn q (le_trans (le_max_left _ _) hq), hm q (le_trans (le_max_right _ _) hq),
      add_zero]
  zero_mem' := ⟨fun q => (sepTensorsUpper P q).zero_mem, 0, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨hf, n, hn⟩
    refine ⟨fun q => (sepTensorsUpper P q).smul_mem c (hf q), n, fun q hq => ?_⟩
    rw [Pi.smul_apply, hn q hq, smul_zero]
end YangMills.Construction.ReflectionSpaces
