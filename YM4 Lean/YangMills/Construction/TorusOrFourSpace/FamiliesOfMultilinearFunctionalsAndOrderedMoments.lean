import YangMills.Construction.TorusOrFourSpace.HierarchiesCentredMomentsAndObeyingABoundFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
@[ext]
structure MultilinearFamily where
  func : (n : ℕ) → 2 ≤ n → sepC1Tuples D E n → ℝ
  multilinear : ∀ n (hn : 2 ≤ n),
    IsMultilinearOn D E (sepC1Tuples D E n) (func n hn)
namespace MultilinearFamily
variable {D E}
def indexOrderedMoment (Φ : MultilinearFamily D E) {q : ℕ} (_hq : 1 ≤ q)
    (f : sepC1Tuples D E q) : ℝ :=
  ∑ π ∈ (partitionsNoSingletons q).attach, ∏ B ∈ π.1.parts.attach,
    Φ.func B.1.card (two_le_card_of_mem_partitionsNoSingletons π.2 B.2)
      ⟨restrictTuple D E f.1 B.1, restrictTuple_mem_sepC1Tuples D E f.2 B.1⟩
end MultilinearFamily
end YangMills.Construction.PeriodicSpace.Kind
