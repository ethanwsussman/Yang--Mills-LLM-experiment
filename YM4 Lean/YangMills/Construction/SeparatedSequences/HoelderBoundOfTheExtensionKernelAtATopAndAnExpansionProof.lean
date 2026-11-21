import YangMills.Construction.SeparatedSequences.BoundOfTheDifferencesOfTheExtensionKernelAtATopAndAnExpansionProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses
namespace KernelHolder
open SingleSequence
section Seminorms
variable {C : ClassData}
end Seminorms
theorem mul_mul_mul_le_of_le {a a' q r r' t : ℝ} (ha : a ≤ a') (ha' : 0 ≤ a') (hq : 0 ≤ q)
    (hr : r ≤ r') (hr0 : 0 ≤ r) (ht : t ≤ 1) (ht0 : 0 ≤ t) : a * q * r * t ≤ a' * q * r' := by
  have h1 : a * q * r * t ≤ a' * q * r * t :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hq) hr0) ht0
  have h2 : a' * q * r * t ≤ a' * q * r' * t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (mul_nonneg ha' hq)) ht0
  have h3 : a' * q * r' * t ≤ a' * q * r' * 1 :=
    mul_le_mul_of_nonneg_left ht (mul_nonneg (mul_nonneg ha' hq) (hr0.trans hr))
  linarith
end KernelHolder
end SeparatedClasses
end YangMills.Construction
end
