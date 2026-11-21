import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ReflectionKernel
def normSq (u : Fin 4 → ℝ) : ℝ := ∑ l, u l ^ 2
def reflectionEntry (u : Fin 4 → ℝ) (m r : Fin 4) : ℝ :=
  (if m = r then 1 else 0) - 2 * u m * u r / normSq u
def kernel (u : Fin 4 → ℝ) (m n r s : Fin 4) : ℝ :=
  (reflectionEntry u m r * reflectionEntry u n s - reflectionEntry u m s * reflectionEntry u n r) /
    (Real.pi ^ 2 * normSq u ^ 2)
def orientedPlanes : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun A => A.1 < A.2
def KernelEstimates : Prop :=
  (∀ (u : Fin 4 → ℝ) (m n r s : Fin 4), u ≠ 0 → |kernel u m n r s| ≤ 18 / normSq u ^ 2) ∧
  (∀ (u w : Fin 4 → ℝ) (m n r s : Fin 4), u ≠ 0 → 4 * normSq (u - w) ≤ normSq u →
    |kernel u m n r s - kernel w m n r s| ≤
      3000 * Real.sqrt (normSq (u - w)) / Real.sqrt (normSq u) ^ 5) ∧
  ∀ u : Fin 4 → ℝ, u ≠ 0 →
    ∑ A ∈ orientedPlanes, ∑ B ∈ orientedPlanes,
      kernel u A.1 A.2 B.1 B.2 * kernel u B.1 B.2 A.1 A.2 = 6 / (Real.pi ^ 4 * normSq u ^ 4)
end ReflectionKernel
end YangMills.Construction
end
