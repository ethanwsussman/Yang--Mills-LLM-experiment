import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexOrder Pointwise
noncomputable section
namespace YangMills.Construction
namespace SeparatedTupleFunctionals
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.TestFunctions (partialDerivR4)
section Vectors
variable {n : ℕ}
def dotProd (u w : Fin n → ℝ) : ℝ := ∑ i, u i * w i
end Vectors
section Functions
variable {E : Type*}
def closedSupport [Zero E] [TopologicalSpace E] (f : AmbientSpace → E) : Set AmbientSpace :=
  closure {u | f u ≠ 0}
variable (E) [NormedAddCommGroup E] [NormedSpace ℝ E]
def contCompactSupp : Set (AmbientSpace → E) := {f | Continuous f ∧ IsCompact (closedSupport f)}
variable {E} in
def HasContPartials (f : AmbientSpace → E) : Prop :=
  ∀ μ : Fin 4, (∀ u : AmbientSpace,
      DifferentiableAt ℝ (fun t : ℝ => f (u + t • Pi.single μ (1 : ℝ))) 0) ∧
    Continuous (partialDerivR4 μ f)
def c1CompactSupp : Set (AmbientSpace → E) :=
  {f | f ∈ contCompactSupp E ∧ HasContPartials f}
def c1CompactSuppIn (O : Set AmbientSpace) : Set (AmbientSpace → E) :=
  {f | f ∈ c1CompactSupp E ∧ closedSupport f ⊆ O}
end Functions
def IsRealNonneg (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re
theorem isRealNonneg_iff (z : ℂ) : IsRealNonneg z ↔ 0 ≤ z := by
  rw [Complex.nonneg_iff]
  exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩
end SeparatedTupleFunctionals
end YangMills.Construction
