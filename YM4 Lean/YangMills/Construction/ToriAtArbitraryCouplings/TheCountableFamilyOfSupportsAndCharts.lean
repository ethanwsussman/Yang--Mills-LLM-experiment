import YangMills.Construction.ToriAtArbitraryCouplings.TheGradientNorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
def IsRationalBox (P : Set (Fin 4 → ℝ)) : Prop :=
  ∃ a b : Fin 4 → ℚ, (∀ μ, a μ < b μ) ∧
    P = Set.pi Set.univ fun μ => Set.Icc (a μ : ℝ) (b μ : ℝ)
def euclidSupportFamily : Set (Set (Fin 4 → ℝ)) :=
  {Q | ∃ B : Set (Set (Fin 4 → ℝ)), B.Finite ∧ (∀ P ∈ B, IsRationalBox P) ∧ Q = ⋃₀ B}
namespace TorusSide
variable (s : TorusSide)
def torusSupportFamily : Set (Set s.asMirrorData.Torus) :=
  {Q | ∃ B : Set (Set (Fin 4 → ℝ)), B.Finite ∧
    (∀ P ∈ B, IsRationalBox P ∧ Set.InjOn s.proj P) ∧
    Q = ⋃ P ∈ B, s.proj '' P}
def supportFamily : (E : Ambient) → Set (Set (s.Point E))
  | .torus => s.torusSupportFamily
  | .euclidean => euclidSupportFamily
theorem empty_mem_supportFamily (E : Ambient) : (∅ : Set (s.Point E)) ∈ s.supportFamily E := by
  cases E
  · exact ⟨∅, Set.finite_empty, by simp, by simp; rfl⟩
  · exact ⟨∅, Set.finite_empty, by simp, by simp; rfl⟩
def c1VanishingOutside (E : Ambient) (Q : Set (s.Point E)) : Set (s.Point E → ℝ) :=
  {f | f ∈ s.c1Set E ∧ ∀ x, x ∉ Q → f x = 0}
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end
