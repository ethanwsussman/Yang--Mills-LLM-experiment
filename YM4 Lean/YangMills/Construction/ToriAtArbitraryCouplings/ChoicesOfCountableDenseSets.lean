import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableFamilyOfSupportsAndCharts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def c1NormOn : (E : Ambient) → (s.Point E → ℝ) → ℝ
  | .torus, g => TestFunctions.c1NormTorus g
  | .euclidean, g => TestFunctions.c1NormR4 g
theorem c1NormOn_eq_max (E : Ambient) (g : s.Point E → ℝ) :
    s.c1NormOn E g = max (TestFunctions.uniformNorm g)
      (⨆ ν : Fin 4, TestFunctions.uniformNorm (s.partialD ν E g)) := by
  cases E <;> rfl
def IsC1DenseIn (E : Ambient) (K : Set (s.Point E))
    (S : Set (s.Point E → ℝ)) : Prop :=
  ∀ g ∈ s.c1VanishingOutside E K, ∀ δ : ℝ, 0 < δ → ∃ ψ ∈ S, s.c1NormOn E (g - ψ) < δ
structure IsCountableC1DenseChoice (E : Ambient) (F : s.supportFamily E → Set (s.Point E → ℝ)) :
    Prop where
  countable : ∀ K : s.supportFamily E, (F K).Countable
  subset : ∀ K : s.supportFamily E, F K ⊆ s.c1VanishingOutside E K
  dense : ∀ K : s.supportFamily E, s.IsC1DenseIn E K (F K)
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end
