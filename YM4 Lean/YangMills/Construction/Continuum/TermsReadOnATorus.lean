import YangMills.Construction.Continuum.PeriodLatticeCoveringMapAndFlatDistance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusTransport
open YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions
open scoped ContDiff
namespace TransportData
variable (D : TransportData)
def IsTorusOpen (V : Set D.Torus) : Prop :=
  ∀ ξ ∈ V, ∃ ε : ℝ, 0 < ε ∧ {η : D.Torus | D.torusDist η ξ < ε} ⊆ V
@[instance_reducible] def torusTopology : TopologicalSpace D.Torus where
  IsOpen := D.IsTorusOpen
  isOpen_univ := fun _ _ => ⟨1, one_pos, Set.subset_univ _⟩
  isOpen_inter := by
    intro V W hV hW ξ hξ
    obtain ⟨ε, hε, hεV⟩ := hV ξ hξ.1
    obtain ⟨δ, hδ, hδW⟩ := hW ξ hξ.2
    refine ⟨min ε δ, lt_min hε hδ, fun η hη => ⟨hεV ?_, hδW ?_⟩⟩
    · exact lt_of_lt_of_le (show D.torusDist η ξ < min ε δ from hη) (min_le_left _ _)
    · exact lt_of_lt_of_le (show D.torusDist η ξ < min ε δ from hη) (min_le_right _ _)
  isOpen_sUnion := by
    rintro S hS ξ ⟨V, hV, hξ⟩
    obtain ⟨ε, hε, hεV⟩ := hS V hV ξ hξ
    exact ⟨ε, hε, fun η hη => ⟨V, hV, hεV hη⟩⟩
def torusClosure (A : Set D.Torus) : Set D.Torus := @closure _ D.torusTopology A
def torusSupport {E : Type*} [Zero E] (f : D.Torus → E) : Set D.Torus :=
  D.torusClosure (Function.support f)
def IsTorusCompact (A : Set D.Torus) : Prop := @IsCompact _ D.torusTopology A
section Derivatives
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def IsC1 (u : D.Torus → E) : Prop := IsC1R4 (u ∘ D.projHom)
def partialDeriv (μ : Fin 4) (u : D.Torus → E) (ξ : D.Torus) : E :=
  partialDerivR4 μ (u ∘ D.projHom) (liftPoint ξ)
end Derivatives
def closedBall (ξ : D.Torus) (R : ℝ) : Set D.Torus := {η | D.torusDist η ξ ≤ R}
end TransportData
end YangMills.Construction.TorusTransport
end
