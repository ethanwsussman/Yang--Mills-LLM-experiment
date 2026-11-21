import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.DisjointUnionIntegrals
open YangMills.Construction.ColdStepAtMirrorFrames
def joinFields {α : Type} [DecidableEq α] (C T : Finset α) (a : C → BondVector) (ξ : T → BondVector) (b : α) :
    BondVector :=
  if h : b ∈ C then a ⟨b, h⟩ else if h' : b ∈ T then ξ ⟨b, h'⟩ else 0
def IntegralSplitsOverDisjointUnion : Prop :=
  ∀ (α : Type) [DecidableEq α] (S C T : Finset α) (G : (S → BondVector) → ℝ), S = C ∪ T → Disjoint C T →
    Integrable G →
    Integrable (fun p : (C → BondVector) × (T → BondVector) => G fun b => joinFields C T p.1 p.2 b) ∧
    ∫ η, G η = ∫ p : (C → BondVector) × (T → BondVector), G fun b => joinFields C T p.1 p.2 b
end YangMills.Construction.DisjointUnionIntegrals
end
