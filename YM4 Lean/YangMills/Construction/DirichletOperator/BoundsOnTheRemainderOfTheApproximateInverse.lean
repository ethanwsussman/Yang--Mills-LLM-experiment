import YangMills.Construction.DirichletOperator.TermsOfTheRemainder
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open RegionSequence
open RemainderEstimates
noncomputable section
namespace ApproxInverseRemainder
structure Constants where
  C : ℝ
  minBlock : ℝ
  minProduct : ℝ
  Cα : ℝ → ℝ
  Cε : ℝ → ℝ
instance : Inhabited Constants := ⟨⟨0, 0, 0, fun _ => 0, fun _ => 0⟩⟩
namespace Constants
variable (c : Constants)
structure Holds (L : ℕ) (𝒮 : NestedRegions) (M : ℕ) : Prop where
  kernel_terms : KernelGreenCutoffBound 𝒮 M L c.C
  adjoint_terms : CutoffGreenAdjBound 𝒮 M L c.C
  adjoint_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → RemainderAdjHolderBound 𝒮 M L α (c.Cα α)
  source_terms : ∀ ε : ℝ, 0 < ε → ε < 1 → DivergenceSourceBound 𝒮 M L ε (c.Cε ε)
  source_terms_two : DivergenceSourceL2Bound 𝒮 M L c.C
structure Valid (L : ℕ) : Prop where
  holds : ForChainsAbove L c.minBlock c.minProduct (fun 𝒮 M => c.Holds L 𝒮 M)
end Constants
def chosenConstants (L : ℕ) : Constants := Classical.epsilon fun c : Constants => c.Valid L
end ApproxInverseRemainder
end
end YangMills.Construction
