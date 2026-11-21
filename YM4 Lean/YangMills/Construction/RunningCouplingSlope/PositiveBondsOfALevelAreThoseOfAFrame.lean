import YangMills.Construction.RunningCouplingSlope.CoordinatesOfTheStepsOfAChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def FramePositiveEdgesBijective : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k m : ℕ, 0 < n → m ≤ k →
    ∀ (F : BlockAverages.BlockFrame) (l : ℕ), (∀ i, F.period l i = 2 * L ^ (n + (k - m))) →
      (∀ b : F.Site l × Fin 4, (edgeOfCoords (L := L) (n := n) (k := k) m b).IsPositivelyOriented) ∧
      Function.Injective
        (fun b : F.Site l × Fin 4 => edgeOfCoords (L := L) (n := n) (k := k) m b) ∧
      ∀ c : Tower.Edge L n k m, c.IsPositivelyOriented → ∃ b : F.Site l × Fin 4, edgeOfCoords m b = c
end RunningCouplingSlope
end YangMills.Construction
end
