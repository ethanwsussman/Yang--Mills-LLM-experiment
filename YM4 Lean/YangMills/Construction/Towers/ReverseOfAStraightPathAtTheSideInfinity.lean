import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
namespace Tower.FullSpace
def AxisPathReversal.statement : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
  ∀ (x y : Vertex L k j) (μ : Fin 4) (m : ℤ), IsAxisDisplacement x y μ m →
    (∃ q : Fin 4 × ℤ, IsAxisDisplacement y x q.1 q.2) ∧
    axisPath y x = ((axisPath x y).map InfiniteLattice.Link.opposite).reverse ∧
    ∀ (𝕜 E : Type) [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : Edge L k j → E),
      (∀ e, f e.opposite = -f e) →
        ((axisPath y x).map f).sum = -((axisPath x y).map f).sum
end Tower.FullSpace
end YangMills.Construction
