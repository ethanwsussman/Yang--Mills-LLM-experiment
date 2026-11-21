import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FormOnAFibre
def VertexFunctionsAreEuclidean.Statement : Prop :=
  ∀ L m k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → j ≤ k →
    Tower.VertexFunctionsEuclidean L m k j
end YangMills.Construction.FormOnAFibre
end
