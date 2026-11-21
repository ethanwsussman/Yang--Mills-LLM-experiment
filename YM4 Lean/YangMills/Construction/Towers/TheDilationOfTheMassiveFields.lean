import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import YangMills.Construction.Towers.DilationOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.Scaling
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs (descendField)
variable {L : ℕ}
theorem scaleEdge_isPositivelyOriented_iff (hL : 0 < L) (k : ℕ) (e : FullSpace.Edge L k 0) :
    (FullSpace.scaleEdge hL (Nat.zero_le k) 0 e).IsPositivelyOriented ↔ e.IsPositivelyOriented := by
  constructor
  · rintro ⟨ν, hν⟩
    refine ⟨ν, (FullSpace.scaleVertex hL (Nat.zero_le k) 0).injective ?_⟩
    rw [map_sub, FullSpace.scaleVertex_axisStep]
    exact hν
  · rintro ⟨ν, hν⟩
    refine ⟨ν, ?_⟩
    change FullSpace.scaleVertex hL (Nat.zero_le k) 0 e.terminal -
      FullSpace.scaleVertex hL (Nat.zero_le k) 0 e.initial = _
    rw [← map_sub, hν, FullSpace.scaleVertex_axisStep]
def scalePosEdge (hL : 0 < L) (k : ℕ) :
    PeriodicOperators.PosEdge L k 0 ≃ PeriodicOperators.PosEdge L 0 0 :=
  (FullSpace.scaleEdge hL (Nat.zero_le k) 0).subtypeEquiv fun e =>
    (scaleEdge_isPositivelyOriented_iff hL k e).symm
def scaleEdgeIndex (hL : 0 < L) (k : ℕ) :
    (colourEdges L k 0).Carrier ≃ (colourEdges L 0 0).Carrier :=
  (Equiv.refl (Fin 3)).prodCongr (scalePosEdge hL k)
def scaleVertexIndex (hL : 0 < L) (k : ℕ) :
    (colourVertices L k 0).Carrier ≃ (colourVertices L 0 0).Carrier :=
  (Equiv.refl (Fin 3)).prodCongr (FullSpace.scaleVertex hL (Nat.zero_le k) 0).toEquiv
def scaledField (hL : 0 < L) (k : ℕ) (f : (colourEdges L k 0).Carrier → ℂ) :
    (colourEdges L 0 0).Carrier → ℂ :=
  f ∘ (scaleEdgeIndex hL k).symm
def scaledQuotField (hL : 0 < L) (k n : ℕ)
    (ζ : (colourEdges L k 0).QuotMod (2 * L ^ n) → ℂ) :
    (colourEdges L 0 0).QuotMod (2 * L ^ (n + k)) → ℂ :=
  descendField (colourEdges L 0 0) (2 * L ^ (n + k))
    (scaledField hL k (liftQuotField (colourEdges L k 0) (2 * L ^ n) ζ))
open Classical in
def thirdColourWave (L k : ℕ) (q : InfiniteLattice.AmbientSpace) (ρ : Fin 4) :
    (colourEdges L k 0).Carrier → ℂ :=
  fun i => if i.1 = 2 ∧ i.2.1.terminal - i.2.1.initial = InfiniteLattice.axisStep (meshAt L k 0) ρ then
    Complex.exp (Complex.I * bilinDot (toComplexVec q) (toComplexVec ((colourEdges L k 0).pos i)))
  else 0
def shiftedMomentum (p : InfiniteLattice.AmbientSpace) (m : Fin 4 → ℤ) : InfiniteLattice.AmbientSpace :=
  fun μ => p μ + 2 * Real.pi * (m μ : ℝ)
end YangMills.Construction.Tower.MassiveOpFunctions.Scaling
end
