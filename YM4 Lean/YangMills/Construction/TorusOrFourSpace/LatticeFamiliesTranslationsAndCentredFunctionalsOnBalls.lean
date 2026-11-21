import YangMills.Construction.TorusOrFourSpace.HierarchiesCentredMomentsAndObeyingABoundFunction
import YangMills.Construction.TorusOrFourSpace.TensorsOfSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
def sepTensorSpanOnBall (ρ : ℝ≥0∞) (q : ℕ) : Submodule ℂ ((Fin q → E.Pt D) → ℂ) :=
  Submodule.span ℂ
    {F | ∃ h ∈ sepC1TuplesWithin D E q (centredBall D E ρ),
      F = tensorFn D E fun i y => ((h i y : ℝ) : ℂ)}
theorem restrictTuple_mem_sepC1TuplesWithin {q : ℕ} {O : Set (E.Pt D)} {h : FnTuple D E q}
    (hh : h ∈ sepC1TuplesWithin D E q O) (J : Finset (Fin q)) :
    restrictTuple D E h J ∈ sepC1TuplesWithin D E J.card O :=
  ⟨restrictTuple_mem_sepC1Tuples D E hh.1 J, fun _ => hh.2 _⟩
structure BallMultilinearFamily (ρ : ℝ≥0∞) where
  func : (n : ℕ) → 2 ≤ n → sepC1TuplesWithin D E n (centredBall D E ρ) → ℝ
  multilinear : ∀ n (hn : 2 ≤ n),
    IsMultilinearOn D E (sepC1TuplesWithin D E n (centredBall D E ρ)) (func n hn)
variable {D E} in
def BallMultilinearFamily.centredFunc {ρ : ℝ≥0∞} (Ψ : BallMultilinearFamily D E ρ)
    {q : ℕ} (h : sepC1TuplesWithin D E q (centredBall D E ρ)) : ℝ :=
  ∑ ξ ∈ (partitionsNoSingletons q).attach, ∏ J ∈ ξ.1.parts.attach,
    Ψ.func J.1.card (two_le_card_of_mem_partitionsNoSingletons ξ.2 J.2)
      ⟨restrictTuple D E h.1 J.1, restrictTuple_mem_sepC1TuplesWithin D E h.2 J.1⟩
end YangMills.Construction.PeriodicSpace.Kind
