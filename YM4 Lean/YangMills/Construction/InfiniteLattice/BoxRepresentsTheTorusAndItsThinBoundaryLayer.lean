import YangMills.Construction.Constants.BoxTorusNumbers
import YangMills.Construction.InfiniteLattice.FramesRectangularPeriodLatticesAndTheBox
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace FundamentalBox
open NormalFamilies
def RepresentsQuotientWithThinShell : Prop :=
  ∀ (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+) (Λ : PeriodSublattice 1), Λ.IsBoxShaped F s →
    (∀ c : Λ.QuotientTorus, ∃! x : LatticePoint 1, x ∈ F.fundamentalBox s ∧ Λ.quotientMap x = c) ∧
    (F.fundamentalBox s).encard = (Λ.periods.index : ℕ∞) ∧
    (∀ c : Λ.QuotientLink, ∃! b : PositiveLink 1,
      b ∈ (c : Set (PositiveLink 1)) ∧ b.1 ∈ F.boxLinks s) ∧
    ∀ ρ : ℕ+, ((F.boundaryShell s ρ).ncard : ℝ) ≤
      (Constants.BoxTorus.layerNumber : ℝ) * ((ρ : ℕ) : ℝ) * ((F.fundamentalBox s).ncard : ℝ) *
        ∑ i, (((s i : ℕ) : ℝ))⁻¹
end FundamentalBox
end InfiniteLattice
end YangMills.Construction
