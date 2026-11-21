import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsWithTheirConstantsForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Cumulants
open MeasureTheory BlockAverages ColdStepAtMirrorFrames
def placeSummedCumulantBound : Prop :=
  ∀ (N : ℕ) (κ : ℝ) (M : ℕ), 0 < κ → 1 ≤ M → ∃ W : ℝ, 0 ≤ W ∧
    ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (w : ℝ → ℝ) (Ψ : BondField ι → ℝ) (Q : Fin M → Type)
      [∀ i, Fintype (Q i)] (z : ∀ i, Q i → F.Cell) (O : ∀ i, Q i → BondField ι → ℝ)
      (e : ∀ i, Q i → ℝ) (A : Fin M → ℝ) (T₀ r n : ℝ) (Y₀ : F.Cell),
      κ / 16 ≤ r → 0 ≤ T₀ → (∀ i, 0 ≤ A i) → (∀ i q, 0 ≤ e i q) → (∀ i, Nonempty (Q i)) →
      (∀ i (u : F.Cell), (Finset.univ.filter fun q => z i q = u).card ≤ N) →
      (∀ (p : ∀ i, Q i) (J : Finset (Fin M)),
        Integrable fun η => (∏ l ∈ J, O l (p l) η) * ballDensity w Ψ η) →
      (∀ p : ∀ i, Q i, |cumulantFromMoments w Ψ fun i => O i (p i)| ≤
        T₀ * (∏ i, (A i * Real.exp (-(r * e i (p i))))) *
          Real.exp (-(κ / 8 * ConvexObservables.cellsDiameter fun i => z i (p i)))) →
      (∀ (p : ∀ i, Q i) (i : Fin M),
        cellSupDist (z i (p i)) Y₀ ≤ ConvexObservables.cellsDiameter fun i => z i (p i)) →
      (∀ p : ∀ i, Q i, n ≤ (ConvexObservables.cellsDiameter fun i => z i (p i)) + ∑ i, e i (p i)) →
      |cumulantFromMoments w Ψ fun i η => ∑ q, O i q η| ≤
        W * T₀ * (∏ i, A i) * Real.exp (-(κ / 16 * n))
end YangMills.Construction.Cumulants
end
