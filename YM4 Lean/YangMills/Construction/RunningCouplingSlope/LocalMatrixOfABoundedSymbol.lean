import YangMills.Construction.RunningCouplingSlope.CellsOfATower
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
structure IsCellQuotient (L n k : ℕ) (I : PeriodicOperators.PeriodicData) {ι : Type}
    (q : I.Carrier → ι) (c : ι → Tower.Vertex L n k k) : Prop where
  surjective : Function.Surjective q
  image_eq_iff : ∀ i i', q i = q i' ↔
    ∃ m : Fin 4 → ℤ, i' = I.translate (LocalKernels.Periodisation.periodSide L n • m) i
  exists_near_cell : ∀ i, ∃ v : Fin 4 → ℤ, cellOfCoords L n k v = c (q i) ∧
    ∀ μ, |I.pos i μ - (v μ : ℝ)| ≤ 1
  eq_of_same_cell : ∀ i (m : Fin 4 → ℤ), c (q i) = c (q (I.translate m i)) →
    q i = q (I.translate m i)
def BoundedSymbolLocalMatrix : Prop :=
  ∀ υ : ℝ, 0 < υ → ∃ K θ : ℝ, 0 < K ∧ 0 < θ ∧
    ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ I I' : PeriodicOperators.PeriodicData, PeriodicOperators.IsPeriodic I →
      PeriodicOperators.IsPeriodic I' →
    ∀ w w' : ℝ, 0 < w → 0 < w' → (∀ i, I.weightOf i = w) → (∀ i, I'.weightOf i = w') →
    ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
      (q : I.Carrier → ι) (q' : I'.Carrier → ι') (c : ι → Tower.Vertex L n k k)
      (c' : ι' → Tower.Vertex L n k k),
      IsCellQuotient L n k I q c → IsCellQuotient L n k I' q' c' →
      ∀ (T : I'.Carrier → I.Carrier → ℂ) (C : ℝ), 0 < C → PeriodicOperators.IsPeriodicKernel I I' T →
        Tower.FreeStrip.SymbolBoundedOn I I' T (PeriodicOperators.imStrip υ) C →
      ∀ M : Matrix ι' ι ℂ,
        (∀ i' i, M (q' i') (q i) =
          PeriodicOperators.periodization I I' T (LocalKernels.Periodisation.periodSide L n) i' i) →
        IsLocalOnCells c c' M (K * C * Real.sqrt (w / w')) θ fun _ => 1
end YangMills.Construction.RunningCouplingSlope
end
