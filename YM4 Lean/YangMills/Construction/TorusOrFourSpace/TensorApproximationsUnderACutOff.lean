import YangMills.Construction.TorusOrFourSpace.ModesOfACutOffOnThePeriodBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell
open Kind.Tuple
def cutoffFourierSum (D : Params) {n : ℕ+} (P : ℝ)
    (χ : Fin (n : ℕ) → Kind.euclidean.Pt D → ℝ) (F : Kind.euclidean.Tuple D n → ℂ)
    (t : ℕ+) : Kind.euclidean.Tuple D n → ℂ :=
  ∑ k ∈ IntCoords.cubeUpTo t, fourierCoeff D P F k •
    tensorProd D Kind.euclidean fun i => cutoffMode D P (χ i) (k.block i)
def TensorApproxUnderCutoff : Prop :=
  ∀ (D : Params) (n : ℕ+) (ρ : ℝ), 0 < ρ →
    ∀ O : Fin (n : ℕ) → Set (Kind.euclidean.Pt D),
      (∀ i, Kind.IsOpenQ D Kind.euclidean (O i)) →
      (∀ i, ∀ u ∈ O i, TorusMetric.euclidNormVec u ≤ ρ) →
    (∀ K : Fin (n : ℕ) → Set (Kind.euclidean.Pt D),
      (∀ i, Kind.IsCompactQ D Kind.euclidean (K i)) → (∀ i, K i ⊆ O i) →
      ∃ χ, IsCutoffFamily D Kind.euclidean O χ ∧ ∀ i, ∀ y ∈ K i, χ i y = 1) ∧
    (∀ (F : Kind.Tuple.testFns D Kind.euclidean
          (boxSet D Kind.euclidean O)) (χ),
      IsCutoffFamily D Kind.euclidean O χ →
      (∀ i, ∀ y ∈ supportT D Kind.euclidean F.1, χ i (y i) = 1) →
      IsCutoffOf D Kind.euclidean χ F) ∧
    Kind.Tuple.testFns D Kind.euclidean (boxSet D Kind.euclidean O) ⊆
      cellTestFns D n (4 * ρ) ∧
    ∀ (F : Kind.Tuple.testFns D Kind.euclidean
          (boxSet D Kind.euclidean O)) (χ),
      IsCutoffOf D Kind.euclidean χ F →
      ∃ Fs : ℕ+ → Kind.Tuple.testFns D Kind.euclidean
          (boxSet D Kind.euclidean O),
        (∀ t, (Fs t).1 = cutoffFourierSum D (4 * ρ) χ F.1 t) ∧
        (∀ t, ∃ (m : ℕ) (φ : Fin m → Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ),
          (∀ l i, φ l i ∈ singleTestFns D Kind.euclidean (O i) ∧
            Kind.supportQ D Kind.euclidean (φ l i) ⊆ Kind.supportQ D Kind.euclidean (χ i)) ∧
          (Fs t).1 = ∑ l, tensorProd D Kind.euclidean (φ l)) ∧
        TendstoInTestFns Fs F
end YangMills.Construction.PeriodicSpace.PeriodCell
