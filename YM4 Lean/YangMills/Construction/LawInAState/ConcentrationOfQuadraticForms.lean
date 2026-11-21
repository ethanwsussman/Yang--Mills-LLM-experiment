import YangMills.Construction.LawInAState.MomentsOfWickPolynomials
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
namespace YangMills.Construction.QuadraticConcentration
variable {ι V : Type} [Fintype ι] [Fintype V]
def centeredQuadraticForm (C M : Matrix ι ι ℝ) (F ξ : ι → ℝ) : ℝ :=
  (1 / 2) * ((F + ξ) ⬝ᵥ M.mulVec (F + ξ)) - (1 / 2) * Matrix.trace (M * C)
def average (G : V → ℝ) : ℝ := (Fintype.card V : ℝ)⁻¹ * ∑ v, G v
structure IsAdmissibleFormFamily [DecidableEq ι] (F : ι → ℝ) (M : V → Matrix ι ι ℝ) (Near : V → V → Prop) (a A φ ε : ℝ) : Prop where
  symm : ∀ v, (M v).IsSymm
  op : ∀ v (s t : ι → ℝ), (s ⬝ᵥ (M v).mulVec t) ^ 2 ≤ a ^ 2 * (s ⬝ᵥ s) * (t ⬝ᵥ t)
  hs : ∀ v, Matrix.trace (M v * M v) ≤ A
  image : ∀ v, (M v).mulVec F ⬝ᵥ (M v).mulVec F ≤ A * φ ^ 2
  self : ∀ v, |F ⬝ᵥ (M v).mulVec F| ≤ A * φ ^ 2
  far_trace : ∀ v w, ¬ Near v w → |Matrix.trace (M v * M w)| ≤ ε
  far_product : ∀ v w, ¬ Near v w → Matrix.trace ((M v * M w) * (M v * M w)ᵀ) ≤ ε ^ 2
  far_image : ∀ v w, ¬ Near v w → |(M v).mulVec F ⬝ᵥ (M w).mulVec F| ≤ ε
def productAverageBound (lam A φ ε η : ℝ) : ℝ :=
  lam ^ 2 * A * η + lam ^ (3 / 2 : ℝ) * A * φ * η + lam * A * φ ^ 2 + lam * Real.sqrt (ε * A) * φ +
    lam * A ^ (3 / 2 : ℝ) * φ ^ 2 * η + lam ^ (1 / 2 : ℝ) * A ^ (3 / 2 : ℝ) * φ ^ 3 * η +
    lam ^ (1 / 2 : ℝ) * A * φ ^ 2 * Real.sqrt ε + A ^ 2 * φ ^ 4
def averageBound (lam A φ ε η : ℝ) : ℝ :=
  lam * Real.sqrt A * η + lam ^ (1 / 2 : ℝ) * Real.sqrt A * φ * η + lam ^ (1 / 2 : ℝ) * Real.sqrt ε + A * φ ^ 2
def singleFormBound (lam A φ : ℝ) : ℝ :=
  lam * Real.sqrt A + lam ^ (1 / 2 : ℝ) * Real.sqrt A * φ + A * φ ^ 2
open Classical in
def quadraticConcentrationStatement : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (ι V : Type) [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty V]
    (C : Matrix ι ι ℝ) (μ : Measure (ι → ℝ)) (F : ι → ℝ) (M M' : V → Matrix ι ι ℝ) (Near : V → V → Prop)
    (lam A φ ε ρ : ℝ), 0 ≤ lam → 1 ≤ A → 0 ≤ φ → 0 ≤ ε → 0 ≤ ρ → C.IsSymm →
    (∀ t : ι → ℝ, 0 ≤ t ⬝ᵥ C.mulVec t) → (∀ t : ι → ℝ, t ⬝ᵥ C.mulVec t ≤ lam * (t ⬝ᵥ t)) →
    WickMoments.IsCenteredGaussian (fun i j => C i j) μ → IsAdmissibleFormFamily F M Near a A φ ε →
    IsAdmissibleFormFamily F M' Near a A φ ε →
    ((Finset.univ.filter fun p : V × V => Near p.1 p.2).card : ℝ) ≤ ρ * (Fintype.card V : ℝ) ^ 2 →
      (∫ ξ, (average (fun v => centeredQuadraticForm C (M v) F ξ * centeredQuadraticForm C (M' v) F ξ) -
            average (fun v => (1 / 2) * Matrix.trace (M v * C * M' v * C))) ^ 16 ∂μ ≤
          (C₀ * productAverageBound lam A φ ε (Real.sqrt ρ + Real.sqrt ε)) ^ 16) ∧
      (∫ ξ, average (fun v => centeredQuadraticForm C (M v) F ξ) ^ 16 ∂μ ≤
          (C₀ * averageBound lam A φ ε (Real.sqrt ρ + Real.sqrt ε)) ^ 16) ∧
      ∀ v, ∫ ξ, centeredQuadraticForm C (M v) F ξ ^ 32 ∂μ ≤ (C₀ * singleFormBound lam A φ) ^ 32
end YangMills.Construction.QuadraticConcentration
end
