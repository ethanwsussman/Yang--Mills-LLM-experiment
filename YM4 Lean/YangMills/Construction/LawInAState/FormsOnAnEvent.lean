import YangMills.Construction.LawInAState.ConcentrationOfQuadraticForms
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal
namespace YangMills.Construction.QuadraticConcentration
open YangMills.Construction.WickMoments
variable {ι V Ω : Type}
def IsDominatedByGaussianShifts [MeasurableSpace Ω] (P : Measure Ω) (E : Set Ω) (Y : Ω → ι → ℝ)
    (𝓕 : Set ((ι → ℝ) × Measure (ι → ℝ))) (η : ℝ) : Prop :=
  ∀ (h : (ι → ℝ) → ℝ≥0∞) (b : ℝ≥0∞), Measurable h → (∀ p ∈ 𝓕, ∫⁻ ξ, h (p.1 + ξ) ∂p.2 ≤ b) →
    ∫⁻ u in E, h (Y u) ∂P ≤ ENNReal.ofReal (1 + η) * P E * b
open Classical in
structure QuadraticFormsOnEvent [Fintype ι] [DecidableEq ι] [Fintype V] [MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (Y : Ω → ι → ℝ) (C : Matrix ι ι ℝ) (𝓕 : Set ((ι → ℝ) × Measure (ι → ℝ)))
    (M M' : V → Matrix ι ι ℝ) (Near : V → V → Prop) (f g : V → Ω → ℝ) (κ₀ κ₀' : V → ℝ)
    (a lam A φ ε ρ η err D τ : ℝ) : Prop where
  isProbability : IsProbabilityMeasure P
  measurableSet : MeasurableSet E
  compl_le : P Eᶜ ≤ ENNReal.ofReal τ
  τ_nonneg : 0 ≤ τ
  τ_le : τ ≤ 1 / 2
  measurable_indicator : Measurable (E.indicator Y)
  dominated : IsDominatedByGaussianShifts P E Y 𝓕 η
  η_pos : 0 < η
  η_le : η ≤ 1
  lam_pos : 0 < lam
  one_le_A : 1 ≤ A
  φ_nonneg : 0 ≤ φ
  ε_nonneg : 0 ≤ ε
  ρ_nonneg : 0 ≤ ρ
  err_nonneg : 0 ≤ err
  D_nonneg : 0 ≤ D
  symm : C.IsSymm
  posSemidef : ∀ t : ι → ℝ, 0 ≤ t ⬝ᵥ C.mulVec t
  quad_le : ∀ t : ι → ℝ, t ⬝ᵥ C.mulVec t ≤ lam * (t ⬝ᵥ t)
  gaussian_family : ∀ p ∈ 𝓕, IsCenteredGaussian (fun i j => C i j) p.2 ∧ IsAdmissibleFormFamily p.1 M Near a A φ ε ∧
    IsAdmissibleFormFamily p.1 M' Near a A φ ε
  near_card_le : ((Finset.univ.filter fun p : V × V => Near p.1 p.2).card : ℝ) ≤ ρ * (Fintype.card V : ℝ) ^ 2
  approx_left : ∀ᵐ u ∂P, u ∈ E → ∀ v, |f v u - κ₀ v - (1 / 2) * (Y u ⬝ᵥ (M v).mulVec (Y u))| ≤ err
  approx_right : ∀ᵐ u ∂P, u ∈ E → ∀ v, |g v u - κ₀' v - (1 / 2) * (Y u ⬝ᵥ (M' v).mulVec (Y u))| ≤ err
  memLp_left : ∀ v, MemLp (f v) 64 P ∧ eLpNorm (f v) 64 P ≤ ENNReal.ofReal D
  memLp_right : ∀ v, MemLp (g v) 64 P ∧ eLpNorm (g v) 64 P ≤ ENNReal.ofReal D
def centeringBound (C₀ lam A φ η err D τ : ℝ) : ℝ :=
  (2 * Real.sqrt η * (C₀ * singleFormBound lam A φ) + A * φ ^ 2) + err +
    (3 * D + 2 * (2 * Real.sqrt η * (C₀ * singleFormBound lam A φ) + A * φ ^ 2) + 2 * err) * Real.sqrt τ
def productBoundOnEvent (C₀ lam A φ ε ρ η err D τ : ℝ) : ℝ :=
  2 * (C₀ * productAverageBound lam A φ ε (Real.sqrt ρ + Real.sqrt ε)) + 4 * (C₀ * singleFormBound lam A φ) * err +
    4 * centeringBound C₀ lam A φ η err D τ * (C₀ * averageBound lam A φ ε (Real.sqrt ρ + Real.sqrt ε)) +
    (err + centeringBound C₀ lam A φ η err D τ) ^ 2 +
    (4 * D ^ 2 + 4 * (C₀ * productAverageBound lam A φ ε (Real.sqrt ρ + Real.sqrt ε)) +
      4 * (C₀ * singleFormBound lam A φ) ^ 2) * τ ^ (1 / 32 : ℝ)
def meanBoundOnEvent (C₀ lam A φ ε ρ η err D τ : ℝ) : ℝ :=
  2 * (C₀ * averageBound lam A φ ε (Real.sqrt ρ + Real.sqrt ε)) + err + centeringBound C₀ lam A φ η err D τ +
    2 * D * τ ^ (1 / 32 : ℝ)
def formsOnEventStatement : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (ι V Ω : Type) [Fintype ι] [DecidableEq ι] [Fintype V] [Nonempty V]
    [MeasurableSpace Ω] (P : Measure Ω) (E : Set Ω) (Y : Ω → ι → ℝ) (C : Matrix ι ι ℝ)
    (𝓕 : Set ((ι → ℝ) × Measure (ι → ℝ))) (M M' : V → Matrix ι ι ℝ) (Near : V → V → Prop)
    (f g : V → Ω → ℝ) (κ₀ κ₀' : V → ℝ) (lam A φ ε ρ η err D τ : ℝ),
    QuadraticFormsOnEvent P E Y C 𝓕 M M' Near f g κ₀ κ₀' a lam A φ ε ρ η err D τ →
      eLpNorm (fun u => average (fun v => (f v u - ∫ w, f v w ∂P) * (g v u - ∫ w, g v w ∂P)) -
          average (fun v => (1 / 2) * Matrix.trace (M v * C * M' v * C))) 16 P ≤
        ENNReal.ofReal (productBoundOnEvent C₀ lam A φ ε ρ η err D τ) ∧
      eLpNorm (fun u => average fun v => f v u - ∫ w, f v w ∂P) 16 P ≤
        ENNReal.ofReal (meanBoundOnEvent C₀ lam A φ ε ρ η err D τ) ∧
      eLpNorm (fun u => average fun v => g v u - ∫ w, g v w ∂P) 16 P ≤
        ENNReal.ofReal (meanBoundOnEvent C₀ lam A φ ε ρ η err D τ)
end YangMills.Construction.QuadraticConcentration
end
