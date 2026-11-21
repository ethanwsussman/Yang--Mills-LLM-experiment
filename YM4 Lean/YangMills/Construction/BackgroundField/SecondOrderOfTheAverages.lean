import YangMills.Construction.BackgroundField.GaugeFixedOperators
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.BackgroundField
open Set PeriodicLattice Matrices
variable {L m K : ℕ}
def interiorBonds (Ω : Set (FineSite L m K)) : Set (FineBond L m K) :=
  {b | b.source ∈ Ω ∧ b.target ∈ Ω}
def interiorPlaquettes (Ω : Set (FineSite L m K)) : Set (FinePlaquette L m K) :=
  {p | p.vertices ⊆ Ω}
def smallInteriorForms (Ω : Set (FineSite L m K)) (α₁ : ℝ) : Set (FineBond L m K → ComplexMatrix2) :=
  {A | IsBondForm complexLieAlgebra A ∧
    ∀ b ∈ interiorBonds Ω, ComplexMatrix2.operatorNorm (A b) < α₁}
def scaledAverageAngle (k : ℕ) (U₀ A : FineBond L m K → ComplexMatrix2) (c : BondAtLevel L m K k) :
    ComplexMatrix2 :=
  relativeAverageAngle U₀ (((finestMeshInLevelUnits L k : ℝ) : ℂ) • A) k c
def averageAngleLinearPart (k : ℕ) (U₀ A : FineBond L m K → ComplexMatrix2)
    (c : BondAtLevel L m K k) : ComplexMatrix2 :=
  deriv (fun z : ℂ => scaledAverageAngle k U₀ (z • A) c) 0
def averageAngleRemainder (k : ℕ) (U₀ A : FineBond L m K → ComplexMatrix2)
    (c : BondAtLevel L m K k) : ComplexMatrix2 :=
  scaledAverageAngle k U₀ A c - averageAngleLinearPart k U₀ A c
def AnalyticOnBondForms (𝒟 : Set (FineBond L m K → ComplexMatrix2))
    (F : (FineBond L m K → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∀ (n : ℕ) (A : FineBond L m K → ComplexMatrix2) (D : Fin n → FineBond L m K → ComplexMatrix2),
    IsBondForm complexLieAlgebra A → (∀ i, IsBondForm complexLieAlgebra (D i)) →
    AnalyticOnNhd ℂ (fun z : Fin n → ℂ => F (A + ∑ i, z i • D i)) {z | A + ∑ i, z i • D i ∈ 𝒟}
structure AverageExpansionConstants where
  remainderBound : ℝ
  smallness : ℝ
def IsAverageExpansionConstants (L : ℕ) (N : AverageExpansionConstants) : Prop :=
  0 < N.remainderBound ∧ 0 < N.smallness ∧
    ∀ (m K k : ℕ), 0 < m → k ≤ K → ∀ Ω : Set (FineSite L m K),
      Ω = fineBlockUnion (levelSitesOf k Ω) →
      ∀ (α₀ α₁ : ℝ) (U₀ : FineBond L m K → ComplexMatrix2), 0 < α₀ → 0 < α₁ →
        α₀ ≤ N.smallness → α₁ ≤ N.smallness →
        IsGaugeField compactGaugeGroup univ U₀ →
        (∀ p ∈ interiorPlaquettes Ω,
          ComplexMatrix2.operatorNorm (plaquetteHolonomy U₀ p - 1) <
            α₀ * finestMeshInLevelUnits L k ^ 2) →
        ∀ c : BondAtLevel L m K k, c.source ∈ levelSitesOf k Ω → c.target ∈ levelSitesOf k Ω →
          AnalyticOnBondForms (smallInteriorForms Ω α₁) (fun A => scaledAverageAngle k U₀ A c) ∧
          (∀ A ∈ smallInteriorForms Ω α₁, ∀ A' ∈ smallInteriorForms Ω α₁,
            (∀ b ∈ interiorBonds (fineBlock c.source ∪ fineBlock c.target), A b = A' b) →
            scaledAverageAngle k U₀ A c = scaledAverageAngle k U₀ A' c) ∧
          ∀ (A : FineBond L m K → ComplexMatrix2) (a : ℝ), IsBondForm complexLieAlgebra A →
            (∀ b ∈ interiorBonds Ω, ComplexMatrix2.operatorNorm (A b) ≤ a) → a < α₁ →
            ComplexMatrix2.operatorNorm (averageAngleRemainder k U₀ A c) ≤
                N.remainderBound * a ^ 2 ∧
              N.remainderBound * a ^ 2 < N.remainderBound * α₁ ^ 2
def averageExpansionRemainderBound : ℝ :=
  Classical.epsilon fun C₂ => ∀ L : ℕ, Odd L → 1 < L →
    ∃ c₄, IsAverageExpansionConstants L ⟨C₂, c₄⟩
def averageExpansionConstants (L : ℕ) : AverageExpansionConstants :=
  ⟨averageExpansionRemainderBound,
    Classical.epsilon fun c₄ =>
      IsAverageExpansionConstants L ⟨averageExpansionRemainderBound, c₄⟩⟩
end YangMills.Construction.BackgroundField
