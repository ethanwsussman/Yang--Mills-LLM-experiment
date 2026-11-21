import YangMills.Construction.LawInAState.ConcentrationOfQuadraticForms
import Mathlib
set_option autoImplicit false
noncomputable section
open Matrix
namespace YangMills.Construction.QuadraticConcentration
variable {ι V S : Type}
open Classical in
structure DominatedBySites [Fintype ι] [Fintype S] (g : ι → S → ℝ) (Y : V → Finset S) (M : V → Matrix ι ι ℝ)
    (Near : V → V → Prop) (In : Set ι) (c₀ G Nc τ τ₂ : ℝ) : Prop where
  symm : ∀ v, (M v).IsSymm
  nonneg : ∀ i y, 0 ≤ g i y
  entry_le : ∀ v i j, |M v i j| ≤ c₀ * ∑ y ∈ Y v, g i y * g j y
  col_sum_le : ∀ y, ∑ i, g i y ≤ G
  row_sum_le : ∀ i, ∑ y, g i y ≤ G
  card_le : ∀ v, ((Y v).card : ℝ) ≤ Nc
  overlap_le : ∀ v w, ¬ Near v w → ∀ y ∈ Y v, ∀ y' ∈ Y w, ∑ i, g i y * g i y' ≤ τ
  outside_mass_le : ∀ v, ∀ y ∈ Y v, ∑ i ∈ Finset.univ.filter (fun i => i ∉ In), g i y ≤ τ₂
def vectorMass (c₀ G Nc τ₂ φ₀ Fm : ℝ) : ℝ := c₀ * G * Nc * (G * φ₀ ^ 2 + τ₂ * Fm ^ 2)
def sitesDominatedFormFamilyStatement : Prop :=
  ∀ (ι V S : Type) [Fintype ι] [DecidableEq ι] [Fintype S] (g : ι → S → ℝ) (Y : V → Finset S) (M : V → Matrix ι ι ℝ)
    (Near : V → V → Prop) (In : Set ι) (c₀ G Nc τ τ₂ φ₀ Fm A φ ε : ℝ) (F : ι → ℝ),
    0 ≤ c₀ → 0 ≤ G → 0 ≤ Nc → 0 ≤ τ → 0 ≤ τ₂ → 0 ≤ φ₀ → 0 ≤ Fm → 0 ≤ ε →
    DominatedBySites g Y M Near In c₀ G Nc τ τ₂ → (∀ i ∈ In, |F i| ≤ φ₀) → (∀ i, |F i| ≤ Fm) →
    c₀ ^ 2 * G ^ 4 * Nc ≤ A → c₀ * G ^ 2 * vectorMass c₀ G Nc τ₂ φ₀ Fm ≤ A * φ ^ 2 →
    vectorMass c₀ G Nc τ₂ φ₀ Fm ≤ A * φ ^ 2 →
    c₀ ^ 2 * Nc ^ 2 * τ ^ 2 ≤ ε → c₀ ^ 2 * τ * Nc * G ^ 2 ≤ ε → Fm ^ 2 * c₀ ^ 2 * G ^ 2 * Nc ^ 2 * τ ≤ ε →
      IsAdmissibleFormFamily F M Near (c₀ * G ^ 2) A φ ε
end YangMills.Construction.QuadraticConcentration
end
