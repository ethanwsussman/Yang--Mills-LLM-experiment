import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.Jets
import YangMills.Construction.Towers.AveragesAreContractions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BoundedExpansionSymbol
open YangMills.Construction.Tower.SmoothingContraction (OpNormLE)
structure RowsBounded (P Q : PeriodicData) (Z : Q.Carrier → P.Carrier → ℂ)
    (S : Q.Carrier → Set P.Carrier) (L : Q.Carrier → Q.Carrier → P.Carrier → ℂ) (β r : ℝ) (m : ℕ) :
    Prop where
  support_finite : ∀ j, (S j).Finite
  eq_zero_of_not_mem : ∀ j i, i ∉ S j → Z j i = 0
  expansion_eq : ∀ j, ∀ i ∈ S j, Z j i = L j j i
  opNorm_le : ∀ j, OpNormLE P Q (L j) β
  dist_le : ∀ j, ∀ i ∈ S j, ∀ μ, |P.pos i μ - Q.pos j μ| ≤ r
  encard_le : ∀ i, {j | i ∈ S j}.encard ≤ m
def SymbolNormBound : Prop :=
  ∀ P Q : PeriodicData, IsPeriodic P → IsPeriodic Q →
    ∀ Z : Q.Carrier → P.Carrier → ℂ, IsFiniteRangeAllRates P Q Z →
    ∀ (S : Q.Carrier → Set P.Carrier) (L : Q.Carrier → Q.Carrier → P.Carrier → ℂ) (β r : ℝ) (m : ℕ),
      0 ≤ β → 0 ≤ r → RowsBounded P Q Z S L β r m →
      ∀ k : Fin 4 → ℂ, quotHomNorm (symbolHom P Q Z k) ≤
        ENNReal.ofReal (Real.sqrt m * β * Real.exp (r * ∑ μ, |(k μ).im|))
end YangMills.Construction.PeriodicOperators.BoundedExpansionSymbol
end
