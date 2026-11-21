import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace Coercivity
variable {ι : Type}
def familyDivergence (d b : ι → Fin 4 → ℂ) (m : ι) : ℂ := ∑ μ, conj (d m μ) * b m μ
def weightedSiteSum (s : Finset ι) (v : ι → ℝ) (l : ι → ℂ) : ℂ := ∑ m ∈ s, (v m : ℂ) * l m
def weightedBondSum (s : Finset ι) (u b : ι → Fin 4 → ℂ) (μ : Fin 4) : ℂ := ∑ m ∈ s, u m μ * b m μ
def bondNormSq (b : ι → Fin 4 → ℂ) (m : ι) : ℝ := ∑ μ, ‖b m μ‖ ^ 2
def bondDirichlet (s : Finset ι) (D : ι → ℝ) (b : ι → Fin 4 → ℂ) : ℝ :=
  ∑ m ∈ s, D m * bondNormSq b m
def bondSobolevSq (s : Finset ι) (D : ι → ℝ) (b : ι → Fin 4 → ℂ) : ℝ :=
  ∑ m ∈ s, (D m + 1) * bondNormSq b m
def bondQuadraticForm (s : Finset ι) (D : ι → ℝ) (d : ι → Fin 4 → ℂ) (v : ι → ℝ)
    (u b : ι → Fin 4 → ℂ) : ℝ :=
  bondDirichlet s D b - ‖weightedSiteSum s v (familyDivergence d b)‖ ^ 2 +
    ∑ μ, ‖weightedBondSum s u b μ‖ ^ 2
def siteDirichlet (s : Finset ι) (D : ι → ℝ) (l : ι → ℂ) : ℝ := ∑ m ∈ s, D m * ‖l m‖ ^ 2
def siteSobolevSq (s : Finset ι) (D : ι → ℝ) (l : ι → ℂ) : ℝ :=
  ∑ m ∈ s, (D m + 1) * ‖l m‖ ^ 2
def siteQuadraticForm (s : Finset ι) (D : ι → ℝ) (v : ι → ℝ) (l : ι → ℂ) : ℝ :=
  siteDirichlet s D l + ‖weightedSiteSum s v l‖ ^ 2
def bondResolventWeight (s : Finset ι) (D : ι → ℝ) (u : ι → Fin 4 → ℂ) (μ : Fin 4) : ℝ :=
  ∑ m ∈ s, ‖u m μ‖ ^ 2 * (D m + 1)⁻¹
def siteResolventWeight (s : Finset ι) (D : ι → ℝ) (v : ι → ℝ) : ℝ :=
  ∑ m ∈ s, v m ^ 2 * (D m + 1)⁻¹
structure IsAdmissibleFamily (p r B T : ℝ) (s : Finset ι) (z : ι) (D : ι → ℝ)
    (d : ι → Fin 4 → ℂ) (v : ι → ℝ) (u : ι → Fin 4 → ℂ) (dc : Fin 4 → ℂ) : Prop where
  mem : z ∈ s
  eq_normSq : ∀ m ∈ s, D m = ∑ μ, ‖d m μ‖ ^ 2
  four_le : ∀ m ∈ s, m ≠ z → 4 ≤ D m
  le_bound : D z ≤ B
  site_lower : p ≤ v z
  bond_lower : ∀ μ, r ≤ ‖u z μ‖
  site_sum_sq : ∑ m ∈ s, v m ^ 2 = 1
  bond_sum_sq_le : ∀ μ, ∑ m ∈ s, ‖u m μ‖ ^ 2 ≤ 1
  deficit_le : 1 - v z ^ 2 ≤ T * D z
  mul_eq : ∀ m ∈ s, ∀ μ, u m μ * d m μ = dc μ * (v m : ℂ)
def FiniteFamilyCoercivity : Prop :=
  ∀ p r B T : ℝ, 0 < p → 0 < r → 0 < B → 0 < T →
    ∃ cXi ∈ Ioc (0 : ℝ) 1, ∃ cY ∈ Ioc (0 : ℝ) 1, ∃ cC ∈ Ioc (0 : ℝ) 1,
      ∀ (κ : Type) (s : Finset κ) (z : κ) (D : κ → ℝ) (d : κ → Fin 4 → ℂ) (v : κ → ℝ)
        (u : κ → Fin 4 → ℂ) (dc : Fin 4 → ℂ), IsAdmissibleFamily p r B T s z D d v u dc →
        (∀ b : κ → Fin 4 → ℂ, cXi * bondSobolevSq s D b ≤ bondQuadraticForm s D d v u b ∧
          bondQuadraticForm s D d v u b ≤ bondSobolevSq s D b) ∧
        (∀ l : κ → ℂ, cY * siteSobolevSq s D l ≤ siteQuadraticForm s D v l ∧
          siteQuadraticForm s D v l ≤ siteSobolevSq s D l) ∧
        (∀ μ, cC ≤ bondResolventWeight s D u μ) ∧ cC ≤ siteResolventWeight s D v
end Coercivity
end YangMills.Construction
end
