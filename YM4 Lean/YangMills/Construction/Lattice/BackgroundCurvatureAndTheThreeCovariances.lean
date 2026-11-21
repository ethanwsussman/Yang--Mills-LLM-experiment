import YangMills.Construction.Lattice.ConditionalExpectationsOfTheFreeField
import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Lattice.LinearAveragesOfCochains
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice
section Opposite
variable {L m : ℕ} {j j' : ℤ}
theorem cochainAverage_opposite (hL : 1 < L) (hj : -(m : ℤ) < j) (α : Bond L m j' → ℝ)
    (c : Bond L m j) : cochainAverage α c.opposite = -cochainAverage α c := by
  have hopp : c.opposite.opposite = c := rfl
  by_cases hc : c.IsPositivelyOriented
  · have h := Bond.opposite_not_isPositivelyOriented hL hj hc
    simp only [cochainAverage, if_pos hc, if_neg h, hopp]
  · have h : c.opposite.IsPositivelyOriented := by
      obtain ⟨μ, h | h⟩ := c.isNeighbour
      · exact absurd ⟨μ, h⟩ hc
      · refine ⟨μ, ?_⟩
        change c.source - c.target = _
        rw [← neg_sub, h, neg_neg]
    simp only [cochainAverage, if_pos h, if_neg hc, neg_neg]
theorem cochainAverageIterate_mem {K n : ℕ} (hL : 1 < L) (hm : 0 < m) (hn : n ≤ K)
    {α : BondAtLevel L m K 0 → ℝ} (hα : α ∈ bondCochains L m (levelDepth K 0)) :
    cochainAverageIterate n α ∈ bondCochains L m (levelDepth K n) := by
  cases n with
  | zero => exact hα
  | succ n =>
    intro c
    exact cochainAverage_opposite hL (by simp only [levelDepth]; omega) _ c
end Opposite
section Coarse
variable (S : Conventions.StandingParameters)
def finestFreePotential (ω : ExactPlaquetteCochain S.L S.m ((S.K : ℕ) : ℤ)) :
    bondCochains S.L S.m (levelDepth S.K 0) :=
  freeGaugePotential ω
def averagedFreePotential (s : ℕ) (ω : ExactPlaquetteCochain S.L S.m ((S.K : ℕ) : ℤ)) :
    bondCochains S.L S.m (levelDepth S.K (S.K - s)) :=
  ⟨cochainAverageIterate (S.K - s) (finestFreePotential S ω).1,
    cochainAverageIterate_mem (lt_of_lt_of_le (by norm_num) S.isAdmissible.2) S.m.pos
      (Nat.sub_le _ _) (finestFreePotential S ω).2⟩
abbrev FormVanishingOnClosed (s : ℕ) : Type :=
  {θ : bondCochains S.L S.m (levelDepth S.K (S.K - s)) →ₗ[ℝ] ℝ //
    ∀ h ∈ closedBondCochains S.L S.m (levelDepth S.K (S.K - s)), θ h = 0}
@[instance_reducible]
def coarseSigmaAlgebra (s : ℕ) : MeasurableSpace (ExactPlaquetteCochain S.L S.m ((S.K : ℕ) : ℤ)) :=
  ⨆ θ : FormVanishingOnClosed S s,
    MeasurableSpace.comap (fun ω => θ.1 (averagedFreePotential S s ω)) inferInstance
end Coarse
section CondExp
variable {L m : ℕ} {j : ℤ} [Finite (Plaquette L m j)]
def freeCondExp (𝓕 : MeasurableSpace (ExactPlaquetteCochain L m j))
    (Y : ExactPlaquetteCochain L m j → ℝ) : ExactPlaquetteCochain L m j → ℝ :=
  Classical.epsilon (IsConditionalRepresentative 𝓕 Y)
def freeCurvatureCovariance (p q : Plaquette L m j) : ℝ :=
  freeMean fun ω => freeCurvatureAtPlaquette p ω * freeCurvatureAtPlaquette q ω
end CondExp
section Background
variable (S : Conventions.StandingParameters)
def backgroundCurvature (s : ℕ) (p : Plaquette S.L S.m ((S.K : ℕ) : ℤ))
    (ω : ExactPlaquetteCochain S.L S.m ((S.K : ℕ) : ℤ)) : ℝ :=
  freeCondExp (coarseSigmaAlgebra S s) (freeCurvatureAtPlaquette p) ω
def backgroundCurvatureCovariance (s : ℕ) (p q : Plaquette S.L S.m ((S.K : ℕ) : ℤ)) : ℝ :=
  freeMean fun ω => backgroundCurvature S s p ω * backgroundCurvature S s q ω
def fluctuationCurvatureCovariance (s : ℕ) (p q : Plaquette S.L S.m ((S.K : ℕ) : ℤ)) : ℝ :=
  freeCurvatureCovariance p q - backgroundCurvatureCovariance S s p q
theorem backgroundCurvatureCovariance_comm (s : ℕ) (p q : Plaquette S.L S.m ((S.K : ℕ) : ℤ)) :
    backgroundCurvatureCovariance S s p q = backgroundCurvatureCovariance S s q p := by
  simp only [backgroundCurvatureCovariance, mul_comm]
end Background
end YangMills.Construction.PeriodicLattice
