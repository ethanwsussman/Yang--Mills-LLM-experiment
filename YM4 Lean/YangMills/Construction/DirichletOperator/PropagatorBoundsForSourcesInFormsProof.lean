import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.InequalitiesOnCubesOfTheFirstKindProof
import YangMills.Construction.DirichletOperator.PropagatorBoundsForDivergenceSourcesProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.Propagator YangMills.Construction.PropagatorThresholds YangMills.Construction.RemainderEstimates YangMills.Construction.Weighted
noncomputable section
namespace YangMills.Construction.DirichletOperator.OneFormSourcePropagator
structure IsRealSeminorm {V : Type} [AddCommGroup V] [Module ℝ V] (q : V → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ q v
  add_le : ∀ v w, q (v + w) ≤ q v + q w
  smul_le : ∀ (a : ℝ) (v : V), q (a • v) ≤ |a| * q v
section RealSeminorms
variable {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
theorem IsRealSeminorm.comp_linear {q : W → ℝ} (hq : IsRealSeminorm q) {T : V → W}
    (hT : IsLinearMap ℝ T) : IsRealSeminorm fun v => q (T v) where
  nonneg v := hq.nonneg _
  add_le v w := by rw [hT.map_add]; exact hq.add_le _ _
  smul_le a v := by rw [hT.map_smul]; exact hq.smul_le _ _
theorem IsRealSeminorm.map_zero {q : V → ℝ} (hq : IsRealSeminorm q) : q 0 = 0 := by
  have h := hq.smul_le 0 0
  simp only [smul_zero, abs_zero, zero_mul] at h
  exact le_antisymm h (hq.nonneg 0)
end RealSeminorms
variable {𝒮 : NestedRegions}
section Norms
variable [Finite 𝒮.FineBond]
end Norms
theorem finite_fineBond (hTL : Torus.TorusLengthsStatement) {K m M R₁ : ℕ}
    (hab : IsAboveThresholds 𝒮 K m M R₁) : Finite 𝒮.FineBond := by
  have hL : (0 : ℝ) < 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒮.L)
  have hside : 𝒮.side = ((2 * 𝒮.L ^ (m + K) : ℕ) : ℝ) * 𝒮.ξ := by
    rw [hab.unitSeparated.side_eq, hab.unitSeparated.ξ_eq]
    simp only [Torus.unitSide, Torus.unitSpacing]
    have e : (m : ℤ) + (K : ℤ) - (𝒮.s : ℤ) = ((m + K : ℕ) : ℤ) + -(𝒮.s : ℤ) := by
      push_cast; ring
    rw [e, zpow_add₀ hL.ne', zpow_natCast]
    push_cast
    ring
  have hk : 0 < 2 * 𝒮.L ^ (m + K) := by
    have : 0 < 𝒮.L ^ (m + K) := pow_pos (by have := 𝒮.thirteen_le_L; omega) _
    omega
  have hfin := ((hTL 4 𝒮.side 𝒮.side_pos).2 𝒮.ξ _ 𝒮.ξ_pos hk hside).finite
  have : Finite 𝒮.FineSite := hfin.to_subtype
  exact Finite.of_injective (fun b : 𝒮.FineBond => (b.source, b.dir)) fun b b' h => by
    cases b; cases b'; simp_all
theorem levelScale_pos (y : 𝒮.Point) : 0 < 𝒮.levelScale y := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.levelScale_pos <;> assumption
theorem levelScale_le_one {K m M R₁ : ℕ} (hab : IsAboveThresholds 𝒮 K m M R₁) {y : 𝒮.Point}
    (hy : y ∈ 𝒮.allCentres) : 𝒮.levelScale y ≤ 1 := by
  have hL1 : (1 : ℝ) ≤ 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒮.L)
  have hL : (0 : ℝ) < 𝒮.L := by linarith
  obtain ⟨n, hn, hy⟩ := hy
  have hi : Torus.shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y ≤ n := Nat.sInf_le hy
  show (𝒮.L : ℝ) ^ ((Torus.shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y : ℕ) : ℤ) * 𝒮.ξ ≤ 1
  generalize Torus.shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y = k at hi
  rw [hab.unitSeparated.ξ_eq]
  simp only [Torus.unitSpacing]
  rw [← zpow_add₀ hL.ne']
  refine zpow_le_one_of_nonpos₀ hL1 ?_
  omega
theorem anchoredIn_outerCube {y : 𝒮.Point} {b : 𝒮.FineBond}
    (hb : (b.source : 𝒮.Point) ∈ wideCell y) :
    AnchoredIn (ApproxInverseScales.outerCube y) b := by apply _root_.YangMills.Construction.DivSourceEstimate.anchoredIn_outerCube <;> assumption
theorem wideCell_subset_outerCube (y : 𝒮.Point) :
    wideCell y ⊆ ApproxInverseScales.outerCube y := by apply _root_.YangMills.Construction.DivSourceEstimate.wideCell_subset_outerCube <;> assumption
theorem weightedDist_nonneg (y y' : 𝒮.Point) : 0 ≤ 𝒮.weightedDist y y' := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
theorem pNorm_nonneg (p : NormExponent) (f : 𝒮.FineBond → ℝ) :
    0 ≤ (formCutSpace 𝒮).pNorm p f := by apply _root_.YangMills.Construction.DivSourceEstimate.pNorm_nonneg <;> assumption
def cellWeight (p : NormExponent) (cc : ℝ) (y y' : 𝒮.Point) (J : 𝒮.FineBond → ℝ) : ℝ :=
  2 * cc * |separatedSumConst 4 𝒮.L (mainRate 𝒮.L / 2)| *
    Real.exp (-(mainRate 𝒮.L / 2) * 𝒮.weightedDist y y') * (formCutSpace 𝒮).pNorm p J
def IsDominated (M : ℕ) (y y' : 𝒮.Point) (R : OperatorFunctional 𝒮) (ρ : ℝ) : Prop :=
  ∀ q : (𝒮.FineBond → ℝ) → ℝ, IsRealSeminorm q → ∀ (p : NormExponent) (cc : ℝ), 0 ≤ cc →
    (∀ f ∈ 𝒮.oneForms, ∑ᶠ Q ∈ PartitionCubes.active 𝒮 M, q (Q.invTerm f) ≤
      cc * ApproxInverseScales.weightedSourceSum ((formCutSpace 𝒮).pNorm p) y f) →
    ∀ J, IsOneFormIn (𝒮.cellOf y') J → R (fun T => q (T J)) ≤ ρ * cellWeight p cc y y' J
section Suprema
variable [Finite 𝒮.FineBond]
theorem abs_le_supBond (f : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond) : |f b| ≤ supBond f :=
  le_ciSup (f := fun b => ‖f b‖) (finite_range _).bddAbove b
omit [Finite 𝒮.FineBond] in
theorem supBond_nonneg (f : 𝒮.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem abs_le_supTensor {r : ℕ} (J : 𝒮.Tensor r) (ν : Fin r → Fin 4) (b : 𝒮.FineBond) :
    |J ν b| ≤ supTensor J :=
  (abs_le_supBond (J ν) b).trans
    (le_ciSup (f := fun ν => supBond (J ν)) (finite_range _).bddAbove ν)
omit [Finite 𝒮.FineBond] in
theorem supTensor_nonneg {r : ℕ} (J : 𝒮.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
end Suprema
theorem supSite_nonneg (ζ : 𝒮.FineSite → ℝ) : 0 ≤ supSite ζ :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem holderSite_nonneg (α lam : ℝ) (ζ : 𝒮.FineSite → ℝ) : 0 ≤ holderSite α lam ζ := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderSite_nonneg <;> assumption
theorem mul_four_le {B₀ B t e E N : ℝ} (hB₀ : 0 ≤ B₀) (hB : B₀ ≤ B) (ht : 0 ≤ t) (he : 0 ≤ e)
    (hE : e ≤ E) (hN : 0 ≤ N) : B₀ * t * e * N ≤ B * t * E * N := by
  have h₁ : B₀ * t ≤ B * t := mul_le_mul_of_nonneg_right hB ht
  have h₂ : B₀ * t * e ≤ B * t * E :=
    mul_le_mul h₁ hE he ((mul_nonneg hB₀ ht).trans h₁)
  exact mul_le_mul_of_nonneg_right h₂ hN
end YangMills.Construction.DirichletOperator.OneFormSourcePropagator
