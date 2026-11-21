import YangMills.Construction.Towers.DilationCarriesObjectsAtAnIndexOfATower
import YangMills.Construction.Towers.PropertiesOfTheDilationOfATower
import Mathlib
set_option autoImplicit false
open Set
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.Tower.ScalingPreservesObjectsAtLevel
open YangMills.Construction.TorusMetric (torusProj torusSupNorm supNormVec)
theorem supNormVec_smul {c : ℝ} (hc : 0 ≤ c) (w : Fin 4 → ℝ) :
    supNormVec (c • w) = c * supNormVec w := by
  unfold supNormVec
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun μ => |w μ|) (Finset.mem_univ μ)) hc
  · obtain ⟨μ, -, hμ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun μ => |w μ|)
    rw [hμ, ← abs_of_nonneg hc, ← abs_mul, abs_of_nonneg hc]
    exact Finset.le_sup' (fun μ => |(c • w) μ|) (Finset.mem_univ μ)
section Periodic
variable {L n k j : ℕ}
theorem scaling_torusProj (hL : 0 < L) (x : Fin 4 → ℝ) :
    scaling hL n k j (torusProj (PeriodicLattice.torusSide L n) x) =
      torusProj (PeriodicLattice.torusSide L (scaledExponent n k j)) ((L : ℝ) ^ (k - j) • x) :=
  scaling_mk hL x
theorem torusSupNorm_scaling (hL : 0 < L) (z : PeriodicLattice.FourTorus L n) :
    torusSupNorm (scaling hL n k j z) = (L : ℝ) ^ (k - j) * torusSupNorm z := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hc : (0 : ℝ) < (L : ℝ) ^ (k - j) := pow_pos hLpos _
  have himage : supNormVec '' (torusProj (PeriodicLattice.torusSide L (scaledExponent n k j)) ⁻¹'
        {scaling hL n k j z}) =
      ((L : ℝ) ^ (k - j)) • (supNormVec '' (torusProj (PeriodicLattice.torusSide L n) ⁻¹' {z})) := by
    ext t
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : torusProj (PeriodicLattice.torusSide L (scaledExponent n k j)) w =
          scaling hL n k j z := hw
      have hcw : ((L : ℝ) ^ (k - j)) • (((L : ℝ) ^ (k - j))⁻¹ • w) = w :=
        smul_inv_smul₀ hc.ne' w
      refine ⟨supNormVec (((L : ℝ) ^ (k - j))⁻¹ • w), ⟨_, ?_, rfl⟩, ?_⟩
      · apply (scaling hL n k j).injective
        rw [scaling_torusProj, hcw, hw']
      · show ((L : ℝ) ^ (k - j)) • supNormVec (((L : ℝ) ^ (k - j))⁻¹ • w) = supNormVec w
        rw [smul_eq_mul, ← supNormVec_smul hc.le, hcw]
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      have hw' : torusProj (PeriodicLattice.torusSide L n) w = z := hw
      refine ⟨((L : ℝ) ^ (k - j)) • w, ?_, ?_⟩
      · show torusProj _ _ = _
        rw [← scaling_torusProj, hw']
      · show supNormVec _ = ((L : ℝ) ^ (k - j)) • supNormVec w
        rw [smul_eq_mul, supNormVec_smul hc.le]
  rw [torusSupNorm, himage, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
  rfl
theorem image_cubeAround (hL : 0 < L) (hj : j ≤ k) {i : ℕ} (y : Vertex L n k i) :
    scaling hL n k j '' PeriodicLattice.cubeAround y =
      PeriodicLattice.cubeAround (scaleVertex hL hj i y) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hc : (0 : ℝ) < (L : ℝ) ^ (k - j) := pow_pos hLpos _
  have hmem : ∀ x : PeriodicLattice.FourTorus L n,
      scaling hL n k j x ∈ PeriodicLattice.cubeAround (scaleVertex hL hj i y) ↔
        x ∈ PeriodicLattice.cubeAround y := by
    intro x
    show torusSupNorm (scaling hL n k j x - (scaleVertex hL hj i y :
        PeriodicLattice.FourTorus L (scaledExponent n k j))) ≤
        PeriodicLattice.meshSize L (PeriodicLattice.levelDepth j i) / 2 ↔
      torusSupNorm (x - (y : PeriodicLattice.FourTorus L n)) ≤
        PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k i) / 2
    rw [coe_scaleVertex, ← map_sub, torusSupNorm_scaling, ← pow_mul_meshSize_levelDepth hL hj i,
      mul_div_assoc]
    exact mul_le_mul_iff_right₀ hc
  ext x'
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).2 hx
  · intro hx'
    obtain ⟨x, rfl⟩ := (scaling hL n k j).surjective x'
    exact ⟨x, (hmem x).1 hx', rfl⟩
theorem preservesAtLevel_torus (hL : 0 < L) (hj : j ≤ k) (hP : ScalingOnTorus hL hj n) {i : ℕ}
    (hi : i ≤ j) : ScalingPreservesAtLevel hL hj n i := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hexp : ((scaledExponent n k j : ℕ) : ℤ) + PeriodicLattice.levelDepth j i =
      (n : ℤ) + PeriodicLattice.levelDepth k i := by
    simp only [scaledExponent, PeriodicLattice.levelDepth]
    push_cast [Nat.cast_sub hj]
    ring
  refine ⟨fun r hr y => ?_, fun x x' μ c => ?_, fun x x' μ c h => ?_⟩
  · have hdepth : ∀ m : ℕ, m = k ∨ m = j →
        PeriodicLattice.levelDepth m (i - r) = PeriodicLattice.levelDepth m i + (r : ℤ) := by
      intro m _
      simp only [PeriodicLattice.levelDepth]
      push_cast [Nat.cast_sub hr]
      ring
    have hlat := (hP.atLevel (i - r) (by omega)).image_sublattice
    rw [hdepth k (Or.inl rfl), hdepth j (Or.inr rfl)] at hlat
    simp only [PeriodicLattice.refinedBlock]
    rw [image_inter (scaling hL n k j).injective, image_cubeAround hL hj y, hlat]
  · simp only [PeriodicLattice.IsAxialDisplacement]
    rw [hexp]
    exact and_congr_left' ((hP.atLevel i hi).sub_eq_step_iff x x' μ c)
  · refine (hP.atLevel i hi).axialPath x x' μ c (eq_add_of_sub_eq' h.1) ?_
    have hb := h.2
    have hpow : (L : ℝ) ^ ((n : ℤ) + PeriodicLattice.levelDepth k i) * meshAt L k i =
        PeriodicLattice.torusSide L n / 2 := by
      rw [meshAt, ← zpow_add₀ hLpos.ne', PeriodicLattice.torusSide]
      simp only [PeriodicLattice.levelDepth]
      rw [show (n : ℤ) + ((k : ℤ) - (i : ℤ)) + ((i : ℤ) - (k : ℤ)) = (n : ℤ) by ring, zpow_natCast]
      ring
    rw [← hpow]
    exact mul_lt_mul_of_pos_right hb (zpow_pos hLpos _)
end Periodic
section Unbounded
variable {L k j : ℕ}
theorem scaling_axisSum (hL : 0 < L) (y : InfiniteLattice.AmbientSpace) (ν : Fin 4 → ℤ) (a : ℝ) :
    FullSpace.scaling hL k j (y + ∑ μ, Pi.single μ ((ν μ : ℝ) * a)) =
      FullSpace.scaling hL k j y + ∑ μ, Pi.single μ ((ν μ : ℝ) * ((L : ℝ) ^ (k - j) * a)) := by
  rw [map_add]
  congr 1
  rw [FullSpace.scaling_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Pi.single_smul, smul_eq_mul]
  congr 1
  ring
theorem preservesAtLevel_fullSpace (hL : 0 < L) (hj : j ≤ k) (hP : FullSpace.ScalingOnSpace hL hj)
    {i : ℕ} (hi : i ≤ j) : FullSpace.PreservesAtLevel hL hj i := by
  refine ⟨fun r _ y => ?_, fun x x' μ c h => ?_⟩
  · ext x'
    constructor
    · rintro ⟨x, ⟨ν, hν, rfl⟩, rfl⟩
      refine ⟨ν, hν, ?_⟩
      rw [scaling_axisSum, pow_mul_meshAt hL hj]
      rfl
    · rintro ⟨ν, hν, rfl⟩
      refine ⟨_, ⟨ν, hν, rfl⟩, ?_⟩
      rw [scaling_axisSum, pow_mul_meshAt hL hj]
      rfl
  · exact (hP.atLevel i hi).axisPath x x' μ c (eq_add_of_sub_eq' h)
end Unbounded
theorem statement_of_scalingProperties (h : ScalingPropertiesStatement) : Statement := by
  intro L hL hS k j hj _ i hi
  obtain ⟨h₁, h₂⟩ := h L k j hS hj
  exact ⟨fun n hn => preservesAtLevel_torus hL hj (h₁ n hn) hi, preservesAtLevel_fullSpace hL hj h₂ hi⟩
end YangMills.Construction.Tower.ScalingPreservesObjectsAtLevel
end
