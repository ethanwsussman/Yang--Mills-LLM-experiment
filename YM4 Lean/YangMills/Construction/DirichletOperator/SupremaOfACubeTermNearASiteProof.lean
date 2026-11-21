import YangMills.Construction.DirichletOperator.BoundsAtOneCubeProof
import YangMills.Construction.DirichletOperator.ComparisonEstimatesOnTheTorusProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeTorus (levelSpacing)
open YangMills.Construction.LeibnizHolder (supBondOn supTensorOn BondProductRules bondCommutator)
open YangMills.Construction.ApproxInverseScales (blockLowerBound outerCube)
noncomputable section
namespace YangMills.Construction.NearSiteSuprema
section Lengths
variable {S : ℝ}
theorem supNorm_sub_le_add (p q r : PeriodicTorus 4 S) :
    supNorm (p - r) ≤ supNorm (p - q) + supNorm (q - r) := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.supNorm_sub_le <;> assumption
theorem supNorm_sub_comm (p q : PeriodicTorus 4 S) : supNorm (p - q) = supNorm (q - p) := by apply _root_.YangMills.Construction.PartitionCubes.TorusComponents.supNorm_sub_comm <;> assumption
theorem supNorm_unitStep_le {ξ : ℝ} (hξ : 0 < ξ) (ν : Fin 4) :
    supNorm ((unitStep 4 S ξ ν : LatticeSite 4 S ξ) : PeriodicTorus 4 S) ≤ ξ := by apply _root_.YangMills.Construction.TorusComparisonProof.supNorm_unitStep_le <;> assumption
end Lengths
variable {𝒮 : NestedRegions}
section Suprema
variable {𝒯 : NestedRegions} {X : Set 𝒯.Point}
theorem supBondOn_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ supBondOn X f :=
  Real.sSup_nonneg (by rintro _ ⟨b, -, rfl⟩; exact abs_nonneg _)
theorem abs_le_supBondOn [Finite 𝒯.FineBond] (f : 𝒯.FineBond → ℝ) {c : 𝒯.FineBond}
    (hc : (c.source : 𝒯.Point) ∈ X) : |f c| ≤ supBondOn X f := by
  refine le_csSup ?_ ⟨c, hc, rfl⟩
  refine ((Set.finite_range fun b : 𝒯.FineBond => |f b|).subset ?_).bddAbove
  rintro _ ⟨b, -, rfl⟩
  exact ⟨b, rfl⟩
end Suprema
def pullback (𝔏 : CubeSystem 𝒮) (v : 𝔏.setting.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => v (𝔏.mapBond b)
section Pullback
variable {𝔏 : CubeSystem 𝒮} {y : 𝒮.Point} {ρ : ℝ}
end Pullback
theorem scale_pos (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem thirteen_le_L_real : (13 : ℝ) ≤ 𝒮.L := by exact_mod_cast 𝒮.thirteen_le_L
theorem ξ_le_scale (n : ℕ) : 𝒮.ξ ≤ 𝒮.scale n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.ξ_le_scale <;> assumption
theorem mem_thicken_of_near {M : ℕ} (Q : LevelCube 𝒮 M) (y : 𝒮.Point) {ρ : ℝ}
    (hmeet : (Q.supp ∩ cubeHalfSide y (4 * ρ)).Nonempty)
    (hρ : ρ ≤ (𝒮.L : ℝ) * levelSpacing Q) (hM : (𝒮.L : ℝ) ^ 5 ≤ M) (x : 𝒮.Point)
    (hx : supNorm (x - y) ≤ 4 * ρ) : x ∈ Q.thicken (5 / 6) := by
  obtain ⟨q, hq, hqy⟩ := hmeet
  have hqy' : supNorm (q - y) ≤ 2 * (4 * ρ) / 2 := hqy
  have hxq : supNorm (x - q) ≤ 8 * ρ := by
    have h1 := supNorm_sub_le_add x y q
    rw [supNorm_sub_comm y q] at h1
    linarith
  have hs : 0 < levelSpacing Q := scale_pos Q.level
  have hL := thirteen_le_L_real (𝒮 := 𝒮)
  have h3 : (58 : ℝ) ≤ (𝒮.L : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13) hL 3
    norm_num at this
    linarith
  have hM' : 58 * (𝒮.L : ℝ) ^ 2 ≤ M := by
    have := mul_le_mul_of_nonneg_left h3 (sq_nonneg (𝒮.L : ℝ))
    have e : (𝒮.L : ℝ) ^ 5 = (𝒮.L : ℝ) ^ 2 * (𝒮.L : ℝ) ^ 3 := by ring
    linarith
  have hbound : 8 * ρ ≤ 5 / 6 * mollifyRadius 𝒮 M Q.level := by
    have e : mollifyRadius 𝒮 M Q.level = (M : ℝ) * levelSpacing Q / (6 * (𝒮.L : ℝ)) := rfl
    have e' : 5 / 6 * ((M : ℝ) * levelSpacing Q / (6 * (𝒮.L : ℝ))) =
        5 * (M : ℝ) * levelSpacing Q / (36 * (𝒮.L : ℝ)) := by
      field_simp
      ring
    rw [e, e', le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right hM' hs.le
    have h2 := mul_le_mul_of_nonneg_right hρ (by positivity : 0 ≤ 8 * (36 * (𝒮.L : ℝ)))
    nlinarith
  have : supSetDist {x} Q.supp ≤ ENNReal.ofReal (supNorm (x - q)) :=
    iInf₂_le_of_le x rfl (iInf₂_le q hq)
  exact this.trans (ENNReal.ofReal_le_ofReal (hxq.trans hbound))
theorem finite_fineBond (hl : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
end YangMills.Construction.NearSiteSuprema
