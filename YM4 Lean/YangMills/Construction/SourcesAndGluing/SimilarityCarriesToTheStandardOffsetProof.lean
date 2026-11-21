import YangMills.Construction.SourcesAndGluing.SimilarityCarriesToTheStandardOffset
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.OriginNormalization
variable {D : GluingSetup}
theorem centeringPoint_mem_gridPoints (g : CubicGrid D) (hg : g.IsMirrorGrid) :
    g.centeringPoint ∈ D.gridPoints := by
  choose i hi using hg
  refine ⟨fun μ => -i μ - 1, fun μ => ?_⟩
  simp only [CubicGrid.centeringPoint, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Conventions.onesVector, hi μ]
  push_cast
  ring
theorem mappedGrid_origin (g : CubicGrid D) (hg : g.IsMirrorGrid) (Ψ : LatticeRescaling D)
    (hbase : Ψ.base = g.centeringPoint) :
    (Ψ.mappedGrid g hg).origin =
      (-(1 / 2) * Ψ.scaleExponent.target.mesh) • Conventions.onesVector := by
  funext μ
  change (D.L : ℝ) ^ Ψ.exp * (g.origin μ + Ψ.base μ) = _
  rw [hbase, Ψ.target_mesh_eq]
  simp only [CubicGrid.centeringPoint, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Conventions.onesVector]
  ring
theorem mappedGrid_isMirrorGrid (g : CubicGrid D) (hg : g.IsMirrorGrid) (Ψ : LatticeRescaling D)
    (hbase : Ψ.base = g.centeringPoint) : (Ψ.mappedGrid g hg).IsMirrorGrid := by
  intro μ
  refine ⟨-1, ?_⟩
  rw [mappedGrid_origin g hg Ψ hbase]
  simp only [Pi.smul_apply, smul_eq_mul, Conventions.onesVector]
  push_cast
  ring
def normalizedCheckerboard (Ψ : LatticeRescaling D) (j : ℤ)
    (hlow : -((D.K : ℕ) : ℤ) ≤ j) (hhigh : j ≤ ((D.m : ℕ) : ℤ)) :
    ReflectionPositivity.CheckerboardDatum D.L where
  depth := (Ψ.scaleExponent.target.K : ℕ)
  sizeExp := (Ψ.scaleExponent.target.m : ℕ)
  cellExp := j + Ψ.exp
  basePoint := (-(1 / 2) * Ψ.scaleExponent.target.mesh) • Conventions.onesVector
  one_le_depth_add_sizeExp := by
    have := Ψ.scaleExponent.target.K.pos
    omega
  neg_depth_le_cellExp := by
    have : ((Ψ.scaleExponent.target.K : ℕ) : ℤ) = ((D.K : ℕ) : ℤ) - Ψ.exp :=
      Ψ.scaleExponent.target_K
    omega
  cellExp_le_sizeExp := by
    have : ((Ψ.scaleExponent.target.m : ℕ) : ℤ) = ((D.m : ℕ) : ℤ) + Ψ.exp :=
      Ψ.scaleExponent.target_m
    omega
  basePoint_mem μ := by
    refine ⟨-1, ?_⟩
    change (-(1 / 2) * Ψ.scaleExponent.target.mesh) * 1 = Ψ.scaleExponent.target.mesh * _
    push_cast
    ring
theorem exp_add_nonneg_of_one_le (Ψ : LatticeRescaling D) {j : ℤ}
    (h : 1 ≤ (D.L : ℝ) ^ Ψ.exp * (D.L : ℝ) ^ j) : 0 ≤ j + Ψ.exp := by
  have hL := D.one_lt_L
  rw [← zpow_add₀ (by linarith), ← zpow_zero (D.L : ℝ)] at h
  have := (zpow_le_zpow_iff_right₀ hL).1 h
  omega
theorem rescalingNormalizesOriginClaim_holds : RescalingNormalizesOriginClaim := by
  intro D g hg
  refine ⟨centeringPoint_mem_gridPoints g hg, fun Ψ hbase => ?_⟩
  have horigin := mappedGrid_origin g hg Ψ hbase
  refine ⟨?_, fun hone j hj => ?_⟩
  · rw [(Ψ.mappedGrid g hg).mirrorOrigin_of_isMirrorGrid (mappedGrid_isMirrorGrid g hg Ψ hbase),
      horigin]
  · have hscale := g.isGridScale
    rw [hj] at hscale
    obtain ⟨hlow, hhigh⟩ := (D.isGridScale_zpow_iff j).1 hscale
    rw [hj] at hone
    refine ⟨normalizedCheckerboard Ψ j hlow hhigh, Ψ.scaleExponent.target_K,
      Ψ.scaleExponent.target_m, rfl, rfl, ?_⟩
    refine ⟨(Ψ.scaleExponent.target.K).pos, (Ψ.scaleExponent.target.m).pos,
      exp_add_nonneg_of_one_le Ψ hone, rfl⟩
end YangMills.Construction.SourcesAndGluing.OriginNormalization
end
