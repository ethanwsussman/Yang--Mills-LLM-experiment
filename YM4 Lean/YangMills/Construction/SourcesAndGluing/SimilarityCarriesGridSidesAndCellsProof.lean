import YangMills.Construction.SourcesAndGluing.SimilarityCarriesGridSidesAndCells
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.RescalingKeepsGridScalesAndCubes
variable {D : GluingSetup} (Ψ : LatticeRescaling D)
theorem pos_mul_mem_Icc_iff {p t s : ℝ} (hp : 0 < p) :
    p * t ∈ Icc 0 (p * s) ↔ t ∈ Icc 0 s := by
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨le_of_mul_le_mul_left (by simpa using hlo : p * 0 ≤ p * t) hp,
      le_of_mul_le_mul_left hhi hp⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨mul_nonneg hp.le hlo, mul_le_mul_of_nonneg_left hhi hp.le⟩
theorem pos_mul_mem_Ioo_iff {p t s : ℝ} (hp : 0 < p) :
    p * t ∈ Ioo 0 (p * s) ↔ t ∈ Ioo 0 s := by
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨lt_of_mul_lt_mul_left (by simpa using hlo : p * 0 < p * t) hp.le,
      lt_of_mul_lt_mul_left hhi hp.le⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨mul_pos hp hlo, mul_lt_mul_of_pos_left hhi hp⟩
theorem toSpace_apply (x : InfiniteLattice.AmbientSpace) (μ : Fin 4) :
    Ψ.toSpace x μ = (D.L : ℝ) ^ Ψ.exp * (x μ + Ψ.base μ) := rfl
theorem toSpace_surjective : Function.Surjective Ψ.toSpace := by
  intro y
  refine ⟨fun μ => ((D.L : ℝ) ^ Ψ.exp)⁻¹ * y μ - Ψ.base μ, ?_⟩
  funext μ
  rw [toSpace_apply]
  have hp := Ψ.zpow_L_pos.ne'
  field_simp
  ring
theorem toSpace_image_eq_of_iff {s t : Set InfiniteLattice.AmbientSpace}
    (h : ∀ x, Ψ.toSpace x ∈ t ↔ x ∈ s) : Ψ.toSpace '' s = t := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).2 hx
  · intro hy
    obtain ⟨x, rfl⟩ := toSpace_surjective Ψ y
    exact ⟨x, (h x).1 hy, rfl⟩
theorem mapsGridScales : Ψ.MapsGridScales := by
  intro c hc
  have hp := Ψ.zpow_L_pos
  have hg := Ψ.isGridScale_scaled hc
  have hL : (Ψ.scaleExponent.target.L : ℝ) = (D.L : ℝ) := rfl
  refine ⟨hg, ?_, ?_⟩
  · simp only [GluingSetup.cellCount]
    rw [Ψ.target_side_eq, mul_div_mul_left _ _ hp.ne']
  · constructor
    · rintro ⟨-, h⟩
      refine ⟨hc, ?_⟩
      rw [Ψ.target_mesh_eq, hL] at h
      refine le_of_mul_le_mul_left ?_ hp
      calc (D.L : ℝ) ^ Ψ.exp * ((D.L : ℝ) ^ 2 * D.mesh)
          = (D.L : ℝ) ^ 2 * ((D.L : ℝ) ^ Ψ.exp * D.mesh) := by ring
        _ ≤ (D.L : ℝ) ^ Ψ.exp * c := h
    · rintro ⟨-, h⟩
      refine ⟨hg, ?_⟩
      rw [Ψ.target_mesh_eq, hL]
      calc (D.L : ℝ) ^ 2 * ((D.L : ℝ) ^ Ψ.exp * D.mesh)
          = (D.L : ℝ) ^ Ψ.exp * ((D.L : ℝ) ^ 2 * D.mesh) := by ring
        _ ≤ (D.L : ℝ) ^ Ψ.exp * c := mul_le_mul_of_nonneg_left h hp.le
theorem mappedGrid_isMirrorGrid (g : CubicGrid D) (hg : g.IsMirrorGrid) :
    (Ψ.mappedGrid g hg).IsMirrorGrid := by
  intro μ
  obtain ⟨i, hi⟩ := hg μ
  obtain ⟨n, hn⟩ := Ψ.base_mem
  refine ⟨i + n μ, ?_⟩
  change Ψ.toSpace g.origin μ = Ψ.scaleExponent.target.mesh * (((i + n μ : ℤ) : ℝ) + 1 / 2)
  rw [Ψ.target_mesh_eq, toSpace_apply, hi, hn μ]
  push_cast
  ring
theorem toSpace_sub_mappedGrid (g : CubicGrid D) (hg : g.IsMirrorGrid)
    (x : InfiniteLattice.AmbientSpace) (μ : Fin 4) (t : ℝ) :
    Ψ.toSpace x μ - ((Ψ.mappedGrid g hg).origin μ + (Ψ.mappedGrid g hg).edge * t) =
      (D.L : ℝ) ^ Ψ.exp * (x μ - (g.origin μ + g.edge * t)) := by
  change Ψ.toSpace x μ - (Ψ.toSpace g.origin μ + (D.L : ℝ) ^ Ψ.exp * g.edge * t) = _
  rw [toSpace_apply, toSpace_apply]
  ring
theorem mapsCubes (g : CubicGrid D) (hg : g.IsMirrorGrid) : Ψ.MapsCubes g hg := by
  have hp := Ψ.zpow_L_pos
  refine ⟨mappedGrid_isMirrorGrid Ψ g hg, fun k => ?_, fun k => ?_, fun μ n => ?_⟩
  · refine toSpace_image_eq_of_iff Ψ fun x => forall_congr' fun μ => ?_
    rw [toSpace_sub_mappedGrid]
    exact pos_mul_mem_Icc_iff hp
  · refine toSpace_image_eq_of_iff Ψ fun x => forall_congr' fun μ => ?_
    rw [toSpace_sub_mappedGrid]
    exact pos_mul_mem_Ioo_iff hp
  · refine toSpace_image_eq_of_iff Ψ fun x => ?_
    change Ψ.toSpace x μ = Ψ.toSpace g.origin μ + (n : ℝ) * ((D.L : ℝ) ^ Ψ.exp * g.edge) ↔
      x μ = g.origin μ + (n : ℝ) * g.edge
    rw [toSpace_apply, toSpace_apply]
    constructor
    · intro h
      have hscaled : (D.L : ℝ) ^ Ψ.exp * (x μ) =
          (D.L : ℝ) ^ Ψ.exp * (g.origin μ + (n : ℝ) * g.edge) := by
        linear_combination h
      exact mul_left_cancel₀ hp.ne' hscaled
    · intro h
      rw [h]
      ring
theorem statement_holds : Statement :=
  fun _ Ψ => ⟨mapsGridScales Ψ, fun g hg => mapsCubes Ψ g hg⟩
end YangMills.Construction.SourcesAndGluing.RescalingKeepsGridScalesAndCubes
end
