import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesCellsAndGroupProof
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesSidesAndOffsets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
namespace ScalingSidesCentres
open ChessboardTori (ReflectionGrid)
open InfiniteLattice (AmbientSpace)
variable {D : GridSetup} (S : ScalingMap D)
theorem L_ne_zero : (D.L : ℝ) ≠ 0 := by
  linarith [D.one_lt_factor]
theorem injective_toFun : Function.Injective S.toFun := S.toPerm.injective
theorem surjective_toFun : Function.Surjective S.toFun := S.toPerm.surjective
theorem cellSide_gridImage (g : ReflectionGrid D) :
    (S.gridImage g).cellSide = S.scale * g.cellSide := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ScalingProof.cellSide_gridImage <;> assumption
theorem toFun_mem_cell_gridImage_iff (g : ReflectionGrid D) (k : Fin 4 → ℤ) (x : AmbientSpace) :
    S.toFun x ∈ (S.gridImage g).cell k ↔ x ∈ g.cell k := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ScalingProof.apply_mem_cell_iff <;> assumption
theorem cell_gridImage (g : ReflectionGrid D) (k : Fin 4 → ℤ) :
    (S.gridImage g).cell k = S.toFun '' g.cell k := by
  ext y
  obtain ⟨x, rfl⟩ := surjective_toFun S y
  rw [toFun_mem_cell_gridImage_iff, (injective_toFun S).mem_set_image]
theorem cellSet_gridImage (g : ReflectionGrid D) :
    (S.gridImage g).cellSet = (fun C : Set AmbientSpace => S.toFun '' C) '' g.cellSet := by
  ext C
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨g.cell k, ⟨k, rfl⟩, (cell_gridImage S g k).symm⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, cell_gridImage S g k⟩
theorem reflectionGrid_ext {E : GridSetup} {g h : ReflectionGrid E} (hq : g.q = h.q)
    (ho : g.origin = h.origin) : g = h := by
  cases g
  cases h
  simp only at hq ho
  subst hq
  subst ho
  rfl
def pullbackGrid (g' : ReflectionGrid S.image) : ReflectionGrid D where
  q := g'.q - S.power
  one_sub_K_le_q := by
    have h := g'.one_sub_K_le_q
    have hb := S.power_lt
    change 1 - ((((D.K : ℕ) - S.power : ℕ)) : ℤ) ≤ g'.q at h
    omega
  origin := S.toPerm⁻¹ g'.origin
  origin_mem := by
    intro μ
    obtain ⟨i, hi⟩ := g'.origin_mem μ
    obtain ⟨u, hu⟩ := S.shift_mem
    refine ⟨i + u μ, ?_⟩
    have hf := S.scale_pos.ne'
    change S.scale⁻¹ * g'.origin μ + S.shift μ = _
    rw [hi, S.image_mesh, hu μ]
    push_cast
    field_simp
    ring
theorem gridImage_pullbackGrid (g' : ReflectionGrid S.image) :
    S.gridImage (pullbackGrid S g') = g' := by
  refine reflectionGrid_ext (sub_add_cancel _ _) ?_
  exact S.toPerm.apply_symm_apply g'.origin
theorem isAdmissibleSide_image {l : ℝ} (hl : D.IsAdmissibleSide l) :
    S.image.IsAdmissibleSide (S.scale * l) := by
  obtain ⟨⟨n, hn⟩, ha⟩ := hl
  refine ⟨⟨n + S.power, ?_⟩, ?_⟩
  · change (D.L : ℝ) ^ S.power * l = (D.L : ℝ) ^ (n + (S.power : ℤ))
    rw [hn, zpow_add₀ L_ne_zero, zpow_natCast, mul_comm]
  · rw [S.image_mesh]
    change S.scale * D.mesh ≤ S.scale * l / (D.L : ℝ) ^ 2
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ha S.scale_pos.le
end ScalingSidesCentres
open ScalingSidesCentres in
open InfiniteLattice (AmbientSpace) in
theorem scalingPreservesSidesAndCentres_holds : ScalingPreservesSidesAndCentres := by
  intro D S
  refine ⟨fun l hl => ⟨isAdmissibleSide_image S hl, fun g' hg' => ?_⟩,
    fun c hc μ => S.toFun_halfInteger hc μ⟩
  have himage := gridImage_pullbackGrid S g'
  have hside : (pullbackGrid S g').cellSide = l := by
    have h : S.scale * (pullbackGrid S g').cellSide = S.scale * l := by
      rw [← cellSide_gridImage, himage, hg']
    exact mul_left_cancel₀ S.scale_pos.ne' h
  refine ⟨(pullbackGrid S g').cellSet, ⟨pullbackGrid S g', hside, rfl, by rw [himage]⟩, ?_⟩
  rintro G ⟨g, -, rfl, hg⟩
  have hinj : Function.Injective fun G : Set (Set AmbientSpace) =>
      (fun C : Set AmbientSpace => S.toFun '' C) '' G :=
    Set.image_injective.2 (Set.image_injective.2 (injective_toFun S))
  apply hinj
  change (fun C : Set AmbientSpace => S.toFun '' C) '' g.cellSet =
    (fun C : Set AmbientSpace => S.toFun '' C) '' (pullbackGrid S g').cellSet
  rw [← cellSet_gridImage, ← cellSet_gridImage, hg, himage]
end YangMills.Construction.MirrorGridsAllSides
end
