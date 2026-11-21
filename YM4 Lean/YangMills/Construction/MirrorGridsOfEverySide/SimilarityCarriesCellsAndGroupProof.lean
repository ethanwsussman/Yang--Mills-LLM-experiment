import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorusProof
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesCellsAndGroup
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.ChessboardTori (ReflectionGrid orientationSign HasLinearComponent linearComponent coordVec)
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides.ScalingProof
variable {D : GridSetup} (S : ScalingMap D) (g : ReflectionGrid D)
theorem cellSide_gridImage : (S.gridImage g).cellSide = S.scale * g.cellSide := by
  have hL : (D.L : ℝ) ≠ 0 := by linarith [D.one_lt_factor]
  change (D.L : ℝ) ^ (g.q + (S.power : ℤ)) = (D.L : ℝ) ^ S.power * (D.L : ℝ) ^ g.q
  rw [zpow_add₀ hL, zpow_natCast, mul_comm]
theorem image_eq_of_forall_mem_iff {A B : Set AmbientSpace} (h : ∀ x, S.toFun x ∈ B ↔ x ∈ A) :
    S.toFun '' A = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).2 hx
  · intro hy
    have hy' : S.toFun (S.toPerm.symm y) = y := S.toPerm.apply_symm_apply y
    exact ⟨S.toPerm.symm y, (h _).1 (by rwa [hy']), hy'⟩
theorem apply_mem_cell_iff (k : Fin 4 → ℤ) (x : AmbientSpace) :
    S.toFun x ∈ (S.gridImage g).cell k ↔ x ∈ g.cell k := by
  have hs := S.scale_pos
  simp only [ReflectionGrid.cell, mem_ofPred_eq, mem_Icc, cellSide_gridImage]
  refine forall_congr' fun μ => ?_
  have hμ : S.toFun x μ - ((S.gridImage g).origin μ + S.scale * g.cellSide * k μ) =
      S.scale * (x μ - (g.origin μ + g.cellSide * k μ)) := by
    change S.scale * (x μ - S.shift μ) -
      (S.scale * (g.origin μ - S.shift μ) + S.scale * g.cellSide * k μ) = _
    ring
  rw [hμ]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨nonneg_of_mul_nonneg_right hlo hs, le_of_mul_le_mul_left hhi hs⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨mul_nonneg hs.le hlo, mul_le_mul_of_nonneg_left hhi hs.le⟩
theorem apply_mem_wall_iff (μ : Fin 4) (k : ℤ) (x : AmbientSpace) :
    S.toFun x ∈ (S.gridImage g).wall μ k ↔ x ∈ g.wall μ k := by
  have hs := S.scale_pos
  change S.scale * (x μ - S.shift μ) =
      S.scale * (g.origin μ - S.shift μ) + k * (S.gridImage g).cellSide ↔
        x μ = g.origin μ + k * g.cellSide
  rw [cellSide_gridImage]
  constructor
  · intro h
    apply mul_left_cancel₀ hs.ne'
    linear_combination h
  · intro h
    rw [h]
    ring
def toHomeomorph : AmbientSpace ≃ₜ AmbientSpace where
  toEquiv := S.toPerm
  continuous_toFun :=
    continuous_pi fun μ => continuous_const.mul ((continuous_apply μ).sub continuous_const)
  continuous_invFun :=
    continuous_pi fun μ => (continuous_const.mul (continuous_apply μ)).add continuous_const
theorem apply_reflect (μ : Fin 4) (k : ℤ) (x : AmbientSpace) :
    S.toFun (g.reflect μ k x) = (S.gridImage g).reflect μ k (S.toFun x) := by
  funext ν
  change S.scale * ((x ν - (2 * (x μ - g.origin μ - k * g.cellSide)) * coordVec μ ν) - S.shift ν) =
    S.scale * (x ν - S.shift ν) - (2 * (S.scale * (x μ - S.shift μ) -
      S.scale * (g.origin μ - S.shift μ) - k * (S.gridImage g).cellSide)) * coordVec μ ν
  rw [cellSide_gridImage]
  ring
theorem conj_reflectPerm (μ : Fin 4) (k : ℤ) :
    S.toPerm * g.reflectPerm μ k * S.toPerm⁻¹ = (S.gridImage g).reflectPerm μ k := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := S.toPerm.surjective y
  have hx : S.toPerm⁻¹ (S.toPerm x) = x := S.toPerm.symm_apply_apply x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hx]
  exact apply_reflect S g μ k x
theorem map_reflectionGroup :
    g.reflectionGroup.map (MulAut.conj S.toPerm).toMonoidHom = (S.gridImage g).reflectionGroup := by
  unfold ReflectionGrid.reflectionGroup
  rw [MonoidHom.map_closure, ← range_comp]
  congr 2
  funext p
  exact conj_reflectPerm S g p.1 p.2
theorem linearComponent_eq {r : AmbientSpace → AmbientSpace} {R : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (h : HasLinearComponent r R) : linearComponent r = R := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.linearComponent_eq <;> assumption
theorem orientationSign_eq {r r' : AmbientSpace → AmbientSpace}
    {R : AmbientSpace →ₗ[ℝ] AmbientSpace} (h : HasLinearComponent r R)
    (h' : HasLinearComponent r' R) : orientationSign r = orientationSign r' := by
  unfold orientationSign
  rw [linearComponent_eq h, linearComponent_eq h']
theorem hasLinearComponent_conj (r : Equiv.Perm AmbientSpace) {R : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (h : HasLinearComponent r R) :
    HasLinearComponent (S.toPerm * r * S.toPerm⁻¹ : Equiv.Perm AmbientSpace) R := by
  obtain ⟨w, hw⟩ := h
  have hs := S.scale_pos.ne'
  refine ⟨S.toFun (R S.shift + w), fun y => ?_⟩
  have hinv : S.toPerm⁻¹ y = S.scale⁻¹ • y + S.shift := rfl
  have hlin : R (S.scale⁻¹ • y + S.shift) = S.scale⁻¹ • R y + R S.shift := by
    rw [map_add, map_smul]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, hw, hlin]
  funext μ
  change S.scale * ((S.scale⁻¹ • R y + R S.shift + w) μ - S.shift μ) = R y μ +
    S.scale * ((R S.shift + w) μ - S.shift μ)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring
theorem exists_hasLinearComponent_reflect (μ : Fin 4) (k : ℤ) :
    ∃ R, HasLinearComponent (g.reflectPerm μ k) R := by
  refine ⟨LinearMap.id - (2 : ℝ) • (LinearMap.proj μ : AmbientSpace →ₗ[ℝ] ℝ).smulRight (coordVec μ),
    (2 * (g.origin μ + k * g.cellSide)) • coordVec μ, fun x => ?_⟩
  change g.reflect μ k x = _
  funext ν
  simp only [ReflectionGrid.reflect, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]
  ring
theorem exists_hasLinearComponent_of_mem {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) :
    ∃ R, HasLinearComponent r R := by
  refine Subgroup.closure_induction''
    (p := fun (r : Equiv.Perm AmbientSpace) _ => ∃ R, HasLinearComponent r R) ?_ ?_ ?_ ?_ hr
  · rintro _ ⟨p, rfl⟩
    exact exists_hasLinearComponent_reflect g p.1 p.2
  · rintro _ ⟨p, rfl⟩
    exact exists_hasLinearComponent_reflect g p.1 p.2
  · exact ⟨LinearMap.id, 0, fun x => by simp⟩
  · rintro a b _ _ ⟨A, v, ha⟩ ⟨B, w, hb⟩
    refine ⟨A ∘ₗ B, A w + v, fun x => ?_⟩
    rw [Equiv.Perm.mul_apply, ha, hb, map_add, LinearMap.comp_apply, add_assoc]
theorem scalingPreservesCellsAndGroup_holds : ScalingPreservesCellsAndGroup := by
  intro D S g _
  refine ⟨fun k => image_eq_of_forall_mem_iff S (apply_mem_cell_iff S g k), fun k => ?_, fun k => ?_,
    ?_, ?_⟩
  · have hint := (toHomeomorph S).image_interior (g.cell k)
    have himg : (toHomeomorph S) '' g.cell k = (S.gridImage g).cell k :=
      image_eq_of_forall_mem_iff S (apply_mem_cell_iff S g k)
    rw [himg] at hint
    exact hint
  · funext μ
    change S.scale * (g.origin μ + g.cellSide * k μ + g.cellSide / 2 - S.shift μ) =
      S.scale * (g.origin μ - S.shift μ) + (S.gridImage g).cellSide * k μ +
        (S.gridImage g).cellSide / 2
    rw [cellSide_gridImage]
    ring
  · unfold ReflectionGrid.wallSet
    rw [← range_comp]
    congr 1
    funext p
    exact image_eq_of_forall_mem_iff S (apply_mem_wall_iff S g p.1 p.2)
  · refine ⟨((MulAut.conj S.toPerm).subgroupMap g.reflectionGroup).trans
      (MulEquiv.subgroupCongr (map_reflectionGroup S g)), fun r => ⟨rfl, ?_⟩⟩
    obtain ⟨R, hR⟩ := exists_hasLinearComponent_of_mem g r.2
    exact orientationSign_eq (hasLinearComponent_conj S r.1 hR) hR
end YangMills.Construction.MirrorGridsAllSides.ScalingProof
end
