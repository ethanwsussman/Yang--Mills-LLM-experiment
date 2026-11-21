import YangMills.Construction.Lattice.CubesUnderRefinement
import YangMills.Construction.SeparatedSequences.ClassExpansionsAndAveragesInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.ClassSequenceHasASettingOfRegions
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice.DirichletOperators
open YangMills.Construction.Torus (PeriodicTorus torusProj cubeAt spacingLattice scaleSpacing unitSide unitSpacing supNorm IsCubeUnion)
noncomputable section
namespace YangMills.Construction.SeparatedClasses.NestedRegionsOfSequence
open SingleSequence SingleSequence.SequenceData
open scoped Pointwise
variable (s : SequenceData)
theorem blockFactor_pos : (0 : ℝ) < (s.data.L : ℝ) := by apply _root_.YangMills.Construction.SeparatedClasses.SingleSequence.NestedRescale.blockFactor_pos <;> assumption
theorem mesh_pos : 0 < s.mesh := zpow_pos (blockFactor_pos s) _
theorem unitTorusSide_pos : 0 < s.unitTorusSide :=
  mul_pos two_pos (zpow_pos (blockFactor_pos s) _)
def rescaling : ℝ := (s.data.L : ℝ) ^ ((s.data.cutoff : ℤ) - (s.data.t : ℤ))
theorem rescaling_pos : 0 < rescaling s := zpow_pos (blockFactor_pos s) _
theorem unitTorusSide_eq_rescaling_mul :
    s.unitTorusSide = rescaling s * PeriodicLattice.torusSide s.data.L s.data.m := by
  have hL := (blockFactor_pos s).ne'
  simp only [SequenceData.unitTorusSide, unitSide, rescaling, PeriodicLattice.torusSide]
  rw [show ((s.data.m : ℕ) : ℤ) + (s.data.cutoff : ℤ) - (s.data.t : ℤ) =
      ((s.data.m : ℕ) : ℤ) + ((s.data.cutoff : ℤ) - (s.data.t : ℤ)) by ring,
    zpow_add₀ hL, zpow_natCast]
  ring
def toTorusAddEquiv : s.data.Point ≃+ PeriodicTorus 4 s.unitTorusSide :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle _ _ s.torusSide_ne_zero (unitTorusSide_pos s).ne'
theorem addEquiv_torusProj (v : Fin 4 → ℝ) :
    toTorusAddEquiv s (torusProj 4 (PeriodicLattice.torusSide s.data.L s.data.m) v) =
      torusProj 4 s.unitTorusSide (rescaling s • v) := by
  funext μ
  change AddCircle.equivAddCircle _ _ s.torusSide_ne_zero (unitTorusSide_pos s).ne'
    ((v μ : ℝ) : AddCircle (PeriodicLattice.torusSide s.data.L s.data.m)) = _
  have hk : (PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * s.unitTorusSide = rescaling s := by
    rw [unitTorusSide_eq_rescaling_mul]
    have := s.torusSide_ne_zero
    field_simp
  rw [AddCircle.equivAddCircle_apply_mk, hk, mul_comm]
  rfl
theorem supNormVec_eq_norm (v : Fin 4 → ℝ) : TorusMetric.supNormVec v = ‖v‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
theorem supNorm_addEquiv (p : s.data.Point) :
    supNorm (toTorusAddEquiv s p) = rescaling s * TorusMetric.torusSupNorm p := by
  have hc := rescaling_pos s
  have hset : {r | ∃ v : Fin 4 → ℝ, torusProj 4 s.unitTorusSide v = toTorusAddEquiv s p ∧ r = ‖v‖} =
      rescaling s • (TorusMetric.supNormVec ''
        (TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) ⁻¹' {p})) := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine Set.mem_smul_set.2 ⟨‖(rescaling s)⁻¹ • w‖,
        ⟨(rescaling s)⁻¹ • w, ?_, supNormVec_eq_norm _⟩, ?_⟩
      · apply (toTorusAddEquiv s).injective
        change toTorusAddEquiv s (torusProj 4 _ _) = _
        rw [addEquiv_torusProj, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hw]
      · simp only [norm_smul, smul_eq_mul, norm_inv, Real.norm_of_nonneg hc.le]
        field_simp
    · intro hr
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hr
      have hv' : torusProj 4 (PeriodicLattice.torusSide s.data.L s.data.m) v = p := hv
      refine ⟨rescaling s • v, ?_, ?_⟩
      · rw [← addEquiv_torusProj, hv']
      · rw [supNormVec_eq_norm, norm_smul, Real.norm_of_nonneg hc.le, smul_eq_mul]
  unfold supNorm TorusMetric.torusSupNorm
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
theorem image_cubeAround {i : ℤ} (y : PeriodicLattice.Site s.data.L s.data.m i) :
    toTorusAddEquiv s '' PeriodicLattice.cubeAround y =
      cubeAt (toTorusAddEquiv s y) (rescaling s * PeriodicLattice.meshSize s.data.L i) := by
  have hc := rescaling_pos s
  ext q
  obtain ⟨p, rfl⟩ := (toTorusAddEquiv s).surjective q
  rw [(toTorusAddEquiv s).injective.mem_set_image]
  change TorusMetric.torusSupNorm (p - (y : s.data.Point)) ≤ _ ↔
    supNorm (toTorusAddEquiv s p - toTorusAddEquiv s y) ≤ _
  rw [← map_sub, supNorm_addEquiv, mul_div_assoc]
  exact ⟨fun h => mul_le_mul_of_nonneg_left h hc.le, fun h => le_of_mul_le_mul_left h hc⟩
theorem addEquiv_mem_spacingLattice_iff {i : ℤ} (p : s.data.Point) :
    toTorusAddEquiv s p ∈
        spacingLattice 4 s.unitTorusSide (rescaling s * PeriodicLattice.meshSize s.data.L i) ↔
      p ∈ PeriodicLattice.sublattice s.data.L s.data.m i := by
  constructor
  · rintro ⟨k, hk⟩
    have hp : p = torusProj 4 (PeriodicLattice.torusSide s.data.L s.data.m)
        (fun μ => (k μ : ℝ) * PeriodicLattice.meshSize s.data.L i) := by
      apply (toTorusAddEquiv s).injective
      rw [addEquiv_torusProj, hk]
      congr 1
      funext μ
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    exact ⟨k, fun μ => congrFun hp μ⟩
  · rintro ⟨n, hn⟩
    have hp : p = torusProj 4 (PeriodicLattice.torusSide s.data.L s.data.m)
        (fun μ => (n μ : ℝ) * PeriodicLattice.meshSize s.data.L i) := funext hn
    refine ⟨n, ?_⟩
    rw [hp, addEquiv_torusProj]
    congr 1
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
theorem isCubeUnion_image {i : ℤ} {X : Set s.data.Point}
    (h : PeriodicLattice.IsPartitionRegion i X) :
    IsCubeUnion (rescaling s * PeriodicLattice.meshSize s.data.L i) (toTorusAddEquiv s '' X) := by
  obtain ⟨C, hC, rfl⟩ := h
  refine ⟨(fun Q => toTorusAddEquiv s '' Q) '' C, ?_, Set.image_sUnion⟩
  rintro _ ⟨Q, hQ, rfl⟩
  obtain ⟨y, rfl⟩ := hC hQ
  exact ⟨toTorusAddEquiv s y, (addEquiv_mem_spacingLattice_iff s _).2 y.2, image_cubeAround s y⟩
theorem scaleSpacing_eq (n : ℕ) :
    scaleSpacing s.data.L s.mesh n =
      rescaling s * PeriodicLattice.meshSize s.data.L
        (PeriodicLattice.levelDepth s.data.cutoff n) := by
  have hL := (blockFactor_pos s).ne'
  simp only [scaleSpacing, SequenceData.mesh, unitSpacing, rescaling, PeriodicLattice.meshSize,
    PeriodicLattice.levelDepth]
  rw [← zpow_add₀ hL, ← zpow_add₀ hL]
  congr 1
  ring
theorem mesh_eq :
    s.mesh = rescaling s * PeriodicLattice.meshSize s.data.L
      (PeriodicLattice.levelDepth s.data.cutoff 0) := by
  rw [← scaleSpacing_eq]
  simp [scaleSpacing]
end YangMills.Construction.SeparatedClasses.NestedRegionsOfSequence
