import YangMills.Construction.GeneralTorus.CubePartitions
import YangMills.Construction.GeneralTorus.ShellsCubesAndScaledDistance
import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorusProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
open Set TorusMetric
open scoped ENNReal Pointwise
namespace LevelUnitParams
variable (P : LevelUnitParams)
theorem L_pos : (0 : ℝ) < P.L := by
  have := P.blocking.thirteen_le
  exact_mod_cast (by omega : 0 < P.L)
theorem one_lt_L : (1 : ℝ) < P.L := by
  have := P.blocking.thirteen_le
  exact_mod_cast (by omega : 1 < P.L)
theorem lengthFactor_pos : 0 < P.lengthFactor := pow_pos P.L_pos _
theorem lengthFactor_eq_zpow : P.lengthFactor = (P.L : ℝ) ^ ((P.K : ℤ) - (P.t : ℤ)) := by
  rw [lengthFactor, ← zpow_natCast, Nat.cast_sub P.t_le]
theorem torusSide_eq_zpow :
    P.toScaleData.torusSide = 2 * (P.L : ℝ) ^ ((P.m : ℤ) + (P.K : ℤ) - (P.t : ℤ)) := by
  change 2 * (P.L : ℝ) ^ (P.m + P.K - P.t) = _
  have h : P.t ≤ P.m + P.K := by have := P.t_le; omega
  rw [← zpow_natCast, Nat.cast_sub h, Nat.cast_add]
theorem torusSide_eq_mul :
    P.toScaleData.torusSide = P.lengthFactor * PeriodicLattice.torusSide P.L P.m := by
  have h := P.L_pos.ne'
  rw [torusSide_eq_zpow, lengthFactor_eq_zpow, PeriodicLattice.torusSide,
    ← zpow_natCast (P.L : ℝ) P.m]
  rw [mul_left_comm, ← zpow_add₀ h]
  congr 2
  ring
theorem toLevelUnits_eq_mul (r : ℝ) :
    PeriodicLattice.toLevelUnits P.L P.K P.t r = P.lengthFactor * r := by
  rw [lengthFactor_eq_zpow]
  rfl
theorem readPoint_injective : Function.Injective P.readPoint := P.levelEquiv.injective
theorem readPoint_surjective : Function.Surjective P.readPoint := P.levelEquiv.surjective
theorem readPoint_sub (x y : P.PhysSpace) :
    P.readPoint x - P.readPoint y = P.readPoint (x - y) :=
  (map_sub P.levelEquiv x y).symm
theorem readPoint_torusProj (v : Fin 4 → ℝ) :
    P.readPoint (torusProj (PeriodicLattice.torusSide P.L P.m) v) =
      torusProj P.toScaleData.torusSide (P.lengthFactor • v) := by
  funext μ
  change AddCircle.equivAddCircle (PeriodicLattice.torusSide P.L P.m) P.toScaleData.torusSide
    P.physSide_ne_zero P.torusSide_ne_zero ((v μ : ℝ) : AddCircle _) = _
  rw [AddCircle.equivAddCircle_apply_mk]
  simp only [torusProj, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [P.torusSide_eq_mul, mul_comm]
  congr 1
  field_simp [P.physSide_ne_zero]
theorem supNormVec_smul {c : ℝ} (hc : 0 < c) (v : Fin 4 → ℝ) :
    supNormVec (c • v) = c * supNormVec v := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.supNormVec_smul <;> assumption
theorem l1NormVec_smul {c : ℝ} (hc : 0 < c) (v : Fin 4 → ℝ) :
    l1NormVec (c • v) = c * l1NormVec v := by
  simp [l1NormVec, abs_mul, abs_of_pos hc, Finset.mul_sum]
theorem torusSupNorm_readPoint (x : P.PhysSpace) :
    torusSupNorm (P.readPoint x) = P.lengthFactor * torusSupNorm x := by
  have hc := P.lengthFactor_pos
  have e : supNormVec '' (torusProj P.toScaleData.torusSide ⁻¹' {P.readPoint x}) =
      P.lengthFactor •
        (supNormVec '' (torusProj (PeriodicLattice.torusSide P.L P.m) ⁻¹' {x})) := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨_, ⟨P.lengthFactor⁻¹ • w, ?_, rfl⟩, ?_⟩
      · have hw' : torusProj P.toScaleData.torusSide w = P.readPoint x := hw
        show torusProj _ _ = x
        apply P.readPoint_injective
        rw [readPoint_torusProj, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hw']
      · simp only [smul_eq_mul]
        rw [← supNormVec_smul hc, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨P.lengthFactor • v, ?_, supNormVec_smul hc v⟩
      rw [mem_preimage, mem_singleton_iff] at hv ⊢
      rw [← readPoint_torusProj, hv]
  rw [torusSupNorm, e, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
  rfl
theorem image_readPoint_supBall (s : ℝ) (y : P.PhysSpace) :
    P.readPoint '' {x | torusSupNorm (x - y) ≤ s / 2} =
      supCube (P.lengthFactor * s) (P.readPoint y) := by
  have hc := P.lengthFactor_pos
  ext z
  obtain ⟨x, rfl⟩ := P.readPoint_surjective z
  simp only [supCube, mem_ofPred_eq, P.readPoint_injective.mem_set_image]
  rw [readPoint_sub, torusSupNorm_readPoint, mul_div_assoc]
  exact (mul_le_mul_iff_right₀ hc).symm
theorem image_readPoint_sublattice (j : ℤ) :
    P.readPoint '' (PeriodicLattice.sublattice P.L P.m j : Set P.PhysSpace) =
      (spacingLattice P.toScaleData.torusSide (P.lengthFactor * PeriodicLattice.meshSize P.L j) :
        Set P.toScaleData.Space) := by
  ext z
  constructor
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    refine ⟨k, ?_⟩
    have e : x = torusProj (PeriodicLattice.torusSide P.L P.m)
        fun μ => (k μ : ℝ) * PeriodicLattice.meshSize P.L j :=
      funext hk
    rw [e, readPoint_torusProj]
    congr 1
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rintro ⟨k, rfl⟩
    refine ⟨torusProj (PeriodicLattice.torusSide P.L P.m)
        fun μ => (k μ : ℝ) * PeriodicLattice.meshSize P.L j,
      ⟨k, fun μ => rfl⟩, ?_⟩
    rw [readPoint_torusProj]
    congr 1
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
theorem image_standardCubePartition {i : ℤ}
    (hs : P.toScaleData.AdmitsPartition (P.lengthFactor * PeriodicLattice.meshSize P.L i)) :
    (fun Q => P.readPoint '' Q) '' PeriodicLattice.standardCubePartition P.L P.m i =
      P.toScaleData.cubePartition (P.lengthFactor * PeriodicLattice.meshSize P.L i) := by
  ext Q
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨hs, P.readPoint y, ?_, P.image_readPoint_supBall _ _⟩
    rw [← SetLike.mem_coe, ← image_readPoint_sublattice]
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨_, y, hy, rfl⟩
    rw [← SetLike.mem_coe, ← image_readPoint_sublattice] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨_, ⟨⟨x, hx⟩, rfl⟩, P.image_readPoint_supBall _ _⟩
theorem isUnionOfCubes_image {i : ℤ}
    (hs : P.toScaleData.AdmitsPartition (P.lengthFactor * PeriodicLattice.meshSize P.L i))
    {X : Set P.PhysSpace} (hX : PeriodicLattice.IsPartitionRegion i X) :
    IsUnionOfCubes (P.toScaleData.cubePartition (P.lengthFactor * PeriodicLattice.meshSize P.L i))
      (P.readPoint '' X) := by
  obtain ⟨C, hC, rfl⟩ := hX
  refine ⟨(fun Q => P.readPoint '' Q) '' C, ?_, image_sUnion⟩
  rw [← P.image_standardCubePartition hs]
  exact image_mono hC
theorem image_complementRegion (hp : CubePartitions.CubePartitionFacts) {i : ℤ}
    (hs : P.toScaleData.AdmitsPartition (P.lengthFactor * PeriodicLattice.meshSize P.L i))
    {X : Set P.PhysSpace} (hX : PeriodicLattice.IsPartitionRegion i X) :
    P.readPoint '' PeriodicLattice.complementRegion i X =
      closedComplement (P.readPoint '' X) := by
  have h := (hp P.toScaleData _ 1 hs.1 le_rfl odd_one (by simpa using hs.2)).2.2.2.2.1.2 _
    (P.isUnionOfCubes_image hs hX)
  rw [h.1, ← P.image_standardCubePartition hs]
  ext z
  constructor
  · rintro ⟨x, ⟨Q, ⟨hQ, hQX⟩, hx⟩, rfl⟩
    exact ⟨P.readPoint '' Q, ⟨⟨Q, hQ, rfl⟩, fun hsub =>
      hQX ⟨hQ, (image_subset_image_iff P.readPoint_injective).1 hsub⟩⟩, ⟨x, hx, rfl⟩⟩
  · rintro ⟨_, ⟨⟨Q, hQ, rfl⟩, hn⟩, ⟨x, hx, rfl⟩⟩
    exact ⟨x, ⟨Q, ⟨hQ, fun hc => hn (image_mono hc.2)⟩, hx⟩, rfl⟩
theorem set_antitone (B : SeparatedChain P.toScaleData) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ P.t) : B.set b ⊆ B.set a := by
  induction b, hab using Nat.le_induction with
  | base => exact subset_rfl
  | succ b hab ih =>
    exact (B.mono b (by change b < P.t; omega)).trans (ih (by omega))
theorem displacement_scaleSegment (s : LiftedSegment) :
    (P.scaleSegment s).displacement = P.lengthFactor • s.displacement := by
  simp [LiftedSegment.displacement, scaleSegment, smul_sub]
theorem pointAt_scaleSegment (s : LiftedSegment) (u : ℝ) :
    (P.scaleSegment s).pointAt P.toScaleData.torusSide u =
      P.readPoint (s.pointAt (PeriodicLattice.torusSide P.L P.m) u) := by
  rw [LiftedSegment.pointAt, LiftedSegment.pointAt, readPoint_torusProj,
    displacement_scaleSegment]
  congr 1
  funext μ
  simp only [scaleSegment, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem segmentsSupport_map (Γ : List LiftedSegment) :
    segmentsSupport P.toScaleData.torusSide (Γ.map P.scaleSegment) =
      P.readPoint '' segmentsSupport (PeriodicLattice.torusSide P.L P.m) Γ := by
  ext z
  constructor
  · intro hz
    obtain ⟨s', hs', hz⟩ := mem_iUnion₂.1 hz
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs'
    obtain ⟨u, hu, rfl⟩ := hz
    exact ⟨s.pointAt _ u, mem_iUnion₂.2 ⟨s, hs, u, hu, rfl⟩, (P.pointAt_scaleSegment s u).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, u, hu, rfl⟩ := mem_iUnion₂.1 hx
    exact mem_iUnion₂.2 ⟨_, List.mem_map_of_mem hs, u, hu, P.pointAt_scaleSegment s u⟩
end LevelUnitParams
end YangMills.Construction.GeneralTorus
