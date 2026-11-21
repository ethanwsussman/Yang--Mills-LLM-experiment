import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnitsProof
import YangMills.Construction.Lattice.LatticesAndCubesOfOrder
import YangMills.Construction.SeparatedSequences.BasePointIsThatOfTheOperatorsAndTheFoot
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice.DirichletOperators
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.SeparatedClasses.AnchorAgreementProof
variable (C : ClassData)
abbrev levelSide : ℝ := PeriodicLattice.torusSide C.L C.m
abbrev readSide : ℝ := C.levelUnitTorus.toScaleData.torusSide
abbrev fineMesh : ℝ := C.levelUnitTorus.toScaleData.baseSpacing
def scaleFactor (S : ℝ) : ℝ := (levelSide C)⁻¹ * S
theorem cast_L_pos : (0 : ℝ) < C.L := by
  have := C.isAdmissible.2
  exact_mod_cast (by omega : 0 < C.L)
theorem readSide_eq :
    readSide C = 2 * (C.L : ℝ) ^ ((C.m : ℕ) + (C.K : ℕ) - C.t) := rfl
theorem fineMesh_eq : fineMesh C = (C.L : ℝ) ^ (-(C.t : ℤ)) := rfl
theorem scaleFactor_readSide :
    scaleFactor C (readSide C) = (C.L : ℝ) ^ (((C.K : ℕ) : ℤ) - (C.t : ℤ)) := by
  have hL := (cast_L_pos C).ne'
  have hpow : (C.L : ℝ) ^ ((C.m : ℕ) + (C.K : ℕ) - C.t) =
      (C.L : ℝ) ^ (C.m : ℕ) * (C.L : ℝ) ^ (((C.K : ℕ) : ℤ) - (C.t : ℤ)) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hL]
    congr 1
    have := C.t_le_cutoff
    omega
  simp only [scaleFactor, levelSide, PeriodicLattice.torusSide, readSide_eq, hpow]
  field_simp
theorem scaleFactor_pos : 0 < scaleFactor C (readSide C) := by
  rw [scaleFactor_readSide]
  exact zpow_pos (cast_L_pos C) _
theorem meshSize_mul_scaleFactor (n : ℕ) :
    PeriodicLattice.meshSize C.L (PeriodicLattice.levelDepth C.K n) * scaleFactor C (readSide C) =
      (C.L : ℝ) ^ n * fineMesh C := by
  have hL := (cast_L_pos C).ne'
  rw [scaleFactor_readSide, fineMesh_eq, PeriodicLattice.meshSize, ← zpow_natCast,
    ← zpow_add₀ hL, ← zpow_add₀ hL]
  congr 1
  simp only [PeriodicLattice.levelDepth]
  ring
variable {C} {S : ℝ} (hS : S ≠ 0)
theorem scaleEquiv_coe (v : Fin 4 → ℝ) :
    C.scaleEquiv hS (fun μ => ((v μ : ℝ) : AddCircle (levelSide C))) =
      fun μ => ((v μ * scaleFactor C S : ℝ) : AddCircle S) := by
  funext μ
  exact AddCircle.equivAddCircle_apply_mk (levelSide C) S _ hS (v μ)
theorem scaleEquiv_latticePoint (hSeq : S = readSide C) (k : Fin 4 → ℤ) (n : ℕ) :
    C.scaleEquiv hS (fun μ =>
        (((k μ : ℝ) * PeriodicLattice.meshSize C.L (PeriodicLattice.levelDepth C.K n) : ℝ) :
          AddCircle (levelSide C))) =
      fun μ => (((k μ : ℝ) * ((C.L : ℝ) ^ n * fineMesh C) : ℝ) : AddCircle S) := by
  subst hSeq
  rw [scaleEquiv_coe]
  funext μ
  rw [mul_assoc, meshSize_mul_scaleFactor]
theorem exists_coords {n : ℕ} (x : C.LatticeSite n) : ∃ k : Fin 4 → ℤ, (x : C.Point) = fun μ =>
    (((k μ : ℝ) * PeriodicLattice.meshSize C.L (PeriodicLattice.levelDepth C.K n) : ℝ) :
      AddCircle (levelSide C)) := by
  obtain ⟨k, hk⟩ := x.2
  exact ⟨k, funext hk⟩
theorem scaleEquiv_mem_spacingLattice (hSeq : S = readSide C) {n : ℕ} (x : C.LatticeSite n) :
    C.scaleEquiv hS (x : C.Point) ∈ Torus.spacingLattice 4 S ((C.L : ℝ) ^ n * fineMesh C) := by
  obtain ⟨k, hk⟩ := exists_coords x
  refine ⟨k, ?_⟩
  rw [hk, scaleEquiv_latticePoint hS hSeq k n]
  rfl
theorem supNormVec_eq_norm (w : Fin 4 → ℝ) : TorusMetric.supNormVec w = ‖w‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
theorem supNorm_scaleEquiv (hSeq : S = readSide C) (p : C.Point) :
    Torus.supNorm (C.scaleEquiv hS p : Torus.PeriodicTorus 4 S) =
      scaleFactor C S * TorusMetric.torusSupNorm p := by
  subst hSeq
  have hr := scaleFactor_pos C
  have hset : {r | ∃ v : Fin 4 → ℝ, Torus.torusProj 4 (readSide C) v = C.scaleEquiv hS p ∧
      r = ‖v‖} = scaleFactor C (readSide C) •
        (TorusMetric.supNormVec '' (TorusMetric.torusProj (levelSide C) ⁻¹' {p})) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine Set.mem_smul_set.2 ⟨TorusMetric.supNormVec ((scaleFactor C (readSide C))⁻¹ • v),
        ⟨_, ?_, rfl⟩, ?_⟩
      · apply (C.scaleEquiv hS).injective
        refine Eq.trans ?_ hv
        refine (scaleEquiv_coe hS _).trans ?_
        funext μ
        simp only [Pi.smul_apply, smul_eq_mul, Torus.torusProj]
        rw [show (scaleFactor C (readSide C))⁻¹ * v μ * scaleFactor C (readSide C) = v μ by
          field_simp]
      · rw [supNormVec_eq_norm, norm_smul, smul_eq_mul, norm_inv, Real.norm_of_nonneg hr.le,
          mul_inv_cancel_left₀ hr.ne']
    · intro h
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := Set.mem_smul_set.1 h
      refine ⟨scaleFactor C (readSide C) • w, ?_, ?_⟩
      · have hw' : TorusMetric.torusProj (levelSide C) w = p := hw
        rw [← hw']
        refine Eq.trans ?_ (scaleEquiv_coe hS _).symm
        funext μ
        simp only [Pi.smul_apply, smul_eq_mul, Torus.torusProj]
        rw [mul_comm]
      · rw [supNormVec_eq_norm, norm_smul, smul_eq_mul, Real.norm_of_nonneg hr.le]
  simp only [Torus.supNorm, TorusMetric.torusSupNorm]
  rw [hset, Real.sInf_smul_of_nonneg hr.le]
  rfl
theorem mem_cubeAround_iff (hSeq : S = readSide C) {n : ℕ} (y : C.LatticeSite n) (x : C.Point) :
    x ∈ PeriodicLattice.cubeAround y ↔ C.scaleEquiv hS x ∈
      Torus.cubeAt (C.scaleEquiv hS (y : C.Point)) ((C.L : ℝ) ^ n * fineMesh C) := by
  subst hSeq
  change TorusMetric.torusSupNorm (x - (y : C.Point)) ≤ _ ↔
    Torus.supNorm (C.scaleEquiv hS x - C.scaleEquiv hS (y : C.Point)) ≤ _
  rw [← map_sub, supNorm_scaleEquiv hS rfl, ← meshSize_mul_scaleFactor]
  have hr := scaleFactor_pos C
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hr.le
    linarith
  · intro h
    refine le_of_mul_le_mul_left ?_ hr
    linarith
theorem isCubeUnion_image (hSeq : S = readSide C) {n : ℕ} {X : Set C.Point}
    {F : Set (Set C.Point)}
    (hF : F ⊆ PeriodicLattice.standardCubePartition C.L C.m (PeriodicLattice.levelDepth C.K n))
    (hX : X = ⋃₀ F) :
    Torus.IsCubeUnion ((C.L : ℝ) ^ n * fineMesh C) (C.scaleEquiv hS '' X) := by
  refine ⟨(fun Q => C.scaleEquiv hS '' Q) '' F, ?_, ?_⟩
  · rintro _ ⟨Q, hQ, rfl⟩
    obtain ⟨y, rfl⟩ := hF hQ
    refine ⟨_, scaleEquiv_mem_spacingLattice hS hSeq y, ?_⟩
    ext q
    obtain ⟨x, rfl⟩ := (C.scaleEquiv hS).surjective q
    rw [(C.scaleEquiv hS).injective.mem_set_image]
    exact mem_cubeAround_iff hS hSeq y x
  · rw [hX, sUnion_eq_biUnion, image_iUnion₂, sUnion_image]
def frameBonds {ξ : ℝ} (A : Set (Torus.PeriodicTorus 4 S)) :
    BondFrame → Set (Dirichlet.LatticeBond 4 S ξ)
  | BondFrame.interior => {c | (c.source : Torus.PeriodicTorus 4 S) ∈ A ∧
      (c.target : Torus.PeriodicTorus 4 S) ∈ A}
  | BondFrame.star => {c | (c.source : Torus.PeriodicTorus 4 S) ∈ A ∨
      (c.target : Torus.PeriodicTorus 4 S) ∈ A}
end YangMills.Construction.SeparatedClasses.AnchorAgreementProof
