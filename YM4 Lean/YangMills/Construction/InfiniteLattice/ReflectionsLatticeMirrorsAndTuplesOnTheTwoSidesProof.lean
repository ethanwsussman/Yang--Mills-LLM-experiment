import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstructionProof
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAndTwoFormsOfReflectionPositivityProof
import YangMills.Construction.InfiniteLattice.RulesForObservablesIsometriesAndMirrorsProof
import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import YangMills.Construction.InfiniteLattice.ReflectionsLatticeMirrorsAndTuplesOnTheTwoSides
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Continuum.SeparatedFourTuples
open YangMills.Construction.LatticeConventions (euclidDot basisVector Direction)
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice.EuclideanMirrors
namespace MirrorReflections
theorem sqNorm_pos (n : ReflNormal) : 0 < n.sqNorm := by
  rcases n.sqNorm_eq_one_or_two with h | h <;> rw [h] <;> norm_num
theorem euclidDot_smul_right (t : ℝ) (u v : Fin 4 → ℝ) :
    euclidDot u (t • v) = t * euclidDot u v := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.euclidDot_smul_right <;> assumption
theorem euclidDot_smul_left (t : ℝ) (u v : Fin 4 → ℝ) :
    euclidDot (t • u) v = t * euclidDot u v := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_smul_left <;> assumption
theorem euclidDot_sub_right (u v w : Fin 4 → ℝ) :
    euclidDot u (v - w) = euclidDot u v - euclidDot u w := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_sub_right <;> assumption
theorem hyperplaneReflection_apply (n : ReflNormal) (c : ℝ) (x : Fin 4 → ℝ) (μ : Fin 4) :
    hyperplaneReflection n c x μ =
      x μ - 2 * (euclidDot n.1 x - c) * ((n.sqNorm)⁻¹ * n.1 μ) := by
  simp [hyperplaneReflection, ReflNormal.dual]
theorem euclidNormVec_unitNormalVec (n : ReflNormal) :
    YangMills.Construction.TorusMetric.euclidNormVec (unitNormalVec n) = 1 := by
  have hq := sqNorm_pos n
  have hs : Real.sqrt n.sqNorm ^ 2 = n.sqNorm := Real.sq_sqrt hq.le
  have hsum : ∑ μ, unitNormalVec n μ ^ 2 = 1 := by
    have h : ∑ μ, unitNormalVec n μ ^ 2 = ((Real.sqrt n.sqNorm)⁻¹) ^ 2 * euclidDot n.1 n.1 := by
      simp only [unitNormalVec, euclidDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by ring
    rw [h, ← n.sqNorm_eq_euclidDot, inv_pow, hs, inv_mul_cancel₀ n.sqNorm_ne_zero]
  unfold YangMills.Construction.TorusMetric.euclidNormVec
  rw [hsum, Real.sqrt_one]
theorem isOrthogonalReflection_hyperplaneReflection (n : ReflNormal) (c : ℝ) :
    IsOrthogonalReflection n c := by
  have hs0 : Real.sqrt n.sqNorm ≠ 0 := (Real.sqrt_pos.2 (sqNorm_pos n)).ne'
  have hlt : ∀ x, c < euclidDot n.1 x → euclidDot n.1 (hyperplaneReflection n c x) < c :=
    fun x hx => by
      rw [euclidDot_hyperplaneReflection]
      linarith
  have hgt : ∀ x, euclidDot n.1 x < c → c < euclidDot n.1 (hyperplaneReflection n c x) :=
    fun x hx => by
      rw [euclidDot_hyperplaneReflection]
      linarith
  refine ⟨euclidNormVec_unitNormalVec n, ?_, euclidNormVec_hyperplaneReflection_sub n c, ?_, ?_,
    ?_, hyperplaneReflection_hyperplaneReflection n c, ?_, ?_⟩
  · ext x
    change euclidDot n.1 x = c ↔ euclidDot (unitNormalVec n) x = c / Real.sqrt n.sqNorm
    rw [unitNormalVec, euclidDot_smul_left, eq_div_iff hs0, inv_mul_eq_div,
      div_mul_cancel₀ _ hs0]
  · intro x hx
    have hx' : euclidDot n.1 x = c := hx
    simp [hyperplaneReflection, hx']
  · intro x
    rw [euclidDot_hyperplaneReflection]
    ring
  · intro x
    refine ⟨-(2 * (euclidDot n.1 x - c)) * (n.sqNorm)⁻¹, ?_⟩
    funext μ
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hyperplaneReflection_apply]
    ring
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hlt y hy
    · intro hx
      exact ⟨hyperplaneReflection n c x, hgt x hx, hyperplaneReflection_hyperplaneReflection n c x⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hgt y hy
    · intro hx
      exact ⟨hyperplaneReflection n c x, hlt x hx, hyperplaneReflection_hyperplaneReflection n c x⟩
theorem euclidDot_eq_dotProduct (u v : Fin 4 → ℝ) : euclidDot u v = u ⬝ᵥ v := rfl
theorem hyperplaneReflection_eq_hyperplaneReflect (n : ReflNormal) (c : ℝ) :
    hyperplaneReflection n c = hyperplaneReflect n.1 c := by
  funext x μ
  rw [hyperplaneReflection_apply]
  have hq : n.1 ⬝ᵥ n.1 = n.sqNorm := (n.sqNorm_eq_euclidDot).symm
  simp only [hyperplaneReflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hq,
    euclidDot_eq_dotProduct, div_eq_mul_inv]
  ring
theorem realNormal_axial (μ : Fin 4) : (ReflectionClass.axial μ).realNormal = basisVector μ := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.realNormal_axial <;> assumption
theorem realNormal_diagonal_one (μ ν : Fin 4) (lt : μ < ν) :
    (ReflectionClass.diagonal μ ν lt 1).realNormal = basisVector μ + basisVector ν := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.realNormal_diagonal_one <;> assumption
theorem realNormal_diagonal_neg_one (μ ν : Fin 4) (lt : μ < ν) :
    (ReflectionClass.diagonal μ ν lt (-1)).realNormal = basisVector μ - basisVector ν := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.realNormal_diagonal_neg_one <;> assumption
theorem exists_reflectionClass (n : ReflNormal) : ∃ F : ReflectionClass, F.realNormal = n.1 := by
  obtain ⟨n, ⟨κ, rfl⟩ | ⟨κ, lam, hlt, rfl | rfl⟩⟩ := n
  · exact ⟨.axial κ, realNormal_axial κ⟩
  · exact ⟨.diagonal κ lam hlt 1, realNormal_diagonal_one κ lam hlt⟩
  · exact ⟨.diagonal κ lam hlt (-1), realNormal_diagonal_neg_one κ lam hlt⟩
theorem realNormal_mem_reflectionNormals (F : ReflectionClass) :
    F.realNormal ∈ reflectionNormals := by
  cases F with
  | axial μ => exact Or.inl ⟨μ, realNormal_axial μ⟩
  | diagonal μ ν lt s =>
    rcases Int.units_eq_one_or s with rfl | rfl
    · exact Or.inr ⟨μ, ν, lt, Or.inl (realNormal_diagonal_one μ ν lt)⟩
    · exact Or.inr ⟨μ, ν, lt, Or.inr (realNormal_diagonal_neg_one μ ν lt)⟩
theorem sqNorm_eq_of_realNormal {n : ReflNormal} {F : ReflectionClass} (h : F.realNormal = n.1) :
    n.sqNorm = F.realNormal ⬝ᵥ F.realNormal := by
  rw [n.sqNorm_eq_euclidDot, h]
  rfl
theorem sqNorm_eq_one_of_axial {n : ReflNormal} {μ : Fin 4}
    (h : (ReflectionClass.axial μ).realNormal = n.1) : n.sqNorm = 1 := by
  rw [sqNorm_eq_of_realNormal h, ReflectionClass.realNormal_dot_axial]
theorem sqNorm_eq_two_of_diagonal {n : ReflNormal} {μ ν : Fin 4} {lt : μ < ν} {s : ℤˣ}
    (h : (ReflectionClass.diagonal μ ν lt s).realNormal = n.1) : n.sqNorm = 2 := by
  rw [sqNorm_eq_of_realNormal h, ReflectionClass.realNormal_dot_diagonal]
theorem isLatticeAligned_of_latticeMirror {a' : ℝ} (P : InfiniteLattice.LatticeMirror a')
    {n : ReflNormal} (h : P.cls.realNormal = n.1) :
    (AffineMirror.mk n P.level).IsLatticeAligned a' := by
  obtain ⟨F, c, hc⟩ := P
  cases F with
  | axial μ =>
    obtain ⟨k, rfl⟩ := hc
    refine ⟨fun _ => ⟨k, mul_comm _ _⟩, fun h2 => ?_⟩
    have h1 : n.sqNorm = 1 := sqNorm_eq_one_of_axial h
    have h2' : n.sqNorm = 2 := h2
    rw [h1] at h2'
    norm_num at h2'
  | diagonal μ ν lt s =>
    obtain ⟨k, rfl⟩ := hc
    refine ⟨fun h1 => ?_, fun _ => ⟨k, mul_comm _ _⟩⟩
    have h2 : n.sqNorm = 2 := sqNorm_eq_two_of_diagonal h
    have h1' : n.sqNorm = 1 := h1
    rw [h2] at h1'
    norm_num at h1'
theorem exists_latticeMirror_of_isLatticeAligned {a' : ℝ} (M : AffineMirror)
    (hM : M.IsLatticeAligned a') :
    ∃ P : InfiniteLattice.LatticeMirror a', P.cls.realNormal = M.normal.1 ∧ P.level = M.offset := by
  obtain ⟨F, hF⟩ := exists_reflectionClass M.normal
  have hoff : F.IsAdmissibleLevel a' M.offset := by
    cases F with
    | axial μ =>
      obtain ⟨k, hk⟩ := hM.1 (sqNorm_eq_one_of_axial hF)
      exact ⟨k, by rw [hk]; ring⟩
    | diagonal μ ν lt s =>
      obtain ⟨k, hk⟩ := hM.2 (sqNorm_eq_two_of_diagonal hF)
      exact ⟨k, by rw [hk]; ring⟩
  exact ⟨⟨F, M.offset, hoff⟩, hF, rfl⟩
theorem plane_eq_carrier {a' : ℝ} (P : InfiniteLattice.LatticeMirror a') (M : AffineMirror)
    (h : P.cls.realNormal = M.normal.1) (h' : P.level = M.offset) :
    P.plane = M.carrier := by
  ext x
  change P.cls.realNormal ⬝ᵥ x = P.level ↔ euclidDot M.normal.1 x = M.offset
  rw [h, h']
  rfl
theorem hyperplaneReflect_eq_of_setOf_eq {u v : Fin 4 → ℝ} (hu : u ⬝ᵥ u ≠ 0) (hv : v ⬝ᵥ v ≠ 0)
    {d c : ℝ} (h : {x : Fin 4 → ℝ | u ⬝ᵥ x = d} = {x | v ⬝ᵥ x = c}) :
    hyperplaneReflect u d = hyperplaneReflect v c := by
  set t : ℝ := (u ⬝ᵥ v) / (v ⬝ᵥ v) with ht
  set p : Fin 4 → ℝ := (c / (v ⬝ᵥ v)) • v with hp
  have hvp : v ⬝ᵥ p = c := by
    rw [hp, dotProduct_smul, smul_eq_mul]
    field_simp
  have hup : u ⬝ᵥ p = d := by
    have : p ∈ {x : Fin 4 → ℝ | u ⬝ᵥ x = d} := by
      rw [h]
      exact hvp
    exact this
  set w : Fin 4 → ℝ := u - t • v with hw
  have hvw : v ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_sub, dotProduct_smul, smul_eq_mul, ht, dotProduct_comm v u]
    field_simp
    ring
  have huw : u ⬝ᵥ w = 0 := by
    have hmem : p + w ∈ {x : Fin 4 → ℝ | v ⬝ᵥ x = c} := by
      change v ⬝ᵥ (p + w) = c
      rw [dotProduct_add, hvp, hvw, add_zero]
    rw [← h] at hmem
    have hmem' : u ⬝ᵥ (p + w) = d := hmem
    rw [dotProduct_add, hup] at hmem'
    linarith
  have hww : w ⬝ᵥ w = 0 := by
    have : w ⬝ᵥ w = u ⬝ᵥ w - t * (v ⬝ᵥ w) := by
      conv_lhs => rw [hw]
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [this, huw, hvw]
    ring
  have hw0 : w = 0 := dotProduct_self_eq_zero.1 hww
  have hutv : u = t • v := sub_eq_zero.1 hw0
  have ht0 : t ≠ 0 := by
    intro h0
    apply hu
    rw [hutv, h0, zero_smul]
    simp
  have hd : d = t * c := by
    rw [← hup, hutv, smul_dotProduct, smul_eq_mul, hvp]
  funext x
  simp only [hyperplaneReflect]
  rw [hutv, hd]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_smul]
  congr 1
  congr 1
  field_simp
theorem symmetry_toFun_eq_reflect {a' : ℝ} (M : AffineMirror) (P : InfiniteLattice.LatticeMirror a')
    (h : P.plane = M.carrier) : P.symmetry.toFun = M.reflect := by
  have hM : M.normal.1 ⬝ᵥ M.normal.1 ≠ 0 := by
    rw [← euclidDot_eq_dotProduct, ← M.normal.sqNorm_eq_euclidDot]
    exact M.normal.sqNorm_ne_zero
  change hyperplaneReflect P.cls.realNormal P.level =
    EuclideanMirrors.hyperplaneReflection M.normal M.offset
  rw [hyperplaneReflection_eq_hyperplaneReflect]
  exact hyperplaneReflect_eq_of_setOf_eq P.cls.realNormal_dot_ne_zero hM h
theorem latticeAlignedEqClassMirrors (a' : ℝ) : LatticeAlignedEqClassMirrors a' := by
  refine ⟨fun M hM => ?_, ?_, ?_, ?_, fun M _ P h => symmetry_toFun_eq_reflect M P h,
    fun n => ⟨fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩⟩
  · obtain ⟨P, hP, hP'⟩ := exists_latticeMirror_of_isLatticeAligned M hM
    have h := symmetry_toFun_eq_reflect M P (plane_eq_carrier P M hP hP')
    rw [← h]
    exact P.symmetry.image_eq
  · ext H
    constructor
    · rintro ⟨M, hM, hc, rfl⟩
      obtain ⟨P, hP, hP'⟩ := exists_latticeMirror_of_isLatticeAligned M hM
      obtain ⟨F, c, hoff⟩ := P
      cases F with
      | axial μ => exact ⟨⟨_, c, hoff⟩, μ, rfl, plane_eq_carrier _ M hP hP'⟩
      | diagonal μ ν lt s =>
        have h2 : M.normal.sqNorm = 2 := sqNorm_eq_two_of_diagonal hP
        have h1 : M.normal.sqNorm = 1 := hc
        rw [h2] at h1
        norm_num at h1
    · rintro ⟨P, μ, hF, rfl⟩
      have hN : P.cls.realNormal =
          (⟨_, realNormal_mem_reflectionNormals P.cls⟩ : ReflNormal).1 := rfl
      refine ⟨AffineMirror.mk ⟨_, realNormal_mem_reflectionNormals P.cls⟩ P.level,
        isLatticeAligned_of_latticeMirror P hN, ?_, (plane_eq_carrier P _ hN rfl).symm⟩
      change ReflNormal.sqNorm ⟨_, realNormal_mem_reflectionNormals P.cls⟩ = 1
      exact sqNorm_eq_one_of_axial (congrArg ReflectionClass.realNormal hF).symm
  · ext H
    constructor
    · rintro ⟨M, hM, hc, rfl⟩
      obtain ⟨P, hP, hP'⟩ := exists_latticeMirror_of_isLatticeAligned M hM
      obtain ⟨F, c, hoff⟩ := P
      cases F with
      | axial μ =>
        have h1 : M.normal.sqNorm = 1 := sqNorm_eq_one_of_axial hP
        have h2 : M.normal.sqNorm = 2 := hc
        rw [h1] at h2
        norm_num at h2
      | diagonal μ ν lt s =>
        exact ⟨⟨_, c, hoff⟩, μ, ν, lt, s, rfl, plane_eq_carrier _ M hP hP'⟩
    · rintro ⟨P, μ, ν, lt, s, hF, rfl⟩
      have hN : P.cls.realNormal =
          (⟨_, realNormal_mem_reflectionNormals P.cls⟩ : ReflNormal).1 := rfl
      refine ⟨AffineMirror.mk ⟨_, realNormal_mem_reflectionNormals P.cls⟩ P.level,
        isLatticeAligned_of_latticeMirror P hN, ?_, (plane_eq_carrier P _ hN rfl).symm⟩
      change ReflNormal.sqNorm ⟨_, realNormal_mem_reflectionNormals P.cls⟩ = 2
      exact sqNorm_eq_two_of_diagonal (congrArg ReflectionClass.realNormal hF).symm
  · ext H
    constructor
    · rintro ⟨M, hM, rfl⟩
      obtain ⟨P, hP, hP'⟩ := exists_latticeMirror_of_isLatticeAligned M hM
      exact ⟨P.cls, P, rfl, plane_eq_carrier P M hP hP'⟩
    · rintro ⟨F, P, -, rfl⟩
      have hN : P.cls.realNormal =
          (⟨_, realNormal_mem_reflectionNormals P.cls⟩ : ReflNormal).1 := rfl
      exact ⟨AffineMirror.mk ⟨_, realNormal_mem_reflectionNormals P.cls⟩ P.level,
        isLatticeAligned_of_latticeMirror P hN, (plane_eq_carrier P _ hN rfl).symm⟩
theorem euclidDot_basisVector (κ : Fin 4) (x : Fin 4 → ℝ) : euclidDot (basisVector κ) x = x κ := by
  simp [euclidDot, basisVector, Pi.single_apply]
theorem euclidDot_add_left (u v x : Fin 4 → ℝ) :
    euclidDot (u + v) x = euclidDot u x + euclidDot v x := by apply _root_.YangMills.Construction.LatticeConventions.LatticeMirrorsAndReflectionPositivity.euclidDot_add_left <;> assumption
theorem euclidDot_sub_left (u v x : Fin 4 → ℝ) :
    euclidDot (u - v) x = euclidDot u x - euclidDot v x := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.euclidDot_sub_left <;> assumption
def originReflectionLinearMap (n : ReflNormal) : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ where
  toFun := hyperplaneReflection n 0
  map_add' x y := by
    funext μ
    have h : euclidDot n.1 (x + y) = euclidDot n.1 x + euclidDot n.1 y := by
      simp only [euclidDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    simp only [Pi.add_apply, hyperplaneReflection_apply, h]
    ring
  map_smul' t x := by
    funext μ
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, hyperplaneReflection_apply,
      euclidDot_smul_right]
    ring
theorem originReflection_hyperoctahedral (n : ReflNormal) : OriginReflectionHyperoctahedral n := by
  refine ⟨LinearEquiv.ofInvolutive (originReflectionLinearMap n)
    (hyperplaneReflection_hyperplaneReflection n 0), ?_, rfl⟩
  rw [InfiniteLattice.mem_hyperoctahedralLinearGroup_iff]
  change ∃ (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ),
    ∀ x μ, hyperplaneReflection n 0 x μ = ((s μ : ℤ) : ℝ) * x (π μ)
  obtain ⟨F, hF⟩ := exists_reflectionClass n
  obtain ⟨n, hn⟩ := n
  rcases hn with ⟨κ, rfl⟩ | ⟨κ, lam, hlt, rfl | rfl⟩
  · have hq : ReflNormal.sqNorm ⟨basisVector κ, Or.inl ⟨κ, rfl⟩⟩ = 1 :=
      sqNorm_eq_one_of_axial (realNormal_axial κ)
    refine ⟨1, fun μ => if μ = κ then -1 else 1, fun x μ => ?_⟩
    have hd : euclidDot (basisVector κ) x = x κ := euclidDot_basisVector κ x
    rw [hyperplaneReflection_apply, hq]
    change x μ - 2 * (euclidDot (basisVector κ) x - 0) * (1⁻¹ * basisVector κ μ) = _
    rw [hd]
    simp only [basisVector, Pi.single_apply, Equiv.Perm.coe_one, id]
    by_cases h : μ = κ
    · subst h
      simp
      ring
    · simp [h]
  · have hq : ReflNormal.sqNorm
        ⟨basisVector κ + basisVector lam, Or.inr ⟨κ, lam, hlt, Or.inl rfl⟩⟩ = 2 :=
      sqNorm_eq_two_of_diagonal (realNormal_diagonal_one κ lam hlt)
    have hne : κ ≠ lam := hlt.ne
    refine ⟨Equiv.swap κ lam, fun μ => if μ = κ ∨ μ = lam then -1 else 1, fun x μ => ?_⟩
    have hd : euclidDot (basisVector κ + basisVector lam) x = x κ + x lam := by
      rw [euclidDot_add_left, euclidDot_basisVector, euclidDot_basisVector]
    rw [hyperplaneReflection_apply, hq]
    change x μ - 2 * (euclidDot (basisVector κ + basisVector lam) x - 0) *
      (2⁻¹ * (basisVector κ + basisVector lam) μ) = _
    rw [hd]
    simp only [basisVector, Pi.add_apply, Pi.single_apply]
    by_cases h : μ = κ
    · subst h
      simp [hne]
      ring
    · by_cases h' : μ = lam
      · subst h'
        simp [h]
        ring
      · simp [h, h', Equiv.swap_apply_of_ne_of_ne h h']
  · have hq : ReflNormal.sqNorm
        ⟨basisVector κ - basisVector lam, Or.inr ⟨κ, lam, hlt, Or.inr rfl⟩⟩ = 2 :=
      sqNorm_eq_two_of_diagonal (realNormal_diagonal_neg_one κ lam hlt)
    have hne : κ ≠ lam := hlt.ne
    refine ⟨Equiv.swap κ lam, fun _ => 1, fun x μ => ?_⟩
    have hd : euclidDot (basisVector κ - basisVector lam) x = x κ - x lam := by
      rw [euclidDot_sub_left, euclidDot_basisVector, euclidDot_basisVector]
    rw [hyperplaneReflection_apply, hq]
    change x μ - 2 * (euclidDot (basisVector κ - basisVector lam) x - 0) *
      (2⁻¹ * (basisVector κ - basisVector lam) μ) = _
    rw [hd]
    simp only [basisVector, Pi.sub_apply, Pi.single_apply]
    by_cases h : μ = κ
    · subst h
      simp [hne]
      ring
    · by_cases h' : μ = lam
      · subst h'
        simp [h]
        ring
      · simp [h, h', Equiv.swap_apply_of_ne_of_ne h h']
theorem lt_of_lt_euclidDot_hyperplaneReflection (n : ReflNormal) (c : ℝ) (x : Fin 4 → ℝ)
    (h : c < euclidDot n.1 (hyperplaneReflection n c x)) : euclidDot n.1 x < c := by
  rw [euclidDot_hyperplaneReflection] at h
  linarith
theorem oppositeSideTuples_holds (s : Conventions.StandingParameters) (n : ReflNormal) (c : ℝ) :
    OppositeSideTuples s n c := by
  intro X Y hX hY
  have hXs := mem_sepTuplesIn_iff.1 hX
  have hYs := mem_sepTuplesIn_iff.1 hY
  have hside : ∀ i, tsupport (tupleComponents (reflectTuple s n c X) i) ⊆
      {x : Fin 4 → ℝ | euclidDot n.1 x < c} := by
    intro i x hx
    have hx' : x ∈ (hyperplaneReflectionEquiv s n c).symm ⁻¹' tsupport (tupleComponents X i) := by
      have h := FourSpaceSymbols.tsupport_transportFn
        (isDistIsometry_hyperplaneReflectionEquiv s n c) (tupleComponents X i)
      rw [← h]
      exact hx
    exact lt_of_lt_euclidDot_hyperplaneReflection n c x (hXs i hx')
  refine ⟨hside, joinTuple_mem_allSeparatedTuples fun i j => ?_⟩
  refine Set.disjoint_left.2 fun x h1 h2 => ?_
  have h3 : euclidDot n.1 x < c := hside i h1
  have h4 : c < euclidDot n.1 x := hYs j h2
  linarith
theorem reflectionEqShiftOriginReflection_holds (s : Conventions.StandingParameters)
    (n : ReflNormal) (c : ℝ) : ReflectionEqShiftOriginReflection s n c := by
  intro x
  change hyperplaneReflection n c x = hyperplaneReflection n 0 x + (2 * c) • n.dual
  funext μ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyperplaneReflection_apply,
    ReflNormal.dual]
  ring
theorem hyperplaneReflection_sub_of_mem (n : ReflNormal) (c : ℝ) {v : Fin 4 → ℝ}
    (hv : euclidDot n.1 v = c) (x : Fin 4 → ℝ) :
    hyperplaneReflection n c x - v = hyperplaneReflection n 0 (x - v) := by
  funext μ
  simp only [Pi.sub_apply, hyperplaneReflection_apply, euclidDot_sub_right, hv]
  ring
theorem reflectionAboutMirrorPoint_holds (s : Conventions.StandingParameters) (n : ReflNormal)
    (c : ℝ) : ReflectionAboutMirrorPoint s n c := by
  refine ⟨by rw [euclidDot_smul_right, euclidDot_dual, mul_one], fun v hv =>
    ⟨hyperplaneReflection_sub_of_mem n c hv, fun Z h x => ?_, fun Y => ?_⟩⟩
  · have e1 := FourSpaceSymbols.translateFn_apply (s := s) v h (hyperplaneReflection n c x)
    have e2 := FourSpaceSymbols.translateFn_apply (s := s) v
      (fun y : Fin 4 → ℝ => h (hyperplaneReflection n 0 y)) x
    exact e1.trans ((congrArg h (hyperplaneReflection_sub_of_mem n c hv x)).trans e2.symm)
  · refine sepTuple_ext rfl fun i => ?_
    funext x
    have e : ∀ y : Fin 4 → ℝ,
        hyperplaneReflection n c y + -v = hyperplaneReflection n 0 (y + -v) := fun y => by
      rw [← sub_eq_add_neg, ← sub_eq_add_neg]
      exact hyperplaneReflection_sub_of_mem n c hv y
    exact congrArg (Y.1.2 i) (e x)
theorem statement_holds : Statement :=
  ⟨isOrthogonalReflection_hyperplaneReflection, fun a' _ => latticeAlignedEqClassMirrors a',
    originReflection_hyperoctahedral, fun s n c =>
      ⟨oppositeSideTuples_holds s n c, reflectionEqShiftOriginReflection_holds s n c,
        reflectionAboutMirrorPoint_holds s n c⟩⟩
end MirrorReflections
end InfiniteLattice.EuclideanMirrors
end YangMills.Construction
end
