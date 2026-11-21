import YangMills.Construction.EuclideanFunctionals.ForwardTubeAndTheSemigroupOfItsOperators
import YangMills.Construction.EuclideanFunctionals.OperatorsOfThePlaneSemigroupExpansionAndProductsOverTheWedge
import YangMills.Construction.RotationInvariance.OrderedTuplesOfFunctionsAndTheCosineOfAnAperture
import Mathlib
set_option autoImplicit false
open Complex ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TubeSemigroup
open YangMills.Construction.ForwardTube
theorem pair_ext_lightCone {v w : ℂ × ℂ} (hp : lightConePlus v = lightConePlus w)
    (hm : lightConeMinus v = lightConeMinus w) : v = w := by
  rw [← ofLightConeCoords_lightConePlus_lightConeMinus v,
    ← ofLightConeCoords_lightConePlus_lightConeMinus w, hp, hm]
theorem lightConePlus_re (v : ℂ × ℂ) : (lightConePlus v).re = v.1.re - v.2.im := by
  simp [lightConePlus, sub_eq_add_neg]
theorem lightConeMinus_re (v : ℂ × ℂ) : (lightConeMinus v).re = v.1.re + v.2.im := by
  simp [lightConeMinus]
theorem mem_forwardTube_iff (v : ℂ × ℂ) :
    v ∈ forwardTube ↔ 0 < v.1.re - v.2.im ∧ 0 < v.1.re + v.2.im := by
  change ((lightConePlus v).re > 0 ∧ (lightConeMinus v).re > 0) ↔ _
  rw [lightConePlus_re, lightConeMinus_re]
theorem complexBoost_complexBoost (z w : ℂ) (v : ℂ × ℂ) :
    complexBoost z (complexBoost w v) = complexBoost (z + w) v := by
  apply pair_ext_lightCone
  · rw [lightConePlus_complexBoost, lightConePlus_complexBoost, lightConePlus_complexBoost,
      ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · rw [lightConeMinus_complexBoost, lightConeMinus_complexBoost, lightConeMinus_complexBoost,
      ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
theorem complexBoost_zero (v : ℂ × ℂ) : complexBoost 0 v = v := by
  apply pair_ext_lightCone <;> simp [lightConePlus_complexBoost, lightConeMinus_complexBoost]
theorem complexBoost_neg_cancel (z : ℂ) (v : ℂ × ℂ) :
    complexBoost z (complexBoost (-z) v) = v := by
  rw [complexBoost_complexBoost, add_neg_cancel, complexBoost_zero]
theorem mem_image_complexBoost_iff (z : ℂ) (A : Set (ℂ × ℂ)) (v : ℂ × ℂ) :
    v ∈ complexBoost z '' A ↔ complexBoost (-z) v ∈ A := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h := complexBoost_neg_cancel (-z) u
    rw [neg_neg] at h
    rwa [h]
  · intro h
    exact ⟨_, h, complexBoost_neg_cancel z v⟩
theorem image_imagBoost_eq {A : Set (ℂ × ℂ)}
    (hA : ∀ (s : ℝ) (v : ℂ × ℂ), v ∈ A → imagBoost s v ∈ A) (s : ℝ) :
    imagBoost s '' A = A := by
  apply Set.ext
  intro v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hA s u hu
  · intro hv
    refine ⟨imagBoost (-s) v, hA _ _ hv, ?_⟩
    have h : I * ((-s : ℝ) : ℂ) = -(I * (s : ℂ)) := by
      push_cast
      ring
    simp only [imagBoost]
    rw [h]
    exact complexBoost_neg_cancel _ _
theorem image_eq_self_of_involutive {f : ℂ × ℂ → ℂ × ℂ} {A : Set (ℂ × ℂ)}
    (hf : ∀ v, f (f v) = v) (hA : ∀ v ∈ A, f v ∈ A) : f '' A = A := by
  apply Set.ext
  intro v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hA u hu
  · intro hv
    exact ⟨f v, hA v hv, hf v⟩
theorem isOpenConvexConeSet_of_pos_pos {L M : ℂ × ℂ → ℝ} (hL : Continuous L)
    (hM : Continuous M) (hLl : IsLinearMap ℝ L) (hMl : IsLinearMap ℝ M) :
    IsOpenConvexConeSet {v | L v > 0 ∧ M v > 0} := by
  refine ⟨?_, ?_, ?_⟩
  · exact (isOpen_lt continuous_const hL).inter (isOpen_lt continuous_const hM)
  · exact (convex_halfSpace_gt hLl 0).inter (convex_halfSpace_gt hMl 0)
  · rintro v ⟨h₁, h₂⟩ a ha
    refine ⟨?_, ?_⟩
    · rw [hLl.map_smul, smul_eq_mul]
      exact mul_pos ha h₁
    · rw [hMl.map_smul, smul_eq_mul]
      exact mul_pos ha h₂
theorem isLinearMap_re_mul_lightConePlus (a : ℂ) :
    IsLinearMap ℝ fun v : ℂ × ℂ => (a * lightConePlus v).re :=
  { map_add := fun x y => by
      simp only [lightConePlus, Prod.fst_add, Prod.snd_add]
      rw [← Complex.add_re]
      congr 1
      ring
    map_smul := fun r x => by
      simp only [lightConePlus, Prod.smul_fst, Prod.smul_snd, Complex.real_smul, smul_eq_mul]
      rw [← Complex.re_ofReal_mul]
      congr 1
      ring }
theorem isLinearMap_re_mul_lightConeMinus (a : ℂ) :
    IsLinearMap ℝ fun v : ℂ × ℂ => (a * lightConeMinus v).re :=
  { map_add := fun x y => by
      simp only [lightConeMinus, Prod.fst_add, Prod.snd_add]
      rw [← Complex.add_re]
      congr 1
      ring
    map_smul := fun r x => by
      simp only [lightConeMinus, Prod.smul_fst, Prod.smul_snd, Complex.real_smul, smul_eq_mul]
      rw [← Complex.re_ofReal_mul]
      congr 1
      ring }
theorem isOpenConvexConeSet_re_mul (a b : ℂ) :
    IsOpenConvexConeSet
      {v : ℂ × ℂ | (a * lightConePlus v).re > 0 ∧ (b * lightConeMinus v).re > 0} := by
  apply isOpenConvexConeSet_of_pos_pos (L := fun v => (a * lightConePlus v).re)
    (M := fun v => (b * lightConeMinus v).re) _ _ (isLinearMap_re_mul_lightConePlus a)
    (isLinearMap_re_mul_lightConeMinus b)
  · simp only [lightConePlus]
    fun_prop
  · simp only [lightConeMinus]
    fun_prop
theorem image_forwardTube_complexBoost (z : ℂ) :
    complexBoost z '' forwardTube =
      {v : ℂ × ℂ | (exp (I * -z) * lightConePlus v).re > 0 ∧
        (exp (-(I * -z)) * lightConeMinus v).re > 0} := by
  apply Set.ext
  intro v
  rw [mem_image_complexBoost_iff]
  change ((lightConePlus (complexBoost (-z) v)).re > 0 ∧
    (lightConeMinus (complexBoost (-z) v)).re > 0) ↔ _
  rw [lightConePlus_complexBoost, lightConeMinus_complexBoost]
  rfl
theorem complexBoost_ofReal (t : ℝ) (v : ℂ × ℂ) :
    complexBoost (t : ℂ) v =
      (v.1 * (Real.cos t : ℂ) - v.2 * (Real.sin t : ℂ),
        v.1 * (Real.sin t : ℂ) + v.2 * (Real.cos t : ℂ)) := by
  have hp : exp (I * (t : ℂ)) = (Real.cos t : ℂ) + (Real.sin t : ℂ) * I := by
    rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hm : exp (-(I * (t : ℂ))) = (Real.cos t : ℂ) - (Real.sin t : ℂ) * I := by
    rw [show -(I * (t : ℂ)) = ((-t : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  apply pair_ext_lightCone
  · rw [lightConePlus_complexBoost, hp]
    simp only [lightConePlus]
    linear_combination ((Real.sin t : ℂ) * v.2) * I_sq
  · rw [lightConeMinus_complexBoost, hm]
    simp only [lightConeMinus]
    linear_combination ((Real.sin t : ℂ) * v.2) * I_sq
theorem complexBoost_neg_ofReal (t : ℝ) (v : ℂ × ℂ) :
    complexBoost (-(t : ℂ)) v =
      (v.1 * (Real.cos t : ℂ) + v.2 * (Real.sin t : ℂ),
        -(v.1 * (Real.sin t : ℂ)) + v.2 * (Real.cos t : ℂ)) := by
  rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; rfl, complexBoost_ofReal, Real.cos_neg,
    Real.sin_neg]
  push_cast
  apply Prod.ext
  · simp only
    ring
  · simp only
    ring
theorem complexBoost_neg_mem_forwardTube_iff (t : ℝ) (v : ℂ × ℂ) :
    complexBoost (-(t : ℂ)) v ∈ forwardTube ↔
      0 < (v.1.re * Real.cos t + v.2.re * Real.sin t) -
          (-(v.1.im * Real.sin t) + v.2.im * Real.cos t) ∧
        0 < (v.1.re * Real.cos t + v.2.re * Real.sin t) +
          (-(v.1.im * Real.sin t) + v.2.im * Real.cos t) := by
  rw [complexBoost_neg_ofReal, mem_forwardTube_iff]
  simp only [Complex.add_re, Complex.add_im, Complex.neg_im, Complex.re_mul_ofReal,
    Complex.im_mul_ofReal]
theorem embedPlane_pairRe (v : ℂ × ℂ) :
    embedPlane (pairRe v) = ((v.1.re : ℂ), (v.2.re : ℂ)) := by
  simp [embedPlane, pairRe, YangMills.Construction.OneLoopNotation.reVec]
theorem embedPlane_of_mem_realVectors {v : ℂ × ℂ} (hv : v ∈ realVectors) :
    embedPlane (!₂[v.1.re, v.2.re] : RealPlane) = v := by
  obtain ⟨h₁, h₂⟩ := hv
  apply Prod.ext
  · apply Complex.ext <;> simp [embedPlane, h₁]
  · apply Complex.ext <;> simp [embedPlane, h₂]
theorem embedPlane_mem_realVectors (y : RealPlane) : embedPlane y ∈ realVectors :=
  ⟨Complex.ofReal_im _, Complex.ofReal_im _⟩
theorem isOpenConvexConeSet_forwardTube : IsOpenConvexConeSet forwardTube := by
  have h := isOpenConvexConeSet_re_mul 1 1
  simp only [one_mul] at h
  exact h
theorem forwardTubeConeFacts : ForwardTubeConeFacts := by
  refine ⟨?_, isOpenConvexConeSet_forwardTube, ?_, ?_, ?_, fun s =>
    image_imagBoost_eq (fun s _ hv => imagBoost_mem_forwardTube s hv) s⟩
  · apply Set.ext
    intro v
    change ((lightConePlus v).re > 0 ∧ (lightConeMinus v).re > 0) ↔ v.1.re > |v.2.im|
    rw [lightConePlus_re, lightConeMinus_re]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · intro h
      obtain ⟨h₁, h₂⟩ := abs_lt.mp h
      exact ⟨by linarith, by linarith⟩
  · apply Set.ext
    intro v
    constructor
    · rintro ⟨hv, hr⟩
      refine ⟨!₂[v.1.re, v.2.re], ?_, embedPlane_of_mem_realVectors hr⟩
      have h := (mem_forwardTube_iff v).1 hv
      change 0 < (!₂[v.1.re, v.2.re] : RealPlane) 0
      simp only [Matrix.cons_val_zero]
      linarith [h.1, h.2]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(mem_forwardTube_iff _).2 ?_, embedPlane_mem_realVectors y⟩
      have hy' : 0 < y 0 := hy
      simp [embedPlane, hy']
  · apply image_eq_self_of_involutive
    · intro v
      simp [conjPair]
    · intro v hv
      have h := (mem_forwardTube_iff v).1 hv
      rw [mem_forwardTube_iff]
      simp only [conjPair, Complex.conj_re, Complex.conj_im]
      constructor <;> linarith [h.1, h.2]
  · intro v hv
    have h := (mem_forwardTube_iff v).1 hv
    rw [mem_forwardTube_iff, embedPlane_pairRe]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    constructor <;> linarith [h.1, h.2]
theorem lightConePlus_tubeStar_eq_conj (v : ℂ × ℂ) :
    lightConePlus (tubeStar v) = conj (lightConePlus v) := by
  simp only [lightConePlus, tubeStar, map_add, map_mul, Complex.conj_I]
  ring
theorem lightConeMinus_tubeStar_eq_conj (v : ℂ × ℂ) :
    lightConeMinus (tubeStar v) = conj (lightConeMinus v) := by
  simp only [lightConeMinus, tubeStar, map_sub, map_mul, Complex.conj_I]
  ring
theorem exp_I_mul_I_mul_ofReal (s : ℝ) :
    exp (I * (I * (s : ℂ))) = ((Real.exp (-s) : ℝ) : ℂ) := by apply _root_.YangMills.SharedProofs.p81843 <;> assumption
theorem exp_neg_I_mul_I_mul_ofReal (s : ℝ) :
    exp (-(I * (I * (s : ℂ)))) = ((Real.exp s : ℝ) : ℂ) := by apply _root_.YangMills.SharedProofs.p100365 <;> assumption
theorem tubeStarFacts : TubeStarFacts := by
  refine ⟨?_, ?_, ?_, ?_,
    fun v => ⟨lightConePlus_tubeStar_eq_conj v, lightConeMinus_tubeStar_eq_conj v⟩, ?_, ?_⟩
  · intro v w
    apply Prod.ext
    · simp [tubeStar]
    · simp only [tubeStar, Prod.snd_add, map_add]
      ring
  · intro a v
    apply Prod.ext
    · simp [tubeStar]
    · simp [tubeStar]
  · apply image_eq_self_of_involutive
    · intro v
      simp [tubeStar]
    · intro v hv
      refine ⟨?_, ?_⟩
      · rw [lightConePlus_tubeStar_eq_conj, Complex.conj_re]
        exact hv.1
      · rw [lightConeMinus_tubeStar_eq_conj, Complex.conj_re]
        exact hv.2
  · apply Prod.ext
    · simp [tubeStar, embedPlane, RealPlane.unitX]
    · simp [tubeStar, embedPlane, RealPlane.unitX]
  · intro s v
    apply pair_ext_lightCone
    · rw [lightConePlus_tubeStar_eq_conj, imagBoost, imagBoost, lightConePlus_complexBoost,
        lightConePlus_complexBoost, exp_I_mul_I_mul_ofReal, lightConePlus_tubeStar_eq_conj,
        map_mul, Complex.conj_ofReal]
    · rw [lightConeMinus_tubeStar_eq_conj, imagBoost, imagBoost, lightConeMinus_complexBoost,
        lightConeMinus_complexBoost, exp_neg_I_mul_I_mul_ofReal,
        lightConeMinus_tubeStar_eq_conj, map_mul, Complex.conj_ofReal]
  · intro y
    apply Prod.ext
    · simp [tubeStar, embedPlane, RealPlane.reflectFirst]
    · simp [tubeStar, embedPlane, RealPlane.reflectFirst]
theorem rotatedTubeConeFacts : RotatedTubeConeFacts := by
  intro θ
  have hmem : ∀ v, v ∈ rotatedForwardTube θ ↔
      complexBoost (-((θ : ℝ) : ℂ)) v ∈ forwardTube :=
    fun v => mem_image_complexBoost_iff _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · change IsOpenConvexConeSet (complexBoost ((θ : ℝ) : ℂ) '' forwardTube)
    rw [image_forwardTube_complexBoost]
    exact isOpenConvexConeSet_re_mul _ _
  · apply image_imagBoost_eq
    intro s v hv
    rw [hmem] at hv ⊢
    have h := imagBoost_mem_forwardTube s hv
    rw [imagBoost, complexBoost_complexBoost, add_comm,
      ← complexBoost_complexBoost] at h
    exact h
  · intro v hv
    rw [hmem, complexBoost_neg_mem_forwardTube_iff] at hv
    rw [hmem, complexBoost_neg_mem_forwardTube_iff, embedPlane_pairRe]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    constructor <;> linarith [hv.1, hv.2]
  · have hdir0 : rotatedDirection θ 0 = Real.cos θ := by
      simp [rotatedDirection, rotatedUnitVector_eq_cos_sin, Complex.cos_ofReal_re]
    have hdir1 : rotatedDirection θ 1 = Real.sin θ := by
      simp [rotatedDirection, rotatedUnitVector_eq_cos_sin, Complex.sin_ofReal_re]
    apply Set.ext
    intro v
    constructor
    · rintro ⟨hv, hr⟩
      refine ⟨!₂[v.1.re, v.2.re], ?_, embedPlane_of_mem_realVectors hr⟩
      rw [hmem, complexBoost_neg_mem_forwardTube_iff, hr.1, hr.2] at hv
      change 0 < inner ℝ (rotatedDirection θ) (!₂[v.1.re, v.2.re] : RealPlane)
      rw [inner_eq_coord_sum, hdir0, hdir1]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith [hv.1, hv.2]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, embedPlane_mem_realVectors y⟩
      have hy' : 0 < inner ℝ (rotatedDirection θ) y := hy
      rw [inner_eq_coord_sum, hdir0, hdir1] at hy'
      rw [hmem, complexBoost_neg_mem_forwardTube_iff]
      simp only [embedPlane, Complex.ofReal_re, Complex.ofReal_im]
      constructor <;> linarith
theorem lightConeExponentIdentity : LightConeExponentIdentity := by
  intro v E q
  simp only [lightConePlus, lightConeMinus]
  push_cast
  ring
def singletonPairEquiv :
    (Fin 1 → ℂ × ℂ) ≃ YangMills.Construction.Coordinates.ComplexCoordinates 2 :=
  pairTupleEquiv 1
theorem singletonPairEquiv_symm_apply (z : YangMills.Construction.Coordinates.ComplexCoordinates 2) :
    singletonPairEquiv.symm z 0 = (z 0, z 1) := by
  have hz := singletonPairEquiv.apply_symm_apply z
  have h₀ : singletonPairEquiv (singletonPairEquiv.symm z) 0 =
      (singletonPairEquiv.symm z 0).1 :=
    pairTupleEquiv_apply_fst (singletonPairEquiv.symm z) 0
  have h₁ : singletonPairEquiv (singletonPairEquiv.symm z) 1 =
      (singletonPairEquiv.symm z 0).2 :=
    pairTupleEquiv_apply_snd (singletonPairEquiv.symm z) 0
  rw [hz] at h₀ h₁
  exact Prod.ext h₀.symm h₁.symm
theorem isHolomorphicOnOpen_of_singleton {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [CompleteSpace Y] {A : Set (ℂ × ℂ)} {f : ℂ × ℂ → Y}
    (h : HolomorphicVectorOnTuples {x : Fin 1 → ℂ × ℂ | x 0 ∈ A} fun x => f (x 0)) :
    YangMills.Construction.BanachValued.IsHolomorphicOnOpen
      {z : YangMills.Construction.Coordinates.ComplexCoordinates 2 | (z 0, z 1) ∈ A}
      fun z : YangMills.Construction.Coordinates.ComplexCoordinates 2 => f (z 0, z 1) := by
  have h' : YangMills.Construction.BanachValued.IsHolomorphicOnOpen
      (singletonPairEquiv '' {x : Fin 1 → ℂ × ℂ | x 0 ∈ A})
      ((fun x : Fin 1 → ℂ × ℂ => f (x 0)) ∘ singletonPairEquiv.symm) := h
  have hset : singletonPairEquiv '' {x : Fin 1 → ℂ × ℂ | x 0 ∈ A} =
      {z : YangMills.Construction.Coordinates.ComplexCoordinates 2 | (z 0, z 1) ∈ A} := by
    apply Set.ext
    intro z
    rw [Equiv.image_eq_preimage_symm]
    change singletonPairEquiv.symm z 0 ∈ A ↔ _
    rw [singletonPairEquiv_symm_apply]
    rfl
  have hfun : ((fun x : Fin 1 → ℂ × ℂ => f (x 0)) ∘ singletonPairEquiv.symm) =
      fun z : YangMills.Construction.Coordinates.ComplexCoordinates 2 => f (z 0, z 1) := by
    funext z
    simp only [Function.comp_apply, singletonPairEquiv_symm_apply]
  rw [hset, hfun] at h'
  exact h'
theorem forwardTubeSemigroupFacts_of_holds (hPlane : Holds) : ForwardTubeSemigroupFacts := by
  refine ⟨forwardTubeConeFacts, tubeStarFacts, rotatedTubeConeFacts,
    lightConeExponentIdentity, ?_⟩
  intro c S σ hc
  obtain ⟨hB, hS, -, hE, hR, -⟩ := hPlane c S σ hc
  have hzero : (0 : ℂ × ℂ) ∈ closedForwardTube := by
    refine ⟨?_, ?_⟩ <;> simp [lightConePlus, lightConeMinus]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro v hv
    exact ⟨hB.2.1 v hv, (hS.2 v hv v hv).2.2.1⟩
  · rw [hB.2.1 0 hzero, hS.1]
  · intro v hv v' hv'
    obtain ⟨hadd, -, -, hmul, -, -⟩ := hS.2 v hv v' hv'
    rw [hB.2.1 _ hadd, hmul]
  · intro v hv
    obtain ⟨-, hstar, -, -, hs, -⟩ := hS.2 v hv v hv
    rw [hB.2.1 _ hstar, hs]
  · exact isHolomorphicOnOpen_of_singleton hE.2
  · intro y hy F
    exact (hR y hy).2 F
end YangMills.Construction.EuclideanFunctionals.TubeSemigroup
