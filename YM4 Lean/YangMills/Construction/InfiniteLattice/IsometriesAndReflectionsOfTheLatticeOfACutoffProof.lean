import YangMills.Construction.InfiniteLattice.PlaquetteFunctionAndActionOfTheIsometriesProof
import YangMills.Construction.InfiniteLattice.EightLoopsRoundAPlaquetteProof
import YangMills.Construction.InfiniteLattice.IsometriesAndReflectionsOfTheLatticeOfACutoff
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfFourSpaceAsBijections
import YangMills.Construction.InfiniteLattice.WilsonMeasureOfAPeriodLatticeAndItsExtensionAreStatesProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace CutoffSymmetries
variable {a : ℝ}
def IsStepApart (x y : LatticePoint a) : Prop :=
  ∃ μ : Fin 4, y - x = axisStep a μ ∨ y - x = -axisStep a μ
theorem IsStepApart.symm {x y : LatticePoint a} (h : IsStepApart x y) : IsStepApart y x := by apply _root_.YangMills.Construction.InfiniteLattice.FaceEnergyAndMotions.Neighbours.symm <;> assumption
open Classical in
def linkValue (U : GaugeField a) (x y : LatticePoint a) : Matrices.ComplexMatrix2.specialUnitary :=
  if h : IsStepApart x y then U ⟨x, y, h⟩ else 1
theorem linkValue_of_isStepApart (U : GaugeField a) {x y : LatticePoint a} (h : IsStepApart x y) :
    linkValue U x y = U ⟨x, y, h⟩ :=
  dif_pos h
theorem linkValue_swap (U : GaugeField a) (x y : LatticePoint a) :
    linkValue U y x = (linkValue U x y)⁻¹ := by
  by_cases h : IsStepApart x y
  · rw [linkValue_of_isStepApart U h.symm, linkValue_of_isStepApart U h]
    exact U.2 ⟨x, y, h⟩
  · have h' : ¬ IsStepApart y x := fun k => h k.symm
    simp [linkValue, h, h']
def loopReTrace (U : GaugeField a) (c₀ c₁ c₂ c₃ : LatticePoint a) : ℝ :=
  (Matrices.ComplexMatrix2.fullTrace ((linkValue U c₀ c₁ * linkValue U c₁ c₂ * linkValue U c₂ c₃ *
    linkValue U c₃ c₀ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re
theorem re_fullTrace_inv (g : Matrices.ComplexMatrix2.specialUnitary) :
    (Matrices.ComplexMatrix2.fullTrace ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
      Matrices.ComplexMatrix2)).re =
    (Matrices.ComplexMatrix2.fullTrace (g : Matrices.ComplexMatrix2)).re := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.re_fullTrace_inv <;> assumption
theorem re_fullTrace_mul_comm (g h : Matrices.ComplexMatrix2.specialUnitary) :
    (Matrices.ComplexMatrix2.fullTrace ((g * h : Matrices.ComplexMatrix2.specialUnitary) :
      Matrices.ComplexMatrix2)).re =
    (Matrices.ComplexMatrix2.fullTrace ((h * g : Matrices.ComplexMatrix2.specialUnitary) :
      Matrices.ComplexMatrix2)).re := by apply _root_.YangMills.Construction.InfiniteLattice.PlaquetteLoops.re_fullTrace_mul_comm <;> assumption
theorem loopReTrace_rotate (U : GaugeField a) (c₀ c₁ c₂ c₃ : LatticePoint a) :
    loopReTrace U c₀ c₁ c₂ c₃ = loopReTrace U c₁ c₂ c₃ c₀ := by
  simp only [loopReTrace]
  rw [mul_assoc, mul_assoc, re_fullTrace_mul_comm]
  simp only [mul_assoc]
theorem loopReTrace_reverse (U : GaugeField a) (c₀ c₁ c₂ c₃ : LatticePoint a) :
    loopReTrace U c₀ c₃ c₂ c₁ = loopReTrace U c₀ c₁ c₂ c₃ := by
  simp only [loopReTrace]
  rw [← re_fullTrace_inv (linkValue U c₀ c₁ * linkValue U c₁ c₂ * linkValue U c₂ c₃ *
    linkValue U c₃ c₀)]
  congr 3
  rw [linkValue_swap U c₃ c₀, linkValue_swap U c₂ c₃, linkValue_swap U c₁ c₂,
    linkValue_swap U c₀ c₁]
  simp only [mul_inv_rev, mul_assoc]
def squareSpan (z d d' : AmbientSpace) : Set AmbientSpace :=
  {y | ∃ t ∈ Icc (0 : ℝ) 1, ∃ t' ∈ Icc (0 : ℝ) 1, y = z + t • d + t' • d'}
theorem squareSpan_swap (z d d' : AmbientSpace) : squareSpan z d' d = squareSpan z d d' := by
  ext y
  constructor
  · rintro ⟨t, ht, t', ht', rfl⟩
    exact ⟨t', ht', t, ht, add_right_comm _ _ _⟩
  · rintro ⟨t, ht, t', ht', rfl⟩
    exact ⟨t', ht', t, ht, add_right_comm _ _ _⟩
theorem squareSpan_flip (z d d' : AmbientSpace) :
    squareSpan (z + d) (-d) d' = squareSpan z d d' := by
  ext y
  constructor
  · rintro ⟨t, ht, t', ht', rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, t', ht', ?_⟩
    rw [sub_smul, one_smul, smul_neg]
    abel
  · rintro ⟨t, ht, t', ht', rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, t', ht', ?_⟩
    rw [sub_smul, one_smul, smul_neg]
    abel
structure SpansFace (z d d' : LatticePoint a) (q : ElementaryPlaquette a) : Prop where
  closedSquare_eq : q.closedSquare = squareSpan (z : AmbientSpace) (d : AmbientSpace) (d' : AmbientSpace)
  center_eq : q.center =
    (z : AmbientSpace) + (1 / 2 : ℝ) • (d : AmbientSpace) + (1 / 2 : ℝ) • (d' : AmbientSpace)
  faceEnergy_eq : ∀ U : GaugeField a,
    faceEnergy U q = 1 - (1 / 2) * loopReTrace U z (z + d) (z + d + d') (z + d')
theorem SpansFace.swap {z d d' : LatticePoint a} {q : ElementaryPlaquette a} (h : SpansFace z d d' q) :
    SpansFace z d' d q where
  closedSquare_eq := by rw [h.closedSquare_eq, squareSpan_swap]
  center_eq := by rw [h.center_eq, add_right_comm]
  faceEnergy_eq U := by
    rw [h.faceEnergy_eq, add_right_comm z d' d, loopReTrace_reverse]
theorem SpansFace.flip {z d d' : LatticePoint a} {q : ElementaryPlaquette a} (h : SpansFace z d d' q) :
    SpansFace (z + d) (-d) d' q where
  closedSquare_eq := by
    rw [h.closedSquare_eq, ← squareSpan_flip]
    rfl
  center_eq := by
    rw [h.center_eq]
    have e : (((z + d : LatticePoint a) : AmbientSpace)) = (z : AmbientSpace) + (d : AmbientSpace) := rfl
    have e' : ((-d : LatticePoint a) : AmbientSpace) = -(d : AmbientSpace) := rfl
    rw [e, e']
    funext κ
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  faceEnergy_eq U := by
    have e₁ : z + d + -d = z := by abel
    rw [h.faceEnergy_eq, e₁, loopReTrace_reverse U (z + d) (z + d + d') (z + d') z,
      loopReTrace_rotate U z]
theorem coe_axisStep (μ : Fin 4) :
    ((axisStep a μ : LatticePoint a) : AmbientSpace) = a • (Pi.single μ 1 : AmbientSpace) := by
  funext κ
  by_cases h : κ = μ
  · subst h
    simp [axisStep]
  · simp [axisStep, Pi.single_eq_of_ne h]
theorem isStepApart_add_axisStep (x : LatticePoint a) (μ : Fin 4) : IsStepApart x (x + axisStep a μ) :=
  ⟨μ, Or.inl (by abel)⟩
theorem isStepApart_add_axisStep_back (x : LatticePoint a) (μ : Fin 4) :
    IsStepApart (x + axisStep a μ) x :=
  (isStepApart_add_axisStep x μ).symm
theorem linkValue_forward (U : GaugeField a) (x : LatticePoint a) (μ : Fin 4) :
    linkValue U x (x + axisStep a μ) = U (Link.forwardFrom x μ) :=
  linkValue_of_isStepApart U (isStepApart_add_axisStep x μ)
theorem spansFace_self (p : ElementaryPlaquette a) :
    SpansFace p.corner (axisStep a p.lowAxis) (axisStep a p.highAxis) p where
  closedSquare_eq := by
    ext y
    constructor
    · rintro ⟨t, ht, t', ht', rfl⟩
      refine ⟨t, ht, t', ht', ?_⟩
      rw [coe_axisStep, coe_axisStep, smul_add, smul_comm a t, smul_comm a t', add_assoc]
    · rintro ⟨t, ht, t', ht', rfl⟩
      refine ⟨t, ht, t', ht', ?_⟩
      rw [coe_axisStep, coe_axisStep, smul_add, smul_comm a t, smul_comm a t', add_assoc]
  center_eq := by
    rw [coe_axisStep, coe_axisStep]
    funext κ
    simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> ring
  faceEnergy_eq U := by
    have e : p.corner + axisStep a p.lowAxis + axisStep a p.highAxis =
        p.corner + axisStep a p.highAxis + axisStep a p.lowAxis := add_right_comm _ _ _
    have h₀ := linkValue_forward U p.corner p.lowAxis
    have h₁ := linkValue_forward U (p.corner + axisStep a p.lowAxis) p.highAxis
    have h₂ := linkValue_forward U (p.corner + axisStep a p.highAxis) p.lowAxis
    have h₃ := linkValue_forward U p.corner p.highAxis
    have h₄ : linkValue U (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis)
        (p.corner + axisStep a p.highAxis) =
        (U (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis))⁻¹ := by
      rw [linkValue_swap U (p.corner + axisStep a p.highAxis), e, h₂]
    have h₅ : linkValue U (p.corner + axisStep a p.highAxis) p.corner =
        (U (Link.forwardFrom p.corner p.highAxis))⁻¹ := by
      rw [linkValue_swap U p.corner, h₃]
    have hprod : linkValue U p.corner (p.corner + axisStep a p.lowAxis) *
        linkValue U (p.corner + axisStep a p.lowAxis)
          (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis) *
        linkValue U (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis)
          (p.corner + axisStep a p.highAxis) *
        linkValue U (p.corner + axisStep a p.highAxis) p.corner = faceHolonomy U p := by
      rw [h₀, h₁, h₄, h₅]
      rfl
    rw [faceEnergy, loopReTrace, hprod]
def SpansFaceEverywhere (d d' : LatticePoint a) : Prop :=
  ∀ z : LatticePoint a, ∃ q : ElementaryPlaquette a, SpansFace z d d' q
theorem SpansFaceEverywhere.swap {d d' : LatticePoint a} (h : SpansFaceEverywhere d d') :
    SpansFaceEverywhere d' d := fun z => by
  obtain ⟨q, hq⟩ := h z
  exact ⟨q, hq.swap⟩
theorem SpansFaceEverywhere.flip {d d' : LatticePoint a} (h : SpansFaceEverywhere d d') :
    SpansFaceEverywhere (-d) d' := fun z => by
  obtain ⟨q, hq⟩ := h (z - d)
  have := hq.flip
  rw [sub_add_cancel] at this
  exact ⟨q, this⟩
theorem spansFaceEverywhere_of_lt {α β : Fin 4} (h : α < β) {d d' : LatticePoint a}
    (hd : d = axisStep a α ∨ d = -axisStep a α) (hd' : d' = axisStep a β ∨ d' = -axisStep a β) :
    SpansFaceEverywhere d d' := by
  have base : SpansFaceEverywhere (axisStep a α) (axisStep a β) := fun z =>
    ⟨⟨z, α, β, h⟩, spansFace_self (⟨z, α, β, h⟩ : ElementaryPlaquette a)⟩
  have second : SpansFaceEverywhere (axisStep a α) (-axisStep a β) := base.swap.flip.swap
  rcases hd with rfl | rfl <;> rcases hd' with rfl | rfl
  · exact base
  · exact second
  · exact base.flip
  · exact second.flip
theorem spansFaceEverywhere_of_ne {α β : Fin 4} (h : α ≠ β) {d d' : LatticePoint a}
    (hd : d = axisStep a α ∨ d = -axisStep a α) (hd' : d' = axisStep a β ∨ d' = -axisStep a β) :
    SpansFaceEverywhere d d' := by
  rcases lt_or_gt_of_ne h with h | h
  · exact spansFaceEverywhere_of_lt h hd hd'
  · exact (spansFaceEverywhere_of_lt h hd' hd).swap
theorem center_injective (ha : a ≠ 0) :
    Function.Injective (ElementaryPlaquette.center : ElementaryPlaquette a → AmbientSpace) := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.center_injective <;> assumption
theorem linkValue_pullbackField (r : LatticeSymmetry a) (U : GaugeField a) {x y : LatticePoint a}
    (h : IsStepApart x y) :
    linkValue (r.pullbackField U) x y = linkValue U (r.pointMap x) (r.pointMap y) := by
  rw [linkValue_of_isStepApart _ h]
  exact (linkValue_of_isStepApart U (r.linkMap ⟨x, y, h⟩).isAdjacent).symm
theorem exists_image_of_axisStep (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace)
    (hw : w ∈ hyperoctahedralLinearGroup) (μ : Fin 4) :
    ∃ (α : Fin 4) (d : LatticePoint a), (d = axisStep a α ∨ d = -axisStep a α) ∧
      (d : AmbientSpace) = w ((axisStep a μ : LatticePoint a) : AmbientSpace) := by
  have hmem : w (Pi.single μ 1) ∈ signedUnitVectors := by
    rw [← show w '' signedUnitVectors = signedUnitVectors from hw]
    exact mem_image_of_mem _ ⟨μ, Or.inl rfl⟩
  obtain ⟨α, h | h⟩ := hmem
  · refine ⟨α, axisStep a α, Or.inl rfl, ?_⟩
    rw [coe_axisStep, coe_axisStep, map_smul, h]
  · refine ⟨α, -axisStep a α, Or.inr rfl, ?_⟩
    have e : ((-axisStep a α : LatticePoint a) : AmbientSpace) =
        -((axisStep a α : LatticePoint a) : AmbientSpace) := rfl
    rw [e, coe_axisStep, coe_axisStep, map_smul, h, smul_neg]
theorem axes_ne_of_images (ha : a ≠ 0) (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) {μ ν α : Fin 4}
    (hμν : μ ≠ ν) {d d' : LatticePoint a} (hd : d = axisStep a α ∨ d = -axisStep a α)
    (hd' : d' = axisStep a α ∨ d' = -axisStep a α)
    (hdw : (d : AmbientSpace) = w ((axisStep a μ : LatticePoint a) : AmbientSpace))
    (hdw' : (d' : AmbientSpace) = w ((axisStep a ν : LatticePoint a) : AmbientSpace)) : False := by
  have hs : ((axisStep a μ : LatticePoint a) : AmbientSpace) =
      ((axisStep a ν : LatticePoint a) : AmbientSpace) ∨
      ((axisStep a μ : LatticePoint a) : AmbientSpace) =
      -((axisStep a ν : LatticePoint a) : AmbientSpace) := by
    have hdd : d = d' ∨ d = -d' := by
      rcases hd with rfl | rfl <;> rcases hd' with rfl | rfl <;> simp
    rcases hdd with e | e
    · left
      apply w.injective
      rw [← hdw, ← hdw', e]
    · right
      apply w.injective
      rw [map_neg, ← hdw, ← hdw', e]
      rfl
  have hval : ∀ κ : Fin 4, ((axisStep a κ : LatticePoint a) : AmbientSpace) μ =
      if μ = κ then a else 0 := fun κ => by
    rw [coe_axisStep]
    by_cases h : μ = κ
    · subst h
      simp
    · simp [h]
  rcases hs with e | e
  · have := congrFun e μ
    rw [hval, hval] at this
    simp [hμν] at this
    exact ha this
  · have := congrFun e μ
    rw [Pi.neg_apply, hval, hval] at this
    simp [hμν] at this
    exact ha this
theorem exists_image (ha : a ≠ 0) (r : LatticeSymmetry a) (p : ElementaryPlaquette a) :
    ∃ q : ElementaryPlaquette a, q.closedSquare = r.toFun '' p.closedSquare ∧
      q.center = r.toFun p.center ∧
      ∀ U : GaugeField a, faceEnergy (r.pullbackField U) p = faceEnergy U q := by
  obtain ⟨w, hw, v, hrw⟩ := r.toFun_mem_latticeMotions ha
  have hr : ∀ y, r.toFun y = w y + v := fun y => by
    rw [hrw]
    rfl
  obtain ⟨α, d, hd, hdw⟩ := exists_image_of_axisStep (a := a) w hw p.lowAxis
  obtain ⟨β, d', hd', hdw'⟩ := exists_image_of_axisStep (a := a) w hw p.highAxis
  have hαβ : α ≠ β := by
    rintro rfl
    exact axes_ne_of_images ha w p.lowAxis_lt_highAxis.ne hd hd' hdw hdw'
  obtain ⟨q, hq⟩ := spansFaceEverywhere_of_ne hαβ hd hd' (r.pointMap p.corner)
  have hp := spansFace_self p
  have hz : ((r.pointMap p.corner : LatticePoint a) : AmbientSpace) = w (p.corner : AmbientSpace) + v :=
    hr _
  have himg : ∀ t t' : ℝ, r.toFun ((p.corner : AmbientSpace) +
      t • ((axisStep a p.lowAxis : LatticePoint a) : AmbientSpace) +
      t' • ((axisStep a p.highAxis : LatticePoint a) : AmbientSpace)) =
      ((r.pointMap p.corner : LatticePoint a) : AmbientSpace) + t • (d : AmbientSpace) +
        t' • (d' : AmbientSpace) := fun t t' => by
    rw [hr, hz, hdw, hdw', map_add, map_add, map_smul, map_smul]
    abel
  have m₁ : r.pointMap (p.corner + axisStep a p.lowAxis) = r.pointMap p.corner + d := by
    refine Subtype.ext ?_
    have h := himg 1 0
    simp only [one_smul, zero_smul, add_zero] at h
    exact h
  have m₂ : r.pointMap (p.corner + axisStep a p.highAxis) = r.pointMap p.corner + d' := by
    refine Subtype.ext ?_
    have h := himg 0 1
    simp only [one_smul, zero_smul, add_zero] at h
    exact h
  have m₃ : r.pointMap (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis) =
      r.pointMap p.corner + d + d' := by
    refine Subtype.ext ?_
    have h := himg 1 1
    simp only [one_smul] at h
    exact h
  refine ⟨q, ?_, ?_, fun U => ?_⟩
  · rw [hq.closedSquare_eq, hp.closedSquare_eq]
    ext y
    constructor
    · rintro ⟨t, ht, t', ht', rfl⟩
      exact ⟨_, ⟨t, ht, t', ht', rfl⟩, himg t t'⟩
    · rintro ⟨_, ⟨t, ht, t', ht', rfl⟩, rfl⟩
      exact ⟨t, ht, t', ht', himg t t'⟩
  · rw [hq.center_eq, hp.center_eq, himg]
  · rw [hp.faceEnergy_eq, hq.faceEnergy_eq]
    simp only [loopReTrace]
    rw [linkValue_pullbackField r U (isStepApart_add_axisStep p.corner p.lowAxis),
      linkValue_pullbackField r U (isStepApart_add_axisStep (p.corner + axisStep a p.lowAxis) p.highAxis),
      linkValue_pullbackField r U (x := p.corner + axisStep a p.lowAxis + axisStep a p.highAxis)
        (y := p.corner + axisStep a p.highAxis)
        ⟨p.lowAxis, Or.inr (by abel)⟩,
      linkValue_pullbackField r U (isStepApart_add_axisStep_back p.corner p.highAxis), m₁, m₂, m₃]
def inverseSymmetry (r : LatticeSymmetry a) : LatticeSymmetry a where
  toFun := r.toEquivAmbient.symm
  preservesDist x y := by
    have h := r.preservesDist (r.toEquivAmbient.symm x) (r.toEquivAmbient.symm y)
    have e : ∀ u, r.toFun (r.toEquivAmbient.symm u) = u := r.toEquivAmbient.apply_symm_apply
    rw [e, e] at h
    exact h.symm
  image_eq := by
    have e : ∀ u, r.toFun (r.toEquivAmbient.symm u) = u := r.toEquivAmbient.apply_symm_apply
    have e' : ∀ u, r.toEquivAmbient.symm (r.toFun u) = u := r.toEquivAmbient.symm_apply_apply
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ r.toFun '' (latticeSubgroup a : Set AmbientSpace) := by
        rw [r.image_eq]
        exact hz
      obtain ⟨u, hu, rfl⟩ := hz'
      rw [e']
      exact hu
    · intro hy
      have hy' : r.toFun y ∈ (latticeSubgroup a : Set AmbientSpace) := by
        rw [← r.image_eq]
        exact mem_image_of_mem _ hy
      exact ⟨_, hy', e' y⟩
def faceEquiv (ha : a ≠ 0) (r : LatticeSymmetry a) : ElementaryPlaquette a ≃ ElementaryPlaquette a :=
  Equiv.ofBijective (fun p => (exists_image ha r p).choose) (by
    have hb : ∀ (s : LatticeSymmetry a) (p : ElementaryPlaquette a),
        (exists_image ha s p).choose.center = s.toFun p.center := fun s p =>
      (exists_image ha s p).choose_spec.2.1
    constructor
    · intro p p' h
      apply center_injective ha
      apply r.toFun_injective
      exact (hb r p).symm.trans ((congrArg ElementaryPlaquette.center h).trans (hb r p'))
    · intro p'
      refine ⟨(exists_image ha (inverseSymmetry r) p').choose, ?_⟩
      apply center_injective ha
      exact (hb r _).trans ((congrArg r.toFun (hb (inverseSymmetry r) p')).trans
        (r.toEquivAmbient.apply_symm_apply _)))
theorem center_faceEquiv (ha : a ≠ 0) (r : LatticeSymmetry a) (p : ElementaryPlaquette a) :
    (faceEquiv ha r p).center = r.toFun p.center :=
  (exists_image ha r p).choose_spec.2.1
theorem faceEnergy_faceEquiv (ha : a ≠ 0) (r : LatticeSymmetry a) (p : ElementaryPlaquette a)
    (U : GaugeField a) :
    faceEnergy (r.pullbackField U) p = faceEnergy U (faceEquiv ha r p) :=
  (exists_image ha r p).choose_spec.2.2 U
theorem actOn_smearedEnergy {E : Type*} [AddCommMonoid E] [Module ℝ E] (ha : a ≠ 0)
    (r : LatticeSymmetry a) (f : AmbientSpace → E) :
    r.actOn (smearedEnergy f) = smearedEnergy (r.pushforwardFun f) := by
  funext U
  change (∑ᶠ p : ElementaryPlaquette a, faceEnergy (r.pullbackField U) p • f p.center) =
    ∑ᶠ p : ElementaryPlaquette a, faceEnergy U p • r.pushforwardFun f p.center
  refine Eq.trans ?_ (finsum_comp_equiv (faceEquiv ha r)
    (f := fun p : ElementaryPlaquette a => faceEnergy U p • r.pushforwardFun f p.center))
  refine finsum_congr fun p => ?_
  rw [faceEnergy_faceEquiv ha r p U, center_faceEquiv ha r p,
    LatticeSymmetry.pushforwardFun_apply_toFun]
theorem actionProperties (ha : a ≠ 0) (r r' : LatticeSymmetry a) :
    LatticeSymmetry.ActionProperties r r' := by
  refine ⟨fun _ _ => rfl, fun p => ?_, fun f _ => actOn_smearedEnergy ha r f,
    fun f _ => actOn_smearedEnergy ha r f⟩
  obtain ⟨q, hq, -, hact⟩ := exists_image ha r p
  exact ⟨q, hq, funext hact⟩
theorem reflectTime_apply_timeAxis (t : ℝ) (x : AmbientSpace) :
    reflectTime t x timeAxis = 2 * t - x timeAxis := by
  simp only [reflectTime, coordinateReflection, basisVector, Pi.sub_apply, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul]
  ring
theorem reflectTime_reflectTime (t : ℝ) (x : AmbientSpace) :
    reflectTime t (reflectTime t x) = x := by
  have h := reflectTime_apply_timeAxis t x
  funext κ
  by_cases hκ : κ = timeAxis
  · subst hκ
    rw [reflectTime_apply_timeAxis, h]
    ring
  · simp [reflectTime, coordinateReflection, basisVector, Pi.single_eq_of_ne hκ]
def timeAxisPoint (a : ℝ) (q : ℤ) : LatticePoint a := q • axisStep a timeAxis
theorem timeAxisPoint_apply_timeAxis (q : ℤ) :
    ((timeAxisPoint a q : LatticePoint a) : AmbientSpace) timeAxis = (q : ℝ) * a := by
  change q • ((axisStep a timeAxis : LatticePoint a) : AmbientSpace) timeAxis = _
  rw [coe_axisStep]
  simp
theorem timeReflectionLevelSets (ha : a ≠ 0) : TimeReflectionLevelSets a := by
  refine ⟨fun t => ⟨?_, fun ht => ⟨timeReflect ⟨t, ht⟩, timeReflect_toFun_eq ⟨t, ht⟩⟩⟩,
    ?_, ?_⟩
  · rintro ⟨r, hr⟩
    obtain ⟨n, hn⟩ := (r.pointMap 0).2
    have h₀ : ((r.pointMap 0 : LatticePoint a) : AmbientSpace) = reflectTime t 0 := by
      change r.toFun ((0 : LatticePoint a) : AmbientSpace) = _
      rw [hr]
      rfl
    have h₁ := hn timeAxis
    rw [h₀, reflectTime_apply_timeAxis] at h₁
    refine ⟨n timeAxis, ?_⟩
    have h₂ : (0 : AmbientSpace) timeAxis = 0 := rfl
    rw [h₂] at h₁
    linarith
  · rintro t ⟨q, rfl⟩
    exact ⟨⟨timeAxisPoint a q, timeAxisPoint_apply_timeAxis q⟩, fun x hx => hx⟩
  · rintro t ⟨q, rfl⟩
    have key : ∀ x : LatticePoint a, (x : AmbientSpace) timeAxis = ((q : ℝ) + 1 / 2) * a - a / 2 →
        (x : AmbientSpace) + (a / 2) • basisVector timeAxis ∈ equalTimePlane (((q : ℝ) + 1 / 2) * a) ∧
        (x : AmbientSpace) + (a / 2) • basisVector timeAxis =
          (Link.forwardFrom x timeAxis).midpoint := by
      intro x hx
      constructor
      · change ((x : AmbientSpace) + (a / 2) • basisVector timeAxis) timeAxis = _
        simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, hx]
        ring
      · have e : (((x + axisStep a timeAxis : LatticePoint a)) : AmbientSpace) =
            (x : AmbientSpace) + ((axisStep a timeAxis : LatticePoint a) : AmbientSpace) := rfl
        simp only [Link.midpoint, Link.forwardFrom, e]
        rw [coe_axisStep]
        funext κ
        simp only [basisVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
    refine ⟨fun x hx => ?_, ⟨Link.forwardFrom (timeAxisPoint a q) timeAxis,
      ((key (timeAxisPoint a q) ?_).2 ▸ (key (timeAxisPoint a q) ?_).1)⟩, key⟩
    · obtain ⟨n, hn⟩ := x.2
      have h₁ : (n timeAxis : ℝ) * a = ((q : ℝ) + 1 / 2) * a := (hn timeAxis).symm.trans hx
      have h₂ : (n timeAxis : ℝ) = (q : ℝ) + 1 / 2 := mul_right_cancel₀ ha h₁
      have h₃ : ((2 * n timeAxis : ℤ) : ℝ) = ((2 * q + 1 : ℤ) : ℝ) := by
        push_cast
        linarith
      have h₄ : 2 * n timeAxis = 2 * q + 1 := by exact_mod_cast h₃
      omega
    · rw [timeAxisPoint_apply_timeAxis]
      ring
    · rw [timeAxisPoint_apply_timeAxis]
      ring
theorem isBoundedObservable_actOn (r : LatticeSymmetry a) {B : GaugeField a → ℂ}
    (hB : IsBoundedObservable B) : IsBoundedObservable (r.actOn B) := by apply _root_.YangMills.Construction.InfiniteLattice.LiftedGibbsStates.isBoundedObservable_actOn <;> assumption
theorem isBoundedObservable_timeConj (t : halfSpacingTimes a) {B : GaugeField a → ℂ}
    (hB : IsBoundedObservable B) : IsBoundedObservable (timeConj t B) := by
  obtain ⟨hm, C, hC⟩ := isBoundedObservable_actOn (timeReflect t) hB
  refine ⟨Complex.continuous_conj.measurable.comp hm, C, fun U => ?_⟩
  rw [timeConj, RCLike.norm_conj]
  exact hC U
theorem linkMap_linkMap_timeReflect (t : halfSpacingTimes a) (b : Link a) :
    (timeReflect t).linkMap ((timeReflect t).linkMap b) = b := by
  have h : ∀ x : LatticePoint a, (timeReflect t).pointMap ((timeReflect t).pointMap x) = x :=
    fun x => by
      refine Subtype.ext ?_
      change (timeReflect t).toFun ((timeReflect t).toFun (x : AmbientSpace)) = x
      rw [timeReflect_toFun_eq, reflectTime_reflectTime]
  exact Link.ext (h _) (h _)
theorem pullbackField_timeReflect_twice (t : halfSpacingTimes a) (U : GaugeField a) :
    (timeReflect t).pullbackField ((timeReflect t).pullbackField U) = U := by
  refine Subtype.ext (funext fun b => ?_)
  change U ((timeReflect t).linkMap ((timeReflect t).linkMap b)) = U b
  rw [linkMap_linkMap_timeReflect]
theorem timeConjProperties (t : halfSpacingTimes a) : TimeConjProperties t := by
  refine ⟨fun B hB => isBoundedObservable_timeConj t hB, fun c c' B B' _ _ => ?_,
    fun B B' _ _ => ?_, fun B _ => ?_⟩
  · funext U
    simp [timeConj, LatticeSymmetry.actOn]
  · funext U
    simp [timeConj, LatticeSymmetry.actOn]
  · funext U
    simp [timeConj, LatticeSymmetry.actOn, pullbackField_timeReflect_twice]
end CutoffSymmetries
theorem cutoffSymmetriesAndTimeReflections_holds : CutoffSymmetriesAndTimeReflections := by
  intro s
  have ha : s.spacing ≠ 0 := by
    refine zpow_ne_zero _ ?_
    have h := s.isAdmissible.2
    exact_mod_cast (by omega : s.L ≠ 0)
  exact ⟨fun r r' => CutoffSymmetries.actionProperties ha r r',
    CutoffSymmetries.timeReflectionLevelSets ha,
    CutoffSymmetries.timeConjProperties⟩
end YangMills.Construction.InfiniteLattice
