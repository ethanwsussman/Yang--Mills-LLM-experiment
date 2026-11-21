import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopies
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace ReflectionGroupAndTransport
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def axisTranslation (t : ℤ) : Equiv.Perm ℝ := Equiv.addRight (2 * t * g.cellSide)
theorem axisTranslation_apply (t : ℤ) (y : ℝ) :
    axisTranslation g t y = y + 2 * t * g.cellSide := rfl
theorem axisReflectionPerm_apply (μ : Fin 4) (k : ℤ) (y : ℝ) :
    g.axisReflectionPerm μ k y = 2 * (g.origin μ + k * g.cellSide) - y := rfl
theorem axisTranslation_zero : axisTranslation g 0 = 1 := by
  ext y
  simp [axisTranslation_apply]
theorem axisReflectionPerm_mul_axisReflectionPerm (μ : Fin 4) (k k' : ℤ) :
    g.axisReflectionPerm μ k * g.axisReflectionPerm μ k' =
      axisTranslation g (k - k') := by
  ext y
  simp only [Equiv.Perm.coe_mul, Function.comp, axisReflectionPerm_apply,
    axisTranslation_apply]
  push_cast
  ring
theorem axisReflectionPerm_mul_axisTranslation (μ : Fin 4) (k t : ℤ) :
    g.axisReflectionPerm μ k * axisTranslation g t =
      g.axisReflectionPerm μ (k - t) := by
  ext y
  simp only [Equiv.Perm.coe_mul, Function.comp, axisReflectionPerm_apply,
    axisTranslation_apply]
  push_cast
  ring
theorem axisTranslation_mul_axisReflectionPerm (μ : Fin 4) (k t : ℤ) :
    axisTranslation g t * g.axisReflectionPerm μ k =
      g.axisReflectionPerm μ (k + t) := by
  ext y
  simp only [Equiv.Perm.coe_mul, Function.comp, axisReflectionPerm_apply,
    axisTranslation_apply]
  push_cast
  ring
theorem axisTranslation_mul_axisTranslation (t t' : ℤ) :
    axisTranslation g t * axisTranslation g t' = axisTranslation g (t + t') := by
  ext y
  simp only [Equiv.Perm.coe_mul, Function.comp, axisTranslation_apply]
  push_cast
  ring
theorem mem_axisGroup_iff (μ : Fin 4) (f : Equiv.Perm ℝ) :
    f ∈ g.axisGroup μ ↔
      (∃ k : ℤ, f = g.axisReflectionPerm μ k) ∨ ∃ t : ℤ, f = axisTranslation g t := by
  constructor
  · intro hf
    refine Subgroup.closure_induction
      (p := fun f _ => (∃ k : ℤ, f = g.axisReflectionPerm μ k) ∨
        ∃ t : ℤ, f = axisTranslation g t) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨k, rfl⟩
      exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨0, (axisTranslation_zero g).symm⟩
    · rintro x y _ _ (⟨k, rfl⟩ | ⟨t, rfl⟩) (⟨k', rfl⟩ | ⟨t', rfl⟩)
      · exact Or.inr ⟨_, axisReflectionPerm_mul_axisReflectionPerm g μ k k'⟩
      · exact Or.inl ⟨_, axisReflectionPerm_mul_axisTranslation g μ k t'⟩
      · exact Or.inl ⟨_, axisTranslation_mul_axisReflectionPerm g μ k' t⟩
      · exact Or.inr ⟨_, axisTranslation_mul_axisTranslation g t t'⟩
    · rintro x _ (⟨k, rfl⟩ | ⟨t, rfl⟩)
      · refine Or.inl ⟨k, inv_eq_of_mul_eq_one_right ?_⟩
        rw [axisReflectionPerm_mul_axisReflectionPerm, sub_self, axisTranslation_zero]
      · refine Or.inr ⟨-t, inv_eq_of_mul_eq_one_right ?_⟩
        rw [axisTranslation_mul_axisTranslation, add_neg_cancel, axisTranslation_zero]
  · rintro (⟨k, rfl⟩ | ⟨t, rfl⟩)
    · exact Subgroup.subset_closure ⟨k, rfl⟩
    · have e : axisTranslation g t =
          g.axisReflectionPerm μ t * g.axisReflectionPerm μ 0 := by
        rw [axisReflectionPerm_mul_axisReflectionPerm, sub_zero]
      rw [e]
      exact mul_mem (Subgroup.subset_closure ⟨t, rfl⟩) (Subgroup.subset_closure ⟨0, rfl⟩)
theorem axisReflectionPerm_mem (μ : Fin 4) (k : ℤ) : g.axisReflectionPerm μ k ∈ g.axisGroup μ :=
  (mem_axisGroup_iff g μ _).mpr (Or.inl ⟨k, rfl⟩)
theorem axisTranslation_mem (μ : Fin 4) (t : ℤ) : axisTranslation g t ∈ g.axisGroup μ :=
  (mem_axisGroup_iff g μ _).mpr (Or.inr ⟨t, rfl⟩)
def zmodZeroToInt (i : ZMod 0) : ℤ := i
def dihedralToAxisGroup (μ : Fin 4) : DihedralGroup 0 → g.axisGroup μ
  | .r t => ⟨axisTranslation g (zmodZeroToInt t), axisTranslation_mem g μ _⟩
  | .sr k => ⟨g.axisReflectionPerm μ (-zmodZeroToInt k), axisReflectionPerm_mem g μ _⟩
theorem dihedralToAxisGroup_mul (μ : Fin 4) (a b : DihedralGroup 0) :
    dihedralToAxisGroup g μ (a * b) = dihedralToAxisGroup g μ a * dihedralToAxisGroup g μ b := by
  rcases a with i | i <;> rcases b with j | j
  · rw [DihedralGroup.r_mul_r]
    exact Subtype.ext (axisTranslation_mul_axisTranslation g (zmodZeroToInt i) (zmodZeroToInt j)).symm
  · rw [DihedralGroup.r_mul_sr]
    refine Subtype.ext ?_
    refine Eq.trans ?_
      (axisTranslation_mul_axisReflectionPerm g μ (-zmodZeroToInt j) (zmodZeroToInt i)).symm
    have e : -zmodZeroToInt (j - i) = -zmodZeroToInt j + zmodZeroToInt i := by
      change -(zmodZeroToInt j - zmodZeroToInt i) = _
      ring
    change g.axisReflectionPerm μ (-zmodZeroToInt (j - i)) = _
    rw [e]
  · rw [DihedralGroup.sr_mul_r]
    refine Subtype.ext ?_
    refine Eq.trans ?_
      (axisReflectionPerm_mul_axisTranslation g μ (-zmodZeroToInt i) (zmodZeroToInt j)).symm
    have e : -zmodZeroToInt (i + j) = -zmodZeroToInt i - zmodZeroToInt j := by
      change -(zmodZeroToInt i + zmodZeroToInt j) = _
      ring
    change g.axisReflectionPerm μ (-zmodZeroToInt (i + j)) = _
    rw [e]
  · rw [DihedralGroup.sr_mul_sr]
    refine Subtype.ext ?_
    refine Eq.trans ?_
      (axisReflectionPerm_mul_axisReflectionPerm g μ (-zmodZeroToInt i) (-zmodZeroToInt j)).symm
    have e : zmodZeroToInt (j - i) = -zmodZeroToInt i - -zmodZeroToInt j := by
      change zmodZeroToInt j - zmodZeroToInt i = _
      ring
    change axisTranslation g (zmodZeroToInt (j - i)) = _
    rw [e]
theorem dihedralToAxisGroup_injective (μ : Fin 4) :
    Function.Injective (dihedralToAxisGroup g μ) := by
  have hs : g.cellSide ≠ 0 := g.cellSide_pos.ne'
  have cancel : ∀ m n : ℤ, (2 * (m : ℝ) * g.cellSide = 2 * n * g.cellSide) → m = n := by
    intro m n h
    have h2 : (m : ℝ) = n := by
      have := mul_right_cancel₀ hs h
      linarith
    exact_mod_cast h2
  intro a b h
  have val : ∀ y : ℝ, (dihedralToAxisGroup g μ a).1 y = (dihedralToAxisGroup g μ b).1 y :=
    fun y => by rw [h]
  rcases a with i | i <;> rcases b with j | j
  · have h0 := val 0
    simp only [dihedralToAxisGroup, axisTranslation_apply, zero_add] at h0
    have : zmodZeroToInt i = zmodZeroToInt j := cancel _ _ h0
    exact congrArg DihedralGroup.r this
  · have h0 := val 0
    have h1 := val 1
    simp only [dihedralToAxisGroup, axisTranslation_apply, axisReflectionPerm_apply] at h0 h1
    exfalso
    linarith
  · have h0 := val 0
    have h1 := val 1
    simp only [dihedralToAxisGroup, axisTranslation_apply, axisReflectionPerm_apply] at h0 h1
    exfalso
    linarith
  · have h0 := val 0
    simp only [dihedralToAxisGroup, axisReflectionPerm_apply, sub_zero] at h0
    have h2 : 2 * ((zmodZeroToInt i : ℝ)) * g.cellSide = 2 * (zmodZeroToInt j) * g.cellSide := by
      push_cast at h0
      linarith
    have : zmodZeroToInt i = zmodZeroToInt j := cancel _ _ h2
    exact congrArg DihedralGroup.sr this
theorem dihedralToAxisGroup_surjective (μ : Fin 4) :
    Function.Surjective (dihedralToAxisGroup g μ) := by
  rintro ⟨f, hf⟩
  rcases (mem_axisGroup_iff g μ f).mp hf with ⟨k, rfl⟩ | ⟨t, rfl⟩
  · refine ⟨DihedralGroup.sr (-k : ℤ), Subtype.ext ?_⟩
    change g.axisReflectionPerm μ (-(-k)) = _
    rw [neg_neg]
  · exact ⟨DihedralGroup.r (t : ℤ), rfl⟩
theorem nonempty_axisGroup_mulEquiv_dihedral (μ : Fin 4) :
    Nonempty (g.axisGroup μ ≃* DihedralGroup 0) :=
  ⟨(MulEquiv.ofBijective (MonoidHom.mk' (dihedralToAxisGroup g μ) (dihedralToAxisGroup_mul g μ))
    ⟨dihedralToAxisGroup_injective g μ, dihedralToAxisGroup_surjective g μ⟩).symm⟩
variable {g}
theorem actsOnCoord_or_reflectsCoord_of_mem {r : AmbientSpace → AmbientSpace} {μ : Fin 4}
    {f : Equiv.Perm ℝ} (hf : f ∈ g.axisGroup μ) (h : ∀ x, r x μ = f (x μ)) :
    (∃ t : ℤ, g.ActsOnCoord r μ (g.coordShift t)) ∨ g.ReflectsCoord r μ := by
  rcases (mem_axisGroup_iff g μ f).mp hf with ⟨k, rfl⟩ | ⟨t, rfl⟩
  · refine Or.inr ⟨k, fun x => ?_⟩
    rw [h, axisReflectionPerm_apply]
    simp only [ReflectionGrid.coordReflect]
    ring
  · refine Or.inl ⟨t, fun x => ?_⟩
    rw [h, axisTranslation_apply]
    simp only [ReflectionGrid.coordShift]
    ring
variable (g)
def piAxisPerm (f : ∀ μ, g.axisGroup μ) : Equiv.Perm AmbientSpace :=
  Equiv.piCongrRight fun μ => (f μ).1
variable {g}
theorem piAxisPerm_mem (hG : g.ReflectionGroupCoordForm) (f : ∀ μ, g.axisGroup μ) :
    piAxisPerm g f ∈ g.reflectionGroup := by
  obtain ⟨s, hs, e⟩ := hG.2.1 (piAxisPerm g f) fun μ =>
    actsOnCoord_or_reflectsCoord_of_mem (f μ).2 fun _ => rfl
  rwa [← Equiv.coe_fn_injective e]
theorem exists_axisGroup_factor (hG : g.ReflectionGroupCoordForm) {r : Equiv.Perm AmbientSpace}
    (hr : r ∈ g.reflectionGroup) (μ : Fin 4) : ∃ f : g.axisGroup μ, ∀ x, r x μ = f.1 (x μ) := by
  rcases hG.1 r hr μ with ⟨t, ht⟩ | ⟨k, hk⟩
  · refine ⟨⟨axisTranslation g t, axisTranslation_mem g μ t⟩, fun x => ?_⟩
    have := ht x
    simp only [ReflectionGrid.coordShift] at this
    rw [axisTranslation_apply]
    linarith
  · refine ⟨⟨g.axisReflectionPerm μ k, axisReflectionPerm_mem g μ k⟩, fun x => ?_⟩
    have := hk x
    simp only [ReflectionGrid.coordReflect] at this
    rw [axisReflectionPerm_apply]
    linarith
theorem exists_pi_axisGroup_mulEquiv (hG : g.ReflectionGroupCoordForm) :
    ∃ φ : (∀ μ, g.axisGroup μ) ≃* g.reflectionGroup,
      ∀ (f : ∀ μ, g.axisGroup μ) (x : AmbientSpace) (μ : Fin 4), (φ f).1 x μ = (f μ).1 (x μ) := by
  let ψ : (∀ μ, g.axisGroup μ) →* g.reflectionGroup :=
    MonoidHom.mk' (fun f => ⟨piAxisPerm g f, piAxisPerm_mem hG f⟩) fun f f' =>
      Subtype.ext (Equiv.ext fun x => funext fun μ => rfl)
  have hinj : Function.Injective ψ := by
    intro f f' h
    funext μ
    refine Subtype.ext (Equiv.ext fun y => ?_)
    exact congrArg (fun e : g.reflectionGroup => e.1 (fun _ => y) μ) h
  have hsurj : Function.Surjective ψ := by
    rintro ⟨r, hr⟩
    choose f hf using exists_axisGroup_factor hG hr
    exact ⟨f, Subtype.ext (Equiv.ext fun x => funext fun μ => (hf μ x).symm)⟩
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩, fun _ _ _ => rfl⟩
variable (g)
theorem reflect_apply_self (μ : Fin 4) (k : ℤ) (x : AmbientSpace) :
    g.reflect μ k x μ = 2 * (g.origin μ + k * g.cellSide) - x μ := by
  simp [ReflectionGrid.reflect, coordVec]
  ring
theorem reflect_apply_of_ne {μ ν : Fin 4} (h : ν ≠ μ) (k : ℤ) (x : AmbientSpace) :
    g.reflect μ k x ν = x ν := by
  simp [ReflectionGrid.reflect, coordVec, Pi.single_eq_of_ne h]
theorem numReflectedCoords_reflect (μ : Fin 4) (k : ℤ) :
    g.numReflectedCoords (g.reflect μ k) = 1 := by
  classical
  refine Finset.card_eq_one.mpr ⟨μ, ?_⟩
  ext ν
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨k', hk'⟩
    by_contra hne
    have h0 := hk' fun _ => g.origin ν
    have h1 := hk' fun _ => g.origin ν + 1
    simp only [reflect_apply_of_ne g hne, ReflectionGrid.coordReflect] at h0 h1
    linarith
  · rintro rfl
    refine ⟨k, fun x => ?_⟩
    rw [reflect_apply_self]
    simp only [ReflectionGrid.coordReflect]
    ring
variable {g}
theorem orientationSign_reflect (hG : g.ReflectionGroupCoordForm) (μ : Fin 4) (k : ℤ) :
    orientationSign (g.reflect μ k) = -1 := by
  have h : orientationSign (g.reflect μ k) = (-1) ^ g.numReflectedCoords (g.reflect μ k) :=
    hG.2.2.1 (g.reflectPerm μ k) (g.reflectElem μ k).2
  rw [h, numReflectedCoords_reflect, pow_one]
theorem orientationSignIsHom (hG : g.ReflectionGroupCoordForm) : g.OrientationSignIsHom :=
  ⟨⟨MonoidHom.mk' (fun r : g.reflectionGroup => orientationSign r.1) fun a b =>
      hG.2.2.2.1 a.1 a.2 b.1 b.2,
    fun _ => rfl⟩, orientationSign_reflect hG, hG.2.2.2.2.2.2.2⟩
theorem mover_eq (hG : g.ReflectionGroupCoordForm) {S S' : Set AmbientSpace}
    (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet) (r : g.reflectionGroup)
    (h : (r.1 : AmbientSpace → AmbientSpace) '' S = S') :
    g.mover S S' = r := by
  have hc : ((g.mover S S').1 : AmbientSpace → AmbientSpace) '' S = S' :=
    Classical.epsilon_spec
      (p := fun r : g.reflectionGroup => (r.1 : AmbientSpace → AmbientSpace) '' S = S') ⟨r, h⟩
  exact (hG.2.2.2.2.2.2.1 S hS S' hS').unique hc h
theorem pullbackField_toLatticeSym_mul (h r : g.reflectionGroup) (U : D.GaugeField) :
    (g.toLatticeSym (h * r)).pullbackField U =
      (g.toLatticeSym r).pullbackField ((g.toLatticeSym h).pullbackField U) := by
  apply Subtype.ext
  funext b
  change U.1 ((g.toLatticeSym (h * r)).linkMap b) =
    U.1 ((g.toLatticeSym h).linkMap ((g.toLatticeSym r).linkMap b))
  congr 1
theorem conj_signedConj (σ : ℤˣ) (z : ℂ) :
    starRingEnd ℂ (Conventions.signedConj σ z) = Conventions.signedConj (-σ) z := by
  rcases Int.units_eq_one_or σ with rfl | rfl <;> simp [Conventions.signedConj]
theorem conj_actOn_transportTo (hG : g.ReflectionGroupCoordForm) {S S' : Set AmbientSpace}
    (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet) (F : D.GaugeField → ℂ) (θ : g.reflectionGroup)
    (hθ : orientationSign θ.1 = -1) :
    (fun U => starRingEnd ℂ ((g.toLatticeSym θ).actOn (g.transportTo S S' F) U)) =
      g.transportTo S ((θ.1 : AmbientSpace → AmbientSpace) '' S') F := by
  obtain ⟨r, hr, -⟩ := hG.2.2.2.2.2.2.1 S hS S' hS'
  have hrc : g.mover S S' = r := mover_eq hG hS hS' r hr
  have hθS' : (θ.1 : AmbientSpace → AmbientSpace) '' S' ∈ g.cellSet :=
    hG.2.2.2.2.2.1 _ θ.2 S' hS'
  have hc : g.mover S ((θ.1 : AmbientSpace → AmbientSpace) '' S') = θ * r := by
    refine mover_eq hG hS hθS' _ ?_
    rw [← hr, ← image_comp]
    rfl
  have hsg : orientationSign (θ * r).1 = -orientationSign r.1 := by
    have h := hG.2.2.2.1 θ.1 θ.2 r.1 r.2
    rw [hθ, neg_one_mul] at h
    exact h
  funext U
  simp only [ReflectionGrid.transportTo, hrc, hc, ReflectionGrid.transport]
  change starRingEnd ℂ (Conventions.signedConj (orientationSign r.1)
      (F ((g.toLatticeSym r).pullbackField ((g.toLatticeSym θ).pullbackField U)))) =
    Conventions.signedConj (orientationSign (θ * r).1)
      (F ((g.toLatticeSym (θ * r)).pullbackField U))
  rw [pullbackField_toLatticeSym_mul, hsg, conj_signedConj]
theorem transportLaws (hG : g.ReflectionGroupCoordForm) (hC : g.TransportRules) :
    g.TransportLaws := by
  have hbase : g.baseCell ∈ g.cellSet := ⟨0, rfl⟩
  have rules : ∀ S ∈ g.cellSet, ∀ S' ∈ g.cellSet, ∀ S'' ∈ g.cellSet,
      ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
      ∀ F' ∈ ReflectionGrid.cellObservables (D := D) S,
      g.transportTo S S' F ∈ ReflectionGrid.cellObservables (D := D) S' ∧
      g.transportTo S S F = F ∧
      g.transportTo S' S'' (g.transportTo S S' F) = g.transportTo S S'' F ∧
      g.transportTo S S' (fun U => starRingEnd ℂ (F U)) =
        (fun U => starRingEnd ℂ (g.transportTo S S' F U)) ∧
      g.transportTo S S' (F * F') = g.transportTo S S' F * g.transportTo S S' F' ∧
      g.transportTo S S' (F + F') = g.transportTo S S' F + g.transportTo S S' F' ∧
      g.transportTo S S' 1 = 1 := by
    intro S hS S' hS' S'' hS'' F hF F' hF'
    obtain ⟨r, hr, -⟩ := hG.2.2.2.2.2.2.1 S hS S' hS'
    obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := hC S hS S' hS' S'' hS'' r hr F hF F' hF' 1
    exact ⟨h1, h2, h3, h4, h5, h6, h8⟩
  refine ⟨fun S hS S' hS' S'' hS'' F hF F' hF' => ?_, fun S hS F hF => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := rules S hS S' hS' S'' hS'' F hF F' hF'
    exact ⟨h1, h2, h3, h5, h6, h4, h7, fun μ k =>
      conj_actOn_transportTo hG hS hS' F (g.reflectElem μ k) (orientationSign_reflect hG μ k)⟩
  · obtain ⟨h1, -, h3, -⟩ := rules S hS g.baseCell hbase S hS F hF F hF
    obtain ⟨-, h2', -⟩ := rules S hS S hS S hS F hF F hF
    refine ⟨⟨h1, h3.trans h2'⟩, fun F' hF' e => ?_⟩
    obtain ⟨-, h2'', h3'', -⟩ := rules g.baseCell hbase S hS g.baseCell hbase F' hF' F' hF'
    rw [← e, h3'', h2'']
variable (g)
theorem closure_range_reflectElem :
    Subgroup.closure (range fun p : Fin 4 × ℤ => g.reflectElem p.1 p.2) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage
    (k := range fun p : Fin 4 × ℤ => g.reflectPerm p.1 p.2)
  have e : (range fun p : Fin 4 × ℤ => g.reflectElem p.1 p.2) =
      ((↑) : g.reflectionGroup → Equiv.Perm AmbientSpace) ⁻¹'
        (range fun p : Fin 4 × ℤ => g.reflectPerm p.1 p.2) := by
    ext x
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p, congrArg Subtype.val hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨p, Subtype.ext hp⟩
  rw [e]
  exact h
variable {g}
theorem inducedTorusMapsFormQuotient (h : g.TorusGroupQuotient) :
    g.InducedTorusMapsFormQuotient := by
  obtain ⟨⟨φ, h1, h2, h3⟩, -⟩ := h
  refine ⟨φ, h1, h2, h3, ?_⟩
  have e : (range fun p : Fin 4 × ℤ => φ (g.reflectElem p.1 p.2)) =
      φ '' range fun p : Fin 4 × ℤ => g.reflectElem p.1 p.2 := by
    rw [← range_comp]
    rfl
  rw [e, ← MonoidHom.map_closure, closure_range_reflectElem, MonoidHom.range_eq_map]
end ReflectionGroupAndTransport
open ReflectionGroupAndTransport in
theorem ReflectionGroupAndTransport.proof (h : GridBasicProperties.Statement) :
    ReflectionGroupAndTransport.Statement := by
  intro D g hg
  obtain ⟨-, -, -, hG, hC, -, hT⟩ := h D g
  refine ⟨⟨fun μ => ⟨fun f => ?_, nonempty_axisGroup_mulEquiv_dihedral g μ⟩,
      exists_pi_axisGroup_mulEquiv hG,
      fun r hr => (g.reflectionGroup_le_latticeSymGroup hr).2⟩,
    hG.2.2.2.2.2.2.1, orientationSignIsHom hG, transportLaws hG hC,
    fun hℓ => ⟨(hT hℓ).1, inducedTorusMapsFormQuotient (hT hℓ).2.1, (hT hℓ).2.1⟩,
    fun b k => ⟨hg.coarsen b k, g.cellSide_coarsen b k, rfl⟩⟩
  rw [mem_axisGroup_iff]
  constructor
  · rintro (⟨k, rfl⟩ | ⟨t, rfl⟩)
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨t, fun _ => rfl⟩
  · rintro (⟨k, hk⟩ | ⟨t, ht⟩)
    · exact Or.inl ⟨k, Equiv.coe_fn_injective hk⟩
    · exact Or.inr ⟨t, Equiv.ext ht⟩
end YangMills.Construction.ChessboardTori
end
