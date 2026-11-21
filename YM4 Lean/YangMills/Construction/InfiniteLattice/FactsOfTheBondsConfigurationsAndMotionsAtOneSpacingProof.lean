import YangMills.Construction.InfiniteLattice.BondsPlaquettesCircuitsAndConfigurationsOfTheLatticeOfACutoffProof
import YangMills.Construction.InfiniteLattice.FactsOfOneLatticeAtOneSpacingProof
import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.OneSpacing
open YangMills.Construction.InfiniteLattice
open YangMills.Construction.Matrices
section Transversal
variable {X β ι : Type} [TopologicalSpace X]
def extendOnOrientations (opp : β → β) (φ : ι → β) (g : ι → ComplexMatrix2.specialUnitary)
    (b : β) : ComplexMatrix2.specialUnitary :=
  open Classical in
  if h : ∃ i, φ i = b then g h.choose
  else if h' : ∃ i, φ i = opp b then (g h'.choose)⁻¹ else 1
theorem extendOnOrientations_apply {opp : β → β} {φ : ι → β} (hφ : Function.Injective φ)
    (g : ι → ComplexMatrix2.specialUnitary) (i : ι) : extendOnOrientations opp φ g (φ i) = g i := by
  have h : ∃ i', φ i' = φ i := ⟨i, rfl⟩
  rw [extendOnOrientations, dif_pos h, hφ h.choose_spec]
theorem extendOnOrientations_apply_opposite {opp : β → β} {φ : ι → β} (hφ : Function.Injective φ)
    (hopp : ∀ b, opp (opp b) = b) (hxor : ∀ b, Xor (b ∈ range φ) (opp b ∈ range φ))
    (g : ι → ComplexMatrix2.specialUnitary) (i : ι) :
    extendOnOrientations opp φ g (opp (φ i)) = (g i)⁻¹ := by
  have hn : ¬ ∃ i', φ i' = opp (φ i) := by
    rcases hxor (φ i) with h | h
    · exact h.2
    · exact absurd ⟨i, rfl⟩ h.2
  have h : ∃ i', φ i' = opp (opp (φ i)) := ⟨i, (hopp _).symm⟩
  rw [extendOnOrientations, dif_neg hn, dif_pos h]
  have : h.choose = i := hφ (h.choose_spec.trans (hopp _))
  rw [this]
theorem extendOnOrientations_opposite {opp : β → β} {φ : ι → β} (hφ : Function.Injective φ)
    (hopp : ∀ b, opp (opp b) = b) (hxor : ∀ b, Xor (b ∈ range φ) (opp b ∈ range φ))
    (g : ι → ComplexMatrix2.specialUnitary) (b : β) :
    extendOnOrientations opp φ g (opp b) = (extendOnOrientations opp φ g b)⁻¹ := by
  rcases hxor b with h | h
  · obtain ⟨i, rfl⟩ := h.1
    rw [extendOnOrientations_apply_opposite hφ hopp hxor, extendOnOrientations_apply hφ]
  · obtain ⟨i, hi⟩ := h.1
    have hb : b = opp (φ i) := by rw [hi, hopp]
    rw [hb, hopp, extendOnOrientations_apply_opposite hφ hopp hxor, extendOnOrientations_apply hφ,
      inv_inv]
theorem continuous_extendOnOrientations (opp : β → β) (φ : ι → β) :
    Continuous (extendOnOrientations opp φ) := by
  refine continuous_pi fun b => ?_
  unfold extendOnOrientations
  split_ifs with h h'
  · exact continuous_apply _
  · exact (continuous_apply _).inv
  · exact continuous_const
theorem isHomeomorph_restrictToTransversal (val : X → β → ComplexMatrix2.specialUnitary)
    (opp : β → β) (φ : ι → β)
    (hind : IsInducing val) (hinj : Function.Injective val)
    (hrange : ∀ f : β → ComplexMatrix2.specialUnitary, (∀ b, f (opp b) = (f b)⁻¹) →
      ∃ U, val U = f)
    (hval : ∀ U b, val U (opp b) = (val U b)⁻¹) (hopp : ∀ b, opp (opp b) = b)
    (hφ : Function.Injective φ) (hxor : ∀ b, Xor (b ∈ range φ) (opp b ∈ range φ)) :
    IsHomeomorph fun U i => val U (φ i) := by
  have hc : Continuous fun (U : X) (i : ι) => val U (φ i) :=
    continuous_pi fun i => (continuous_apply _).comp hind.continuous
  have hcomp : extendOnOrientations opp φ ∘ (fun (U : X) (i : ι) => val U (φ i)) = val := by
    funext U b
    rcases hxor b with h | h
    · obtain ⟨i, rfl⟩ := h.1
      exact extendOnOrientations_apply hφ _ i
    · obtain ⟨i, hi⟩ := h.1
      have hb : b = opp (φ i) := by rw [hi, hopp]
      rw [hb, Function.comp_apply, extendOnOrientations_apply_opposite hφ hopp hxor, hval]
  have hi : IsInducing fun (U : X) (i : ι) => val U (φ i) :=
    IsInducing.of_comp hc (continuous_extendOnOrientations opp φ) (by rw [hcomp]; exact hind)
  refine isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨hi, fun U U' h => hinj ?_⟩, fun g => ?_⟩
  · have h' := congrArg (extendOnOrientations opp φ) h
    have e := congrFun hcomp
    simp only [Function.comp_apply] at e
    rw [e, e] at h'
    exact h'
  · obtain ⟨U, hU⟩ := hrange _ (extendOnOrientations_opposite hφ hopp hxor g)
    exact ⟨U, funext fun i => by
      change val U (φ i) = g i
      rw [hU]
      exact extendOnOrientations_apply hφ g i⟩
theorem isHomeomorph_restrictToTransversal_prod (val : X → β → ComplexMatrix2.specialUnitary)
    (opp : β → β) (P S : Set β)
    (hind : IsInducing val) (hinj : Function.Injective val)
    (hrange : ∀ f : β → ComplexMatrix2.specialUnitary, (∀ b, f (opp b) = (f b)⁻¹) →
      ∃ U, val U = f)
    (hval : ∀ U b, val U (opp b) = (val U b)⁻¹) (hopp : ∀ b, opp (opp b) = b)
    (hS : S ⊆ P) (hxor : ∀ b, Xor (b ∈ P) (opp b ∈ P)) :
    IsHomeomorph fun U =>
      ((fun b : S => val U b : LinkVariables S),
        (fun b : ↥(P \ S) => val U b : LinkVariables ↥(P \ S))) := by
  have hφ : Function.Injective (Sum.elim (Subtype.val : S → β) (Subtype.val : ↥(P \ S) → β)) := by
    rintro (⟨b, hb⟩ | ⟨b, hb⟩) (⟨b', hb'⟩ | ⟨b', hb'⟩) h
    · simp only [Sum.elim_inl] at h
      subst h
      rfl
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      subst h
      exact absurd hb hb'.2
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      subst h
      exact absurd hb' hb.2
    · simp only [Sum.elim_inr] at h
      subst h
      rfl
  have hr : range (Sum.elim (Subtype.val : S → β) (Subtype.val : ↥(P \ S) → β)) = P := by
    rw [Set.Sum.elim_range, Subtype.range_coe, Subtype.range_coe, union_sdiff_cancel hS]
  have h := isHomeomorph_restrictToTransversal val opp _ hind hinj hrange hval hopp hφ
    (by rw [hr]; exact hxor)
  exact (Homeomorph.sumArrowHomeomorphProdArrow (X := ComplexMatrix2.specialUnitary)).isHomeomorph.comp h
end Transversal
section Borel
instance instSecondCountableSpecialUnitary : SecondCountableTopology ComplexMatrix2.specialUnitary := by
  have : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology
    (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)
theorem linkVariablesBorelEqPi_of_countable (ι : Type) [Countable ι] : LinkVariablesBorelEqPi ι := by
  have h : @MeasurableSpace.pi ι (fun _ => ComplexMatrix2.specialUnitary)
      (fun _ => borel ComplexMatrix2.specialUnitary) = borel (LinkVariables ι) :=
    (inferInstance : BorelSpace (LinkVariables ι)).measurable_eq
  exact ⟨h.symm, h.symm⟩
theorem borel_eq_iSup_comap_of_isInducing {X ι : Type} [TopologicalSpace X] [Countable ι]
    (R : X → ι → ComplexMatrix2.specialUnitary) (hR : IsInducing R) :
    borel X = ⨆ i, MeasurableSpace.comap (fun U => R U i) (borel ComplexMatrix2.specialUnitary) := by
  have h1 : borel X = MeasurableSpace.comap R (borel (LinkVariables ι)) := by
    conv_lhs => rw [hR.eq_induced]
    exact borel_comap
  rw [h1, (linkVariablesBorelEqPi_of_countable ι).2, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp]
  rfl
end Borel
section Space
variable {a : ℝ}
theorem isInducing_gaugeField_val :
    IsInducing (Subtype.val : GaugeField a → Link a → ComplexMatrix2.specialUnitary) :=
  IsInducing.subtypeVal
theorem countable_link (a : ℝ) : Countable (Link a) := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.countable_link <;> assumption
theorem exists_gaugeField_val_eq (f : Link a → ComplexMatrix2.specialUnitary)
    (hf : ∀ b, f b.opposite = (f b)⁻¹) : ∃ U : GaugeField a, U.1 = f :=
  ⟨⟨f, hf⟩, rfl⟩
theorem isHomeomorph_restrictField_positiveLinks (ha : 0 < a) :
    IsHomeomorph fun U : GaugeField a => restrictField U (positiveLinkSet a) := by apply _root_.YangMills.Construction.FixedSpacing.BasicFactsProof.isHomeomorph_restrictField <;> assumption
theorem fieldsAsProduct_of_pos (ha : 0 < a) : FieldsAsProduct a := by
  have := countable_link a
  refine ⟨Set.to_countable _, fun b => ?_, isHomeomorph_restrictField_positiveLinks ha⟩
  rcases xor_mem_positiveLinks ha b with h | h
  · exact Or.inl ⟨h.1, fun ⟨b', hb', e⟩ => h.2 (by rw [e]; exact hb')⟩
  · exact Or.inr ⟨⟨b.opposite, h.1, rfl⟩, h.2⟩
theorem fieldBorelGenerated_of_pos (ha : 0 < a) : FieldBorelGenerated a := by
  have := countable_link a
  refine ⟨fun S _ => linkVariablesBorelEqPi_of_countable S, ?_⟩
  have h := borel_eq_iSup_comap_of_isInducing _
    (isHomeomorph_restrictField_positiveLinks ha).isEmbedding.isInducing
  rw [h, linkSigma, iSup_subtype']
  rfl
theorem fieldSplitting_of_pos (ha : 0 < a) : FieldSplitting ha := by
  intro S hS
  have hH : IsHomeomorph fun U : GaugeField a =>
      (restrictField U S, restrictField U (positiveLinkSet a \ S)) :=
    isHomeomorph_restrictToTransversal_prod
      (Subtype.val : GaugeField a → Link a → ComplexMatrix2.specialUnitary) Link.opposite _ S
      isInducing_gaugeField_val Subtype.val_injective exists_gaugeField_val_eq (fun U b => U.2 b)
      (fun _ => rfl) hS (xor_mem_positiveLinks ha)
  have h₁ : ∀ (V : LinkVariables S) (ω : GaugeField a),
      restrictField (gluedField ha hS V ω) S = V := fun V ω =>
    funext fun b => gluedField_apply_of_mem ha hS V ω b
  have h₂ : ∀ (V : LinkVariables S) (ω : GaugeField a),
      restrictField (gluedField ha hS V ω) (positiveLinkSet a \ S) =
        restrictField ω (positiveLinkSet a \ S) := fun V ω =>
    funext fun b => gluedField_apply_of_notMem ha hS V ω b.2
  refine ⟨hH, fun V ω => by rw [h₁, h₂], ?_, fun V U U' h => ?_, h₁⟩
  · rw [hH.isEmbedding.isInducing.continuous_iff]
    have : (fun U : GaugeField a =>
        (restrictField U S, restrictField U (positiveLinkSet a \ S))) ∘
          (fun p : LinkVariables S × GaugeField a => gluedField ha hS p.1 p.2) =
        fun p => (p.1, restrictField p.2 (positiveLinkSet a \ S)) := by
      funext p
      simp only [Function.comp_apply, h₁, h₂]
    rw [this]
    refine continuous_fst.prodMk (continuous_pi fun b => ?_)
    exact ((continuous_apply b.1).comp continuous_subtype_val).comp continuous_snd
  · refine (eq_gluedField ha hS V U _ (fun b => gluedField_apply_of_mem ha hS V U' b)
      fun b hb => ?_).symm
    rw [gluedField_apply_of_notMem ha hS V U' hb]
    exact (congrFun h ⟨b, hb⟩).symm
theorem id_mem_hypercubicGroup : (LinearMap.id : AmbientSpace →ₗ[ℝ] AmbientSpace) ∈ hypercubicGroup :=
  ⟨1, fun _ => Or.inl rfl⟩
theorem comp_mem_hypercubicGroup {w w' : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hypercubicGroup) (hw' : w' ∈ hypercubicGroup) :
    w ∘ₗ w' ∈ hypercubicGroup := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.comp_mem_hypercubicGroup <;> assumption
theorem exists_inverse_mem_hypercubicGroup {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hypercubicGroup) :
    ∃ w' ∈ hypercubicGroup, (∀ x, w (w' x) = x) ∧ ∀ x, w' (w x) = x := by
  obtain ⟨f, rfl⟩ := exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
  have hunit : ∀ μ, ((f.2 μ : ℤ) : ℝ) * ((f.2 μ : ℤ) : ℝ) = 1 := fun μ => by
    rcases Int.units_eq_one_or (f.2 μ) with hs | hs <;> simp [hs]
  have e₁ : ∀ μ, f.1⁻¹ (f.1 μ) = μ := fun μ => Equiv.symm_apply_apply _ _
  have e₂ : ∀ μ, f.1 (f.1⁻¹ μ) = μ := fun μ => Equiv.apply_symm_apply _ _
  refine ⟨frameLinearMap (f.1⁻¹, fun μ => f.2 (f.1⁻¹ μ)), frameLinearMap_mem_hypercubicGroup _,
    fun x => funext fun μ => ?_, fun x => funext fun μ => ?_⟩
  · simp only [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, LinearMap.coe_mk,
      AddHom.coe_mk, e₁]
    rw [← mul_assoc, hunit, one_mul]
  · simp only [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, LinearMap.coe_mk,
      AddHom.coe_mk, e₂]
    rw [← mul_assoc, hunit, one_mul]
theorem coe_mem_latticeMotions {w : AmbientSpace →ₗ[ℝ] AmbientSpace} (hw : w ∈ hypercubicGroup) :
    (⇑w : AmbientSpace → AmbientSpace) ∈ latticeMotions a :=
  ⟨w, hw, 0, zero_mem _, fun x => by simp⟩
theorem map_mem_latticeSubgroup {w : AmbientSpace →ₗ[ℝ] AmbientSpace} (hw : w ∈ hypercubicGroup)
    {v : AmbientSpace} (hv : v ∈ latticeSubgroup a) : w v ∈ latticeSubgroup a := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.apply_mem_latticeSubgroup <;> assumption
theorem motionsClosed_holds (a : ℝ) : MotionsClosed a := by
  refine ⟨⟨LinearMap.id, id_mem_hypercubicGroup, 0, zero_mem _, fun x => by simp⟩, ?_, ?_⟩
  · rintro r ⟨w, hw, v, hv, hr⟩ t ⟨w', hw', v', hv', ht⟩
    refine ⟨w ∘ₗ w', comp_mem_hypercubicGroup hw hw', w v' + v,
      add_mem (map_mem_latticeSubgroup hw hv') hv, fun x => ?_⟩
    simp only [latticeMotionMul, Function.comp_apply, hr, ht, map_add, LinearMap.comp_apply,
      add_assoc]
  · rintro r ⟨w, hw, v, hv, hr⟩
    obtain ⟨w', hw', h₁, h₂⟩ := exists_inverse_mem_hypercubicGroup hw
    refine ⟨fun x => w' x + -(w' v), ⟨w', hw', -(w' v), neg_mem (map_mem_latticeSubgroup hw' hv),
      fun x => rfl⟩, funext fun x => ?_, funext fun x => ?_⟩
    · simp only [latticeMotionMul, Function.comp_apply, hr, map_add, map_neg, h₁, id]
      abel
    · simp only [latticeMotionMul, Function.comp_apply, hr, map_add, h₂, id]
      abel
theorem coordinateReflection_mem_latticeMotions {μ : Fin 4} {c : ℝ}
    (h : ∃ n : ℤ, 2 * c = (n : ℝ) * a) : coordinateReflection μ c ∈ latticeMotions a := by
  obtain ⟨n, hn⟩ := h
  refine ⟨coordinateSignFlip μ, coordinateSignFlip_mem_hypercubicGroup μ, (2 * c) • basisVector μ,
    ⟨Pi.single μ n, fun ν => ?_⟩, coordinateReflection_eq_signFlip_add μ c⟩
  by_cases h : ν = μ
  · subst h
    simp [basisVector, hn]
  · simp [basisVector, Pi.single_eq_of_ne h]
theorem motionGroupFacts_holds (a : ℝ) : MotionGroupFacts a :=
  ⟨motionsClosed_holds a, fun _ hr =>
      ⟨LatticeMotion.euclidNormVec_sub hr, LatticeMotion.image_latticeSubgroup hr⟩,
    fun v hv => ⟨LinearMap.id, id_mem_hypercubicGroup, v, hv, fun _ => rfl⟩,
    fun _ hw => coe_mem_latticeMotions hw, fun _ _ h => coordinateReflection_mem_latticeMotions h⟩
theorem finite_plaquettes_center_mem (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : {p : ElementaryPlaquette a | p.center ∈ S}.Finite := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.finite_center_mem_of_isBounded <;> assumption
theorem axisStep_ne_zero (ha : 0 < a) (μ : Fin 4) : axisStep a μ ≠ 0 := fun h => by
  have h' := congrFun (congrArg Subtype.val h) μ
  simp [axisStep] at h'
  exact ha.ne' h'
theorem forwardFrom_inj (ha : 0 < a) {x y : LatticePoint a} {κ l : Fin 4}
    (h : Link.forwardFrom x κ = Link.forwardFrom y l) : x = y ∧ κ = l := by
  have h₁ : x = y := congrArg Link.initial h
  subst h₁
  have h₂ : x + axisStep a κ = x + axisStep a l := congrArg Link.terminal h
  have h₃ := add_left_cancel h₂
  refine ⟨rfl, ?_⟩
  by_contra hne
  have h' := congrFun (congrArg Subtype.val h₃) κ
  simp [axisStep, Pi.single_eq_of_ne hne] at h'
  exact ha.ne' h'
def plaquettesAtLink (x : LatticePoint a) (κ : Fin 4) (q : {l : Fin 4 // l ≠ κ} × Bool) :
    ElementaryPlaquette a :=
  ⟨if q.2 then x else x - axisStep a q.1.1, min κ q.1.1, max κ q.1.1, min_lt_max.mpr q.1.2.symm⟩
theorem plaquettesAtLink_injective (ha : 0 < a) (x : LatticePoint a) (κ : Fin 4) :
    Function.Injective (plaquettesAtLink x κ) := by
  have hdec : ∀ κ l l' : Fin 4, l ≠ κ → l' ≠ κ → min κ l = min κ l' → max κ l = max κ l' →
      l = l' := by decide
  rintro ⟨⟨l, hl⟩, ε⟩ ⟨⟨l', hl'⟩, ε'⟩ h
  have h₀ : (if ε then x else x - axisStep a l) = (if ε' then x else x - axisStep a l') :=
    congrArg ElementaryPlaquette.corner h
  have h₁ : min κ l = min κ l' := congrArg ElementaryPlaquette.lowAxis h
  have h₂ : max κ l = max κ l' := congrArg ElementaryPlaquette.highAxis h
  have hll := hdec κ l l' hl hl' h₁ h₂
  subst hll
  have hz := axisStep_ne_zero ha l
  cases ε <;> cases ε'
  · rfl
  · have h₃ : x - axisStep a l = x := by simpa only [Bool.false_eq_true, ↓reduceIte] using h₀
    exact absurd (sub_eq_self.mp h₃) hz
  · have h₃ : x = x - axisStep a l := by simpa only [Bool.false_eq_true, ↓reduceIte] using h₀
    exact absurd (sub_eq_self.mp h₃.symm) hz
  · rfl
theorem range_plaquettesAtLink (ha : 0 < a) (x : LatticePoint a) (κ : Fin 4) :
    range (plaquettesAtLink x κ) =
      {p : ElementaryPlaquette a | Link.forwardFrom x κ ∈ p.sideLinks} := by
  ext p
  constructor
  · rintro ⟨⟨⟨l, hl⟩, ε⟩, rfl⟩
    rcases lt_or_gt_of_ne hl with h | h
    · cases ε
      · simp [plaquettesAtLink, ElementaryPlaquette.sideLinks, min_eq_right h.le, max_eq_left h.le]
      · simp [plaquettesAtLink, ElementaryPlaquette.sideLinks, min_eq_right h.le, max_eq_left h.le]
    · cases ε
      · simp [plaquettesAtLink, ElementaryPlaquette.sideLinks, min_eq_left h.le, max_eq_right h.le]
      · simp [plaquettesAtLink, ElementaryPlaquette.sideLinks, min_eq_left h.le, max_eq_right h.le]
  · obtain ⟨y, f, s, hfs⟩ := p
    intro hp
    simp only [mem_ofPred_eq, ElementaryPlaquette.sideLinks, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with h | h | h | h
    · obtain ⟨rfl, rfl⟩ := forwardFrom_inj ha h
      exact ⟨(⟨s, hfs.ne'⟩, true),
        ElementaryPlaquette.ext rfl (min_eq_left hfs.le) (max_eq_right hfs.le)⟩
    · obtain ⟨rfl, rfl⟩ := forwardFrom_inj ha h
      exact ⟨(⟨s, hfs.ne'⟩, false), ElementaryPlaquette.ext (by simp [plaquettesAtLink])
        (min_eq_left hfs.le) (max_eq_right hfs.le)⟩
    · obtain ⟨rfl, rfl⟩ := forwardFrom_inj ha h
      exact ⟨(⟨f, hfs.ne⟩, true),
        ElementaryPlaquette.ext rfl (min_eq_right hfs.le) (max_eq_left hfs.le)⟩
    · obtain ⟨rfl, rfl⟩ := forwardFrom_inj ha h
      exact ⟨(⟨f, hfs.ne⟩, false), ElementaryPlaquette.ext (by simp [plaquettesAtLink])
        (min_eq_right hfs.le) (max_eq_left hfs.le)⟩
theorem encard_plaquettes_containing_link (ha : 0 < a) (x : LatticePoint a) (κ : Fin 4) :
    {p : ElementaryPlaquette a | Link.forwardFrom x κ ∈ p.sideLinks}.encard = 6 := by
  have hc : ∀ κ : Fin 4, Fintype.card {l : Fin 4 // l ≠ κ} = 3 := by decide
  rw [← range_plaquettesAtLink ha, ← image_univ, (plaquettesAtLink_injective ha x κ).encard_image,
    Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_prod, hc, Fintype.card_bool]
  rfl
theorem encard_hasEdgeIn_le (ha : 0 < a) {W : Set (Link a)} (hW : W.Finite)
    (hB : W ⊆ positiveLinkSet a) :
    {p : ElementaryPlaquette a | p.HasEdgeIn W}.encard ≤ 6 * W.encard := by
  induction W, hW using Set.Finite.induction_on with
  | empty => simp [ElementaryPlaquette.HasEdgeIn]
  | @insert b s hb hs ih =>
    have hsub : {p : ElementaryPlaquette a | p.HasEdgeIn (insert b s)} ⊆
        {p : ElementaryPlaquette a | b ∈ p.sideLinks} ∪
          {p : ElementaryPlaquette a | p.HasEdgeIn s} := by
      rintro p ⟨c, hc, rfl | hs'⟩
      · exact Or.inl hc
      · exact Or.inr ⟨c, hc, hs'⟩
    obtain ⟨x, κ, rfl⟩ := hB (mem_insert _ _)
    calc _ ≤ _ := Set.encard_le_encard hsub
      _ ≤ _ := Set.encard_union_le _ _
      _ ≤ 6 + 6 * s.encard := add_le_add (encard_plaquettes_containing_link ha x κ).le
          (ih fun c hc => hB (mem_insert_of_mem _ hc))
      _ = _ := by
          rw [Set.encard_insert_of_notMem hb, mul_add, mul_one, add_comm]
theorem plaquetteFiniteness_of_pos (ha : 0 < a) : PlaquetteFiniteness a := by
  refine ⟨fun S hS => finite_plaquettes_center_mem ha hS, fun f hf => ?_,
    fun x κ => encard_plaquettes_containing_link ha x κ,
    fun W hB hW => ⟨encard_hasEdgeIn_le ha hW hB, ?_⟩⟩
  · refine (finite_plaquettes_center_mem ha hf.2).subset fun p hp => ?_
    exact hp
  · have hP : {p : ElementaryPlaquette a | p.HasEdgeIn W}.Finite := by
      have h : {p : ElementaryPlaquette a | p.HasEdgeIn W}.encard ≤
          ((6 * hW.toFinset.card : ℕ) : ℕ∞) := by
        push_cast
        rw [← hW.encard_eq_coe_toFinset_card]
        exact encard_hasEdgeIn_le ha hW hB
      exact Set.finite_of_encard_le_coe h
    refine (hP.biUnion fun p _ => List.finite_toSet p.sideLinks).subset ?_
    rintro b ⟨p, hp, hb⟩
    exact mem_iUnion₂.mpr ⟨p, hp, hb⟩
theorem mirrorsAtHalfLevels_of_pos (ha : 0 < a) : MirrorsAtHalfLevels a := by
  rintro μ c ⟨q, rfl⟩
  refine ⟨eq_empty_iff_forall_notMem.mpr ?_,
    coordinateReflection_mem_latticeMotions ⟨2 * q + 1, by push_cast; ring⟩⟩
  rintro x ⟨hx, n, hn⟩
  have h : (n μ : ℝ) * a = ((q : ℝ) + 1 / 2) * a := (hn μ).symm.trans hx
  have h₁ : (n μ : ℝ) = (q : ℝ) + 1 / 2 := mul_right_cancel₀ ha.ne' h
  have h₂ : (2 * n μ : ℝ) = 2 * q + 1 := by rw [h₁]; ring
  have h₃ : 2 * n μ = 2 * q + 1 := by exact_mod_cast h₂
  omega
end Space
section Torus
open PeriodicLattice (CompactGaugeField forwardBonds pointsPerAxis)
variable {L m : ℕ} {j : ℤ}
theorem isInducing_linkValue :
    IsInducing (CompactGaugeField.linkValue : CompactGaugeField L m j → _) :=
  ⟨by rw [induced_to_pi]; rfl⟩
theorem linkValue_injective :
    Function.Injective (CompactGaugeField.linkValue : CompactGaugeField L m j → _) :=
  fun _ _ h => Subtype.ext (funext fun b => congrArg Subtype.val (congrFun h b))
theorem exists_linkValue_eq (f : PeriodicLattice.Bond L m j → ComplexMatrix2.specialUnitary)
    (hf : ∀ b, f b.opposite = (f b)⁻¹) : ∃ U : CompactGaugeField L m j, U.linkValue = f :=
  ⟨CompactGaugeField.ofLinkValues f hf,
    funext fun b => CompactGaugeField.linkValue_ofLinkValues f hf b⟩
theorem torusFieldsAsProduct_of_le (hL : 2 ≤ L) (hj : -(m : ℤ) < j)
    (hf : Finite (PeriodicLattice.Bond L m j)) : TorusFieldsAsProduct L m j := by
  refine ⟨Set.toFinite _, ?_⟩
  refine isHomeomorph_restrictToTransversal
    (CompactGaugeField.linkValue : CompactGaugeField L m j → _)
    PeriodicLattice.Bond.opposite (Subtype.val : forwardBonds L m j → _)
    isInducing_linkValue linkValue_injective exists_linkValue_eq
    (fun U b => U.linkValue_opposite b) (fun _ => rfl) Subtype.val_injective ?_
  rw [Subtype.range_coe]
  exact PeriodicLattice.xor_mem_positiveBonds hL hj
theorem torusFieldBorelGenerated_of_le (hL : 2 ≤ L) (hj : -(m : ℤ) < j)
    (hf : Finite (PeriodicLattice.Bond L m j)) : TorusFieldBorelGenerated L m j := by
  refine ⟨fun S _ => linkVariablesBorelEqPi_of_countable S, ?_⟩
  have h := borel_eq_iSup_comap_of_isInducing _
    (torusFieldsAsProduct_of_le hL hj hf).2.isEmbedding.isInducing
  rw [h, iSup_subtype']
  rfl
theorem torusFieldSplitting_of_le (hL : 2 ≤ L) (hj : -(m : ℤ) < j) :
    TorusFieldSplitting hL hj := by
  intro S hS
  have hH : IsHomeomorph fun U : CompactGaugeField L m j =>
      (U.restrictTo S, U.restrictTo (forwardBonds L m j \ S)) :=
    isHomeomorph_restrictToTransversal_prod
      (CompactGaugeField.linkValue : CompactGaugeField L m j → _)
      PeriodicLattice.Bond.opposite _ S isInducing_linkValue linkValue_injective exists_linkValue_eq
      (fun U b => U.linkValue_opposite b) (fun _ => rfl) hS
      (PeriodicLattice.xor_mem_positiveBonds hL hj)
  have h₁ : ∀ (V : LinkVariables S) (ω : CompactGaugeField L m j),
      (CompactGaugeField.glue hL hj hS V ω).restrictTo S = V := fun V ω =>
    funext fun b => CompactGaugeField.glue_of_mem hL hj hS V ω b
  have h₂ : ∀ (V : LinkVariables S) (ω : CompactGaugeField L m j),
      (CompactGaugeField.glue hL hj hS V ω).restrictTo (forwardBonds L m j \ S) =
        ω.restrictTo (forwardBonds L m j \ S) := fun V ω =>
    funext fun b => CompactGaugeField.glue_of_notMem hL hj hS V ω b.2
  refine ⟨hH, fun V ω => by rw [h₁, h₂], ?_, fun V U U' h => ?_, h₁⟩
  · rw [hH.isEmbedding.isInducing.continuous_iff]
    have : (fun U : CompactGaugeField L m j =>
        (U.restrictTo S, U.restrictTo (forwardBonds L m j \ S))) ∘
          (fun p : LinkVariables S × CompactGaugeField L m j =>
            CompactGaugeField.glue hL hj hS p.1 p.2) =
        fun p => (p.1, p.2.restrictTo (forwardBonds L m j \ S)) := by
      funext p
      simp only [Function.comp_apply, h₁, h₂]
    rw [this]
    refine continuous_fst.prodMk (continuous_pi fun b => ?_)
    exact ((continuous_apply b.1).comp isInducing_linkValue.continuous).comp continuous_snd
  · refine (CompactGaugeField.eq_glue hL hj hS V U _
      (fun b => CompactGaugeField.glue_of_mem hL hj hS V U' b) fun b hb => ?_).symm
    rw [CompactGaugeField.glue_of_notMem hL hj hS V U' hb]
    exact (congrFun h ⟨b, hb⟩).symm
theorem torusCounts_of_le {K : ℕ} (hL : 13 ≤ L) (hm : 0 < m) (hK : 0 < K)
    (hn : ∀ (y : PeriodicLattice.Site L m (K : ℤ)) (μ : Fin 4),
      (PeriodicLattice.axisLine y μ).ncard = 2 * L ^ (m + K)) :
    TorusCounts L m K := by
  have hL' : (13 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (1 : ℝ) < L := by linarith
  have hpow : (L : ℝ) ≤ (L : ℝ) ^ (m + K) := le_self_pow₀ h1.le (by omega)
  refine ⟨rfl, PeriodicLattice.pointsPerAxis_eq L m K, fun y μ => ?_,
    ⟨2 * (L : ℤ) ^ (m + K), even_two_mul _, ?_⟩, ?_, ?_, fun C => ?_⟩
  · rw [hn, PeriodicLattice.pointsPerAxis_eq]
    push_cast
    rfl
  · rw [PeriodicLattice.pointsPerAxis_eq]
    push_cast
    rfl
  · rw [PeriodicLattice.pointsPerAxis_eq]
    linarith
  · have h2 : (L : ℝ) ^ (-(K : ℤ)) < 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ h1 (by omega))
    have h3 : (1 : ℝ) ≤ (L : ℝ) ^ m := one_le_pow₀ h1.le
    simp only [PeriodicLattice.meshSize, PeriodicLattice.torusSide]
    linarith
  · obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt C h1
    refine ⟨PeriodicLattice.torusSide L (n + 1), ⟨n + 1, Nat.succ_pos n, rfl⟩, ?_⟩
    have h4 : (L : ℝ) ^ n ≤ (L : ℝ) ^ (n + 1) := pow_le_pow_right₀ h1.le (Nat.le_succ n)
    have h5 : (0 : ℝ) < (L : ℝ) ^ (n + 1) := by positivity
    simp only [PeriodicLattice.torusSide]
    linarith
end Torus
theorem allFacts_of_torusAndSpaceLatticeProperties
    (h : QuotientLattices.TorusAndSpaceLatticeProperties) : AllFacts := by
  intro s
  have ha := meshSize_pos s
  have hL := two_le_L s
  have hj := neg_m_lt_K s
  have hq := (h s.L s.isAdmissible s.m 0 s.K s.m.pos (Nat.zero_le _)).2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hn, -, hb, -⟩ := hq
  simp only [QuotientLattices.refinementIndex, Nat.cast_zero, sub_zero,
    QuotientLattices.sitesPerAxis, Nat.sub_zero] at hn hb
  exact ⟨fieldsAsProduct_of_pos ha, fieldBorelGenerated_of_pos ha,
    fieldSplitting_of_pos ha, motionGroupFacts_holds _, plaquetteFiniteness_of_pos ha,
    torusCounts_of_le s.isAdmissible.2 s.m.pos s.K.pos hn,
    torusFieldsAsProduct_of_le hL hj hb, torusFieldBorelGenerated_of_le hL hj hb,
    torusFieldSplitting_of_le hL hj, mirrorsAtHalfLevels_of_pos ha⟩
end YangMills.Construction.InfiniteLattice.OneSpacing
end
