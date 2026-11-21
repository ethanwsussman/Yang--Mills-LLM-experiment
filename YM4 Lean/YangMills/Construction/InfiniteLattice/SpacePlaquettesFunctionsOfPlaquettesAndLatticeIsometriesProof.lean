import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfFourSpaceAsBijections
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionSeesNeitherCornerNorSense
import YangMills.Construction.InfiniteLattice.SitesLinksAndPlaquettesOfTheLattice
import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOnALatticeAndItsObservables
import YangMills.Construction.InfiniteLattice.SpacePlaquettesFunctionsOfPlaquettesAndLatticeIsometries
import YangMills.Construction.LawInAState.CovarianceBelowTheAveragesProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CutoffStructureProof
open CutoffLattice CutoffStructure Matrices
variable {a : ℝ}
theorem countable_link (a : ℝ) : Countable (Link a) := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.countable_link <;> assumption
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem linkTopology_eq_instTopology (a : ℝ) :
    linkTopology a = (inferInstance : TopologicalSpace (GaugeField a)) := by
  have h : (inferInstance : TopologicalSpace (GaugeField a)) =
      TopologicalSpace.induced
        (Subtype.val : GaugeField a → Link a → ComplexMatrix2.specialUnitary)
        Pi.topologicalSpace := rfl
  rw [h, Pi.topologicalSpace, induced_iInf]
  simp only [induced_compose]
  rfl
theorem continuous_restrictField (S : Set (Link a)) :
    Continuous (CutoffLattice.restrictField S : GaugeField a → S → ComplexMatrix2.specialUnitary) :=
  continuous_pi fun l => (continuous_apply (l : Link a)).comp continuous_subtype_val
theorem gaugeField_eq_of_positiveLinks (ha : 0 < a) {U V : GaugeField a}
    (h : ∀ l ∈ CutoffLattice.positiveLinks a, U l = V l) : U = V :=
  (fieldEquivValues ha).injective (funext fun l => h l l.2)
theorem fieldOfValues_apply (ha : 0 < a)
    (v : CutoffLattice.positiveLinks a → ComplexMatrix2.specialUnitary)
    (l : Link a) (hl : l ∈ CutoffLattice.positiveLinks a) : fieldOfValues ha v l = v ⟨l, hl⟩ :=
  congrFun ((fieldEquivValues ha).right_inv v) ⟨l, hl⟩
theorem isHomeomorph_restrict_prod (ha : 0 < a) (hc : CompactSpace (GaugeField a))
    (T : Set (Link a)) (hT : T ⊆ CutoffLattice.positiveLinks a) :
    IsHomeomorph (fun U : GaugeField a =>
      (CutoffLattice.restrictField T U,
        CutoffLattice.restrictField (CutoffLattice.positiveLinks a \ T) U)) := by
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨(continuous_restrictField _).prodMk (continuous_restrictField _), ?_, ?_⟩
  · intro U V h
    refine gaugeField_eq_of_positiveLinks ha fun l hl => ?_
    by_cases hl' : l ∈ T
    · exact congrFun (congrArg Prod.fst h) ⟨l, hl'⟩
    · exact congrFun (congrArg Prod.snd h) ⟨l, hl, hl'⟩
  · rintro ⟨v, w⟩
    classical
    let u : CutoffLattice.positiveLinks a → ComplexMatrix2.specialUnitary := fun l =>
      if h : (l : Link a) ∈ T then v ⟨l, h⟩ else w ⟨l, l.2, h⟩
    refine ⟨fieldOfValues ha u, Prod.ext (funext fun l => ?_) (funext fun l => ?_)⟩
    · change fieldOfValues ha u (l : Link a) = v l
      rw [fieldOfValues_apply ha u l (hT l.2)]
      exact dif_pos l.2
    · change fieldOfValues ha u (l : Link a) = w l
      rw [fieldOfValues_apply ha u l l.2.1]
      exact dif_neg l.2.2
theorem borel_pi_eq (ι : Type) [Countable ι] :
    borel (ι → ComplexMatrix2.specialUnitary) = MeasurableSpace.pi := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.borel_linkVariables <;> assumption
theorem borel_prod_pi_eq (ι κ : Type) [Countable ι] [Countable κ] :
    borel ((ι → ComplexMatrix2.specialUnitary) × (κ → ComplexMatrix2.specialUnitary)) =
      (borel (ι → ComplexMatrix2.specialUnitary)).prod
        (borel (κ → ComplexMatrix2.specialUnitary)) := by
  have := secondCountableTopology_specialUnitary
  let m₁ : MeasurableSpace (ι → ComplexMatrix2.specialUnitary) := borel _
  let m₂ : MeasurableSpace (κ → ComplexMatrix2.specialUnitary) := borel _
  have : BorelSpace (ι → ComplexMatrix2.specialUnitary) := ⟨rfl⟩
  have : BorelSpace (κ → ComplexMatrix2.specialUnitary) := ⟨rfl⟩
  exact (BorelSpace.measurable_eq
    (α := (ι → ComplexMatrix2.specialUnitary) × (κ → ComplexMatrix2.specialUnitary))).symm
theorem fieldSpaceStructure (ha : 0 < a) (hc : CompactSpace (GaugeField a))
    (hm : TopologicalSpace.MetrizableSpace (GaugeField a))
    (hb : (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigma (univ : Set (Link a))) : FieldSpaceStructure a := by
  unfold FieldSpaceStructure
  have hcount := countable_link a
  have hsc := secondCountableTopology_specialUnitary
  have hbij : Function.Bijective
      (valuesOnPositive :
        GaugeField a → CutoffLattice.positiveLinks a → ComplexMatrix2.specialUnitary) :=
    (fieldEquivValues ha).bijective
  refine ⟨fun l => ?_, Set.to_countable _, hbij, ?_, linkTopology_eq_instTopology a,
    fun T _ => ?_, hc, hm, hb, fun T hT => ⟨isHomeomorph_restrict_prod ha hc T hT,
      borel_prod_pi_eq _ _⟩⟩
  · by_cases h : l ∈ CutoffLattice.positiveLinks a
    · exact Or.inl ⟨h, opposite_not_mem_positiveLinks ha h⟩
    · exact Or.inr ⟨opposite_mem_positiveLinks_of_not_mem h, h⟩
  · rw [linkTopology_eq_instTopology a, isHomeomorph_iff_continuous_bijective]
    exact ⟨continuous_restrictField _, hbij⟩
  · exact ⟨inferInstance, inferInstance, borel_pi_eq _⟩
theorem axes_eq_of_parity : ∀ f s f' s' : Fin 4, f < s → f' < s' →
    (∀ κ : Fin 4, ((if κ = f then 1 else 0) + (if κ = s then 1 else 0) : ℤ) % 2 =
      ((if κ = f' then 1 else 0) + (if κ = s' then 1 else 0) : ℤ) % 2) → f = f' ∧ s = s' := by
  decide
theorem center_injective (ha : 0 < a) :
    Function.Injective (ElementaryPlaquette.center : ElementaryPlaquette a → AmbientSpace) := by
  intro p q h
  obtain ⟨k, hk⟩ := p.corner.2
  obtain ⟨j, hj⟩ := q.corner.2
  have key : ∀ κ : Fin 4,
      2 * k κ + (if κ = p.lowAxis then 1 else 0) + (if κ = p.highAxis then 1 else 0) =
        2 * j κ + (if κ = q.lowAxis then 1 else 0) + (if κ = q.highAxis then 1 else 0) := by
    intro κ
    have hκ := congrFun h κ
    simp only [ElementaryPlaquette.center, Pi.add_apply, hk κ, hj κ, Pi.single_apply] at hκ
    have hr : ((2 * k κ + (if κ = p.lowAxis then 1 else 0) +
        (if κ = p.highAxis then 1 else 0) : ℤ) : ℝ) * (a / 2) =
        ((2 * j κ + (if κ = q.lowAxis then 1 else 0) +
        (if κ = q.highAxis then 1 else 0) : ℤ) : ℝ) * (a / 2) := by
      push_cast
      split_ifs at hκ ⊢ <;> linarith
    exact_mod_cast mul_right_cancel₀ (by positivity : a / 2 ≠ 0) hr
  have hdir := axes_eq_of_parity p.lowAxis p.highAxis q.lowAxis q.highAxis
    p.lowAxis_lt_highAxis q.lowAxis_lt_highAxis fun κ => by
      have := key κ
      generalize (if κ = p.lowAxis then (1 : ℤ) else 0) = x₁ at this ⊢
      generalize (if κ = p.highAxis then (1 : ℤ) else 0) = x₂ at this ⊢
      generalize (if κ = q.lowAxis then (1 : ℤ) else 0) = x₃ at this ⊢
      generalize (if κ = q.highAxis then (1 : ℤ) else 0) = x₄ at this ⊢
      omega
  refine ElementaryPlaquette.ext (Subtype.ext (funext fun κ => ?_)) hdir.1 hdir.2
  have := key κ
  rw [hdir.1, hdir.2] at this
  have hkj : k κ = j κ := by omega
  rw [hk κ, hj κ, hkj]
theorem axisStep_apply (μ κ : Fin 4) :
    ((axisStep a μ : LatticePoint a) : AmbientSpace) κ = if κ = μ then a else 0 := by apply _root_.YangMills.SharedProofs.p59492 <;> assumption
theorem norm_sub_center_eq (ha : 0 < a) (p : ElementaryPlaquette a) {e e' : ℝ}
    (he : e = 0 ∨ e = 1) (he' : e' = 0 ∨ e' = 1) (y : AmbientSpace)
    (hy : ∀ κ, y κ = (p.corner : AmbientSpace) κ + (if κ = p.lowAxis then e * a else 0) +
      (if κ = p.highAxis then e' * a else 0)) : ‖y - p.center‖ = a / 2 := by
  have hne : p.lowAxis ≠ p.highAxis := ne_of_lt p.lowAxis_lt_highAxis
  have hc : ∀ κ, (y - p.center) κ = (if κ = p.lowAxis then (e - 1 / 2) * a else 0) +
      (if κ = p.highAxis then (e' - 1 / 2) * a else 0) := by
    intro κ
    simp only [Pi.sub_apply, hy, ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply]
    split_ifs <;> ring
  have habs : ∀ t : ℝ, t = 0 ∨ t = 1 → |(t - 1 / 2) * a| = a / 2 := by
    rintro t (rfl | rfl)
    · rw [abs_mul, abs_of_pos ha]
      norm_num [abs_of_neg]
      ring
    · rw [abs_mul, abs_of_pos ha]
      norm_num [abs_of_pos]
      ring
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun κ => ?_
    rw [Real.norm_eq_abs, hc κ]
    by_cases h₁ : κ = p.lowAxis
    · have h₂ : κ ≠ p.highAxis := h₁ ▸ hne
      rw [if_pos h₁, if_neg h₂, add_zero, habs e he]
    · by_cases h₂ : κ = p.highAxis
      · rw [if_neg h₁, if_pos h₂, zero_add, habs e' he']
      · rw [if_neg h₁, if_neg h₂, add_zero, abs_zero]
        positivity
  · have h := norm_le_pi_norm (y - p.center) p.lowAxis
    rwa [Real.norm_eq_abs, hc, if_pos rfl, if_neg hne, add_zero, habs e he] at h
theorem norm_mem_cornerSet_sub_center (ha : 0 < a) (p : ElementaryPlaquette a)
    {y : LatticePoint a} (hy : y ∈ p.cornerSet) : ‖(y : AmbientSpace) - p.center‖ = a / 2 := by
  simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · refine norm_sub_center_eq ha p (Or.inl rfl) (Or.inl rfl) _ fun κ => ?_
    simp
  · refine norm_sub_center_eq ha p (Or.inr rfl) (Or.inl rfl) _ fun κ => ?_
    simp [axisStep_apply]
  · refine norm_sub_center_eq ha p (Or.inr rfl) (Or.inr rfl) _ fun κ => ?_
    simp [axisStep_apply]
  · refine norm_sub_center_eq ha p (Or.inl rfl) (Or.inr rfl) _ fun κ => ?_
    simp [axisStep_apply]
theorem corner_mem_cornerSet (p : ElementaryPlaquette a) : p.corner ∈ p.cornerSet := by
  simp [ElementaryPlaquette.cornerSet]
theorem plaquetteGeometry (ha : 0 < a)
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite) :
    PlaquetteGeometry a := by
  unfold PlaquetteGeometry
  refine ⟨center_injective ha, fun p y hy => norm_mem_cornerSet_sub_center ha p hy,
    fun S hS => ⟨hfin S hS, ?_⟩⟩
  obtain ⟨R, hR⟩ := hS.subset_closedBall (0 : AmbientSpace)
  have hT := hfin (Metric.closedBall 0 (R + a / 2)) Metric.isBounded_closedBall
  have hinj : Function.Injective
      (fun p : ElementaryPlaquette a => (p.corner, p.lowAxis, p.highAxis)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact ElementaryPlaquette.ext h.1 h.2.1 h.2.2
  refine ((hT.prod (Set.finite_univ.prod Set.finite_univ)).preimage hinj.injOn).subset ?_
  intro p hp
  have hb : ‖p.center‖ ≤ R := by
    simpa using hR hp
  have hn : ‖(p.corner : AmbientSpace)‖ ≤ R + a / 2 := by
    have h₁ := norm_mem_cornerSet_sub_center ha p (corner_mem_cornerSet p)
    have h₂ := norm_sub_norm_le (p.corner : AmbientSpace) p.center
    linarith
  simp only [mem_preimage, mem_prod, mem_univ, and_true, mem_ofPred_eq]
  simpa using hn
theorem continuous_re_fullTrace :
    Continuous fun g : ComplexMatrix2.specialUnitary =>
      (ComplexMatrix2.fullTrace (g : ComplexMatrix2)).re :=
  Complex.continuous_re.comp (Continuous.matrix_trace continuous_subtype_val)
def toBoundaryCycle {p : ElementaryPlaquette a} {y : Fin 4 → LatticePoint a} {b : Fin 4 → Link a}
    (h : IsBoundaryCycle p y b) : GibbsAtFixedSpacing.BoundaryCycle p where
  v₁ := y 0
  v₂ := y 1
  v₃ := y 2
  v₄ := y 3
  corners_eq := by
    rw [← h.1]
    ext z
    simp only [mem_insert_iff, mem_singleton_iff, mem_range]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  adj₁₂ := by
    have h₀ := h.2 0
    have hb := (b 0).isAdjacent
    rw [h₀.1, h₀.2] at hb
    exact hb
  adj₂₃ := by
    have h₀ := h.2 1
    have hb := (b 1).isAdjacent
    rw [h₀.1, h₀.2] at hb
    exact hb
  adj₃₄ := by
    have h₀ := h.2 2
    have hb := (b 2).isAdjacent
    rw [h₀.1, h₀.2] at hb
    exact hb
  adj₄₁ := by
    have h₀ := h.2 3
    have hb := (b 3).isAdjacent
    rw [h₀.1, h₀.2] at hb
    exact hb
theorem holonomy_toBoundaryCycle {p : ElementaryPlaquette a} {y : Fin 4 → LatticePoint a}
    {b : Fin 4 → Link a} (h : IsBoundaryCycle p y b) (U : GaugeField a) :
    (toBoundaryCycle h).holonomy U = U (b 0) * U (b 1) * U (b 2) * U (b 3) := by
  have e₀ : ∀ hx, U ⟨y 0, y 1, hx⟩ = U (b 0) := fun hx =>
    congrArg U.1 (Link.ext (h.2 0).1.symm (h.2 0).2.symm)
  have e₁ : ∀ hx, U ⟨y 1, y 2, hx⟩ = U (b 1) := fun hx =>
    congrArg U.1 (Link.ext (h.2 1).1.symm (h.2 1).2.symm)
  have e₂ : ∀ hx, U ⟨y 2, y 3, hx⟩ = U (b 2) := fun hx =>
    congrArg U.1 (Link.ext (h.2 2).1.symm (h.2 2).2.symm)
  have e₃ : ∀ hx, U ⟨y 3, y 0, hx⟩ = U (b 3) := fun hx =>
    congrArg U.1 (Link.ext (h.2 3).1.symm (h.2 3).2.symm)
  change U ⟨y 0, y 1, _⟩ * U ⟨y 1, y 2, _⟩ * U ⟨y 2, y 3, _⟩ * U ⟨y 3, y 0, _⟩ = _
  exact congrArg₂ HMul.hMul (congrArg₂ HMul.hMul (congrArg₂ HMul.hMul (e₀ _) (e₁ _)) (e₂ _)) (e₃ _)
theorem re_fullTrace_boundaryCycle
    (h₂ : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation)
    (ha : 0 < a) (p : ElementaryPlaquette a) (U : GaugeField a) {y : Fin 4 → LatticePoint a}
    {b : Fin 4 → Link a} (h : IsBoundaryCycle p y b) :
    (1 / 2) * (ComplexMatrix2.fullTrace
      ((U (b 0) * U (b 1) * U (b 2) * U (b 3) : ComplexMatrix2.specialUnitary) :
        ComplexMatrix2)).re =
      (1 / 2) * (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re := by
  obtain ⟨hall, -, ⟨c, hc⟩, -⟩ := (h₂.2 a ha).1 p U
  rw [← holonomy_toBoundaryCycle h U, hall (toBoundaryCycle h) c, hc]
theorem isContinuousInLinks_faceEnergy (p : ElementaryPlaquette a) :
    IsContinuousInLinks (faceLinks p)
      (fun U : GaugeField a => faceEnergy U p) := by
  let b₁ : faceLinks p :=
    ⟨Link.forwardFrom p.corner p.lowAxis, by simp [faceLinks, ElementaryPlaquette.edges]⟩
  let b₂ : faceLinks p :=
    ⟨Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis,
      by simp [faceLinks, ElementaryPlaquette.edges]⟩
  let b₃ : faceLinks p :=
    ⟨Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis,
      by simp [faceLinks, ElementaryPlaquette.edges]⟩
  let b₄ : faceLinks p :=
    ⟨Link.forwardFrom p.corner p.highAxis, by simp [faceLinks, ElementaryPlaquette.edges]⟩
  refine ⟨fun v => 1 - (1 / 2) *
    (ComplexMatrix2.fullTrace
      ((v b₁ * v b₂ * (v b₃)⁻¹ * (v b₄)⁻¹ : ComplexMatrix2.specialUnitary) :
        ComplexMatrix2)).re, ?_, fun U => rfl⟩
  exact continuous_const.sub (continuous_const.mul (continuous_re_fullTrace.comp
    ((((continuous_apply b₁).mul (continuous_apply b₂)).mul (continuous_apply b₃).inv).mul
      (continuous_apply b₄).inv)))
theorem faceEnergyProperties
    (h₂ : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation)
    (ha : 0 < a)
    (hc : ∀ p : ElementaryPlaquette a, Continuous fun U : GaugeField a => faceEnergy U p)
    (hi : ∀ (p : ElementaryPlaquette a) (U : GaugeField a), faceEnergy U p ∈ Icc (0 : ℝ) 2) :
    FaceEnergyProperties a :=
  fun p => ⟨fun U _ _ h => re_fullTrace_boundaryCycle h₂ ha p U h, hi p, hc p,
    isContinuousInLinks_faceEnergy p⟩
theorem finsum_cornerSet {E : Type*} [AddCommMonoid E] (p : ElementaryPlaquette a)
    (hnd : [p.corner, p.corner + axisStep a p.lowAxis,
      p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
      p.corner + axisStep a p.highAxis].Nodup) (g : LatticePoint a → E) :
    ∑ᶠ y ∈ p.cornerSet, g y = g p.corner + (g (p.corner + axisStep a p.lowAxis) +
      (g (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis) +
        g (p.corner + axisStep a p.highAxis))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hnd
  obtain ⟨⟨h₁, h₂, h₃⟩, ⟨h₄, h₅⟩, h₆⟩ := hnd
  rw [ElementaryPlaquette.cornerSet, finsum_mem_insert _ (by simp [h₁, h₂, h₃]) (by simp),
    finsum_mem_insert _ (by simp [h₄, h₅]) (by simp), finsum_mem_pair h₆]
theorem four_smul_center (p : ElementaryPlaquette a) :
    (4 : ℝ) • p.center = (p.corner : AmbientSpace) +
      (((p.corner + axisStep a p.lowAxis : LatticePoint a) : AmbientSpace) +
      (((p.corner + axisStep a p.lowAxis + axisStep a p.highAxis : LatticePoint a) :
          AmbientSpace) +
        ((p.corner + axisStep a p.highAxis : LatticePoint a) : AmbientSpace))) := by
  funext κ
  simp only [ElementaryPlaquette.center, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    AddSubgroup.coe_add, axisStep_apply, Pi.single_apply]
  split_ifs <;> ring
theorem center_plaquetteMap (r : LatticeSymmetry a) (p : ElementaryPlaquette a)
    (hnd : ∀ q : ElementaryPlaquette a, [q.corner, q.corner + axisStep a q.lowAxis,
      q.corner + axisStep a q.lowAxis + axisStep a q.highAxis,
      q.corner + axisStep a q.highAxis].Nodup)
    (hc : (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet)
    (hi : Function.Injective r.pointMap) :
    (r.plaquetteMap p).center = r.toFun p.center := by
  obtain ⟨R, hR⟩ := r.exists_linearEquiv_add_apply_zero
  have hm : ∀ y : LatticePoint a,
      ((r.pointMap y : LatticePoint a) : AmbientSpace) = R y + r.toFun 0 := fun y => hR y
  have h₁ : (4 : ℝ) • (r.plaquetteMap p).center =
      ∑ᶠ y ∈ (r.plaquetteMap p).cornerSet, (y : AmbientSpace) :=
    (four_smul_center _).trans (finsum_cornerSet _ (hnd _) _).symm
  rw [hc, finsum_mem_image hi.injOn, finsum_cornerSet p (hnd p)] at h₁
  simp only [hm] at h₁
  have h₂ : (4 : ℝ) • r.toFun p.center = (4 : ℝ) • (r.plaquetteMap p).center := by
    rw [h₁, hR, smul_add, ← map_smul, four_smul_center, map_add, map_add, map_add]
    module
  exact (smul_right_injective AmbientSpace (by norm_num : (4 : ℝ) ≠ 0) h₂).symm
theorem pointMap_injective (r t : LatticeSymmetry a)
    (h : Function.LeftInverse t.toFun r.toFun) : Function.Injective r.pointMap :=
  Function.LeftInverse.injective (g := t.pointMap) fun x => Subtype.ext (h x)
theorem linkMap_linkMap {r t : LatticeSymmetry a} (h : Function.LeftInverse t.toFun r.toFun)
    (b : Link a) : t.linkMap (r.linkMap b) = b :=
  Link.ext (Subtype.ext (h _)) (Subtype.ext (h _))
theorem pullbackField_pullbackField {r t : LatticeSymmetry a}
    (h : Function.LeftInverse r.toFun t.toFun) (U : GaugeField a) :
    t.pullbackField (r.pullbackField U) = U :=
  Subtype.ext (funext fun b => congrArg U.1 (linkMap_linkMap h b))
theorem symmetryProperties (ha : 0 < a)
    (h₁ : FieldSpace.SymmetryProperties)
    (h₃ : SymmetryActionOnObservables)
    (h₄ : SmearedEnergyAndSymmetryAction.Main)
    (hnd : ∀ q : ElementaryPlaquette a, [q.corner, q.corner + axisStep a q.lowAxis,
      q.corner + axisStep a q.lowAxis + axisStep a q.highAxis,
      q.corner + axisStep a q.highAxis].Nodup) :
    CutoffStructure.SymmetryProperties a := by
  obtain ⟨-, -, -, -, hform, -, -, -, hbond, -, -, -, hpl⟩ := h₁ a ha
  obtain ⟨-, hpull, hkeep, hcomp, -, hlin, -, -, -, hinv, -⟩ := h₃ ⟨a, ha⟩
  obtain ⟨-, hact, -, -⟩ := h₄ a ha
  unfold CutoffStructure.SymmetryProperties
  refine ⟨hform, fun r => ?_⟩
  obtain ⟨t, ht⟩ := (hinv r).2.1
  have hA := hact r
  refine ⟨(hbond r).1, (hbond r).2, (hpl r).1, (hpl r).2, fun p => ?_, hA.1, (hpull r).2,
    ⟨t, ht, pullbackField_pullbackField ht.2, pullbackField_pullbackField ht.1⟩,
    ?_, ?_⟩
  · exact center_plaquetteMap r p hnd ((hpl r).1 p) (pointMap_injective r t ht.1)
  · intro r' A A' hA₁ hA₂
    have hk := (hkeep r).1 A A' hA₁ hA₂
    exact ⟨hk.1, ((hlin r).2 A hA₁).2.2.2, hk.2.1, hk.2.2, (hcomp r r').2 A hA₁⟩
  · intro S A hA₁
    constructor
    · intro h
      exact (hA.2.2.2 S A hA₁ h).2.1
    · intro h
      have hrA := ((hkeep r).1 A A hA₁ hA₁).1
      have h₅ := (hact t).2.2.2 (r.setImage S) (r.actOn A) hrA h
      have e₁ : t.setImage (r.setImage S) = S := by
        simp only [LatticeSymmetry.setImage, image_image, ht.1 _, image_id']
      have e₂ : t.actOn (r.actOn A) = A := (((hinv r).2.2 t ht).1 A hA₁).1
      rw [e₁, e₂] at h₅
      exact h₅.2.1
def imageVertices (r : LatticeSymmetry a) (p : ElementaryPlaquette a) :
    Fin 4 → LatticePoint a :=
  ![r.pointMap p.corner, r.pointMap (p.corner + axisStep a p.lowAxis),
    r.pointMap (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis),
    r.pointMap (p.corner + axisStep a p.highAxis)]
def imageLinks (r : LatticeSymmetry a) (p : ElementaryPlaquette a) : Fin 4 → Link a :=
  ![r.linkMap (Link.forwardFrom p.corner p.lowAxis),
    r.linkMap (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis),
    (r.linkMap (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis)).opposite,
    (r.linkMap (Link.forwardFrom p.corner p.highAxis)).opposite]
theorem isBoundaryCycle_image (r : LatticeSymmetry a) (p : ElementaryPlaquette a)
    (hc : (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) :
    IsBoundaryCycle (r.plaquetteMap p) (imageVertices r p) (imageLinks r p) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [hc]
    ext z
    simp only [mem_range, ElementaryPlaquette.cornerSet, image_insert_eq, image_singleton,
      mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [imageVertices]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  · fin_cases i
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · refine ⟨?_, rfl⟩
      change r.pointMap (p.corner + axisStep a p.highAxis + axisStep a p.lowAxis) =
        r.pointMap (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis)
      rw [add_right_comm]
    · exact ⟨rfl, rfl⟩
theorem faceEnergy_pullbackField
    (h₂ : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation)
    (ha : 0 < a) (r : LatticeSymmetry a) (p : ElementaryPlaquette a)
    (hc : (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) (U : GaugeField a) :
    faceEnergy (r.pullbackField U) p = faceEnergy U (r.plaquetteMap p) := by
  have h := re_fullTrace_boundaryCycle h₂ ha (r.plaquetteMap p) U (isBoundaryCycle_image r p hc)
  have e : faceHolonomy (r.pullbackField U) p =
      U (imageLinks r p 0) * U (imageLinks r p 1) * U (imageLinks r p 2) *
        U (imageLinks r p 3) := by
    have e₂ : U (imageLinks r p 2) =
        (U (r.linkMap (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis)))⁻¹ :=
      U.2 _
    have e₃ : U (imageLinks r p 3) = (U (r.linkMap (Link.forwardFrom p.corner p.highAxis)))⁻¹ :=
      U.2 _
    rw [e₂, e₃]
    rfl
  simp only [faceEnergy]
  rw [e, h]
theorem energyCovariance
    (h₂ : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation)
    (ha : 0 < a) (hsum : SmearedEnergyAndSymmetryAction.SmearedEnergyComplex a)
    (hcont : ∀ p : ElementaryPlaquette a, Continuous fun U : GaugeField a => faceEnergy U p)
    (hc : ∀ (r : LatticeSymmetry a) (p : ElementaryPlaquette a),
      (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet)
    (hb : ∀ r : LatticeSymmetry a, Function.Bijective r.plaquetteMap)
    (hx : ∀ (r : LatticeSymmetry a) (p : ElementaryPlaquette a),
      (r.plaquetteMap p).center = r.toFun p.center) : EnergyCovariance a := by
  unfold EnergyCovariance
  refine ⟨fun r p U => faceEnergy_pullbackField h₂ ha r p (hc r p) U, fun f hf => ?_⟩
  obtain ⟨hfin, hs, -, -⟩ := hsum f hf
  have hO : (smearedEnergy f : GaugeField a → ℂ) =
      fun U : GaugeField a => ∑ p ∈ hfin.toFinset, faceEnergy U p • f p.center :=
    funext hs
  refine ⟨hfin.subset ?_, ?_, ?_, fun r => ?_⟩
  · intro p hp h0
    apply hp
    funext U
    simp [show f p.center = 0 from h0]
  · rw [hO]
    exact continuous_finsetSum _ fun p _ => (hcont p).smul continuous_const
  · choose g hg hg' using fun p : ElementaryPlaquette a => isContinuousInLinks_faceEnergy p
    have hmem : ∀ (p : hfin.toFinset) (b : faceLinks (p : ElementaryPlaquette a)),
        (b : Link a) ∈ ⋃ p ∈ {p : ElementaryPlaquette a | f p.center ≠ 0}, faceLinks p :=
      fun p b => mem_biUnion (hfin.mem_toFinset.1 p.2) b.2
    refine ⟨⋃ p ∈ {p : ElementaryPlaquette a | f p.center ≠ 0}, faceLinks p,
      hfin.biUnion fun p _ => List.finite_toSet p.edges,
      fun v => ∑ p ∈ hfin.toFinset.attach,
        g p (fun b => v ⟨b, hmem p b⟩) • f (p : ElementaryPlaquette a).center, ?_, fun U => ?_⟩
    · refine continuous_finsetSum _ fun p _ => ?_
      have h₁ : Continuous fun v :
          (⋃ p ∈ {p : ElementaryPlaquette a | f p.center ≠ 0}, faceLinks p) →
            ComplexMatrix2.specialUnitary => g p (fun b => v ⟨b, hmem p b⟩) :=
        (hg p).comp (continuous_pi fun b => continuous_apply _)
      exact h₁.smul continuous_const
    · rw [hs, ← Finset.sum_attach]
      exact Finset.sum_congr rfl fun p _ =>
        congrArg (· • f (p : ElementaryPlaquette a).center) (hg' p U)
  · funext U
    change smearedEnergy f (r.pullbackField U) = smearedEnergy (r.pushforwardFun f) U
    unfold smearedEnergy
    refine Eq.trans ?_ (finsum_comp_equiv (Equiv.ofBijective r.plaquetteMap (hb r)))
    refine finsum_congr fun p => ?_
    simp only [Equiv.ofBijective_apply]
    rw [faceEnergy_pullbackField h₂ ha r p (hc r p) U, hx r p,
      LatticeSymmetry.pushforwardFun_apply_toFun]
theorem support_smul_subset (f : AmbientSpace → ℂ) (U : GaugeField a) :
    (Function.support fun p : ElementaryPlaquette a => faceEnergy U p • f p.center) ⊆
      {p : ElementaryPlaquette a | f p.center ≠ 0} := by
  intro p hp h0
  apply hp
  simp [show f p.center = 0 from h0]
theorem smearedEnergyAlgebra
    (hsum : SmearedEnergyAndSymmetryAction.SmearedEnergyComplex a)
    (hcov : EnergyCovariance a) : SmearedEnergyAlgebra a := by
  unfold SmearedEnergyAlgebra
  intro f f' hf hf'
  obtain ⟨hfin, -, -, -⟩ := hsum f hf
  obtain ⟨hfin', -, -, -⟩ := hsum f' hf'
  have hadd : (smearedEnergy f + smearedEnergy f' : GaugeField a → ℂ) =
      smearedEnergy (f + f') := by
    funext U
    simp only [Pi.add_apply, smearedEnergy]
    rw [← finsum_add_distrib (hfin.subset (support_smul_subset f U))
      (hfin'.subset (support_smul_subset f' U))]
    exact finsum_congr fun p => (smul_add _ _ _).symm
  have hconj : (fun U : GaugeField a => conj (smearedEnergy f U)) =
      smearedEnergy (fun x => conj (f x)) := by
    funext U
    simp only [smearedEnergy]
    have h := (starRingEnd ℂ).toAddMonoidHom.map_finsum (hfin.subset (support_smul_subset f U))
    refine h.trans (finsum_congr fun p => ?_)
    simp [Complex.real_smul]
  refine ⟨hadd, hconj, ?_, ?_, fun r => ?_⟩
  · funext U
    rw [← Complex.exp_add, ← congrFun hadd U]
    rfl
  · funext U
    rw [← Complex.exp_conj, ← congrFun hconj U]
  · funext U
    exact congrArg Complex.exp (congrFun ((hcov.2 f hf).2.2.2 r) U)
theorem fieldSpaceAndSymmetries (h₁ : FieldSpace.SymmetryProperties)
    (h₂ : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation)
    (h₃ : SymmetryActionOnObservables)
    (h₄ : SmearedEnergyAndSymmetryAction.Main)
    (h₅ : LatticeGeometry.LatticeGeometryStatement)
    (h₆ : ConfigurationSpace.Main) : FieldSpaceAndSymmetries := by
  intro a ha
  obtain ⟨⟨hcomp, hmet, hbor⟩, -, -, -, -, -, -, -, -, -, -, -, hpl⟩ := h₁ a ha
  obtain ⟨-, hbdd, hcorners, -⟩ := h₅ a ha
  obtain ⟨-, -, ⟨hfun, -⟩, -⟩ := h₆ a ha
  have hnd := hcorners.1
  have hcont : ∀ p : ElementaryPlaquette a, Continuous fun U : GaugeField a => faceEnergy U p :=
    fun p => (hfun p).1
  have hiso := symmetryProperties ha h₁ h₃ h₄ hnd
  have hcov := energyCovariance h₂ ha (h₄ a ha).1.1 hcont (fun r => (hpl r).1)
    (fun r => (hpl r).2) (fun r p => (hiso.2 r).2.2.2.2.1 p)
  exact ⟨fieldSpaceStructure ha hcomp hmet hbor,
    plaquetteGeometry ha fun S hS => (hbdd.1 S hS).1,
    faceEnergyProperties h₂ ha hcont fun p => (hfun p).2.1, hiso, hcov,
    smearedEnergyAlgebra (h₄ a ha).1.1 hcov⟩
end YangMills.Construction.InfiniteLattice.CutoffStructureProof
