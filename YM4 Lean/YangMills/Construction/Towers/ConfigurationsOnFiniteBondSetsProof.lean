import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.BondSetFields
private theorem relOpen_iff_image_of_invOn {E E' : Type} [TopologicalSpace E] [TopologicalSpace E']
    {C : Set E} {S : Set E'} {f : E → E'} {g : E' → E} (hf : Continuous f) (hg : Continuous g)
    (hfC : MapsTo f C S) (hgS : MapsTo g S C) (hgf : ∀ x ∈ C, g (f x) = x)
    (hfg : ∀ y ∈ S, f (g y) = y) {O : Set E} (hO : O ⊆ C) :
    Matrices.ComplexMatrix2.IsRelativelyOpen C O ↔
      Matrices.ComplexMatrix2.IsRelativelyOpen S (f '' O) := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨g ⁻¹' A, hA.preimage hg, ?_⟩
    ext y
    constructor
    · rintro ⟨x, ⟨hxA, hxC⟩, rfl⟩
      refine ⟨?_, hfC hxC⟩
      show g (f x) ∈ A
      rw [hgf x hxC]
      exact hxA
    · rintro ⟨hyA, hyS⟩
      exact ⟨g y, ⟨hyA, hgS hyS⟩, hfg y hyS⟩
  · rintro ⟨B, hB, hBe⟩
    refine ⟨f ⁻¹' B, hB.preimage hf, ?_⟩
    ext x
    constructor
    · intro hx
      have h : f x ∈ B ∩ S := hBe ▸ mem_image_of_mem f hx
      exact ⟨h.1, hO hx⟩
    · rintro ⟨hxB, hxC⟩
      have h : f x ∈ f '' O := by
        rw [hBe]
        exact ⟨hxB, hfC hxC⟩
      obtain ⟨y, hy, hyx⟩ := h
      have hxy : y = x := by rw [← hgf y (hO hy), hyx, hgf x hxC]
      exact hxy ▸ hy
private structure AdjugateStable (G : Set Matrices.ComplexMatrix2) : Prop where
  det_eq_one : ∀ X ∈ G, X.det = 1
  adjugate_mem : ∀ X ∈ G, X.adjugate ∈ G
private theorem inv_eq_adjugate_of_det {X : Matrices.ComplexMatrix2} (h : X.det = 1) :
    X⁻¹ = X.adjugate := by
  simp [Matrix.inv_def, h]
abbrev _root_.YangMills.SharedProofs.p104891 := @inv_eq_adjugate_of_det
private theorem adjugate_inv_of_det {X : Matrices.ComplexMatrix2} (h : X.det = 1) :
    X.adjugate⁻¹ = X := by
  rw [← inv_eq_adjugate_of_det h]
  exact Matrix.nonsing_inv_nonsing_inv X (by simp [h])
private theorem adjugateStable_complexGaugeGroup :
    AdjugateStable PeriodicLattice.complexGaugeGroup where
  det_eq_one _ h := h
  adjugate_mem X h := by
    have h' : X.det = 1 := h
    show X.adjugate.det = 1
    rw [Matrix.det_adjugate, h']
    simp
private theorem adjugateStable_compactGaugeGroup :
    AdjugateStable PeriodicLattice.compactGaugeGroup where
  det_eq_one _ h := (Matrix.mem_specialUnitaryGroup_iff.1 h).2
  adjugate_mem X h := by
    obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 h
    have hl : star X * X = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
    have hX : X.adjugate = star X := by
      rw [← inv_eq_adjugate_of_det hd]
      exact Matrix.inv_eq_left_inv hl
    rw [hX]
    refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
    · rw [star_star]
      exact hl
    · rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hd]
      simp
section Extension
variable {β : Type}
open Classical in
private def zeroExtend (pos : β → Prop) (P : Set β)
    (w : positivePart pos P → Matrices.ComplexMatrix2) (b : β) : Matrices.ComplexMatrix2 :=
  if h : b ∈ positivePart pos P then w ⟨b, h⟩ else 0
open Classical in
private def adjugateExtend (rev : β → β) (pos : β → Prop) (P : Set β)
    (w : positivePart pos P → Matrices.ComplexMatrix2) (b : β) : Matrices.ComplexMatrix2 :=
  if pos b then zeroExtend pos P w b else (zeroExtend pos P w (rev b)).adjugate
private theorem continuous_zeroExtend (pos : β → Prop) (P : Set β) (b : β) :
    Continuous fun w => zeroExtend pos P w b := by
  by_cases h : b ∈ positivePart pos P
  · simp only [zeroExtend, dif_pos h]
    exact continuous_apply _
  · simp only [zeroExtend, dif_neg h]
    exact continuous_const
private theorem continuous_adjugateExtend (rev : β → β) (pos : β → Prop) (P : Set β) (b : β) :
    Continuous fun w => adjugateExtend rev pos P w b := by
  by_cases h : pos b
  · simp only [adjugateExtend, if_pos h]
    exact continuous_zeroExtend pos P b
  · simp only [adjugateExtend, if_neg h]
    exact (continuous_zeroExtend pos P (rev b)).matrix_adjugate
private theorem zeroExtend_of_mem {pos : β → Prop} {P : Set β}
    (w : positivePart pos P → Matrices.ComplexMatrix2) {b : β} (h : b ∈ positivePart pos P) :
    zeroExtend pos P w b = w ⟨b, h⟩ := by
  simp only [zeroExtend, dif_pos h]
private theorem continuous_readPositive' (pos : β → Prop) (P : Set β) :
    Continuous (readPositive pos P) :=
  continuous_pi fun _ => continuous_apply _
private theorem continuous_restrict_adjugateExtend (rev : β → β) (pos : β → Prop) (P : Set β) :
    Continuous fun w => restrictTo P (adjugateExtend rev pos P w) :=
  continuous_pi fun b => continuous_adjugateExtend rev pos P b.1
private theorem positivePartCovers_of_involution {rev : β → β} {pos : β → Prop} {P : Set β}
    (hrev : ∀ b, rev (rev b) = b) (hor : ∀ b, pos b ∨ pos (rev b))
    (hnot : ∀ b, pos b → ¬ pos (rev b)) (hfin : P.Finite) (hne : P.Nonempty)
    (hP : ∀ b ∈ P, rev b ∈ P) : PositivePartCovers rev pos P := by
  refine ⟨hfin.subset fun b hb => hb.1, ?_, fun b hb => ?_⟩
  · obtain ⟨b, hb⟩ := hne
    rcases hor b with h | h
    · exact ⟨b, hb, h⟩
    · exact ⟨rev b, hP b hb, h⟩
  · by_cases h : pos b
    · refine Or.inl ⟨⟨hb, h⟩, ?_⟩
      rintro ⟨c, ⟨⟨-, hc⟩, hcb⟩, -⟩
      apply hnot c hc
      rw [hcb]
      exact h
    · have hr : pos (rev b) := (hor b).resolve_left h
      refine Or.inr ⟨⟨rev b, ⟨⟨hP b hb, hr⟩, hrev b⟩, ?_⟩, fun hF => h hF.2⟩
      rintro c ⟨-, hcb⟩
      rw [← hcb, hrev]
variable {rev : β → β} {pos : β → Prop} {P : Set β} {G : Set Matrices.ComplexMatrix2}
  {Q : Set β → (β → Matrices.ComplexMatrix2) → Prop}
  {S : Set (positivePart pos P → Matrices.ComplexMatrix2)}
private theorem adjugateExtend_isField (hG : AdjugateStable G)
    (hrev : ∀ b, rev (rev b) = b) (hor : ∀ b, pos b ∨ pos (rev b))
    (hnot : ∀ b, pos b → ¬ pos (rev b)) (hP : ∀ b ∈ P, rev b ∈ P)
    {w : positivePart pos P → Matrices.ComplexMatrix2} (hw : ∀ i, w i ∈ G) :
    (∀ b ∈ P, adjugateExtend rev pos P w b ∈ G) ∧
      ∀ b ∈ P, adjugateExtend rev pos P w (rev b) = (adjugateExtend rev pos P w b)⁻¹ := by
  have hmem : ∀ b (hb : b ∈ positivePart pos P), zeroExtend pos P w b ∈ G := fun b hb => by
    rw [zeroExtend_of_mem w hb]
    exact hw _
  constructor
  · intro b hb
    by_cases h : pos b
    · simp only [adjugateExtend, if_pos h]
      exact hmem b ⟨hb, h⟩
    · simp only [adjugateExtend, if_neg h]
      exact hG.adjugate_mem _ (hmem _ ⟨hP b hb, (hor b).resolve_left h⟩)
  · intro b hb
    by_cases h : pos b
    · have hr : ¬ pos (rev b) := hnot b h
      simp only [adjugateExtend, if_pos h, if_neg hr, hrev]
      exact (inv_eq_adjugate_of_det (hG.det_eq_one _ (hmem b ⟨hb, h⟩))).symm
    · have hr : pos (rev b) := (hor b).resolve_left h
      simp only [adjugateExtend, if_neg h, if_pos hr]
      exact (adjugate_inv_of_det (hG.det_eq_one _ (hmem _ ⟨hP b hb, hr⟩))).symm
private theorem readPositive_homeomorph (hG : AdjugateStable G)
    (hQ : ∀ U, Q P U ↔ (∀ b ∈ P, U b ∈ G) ∧ ∀ b ∈ P, U (rev b) = (U b)⁻¹)
    (hS : ∀ w, w ∈ S ↔ ∀ i, w i ∈ G)
    (hrev : ∀ b, rev (rev b) = b) (hor : ∀ b, pos b ∨ pos (rev b))
    (hnot : ∀ b, pos b → ¬ pos (rev b)) (hfin : P.Finite) (hP : ∀ b ∈ P, rev b ∈ P) :
    IsReadByPositivePart pos P (fieldsOn Q P) S ∧
      ∀ O, O ⊆ fieldsOn Q P →
        (Matrices.ComplexMatrix2.IsRelativelyOpen (fieldsOn Q P) O ↔
          Matrices.ComplexMatrix2.IsRelativelyOpen S (readPositive pos P '' O)) := by
  have hf := continuous_readPositive' pos P
  have hg := continuous_restrict_adjugateExtend rev pos P
  have hfC : MapsTo (readPositive pos P) (fieldsOn Q P) S := by
    rintro V ⟨U, hU, rfl⟩
    exact (hS _).2 fun i => ((hQ U).1 hU).1 _ i.2.1
  have hgS : MapsTo (fun w => restrictTo P (adjugateExtend rev pos P w)) S (fieldsOn Q P) :=
    fun w hw => ⟨_, (hQ _).2 (adjugateExtend_isField hG hrev hor hnot hP ((hS w).1 hw)), rfl⟩
  have hfg : ∀ w, readPositive pos P (restrictTo P (adjugateExtend rev pos P w)) = w := by
    intro w
    funext b
    show adjugateExtend rev pos P w b.1 = w b
    simp only [adjugateExtend, if_pos b.2.2]
    exact zeroExtend_of_mem w b.2
  have hgf : ∀ V ∈ fieldsOn Q P,
      restrictTo P (adjugateExtend rev pos P (readPositive pos P V)) = V := by
    rintro _ ⟨U, hU, rfl⟩
    obtain ⟨hU₁, hU₂⟩ := (hQ U).1 hU
    have hext : ∀ b (hb : b ∈ positivePart pos P),
        zeroExtend pos P (readPositive pos P (restrictTo P U)) b = U b :=
      fun b hb => zeroExtend_of_mem _ hb
    funext ⟨b, hb⟩
    show adjugateExtend rev pos P _ b = U b
    by_cases h : pos b
    · simp only [adjugateExtend, if_pos h]
      exact hext b ⟨hb, h⟩
    · simp only [adjugateExtend, if_neg h]
      have hr : rev b ∈ P := hP b hb
      rw [hext _ ⟨hr, (hor b).resolve_left h⟩,
        ← inv_eq_adjugate_of_det (hG.det_eq_one _ (hU₁ _ hr)), ← hU₂ _ hr, hrev]
  have hopen : ∀ O, O ⊆ fieldsOn Q P →
      (Matrices.ComplexMatrix2.IsRelativelyOpen (fieldsOn Q P) O ↔
        Matrices.ComplexMatrix2.IsRelativelyOpen S (readPositive pos P '' O)) :=
    fun O hO => relOpen_iff_image_of_invOn hf hg hfC hgS hgf (fun w _ => hfg w) hO
  have hbij : BijOn (readPositive pos P) (fieldsOn Q P) S :=
    InvOn.bijOn (f' := fun w => restrictTo P (adjugateExtend rev pos P w))
      ⟨hgf, fun w _ => hfg w⟩ hfC hgS
  refine ⟨⟨hbij, hf.continuousOn, ?_, hopen, fun ε _ => ?_⟩, hopen⟩
  · refine hg.continuousOn.congr fun w hw => ?_
    have hex : ∃ V ∈ fieldsOn Q P, readPositive pos P V = w := hbij.surjOn hw
    have hmem := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    show Function.invFunOn (readPositive pos P) (fieldsOn Q P) w = _
    rw [← hgf _ hmem, heq]
  · have hfinite : Finite P := hfin.to_subtype
    have hone : Matrices.ComplexMatrix2.IsRelativelyOpen (fieldsOn Q P)
        (nearIdentity (fieldsOn Q P) ε) := by
      refine ⟨⋂ b : P, {V | Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ε}, ?_, ?_⟩
      · exact isOpen_iInter_of_finite fun b =>
          isOpen_lt (continuous_norm.comp ((continuous_apply b).sub continuous_const))
            continuous_const
      · ext V
        simp only [nearIdentity, mem_ofPred_eq, mem_inter_iff, mem_iInter]
        exact and_comm
    exact ⟨hone, (hopen _ fun V hV => hV.1).1 hone⟩
end Extension
private theorem relOpen_iff_restrict_univ {β : Type} {X O : Set (β → Matrices.ComplexMatrix2)}
    (hO : O ⊆ X) :
    Matrices.ComplexMatrix2.IsRelativelyOpen X O ↔
      Matrices.ComplexMatrix2.IsRelativelyOpen (restrictTo (univ : Set β) '' X)
        (restrictTo (univ : Set β) '' O) := by
  refine relOpen_iff_image_of_invOn (g := fun w b => w ⟨b, mem_univ b⟩)
    (continuous_pi fun _ => continuous_apply _) (continuous_pi fun _ => continuous_apply _)
    (mapsTo_image _ _) ?_ (fun _ _ => rfl) (fun _ _ => rfl) hO
  rintro _ ⟨U, hU, rfl⟩
  exact hU
private theorem fieldsOn_univ_eq {β : Type} (Q : Set β → (β → Matrices.ComplexMatrix2) → Prop) :
    fieldsOn Q univ = restrictTo (univ : Set β) '' {U | Q univ U} := by
  ext w
  exact ⟨fun ⟨U, h, e⟩ => ⟨U, h, e.symm⟩, fun ⟨U, h, e⟩ => ⟨U, h, e.symm⟩⟩
private theorem relOpen_iff_reindex {β : Type} {pos : β → Prop} {G : Set Matrices.ComplexMatrix2}
    {S : Set (positivePart pos (univ : Set β) → Matrices.ComplexMatrix2)}
    {S' : Set ({b // pos b} → Matrices.ComplexMatrix2)}
    (hS : ∀ w, w ∈ S ↔ ∀ i, w i ∈ G) (hS' : ∀ w, w ∈ S' ↔ ∀ i, w i ∈ G) {O} (hO : O ⊆ S) :
    Matrices.ComplexMatrix2.IsRelativelyOpen S O ↔
      Matrices.ComplexMatrix2.IsRelativelyOpen S'
        ((fun (w : positivePart pos (univ : Set β) → Matrices.ComplexMatrix2) (b : {b // pos b}) =>
          w ⟨b.1, mem_univ _, b.2⟩) '' O) :=
  relOpen_iff_image_of_invOn (g := fun w b => w ⟨b.1, b.2.2⟩)
    (continuous_pi fun _ => continuous_apply _) (continuous_pi fun _ => continuous_apply _)
    (fun w hw => (hS' _).2 fun _ => (hS w).1 hw _) (fun w hw => (hS _).2 fun _ => (hS' w).1 hw _)
    (fun _ _ => rfl) (fun _ _ => rfl) hO
private theorem relOpen_iff_positive_values {β : Type} {rev : β → β} {pos : β → Prop}
    {G : Set Matrices.ComplexMatrix2} {Q : Set β → (β → Matrices.ComplexMatrix2) → Prop}
    {S' : Set ({b // pos b} → Matrices.ComplexMatrix2)}
    (hG : AdjugateStable G)
    (hQ : ∀ U, Q univ U ↔ (∀ b ∈ univ, U b ∈ G) ∧ ∀ b ∈ univ, U (rev b) = (U b)⁻¹)
    (hS' : ∀ w, w ∈ S' ↔ ∀ i, w i ∈ G) (hrev : ∀ b, rev (rev b) = b)
    (hor : ∀ b, pos b ∨ pos (rev b)) (hnot : ∀ b, pos b → ¬ pos (rev b))
    (hfin : (univ : Set β).Finite) {O : Set (β → Matrices.ComplexMatrix2)}
    (hO : O ⊆ {U | Q univ U}) :
    Matrices.ComplexMatrix2.IsRelativelyOpen {U | Q univ U} O ↔
      Matrices.ComplexMatrix2.IsRelativelyOpen S'
        ((fun (U : β → Matrices.ComplexMatrix2) (b : {b // pos b}) => U b.1) '' O) := by
  have hsub : restrictTo (univ : Set β) '' O ⊆ fieldsOn Q univ := by
    rw [fieldsOn_univ_eq]
    exact image_mono hO
  have hread := (readPositive_homeomorph (P := univ) (Q := Q) (rev := rev) (pos := pos)
    (S := {w | ∀ i, w i ∈ G}) hG hQ (fun _ => Iff.rfl) hrev hor hnot hfin
    (fun _ _ => mem_univ _)).2 _ hsub
  have hvals : readPositive pos univ '' (restrictTo (univ : Set β) '' O) ⊆
      {w | ∀ i, w i ∈ G} := by
    rintro _ ⟨_, ⟨U, hU, rfl⟩, rfl⟩
    exact fun i => ((hQ U).1 (hO hU)).1 _ (mem_univ _)
  have hre := relOpen_iff_reindex (S := {w | ∀ i, w i ∈ G}) (S' := S') (fun _ => Iff.rfl) hS' hvals
  have hfirst := relOpen_iff_restrict_univ hO
  rw [← fieldsOn_univ_eq] at hfirst
  have himage : (fun (w : positivePart pos (univ : Set β) → Matrices.ComplexMatrix2)
      (b : {b // pos b}) => w ⟨b.1, mem_univ _, b.2⟩) ''
        (readPositive pos univ '' (restrictTo univ '' O)) =
      (fun (U : β → Matrices.ComplexMatrix2) (b : {b // pos b}) => U b.1) '' O := by
    rw [image_image, image_image]
    rfl
  rw [himage] at hre
  exact hfirst.trans (hread.trans hre)
private theorem productStructureAt_of_involution {β : Type} {rev : β → β} {pos : β → Prop}
    {IsField : Set Matrices.ComplexMatrix2 → Set β → (β → Matrices.ComplexMatrix2) → Prop}
    (hfield : ∀ G B U, IsField G B U ↔ (∀ b ∈ B, U b ∈ G) ∧ ∀ b ∈ B, U (rev b) = (U b)⁻¹)
    (hrev : ∀ b, rev (rev b) = b) (hor : ∀ b, pos b ∨ pos (rev b))
    (hnot : ∀ b, pos b → ¬ pos (rev b)) {P : Set β} (hfin : P.Finite) (hne : P.Nonempty)
    (hP : ∀ b ∈ P, rev b ∈ P) : ProductStructureAt rev pos IsField P :=
  ⟨positivePartCovers_of_involution hrev hor hnot hfin hne hP,
    (readPositive_homeomorph adjugateStable_complexGaugeGroup (hfield _ P) (fun _ => Iff.rfl)
      hrev hor hnot hfin hP).1,
    (readPositive_homeomorph adjugateStable_compactGaugeGroup (hfield _ P) (fun _ => Iff.rfl)
      hrev hor hnot hfin hP).1⟩
private theorem periodic_positive_or_opposite {L m : ℕ} {i : ℤ} (b : PeriodicLattice.Bond L m i) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
private theorem infinite_positive_or_opposite {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
private theorem fullLatticeProductStructure_of_finite {L n k j : ℕ} (hfin : Finite (Tower.Edge L n k j))
    (hnot : ∀ b : Tower.Edge L n k j,
      b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) :
    FullLatticeProductStructure L n k j := by
  have hrev : ∀ b : Tower.Edge L n k j, b.opposite.opposite = b :=
    fun b => PeriodicLattice.Bond.ext rfl rfl
  have hu : (univ : Set (Tower.Edge L n k j)).Finite := toFinite _
  refine ⟨hu, ⟨PeriodicLattice.Bond.forwardFrom 0 0, mem_univ _⟩, fun _ _ => mem_univ _,
    fieldsOn_univ_eq _, ?_, fun O hO => ?_, fun O hO => ?_, fun O hO => ?_, fun O hO => ?_⟩
  · ext b
    simp [positivePart]
  · rw [fieldsOn_univ_eq]
    exact relOpen_iff_restrict_univ hO
  · rw [fieldsOn_univ_eq]
    exact relOpen_iff_restrict_univ hO
  · exact relOpen_iff_positive_values
      (Q := PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup)
      adjugateStable_compactGaugeGroup (fun _ => Iff.rfl) (fun _ => Iff.rfl) hrev
      periodic_positive_or_opposite hnot hu hO
  · exact relOpen_iff_positive_values
      (Q := PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup)
      adjugateStable_complexGaugeGroup (fun _ => Iff.rfl) (fun _ => Iff.rfl) hrev
      periodic_positive_or_opposite hnot hu hO
private theorem step_ne_neg_step {X : Type} [AddCommGroup X] {Λ : AddSubgroup X} {e : Fin 4 → X}
    (h : QuotientLattices.StepsDistinctAndSigned Λ e) (μ ν : Fin 4) : e μ ≠ -e ν := by
  intro hμν
  have hne := h.2.1 (show QuotientLattices.unitStepsWithZero e (some (1, μ)) =
    QuotientLattices.unitStepsWithZero e (some (-1, ν)) by
      simp [QuotientLattices.unitStepsWithZero, hμν])
  have h1 : (1 : ℤˣ) = -1 := congrArg Prod.fst (Option.some.inj hne)
  exact absurd h1 (by decide)
theorem productStructureHolds_of_torusAndSpaceLatticeProperties
    (hLattices : QuotientLattices.TorusAndSpaceLatticeProperties) : ProductStructureHolds := by
  intro L hL k j hjk
  have hwhole : QuotientLattices.StepsDistinctAndSigned
      (InfiniteLattice.latticeSubgroup (Tower.meshAt L k j))
      (QuotientLattices.spaceAxisSteps (Tower.meshAt L k j)) := by
    obtain ⟨-, -, -, -, -, -, hnine, -, -⟩ := hLattices L hL 1 j k le_rfl hjk
    rw [← Tower.meshSize_levelDepth]
    exact hnine
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨-, hq, -, -, -, hnine, -, -, -⟩ := hLattices L hL n j k hn hjk
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfin, -⟩ := hq
    have hnot : ∀ b : Tower.Edge L n k j,
        b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented := by
      rintro b ⟨μ, hμ⟩ ⟨ν, hν⟩
      have hν' : b.source - b.target = _ := hν
      have hs : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ =
          -PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) ν := by
        rw [← hμ, ← hν', neg_sub]
      exact step_ne_neg_step hnine μ ν (congrArg Subtype.val hs)
    exact ⟨fun P hfinP hne hP => productStructureAt_of_involution (fun _ _ _ => Iff.rfl)
      (fun b => PeriodicLattice.Bond.ext rfl rfl) periodic_positive_or_opposite hnot hfinP hne hP,
      fullLatticeProductStructure_of_finite hfin hnot⟩
  · intro P hfinP hne hP
    have hnot : ∀ b : Tower.FullSpace.Edge L k j,
        b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented := by
      rintro b ⟨μ, hμ⟩ ⟨ν, hν⟩
      have hν' : b.initial - b.terminal = _ := hν
      have hs : InfiniteLattice.axisStep (Tower.meshAt L k j) μ =
          -InfiniteLattice.axisStep (Tower.meshAt L k j) ν := by
        rw [← hμ, ← hν', neg_sub]
      exact step_ne_neg_step hwhole μ ν (congrArg Subtype.val hs)
    exact productStructureAt_of_involution (fun _ _ _ => Iff.rfl)
      (fun b => InfiniteLattice.Link.ext rfl rfl) infinite_positive_or_opposite hnot hfinP hne hP
end YangMills.Construction.Tower.BondSetFields
end
