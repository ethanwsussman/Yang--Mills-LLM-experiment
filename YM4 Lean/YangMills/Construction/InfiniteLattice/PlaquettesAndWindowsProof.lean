import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstructionProof
import YangMills.Construction.InfiniteLattice.FactsOfThePlaquettesAtEverySpacingProof
import YangMills.Construction.InfiniteLattice.BondsAndTheirVariables
import YangMills.Construction.InfiniteLattice.CoveringOnAWindowProof
import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacingProof
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLatticeProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.CutoffLinks.FacesOfWindows
variable {a : ℝ}
theorem axisStep_ne_zero (ha : 0 < a) (μ : Fin 4) : axisStep a μ ≠ 0 := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.axisStep_ne_zero <;> assumption
theorem containsLink_forwardFrom_iff
    (hinj : ∀ (x x' : LatticePoint a) (μ μ' : Fin 4),
      Link.forwardFrom x μ = Link.forwardFrom x' μ' → x = x' ∧ μ = μ')
    (p : ElementaryPlaquette a) (x : LatticePoint a) (κ : Fin 4) :
    ContainsLink p (Link.forwardFrom x κ) ↔
      (p.lowAxis = κ ∧ p.corner = x) ∨ (p.highAxis = κ ∧ p.corner = x - axisStep a p.lowAxis) ∨
        (p.lowAxis = κ ∧ p.corner = x - axisStep a p.highAxis) ∨
          (p.highAxis = κ ∧ p.corner = x) := by
  simp only [ContainsLink, ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h | h)
    · obtain ⟨h₁, h₂⟩ := hinj _ _ _ _ h
      exact Or.inl ⟨h₂.symm, h₁.symm⟩
    · obtain ⟨h₁, h₂⟩ := hinj _ _ _ _ h
      exact Or.inr (Or.inl ⟨h₂.symm, by rw [h₁]; abel⟩)
    · obtain ⟨h₁, h₂⟩ := hinj _ _ _ _ h
      exact Or.inr (Or.inr (Or.inl ⟨h₂.symm, by rw [h₁]; abel⟩))
    · obtain ⟨h₁, h₂⟩ := hinj _ _ _ _ h
      exact Or.inr (Or.inr (Or.inr ⟨h₂.symm, h₁.symm⟩))
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · left
      rw [h₁, h₂]
    · right; left
      rw [h₁, h₂, sub_add_cancel]
    · right; right; left
      rw [h₁, h₂, sub_add_cancel]
    · right; right; right
      rw [h₁, h₂]
theorem spannedFace_of_lt (y : LatticePoint a) {κ ι : Fin 4} (h : ι ≠ κ) (hl : κ < ι) :
    spannedFace y κ ι h = plaquetteOf y κ ι hl :=
  dif_pos hl
theorem spannedFace_of_gt (y : LatticePoint a) {κ ι : Fin 4} (h : ι ≠ κ) (hl : ι < κ) :
    spannedFace y κ ι h = plaquetteOf y ι κ hl :=
  dif_neg (not_lt.mpr hl.le)
theorem setOf_containsLink
    (hinj : ∀ (x x' : LatticePoint a) (μ μ' : Fin 4),
      Link.forwardFrom x μ = Link.forwardFrom x' μ' → x = x' ∧ μ = μ')
    (x : LatticePoint a) (κ : Fin 4) :
    {p : ElementaryPlaquette a | ContainsLink p (Link.forwardFrom x κ)} =
      {p | ∃ (ι : Fin 4) (h : ι ≠ κ),
        p = spannedFace x κ ι h ∨ p = spannedFace (x - axisStep a ι) κ ι h} := by
  ext p
  simp only [mem_ofPred_eq, containsLink_forwardFrom_iff hinj]
  constructor
  · obtain ⟨y, μ, ν, h⟩ := p
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · dsimp only at h₁ h₂
      subst h₁ h₂
      exact ⟨ν, h.ne', Or.inl (spannedFace_of_lt _ h.ne' h).symm⟩
    · dsimp only at h₁ h₂
      subst h₁ h₂
      exact ⟨μ, h.ne, Or.inr (spannedFace_of_gt _ h.ne h).symm⟩
    · dsimp only at h₁ h₂
      subst h₁ h₂
      exact ⟨ν, h.ne', Or.inr (spannedFace_of_lt _ h.ne' h).symm⟩
    · dsimp only at h₁ h₂
      subst h₁ h₂
      exact ⟨μ, h.ne, Or.inl (spannedFace_of_gt _ h.ne h).symm⟩
  · rintro ⟨ι, h, rfl | rfl⟩
    · rcases lt_or_gt_of_ne h with hl | hl
      · rw [spannedFace_of_gt _ h hl]
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · rw [spannedFace_of_lt _ h hl]
        exact Or.inl ⟨rfl, rfl⟩
    · rcases lt_or_gt_of_ne h with hl | hl
      · rw [spannedFace_of_gt _ h hl]
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rw [spannedFace_of_lt _ h hl]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
theorem spannedFace_injective {y y' : LatticePoint a} {κ ι ι' : Fin 4} (h : ι ≠ κ)
    (h' : ι' ≠ κ) (he : spannedFace y κ ι h = spannedFace y' κ ι' h') : y = y' ∧ ι = ι' := by
  rcases lt_or_gt_of_ne h with hl | hl <;> rcases lt_or_gt_of_ne h' with hl' | hl'
  · rw [spannedFace_of_gt _ h hl, spannedFace_of_gt _ h' hl'] at he
    simp only [plaquetteOf, ElementaryPlaquette.mk.injEq] at he
    exact ⟨he.1, he.2.1⟩
  · rw [spannedFace_of_gt _ h hl, spannedFace_of_lt _ h' hl'] at he
    simp only [plaquetteOf, ElementaryPlaquette.mk.injEq] at he
    exact absurd he.2.1 h
  · rw [spannedFace_of_lt _ h hl, spannedFace_of_gt _ h' hl'] at he
    simp only [plaquetteOf, ElementaryPlaquette.mk.injEq] at he
    exact absurd he.2.1.symm h'
  · rw [spannedFace_of_lt _ h hl, spannedFace_of_lt _ h' hl'] at he
    simp only [plaquetteOf, ElementaryPlaquette.mk.injEq] at he
    exact ⟨he.1, he.2.2⟩
theorem card_axes_ne : ∀ κ : Fin 4, Fintype.card {ι : Fin 4 // ι ≠ κ} = 3 := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.card_ne_direction <;> assumption
theorem ncard_setOf_containsLink (ha : 0 < a)
    (hinj : ∀ (x x' : LatticePoint a) (μ μ' : Fin 4),
      Link.forwardFrom x μ = Link.forwardFrom x' μ' → x = x' ∧ μ = μ')
    (x : LatticePoint a) (κ : Fin 4) :
    {p : ElementaryPlaquette a | ContainsLink p (Link.forwardFrom x κ)}.ncard = 6 := by
  let f : {ι : Fin 4 // ι ≠ κ} × Bool → ElementaryPlaquette a := fun q =>
    spannedFace (if q.2 = true then x else x - axisStep a q.1) κ q.1 q.1.2
  have hf : Function.Injective f := by
    rintro ⟨⟨ι, h⟩, s⟩ ⟨⟨ι', h'⟩, s'⟩ he
    obtain ⟨hy, hι⟩ := spannedFace_injective h h' he
    dsimp only at hy hι
    subst hι
    have hne : x - axisStep a ι ≠ x := fun e => axisStep_ne_zero ha ι (sub_eq_self.mp e)
    cases s <;> cases s'
    · rfl
    · simp only [Bool.false_eq_true, if_false, if_true] at hy
      exact absurd hy hne
    · simp only [Bool.false_eq_true, if_false, if_true] at hy
      exact absurd hy.symm hne
    · rfl
  have hrange : {p : ElementaryPlaquette a | ContainsLink p (Link.forwardFrom x κ)} =
      f '' univ := by
    rw [setOf_containsLink hinj]
    ext p
    simp only [mem_ofPred_eq, image_univ, mem_range]
    constructor
    · rintro ⟨ι, h, rfl | rfl⟩
      · exact ⟨(⟨ι, h⟩, true), by simp [f]⟩
      · exact ⟨(⟨ι, h⟩, false), by simp [f]⟩
    · rintro ⟨⟨⟨ι, h⟩, s⟩, rfl⟩
      cases s
      · exact ⟨ι, h, Or.inr (by simp [f])⟩
      · exact ⟨ι, h, Or.inl (by simp [f])⟩
  rw [hrange, Set.ncard_image_of_injective _ hf, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_prod, card_axes_ne, Fintype.card_bool]
variable {d : CutoffData} (W : d.CutoffWindow)
theorem faces_eq_biUnion :
    W.faces = ⋃ b ∈ W.finite.toFinset, {p : ElementaryPlaquette d.spacing | ContainsLink p b} := by
  ext p
  simp [CutoffData.CutoffWindow.faces]
theorem ncard_setOf_containsLink_of_mem
    (hinj : ∀ (x x' : LatticePoint d.spacing) (μ μ' : Fin 4),
      Link.forwardFrom x μ = Link.forwardFrom x' μ' → x = x' ∧ μ = μ')
    {b : Link d.spacing} (hb : b ∈ W.links) :
    {p : ElementaryPlaquette d.spacing | ContainsLink p b}.ncard = 6 := by
  obtain ⟨x, κ, rfl⟩ := W.subset_links hb
  exact ncard_setOf_containsLink d.spacing_pos hinj x κ
theorem faces_finite
    (hinj : ∀ (x x' : LatticePoint d.spacing) (μ μ' : Fin 4),
      Link.forwardFrom x μ = Link.forwardFrom x' μ' → x = x' ∧ μ = μ') :
    W.faces.Finite := by
  rw [faces_eq_biUnion]
  refine Set.Finite.biUnion (Finset.finite_toSet _) fun b hb => ?_
  refine Set.finite_of_ncard_ne_zero ?_
  rw [ncard_setOf_containsLink_of_mem W hinj (by simpa using hb)]
  norm_num
theorem faceCount_le
    (hinj : ∀ (x x' : LatticePoint d.spacing) (μ μ' : Fin 4),
      Link.forwardFrom x μ = Link.forwardFrom x' μ' → x = x' ∧ μ = μ') :
    W.faceCount ≤ 6 * W.links.ncard := by
  unfold CutoffData.CutoffWindow.faceCount
  rw [faces_eq_biUnion, Set.ncard_eq_toFinset_card _ W.finite]
  refine (Finset.set_ncard_biUnion_le _ _).trans ?_
  rw [Finset.sum_congr rfl fun b hb =>
    ncard_setOf_containsLink_of_mem W hinj (by simpa using hb : b ∈ W.links)]
  simp [mul_comm]
theorem mem_links_union_rim {p : ElementaryPlaquette d.spacing} (hp : p ∈ W.faces)
    {b : Link d.spacing} (hb : ContainsLink p b) : b ∈ W.links ∪ W.rim := by apply _root_.YangMills.Construction.CutoffLinks.WindowProjection.mem_links_union_rim <;> assumption
theorem rim_finite (hP : W.faces.Finite) : W.rim.Finite := by
  refine (hP.biUnion fun p _ => List.finite_toSet p.edges).subset ?_
  rintro b ⟨⟨p, hp, hb⟩, -⟩
  exact Set.mem_biUnion hp hb
theorem links_inter_rim : W.links ∩ W.rim = ∅ := by
  ext b
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  exact fun h h' => h'.2 h
theorem faceHolonomy_congr {U U' : GaugeField d.spacing}
    (h₁ : restrictField U W.links = restrictField U' W.links)
    (h₂ : restrictField U W.rim = restrictField U' W.rim)
    {p : ElementaryPlaquette d.spacing} (hp : p ∈ W.faces) :
    faceHolonomy U p = faceHolonomy U' p := by
  have hb : ∀ b, ContainsLink p b → U b = U' b := fun b hb => by
    rcases mem_links_union_rim W hp hb with h | h
    · exact congrFun h₁ ⟨b, h⟩
    · exact congrFun h₂ ⟨b, h⟩
  have e₁ := hb (Link.forwardFrom p.corner p.lowAxis)
    (by simp [ContainsLink, ElementaryPlaquette.edges])
  have e₂ := hb (Link.forwardFrom (p.corner + axisStep d.spacing p.lowAxis) p.highAxis)
    (by simp [ContainsLink, ElementaryPlaquette.edges])
  have e₃ := hb (Link.forwardFrom (p.corner + axisStep d.spacing p.highAxis) p.lowAxis)
    (by simp [ContainsLink, ElementaryPlaquette.edges])
  have e₄ := hb (Link.forwardFrom p.corner p.highAxis)
    (by simp [ContainsLink, ElementaryPlaquette.edges])
  unfold faceHolonomy
  rw [e₁, e₂, e₃, e₄]
theorem faceSum_congr {U U' : GaugeField d.spacing}
    (h₁ : restrictField U W.links = restrictField U' W.links)
    (h₂ : restrictField U W.rim = restrictField U' W.rim) :
    W.faceSum U = W.faceSum U' := by
  unfold CutoffData.CutoffWindow.faceSum
  exact finsum_mem_congr rfl fun p hp => by rw [faceHolonomy_congr W h₁ h₂ hp]
theorem restrictField_fieldOf_links (V : LinkVariables W.links) (ξ : LinkVariables W.rim) :
    restrictField (W.fieldOf V ξ) W.links = V := by
  funext b
  exact d.replaceOn_of_mem W.subset_links V _ b
theorem restrictField_fieldOf_rim (V : LinkVariables W.links) (ξ : LinkVariables W.rim) :
    restrictField (W.fieldOf V ξ) W.rim = ξ := by
  funext b
  have hb : (b : Link d.spacing) ∈ d.links \ W.links := ⟨W.rim_subset_links b.2, b.2.2⟩
  exact (d.replaceOn_of_notMem W.subset_links V _ hb).trans
    (d.extendByOne_of_mem W.rim_subset_links ξ b)
theorem boltzmannFactor_restrictField (U : GaugeField d.spacing) :
    W.boltzmannFactor (restrictField U W.links) (restrictField U W.rim) =
      Real.exp (d.coupling * W.faceSum U) := by
  unfold CutoffData.CutoffWindow.boltzmannFactor
  rw [faceSum_congr W (restrictField_fieldOf_links W _ _) (restrictField_fieldOf_rim W _ _)]
theorem continuous_faceHolonomy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceHolonomy U p := by apply _root_.YangMills.Construction.InfiniteLattice.GaugeFieldSpace.continuous_faceHolonomy <;> assumption
theorem continuous_faceSum (hP : W.faces.Finite) :
    Continuous fun U : GaugeField d.spacing => W.faceSum U := by
  unfold CutoffData.CutoffWindow.faceSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hP]
  refine continuous_finsetSum _ fun p _ => continuous_const.mul ?_
  exact Complex.continuous_re.comp
    (Continuous.matrix_trace (continuous_subtype_val.comp (continuous_faceHolonomy p)))
theorem halfReTrace_mul_comm (g h : Matrices.ComplexMatrix2.specialUnitary) :
    halfReTrace (g * h) = halfReTrace (h * g) := by
  unfold halfReTrace
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrices.ComplexMatrix2.fullTrace,
    Matrices.ComplexMatrix2.fullTrace, Matrix.trace_mul_comm]
theorem halfReTrace_inv (g : Matrices.ComplexMatrix2.specialUnitary) :
    halfReTrace g⁻¹ = halfReTrace g := by
  have h : ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      Matrix.conjTranspose (g : Matrices.ComplexMatrix2) := rfl
  unfold halfReTrace
  rw [h, Matrices.ComplexMatrix2.fullTrace, Matrices.ComplexMatrix2.fullTrace,
    Matrix.trace_conjTranspose]
  simp
theorem halfReTrace_cycle (g : Fin 4 → Matrices.ComplexMatrix2.specialUnitary) (i : Fin 4) :
    halfReTrace (g i * g (i + 1) * g (i + 2) * g (i + 3)) =
      halfReTrace (g 0 * g 1 * g 2 * g 3) := by
  fin_cases i
  · rfl
  · change halfReTrace (g 1 * g 2 * g 3 * g 0) = _
    rw [halfReTrace_mul_comm]
    simp only [mul_assoc]
  · change halfReTrace (g 2 * g 3 * g 0 * g 1) = _
    rw [halfReTrace_mul_comm, ← mul_assoc, halfReTrace_mul_comm]
    simp only [mul_assoc]
  · change halfReTrace (g 3 * g 0 * g 1 * g 2) = _
    rw [mul_assoc (g 3), mul_assoc (g 3), halfReTrace_mul_comm]
theorem holonomyBackward_eq_inv (U : GaugeField a) (p : ElementaryPlaquette a) (i : Fin 4) :
    holonomyBackward U p i = (holonomyForward U p i)⁻¹ := by
  have hrev : ∀ b : Link a, U b.opposite = (U b)⁻¹ := U.2
  unfold holonomyBackward holonomyForward
  simp only [hrev, mul_inv_rev]
  fin_cases i
  · change (U (cyclicLink p 3))⁻¹ * (U (cyclicLink p 2))⁻¹ * (U (cyclicLink p 1))⁻¹ *
        (U (cyclicLink p 0))⁻¹ = (U (cyclicLink p 3))⁻¹ * ((U (cyclicLink p 2))⁻¹ *
        ((U (cyclicLink p 1))⁻¹ * (U (cyclicLink p 0))⁻¹))
    simp only [mul_assoc]
  · change (U (cyclicLink p 0))⁻¹ * (U (cyclicLink p 3))⁻¹ * (U (cyclicLink p 2))⁻¹ *
        (U (cyclicLink p 1))⁻¹ = (U (cyclicLink p 0))⁻¹ * ((U (cyclicLink p 3))⁻¹ *
        ((U (cyclicLink p 2))⁻¹ * (U (cyclicLink p 1))⁻¹))
    simp only [mul_assoc]
  · change (U (cyclicLink p 1))⁻¹ * (U (cyclicLink p 0))⁻¹ * (U (cyclicLink p 3))⁻¹ *
        (U (cyclicLink p 2))⁻¹ = (U (cyclicLink p 1))⁻¹ * ((U (cyclicLink p 0))⁻¹ *
        ((U (cyclicLink p 3))⁻¹ * (U (cyclicLink p 2))⁻¹))
    simp only [mul_assoc]
  · change (U (cyclicLink p 2))⁻¹ * (U (cyclicLink p 1))⁻¹ * (U (cyclicLink p 0))⁻¹ *
        (U (cyclicLink p 3))⁻¹ = (U (cyclicLink p 2))⁻¹ * ((U (cyclicLink p 1))⁻¹ *
        ((U (cyclicLink p 0))⁻¹ * (U (cyclicLink p 3))⁻¹))
    simp only [mul_assoc]
theorem holonomyForward_zero (U : GaugeField a) (p : ElementaryPlaquette a) :
    holonomyForward U p 0 = faceHolonomy U p := by
  have hrev : ∀ b : Link a, U b.opposite = (U b)⁻¹ := U.2
  change U (Link.forwardFrom p.corner p.lowAxis) *
      U (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis) *
      U (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis).opposite *
      U (Link.forwardFrom p.corner p.highAxis).opposite = _
  rw [hrev, hrev]
  rfl
theorem halfReTrace_holonomyForward (U : GaugeField a) (p : ElementaryPlaquette a) (i : Fin 4) :
    halfReTrace (holonomyForward U p i) = halfReTrace (faceHolonomy U p) := by
  rw [← holonomyForward_zero]
  exact halfReTrace_cycle (fun j => U (cyclicLink p j)) i
theorem endpoints_cyclicLink (p : ElementaryPlaquette a) (i : Fin 4) :
    (cyclicLink p i).initial = cyclicCorner p i ∧
      (cyclicLink p i).terminal = cyclicCorner p (i + 1) := by apply _root_.YangMills.Construction.InfiniteLattice.PlaquetteProperties.cyclicEdge_ends <;> assumption
theorem faceCorners_determine (hc : ElementarySquare.ElementarySquareStatement) (d : CutoffData)
    (x y : LatticePoint d.spacing) (μ μ' ν ν' : Fin 4) (h : μ < μ') (h' : ν < ν')
    (he : Tower.FullSpace.faceCorners (plaquetteOf x μ μ' h) =
      Tower.FullSpace.faceCorners (plaquetteOf y ν ν' h')) :
    x = y ∧ μ = ν ∧ μ' = ν' := by
  have hs := (hc d.L d.isAdmissible (d.m : ℕ) 0 (d.K : ℕ) d.m.pos (Nat.zero_le _)).2
  have hdepth : PeriodicLattice.levelDepth (d.K : ℕ) 0 = ((d.K : ℕ) : ℤ) := by
    simp [PeriodicLattice.levelDepth]
  rw [hdepth] at hs
  have key : ∀ (z : LatticePoint d.spacing) (α β : Fin 4) (hh : α < β),
      {c | c ∈ ElementarySquare.vertexList (fun μ t => (Pi.single μ t : AmbientSpace)) d.spacing
        (z : AmbientSpace) α β} =
        Subtype.val '' Tower.FullSpace.faceCorners (plaquetteOf z α β hh) := by
    intro z α β hh
    ext c
    simp [ElementarySquare.vertexList, Tower.FullSpace.faceCorners, plaquetteOf, axisStep]
    simp only [eq_comm (a := c)]
  obtain ⟨-, hdet, -⟩ := hs (x : AmbientSpace) x.2 (y : AmbientSpace) y.2 μ μ' ν ν' h h'
  obtain ⟨hxy, hμ, hμ'⟩ := hdet (by rw [key x μ μ' h, key y ν ν' h', he])
  exact ⟨Subtype.ext hxy, hμ, hμ'⟩
theorem statement_holds (h₁ : ElementarySquare.ElementarySquareStatement)
    (h₂ : LinksAndTheirVariables.Statement) : FacesOfWindows.Statement := by
  intro d W
  have hinj := (h₂ d).1.2.1
  have hP := faces_finite W hinj
  refine ⟨?_, ?_, ⟨hP, faceCount_le W hinj⟩, ?_, ?_, ?_⟩
  · intro x y μ μ' ν ν' h h'
    refine ⟨fun he => ?_, faceCorners_determine h₁ d x y μ μ' ν ν' h h'⟩
    simp only [plaquetteOf, ElementaryPlaquette.mk.injEq] at he
    exact he
  · exact fun x κ => ⟨setOf_containsLink hinj x κ, ncard_setOf_containsLink d.spacing_pos hinj x κ⟩
  · exact ⟨links_inter_rim W, W.finite.union (rim_finite W hP),
      fun p hp b hb => mem_links_union_rim W hp hb⟩
  · refine ⟨fun U U' e e' => faceSum_congr W e e', fun V ξ =>
      ⟨W.fieldOf V ξ, restrictField_fieldOf_links W V ξ,
        restrictField_fieldOf_rim W V ξ⟩, ⟨fun q => W.boltzmannFactor q.1 q.2,
          boltzmannFactor_restrictField W, fun f hf => ?_⟩, boltzmannFactor_restrictField W,
      fun V ξ => Real.exp_pos _, ?_⟩
    · funext q
      obtain ⟨V, ξ⟩ := q
      have e := hf (W.fieldOf V ξ)
      rw [restrictField_fieldOf_links, restrictField_fieldOf_rim] at e
      rw [e]
      rfl
    · obtain ⟨-, hext, -, hW⟩ := (h₂ d).2.2.2.2.2 W.rim W.rim_subset_links
      have hVU := (hW W.links W.subset_links W.finite).1
      have hconf : Continuous fun q : LinkVariables W.links × LinkVariables W.rim =>
          W.fieldOf q.1 q.2 :=
        hVU.comp (continuous_fst.prodMk (hext.comp continuous_snd))
      unfold CutoffData.CutoffWindow.boltzmannFactor
      exact Real.continuous_exp.comp
        (continuous_const.mul ((continuous_faceSum W hP).comp hconf))
  · intro p U
    refine ⟨endpoints_cyclicLink p, fun i => ⟨halfReTrace_holonomyForward U p i, ?_⟩⟩
    rw [holonomyBackward_eq_inv, halfReTrace_inv]
    exact halfReTrace_holonomyForward U p i
end YangMills.Construction.CutoffLinks.FacesOfWindows
