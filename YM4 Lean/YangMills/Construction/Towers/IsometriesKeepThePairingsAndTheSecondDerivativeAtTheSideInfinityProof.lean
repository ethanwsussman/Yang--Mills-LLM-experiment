import YangMills.Construction.Towers.AverageIsDifferentiableOnThePolydiscProof
import YangMills.Construction.Towers.DerivativesOfTheActionOnFinitePlaquetteSetsAtTheSideInfinity
import YangMills.Construction.Towers.ExpansionOfTheMoveAtTheSideInfinity
import YangMills.Construction.Towers.GaugeAndIsometricImagesAreConfigurations
import YangMills.Construction.Towers.IsometriesKeepThePairingsAndTheSecondDerivativeAtTheSideInfinity
import YangMills.Construction.Towers.IsometriesOnExponentialsAndPlaquettesAtTheSideInfinity
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import YangMills.Construction.Towers.PlaquettesAndSumsOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.LeftChartAlgebra.SymmetriesPreservePairingsAndHessian
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.FaceEdgeFinsets.Unbounded (facesMeeting facesMeetingWithBase)
open YangMills.Construction.Tower.FullSpace.ActionDerivsOnFiniteFaces (actionAtExpTwist)
section SingleLattice
variable {a : ℝ}
theorem opposite_opposite (e : InfiniteLattice.Link a) : e.opposite.opposite = e := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_opposite <;> assumption
theorem opposite_isPositivelyOriented_of_not {e : InfiniteLattice.Link a}
    (h : ¬ e.IsPositivelyOriented) : e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem not_opposite_isPositivelyOriented (ha : a ≠ 0) {e : InfiniteLattice.Link a}
    (h : e.IsPositivelyOriented) : ¬ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.not_opposite_isPositivelyOriented <;> assumption
theorem vertexPreimage_eq {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (hinj : ∀ x y : InfiniteLattice.LatticePoint a, f x = f y → x = y)
    {x x' : InfiniteLattice.LatticePoint a} (h : f x' = x) : vertexPreimage f x = x' := by
  have hspec : f (vertexPreimage f x) = x :=
    Classical.epsilon_spec (p := fun y : InfiniteLattice.LatticePoint a => f y = x) ⟨x', h⟩
  exact hinj _ _ (hspec.trans h.symm)
theorem edgePreimage_eq {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (hinj : ∀ x y : InfiniteLattice.LatticePoint a, f x = f y → x = y)
    {c c' : InfiniteLattice.Link a}
    (hi : (c'.initial : InfiniteLattice.AmbientSpace) = f c.initial)
    (ht : (c'.terminal : InfiniteLattice.AmbientSpace) = f c.terminal) :
    edgePreimage f c' = c := by
  have h1 := vertexPreimage_eq hinj hi.symm
  have h2 := vertexPreimage_eq hinj ht.symm
  have hspec := Classical.epsilon_spec (p := fun e : InfiniteLattice.Link a =>
      e.initial = vertexPreimage f c'.initial ∧ e.terminal = vertexPreimage f c'.terminal)
    ⟨c, h1.symm, h2.symm⟩
  exact InfiniteLattice.Link.ext (hspec.1.trans h1) (hspec.2.trans h2)
theorem edgePreimage_opposite {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (hinj : ∀ x y : InfiniteLattice.LatticePoint a, f x = f y → x = y) (hon : MapsLinksOnto a f)
    (e : InfiniteLattice.Link a) :
    edgePreimage f e.opposite = (edgePreimage f e).opposite := by
  obtain ⟨c, hi, ht⟩ := hon.2 e
  rw [edgePreimage_eq hinj hi ht]
  exact edgePreimage_eq (c := c.opposite) (c' := e.opposite) hinj ht hi
theorem edgePreimage_injective {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (hinj : ∀ x y : InfiniteLattice.LatticePoint a, f x = f y → x = y) (hon : MapsLinksOnto a f) :
    Function.Injective (edgePreimage f : InfiniteLattice.Link a → InfiniteLattice.Link a) := by
  intro e e' heq
  obtain ⟨c, hi, ht⟩ := hon.2 e
  obtain ⟨c', hi', ht'⟩ := hon.2 e'
  rw [edgePreimage_eq hinj hi ht, edgePreimage_eq hinj hi' ht'] at heq
  subst heq
  exact InfiniteLattice.Link.ext (Subtype.ext (hi.trans hi'.symm))
    (Subtype.ext (ht.trans ht'.symm))
def positiveRep (c : InfiniteLattice.Link a) : PositiveEdge a :=
  open Classical in
  if h : c.IsPositivelyOriented then ⟨c, h⟩ else ⟨c.opposite, opposite_isPositivelyOriented_of_not h⟩
theorem positiveRep_of_pos {c : InfiniteLattice.Link a} (h : c.IsPositivelyOriented) :
    (positiveRep c : InfiniteLattice.Link a) = c := by
  simp only [positiveRep, dif_pos h]
theorem positiveRep_of_not_pos {c : InfiniteLattice.Link a} (h : ¬ c.IsPositivelyOriented) :
    (positiveRep c : InfiniteLattice.Link a) = c.opposite := by
  simp only [positiveRep, dif_neg h]
theorem eq_or_eq_opposite_of_positiveRep_eq {c d : InfiniteLattice.Link a}
    (h : positiveRep c = positiveRep d) : c = d ∨ c = d.opposite := by
  have h' := congrArg Subtype.val h
  by_cases hc : c.IsPositivelyOriented <;> by_cases hd : d.IsPositivelyOriented
  · rw [positiveRep_of_pos hc, positiveRep_of_pos hd] at h'
    exact Or.inl h'
  · rw [positiveRep_of_pos hc, positiveRep_of_not_pos hd] at h'
    exact Or.inr h'
  · rw [positiveRep_of_not_pos hc, positiveRep_of_pos hd] at h'
    exact Or.inr (by rw [← h', opposite_opposite])
  · rw [positiveRep_of_not_pos hc, positiveRep_of_not_pos hd] at h'
    refine Or.inl ?_
    have := congrArg InfiniteLattice.Link.opposite h'
    rwa [opposite_opposite, opposite_opposite] at this
def pullbackPositive (f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace) :
    PositiveEdge a → PositiveEdge a :=
  fun e => positiveRep (edgePreimage f (e : InfiniteLattice.Link a))
theorem pullbackPositive_injective (ha : a ≠ 0)
    {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (hinj : ∀ x y : InfiniteLattice.LatticePoint a, f x = f y → x = y) (hon : MapsLinksOnto a f) :
    Function.Injective (pullbackPositive (a := a) f) := by
  intro e e' heq
  rcases eq_or_eq_opposite_of_positiveRep_eq heq with h | h
  · exact Subtype.ext (edgePreimage_injective hinj hon h)
  · rw [← edgePreimage_opposite hinj hon] at h
    have h' := edgePreimage_injective hinj hon h
    exact absurd (h' ▸ e.2) (not_opposite_isPositivelyOriented ha e'.2)
theorem pullbackPositive_surjective (ha : a ≠ 0)
    {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (hinj : ∀ x y : InfiniteLattice.LatticePoint a, f x = f y → x = y) (hon : MapsLinksOnto a f) :
    Function.Surjective (pullbackPositive (a := a) f) := by
  rintro ⟨c, hc⟩
  obtain ⟨d, hi, ht⟩ := hon.1 c
  by_cases hd : d.IsPositivelyOriented
  · refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    change (positiveRep (edgePreimage f d) : InfiniteLattice.Link a) = c
    rw [edgePreimage_eq hinj hi ht, positiveRep_of_pos hc]
  · have hd' : d.opposite.IsPositivelyOriented := opposite_isPositivelyOriented_of_not hd
    refine ⟨⟨d.opposite, hd'⟩, Subtype.ext ?_⟩
    change (positiveRep (edgePreimage f d.opposite) : InfiniteLattice.Link a) = c
    have hpre : edgePreimage f d.opposite = c.opposite := edgePreimage_eq hinj ht hi
    rw [hpre, positiveRep_of_not_pos (not_opposite_isPositivelyOriented ha hc), opposite_opposite]
theorem halfTrace_tangentEdgeValue_mul {U : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : IsFieldIn PeriodicLattice.complexGaugeGroup U) (A A' : InfiniteLattice.Link a → ComplexMatrix2)
    (c : InfiniteLattice.Link a) :
    ComplexMatrix2.halfTrace (tangentEdgeValue U A c * tangentEdgeValue U A' c) =
      ComplexMatrix2.halfTrace (A (positiveRep c) * A' (positiveRep c)) := by
  by_cases h : c.IsPositivelyOriented
  · simp only [tangentEdgeValue, if_pos h, positiveRep_of_pos h]
  · have hdet : (U c.opposite).det = 1 := hU.1 c.opposite
    simp only [tangentEdgeValue, if_neg h, positiveRep_of_not_pos h]
    generalize U c.opposite = g at hdet
    generalize A c.opposite = X
    generalize A' c.opposite = Y
    have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one)
    have hii : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one)
    have hprod : -ComplexMatrix2.conjugateBy g⁻¹ X * -ComplexMatrix2.conjugateBy g⁻¹ Y =
        g⁻¹ * (X * Y * g) := by
      simp only [ComplexMatrix2.conjugateBy, hii, neg_mul_neg]
      calc g⁻¹ * X * g * (g⁻¹ * Y * g) = g⁻¹ * X * (g * g⁻¹) * Y * g := by
            simp only [mul_assoc]
        _ = g⁻¹ * (X * Y * g) := by
            rw [hgi, mul_one]
            simp only [mul_assoc]
    rw [hprod]
    have htr : Matrix.trace (g⁻¹ * (X * Y * g)) = Matrix.trace (X * Y) := by
      rw [Matrix.trace_mul_comm, mul_assoc, hgi, mul_one]
    have hhalf : ∀ M : ComplexMatrix2, ComplexMatrix2.halfTrace M = (2 : ℂ)⁻¹ * Matrix.trace M := by
      intro M
      simp [ComplexMatrix2.halfTrace, Matrix.trace]
    rw [hhalf, hhalf, htr]
theorem edgeFormPairing_isometryOnTangent (ha : a ≠ 0)
    {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (hinj : ∀ x y : InfiniteLattice.LatticePoint a, f x = f y → x = y) (hon : MapsLinksOnto a f)
    {U : InfiniteLattice.Link a → ComplexMatrix2} (hU : IsFieldIn PeriodicLattice.complexGaugeGroup U)
    (A A' : InfiniteLattice.Link a → ComplexMatrix2) :
    finiteEdgePairing (isometryOnTangent f U A) (isometryOnTangent f U A') = finiteEdgePairing A A' := by
  let g : PositiveEdge a → ℂ := fun c =>
    ComplexMatrix2.halfTrace (restrictToPositiveEdges A c * restrictToPositiveEdges A' c)
  have hterm : ∀ e : PositiveEdge a,
      ComplexMatrix2.halfTrace (restrictToPositiveEdges (isometryOnTangent f U A) e *
        restrictToPositiveEdges (isometryOnTangent f U A') e) = g (pullbackPositive f e) := by
    intro e
    have hval : ∀ C : InfiniteLattice.Link a → ComplexMatrix2,
        restrictToPositiveEdges (isometryOnTangent f U C) e =
          tangentEdgeValue U C (edgePreimage f (e : InfiniteLattice.Link a)) := by
      intro C
      simp only [restrictToPositiveEdges, isometryOnTangent, extendOddly, if_pos e.2]
    rw [hval, hval]
    exact halfTrace_tangentEdgeValue_mul hU A A' _
  simp only [finiteEdgePairing, traceFinsumPairing]
  exact (finsum_congr hterm).trans
    (finsum_comp (g := g) _
      ⟨pullbackPositive_injective ha hinj hon, pullbackPositive_surjective ha hinj hon⟩)
theorem conjugateBy_inv_mem_traceless {g X : ComplexMatrix2} (hg : g.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy g⁻¹ X ∈ ComplexMatrix2.traceless := by
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [hg]; exact isUnit_one)
  have hii : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv _ (by rw [hg]; exact isUnit_one)
  have hX' : Matrix.trace X = 0 := hX
  change Matrix.trace (ComplexMatrix2.conjugateBy g⁻¹ X) = 0
  rw [ComplexMatrix2.conjugateBy, hii, Matrix.trace_mul_comm, ← mul_assoc, hgi, one_mul, hX']
theorem tangentEdgeValue_mem {U A : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : IsFieldIn PeriodicLattice.complexGaugeGroup U) (hA : A ∈ complexEdgeForms a)
    (c : InfiniteLattice.Link a) : tangentEdgeValue U A c ∈ ComplexMatrix2.traceless := by
  by_cases h : c.IsPositivelyOriented
  · simp only [tangentEdgeValue, if_pos h]
    exact hA.1 c h
  · simp only [tangentEdgeValue, if_neg h]
    exact ComplexMatrix2.traceless.neg_mem
      (conjugateBy_inv_mem_traceless (hU.1 c.opposite)
        (hA.1 _ (opposite_isPositivelyOriented_of_not h)))
theorem isometryOnTangent_mem (ha : a ≠ 0)
    (f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace)
    {U A : InfiniteLattice.Link a → ComplexMatrix2} (hU : IsFieldIn PeriodicLattice.complexGaugeGroup U)
    (hA : A ∈ complexEdgeForms a) : isometryOnTangent f U A ∈ complexEdgeForms a := by
  change IsEdgeFormIn PeriodicLattice.complexLieAlgebra _
  refine ⟨fun e he => ?_, fun e => ?_⟩
  · simp only [isometryOnTangent, extendOddly, if_pos he]
    exact tangentEdgeValue_mem hU hA _
  · by_cases he : e.IsPositivelyOriented
    · simp only [isometryOnTangent, extendOddly, if_pos he,
        if_neg (not_opposite_isPositivelyOriented ha he), opposite_opposite]
    · simp only [isometryOnTangent, extendOddly, if_neg he,
        if_pos (opposite_isPositivelyOriented_of_not he), neg_neg]
theorem isometryOnTangent_linear_combination
    (f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace)
    (U A A' : InfiniteLattice.Link a → ComplexMatrix2) (s t : ℂ) :
    isometryOnTangent f U (s • A + t • A') =
      s • isometryOnTangent f U A + t • isometryOnTangent f U A' := by
  have hlin : ∀ c : InfiniteLattice.Link a, tangentEdgeValue U (s • A + t • A') c =
      s • tangentEdgeValue U A c + t • tangentEdgeValue U A' c := by
    intro c
    by_cases hc : c.IsPositivelyOriented
    · simp only [tangentEdgeValue, if_pos hc, Pi.add_apply, Pi.smul_apply]
    · simp only [tangentEdgeValue, if_neg hc, Pi.add_apply, Pi.smul_apply,
        ComplexMatrix2.conjugateBy, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg,
        neg_add]
  funext e
  by_cases he : e.IsPositivelyOriented
  · simp only [isometryOnTangent, extendOddly, if_pos he, Pi.add_apply, Pi.smul_apply, hlin]
  · simp only [isometryOnTangent, extendOddly, if_neg he, Pi.add_apply, Pi.smul_apply, hlin,
      smul_neg, neg_add]
theorem ne_zero_of_tangentEdgeValue_ne_zero {U A : InfiniteLattice.Link a → ComplexMatrix2}
    {c : InfiniteLattice.Link a} (h : tangentEdgeValue U A c ≠ 0) : A (positiveRep c) ≠ 0 := by
  intro hz
  apply h
  by_cases hc : c.IsPositivelyOriented
  · rw [positiveRep_of_pos hc] at hz
    simp only [tangentEdgeValue, if_pos hc, hz]
  · rw [positiveRep_of_not_pos hc] at hz
    simp only [tangentEdgeValue, if_neg hc, hz, ComplexMatrix2.conjugateBy, mul_zero, zero_mul,
      neg_zero]
end SingleLattice
section LevelsOfTheTower
variable {L k j : ℕ}
theorem hasFiniteEdgeSupport_isometryOnTangent (ha : meshAt L k j ≠ 0)
    {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (hinj : ∀ x y : Vertex L k j, f x = f y → x = y)
    (hon : MapsLinksOnto (meshAt L k j) f) {U A : Edge L k j → ComplexMatrix2}
    (hA : HasFiniteEdgeSupport A) : HasFiniteEdgeSupport (isometryOnTangent f U A) := by
  let T : Set (PositiveEdge (meshAt L k j)) := {d | (d : Edge L k j) ∈ edgeSupport A}
  have hT : T.Finite := Set.Finite.preimage Subtype.val_injective.injOn hA
  have hP := hT.preimage (pullbackPositive_injective ha hinj hon).injOn
  refine (hP.image Subtype.val).subset ?_
  rintro c ⟨hc, hne⟩
  refine ⟨⟨c, hc⟩, ?_, rfl⟩
  have hval : isometryOnTangent f U A c = tangentEdgeValue U A (edgePreimage f c) := by
    simp only [isometryOnTangent, extendOddly, if_pos hc]
  rw [hval] at hne
  exact ⟨(positiveRep _).2, ne_zero_of_tangentEdgeValue_ne_zero hne⟩
theorem faceTermSum_image {Ω : Set (Face L k j)}
    {φ : Face L k j → Face L k j} (hφ : InjOn φ Ω)
    {W W' : Edge L k j → ComplexMatrix2}
    (h : ∀ p, complexFaceTerm W' (φ p) = complexFaceTerm W p) :
    faceTermSum (φ '' Ω) W' = faceTermSum Ω W := by
  unfold faceTermSum
  rw [finsum_mem_image hφ]
  simp only [h]
end LevelsOfTheTower
end YangMills.Construction.Tower.FullSpace.LeftChartAlgebra.SymmetriesPreservePairingsAndHessian
namespace YangMills.Construction
open Tower.FullSpace.LeftChartAlgebra.SymmetriesPreservePairingsAndHessian in
open Tower.FullSpace Tower.FullSpace.LeftChartAlgebra Matrices in
open Tower.FaceEdgeFinsets.Unbounded (facesMeeting facesMeetingWithBase) in
open Tower.FullSpace.ActionDerivsOnFiniteFaces (actionAtExpTwist) in
theorem Tower.FullSpace.LeftChartAlgebra.SymmetriesPreservePairingsAndHessian.statement_holds
    (hI : Tower.FullSpace.SymmetriesActOnExpAndFaces)
    (hX : Tower.FullSpaceTwistExpansionClaim)
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hE : Tower.FaceSums.FacesAndPairings)
    (hF : Tower.FaceEdgeFinsets.FacesAndEdgesFinite)
    (hD : Tower.FullSpace.ActionDerivsOnFiniteFaces.Claim)
    (hG : Tower.GaugeAndSymmetryImages.statement) :
    Tower.FullSpace.LeftChartAlgebra.SymmetriesPreservePairingsAndHessian := by
  intro L k j hL hjk f U hf hm hU A hA A' hA'
  have hL0 : 0 < L := by have := hL.2; omega
  have ha : Tower.meshAt L k j ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr hL0.ne')
  have hcor := (hE L hL k j hjk).2.1
  obtain ⟨⟨w, -, v, -, hw⟩, hrest, -⟩ := (hT L hL0 hL k).2.2.2.2.1 j hjk f hf hm
  obtain ⟨-, hedges, hfaces⟩ := hrest j le_rfl
  have hfinj : Function.Injective f := by
    intro x y hxy
    rw [hw, hw] at hxy
    exact w.injective (add_right_cancel hxy)
  have hinj : ∀ x y : Vertex L k j, f x = f y → x = y :=
    fun x y hxy => Subtype.ext (hfinj hxy)
  refine ⟨fun _ => edgeFormPairing_isometryOnTangent ha hinj hedges hU A A', fun hfA hfA' => ?_⟩
  have hIU := hI L k j hL hjk f U hf hm hU
  have hpush : pushField f U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    ((hG L k j hL hjk).2 U (fun _ => 1) f hU
      (fun _ => by change (1 : ComplexMatrix2).det = 1; exact Matrix.det_one) hf hm).2.1
  have hex : ∀ p : Face L k j, ∃ p', IsImageFace f p p' :=
    fun p => (hIU.2 p).1.exists
  choose φ hφ using hex
  have hφi : Function.Injective φ := by
    intro p q hpq
    have h1 := hφ p
    have h2 := hφ q
    rw [hpq] at h1
    have hc : faceCorners p = faceCorners q :=
      Subtype.val_injective.image_injective (hfinj.image_injective (h1.symm.trans h2))
    have := (hcor p.corner q.corner p.lowAxis p.highAxis q.lowAxis q.highAxis
      p.lowAxis_lt_highAxis q.lowAxis_lt_highAxis).2 hc
    simp only [Prod.mk.injEq] at this
    obtain ⟨e1, e2, e3⟩ := this
    exact InfiniteLattice.ElementaryPlaquette.ext e1 e2 e3
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨p, hp⟩ := hfaces.2 q
    exact ⟨p, (hIU.2 p).1.unique (hφ p) hp⟩
  have hsA := isometryOnTangent_mem ha f hU hA
  have hsA' := isometryOnTangent_mem ha f hU hA'
  have hfsA := hasFiniteEdgeSupport_isometryOnTangent (U := U) ha hinj hedges hfA
  have hfsA' := hasFiniteEdgeSupport_isometryOnTangent (U := U) ha hinj hedges hfA'
  have hS : (edgeSupport A ∪ edgeSupport A').Finite := Set.Finite.union hfA hfA'
  have hSp : ∀ e ∈ edgeSupport A ∪ edgeSupport A', e.IsPositivelyOriented := by
    rintro e (h | h)
    exacts [h.1, h.1]
  have hS' : (edgeSupport (isometryOnTangent f U A) ∪
      edgeSupport (isometryOnTangent f U A')).Finite :=
    Set.Finite.union hfsA hfsA'
  have hSp' : ∀ e ∈ edgeSupport (isometryOnTangent f U A) ∪
      edgeSupport (isometryOnTangent f U A'), e.IsPositivelyOriented := by
    rintro e (h | h)
    exacts [h.1, h.1]
  have hB := (hF L hL k j hjk).2.2.1 _ hS hSp
  have hB' := (hF L hL k j hjk).2.2.1 _ hS' hSp'
  let Ω : Set (Face L k j) := facesMeetingWithBase (edgeSupport A ∪ edgeSupport A') ∪
    φ ⁻¹' facesMeeting (edgeSupport (isometryOnTangent f U A) ∪
      edgeSupport (isometryOnTangent f U A'))
  have hΩ : Ω.Finite := hB.2.2.1.union (hB'.1.preimage hφi.injOn)
  have hΩn : Ω.Nonempty := hB.2.2.2.mono subset_union_left
  have hsub : facesMeeting (edgeSupport A ∪ edgeSupport A') ⊆ Ω :=
    fun p hp => Or.inl (Or.inl hp)
  have hsub' : facesMeeting (edgeSupport (isometryOnTangent f U A) ∪
      edgeSupport (isometryOnTangent f U A')) ⊆ φ '' Ω := by
    intro q hq
    obtain ⟨p, rfl⟩ := hφs q
    exact ⟨p, Or.inr hq, rfl⟩
  have hd := ((hD L k j hL hjk U hU Ω hΩ hΩn).1 A A' hA hA' hfA hfA' hsub).2
  have hd' := ((hD L k j hL hjk _ hpush (φ '' Ω) (hΩ.image φ) (hΩn.image φ)).1 _ _ hsA hsA'
    hfsA hfsA' hsub').2
  have hsame : ∀ s t : ℂ,
      actionAtExpTwist (φ '' Ω) (pushField f U)
          (s • isometryOnTangent f U A + t • isometryOnTangent f U A') =
        actionAtExpTwist Ω U (s • A + t • A') := by
    intro s t
    have hC : s • A + t • A' ∈ complexEdgeForms (Tower.meshAt L k j) :=
      Submodule.add_mem _ (Submodule.smul_mem _ s hA) (Submodule.smul_mem _ t hA')
    have hV : expTwist (s • A + t • A') U ∈
        fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by
      have := (hX L k j hL hjk U 0 (s • A + t • A') hU
        (fun _ => ComplexMatrix2.traceless.zero_mem) hC).1 1
      rwa [one_smul] at this
    unfold actionAtExpTwist
    rw [← isometryOnTangent_linear_combination, hIU.1 _ hC]
    exact faceTermSum_image hφi.injOn fun p =>
      (hI L k j hL hjk f _ hf hm hV).2 p |>.2 _ (hφ p)
  rw [hd, hd']
  simp only [Tower.mixedDirectionalDeriv, hsame]
end YangMills.Construction
end
