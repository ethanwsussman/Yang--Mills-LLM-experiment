import YangMills.Construction.InfiniteLattice.WilsonWindows
import YangMills.Construction.Towers.DerivativesOfTheActionOnFinitePlaquetteSetsAtTheSideInfinity
import YangMills.Construction.Towers.SecondDerivativeAtTheSideInfinityOfFormsWithNoCommonPlaquette
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpaceHessianDisjointVanishes
section
variable {L k j : ℕ}
theorem opposite_not_isPositivelyOriented {a : ℝ} (ha : 0 < a) {e : InfiniteLattice.Link a}
    (he : e.IsPositivelyOriented) : ¬ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem complexFaceTerm_expTwist_congr (ha : 0 < meshAt L k j) {p : FullSpace.Face L k j}
    (hp : ∀ e ∈ FullSpace.faceEdges p, e.IsPositivelyOriented)
    {C C' U : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (h : ∀ e ∈ FullSpace.faceEdges p, C e = C' e) :
    FullSpace.complexFaceTerm (FullSpace.expTwist C U) p =
      FullSpace.complexFaceTerm (FullSpace.expTwist C' U) p := by
  have hfor : ∀ e ∈ FullSpace.faceEdges p, FullSpace.expTwist C U e = FullSpace.expTwist C' U e := by
    intro e he
    simp only [FullSpace.expTwist, if_pos (hp e he), h e he]
  have hrev : ∀ e ∈ FullSpace.faceEdges p,
      FullSpace.expTwist C U e.opposite = FullSpace.expTwist C' U e.opposite := by
    intro e he
    have hn := opposite_not_isPositivelyOriented ha (hp e he)
    have r : ∀ D : FullSpace.Edge L k j → Matrices.ComplexMatrix2, FullSpace.expTwist D U e.opposite =
        (Matrices.ComplexMatrix2.matExp (Complex.I • D e) * U e)⁻¹ := fun D => if_neg hn
    rw [r, r, h e he]
  have hv : FullSpace.faceVariable (FullSpace.expTwist C U) p =
      FullSpace.faceVariable (FullSpace.expTwist C' U) p := by
    simp only [FullSpace.faceVariable, FullSpace.linkHolonomy, FullSpace.faceBoundary, List.map_cons,
      List.map_nil]
    rw [hfor _ (by simp [FullSpace.faceEdges]), hfor _ (by simp [FullSpace.faceEdges]),
      hrev _ (by simp [FullSpace.faceEdges]), hrev _ (by simp [FullSpace.faceEdges])]
  simp only [FullSpace.complexFaceTerm, hv]
theorem deriv_deriv_add_separated (f g : ℂ → ℂ) :
    deriv (fun s : ℂ => deriv (fun t : ℂ => f s + g t) 0) 0 = 0 := by
  simp only [deriv_const_add]
  simp
theorem sum_complexFaceTerm_split (ha : 0 < meshAt L k j)
    (hpos : ∀ p : FullSpace.Face L k j, ∀ e ∈ FullSpace.faceEdges p, e.IsPositivelyOriented)
    (Ω : Finset (FullSpace.Face L k j)) {A A' : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (P : FullSpace.Face L k j → Prop) [DecidablePred P]
    (h' : ∀ p, P p → ∀ e ∈ FullSpace.faceEdges p, A' e = 0)
    (h : ∀ p, ¬ P p → ∀ e ∈ FullSpace.faceEdges p, A e = 0)
    (U : FullSpace.Edge L k j → Matrices.ComplexMatrix2) (s t : ℂ) :
    ∑ p ∈ Ω, FullSpace.complexFaceTerm (FullSpace.expTwist (s • A + t • A') U) p =
      ∑ p ∈ Ω.filter P, FullSpace.complexFaceTerm (FullSpace.expTwist (s • A) U) p +
        ∑ p ∈ Ω.filter (fun p => ¬ P p),
          FullSpace.complexFaceTerm (FullSpace.expTwist (t • A') U) p := by
  have h₁ : ∑ p ∈ Ω.filter P, FullSpace.complexFaceTerm (FullSpace.expTwist (s • A + t • A') U) p =
      ∑ p ∈ Ω.filter P, FullSpace.complexFaceTerm (FullSpace.expTwist (s • A) U) p := by
    refine Finset.sum_congr rfl fun p hp => complexFaceTerm_expTwist_congr ha (hpos p) fun e he => ?_
    show s • A e + t • A' e = s • A e
    rw [h' p (Finset.mem_filter.1 hp).2 e he, smul_zero, add_zero]
  have h₂ : ∑ p ∈ Ω.filter (fun p => ¬ P p),
        FullSpace.complexFaceTerm (FullSpace.expTwist (s • A + t • A') U) p =
      ∑ p ∈ Ω.filter (fun p => ¬ P p),
        FullSpace.complexFaceTerm (FullSpace.expTwist (t • A') U) p := by
    refine Finset.sum_congr rfl fun p hp => complexFaceTerm_expTwist_congr ha (hpos p) fun e he => ?_
    show s • A e + t • A' e = t • A' e
    rw [h p (Finset.mem_filter.1 hp).2 e he, smul_zero, zero_add]
  rw [← Finset.sum_filter_add_sum_filter_not Ω P, h₁, h₂]
theorem mixedDirectionalDeriv_eq_zero (ha : 0 < meshAt L k j)
    (hpos : ∀ p : FullSpace.Face L k j, ∀ e ∈ FullSpace.faceEdges p, e.IsPositivelyOriented)
    {Ω : Set (FullSpace.Face L k j)} (hΩ : Ω.Finite)
    {U A A' : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hno : ¬ ∃ p : FullSpace.Face L k j,
      (∃ e ∈ FullSpace.edgeSupport A, e ∈ FullSpace.faceEdges p) ∧
        ∃ e ∈ FullSpace.edgeSupport A', e ∈ FullSpace.faceEdges p) :
    mixedDirectionalDeriv ℂ
      (FullSpace.ActionDerivsOnFiniteFaces.actionAtExpTwist Ω U)
      A A' = 0 := by
  classical
  let P : FullSpace.Face L k j → Prop :=
    fun p => ¬ ∃ e ∈ FullSpace.edgeSupport A', e ∈ FullSpace.faceEdges p
  have h' : ∀ p, P p → ∀ e ∈ FullSpace.faceEdges p, A' e = 0 := by
    intro p hp e he
    by_contra hne
    exact hp ⟨e, ⟨hpos p e he, hne⟩, he⟩
  have h : ∀ p, ¬ P p → ∀ e ∈ FullSpace.faceEdges p, A e = 0 := by
    intro p hp e he
    by_contra hne
    exact hno ⟨p, ⟨e, ⟨hpos p e he, hne⟩, he⟩, not_not.1 hp⟩
  have hsplit : ∀ s t : ℂ,
      FullSpace.ActionDerivsOnFiniteFaces.actionAtExpTwist Ω U (s • A + t • A') =
      ∑ p ∈ hΩ.toFinset.filter P, FullSpace.complexFaceTerm (FullSpace.expTwist (s • A) U) p +
        ∑ p ∈ hΩ.toFinset.filter (fun p => ¬ P p),
          FullSpace.complexFaceTerm (FullSpace.expTwist (t • A') U) p := by
    intro s t
    rw [← sum_complexFaceTerm_split ha hpos hΩ.toFinset P h' h U s t]
    exact finsum_mem_eq_finite_toFinset_sum _ hΩ
  show deriv (fun s : ℂ => deriv (fun t : ℂ =>
    FullSpace.ActionDerivsOnFiniteFaces.actionAtExpTwist Ω U (s • A + t • A')) 0) 0 = 0
  simp only [hsplit]
  exact deriv_deriv_add_separated _ _
end
theorem holds
    (hD : FullSpace.ActionDerivsOnFiniteFaces.Claim)
    (hF : FaceEdgeFinsets.FacesAndEdgesFinite) : FullSpaceHessianDisjointVanishes := by
  intro L k j hL hj U A A' hU hA hA' hfA hfA' hno
  have ha : 0 < meshAt L k j := by
    have hLpos : (0 : ℝ) < L := by
      have : 0 < L := by have := hL.2; omega
      exact_mod_cast this
    exact zpow_pos hLpos _
  obtain ⟨⟨-, hpos⟩, hsets, -⟩ := (hF L hL k j hj).2
  have hSpos : ∀ e ∈ FullSpace.edgeSupport A ∪ FullSpace.edgeSupport A', e.IsPositivelyOriented := by
    rintro e (he | he)
    · exact he.1
    · exact he.1
  obtain ⟨-, -, hΩfin, hΩne⟩ := hsets _ (hfA.union hfA') hSpos
  have hmix := ((hD L k j hL hj U hU _ hΩfin hΩne).1 A A' hA hA' hfA hfA' subset_union_left).2
  rw [hmix]
  exact mixedDirectionalDeriv_eq_zero ha hpos hΩfin hno
end YangMills.Construction.Tower.FullSpaceHessianDisjointVanishes
end
