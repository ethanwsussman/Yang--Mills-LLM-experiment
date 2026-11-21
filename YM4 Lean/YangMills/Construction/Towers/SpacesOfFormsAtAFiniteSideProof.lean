import YangMills.Construction.OneLoop.PauliMatrixRelations
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.SpacesOfFormsAtAFiniteSide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.FiniteSideForms
open QuotientLattices (IsPositiveStep IsSignedAxisStep StepsDistinctAndSigned torusAxisSteps)
variable {L n k j : ℕ}
theorem isBondForm_coe (B : edgeFormSpace L n k j) :
    PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra
      (B : Edge L n k j → ComplexMatrix2) := B.2
def evalPositive (B : edgeFormSpace L n k j) (p : PositiveEdge L n k j) :
    ComplexMatrix2.hermitianTraceless :=
  ⟨(B : Edge L n k j → ComplexMatrix2) p.1, (isBondForm_coe B).1 p.1 p.2⟩
def positiveValues :
    edgeFormSpace L n k j →ₗ[ℝ] (PositiveEdge L n k j → ComplexMatrix2.hermitianTraceless) where
  toFun := evalPositive
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem isPositivelyOriented_iff_isPositiveStep (b : Edge L n k j) :
    b.IsPositivelyOriented ↔
      IsPositiveStep (torusAxisSteps L n k j) (b.source : PeriodicLattice.FourTorus L n)
        (b.target : PeriodicLattice.FourTorus L n) := by
  constructor
  · rintro ⟨μ, h⟩
    refine ⟨μ, ?_⟩
    have h' := congrArg Subtype.val h
    simpa [IsSignedAxisStep, torusAxisSteps] using h'
  · rintro ⟨μ, h⟩
    refine ⟨μ, Subtype.ext ?_⟩
    simpa [IsSignedAxisStep, torusAxisSteps] using h
theorem xor_isPositivelyOriented_opposite
    (h : StepsDistinctAndSigned
      (PeriodicLattice.sublattice L n (QuotientLattices.refinementIndex k j))
      (torusAxisSteps L n k j)) (b : Edge L n k j) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  have hb := (h.2.2 b.source.1 b.source.2 b.target.1 b.target.2).2
  have step : ∃ (ε : ℤˣ) (μ : Fin 4),
      IsSignedAxisStep (torusAxisSteps L n k j) (b.source : PeriodicLattice.FourTorus L n)
        (b.target : PeriodicLattice.FourTorus L n) ε μ := by
    obtain ⟨μ, e | e⟩ := b.isNeighbour
    · refine ⟨1, μ, ?_⟩
      have e' := congrArg Subtype.val e
      simpa [IsSignedAxisStep, torusAxisSteps] using e'
    · refine ⟨-1, μ, ?_⟩
      have e' := congrArg Subtype.val e
      simpa [IsSignedAxisStep, torusAxisSteps] using e'
  obtain ⟨ε, μ, hs⟩ := step
  have hx := (hb ε μ hs).2
  have h₁ := isPositivelyOriented_iff_isPositiveStep b
  have h₂ : b.opposite.IsPositivelyOriented ↔ IsPositiveStep (torusAxisSteps L n k j)
      (b.target : PeriodicLattice.FourTorus L n) (b.source : PeriodicLattice.FourTorus L n) :=
    isPositivelyOriented_iff_isPositiveStep b.opposite
  unfold Xor at hx ⊢
  rw [h₁, h₂]
  exact hx
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
open Classical in
def oddExtension (v : PositiveEdge L n k j → ComplexMatrix2.hermitianTraceless)
    (b : Edge L n k j) : ComplexMatrix2 :=
  if h : b.IsPositivelyOriented then (v ⟨b, h⟩ : ComplexMatrix2)
  else if h' : b.opposite.IsPositivelyOriented then -(v ⟨b.opposite, h'⟩ : ComplexMatrix2)
  else 0
theorem oddExtension_of_pos (v : PositiveEdge L n k j → ComplexMatrix2.hermitianTraceless)
    {b : Edge L n k j} (h : b.IsPositivelyOriented) :
    oddExtension v b = (v ⟨b, h⟩ : ComplexMatrix2) := dif_pos h
theorem oddExtension_of_not_pos (v : PositiveEdge L n k j → ComplexMatrix2.hermitianTraceless)
    {b : Edge L n k j} (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    oddExtension v b = -(v ⟨b.opposite, h'⟩ : ComplexMatrix2) := by
  unfold oddExtension
  rw [dif_neg h, dif_pos h']
theorem oddExtension_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (v : PositiveEdge L n k j → ComplexMatrix2.hermitianTraceless) :
    oddExtension v ∈ edgeFormSpace L n k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [oddExtension_of_pos v hb]
    exact (v ⟨b, hb⟩).2
  · rcases hx b with ⟨hp, hn⟩ | ⟨hp, hn⟩
    · have hr : b.opposite.opposite.IsPositivelyOriented := by rwa [opposite_opposite]
      rw [oddExtension_of_not_pos v hn hr, oddExtension_of_pos v hp]
      have : (⟨b.opposite.opposite, hr⟩ : PositiveEdge L n k j) = ⟨b, hp⟩ :=
        Subtype.ext (opposite_opposite b)
      rw [this]
    · rw [oddExtension_of_pos v hp, oddExtension_of_not_pos v hn hp, neg_neg]
theorem positiveValues_injective
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    Function.Injective (positiveValues (L := L) (n := n) (k := k) (j := j)) := by
  intro B B' h
  have hv : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      (B : Edge L n k j → ComplexMatrix2) b = (B' : Edge L n k j → ComplexMatrix2) b :=
    fun b hb => congrArg Subtype.val (congrFun h ⟨b, hb⟩)
  refine Subtype.ext (funext fun b => ?_)
  rcases hx b with ⟨hp, _⟩ | ⟨hp, _⟩
  · exact hv b hp
  · have := hv _ hp
    rw [(isBondForm_coe B).2, (isBondForm_coe B').2] at this
    exact neg_injective this
theorem positiveValues_surjective
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    Function.Surjective (positiveValues (L := L) (n := n) (k := k) (j := j)) := by
  intro v
  refine ⟨⟨oddExtension v, oddExtension_mem hx v⟩, funext fun p => Subtype.ext ?_⟩
  exact oddExtension_of_pos v p.2
def positiveValuesEquiv
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    edgeFormSpace L n k j ≃ₗ[ℝ] (PositiveEdge L n k j → ComplexMatrix2.hermitianTraceless) :=
  LinearEquiv.ofBijective positiveValues
    ⟨positiveValues_injective hx, positiveValues_surjective hx⟩
def lieEval (B : edgeFormSpace L n k j) (p : PositiveEdge L n k j) :
    ComplexMatrix2.LieElement := evalPositive B p
theorem restrictToPositiveEdges_eq_toMatrix (B : edgeFormSpace L n k j)
    (p : PositiveEdge L n k j) :
    restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2) p = (lieEval B p).toMatrix := rfl
theorem halfTrace_mul_eq_inner (A B : ComplexMatrix2.LieElement) :
    ComplexMatrix2.halfTrace (A.toMatrix * B.toMatrix) =
      ((inner ℝ A B : ℝ) : ℂ) := by
  have him : (ComplexMatrix2.fullTrace (A.toMatrix * B.toMatrix)).im = 0 :=
    Complex.conj_eq_iff_im.mp (ComplexMatrix2.LieElement.star_fullTrace_mul A B)
  apply Complex.ext
  · rw [Complex.ofReal_re]
    rfl
  · simp [ComplexMatrix2.halfTrace, him]
@[instance_reducible]
def innerProductCore
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [Fintype (PositiveEdge L n k j)] : InnerProductSpace.Core ℝ (edgeFormSpace L n k j) where
  inner B B' := ∑ p, inner ℝ (lieEval B p) (lieEval B' p)
  conj_inner_symm B B' := by
    simp only [conj_trivial]
    exact Finset.sum_congr rfl fun p _ => real_inner_comm _ _
  re_inner_nonneg B := by
    simp only [RCLike.re_to_real]
    exact Finset.sum_nonneg fun p _ => real_inner_self_nonneg
  add_left B B' C := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e : lieEval (B + B') p = lieEval B p + lieEval B' p := rfl
    rw [e, inner_add_left]
  smul_left B B' c := by
    rw [conj_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e : lieEval (c • B) p = c • lieEval B p := rfl
    rw [e, real_inner_smul_left]
  definite B h := by
    have h₀ := (Finset.sum_eq_zero_iff_of_nonneg fun p _ =>
      real_inner_self_nonneg (x := lieEval B p)).mp h
    apply positiveValues_injective hx
    rw [map_zero]
    funext p
    exact inner_self_eq_zero.mp (h₀ p (Finset.mem_univ p))
theorem finiteSideFormSpaces_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hP : OneLoop.PauliMatrixRelations) : FiniteSideFormSpaces := by
  intro L n k j hL hn hjk
  obtain ⟨_, hq, _, _, _, hnine, _⟩ := hA L hL n j k hn hjk
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := hq
  have hx := xor_isPositivelyOriented_opposite hnine
  have hfin : Finite (PositiveEdge L n k j) := by
    have : Finite (Edge L n k j) := hb
    exact Subtype.finite
  let := Fintype.ofFinite (PositiveEdge L n k j)
  have hdim : Module.finrank ℝ ComplexMatrix2.hermitianTraceless = 3 := by
    obtain ⟨e, _⟩ := hP.2.2.1
    exact show Module.finrank ℝ ComplexMatrix2.LieElement = 3 from by
      rw [Module.finrank_eq_card_basis e.toBasis]
      simp
  refine ⟨hfin, Module.Finite.equiv (positiveValuesEquiv hx).symm, ?_, innerProductCore hx,
    fun B B' => ?_⟩
  · rw [(positiveValuesEquiv hx).finrank_eq, Module.finrank_pi_fintype]
    simp [hdim, Nat.card_eq_fintype_card, mul_comm]
  · unfold edgeFormPairing traceFinsumPairing
    rw [finsum_eq_sum_of_fintype]
    show ∑ p, _ =
      ((∑ p, inner ℝ (lieEval B p) (lieEval B' p) : ℝ) : ℂ)
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [restrictToPositiveEdges_eq_toMatrix, restrictToPositiveEdges_eq_toMatrix]
    exact halfTrace_mul_eq_inner (lieEval B p) (lieEval B' p)
end Tower.FiniteSideForms
end YangMills.Construction
end
