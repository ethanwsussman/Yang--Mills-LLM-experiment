import YangMills.Construction.Towers.ExpansionOfTheMoveOnASide
import YangMills.Construction.Towers.IsometriesOnExponentialsAndPlaquettesOfASideProof
import YangMills.Construction.Towers.IsometryOnPairingsAndTheSecondDerivativeOnASide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.SideSymmetryPairingHessian
variable {L n k j : ℕ}
theorem vertex_injective [Finite (Vertex L n k j)]
    {σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hσ : MapsSublatticeOnto k j σ) :
    ∀ x y : Vertex L n k j, σ x = σ y → x = y := by apply _root_.YangMills.Construction.Tower.PeriodicSymmetryAction.vertex_injective_of_mapsOnto <;> assumption
theorem edgePreimage_eq {σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hσ : ∀ x y : Vertex L n k j, σ x = σ y → x = y) {e e' : Edge L n k j}
    (hs : (e'.source : PeriodicLattice.FourTorus L n) = σ e.source)
    (ht : (e'.target : PeriodicLattice.FourTorus L n) = σ e.target) :
    edgePreimage (k := k) (j := j) σ e' = e := by apply _root_.YangMills.Construction.Tower.PeriodicSymmetryAction.edgePreimage_eq <;> assumption
theorem opposite_opposite (e : Edge L n k j) : e.opposite.opposite = e := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
def orientedRep (e : Edge L n k j) : PositiveEdge L n k j :=
  open Classical in
  if h : e.IsPositivelyOriented then ⟨e, h⟩
  else ⟨e.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩
theorem orientedRep_of_pos {e : Edge L n k j} (h : e.IsPositivelyOriented) :
    (orientedRep e : Edge L n k j) = e := by
  simp only [orientedRep, dif_pos h]
theorem orientedRep_of_not_pos {e : Edge L n k j} (h : ¬ e.IsPositivelyOriented) :
    (orientedRep e : Edge L n k j) = e.opposite := by
  simp only [orientedRep, dif_neg h]
theorem orientedRep_edgePreimage_surjective (hL : 1 < L)
    (hdep : -(n : ℤ) < PeriodicLattice.levelDepth k j)
    {σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hσ : ∀ x y : Vertex L n k j, σ x = σ y → x = y) (hE : MapsEdgesOnto k j σ) :
    Function.Surjective fun e : PositiveEdge L n k j =>
      orientedRep (edgePreimage (k := k) (j := j) σ (e : Edge L n k j)) := by
  rintro ⟨e, he⟩
  obtain ⟨d, hs, ht⟩ := hE.1 e
  by_cases hd : d.IsPositivelyOriented
  · refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    change (orientedRep (edgePreimage (k := k) (j := j) σ d) : Edge L n k j) = e
    rw [edgePreimage_eq hσ hs ht, orientedRep_of_pos he]
  · have hd' : d.opposite.IsPositivelyOriented :=
      PeriodicLattice.Bond.opposite_isPositivelyOriented hd
    refine ⟨⟨d.opposite, hd'⟩, Subtype.ext ?_⟩
    change (orientedRep (edgePreimage (k := k) (j := j) σ d.opposite) : Edge L n k j) = e
    have hop : edgePreimage (k := k) (j := j) σ d.opposite = e.opposite :=
      edgePreimage_eq hσ ht hs
    rw [hop, orientedRep_of_not_pos
      (PeriodicLattice.Bond.opposite_not_isPositivelyOriented hL hdep he), opposite_opposite]
theorem halfTrace_tangentEdgeValue_mul {U : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (X₁ X₂ : Edge L n k j → Matrices.ComplexMatrix2) (e : Edge L n k j) :
    Matrices.ComplexMatrix2.halfTrace (tangentEdgeValue U X₁ e * tangentEdgeValue U X₂ e) =
      Matrices.ComplexMatrix2.halfTrace (X₁ (orientedRep e) * X₂ (orientedRep e)) := by
  by_cases h : e.IsPositivelyOriented
  · simp only [tangentEdgeValue, if_pos h, orientedRep_of_pos h]
  · have hop : e.opposite.IsPositivelyOriented :=
      PeriodicLattice.Bond.opposite_isPositivelyOriented h
    have hdet : (U e.opposite).det = 1 := hU.1 e.opposite (mem_univ _)
    simp only [tangentEdgeValue, if_neg h, orientedRep_of_not_pos h]
    generalize U e.opposite = g at hdet
    generalize X₁ e.opposite = P
    generalize X₂ e.opposite = Q
    have hginv : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one)
    have hinvg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one)
    have hinvinv : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one)
    have hprod : -Matrices.ComplexMatrix2.conjugateBy g⁻¹ P *
        -Matrices.ComplexMatrix2.conjugateBy g⁻¹ Q = g⁻¹ * (P * Q * g) := by
      simp only [Matrices.ComplexMatrix2.conjugateBy, hinvinv, neg_mul_neg]
      calc g⁻¹ * P * g * (g⁻¹ * Q * g) = g⁻¹ * P * (g * g⁻¹) * Q * g := by
            simp only [mul_assoc]
        _ = g⁻¹ * (P * Q * g) := by
            rw [hginv, mul_one]
            simp only [mul_assoc]
    rw [hprod]
    have htr : Matrix.trace (g⁻¹ * (P * Q * g)) = Matrix.trace (P * Q) := by
      rw [Matrix.trace_mul_comm, mul_assoc, hginv, mul_one]
    have hhalf : ∀ M : Matrices.ComplexMatrix2,
        Matrices.ComplexMatrix2.halfTrace M = (2 : ℂ)⁻¹ * Matrix.trace M := by
      intro M
      simp [Matrices.ComplexMatrix2.halfTrace, Matrix.trace]
    rw [hhalf, hhalf, htr]
theorem edgeFormPairing_isometryOnTangent (hL : 1 < L)
    (hdep : -(n : ℤ) < PeriodicLattice.levelDepth k j)
    [Finite (PositiveEdge L n k j)]
    {σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hσ : ∀ x y : Vertex L n k j, σ x = σ y → x = y) (hE : MapsEdgesOnto k j σ)
    {U : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (X₁ X₂ : Edge L n k j → Matrices.ComplexMatrix2) :
    edgeFormPairing (isometryOnTangent σ U X₁) (isometryOnTangent σ U X₂) =
      edgeFormPairing X₁ X₂ := by
  have hsurj := orientedRep_edgePreimage_surjective hL hdep hσ hE
  have hinj := (Finite.injective_iff_surjective.mpr hsurj)
  let τ : PositiveEdge L n k j → ℂ := fun e =>
    Matrices.ComplexMatrix2.halfTrace
      (restrictToPositiveEdges X₁ e * restrictToPositiveEdges X₂ e)
  have hterm : ∀ e : PositiveEdge L n k j,
      Matrices.ComplexMatrix2.halfTrace (restrictToPositiveEdges (isometryOnTangent σ U X₁) e *
        restrictToPositiveEdges (isometryOnTangent σ U X₂) e) =
      τ (orientedRep (edgePreimage (k := k) (j := j) σ (e : Edge L n k j))) := by
    intro e
    have hval : ∀ Y : Edge L n k j → Matrices.ComplexMatrix2,
        restrictToPositiveEdges (isometryOnTangent σ U Y) e =
          tangentEdgeValue U Y (edgePreimage (k := k) (j := j) σ (e : Edge L n k j)) := by
      intro Y
      simp only [restrictToPositiveEdges, isometryOnTangent, extendOddly, if_pos e.2]
    rw [hval, hval]
    exact halfTrace_tangentEdgeValue_mul hU X₁ X₂ _
  simp only [edgeFormPairing, traceFinsumPairing]
  exact (finsum_congr hterm).trans (finsum_comp (g := τ) _ ⟨hinj, hsurj⟩)
theorem isometryOnTangent_linear_combination
    (σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (U X₁ X₂ : Edge L n k j → Matrices.ComplexMatrix2) (a b : ℂ) :
    isometryOnTangent σ U (a • X₁ + b • X₂) =
      a • isometryOnTangent σ U X₁ + b • isometryOnTangent σ U X₂ := by
  have hlin : ∀ e : Edge L n k j, tangentEdgeValue U (a • X₁ + b • X₂) e =
      a • tangentEdgeValue U X₁ e + b • tangentEdgeValue U X₂ e := by
    intro e
    by_cases he : e.IsPositivelyOriented
    · simp only [tangentEdgeValue, if_pos he, Pi.add_apply, Pi.smul_apply]
    · simp only [tangentEdgeValue, if_neg he, Pi.add_apply, Pi.smul_apply,
        Matrices.ComplexMatrix2.conjugateBy, mul_add, add_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_neg, neg_add]
  funext e
  by_cases he : e.IsPositivelyOriented
  · simp only [isometryOnTangent, extendOddly, if_pos he, Pi.add_apply, Pi.smul_apply, hlin]
  · simp only [isometryOnTangent, extendOddly, if_neg he, Pi.add_apply, Pi.smul_apply, hlin,
      smul_neg, neg_add]
theorem complexAction_pushField [Finite (Face L n k j)]
    {σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hF : MapsFacesOnto k j σ) {V : Edge L n k j → Matrices.ComplexMatrix2}
    (hV : ∀ p : Face L n k j, (∃! q : Face L n k j, IsImageFace σ p q) ∧
      ∀ q : Face L n k j, IsImageFace σ p q →
        complexFaceTerm (pushField (k := k) (j := j) σ V) q = complexFaceTerm V p) :
    complexAction (pushField (k := k) (j := j) σ V) = complexAction V := by
  have himg : ∀ p : Face L n k j, ∃ q, IsImageFace σ p q := fun p => (hV p).1.exists
  choose ρ hρ using himg
  have hsurj : Function.Surjective ρ := by
    intro q
    obtain ⟨p, hp⟩ := hF.2 q
    exact ⟨p, (hV p).1.unique (hρ p) hp⟩
  have hinj : Function.Injective ρ := Finite.injective_iff_surjective.mpr hsurj
  unfold complexAction
  rw [← finsum_comp _ ⟨hinj, hsurj⟩]
  exact finsum_congr fun p => (hV p).2 _ (hρ p)
theorem statement_holds
    (hExpFaces : Tower.PeriodicSymmetriesActOnExpAndFaces)
    (hTwist : Tower.TwistExpansionOnTorus.Claim)
    (hTower : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hSums : Tower.FaceSums.FacesAndPairings) :
    Statement := by
  intro L n k j hL hn hjk σ U hσ hsub hU X₁ hX₁ X₂ hX₂
  have hLpos : 0 < L := by have := hL.2; omega
  have hLone : 1 < L := by have := hL.2; omega
  have hdep : -(n : ℤ) < PeriodicLattice.levelDepth k j := by
    simp only [PeriodicLattice.levelDepth]
    omega
  obtain ⟨-, hvert, hedgesum, hfacesum⟩ := (hSums L hL k j hjk).1 n hn
  have hfinV : Finite (Vertex L n k j) :=
    Set.finite_univ_iff.mp (hvert univ).2.1
  have hfinE : Finite (PositiveEdge L n k j) :=
    Set.finite_univ_iff.mp (hedgesum univ).2.1
  have hfinF : Finite (Face L n k j) :=
    Set.finite_univ_iff.mp (hfacesum univ).2.1
  have hinj := vertex_injective hsub
  obtain ⟨-, hrest⟩ := (hTower L hLpos hL k).2.2.2.1 n hn j hjk σ hσ hsub
  obtain ⟨-, hedges, hfaces⟩ := hrest j le_rfl
  refine ⟨edgeFormPairing_isometryOnTangent hLone hdep hinj hedges hU X₁ X₂, ?_⟩
  have hsame : ∀ a b : ℂ,
      complexAction (PeriodicLattice.expTwist
          (a • isometryOnTangent σ U X₁ + b • isometryOnTangent σ U X₂)
          (pushField (k := k) (j := j) σ U)) =
        complexAction (PeriodicLattice.expTwist (a • X₁ + b • X₂) U) := by
    intro a b
    have hC : a • X₁ + b • X₂ ∈ complexEdgeForms L n k j :=
      Submodule.add_mem _ (Submodule.smul_mem _ a hX₁) (Submodule.smul_mem _ b hX₂)
    have hW : PeriodicLattice.expTwist (a • X₁ + b • X₂) U ∈
        fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
      have := (hTwist L n k j hL hn hjk U 0 (a • X₁ + b • X₂) hU
        (fun _ => Matrices.ComplexMatrix2.traceless.zero_mem) hC).1 1
      rwa [one_smul] at this
    rw [← isometryOnTangent_linear_combination,
      (hExpFaces L n k j hL hn hjk σ U hσ hsub hU).1 _ hC]
    exact complexAction_pushField hfaces (hExpFaces L n k j hL hn hjk σ _ hσ hsub hW).2
  simp only [complexActionHessian, holLeftSecondDeriv, mixedDirectionalDeriv, hsame]
end YangMills.Construction.Tower.SideSymmetryPairingHessian
end
