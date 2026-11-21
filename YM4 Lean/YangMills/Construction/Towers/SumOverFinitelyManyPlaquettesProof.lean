import YangMills.Construction.Lattice.DomainsOfTheTwoSchemesProof
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSetsProof
import YangMills.Construction.Towers.SumOverFinitelyManyPlaquettes
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
open YangMills.Construction.Matrices.GroupLieProduct
noncomputable section
namespace YangMills.Construction.Tower.FaceSum
variable {B P : Type}
def faceTermPoly : List Matrices.ComplexMatrix2 → ℂ
  | [X₁, X₂, X₃, X₄] => 1 - (1 / 2) * Matrices.ComplexMatrix2.fullTrace (X₁ * X₂ * X₃.adjugate * X₄.adjugate)
  | _ => 0
theorem inv_eq_adjugate_of_det_eq_one {X : Matrices.ComplexMatrix2} (h : X.det = 1) :
    X⁻¹ = X.adjugate := by apply _root_.YangMills.SharedProofs.p104891 <;> assumption
theorem faceTermPoly_eq_faceTerm : ∀ (l : List Matrices.ComplexMatrix2), (∀ X ∈ l, X.det = 1) →
    faceTermPoly l = faceTerm l
  | [X₁, X₂, X₃, X₄], h => by
    simp only [faceTermPoly, faceTerm]
    rw [inv_eq_adjugate_of_det_eq_one (h X₃ (by simp)),
      inv_eq_adjugate_of_det_eq_one (h X₄ (by simp))]
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _, _ => rfl
theorem differentiable_faceTermPoly {N : ℕ}
    {A₁ A₂ A₃ A₄ : Coordinates.ComplexCoordinates N → Matrices.ComplexMatrix2}
    (h₁ : ∀ r s, Differentiable ℂ fun z => A₁ z r s)
    (h₂ : ∀ r s, Differentiable ℂ fun z => A₂ z r s)
    (h₃ : ∀ r s, Differentiable ℂ fun z => A₃ z r s)
    (h₄ : ∀ r s, Differentiable ℂ fun z => A₄ z r s) :
    Differentiable ℂ fun z => faceTermPoly [A₁ z, A₂ z, A₃ z, A₄ z] := by
  have a11 := h₁ 1 1
  have b11 := h₂ 1 1
  have c11 := h₃ 1 1
  have d11 := h₄ 1 1
  simp only [faceTermPoly, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  fun_prop
def faceSumPoly (edges : P → List B) (F : Finset B) (Ω : Finset P)
    (q : F ⊕ Empty → Matrices.ComplexMatrix2) : ℂ :=
  ∑ p ∈ Ω, faceTermPoly ((edges p).map (extendByOne F fun b => q (.inl b)))
def piEntryEquiv {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n) :
    Fin (Coordinates.ComplexCoordinates.productDim
        fun _ : Fin n => Coordinates.ComplexCoordinates.Component.matrix) ≃
      ρ × Fin 4 :=
  (finSigmaFinEquiv (m := n) (n := fun _ => 4)).symm.trans
    ((Equiv.sigmaEquivProd (Fin n) (Fin 4)).trans (Equiv.prodCongr ν.symm (Equiv.refl _)))
theorem matrixPiEquiv_apply {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n)
    (X : ρ → Matrices.ComplexMatrix2)
    (i : Fin (Coordinates.ComplexCoordinates.productDim
      fun _ : Fin n => Coordinates.ComplexCoordinates.Component.matrix)) :
    matrixPiEquiv ν X i =
      Coordinates.ComplexCoordinates.matrixEquiv (X (piEntryEquiv ν i).1) (piEntryEquiv ν i).2 :=
  rfl
theorem matrixPiEquiv_symm_apply {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n) (z) (i : ρ) (r s : Fin 2) :
    (matrixPiEquiv ν).symm z i r s =
      z ((piEntryEquiv ν).symm (i, Coordinates.ComplexCoordinates.entryIndex (r, s))) := by
  have h := matrixPiEquiv_apply ν ((matrixPiEquiv ν).symm z)
    ((piEntryEquiv ν).symm (i, Coordinates.ComplexCoordinates.entryIndex (r, s)))
  simp only [Equiv.apply_symm_apply] at h
  rw [h]
  simp [Coordinates.ComplexCoordinates.matrixEquiv]
theorem differentiable_extendByOne_entry {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n)
    (F : Finset B) (ι : F → ρ) (b : B) (r s : Fin 2) :
    Differentiable ℂ fun z : Coordinates.ComplexCoordinates
        (Coordinates.ComplexCoordinates.productDim
          fun _ : Fin n => Coordinates.ComplexCoordinates.Component.matrix) =>
      extendByOne F (fun c => (matrixPiEquiv ν).symm z (ι c)) b r s := by
  by_cases hb : b ∈ F
  · simp only [extendByOne, dif_pos hb, matrixPiEquiv_symm_apply]
    fun_prop
  · simp only [extendByOne, dif_neg hb]
    fun_prop
theorem differentiable_faceTermPoly_map {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n) (F : Finset B)
    (ι : F → ρ) (l : List B) :
    Differentiable ℂ fun z : Coordinates.ComplexCoordinates
        (Coordinates.ComplexCoordinates.productDim
          fun _ : Fin n => Coordinates.ComplexCoordinates.Component.matrix) =>
      faceTermPoly (l.map (extendByOne F fun c => (matrixPiEquiv ν).symm z (ι c))) := by
  match l with
  | [b₁, b₂, b₃, b₄] =>
    exact differentiable_faceTermPoly
      (fun r s => differentiable_extendByOne_entry ν F ι b₁ r s)
      (fun r s => differentiable_extendByOne_entry ν F ι b₂ r s)
      (fun r s => differentiable_extendByOne_entry ν F ι b₃ r s)
      (fun r s => differentiable_extendByOne_entry ν F ι b₄ r s)
  | [] => exact differentiable_const _
  | [_] => exact differentiable_const _
  | [_, _] => exact differentiable_const _
  | [_, _, _] => exact differentiable_const _
  | _ :: _ :: _ :: _ :: _ :: _ => exact differentiable_const _
theorem faceSumPoly_isHolomorphicVia (edges : P → List B) (F : Finset B) (Ω : Finset P)
    {n : ℕ} (ν : F ⊕ Empty ≃ Fin n) :
    Coordinates.ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν)
      (Equiv.funUnique (Fin 1) ℂ).symm univ (faceSumPoly edges F Ω) := by
  have hD : Differentiable ℂ fun z => faceSumPoly edges F Ω
      ((matrixPiEquiv ν).symm z) := by
    unfold faceSumPoly
    exact Differentiable.fun_sum fun p _ => differentiable_faceTermPoly_map ν F Sum.inl (edges p)
  refine ⟨?_, ?_, fun a _ j => Eventually.of_forall fun ζ => differentiableAt_pi.2 fun _ => ?_⟩
  · rw [image_univ, Equiv.range_eq_univ]
    exact isOpen_univ
  · exact (continuous_pi fun _ => hD.continuous).continuousOn
  · refine DifferentiableAt.comp (𝕜 := ℂ) (g := fun z => faceSumPoly edges F Ω
      ((matrixPiEquiv ν).symm z)) ζ hD.differentiableAt ?_
    fun_prop
theorem isHolomorphicIn_congr {N N' : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {f g : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn O f)
    (hc : ∀ z ∈ O, g z = f z) : Coordinates.ComplexCoordinates.IsHolomorphicIn O g := by apply _root_.YangMills.SharedProofs.p63802 <;> assumption
theorem isHolomorphicToCoords_congr {ι κ E : Type} [Fintype ι] [Fintype κ] {l : ℕ}
    {β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless}
    {e : E ≃ Coordinates.ComplexCoordinates l}
    {W : Set (ι ⊕ κ → Matrices.ComplexMatrix2)} {Φ Φ' : (ι ⊕ κ → Matrices.ComplexMatrix2) → E}
    (h : IsHolomorphicToCoords β e W Φ) (hc : ∀ p ∈ W, Φ' p = Φ p) :
    IsHolomorphicToCoords β e W Φ' := by
  refine ⟨h.1, h.2.1.congr fun p hp => congrArg e (hc p hp), fun p hp => ?_⟩
  obtain ⟨O, h0, hO, hH⟩ := h.2.2 p hp
  refine ⟨O, h0, hO, hH.1, fun ν => isHolomorphicIn_congr (hH.2 ν) fun z hz => ?_⟩
  exact congrArg e (hc _ (hO _ hz))
theorem image_unimodularPi {σ : Type} :
    asGroupFactors '' unimodularPi σ = Matrices.GroupLieProduct σ Empty := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩ (s | e)
    · exact hx s
    · exact e.elim
  · intro hp
    refine ⟨fun s => p (.inl s), fun s => hp (.inl s), ?_⟩
    funext s
    rcases s with s | e
    · rfl
    · exact e.elim
theorem det_extendByOne {F : Finset B} {X : F → Matrices.ComplexMatrix2}
    (hX : X ∈ unimodularPi F) (b : B) :
    (extendByOne F X b).det = 1 := by
  by_cases hb : b ∈ F
  · simp only [extendByOne, dif_pos hb]
    exact hX ⟨b, hb⟩
  · simp only [extendByOne, dif_neg hb]
    exact Matrix.det_one
theorem faceSumPoly_asGroupFactors (edges : P → List B) (F : Finset B) (Ω : Finset P)
    {X : F → Matrices.ComplexMatrix2} (hX : X ∈ unimodularPi F) :
    faceSumPoly edges F Ω (asGroupFactors X) = faceSumOfFamily edges F Ω X := by
  refine Finset.sum_congr rfl fun p _ => faceTermPoly_eq_faceTerm _ fun Y hY => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hY
  exact det_extendByOne hX b
theorem isHolomorphicOnGroupPower_of_expChartTheory
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (edges : P → List B) (F : Finset B) (Ω : Finset P) :
    IsHolomorphicOnGroupPower edges F Ω := by
  refine ⟨fun X hXF b => ?_, ⟨univ, isOpen_univ, (univ_inter _).symm⟩, fun β => ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).2
      (by rw [show (X b).det = 1 from hXF b]; exact isUnit_one)
  · have hR : Matrices.GroupLieProduct.ExpChartHolomorphy.ProductRestrictionHolomorphy F Empty :=
      (hX.2.2.2.1 F Empty).2.2
    have hT := faceSumPoly_isHolomorphicVia edges F Ω (Fintype.equivFin (F ⊕ Empty))
    have h' := (hR ℂ 1 (Fintype.card (F ⊕ Empty)) (Equiv.funUnique (Fin 1) ℂ).symm
      (Fintype.equivFin (F ⊕ Empty)) univ (faceSumPoly edges F Ω) hT).2 β
    rw [univ_inter, ← image_unimodularPi] at h'
    refine isHolomorphicToCoords_congr h' ?_
    rintro _ ⟨X, hXF, rfl⟩
    exact (faceSumPoly_asGroupFactors edges F Ω hXF).symm
theorem faceSumOfFamily_eq_faceSum (edges : P → List B) (F : Finset B) (Ω : Finset P)
    (hΩ : ∀ p ∈ Ω, ∀ b ∈ edges p, b ∈ F) (U : B → Matrices.ComplexMatrix2) :
    faceSumOfFamily edges F Ω (fun b : F => U b) = faceSum edges Ω U := by
  refine Finset.sum_congr rfl fun p hp => congrArg faceTerm ?_
  refine List.map_congr_left fun b hb => ?_
  simp only [extendByOne, dif_pos (hΩ p hp b hb)]
theorem agreesAtField_of_mem (edges : P → List B) (F : Finset B) (Ω : Finset P)
    (hΩ : ∀ p ∈ Ω, ∀ b ∈ edges p, b ∈ F) {U : B → Matrices.ComplexMatrix2}
    (hU : ∀ b, U b ∈ PeriodicLattice.complexGaugeGroup) : AgreesAtField edges F Ω U :=
  ⟨fun b => hU b, faceSumOfFamily_eq_faceSum edges F Ω hΩ U⟩
theorem holomorphy_statement_of_expChartTheory
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) :
    holomorphy_statement := by
  intro L _ k j _
  refine ⟨fun n _ F _ _ Ω hΩ => ⟨isHolomorphicOnGroupPower_of_expChartTheory hX _ F Ω, fun U hU =>
    agreesAtField_of_mem _ F Ω hΩ fun b => hU.1 b (mem_univ b)⟩, ?_⟩
  intro F hF Ω hΩ
  have hH := isHolomorphicOnGroupPower_of_expChartTheory hX FullSpace.faceEdges F Ω
  have hV : ∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      AgreesAtField FullSpace.faceEdges F Ω U :=
    fun U hU => agreesAtField_of_mem _ F Ω hΩ hU.1
  have hW : ∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      FullSpace.IsLocalPresentation PeriodicLattice.complexGaugeGroup
        (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
        (faceSum FullSpace.faceEdges Ω) U F
        (FullSpace.edgeProduct PeriodicLattice.complexGaugeGroup F)
        (faceSumOfFamily FullSpace.faceEdges F Ω) :=
    fun U hU => ⟨hF, ⟨univ, isOpen_univ, (univ_inter _).symm⟩, (hV U hU).1,
      fun U' hU' _ => ((hV U' hU').2).symm⟩
  refine ⟨hH, hV, ⟨subset_rfl, fun _ hU _ _ => ⟨1, one_pos, fun U' hU' _ _ => hU'⟩⟩, hW,
    fun β => ⟨subset_rfl, fun U hU => ⟨F, FullSpace.edgeProduct PeriodicLattice.complexGaugeGroup F,
      faceSumOfFamily FullSpace.faceEdges F Ω, hW U hU, hH.2.2 β⟩⟩⟩
end YangMills.Construction.Tower.FaceSum
end
