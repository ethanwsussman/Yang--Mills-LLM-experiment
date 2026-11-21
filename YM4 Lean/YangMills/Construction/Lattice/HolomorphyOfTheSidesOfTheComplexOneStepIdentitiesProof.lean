import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.CombGaugeRoundACoarsePlaquetteProof
import YangMills.Construction.Lattice.ComplexAverageAtAnImageBondProof
import YangMills.Construction.Lattice.ComplexAverageOnHolomorphicFamilies
import YangMills.Construction.Lattice.EliminationMapOnHolomorphicFamilies
import YangMills.Construction.Lattice.HolomorphyOfTheSidesOfTheComplexOneStepIdentities
import YangMills.Construction.Lattice.LinearisedConstraintOnHolomorphicFamilies
import YangMills.Construction.Lattice.PivotInverseOnHolomorphicFamilies
import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALatticeProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.StepSidesHolomorphy
open Set
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.PeriodicLattice.ComplexTransport
section Closure
variable {ι κ : Type} [Fintype ι] [Fintype κ] {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
  {W : Set (ι ⊕ κ → ComplexMatrix2)} {Φ Ψ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
theorem isHolo_const (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (X : ComplexMatrix2) :
    IsHolomorphicToMatrixEntries b W fun _ => X := (hM ι κ b W hW).1 X
theorem isHolo_coord (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (x : ι ⊕ κ) :
    IsHolomorphicToMatrixEntries b W fun p => p x := (hM ι κ b W hW).2.1 x
theorem isHolo_mul (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    (hΦ : IsHolomorphicToMatrixEntries b W Φ)
    (hΨ : IsHolomorphicToMatrixEntries b W Ψ) :
    IsHolomorphicToMatrixEntries b W fun p => Φ p * Ψ p :=
  (hM ι κ b W hW).2.2.2.1 Φ Ψ hΦ hΨ
theorem isHolo_linearMap (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    (l : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2)
    (hΦ : IsHolomorphicToMatrixEntries b W Φ) :
    IsHolomorphicToMatrixEntries b W fun p => l (Φ p) :=
  (hM ι κ b W hW).2.2.2.2.1 l Φ hΦ
theorem isHolo_inv (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    (hΦ : IsHolomorphicToMatrixEntries b W Φ)
    (hu : ∀ p ∈ W, IsUnit (Φ p).det) : IsHolomorphicToMatrixEntries b W fun p => (Φ p)⁻¹ :=
  (hM ι κ b W hW).2.2.2.2.2.1 Φ hΦ hu
theorem isHolo_mono (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    {W' : Set (ι ⊕ κ → ComplexMatrix2)} (hs : W' ⊆ W)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W')
    (hΦ : IsHolomorphicToMatrixEntries b W Φ) :
    IsHolomorphicToMatrixEntries b W' Φ :=
  (hM ι κ b W hW).2.2.2.2.2.2.2.2.2.1 W' hs hW' Φ hΦ
theorem isHolo_congr (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    (hΦ : IsHolomorphicToMatrixEntries b W Φ)
    (h : EqOn Ψ Φ W) : IsHolomorphicToMatrixEntries b W Ψ :=
  (hM ι κ b W hW).2.2.2.2.2.2.2.2.2.2 Φ Ψ hΦ h
theorem isHolo_neg (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    (hΦ : IsHolomorphicToMatrixEntries b W Φ) :
    IsHolomorphicToMatrixEntries b W fun p => -Φ p :=
  isHolo_congr hM hW (isHolo_linearMap hM hW (-LinearMap.id) hΦ) fun p _ => by simp
theorem isHolo_smul (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (z : ℂ)
    (hΦ : IsHolomorphicToMatrixEntries b W Φ) :
    IsHolomorphicToMatrixEntries b W fun p => z • Φ p :=
  isHolo_congr hM hW (isHolo_linearMap hM hW (z • LinearMap.id) hΦ) fun p _ => by simp
theorem isHolo_conjugateBy (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    (hΦ : IsHolomorphicToMatrixEntries b W Φ)
    (hu : ∀ p ∈ W, IsUnit (Φ p).det) (hΨ : IsHolomorphicToMatrixEntries b W Ψ) :
    IsHolomorphicToMatrixEntries b W fun p => ComplexMatrix2.conjugateBy (Φ p) (Ψ p) :=
  isHolo_mul hM hW (isHolo_mul hM hW hΦ hΨ) (isHolo_inv hM hW hΦ hu)
theorem conjugateBy_mem_traceless (V : ComplexMatrix2) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V A ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
omit [Fintype ι] [Fintype κ] in
theorem det_eq_one_of_mem {p : ι ⊕ κ → ComplexMatrix2} (h : p ∈ GroupLieProduct ι κ) (x : ι) :
    (p (.inl x)).det = 1 := h (.inl x)
omit [Fintype ι] [Fintype κ] in
theorem traceless_of_mem {p : ι ⊕ κ → ComplexMatrix2} (h : p ∈ GroupLieProduct ι κ) (k : κ) :
    p (.inr k) ∈ ComplexMatrix2.traceless := h (.inr k)
theorem isUnit_det_of_eq_one {X : ComplexMatrix2} (h : X.det = 1) : IsUnit X.det := by apply _root_.YangMills.SharedProofs.p11557 <;> assumption
end Closure
theorem opposite_opposite {L m : ℕ} {j : ℤ} (e : Bond L m j) : e.opposite.opposite = e := rfl
section Twisted
variable {L m : ℕ} {j : ℤ} {ι κ : Type} [Fintype ι] [Fintype κ]
  {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
theorem twistedFormValue_of_oriented (σ : FourTorus L m ≃ FourTorus L m)
    (V A : Bond L m j → ComplexMatrix2) (e : Bond L m j)
    (h : (bondPreimage σ e).IsPositivelyOriented) :
    twistedFormValue σ V A e = A (bondPreimage σ e) := by
  unfold twistedFormValue; exact if_pos h
theorem twistedFormValue_of_not_oriented (σ : FourTorus L m ≃ FourTorus L m)
    (V A : Bond L m j → ComplexMatrix2)
    (e : Bond L m j) (h : ¬ (bondPreimage σ e).IsPositivelyOriented) :
    twistedFormValue σ V A e =
      -ComplexMatrix2.conjugateBy (V (bondPreimage σ e).opposite)⁻¹
        (A (bondPreimage σ e).opposite) := by
  unfold twistedFormValue; exact if_neg h
theorem twistedTransportForm_of_oriented (σ : FourTorus L m ≃ FourTorus L m)
    (V A : Bond L m j → ComplexMatrix2) {e : Bond L m j}
    (h : e.IsPositivelyOriented) : twistedTransportForm σ V A e = twistedFormValue σ V A e := by
  unfold twistedTransportForm; exact if_pos h
theorem twistedTransportForm_of_not_oriented (σ : FourTorus L m ≃ FourTorus L m)
    (V A : Bond L m j → ComplexMatrix2) {e : Bond L m j}
    (h : ¬ e.IsPositivelyOriented) :
    twistedTransportForm σ V A e = -twistedFormValue σ V A e.opposite := by
  unfold twistedTransportForm; exact if_neg h
theorem isUnit_det_inv {X : ComplexMatrix2} (h : IsUnit X.det) : IsUnit (X⁻¹).det :=
  Matrix.isUnit_nonsing_inv_det_iff.2 h
theorem isHolo_twistedFormValue (hM : HolomorphyClosureStatement)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    (σ : FourTorus L m ≃ FourTorus L m) (e : Bond L m j)
    {M f : (ι ⊕ κ → ComplexMatrix2) → Bond L m j → ComplexMatrix2}
    (h₁ : (bondPreimage σ e).IsPositivelyOriented →
      IsHolomorphicToMatrixEntries b W fun p => f p (bondPreimage σ e))
    (h₂ : ¬ (bondPreimage σ e).IsPositivelyOriented →
      IsHolomorphicToMatrixEntries b W (fun p => f p (bondPreimage σ e).opposite) ∧
      IsHolomorphicToMatrixEntries b W (fun p => M p (bondPreimage σ e).opposite) ∧
      ∀ p ∈ W, IsUnit (M p (bondPreimage σ e).opposite).det) :
    IsHolomorphicToMatrixEntries b W fun p => twistedFormValue σ (M p) (f p) e := by
  by_cases h : (bondPreimage σ e).IsPositivelyOriented
  · exact isHolo_congr hM hW (h₁ h) fun p _ => twistedFormValue_of_oriented σ _ _ e h
  · obtain ⟨hf, hV, hu⟩ := h₂ h
    exact isHolo_congr hM hW (isHolo_neg hM hW (isHolo_conjugateBy hM hW (isHolo_inv hM hW hV hu)
      (fun p hp => isUnit_det_inv (hu p hp)) hf)) fun p _ =>
        twistedFormValue_of_not_oriented σ _ _ e h
theorem twistedFormValue_mem (σ : FourTorus L m ≃ FourTorus L m) (e : Bond L m j)
    {V f : Bond L m j → ComplexMatrix2}
    (h₁ : (bondPreimage σ e).IsPositivelyOriented →
      f (bondPreimage σ e) ∈ ComplexMatrix2.traceless)
    (h₂ : ¬ (bondPreimage σ e).IsPositivelyOriented →
      f (bondPreimage σ e).opposite ∈ ComplexMatrix2.traceless) :
    twistedFormValue σ V f e ∈ ComplexMatrix2.traceless := by
  by_cases h : (bondPreimage σ e).IsPositivelyOriented
  · rw [twistedFormValue_of_oriented σ _ _ e h]; exact h₁ h
  · rw [twistedFormValue_of_not_oriented σ _ _ e h]
    exact Submodule.neg_mem _ (conjugateBy_mem_traceless _ (h₂ h))
theorem holomorphicForm_twistedTransport (hM : HolomorphyClosureStatement)
    (hX : ∀ e : Bond L m j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (σ : FourTorus L m ≃ FourTorus L m)
    {U A : (ι ⊕ κ → ComplexMatrix2) → Bond L m j → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U)
    (hA : IsHolomorphicBondFormFamily b W A) :
    IsHolomorphicBondFormFamily b W fun p => twistedTransportForm σ (U p) (A p) := by
  have hW := hA.isOpen
  have hunit : ∀ x, ∀ p ∈ W, IsUnit (U p x).det := fun x p hp =>
    isUnit_det_of_eq_one ((hU.isGaugeField p hp).1 x (mem_univ x))
  have hv : ∀ e, IsHolomorphicToMatrixEntries b W fun p => twistedFormValue σ (U p) (A p) e :=
    fun e =>
      isHolo_twistedFormValue hM hW σ e (fun _ => hA.holomorphic _)
        fun _ => ⟨hA.holomorphic _, hU.holomorphic _, hunit _⟩
  have hpos : ∀ e : Bond L m j, ¬ e.IsPositivelyOriented → e.opposite.IsPositivelyOriented :=
    fun e he => by
      rcases hX e with h | h
      · exact absurd h.1 he
      · exact h.1
  have hneg : ∀ e : Bond L m j, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented :=
    fun e he => by
      rcases hX e with h | h
      · exact h.2
      · exact absurd he h.2
  refine ⟨hW, fun p hp => ⟨fun e he => ?_, fun e => ?_⟩, fun e => ?_⟩
  · rw [twistedTransportForm_of_oriented σ _ _ he]
    exact twistedFormValue_mem σ e (fun h => (hA.isBondForm p hp).1 _ h)
      fun h => (hA.isBondForm p hp).1 _ (hpos _ h)
  · by_cases he : e.IsPositivelyOriented
    · rw [twistedTransportForm_of_not_oriented σ _ _ (hneg e he),
        twistedTransportForm_of_oriented σ _ _ he, opposite_opposite]
    · rw [twistedTransportForm_of_oriented σ _ _ (hpos e he),
        twistedTransportForm_of_not_oriented σ _ _ he, neg_neg]
  · by_cases he : e.IsPositivelyOriented
    · exact isHolo_congr hM hW (hv e) fun p _ => twistedTransportForm_of_oriented σ _ _ he
    · exact isHolo_congr hM hW (isHolo_neg hM hW (hv e.opposite)) fun p _ =>
        twistedTransportForm_of_not_oriented σ _ _ he
theorem holomorphicGaugeField_transport (σ : FourTorus L m ≃ FourTorus L m)
    (hr : ∀ e : Bond L m j, bondPreimage σ e.opposite = (bondPreimage σ e).opposite)
    {U : (ι ⊕ κ → ComplexMatrix2) → Bond L m j → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U) :
    IsHolomorphicGaugeFieldFamily b W fun p => transportGaugeField σ (U p) := by
  refine ⟨hU.isOpen, fun p hp => ⟨fun e _ => ?_, fun e _ => ?_⟩, fun e => hU.holomorphic _⟩
  · exact (hU.isGaugeField p hp).1 _ (mem_univ _)
  · show U p (bondPreimage σ e.opposite) = (U p (bondPreimage σ e))⁻¹
    rw [hr]
    exact (hU.isGaugeField p hp).2 _ (mem_univ _)
theorem holomorphicGaugeField_mono (hM : HolomorphyClosureStatement)
    {W' : Set (ι ⊕ κ → ComplexMatrix2)} (hs : W' ⊆ W)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W')
    {U : (ι ⊕ κ → ComplexMatrix2) → Bond L m j → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U) :
    IsHolomorphicGaugeFieldFamily b W' U :=
  ⟨hW', fun p hp => hU.isGaugeField p (hs hp),
    fun e => isHolo_mono hM hU.isOpen hs hW' (hU.holomorphic e)⟩
theorem holomorphicForm_mono (hM : HolomorphyClosureStatement)
    {W' : Set (ι ⊕ κ → ComplexMatrix2)} (hs : W' ⊆ W)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W')
    {A : (ι ⊕ κ → ComplexMatrix2) → Bond L m j → ComplexMatrix2}
    (hA : IsHolomorphicBondFormFamily b W A) :
    IsHolomorphicBondFormFamily b W' A :=
  ⟨hW', fun p hp => hA.isBondForm p (hs hp),
    fun e => isHolo_mono hM hA.isOpen hs hW' (hA.holomorphic e)⟩
end Twisted
section Points
variable {L m : ℕ} {j j' : ℤ} {κ : Type} [Fintype κ]
  {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
theorem gaugeFieldOfPositiveValues_of_mem {ℬ : Set (Bond L m j)}
    (v : PositiveBondOf ℬ → ComplexMatrix2) {e : Bond L m j}
    (h : e ∈ ℬ ∧ e.IsPositivelyOriented) : gaugeFieldOfPositiveValues ℬ v e = v ⟨e, h⟩ := by
  unfold gaugeFieldOfPositiveValues; exact dif_pos h
theorem gaugeFieldOfPositiveValues_of_opposite_mem {ℬ : Set (Bond L m j)}
    (v : PositiveBondOf ℬ → ComplexMatrix2) {e : Bond L m j}
    (h : ¬ (e ∈ ℬ ∧ e.IsPositivelyOriented))
    (h' : e.opposite ∈ ℬ ∧ e.opposite.IsPositivelyOriented) :
    gaugeFieldOfPositiveValues ℬ v e = (v ⟨e.opposite, h'⟩)⁻¹ := by
  unfold gaugeFieldOfPositiveValues; rw [dif_neg h, dif_pos h']
theorem gaugeFieldOfPositiveValues_eq_one {ℬ : Set (Bond L m j)}
    (v : PositiveBondOf ℬ → ComplexMatrix2) {e : Bond L m j}
    (h : ¬ (e ∈ ℬ ∧ e.IsPositivelyOriented))
    (h' : ¬ (e.opposite ∈ ℬ ∧ e.opposite.IsPositivelyOriented)) :
    gaugeFieldOfPositiveValues ℬ v e = 1 := by
  unfold gaugeFieldOfPositiveValues; rw [dif_neg h, dif_neg h']
theorem det_inv_eq_one {X : ComplexMatrix2} (h : X.det = 1) : (X⁻¹).det = 1 := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.det_inv_of_det_eq_one <;> assumption
theorem holomorphicGaugeField_ofPoint (hM : HolomorphyClosureStatement)
    (hX : ∀ e : Bond L m j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (ℬ : Set (Bond L m j))
    [Fintype (PositiveBondOf ℬ)] {W : Set (PositiveBondOf ℬ ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveBondOf ℬ) κ) W)
    (hWP : W ⊆ GroupLieProduct (PositiveBondOf ℬ) κ) :
    IsHolomorphicGaugeFieldFamily b W (gaugeFieldOfPoint ℬ) := by
  refine ⟨hW, fun p hp => ⟨fun e _ => ?_, fun e _ => ?_⟩, fun e => ?_⟩
  · show (gaugeFieldOfPoint ℬ p e).det = 1
    unfold gaugeFieldOfPoint
    by_cases h : e ∈ ℬ ∧ e.IsPositivelyOriented
    · rw [gaugeFieldOfPositiveValues_of_mem _ h]; exact det_eq_one_of_mem (hWP hp) _
    · by_cases h' : e.opposite ∈ ℬ ∧ e.opposite.IsPositivelyOriented
      · rw [gaugeFieldOfPositiveValues_of_opposite_mem _ h h']
        exact det_inv_eq_one (det_eq_one_of_mem (hWP hp) _)
      · rw [gaugeFieldOfPositiveValues_eq_one _ h h']; simp
  · unfold gaugeFieldOfPoint
    by_cases h : e ∈ ℬ ∧ e.IsPositivelyOriented
    · have hne : ¬ (e.opposite ∈ ℬ ∧ e.opposite.IsPositivelyOriented) := fun h' => by
        rcases hX e with h₁ | h₁
        · exact h₁.2 h'.2
        · exact h₁.2 h.2
      rw [gaugeFieldOfPositiveValues_of_opposite_mem _ hne
        (show e.opposite.opposite ∈ ℬ ∧ e.opposite.opposite.IsPositivelyOriented from h),
        gaugeFieldOfPositiveValues_of_mem _ h]
      rfl
    · by_cases h' : e.opposite ∈ ℬ ∧ e.opposite.IsPositivelyOriented
      · rw [gaugeFieldOfPositiveValues_of_mem _ h', gaugeFieldOfPositiveValues_of_opposite_mem _ h h']
        exact (Matrix.nonsing_inv_nonsing_inv _
          (isUnit_det_of_eq_one (det_eq_one_of_mem (hWP hp) _))).symm
      · rw [gaugeFieldOfPositiveValues_eq_one _ h'
          (show ¬ (e.opposite.opposite ∈ ℬ ∧ e.opposite.opposite.IsPositivelyOriented) from h),
          gaugeFieldOfPositiveValues_eq_one _ h h']
        simp
  · by_cases h : e ∈ ℬ ∧ e.IsPositivelyOriented
    · exact isHolo_congr hM hW (isHolo_coord hM hW (.inl ⟨e, h⟩)) fun p _ =>
        gaugeFieldOfPositiveValues_of_mem _ h
    · by_cases h' : e.opposite ∈ ℬ ∧ e.opposite.IsPositivelyOriented
      · exact isHolo_congr hM hW (isHolo_inv hM hW (isHolo_coord hM hW (.inl ⟨e.opposite, h'⟩))
          fun p hp => isUnit_det_of_eq_one (det_eq_one_of_mem (hWP hp) _)) fun p _ =>
            gaugeFieldOfPositiveValues_of_opposite_mem _ h h'
      · exact isHolo_congr hM hW (isHolo_const hM hW 1) fun p _ =>
          gaugeFieldOfPositiveValues_eq_one _ h h'
theorem extendForm_of_mem {Γ : Set (Bond L m j)} (v : SupportBond j' Γ → ComplexMatrix2)
    {e : Bond L m j'}
    (h : e ∈ doubleBlockSupport j' Γ ∧ e.IsPositivelyOriented) : extendForm v e = v ⟨e, h⟩ := by
  unfold extendForm; exact dif_pos h
theorem extendForm_of_opposite_mem {Γ : Set (Bond L m j)} (v : SupportBond j' Γ → ComplexMatrix2)
    {e : Bond L m j'}
    (h : ¬ (e ∈ doubleBlockSupport j' Γ ∧ e.IsPositivelyOriented))
    (h' : e.opposite ∈ doubleBlockSupport j' Γ ∧ e.opposite.IsPositivelyOriented) :
    extendForm v e = -v ⟨e.opposite, h'⟩ := by
  unfold extendForm; rw [dif_neg h, dif_pos h']
theorem extendForm_eq_zero {Γ : Set (Bond L m j)} (v : SupportBond j' Γ → ComplexMatrix2)
    {e : Bond L m j'}
    (h : ¬ (e ∈ doubleBlockSupport j' Γ ∧ e.IsPositivelyOriented))
    (h' : ¬ (e.opposite ∈ doubleBlockSupport j' Γ ∧ e.opposite.IsPositivelyOriented)) :
    extendForm v e = 0 := by
  unfold extendForm; rw [dif_neg h, dif_neg h']
theorem holomorphicForm_extendForm {ι : Type} [Fintype ι] (hM : HolomorphyClosureStatement)
    (hX : ∀ e : Bond L m j', Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    {Γ : Set (Bond L m j)}
    {W : Set (ι ⊕ κ → ComplexMatrix2)} (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    {B : (ι ⊕ κ → ComplexMatrix2) → SupportBond j' Γ → ComplexMatrix2}
    (hB : ∀ x, IsHolomorphicToMatrixEntries b W fun p => B p x)
    (hmem : ∀ p ∈ W, ∀ x, B p x ∈ ComplexMatrix2.traceless) :
    IsHolomorphicBondFormFamily b W fun p => extendForm (B p) := by
  refine ⟨hW, fun p hp => ⟨fun e _ => ?_, fun e => ?_⟩, fun e => ?_⟩
  · by_cases h : e ∈ doubleBlockSupport j' Γ ∧ e.IsPositivelyOriented
    · rw [extendForm_of_mem _ h]; exact hmem p hp _
    · by_cases h' : e.opposite ∈ doubleBlockSupport j' Γ ∧ e.opposite.IsPositivelyOriented
      · rw [extendForm_of_opposite_mem _ h h']; exact Submodule.neg_mem _ (hmem p hp _)
      · rw [extendForm_eq_zero _ h h']; exact Submodule.zero_mem _
  · by_cases h : e ∈ doubleBlockSupport j' Γ ∧ e.IsPositivelyOriented
    · have hne : ¬ (e.opposite ∈ doubleBlockSupport j' Γ ∧ e.opposite.IsPositivelyOriented) :=
        fun h' => by
          rcases hX e with h₁ | h₁
          · exact h₁.2 h'.2
          · exact h₁.2 h.2
      rw [extendForm_of_opposite_mem _ hne
        (show e.opposite.opposite ∈ doubleBlockSupport j' Γ ∧
          e.opposite.opposite.IsPositivelyOriented from h),
        extendForm_of_mem _ h]
      rfl
    · by_cases h' : e.opposite ∈ doubleBlockSupport j' Γ ∧ e.opposite.IsPositivelyOriented
      · rw [extendForm_of_mem _ h', extendForm_of_opposite_mem _ h h', neg_neg]
      · rw [extendForm_eq_zero _ h' (show ¬ (e.opposite.opposite ∈ doubleBlockSupport j' Γ ∧
          e.opposite.opposite.IsPositivelyOriented) from h), extendForm_eq_zero _ h h', neg_zero]
  · by_cases h : e ∈ doubleBlockSupport j' Γ ∧ e.IsPositivelyOriented
    · exact isHolo_congr hM hW (hB ⟨e, h⟩) fun p _ => extendForm_of_mem _ h
    · by_cases h' : e.opposite ∈ doubleBlockSupport j' Γ ∧ e.opposite.IsPositivelyOriented
      · exact isHolo_congr hM hW (isHolo_neg hM hW (hB ⟨e.opposite, h'⟩)) fun p _ =>
          extendForm_of_opposite_mem _ h h'
      · exact isHolo_congr hM hW (isHolo_const hM hW 0) fun p _ => extendForm_eq_zero _ h h'
end Points
section Main
variable {L m K k : ℕ} {σ : FourTorus L m ≃ FourTorus L m} {Γ : Set (BondAtLevel L m K (k + 1))}
structure Hypotheses (σ : FourTorus L m ≃ FourTorus L m) (K k : ℕ)
    (Γ : Set (BondAtLevel L m K (k + 1))) : Prop where
  hM : HolomorphyClosureStatement
  hA : HolomorphicFamilyComplexAverage
  hQ : HolomorphicConstraint.claim
  hP : PivotInverseHolomorphic
  hE : EliminationPreservesHolomorphicForms
  hs : Conventions.IsAdmissibleBlockingFactor L
  hm : 0 < m
  hk : k < K
  fine_xor : ∀ e : BondAtLevel L m K k,
    Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented
  coarse_xor : ∀ e : BondAtLevel L m K (k + 1),
    Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented
  fine_opposite : ∀ e : BondAtLevel L m K k,
    bondPreimage σ e.opposite = (bondPreimage σ e).opposite
  coarse_opposite : ∀ e : BondAtLevel L m K (k + 1),
    bondPreimage σ e.opposite = (bondPreimage σ e).opposite
  coarse_image : ∀ c : BondAtLevel L m K (k + 1), bondPreimage σ (bondImage σ c) = c
  oriented : ∀ c ∈ Γ, c.IsPositivelyOriented
  finite_fine : Finite (BondAtLevel L m K k)
  finite_coarse : Finite (BondAtLevel L m K (k + 1))
theorem bondPreimage_of_orientedImage (D : Hypotheses σ K k Γ) {c c' : BondAtLevel L m K (k + 1)}
    (hc : c.IsPositivelyOriented) (hcc : IsOrientedImage σ c c') :
    ((bondPreimage σ c').IsPositivelyOriented ∧ bondPreimage σ c' = c) ∨
      (¬ (bondPreimage σ c').IsPositivelyOriented ∧ (bondPreimage σ c').opposite = c) := by
  rcases hcc.2 with h | h
  · left
    have e : bondPreimage σ c' = c := by rw [h]; exact D.coarse_image c
    exact ⟨e ▸ hc, e⟩
  · right
    have e : bondPreimage σ c' = c.opposite := by
      rw [h, D.coarse_opposite, D.coarse_image c]
    refine ⟨?_, by rw [e]; rfl⟩
    rw [e]
    rcases D.coarse_xor c with h₁ | h₁
    · exact h₁.2
    · exact absurd hc h₁.2
variable {ι κ : Type} [Fintype ι] [Fintype κ] {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
  {W : Set (ι ⊕ κ → ComplexMatrix2)}
theorem isHolo_twistedFormValue_orientedImage (D : Hypotheses σ K k Γ)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    {M f : (ι ⊕ κ → ComplexMatrix2) → BondAtLevel L m K (k + 1) → ComplexMatrix2}
    {c c' : BondAtLevel L m K (k + 1)}
    (hc : c.IsPositivelyOriented) (hcc : IsOrientedImage σ c c')
    (hf : IsHolomorphicToTraceless b W fun p => f p c)
    (hMh : IsHolomorphicToMatrixEntries b W fun p => M p c)
    (hu : ∀ p ∈ W, IsUnit (M p c).det) :
    IsHolomorphicToTraceless b W fun p => twistedFormValue σ (M p) (f p) c' := by
  rcases bondPreimage_of_orientedImage D hc hcc with ⟨h, e⟩ | ⟨h, e⟩
  · have hval : ∀ p, twistedFormValue σ (M p) (f p) c' = f p c := fun p => by
      rw [twistedFormValue_of_oriented σ _ _ c' h, e]
    refine ⟨fun p hp => ?_, isHolo_congr D.hM hW hf.2 fun p _ => hval p⟩
    show twistedFormValue σ (M p) (f p) c' ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2)
    rw [hval]
    exact hf.1 hp
  · have hval : ∀ p, twistedFormValue σ (M p) (f p) c' =
        -ComplexMatrix2.conjugateBy (M p c)⁻¹ (f p c) := fun p => by
      rw [twistedFormValue_of_not_oriented σ _ _ c' h, e]
    refine ⟨fun p hp => ?_, isHolo_congr D.hM hW (isHolo_neg D.hM hW (isHolo_conjugateBy D.hM hW
      (isHolo_inv D.hM hW hMh hu) (fun p hp => isUnit_det_inv (hu p hp)) hf.2)) fun p _ =>
        hval p⟩
    show twistedFormValue σ (M p) (f p) c' ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2)
    rw [hval]
    exact Submodule.neg_mem _ (conjugateBy_mem_traceless _ (hf.1 hp))
theorem complexBlockAverage_holomorphic (D : Hypotheses σ K k Γ)
    {U : (ι ⊕ κ → ComplexMatrix2) → BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U) {c : BondAtLevel L m K (k + 1)}
    (hc : c.IsPositivelyOriented)
    (h : ∀ p ∈ W, U p ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K k → ComplexMatrix2))) :
    (∀ p ∈ W, IsUnit (complexBlockAverage (U p) c).det) ∧
      IsHolomorphicToMatrixEntries b W fun p => complexBlockAverage (U p) c := by
  obtain ⟨_, h₁, h₂, _⟩ := D.hA L m K k D.hs D.hm D.hk ι κ b W U hU c hc
  have e : {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K k → ComplexMatrix2))} = W := by
    ext p
    exact ⟨fun x => x.1, fun x => ⟨x, h p x⟩⟩
  rw [e] at h₁ h₂
  exact ⟨fun p hp => isUnit_det_of_eq_one (h₁ hp), h₂⟩
theorem constraintMap_holomorphic (D : Hypotheses σ K k Γ)
    {U B : (ι ⊕ κ → ComplexMatrix2) → BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U) (hB : IsHolomorphicBondFormFamily b W B)
    {c : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented)
    (h : ∀ p ∈ W, U p ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K k → ComplexMatrix2)) ∧ ConstraintMapDefined (U p) (B p) c) :
    IsHolomorphicToTraceless b W fun p => constraintMap (U p) (B p) c := by
  obtain ⟨_, _, _, h₁⟩ := D.hA L m K k D.hs D.hm D.hk ι κ b W U hU c hc
  have e : {p | p ∈ W ∧ U p ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K k → ComplexMatrix2)) ∧ ConstraintMapDefined (U p) (B p) c} = W := by
    ext p
    exact ⟨fun x => x.1, fun x => ⟨x, h p x⟩⟩
  have h₂ := (h₁ B hB).2
  rwa [e] at h₂
theorem pivotCoeffInv_holomorphic (D : Hypotheses σ K k Γ)
    {U : (ι ⊕ κ → ComplexMatrix2) → BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U) {c : BondAtLevel L m K (k + 1)}
    (hc : c.IsPositivelyOriented)
    (h : ∀ p ∈ W, U p ∈ (complexAveragingDomainNearOne c :
      Set (BondAtLevel L m K k → ComplexMatrix2)))
    (hi : ∀ p ∈ W, PivotCoeffInvertible (U p) c) {ν : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hν : IsHolomorphicToTraceless b W ν) :
    IsHolomorphicToTraceless b W fun p => pivotCoeffInv (U p) c (ν p) := by
  obtain ⟨_, h₁⟩ := D.hP L m K k D.hs D.hm D.hk ι κ b W U hU c hc h
  have e : {p | p ∈ W ∧ PivotCoeffInvertible (U p) c} = W := by
    ext p
    exact ⟨fun x => x.1, fun x => ⟨x, hi p x⟩⟩
  have h₂ := h₁ ν (by rwa [e])
  rwa [e] at h₂
theorem pivotCorrectionLift_holomorphic (D : Hypotheses σ K k Γ)
    {U : (ι ⊕ κ → ComplexMatrix2) → BondAtLevel L m K k → ComplexMatrix2}
    (hU : IsHolomorphicGaugeFieldFamily b W U) {Γ' : Set (BondAtLevel L m K (k + 1))}
    (hpos : ∀ c ∈ Γ', c.IsPositivelyOriented) (hf : ∀ p ∈ W, ComplexConstraintDefined (U p) Γ')
    (hi : ∀ p ∈ W, ∀ c ∈ Γ', PivotCoeffInvertible (U p) c)
    {ν : (ι ⊕ κ → ComplexMatrix2) → ↥Γ' → ComplexMatrix2}
    (hν : ∀ c, IsHolomorphicToTraceless b W fun p => ν p c)
    (e : SupportBond (levelDepth K k) Γ') :
    IsHolomorphicToTraceless b W fun p => pivotCorrectionLift (U p) Γ' (ν p) e := by
  have hW := hU.isOpen
  by_cases h : ∃ c : ↥Γ', (e : BondAtLevel L m K k) = pivot (c : BondAtLevel L m K (k + 1))
  · have hval : ∀ p, pivotCorrectionLift (U p) Γ' (ν p) e = ((L : ℂ)⁻¹) •
        pivotCoeffInv (U p) (h.choose : BondAtLevel L m K (k + 1)) (ν p h.choose) :=
      fun p => by unfold pivotCorrectionLift; exact dif_pos h
    have h₁ := pivotCoeffInv_holomorphic D hU (hpos _ h.choose.2)
      (fun p hp => hf p hp _ h.choose.2) (fun p hp => hi p hp _ h.choose.2) (hν h.choose)
    refine ⟨fun p hp => ?_, isHolo_congr D.hM hW (isHolo_smul D.hM hW _ h₁.2) fun p _ =>
      hval p⟩
    show pivotCorrectionLift (U p) Γ' (ν p) e ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2)
    rw [hval]
    exact Submodule.smul_mem _ _ (h₁.1 hp)
  · have hval : ∀ p, pivotCorrectionLift (U p) Γ' (ν p) e = 0 :=
      fun p => by unfold pivotCorrectionLift; exact dif_neg h
    refine ⟨fun p _ => ?_, isHolo_congr D.hM hW (isHolo_const D.hM hW 0) fun p _ => hval p⟩
    show pivotCorrectionLift (U p) Γ' (ν p) e ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2)
    rw [hval]
    exact Submodule.zero_mem _
end Main
theorem isRelativelyOpen_sep {E α : Type} [TopologicalSpace E] {P W : Set E} {S : Set α}
    (hS : S.Finite)
    (hW : ComplexMatrix2.IsRelativelyOpen P W) {Q : α → Set E}
    (h : ∀ a ∈ S, ComplexMatrix2.IsRelativelyOpen P (Q a)) :
    ComplexMatrix2.IsRelativelyOpen P {p | p ∈ W ∧ ∀ a ∈ S, p ∈ Q a} := by
  obtain ⟨O, hO, rfl⟩ := hW
  choose! O' hO' using h
  refine ⟨O ∩ ⋂ a ∈ S, O' a, hO.inter (hS.isOpen_biInter fun a ha => (hO' a ha).1), ?_⟩
  ext p
  simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨⟨h₁, fun a ha => ?_⟩, h₂⟩
    have := h₃ a ha
    rw [(hO' a ha).2] at this
    exact this.1
  · rintro ⟨⟨h₁, h₃⟩, h₂⟩
    refine ⟨⟨h₁, h₂⟩, fun a ha => ?_⟩
    rw [(hO' a ha).2]
    exact ⟨h₃ a ha, h₂⟩
section Sides
variable {L m K k : ℕ} {σ : FourTorus L m ≃ FourTorus L m} {Γ : Set (BondAtLevel L m K (k + 1))}
  {κ : Type} [Fintype (SupportBond (levelDepth K k) Γ)] [Fintype κ]
  {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
omit [Fintype (SupportBond (levelDepth K k) Γ)] [Fintype κ] in
theorem oriented_of_mem_orientedImage {c' : BondAtLevel L m K (k + 1)}
    (h : c' ∈ orientedImage σ Γ) : c'.IsPositivelyOriented := by
  obtain ⟨c, _, hc⟩ := h
  exact hc.1
theorem definedPoints_isRelativelyOpen (D : Hypotheses σ K k Γ)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (SupportBond (levelDepth K k) Γ) κ)
      (definedPoints σ (levelDepth K k) Γ κ) := by
  have := D.finite_coarse
  have hΓ : Γ.Finite := Set.toFinite _
  have hΓ' : (orientedImage σ Γ).Finite := Set.toFinite _
  let P : Set (SupportBond (levelDepth K k) Γ ⊕ κ → ComplexMatrix2) :=
    GroupLieProduct (SupportBond (levelDepth K k) Γ) κ
  have hP : ComplexMatrix2.IsRelativelyOpen P P := ⟨univ, isOpen_univ, (univ_inter _).symm⟩
  have hV₀ : IsHolomorphicGaugeFieldFamily b P (fun p => supportGaugeField p) :=
    holomorphicGaugeField_ofPoint D.hM D.fine_xor _ hP subset_rfl
  let S₁ : Set (SupportBond (levelDepth K k) Γ ⊕ κ → ComplexMatrix2) := {p | p ∈ P ∧ ∀ c ∈ Γ, p ∈
    {q | q ∈ P ∧ supportGaugeField q ∈
      (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2))}}
  have hS₁ : ComplexMatrix2.IsRelativelyOpen P S₁ := isRelativelyOpen_sep hΓ hP
    fun c hc => (D.hA L m K k D.hs D.hm D.hk _ κ b _ _ hV₀ c (D.oriented c hc)).1
  have hV₁ := holomorphicGaugeField_mono D.hM (W' := S₁) (fun p hp => hp.1) hS₁ hV₀
  let S₂ : Set (SupportBond (levelDepth K k) Γ ⊕ κ → ComplexMatrix2) := {p | p ∈ S₁ ∧ ∀ c ∈ Γ, p ∈
    {q | q ∈ S₁ ∧ PivotCoeffInvertible (supportGaugeField q) c}}
  have hS₂ : ComplexMatrix2.IsRelativelyOpen P S₂ := isRelativelyOpen_sep hΓ hS₁
    fun c hc => (D.hP L m K k D.hs D.hm D.hk _ κ b _ _ hV₁ c (D.oriented c hc)
      fun p hp => (hp.2 c hc).2).1
  have hV₂ := holomorphicGaugeField_transport σ D.fine_opposite
    (holomorphicGaugeField_mono D.hM (W' := S₂) (fun p hp => hp.1) hS₂ hV₁)
  let S₃ : Set (SupportBond (levelDepth K k) Γ ⊕ κ → ComplexMatrix2) :=
    {p | p ∈ S₂ ∧ ∀ c' ∈ orientedImage σ Γ, p ∈
      {q | q ∈ S₂ ∧ transportGaugeField σ (supportGaugeField q) ∈
        (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → ComplexMatrix2))}}
  have hS₃ : ComplexMatrix2.IsRelativelyOpen P S₃ := isRelativelyOpen_sep hΓ' hS₂
    fun c' hc' => (D.hA L m K k D.hs D.hm D.hk _ κ b _ _ hV₂ c'
      (oriented_of_mem_orientedImage hc')).1
  have hV₃ := holomorphicGaugeField_mono D.hM (W' := S₃) (fun p hp => hp.1) hS₃ hV₂
  let S₄ : Set (SupportBond (levelDepth K k) Γ ⊕ κ → ComplexMatrix2) :=
    {p | p ∈ S₃ ∧ ∀ c' ∈ orientedImage σ Γ, p ∈
      {q | q ∈ S₃ ∧ PivotCoeffInvertible
        (transportGaugeField σ (supportGaugeField q)) c'}}
  have hS₄ : ComplexMatrix2.IsRelativelyOpen P S₄ := isRelativelyOpen_sep hΓ' hS₃
    fun c' hc' => (D.hP L m K k D.hs D.hm D.hk _ κ b _ _ hV₃ c'
      (oriented_of_mem_orientedImage hc') fun p hp => (hp.2 c' hc').2).1
  have e : definedPoints σ (levelDepth K k) Γ κ = S₄ := by
    ext p
    constructor
    · rintro ⟨h₀, h₁, h₂⟩
      have q₁ : p ∈ S₁ := ⟨h₀, fun c hc => ⟨h₀, h₁.defined c hc⟩⟩
      have q₂ : p ∈ S₂ := ⟨q₁, fun c hc => ⟨q₁, h₁.pivot_invertible c hc⟩⟩
      have q₃ : p ∈ S₃ := ⟨q₂, fun c hc => ⟨q₂, h₂.defined c hc⟩⟩
      exact ⟨q₃, fun c hc => ⟨q₃, h₂.pivot_invertible c hc⟩⟩
    · rintro ⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩
      exact ⟨h₀, ⟨fun c hc => (h₁ c hc).2, fun c hc => (h₂ c hc).2⟩,
        ⟨fun c hc => (h₃ c hc).2, fun c hc => (h₄ c hc).2⟩⟩
  rw [e]
  exact hS₄
theorem holomorphicGaugeField_support (D : Hypotheses σ K k Γ) :
    IsHolomorphicGaugeFieldFamily b (definedPoints σ (levelDepth K k) Γ κ)
      (fun p => supportGaugeField p) :=
  holomorphicGaugeField_ofPoint D.hM D.fine_xor _ (definedPoints_isRelativelyOpen D b)
    fun _ hp => hp.1
theorem holomorphicGaugeField_transportSupport (D : Hypotheses σ K k Γ) :
    IsHolomorphicGaugeFieldFamily b (definedPoints σ (levelDepth K k) Γ κ)
      (fun p => transportGaugeField σ (supportGaugeField p)) :=
  holomorphicGaugeField_transport σ D.fine_opposite (holomorphicGaugeField_support D)
theorem linearizedConstraint_sides (D : Hypotheses σ K k Γ)
    {A : (SupportBond (levelDepth K k) Γ ⊕ κ → ComplexMatrix2) →
      BondAtLevel L m K k → ComplexMatrix2}
    (hA : IsHolomorphicBondFormFamily b (definedPoints σ (levelDepth K k) Γ κ) A)
    {c' : BondAtLevel L m K (k + 1)} (hc' : c' ∈ orientedImage σ Γ) :
    IsHolomorphicToTraceless b (definedPoints σ (levelDepth K k) Γ κ)
        (fun p => linearizedConstraint (transportGaugeField σ (supportGaugeField p))
          (twistedTransportForm σ (supportGaugeField p) (A p)) c') ∧
      IsHolomorphicToTraceless b (definedPoints σ (levelDepth K k) Γ κ)
        (fun p => twistedTransportForm σ (complexBlockAverage (supportGaugeField p))
          (linearizedConstraint (supportGaugeField p) (A p)) c') := by
  obtain ⟨c, hc, hcc⟩ := hc'
  have hV := holomorphicGaugeField_support (b := b) (κ := κ) D
  have hS := holomorphicGaugeField_transportSupport (b := b) (κ := κ) D
  have hO : ∀ p ∈ definedPoints σ (levelDepth K k) Γ κ, supportGaugeField p ∈
      (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) :=
    fun p hp => hp.2.1.defined c hc
  have hO' : ∀ p ∈ definedPoints σ (levelDepth K k) Γ κ,
      transportGaugeField σ (supportGaugeField p) ∈
        (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → ComplexMatrix2)) :=
    fun p hp => hp.2.2.defined c' ⟨c, hc, hcc⟩
  obtain ⟨hu, hav⟩ := complexBlockAverage_holomorphic D hV (D.oriented c hc) hO
  constructor
  · exact (D.hQ L m K k D.hs D.hm D.hk _ κ b _ _ hS c' hcc.1 hO').1 _
      (holomorphicForm_twistedTransport D.hM D.fine_xor σ hV hA)
  · have e : (fun p => twistedTransportForm σ (complexBlockAverage (supportGaugeField p))
        (linearizedConstraint (supportGaugeField p) (A p)) c') = fun p =>
        twistedFormValue σ (complexBlockAverage (supportGaugeField p))
          (linearizedConstraint (supportGaugeField p) (A p)) c' :=
      funext fun p => twistedTransportForm_of_oriented σ _ _ hcc.1
    rw [e]
    exact isHolo_twistedFormValue_orientedImage D (definedPoints_isRelativelyOpen D b)
      (D.oriented c hc) hcc
      ((D.hQ L m K k D.hs D.hm D.hk _ κ b _ _ hV c (D.oriented c hc) hO).1 _ hA) hav hu
theorem constraintBilinear_sides (D : Hypotheses σ K k Γ)
    {A₁ A₂ : (SupportBond (levelDepth K k) Γ ⊕ κ → ComplexMatrix2) →
      BondAtLevel L m K k → ComplexMatrix2}
    (hA₁ : IsHolomorphicBondFormFamily b (definedPoints σ (levelDepth K k) Γ κ) A₁)
    (hA₂ : IsHolomorphicBondFormFamily b (definedPoints σ (levelDepth K k) Γ κ) A₂)
    {c' : BondAtLevel L m K (k + 1)} (hc' : c' ∈ orientedImage σ Γ) :
    IsHolomorphicToTraceless b (definedPoints σ (levelDepth K k) Γ κ)
        (fun p => constraintBilinear
          (transportGaugeField σ (supportGaugeField p))
          (twistedTransportForm σ (supportGaugeField p) (A₁ p))
          (twistedTransportForm σ (supportGaugeField p) (A₂ p)) c') ∧
      IsHolomorphicToTraceless b (definedPoints σ (levelDepth K k) Γ κ)
        (fun p => twistedFormValue σ (complexBlockAverage (supportGaugeField p))
          (constraintBilinear (supportGaugeField p) (A₁ p) (A₂ p)) c') := by
  obtain ⟨c, hc, hcc⟩ := hc'
  have hV := holomorphicGaugeField_support (b := b) (κ := κ) D
  have hS := holomorphicGaugeField_transportSupport (b := b) (κ := κ) D
  have hO : ∀ p ∈ definedPoints σ (levelDepth K k) Γ κ, supportGaugeField p ∈
      (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) :=
    fun p hp => hp.2.1.defined c hc
  have hO' : ∀ p ∈ definedPoints σ (levelDepth K k) Γ κ,
      transportGaugeField σ (supportGaugeField p) ∈
        (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → ComplexMatrix2)) :=
    fun p hp => hp.2.2.defined c' ⟨c, hc, hcc⟩
  obtain ⟨hu, hav⟩ := complexBlockAverage_holomorphic D hV (D.oriented c hc) hO
  constructor
  · exact (D.hQ L m K k D.hs D.hm D.hk _ κ b _ _ hS c' hcc.1 hO').2 _ _
      (holomorphicForm_twistedTransport D.hM D.fine_xor σ hV hA₁)
      (holomorphicForm_twistedTransport D.hM D.fine_xor σ hV hA₂)
  · exact isHolo_twistedFormValue_orientedImage D (definedPoints_isRelativelyOpen D b)
      (D.oriented c hc) hcc
      ((D.hQ L m K k D.hs D.hm D.hk _ κ b _ _ hV c (D.oriented c hc) hO).2 _ _ hA₁ hA₂) hav hu
theorem isHolo_formValue {ι : Type} [Fintype ι] {j : ℤ} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {A : (ι ⊕ κ → ComplexMatrix2) → Bond L m j → ComplexMatrix2}
    (hA : IsHolomorphicBondFormFamily b W A) {e : Bond L m j}
    (he : e.IsPositivelyOriented) : IsHolomorphicToTraceless b W fun p => A p e :=
  ⟨fun p hp => (hA.isBondForm p hp).1 e he, hA.holomorphic e⟩
theorem eliminate_sides (D : Hypotheses σ K k Γ)
    {A : (SupportBond (levelDepth K k) Γ ⊕ κ → ComplexMatrix2) →
      BondAtLevel L m K k → ComplexMatrix2}
    (hA : IsHolomorphicBondFormFamily b (definedPoints σ (levelDepth K k) Γ κ) A)
    (e : SupportBond (levelDepth K k) (orientedImage σ Γ)) :
    IsHolomorphicToTraceless b (definedPoints σ (levelDepth K k) Γ κ)
        (fun p => eliminate (transportGaugeField σ (supportGaugeField p))
          (orientedImage σ Γ)
          (twistedTransportForm σ (supportGaugeField p) (A p)) e.1) ∧
      IsHolomorphicToTraceless b (definedPoints σ (levelDepth K k) Γ κ)
        (fun p => twistedTransportForm σ (supportGaugeField p)
          (eliminate (supportGaugeField p) Γ (A p)) e.1) := by
  have hV := holomorphicGaugeField_support (b := b) (κ := κ) D
  have hS := holomorphicGaugeField_transportSupport (b := b) (κ := κ) D
  have h₁ := D.hE L m K k D.hs D.hm D.hk _ κ b _ _ hS (orientedImage σ Γ)
    (fun _ h => oriented_of_mem_orientedImage h) (fun p hp => hp.2.2.defined)
    (fun p hp => hp.2.2.pivot_invertible) _
    (holomorphicForm_twistedTransport D.hM D.fine_xor σ hV hA)
  have h₂ := D.hE L m K k D.hs D.hm D.hk _ κ b _ _ hV Γ D.oriented
    (fun p hp => hp.2.1.defined) (fun p hp => hp.2.1.pivot_invertible) _ hA
  exact ⟨isHolo_formValue h₁ e.2.2,
    isHolo_formValue (holomorphicForm_twistedTransport D.hM D.fine_xor σ hV h₂) e.2.2⟩
theorem pivotCorrectionLift_sides (D : Hypotheses σ K k Γ)
    {ν : (SupportBond (levelDepth K k) Γ ⊕ κ → ComplexMatrix2) → ↥Γ → ComplexMatrix2}
    (hν : ∀ c, IsHolomorphicToTraceless b (definedPoints σ (levelDepth K k) Γ κ)
      fun p => ν p c)
    (e : SupportBond (levelDepth K k) (orientedImage σ Γ)) :
    IsHolomorphicToTraceless b (definedPoints σ (levelDepth K k) Γ κ)
        (fun p => pivotCorrectionLift (transportGaugeField σ (supportGaugeField p))
          (orientedImage σ Γ)
          (twistedTransportCoarse σ (complexBlockAverage (supportGaugeField p)) (ν p)) e) ∧
      IsHolomorphicToTraceless b (definedPoints σ (levelDepth K k) Γ κ)
        (fun p => twistedTransportSupportForm σ (supportGaugeField p)
          (pivotCorrectionLift (supportGaugeField p) Γ (ν p)) e) := by
  have hV := holomorphicGaugeField_support (b := b) (κ := κ) D
  have hS := holomorphicGaugeField_transportSupport (b := b) (κ := κ) D
  have hW := definedPoints_isRelativelyOpen (κ := κ) D b
  have hO : ∀ c ∈ Γ, ∀ p ∈ definedPoints σ (levelDepth K k) Γ κ, supportGaugeField p ∈
      (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) :=
    fun c hc p hp => hp.2.1.defined c hc
  constructor
  · refine pivotCorrectionLift_holomorphic D hS (fun _ h => oriented_of_mem_orientedImage h)
      (fun p hp => hp.2.2.defined) (fun p hp => hp.2.2.pivot_invertible) (fun c' => ?_) e
    obtain ⟨c, hc, hcc⟩ := c'.2
    obtain ⟨hu, hav⟩ := complexBlockAverage_holomorphic D hV (D.oriented c hc) (hO c hc)
    have h₁ : (fun p => Function.extend Subtype.val (ν p) 0 c) = fun p => ν p ⟨c, hc⟩ :=
      funext fun p => Subtype.val_injective.extend_apply (ν p) 0 ⟨c, hc⟩
    exact isHolo_twistedFormValue_orientedImage D hW
      (f := fun p => Function.extend Subtype.val (ν p) 0)
      (D.oriented c hc) hcc (by rw [h₁]; exact hν _) hav hu
  · have hl := fun x => pivotCorrectionLift_holomorphic D hV D.oriented
      (fun p hp => hp.2.1.defined) (fun p hp => hp.2.1.pivot_invertible) hν x
    exact isHolo_formValue (holomorphicForm_twistedTransport D.hM D.fine_xor σ hV
      (holomorphicForm_extendForm D.hM D.fine_xor hW (fun x => (hl x).2)
        fun p hp x => (hl x).1 hp)) e.2.2
theorem constraintMap_sides (D : Hypotheses σ K k Γ)
    {A : (SupportBond (levelDepth K k) Γ ⊕ κ → ComplexMatrix2) →
      BondAtLevel L m K k → ComplexMatrix2}
    (hA : IsHolomorphicBondFormFamily b (definedPoints σ (levelDepth K k) Γ κ) A)
    {c c' : BondAtLevel L m K (k + 1)} (hc : c ∈ Γ) (hcc : IsOrientedImage σ c c') :
    IsHolomorphicToTraceless b
        {p | p ∈ definedPoints σ (levelDepth K k) Γ κ ∧
          ConstraintMapDefined (supportGaugeField p) (A p) c ∧
          ConstraintMapDefined (transportGaugeField σ (supportGaugeField p))
            (twistedTransportForm σ (supportGaugeField p) (A p)) c'}
        (fun p => constraintMap (transportGaugeField σ (supportGaugeField p))
          (twistedTransportForm σ (supportGaugeField p) (A p)) c') ∧
      IsHolomorphicToTraceless b
        {p | p ∈ definedPoints σ (levelDepth K k) Γ κ ∧
          ConstraintMapDefined (supportGaugeField p) (A p) c ∧
          ConstraintMapDefined (transportGaugeField σ (supportGaugeField p))
            (twistedTransportForm σ (supportGaugeField p) (A p)) c'}
        (fun p => twistedFormValue σ (complexBlockAverage (supportGaugeField p))
          (constraintMap (supportGaugeField p) (A p)) c') := by
  have hV := holomorphicGaugeField_support (b := b) (κ := κ) D
  have hS := holomorphicGaugeField_transportSupport (b := b) (κ := κ) D
  have hA' := holomorphicForm_twistedTransport D.hM D.fine_xor σ hV hA
  have hpos := D.oriented c hc
  have hO₁ := ((D.hA L m K k D.hs D.hm D.hk _ κ b _ _ hV c hpos).2.2.2 A hA).1
  have hO₂ := ((D.hA L m K k D.hs D.hm D.hk _ κ b _ _
    (holomorphicGaugeField_mono D.hM (fun p hp => hp.1) hO₁ hS) c' hcc.1).2.2.2 _
    (holomorphicForm_mono D.hM (fun p hp => hp.1) hO₁ hA')).1
  have e : {p | p ∈ definedPoints σ (levelDepth K k) Γ κ ∧
      ConstraintMapDefined (supportGaugeField p) (A p) c ∧
      ConstraintMapDefined (transportGaugeField σ (supportGaugeField p))
        (twistedTransportForm σ (supportGaugeField p) (A p)) c'} =
      {p | p ∈ {p | p ∈ definedPoints σ (levelDepth K k) Γ κ ∧ supportGaugeField p ∈
          (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
          ConstraintMapDefined (supportGaugeField p) (A p) c} ∧
        transportGaugeField σ (supportGaugeField p) ∈
          (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
        ConstraintMapDefined (transportGaugeField σ (supportGaugeField p))
          (twistedTransportForm σ (supportGaugeField p) (A p)) c'} := by
    ext p
    constructor
    · rintro ⟨h₀, h₁, h₂⟩
      exact ⟨⟨h₀, h₀.2.1.defined c hc, h₁⟩, h₀.2.2.defined c' ⟨c, hc, hcc⟩, h₂⟩
    · rintro ⟨⟨h₀, _, h₁⟩, _, h₂⟩
      exact ⟨h₀, h₁, h₂⟩
  rw [e]
  have hsub : ∀ p ∈ {p | p ∈ {p | p ∈ definedPoints σ (levelDepth K k) Γ κ ∧
      supportGaugeField p ∈
        (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
      ConstraintMapDefined (supportGaugeField p) (A p) c} ∧
      transportGaugeField σ (supportGaugeField p) ∈
        (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
      ConstraintMapDefined (transportGaugeField σ (supportGaugeField p))
        (twistedTransportForm σ (supportGaugeField p) (A p)) c'},
      p ∈ definedPoints σ (levelDepth K k) Γ κ := fun p hp => hp.1.1
  have hV₁ := holomorphicGaugeField_mono D.hM hsub hO₂ hV
  have hS₁ := holomorphicGaugeField_mono D.hM hsub hO₂ hS
  have hA₁ := holomorphicForm_mono D.hM hsub hO₂ hA
  have hA₁' := holomorphicForm_mono D.hM hsub hO₂ hA'
  obtain ⟨hu, hav⟩ := complexBlockAverage_holomorphic D hV₁ hpos fun p hp => hp.1.2.1
  exact ⟨constraintMap_holomorphic D hS₁ hA₁' hcc.1 fun p hp => hp.2,
    isHolo_twistedFormValue_orientedImage D hO₂ hpos hcc
      (constraintMap_holomorphic D hV₁ hA₁ hpos fun p hp => hp.1.2) hav hu⟩
theorem holomorphicForm_algebraPart (D : Hypotheses σ K k Γ) :
    IsHolomorphicBondFormFamily b
      (definedPoints σ (levelDepth K k) Γ (SupportBond (levelDepth K k) Γ))
      fun p => extendForm (algebraPartOfPoint p) :=
  holomorphicForm_extendForm D.hM D.fine_xor (definedPoints_isRelativelyOpen D b)
    (fun x => isHolo_coord D.hM (definedPoints_isRelativelyOpen D b) (.inr x))
    fun _ hp x => traceless_of_mem hp.1 x
theorem holomorphicForm_firstAlgebraPart (D : Hypotheses σ K k Γ) :
    IsHolomorphicBondFormFamily b
      (definedPoints σ (levelDepth K k) Γ
        (SupportBond (levelDepth K k) Γ ⊕ SupportBond (levelDepth K k) Γ))
      fun p => extendForm (firstAlgebraPart p) :=
  holomorphicForm_extendForm D.hM D.fine_xor (definedPoints_isRelativelyOpen D b)
    (fun x => isHolo_coord D.hM (definedPoints_isRelativelyOpen D b) (Sum.inr (Sum.inl x)))
    fun _ hp x => traceless_of_mem hp.1 (Sum.inl x)
theorem holomorphicForm_secondAlgebraPart (D : Hypotheses σ K k Γ) :
    IsHolomorphicBondFormFamily b
      (definedPoints σ (levelDepth K k) Γ
        (SupportBond (levelDepth K k) Γ ⊕ SupportBond (levelDepth K k) Γ))
      fun p => extendForm (secondAlgebraPart p) :=
  holomorphicForm_extendForm D.hM D.fine_xor (definedPoints_isRelativelyOpen D b)
    (fun x => isHolo_coord D.hM (definedPoints_isRelativelyOpen D b) (Sum.inr (Sum.inr x)))
    fun _ hp x => traceless_of_mem hp.1 (Sum.inr x)
end Sides
theorem stepSides_holomorphic {L m K k : ℕ} {σ : FourTorus L m ≃ FourTorus L m}
    {Γ : Set (BondAtLevel L m K (k + 1))}
    (D : Hypotheses σ K k Γ) : StepSidesHolomorphic σ Γ := by
  have := D.finite_fine
  have := D.finite_coarse
  let _ : Fintype (SupportBond (levelDepth K k) Γ) := Fintype.ofFinite _
  let _ : Fintype ↥Γ := Fintype.ofFinite _
  refine ⟨fun c' hc' => ⟨inferInstance, inferInstance, fun b => ?_⟩,
    fun c hc c' hcc => ⟨inferInstance, inferInstance, fun b => ?_⟩,
    fun e => ⟨inferInstance, inferInstance, fun b => ?_⟩,
    fun e => ⟨inferInstance, inferInstance, fun b => ?_⟩,
    fun c' hc' => ⟨inferInstance, inferInstance, fun b => ?_⟩⟩
  · exact linearizedConstraint_sides D (holomorphicForm_algebraPart D) hc'
  · exact constraintMap_sides D (holomorphicForm_algebraPart D) hc hcc
  · exact eliminate_sides D (holomorphicForm_algebraPart D) e
  · refine pivotCorrectionLift_sides D (ν := fun p => algebraPartOfPoint p) (fun c => ?_) e
    exact ⟨fun _ hp => traceless_of_mem hp.1 c,
      isHolo_coord D.hM (definedPoints_isRelativelyOpen D b) (.inr c)⟩
  · exact constraintBilinear_sides D (holomorphicForm_firstAlgebraPart D)
      (holomorphicForm_secondAlgebraPart D) hc'
theorem symm_mem_latticeIsometries (hG : LatticeIsometryGroupActionStatement) {L m : ℕ}
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) :
    σ.symm ∈ latticeIsometries L m i := by
  obtain ⟨H, hH⟩ := (hG L m i hs hm hi).1.1
  have h1 : σ ∈ H := by
    have : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    exact this
  have h2 : σ⁻¹ ∈ H := H.inv_mem h1
  have h3 : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := h2
  rw [hH] at h3
  exact h3
theorem bondPreimage_facts (hG : LatticeIsometryGroupActionStatement) {L m : ℕ}
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) {j : ℤ} (hj : i ≤ j) :
    (∀ e : Bond L m j, bondPreimage σ e.opposite = (bondPreimage σ e).opposite) ∧
      ∀ c : Bond L m j, bondPreimage σ (bondImage σ c) = c := by
  have E := ((hG L m i hs hm hi).2.2.2.2 σ hσ j hj).1.2.2.2.1
  have E' := ((hG L m i hs hm hi).2.2.2.2 σ.symm
    (symm_mem_latticeIsometries hG hs hm hi hσ) j hj).1.2.2.2.1
  have p : ∀ e : Bond L m j, ((bondPreimage σ e).source : FourTorus L m) = σ.symm e.source ∧
      ((bondPreimage σ e).target : FourTorus L m) = σ.symm e.target := E'
  constructor
  · intro e
    have q := p e
    have q' := p e.opposite
    apply Bond.ext <;> apply Subtype.ext
    · exact q'.1.trans q.2.symm
    · exact q'.2.trans q.1.symm
  · intro c
    have e := E c
    have q := p (bondImage σ c)
    apply Bond.ext <;> apply Subtype.ext
    · rw [q.1, e.1]; simp
    · rw [q.2, e.2]; simp
theorem finite_bond {L : ℕ} (hL : 0 < L) (m : ℕ) (j : ℤ) : Finite (Bond L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.CoarsePlaquetteGauge.bond_finite <;> assumption
theorem holomorphyOfStepIdentitySides (hM : HolomorphyClosureStatement)
    (hA : HolomorphicFamilyComplexAverage)
    (hQ : HolomorphicConstraint.claim)
    (hP : PivotInverseHolomorphic)
    (hE : EliminationPreservesHolomorphicForms)
    (hX : BondOrientationDichotomy)
    (hG : LatticeIsometryGroupActionStatement) : HolomorphyOfStepIdentitySides := by
  intro L m i σ hs hm hi hσ K k hk hiK Γ hΓ
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hs.2
  have hd₁ : -(m : ℤ) < levelDepth K (k + 1) := by
    simp only [levelDepth]; push_cast; omega
  have hd₀ : -(m : ℤ) < levelDepth K k := by
    simp only [levelDepth]; omega
  have hi₀ : i ≤ levelDepth K k := by
    simp only [levelDepth] at hiK ⊢; push_cast at hiK; omega
  exact stepSides_holomorphic
    { hM := hM, hA := hA, hQ := hQ, hP := hP, hE := hE, hs := hs, hm := hm, hk := hk
      fine_xor := hX L m hs hm _ hd₀
      coarse_xor := hX L m hs hm _ hd₁
      fine_opposite := (bondPreimage_facts hG hs hm hi hσ hi₀).1
      coarse_opposite := (bondPreimage_facts hG hs hm hi hσ hiK).1
      coarse_image := (bondPreimage_facts hG hs hm hi hσ hiK).2
      oriented := hΓ
      finite_fine := finite_bond hL m _
      finite_coarse := finite_bond hL m _ }
end YangMills.Construction.PeriodicLattice.StepSidesHolomorphy
