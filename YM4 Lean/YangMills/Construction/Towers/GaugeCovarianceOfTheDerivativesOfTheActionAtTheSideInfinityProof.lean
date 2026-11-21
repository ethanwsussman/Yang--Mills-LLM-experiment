import YangMills.Construction.Towers.DerivativesOfTheActionOnFinitePlaquetteSetsAtTheSideInfinity
import YangMills.Construction.Towers.ExpansionOfTheMoveAtTheSideInfinity
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesAtTheSideInfinityProof
import YangMills.Construction.Towers.GaugeCovarianceOfTheDerivativesOfTheActionAtTheSideInfinity
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ActionDerivativeCovariance
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.FullSpace.ActionDerivsOnFiniteFaces
open YangMills.Construction.Tower.FaceEdgeFinsets.Unbounded (facesMeeting facesMeetingWithBase)
theorem isUnit_det_of_eq_one {V : ComplexMatrix2} (h : V.det = 1) : IsUnit V.det := by apply _root_.YangMills.SharedProofs.p11557 <;> assumption
theorem isUnit_of_det_eq_one {V : ComplexMatrix2} (h : V.det = 1) : IsUnit V := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.isUnit_of_det_eq_one <;> assumption
theorem det_inv_of_det_eq_one {V : ComplexMatrix2} (h : V.det = 1) : (V⁻¹).det = 1 := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.det_inv_of_det_eq_one <;> assumption
theorem conjugateBy_smul (V X : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy V (c • X) = c • ComplexMatrix2.conjugateBy V X := by
  simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
theorem conjugateBy_ne_zero_iff {V X : ComplexMatrix2} (hV : V.det = 1) :
    ComplexMatrix2.conjugateBy V X ≠ 0 ↔ X ≠ 0 := by
  have hi : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_det_of_eq_one hV)
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · calc X = (V⁻¹ * V) * X * (V⁻¹ * V) := by rw [hi, one_mul, mul_one]
      _ = V⁻¹ * ComplexMatrix2.conjugateBy V X * V := by
          simp only [ComplexMatrix2.conjugateBy, mul_assoc]
      _ = 0 := by rw [h, mul_zero, zero_mul]
  · simp only [ComplexMatrix2.conjugateBy, h, mul_zero, zero_mul]
theorem matExp_conjugateBy {V : ComplexMatrix2} (X : ComplexMatrix2) (hV : V.det = 1) :
    ComplexMatrix2.matExp (Complex.I • ComplexMatrix2.conjugateBy V X) =
      V * ComplexMatrix2.matExp (Complex.I • X) * V⁻¹ := by
  have e : Complex.I • ComplexMatrix2.conjugateBy V X = V * (Complex.I • X) * V⁻¹ := by
    simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact Matrix.exp_conj _ _ (isUnit_of_det_eq_one hV)
section Directions
variable {α : Type*} {φ ψ : (α → ComplexMatrix2) → ℂ}
theorem directionalDeriv_congr {B C : α → ComplexMatrix2} (h : ∀ t : ℂ, φ (t • C) = ψ (t • B)) :
    directionalDeriv ℂ φ C = directionalDeriv ℂ ψ B := by
  have e : (fun t : ℂ => φ (algebraMap ℂ ℂ t • C)) = fun t : ℂ => ψ (algebraMap ℂ ℂ t • B) :=
    funext fun t => h _
  unfold directionalDeriv
  rw [e]
theorem mixedDirectionalDeriv_congr {B B' C C' : α → ComplexMatrix2}
    (h : ∀ s t : ℂ, φ (s • C + t • C') = ψ (s • B + t • B')) :
    mixedDirectionalDeriv ℂ φ C C' = mixedDirectionalDeriv ℂ ψ B B' := by
  have e : ∀ s : ℂ, (fun t : ℂ => φ (algebraMap ℂ ℂ s • C + algebraMap ℂ ℂ t • C')) =
      fun t : ℂ => ψ (algebraMap ℂ ℂ s • B + algebraMap ℂ ℂ t • B') :=
    fun s => funext fun t => h _ _
  unfold mixedDirectionalDeriv
  simp only [e]
end Directions
section OneLattice
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem extendOddly_of_pos (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
theorem extendOddly_of_not_pos (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    extendOddly f b = -f b.opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.extendOddly_of_not_pos <;> assumption
theorem adjointForm_of_pos (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) :
    adjointForm u B b = ComplexMatrix2.conjugateBy (u b.initial) (B b) :=
  extendOddly_of_pos _ hb
theorem adjointForm_of_not_pos (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : ¬ b.IsPositivelyOriented) :
    adjointForm u B b = -ComplexMatrix2.conjugateBy (u b.opposite.initial) (B b.opposite) :=
  extendOddly_of_not_pos _ hb
theorem adjointForm_add (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B B' : InfiniteLattice.Link a → ComplexMatrix2) :
    adjointForm u (B + B') = adjointForm u B + adjointForm u B' := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.adjointForm_add <;> assumption
theorem adjointForm_smul (u : InfiniteLattice.LatticePoint a → ComplexMatrix2) (c : ℂ)
    (B : InfiniteLattice.Link a → ComplexMatrix2) :
    adjointForm u (c • B) = c • adjointForm u B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.smul_apply, adjointForm_of_pos _ _ hb, conjugateBy_smul]
  · simp only [Pi.smul_apply, adjointForm_of_not_pos _ _ hb, conjugateBy_smul, smul_neg]
theorem adjointForm_mem (ha : 0 < a) {u : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    (hu : ∀ x, (u x).det = 1) {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms a) : adjointForm u B ∈ complexEdgeForms a := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.adjointForm_mem <;> assumption
theorem isFieldIn_gaugeAct {U : InfiniteLattice.Link a → ComplexMatrix2}
    {u : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    (hU : IsFieldIn PeriodicLattice.complexGaugeGroup U) (hu : ∀ x, (u x).det = 1) :
    IsFieldIn PeriodicLattice.complexGaugeGroup (gaugeAct u U) := by
  refine ⟨fun b => ?_, fun b => ?_⟩
  · change (u b.initial * U b * (u b.terminal)⁻¹).det = 1
    have h : (U b).det = 1 := hU.1 b
    rw [Matrix.det_mul, Matrix.det_mul, h, hu, det_inv_of_det_eq_one (hu _), one_mul, one_mul]
  · change u b.terminal * U b.opposite * (u b.initial)⁻¹ =
      (u b.initial * U b * (u b.terminal)⁻¹)⁻¹
    rw [hU.2 b, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_eq_one (hu _)), mul_assoc]
theorem expTwist_gaugeAct_of_pos (C U : InfiniteLattice.Link a → ComplexMatrix2)
    {u : InfiniteLattice.LatticePoint a → ComplexMatrix2} (hu : ∀ x, (u x).det = 1)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    expTwist (adjointForm u C) (gaugeAct u U) b = gaugeAct u (expTwist C U) b := by
  have hi : (u b.initial)⁻¹ * u b.initial = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_det_of_eq_one (hu _))
  have e₁ : expTwist (adjointForm u C) (gaugeAct u U) b =
      ComplexMatrix2.matExp (Complex.I • adjointForm u C b) * gaugeAct u U b := by
    unfold expTwist
    exact if_pos hb
  have e₂ : expTwist C U b = ComplexMatrix2.matExp (Complex.I • C b) * U b := by
    unfold expTwist
    exact if_pos hb
  rw [e₁, adjointForm_of_pos _ _ hb, matExp_conjugateBy _ (hu _)]
  change _ * (u b.initial * U b * (u b.terminal)⁻¹) =
    u b.initial * expTwist C U b * (u b.terminal)⁻¹
  rw [e₂]
  calc u b.initial * ComplexMatrix2.matExp (Complex.I • C b) * (u b.initial)⁻¹ *
        (u b.initial * U b * (u b.terminal)⁻¹)
      = u b.initial * ComplexMatrix2.matExp (Complex.I • C b) *
          ((u b.initial)⁻¹ * u b.initial) * U b * (u b.terminal)⁻¹ := by
        simp only [mul_assoc]
    _ = u b.initial * (ComplexMatrix2.matExp (Complex.I • C b) * U b) *
          (u b.terminal)⁻¹ := by
        rw [hi, mul_one]
        simp only [mul_assoc]
theorem ext_of_pos {W W' : InfiniteLattice.Link a → ComplexMatrix2}
    (r : ∀ b : InfiniteLattice.Link a, W b.opposite = (W b)⁻¹)
    (r' : ∀ b : InfiniteLattice.Link a, W' b.opposite = (W' b)⁻¹)
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → W b = W' b) : W = W' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    have e : b.opposite.opposite = b := rfl
    rw [← e, r, r', h _ hr]
end OneLattice
theorem meshAt_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
section Level
variable {L k j : ℕ}
theorem edgeSupport_adjointForm {u : Vertex L k j → ComplexMatrix2} (hu : ∀ x, (u x).det = 1)
    (B : Edge L k j → ComplexMatrix2) : edgeSupport (adjointForm u B) = edgeSupport B := by
  ext b
  refine and_congr_right fun hb => ?_
  rw [adjointForm_of_pos _ _ hb]
  exact conjugateBy_ne_zero_iff (hu _)
theorem actionAtExpTwist_adjointForm (hsp : 0 < meshAt L k j)
    (hG : FullSpace.LeftChartAlgebra.GaugeCovariance L k j)
    (hE : FullSpace.LeftChartAlgebra.TwistExpansion L k j)
    (Ω : Set (Face L k j)) {U : Edge L k j → ComplexMatrix2} {u : Vertex L k j → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hu : ∀ x, u x ∈ PeriodicLattice.complexGaugeGroup) {C : Edge L k j → ComplexMatrix2}
    (hC : C ∈ complexEdgeForms (meshAt L k j)) :
    actionAtExpTwist Ω (gaugeAct u U) (adjointForm u C) = actionAtExpTwist Ω U C := by
  have hd : ∀ x, (u x).det = 1 := hu
  have hUu : gaugeAct u U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    isFieldIn_gaugeAct hU hd
  have hex : ∀ {V : Edge L k j → ComplexMatrix2} {D : Edge L k j → ComplexMatrix2},
      V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
      D ∈ complexEdgeForms (meshAt L k j) →
      expTwist D V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by
    intro V D hV hD
    have h := (hE V 0 D hV (fun _ => ComplexMatrix2.traceless.zero_mem) hD).1 1
    rwa [one_smul] at h
  have hfield : expTwist (adjointForm u C) (gaugeAct u U) = gaugeAct u (expTwist C U) :=
    ext_of_pos (hex hUu (adjointForm_mem hsp hd hC)).2
      (isFieldIn_gaugeAct (hex hU hC) hd).2 fun b hb => expTwist_gaugeAct_of_pos C U hd hb
  unfold actionAtExpTwist faceTermSum
  rw [hfield]
  exact finsum_mem_congr rfl fun p _ => ((hG _ u (hex hU hC) hu).2 p).2
theorem derivativeCovariance_of_level (hD : ActionDerivsOnFiniteFaces.OnLevel L k j)
    (hG : FullSpace.LeftChartAlgebra.GaugeCovariance L k j)
    (hE : FullSpace.LeftChartAlgebra.TwistExpansion L k j)
    (hF : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j)
    (hsp : 0 < meshAt L k j) : FullSpace.LeftChartAlgebra.DerivativeCovariance L k j := by
  intro U u B B' hU hu hB hB' hBf hB'f
  have hd : ∀ x, (u x).det = 1 := hu
  have hUu : gaugeAct u U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    isFieldIn_gaugeAct hU hd
  have hAB := adjointForm_mem hsp hd hB
  have hAB' := adjointForm_mem hsp hd hB'
  have hs := edgeSupport_adjointForm hd B
  have hs' := edgeSupport_adjointForm hd B'
  obtain ⟨-, hfin, -⟩ := hF
  obtain ⟨-, -, hΩf, hΩn⟩ := hfin (edgeSupport B ∪ edgeSupport B') (hBf.union hB'f) (by
    rintro b (h | h) <;> exact h.1)
  have hsub : facesMeeting (edgeSupport B ∪ edgeSupport B') ⊆
      facesMeetingWithBase (edgeSupport B ∪ edgeSupport B') := subset_union_left
  have h₁ := (hD U hU _ hΩf hΩn).1 B B' hB hB' hBf hB'f hsub
  have h₂ := (hD _ hUu _ hΩf hΩn).1 (adjointForm u B) (adjointForm u B') hAB hAB'
    (by unfold HasFiniteEdgeSupport; rw [hs]; exact hBf)
    (by unfold HasFiniteEdgeSupport; rw [hs']; exact hB'f)
    (by rw [hs, hs']; exact hsub)
  have hφ := fun (C : Edge L k j → ComplexMatrix2) (hC : C ∈ complexEdgeForms (meshAt L k j)) =>
    actionAtExpTwist_adjointForm hsp hG hE
      (facesMeetingWithBase (edgeSupport B ∪ edgeSupport B')) hU hu hC
  refine ⟨?_, ?_⟩
  · rw [h₁.1, h₂.1]
    refine directionalDeriv_congr fun t => ?_
    rw [← adjointForm_smul, hφ _ ((complexEdgeForms _).smul_mem _ hB)]
  · rw [h₁.2, h₂.2]
    refine mixedDirectionalDeriv_congr fun s t => ?_
    rw [← adjointForm_smul, ← adjointForm_smul, ← adjointForm_add,
      hφ _ ((complexEdgeForms _).add_mem ((complexEdgeForms _).smul_mem _ hB)
        ((complexEdgeForms _).smul_mem _ hB'))]
end Level
theorem holds
    (hD : ActionDerivsOnFiniteFaces.Claim)
    (hG : Tower.LeftChartAlgebra.GaugeConditionsInfiniteSide)
    (hE : Tower.FullSpaceTwistExpansionClaim)
    (hF : Tower.FaceEdgeFinsets.FacesAndEdgesFinite) : ActionDerivativeCovariance.Claim :=
  fun L k j hL hj =>
    derivativeCovariance_of_level (hD L k j hL hj) (hG L k j hL hj).1 (hE L k j hL hj)
      ((hF L hL k j hj).2) (meshAt_pos hL k j)
end YangMills.Construction.Tower.FullSpace.ActionDerivativeCovariance
end
