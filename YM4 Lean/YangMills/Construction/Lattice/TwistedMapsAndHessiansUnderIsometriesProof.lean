import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomyProof
import YangMills.Construction.Lattice.IteratesOfTheTwoSchemesProof
import YangMills.Construction.Lattice.AverageOfAConfigurationTrivialInsideTwoBlocksProof
import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.BondsAndSpacesOfASeparatedSequence
import YangMills.Construction.Lattice.CovarianceOfComplexActions
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActionsProof
import YangMills.Construction.Lattice.MeanSchemeIsTheAveragingMapOnSmallConfigurationsProof
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometries
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import YangMills.Construction.Towers.WritingsOfAChainInTheLeftChartProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
namespace TwistedTransport
variable {L m : ℕ} {j : ℤ}
theorem det_eq_one_of_mem {V : ComplexMatrix2} (hV : V ∈ complexGaugeGroup) : V.det = 1 := hV
theorem isUnit_det_of_mem {V : ComplexMatrix2} (hV : V ∈ complexGaugeGroup) : IsUnit V.det := by apply _root_.YangMills.Construction.Tower.FullSpace.ChainRule.isUnit_det_of_complex <;> assumption
theorem mul_inv_of_mem {V : ComplexMatrix2} (hV : V ∈ complexGaugeGroup) : V * V⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p13806 <;> assumption
theorem inv_mul_of_mem {V : ComplexMatrix2} (hV : V ∈ complexGaugeGroup) : V⁻¹ * V = 1 := by apply _root_.YangMills.DeltaSharedProofs.p40097 <;> assumption
theorem inv_inv_of_mem {V : ComplexMatrix2} (hV : V ∈ complexGaugeGroup) : V⁻¹⁻¹ = V := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
theorem inv_mem_gaugeGroup {V : ComplexMatrix2} (hV : V ∈ complexGaugeGroup) :
    V⁻¹ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
theorem conjugateBy_add (V A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (A + B) =
      ComplexMatrix2.conjugateBy V A + ComplexMatrix2.conjugateBy V B := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_neg (V A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (-A) = -ComplexMatrix2.conjugateBy V A := by
  simp [ComplexMatrix2.conjugateBy]
theorem conjugateBy_zero (V : ComplexMatrix2) : ComplexMatrix2.conjugateBy V 0 = 0 := by
  simp [ComplexMatrix2.conjugateBy]
theorem conjugateBy_smul (V A : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy V (c • A) = c • ComplexMatrix2.conjugateBy V A := by
  simp [ComplexMatrix2.conjugateBy]
theorem fullTrace_conjugateBy {V : ComplexMatrix2} (hV : V ∈ complexGaugeGroup) (A : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy V A) = ComplexMatrix2.fullTrace A := by
  unfold ComplexMatrix2.conjugateBy ComplexMatrix2.fullTrace
  rw [Matrix.trace_mul_comm, ← mul_assoc, inv_mul_of_mem hV, one_mul]
theorem conjugateBy_mem {V : ComplexMatrix2} (hV : V ∈ complexGaugeGroup) {A : ComplexMatrix2}
    (hA : A ∈ complexLieAlgebra) : ComplexMatrix2.conjugateBy V A ∈ complexLieAlgebra := by
  change ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy V A) = 0
  rw [fullTrace_conjugateBy hV]
  exact hA
theorem conjugateBy_conjugateBy_inv {V : ComplexMatrix2} (hV : V ∈ complexGaugeGroup)
    (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (ComplexMatrix2.conjugateBy V⁻¹ A) = A := by
  unfold ComplexMatrix2.conjugateBy
  rw [inv_inv_of_mem hV]
  calc V * (V⁻¹ * A * V) * V⁻¹ = (V * V⁻¹) * A * (V * V⁻¹) := by
        simp only [mul_assoc]
    _ = A := by rw [mul_inv_of_mem hV, one_mul, mul_one]
theorem halfTracePairing_conjugateBy {V : ComplexMatrix2} (hV : V ∈ complexGaugeGroup)
    (A B : ComplexMatrix2) :
    halfTracePairing (ComplexMatrix2.conjugateBy V A) (ComplexMatrix2.conjugateBy V B) =
      halfTracePairing A B := by
  have e : ComplexMatrix2.conjugateBy V A * ComplexMatrix2.conjugateBy V B =
      ComplexMatrix2.conjugateBy V (A * B) := by
    unfold ComplexMatrix2.conjugateBy
    calc V * A * V⁻¹ * (V * B * V⁻¹) = V * A * (V⁻¹ * V) * B * V⁻¹ := by
          simp only [mul_assoc]
      _ = V * (A * B) * V⁻¹ := by rw [inv_mul_of_mem hV, mul_one]; simp only [mul_assoc]
  unfold halfTracePairing ComplexMatrix2.halfTrace
  rw [e, fullTrace_conjugateBy hV]
theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem matExp_mem_gaugeGroup {A : ComplexMatrix2} (hA : A ∈ complexLieAlgebra) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ complexGaugeGroup := by
  have : ComplexMatrix2.fullTrace (Complex.I • A) = 0 := by
    have h : ComplexMatrix2.fullTrace A = 0 := hA
    simp [ComplexMatrix2.fullTrace, Matrix.trace_smul] at h ⊢
    exact h
  exact SpinHarmonics.det_matExp_of_trace_eq_zero this
theorem mul_mem_gaugeGroup {V W : ComplexMatrix2} (hV : V ∈ complexGaugeGroup)
    (hW : W ∈ complexGaugeGroup) : V * W ∈ complexGaugeGroup := by apply _root_.YangMills.SharedProofs.p592 <;> assumption
structure PullbackData (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop where
  preimage_image : ∀ b : Bond L m j, bondPreimage σ (bondImage σ b) = b
  image_preimage : ∀ b : Bond L m j, bondImage σ (bondPreimage σ b) = b
  preimage_opposite : ∀ b : Bond L m j, bondPreimage σ b.opposite = (bondPreimage σ b).opposite
theorem PullbackData.of_preservesCells {σ : FourTorus L m ≃ FourTorus L m}
    (h : PreservesCells σ j) (h' : PreservesCells σ.symm j) : PullbackData σ j := by
  have key : ∀ (τ : FourTorus L m ≃ FourTorus L m), PreservesCells τ j →
      PreservesCells τ.symm j →
      ∀ b : Bond L m j, bondImage τ.symm (bondImage τ b) = b := by
    intro τ c c' b
    apply Bond.ext
    · apply Subtype.ext
      rw [(c'.2.2.2.1 _).1, c'.1, (c.2.2.2.1 _).1, c.1, Equiv.symm_apply_apply]
    · apply Subtype.ext
      rw [(c'.2.2.2.1 _).2, c'.1, (c.2.2.2.1 _).2, c.1, Equiv.symm_apply_apply]
  exact ⟨fun b => key σ h h' b, fun b => key σ.symm h' h b, fun b => h'.2.2.2.2.1 b⟩
theorem PullbackData.symm {σ : FourTorus L m ≃ FourTorus L m} (h : PullbackData σ j)
    (hr : ∀ b : Bond L m j, bondImage σ b.opposite = (bondImage σ b).opposite) :
    PullbackData σ.symm j :=
  ⟨fun b => h.image_preimage b, fun b => h.preimage_image b, hr⟩
theorem PullbackData.image_opposite {σ : FourTorus L m ≃ FourTorus L m} (h : PullbackData σ j)
    (b : Bond L m j) : bondImage σ b.opposite = (bondImage σ b).opposite := by
  have e : bondPreimage σ (bondImage σ b.opposite) =
      bondPreimage σ (bondImage σ b).opposite := by
    rw [h.preimage_image, h.preimage_opposite, h.preimage_image]
  have := congrArg (bondImage σ) e
  rwa [h.image_preimage, h.image_preimage] at this
theorem opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := Bond.ext rfl rfl
theorem mem_bondSetImage_iff {σ : FourTorus L m ≃ FourTorus L m} (h : PullbackData σ j)
    {ℬ : Set (Bond L m j)} {b : Bond L m j} :
    b ∈ bondSetTransport σ ℬ ↔ bondPreimage σ b ∈ ℬ := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    rwa [h.preimage_image]
  · intro hb
    exact ⟨_, hb, h.image_preimage b⟩
theorem bondSetImage_reversalClosed {σ : FourTorus L m ≃ FourTorus L m} (h : PullbackData σ j)
    {ℬ : Set (Bond L m j)} (hℬ : IsReversalClosed ℬ) :
    IsReversalClosed (bondSetTransport σ ℬ) := by
  intro b hb
  rw [mem_bondSetImage_iff h] at hb ⊢
  rw [h.preimage_opposite]
  exact hℬ _ hb
theorem transport_isGaugeField {σ : FourTorus L m ≃ FourTorus L m} (h : PullbackData σ j)
    {𝒢 : Set ComplexMatrix2} {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField 𝒢 ℬ U) :
    IsGaugeField 𝒢 (bondSetTransport σ ℬ) (transportGaugeField σ U) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · exact hU.1 _ ((mem_bondSetImage_iff h).1 hb)
  · change U (bondPreimage σ b.opposite) = (U (bondPreimage σ b))⁻¹
    rw [h.preimage_opposite]
    exact hU.2 _ ((mem_bondSetImage_iff h).1 hb)
theorem transport_symm_transport {σ : FourTorus L m ≃ FourTorus L m} (h : PullbackData σ j)
    (U : Bond L m j → ComplexMatrix2) :
    transportGaugeField σ.symm (transportGaugeField σ U) = U := by
  funext b
  change U (bondPreimage σ (bondImage σ b)) = U b
  rw [h.preimage_image]
theorem bondSetImage_symm_image {σ : FourTorus L m ≃ FourTorus L m} (h : PullbackData σ j)
    (ℬ : Set (Bond L m j)) : bondSetTransport σ.symm (bondSetTransport σ ℬ) = ℬ := by
  ext b
  constructor
  · rintro ⟨c, ⟨d, hd, rfl⟩, rfl⟩
    change bondPreimage σ (bondImage σ d) ∈ ℬ
    rwa [h.preimage_image]
  · intro hb
    exact ⟨bondImage σ b, ⟨b, hb, rfl⟩, h.preimage_image b⟩
def OrientationDichotomy (L m : ℕ) (j : ℤ) : Prop :=
  ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem opposite_positive_iff (hH : OrientationDichotomy L m j) (b : Bond L m j) :
    b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented := by
  rcases hH b with h | h <;> tauto
section Forms
variable {σ : FourTorus L m ≃ FourTorus L m} {V A B : Bond L m j → ComplexMatrix2} {b : Bond L m j}
  {ℬ : Set (Bond L m j)}
theorem twisted_of_pos_pos (hb : b.IsPositivelyOriented)
    (hp : (bondPreimage σ b).IsPositivelyOriented) :
    twistedTransportForm σ V A b = A (bondPreimage σ b) := by
  simp only [twistedTransportForm, twistedFormValue, if_pos hb, if_pos hp]
theorem twisted_of_pos_neg (hb : b.IsPositivelyOriented)
    (hp : ¬ (bondPreimage σ b).IsPositivelyOriented) :
    twistedTransportForm σ V A b =
      -ComplexMatrix2.conjugateBy (V (bondPreimage σ b).opposite)⁻¹
        (A (bondPreimage σ b).opposite) := by
  simp only [twistedTransportForm, twistedFormValue, if_pos hb, if_neg hp]
theorem twisted_of_neg (hb : ¬ b.IsPositivelyOriented) :
    twistedTransportForm σ V A b = -twistedFormValue σ V A b.opposite := by
  simp only [twistedTransportForm, if_neg hb]
theorem twisted_of_pos (hb : b.IsPositivelyOriented) :
    twistedTransportForm σ V A b = twistedFormValue σ V A b := by
  simp only [twistedTransportForm, if_pos hb]
theorem twisted_opposite (hH : OrientationDichotomy L m j) (b : Bond L m j) :
    twistedTransportForm σ V A b.opposite = -twistedTransportForm σ V A b := by
  by_cases hb : b.IsPositivelyOriented
  · have h' : ¬ b.opposite.IsPositivelyOriented := by
      rw [opposite_positive_iff hH]
      exact not_not.2 hb
    rw [twisted_of_neg h', opposite_opposite, twisted_of_pos hb]
  · have h' : b.opposite.IsPositivelyOriented := (opposite_positive_iff hH b).2 hb
    rw [twisted_of_pos h', twisted_of_neg hb, neg_neg]
theorem twisted_congr (hB : PullbackData σ j) {V' A' : Bond L m j → ComplexMatrix2}
    (h₁ : A (bondPreimage σ b) = A' (bondPreimage σ b))
    (h₂ : A (bondPreimage σ b).opposite = A' (bondPreimage σ b).opposite)
    (h₃ : V (bondPreimage σ b) = V' (bondPreimage σ b))
    (h₄ : V (bondPreimage σ b).opposite = V' (bondPreimage σ b).opposite) :
    twistedTransportForm σ V A b = twistedTransportForm σ V' A' b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [twisted_of_pos hb, twisted_of_pos hb]
    unfold twistedFormValue
    by_cases hp : (bondPreimage σ b).IsPositivelyOriented
    · simp only [if_pos hp, h₁]
    · simp only [if_neg hp, h₂, h₄]
  · rw [twisted_of_neg hb, twisted_of_neg hb]
    unfold twistedFormValue
    rw [hB.preimage_opposite, opposite_opposite]
    by_cases hp : (bondPreimage σ b).opposite.IsPositivelyOriented
    · simp only [if_pos hp, h₂]
    · simp only [if_neg hp, h₁, h₃]
theorem twisted_add (A B : Bond L m j → ComplexMatrix2) :
    twistedTransportForm σ V (A + B) =
      twistedTransportForm σ V A + twistedTransportForm σ V B := by
  have val : ∀ c, twistedFormValue σ V (A + B) c =
      twistedFormValue σ V A c + twistedFormValue σ V B c := by
    intro c
    unfold twistedFormValue
    split_ifs
    · rfl
    · simp only [Pi.add_apply, conjugateBy_add, neg_add]
  funext c
  by_cases hc : c.IsPositivelyOriented
  · simp only [Pi.add_apply, twisted_of_pos hc, val]
  · simp only [Pi.add_apply, twisted_of_neg hc, val, neg_add]
theorem twisted_smul (c : ℂ) (A : Bond L m j → ComplexMatrix2) :
    twistedTransportForm σ V (c • A) = c • twistedTransportForm σ V A := by
  have val : ∀ d, twistedFormValue σ V (c • A) d = c • twistedFormValue σ V A d := by
    intro d
    unfold twistedFormValue
    split_ifs
    · rfl
    · simp only [Pi.smul_apply, conjugateBy_smul, smul_neg]
  funext d
  by_cases hd : d.IsPositivelyOriented
  · simp only [Pi.smul_apply, twisted_of_pos hd, val]
  · simp only [Pi.smul_apply, twisted_of_neg hd, val, smul_neg]
theorem twisted_zero : twistedTransportForm σ V (0 : Bond L m j → ComplexMatrix2) = 0 := by
  have := twisted_smul (σ := σ) (V := V) (0 : ℂ) (0 : Bond L m j → ComplexMatrix2)
  simpa using this
theorem eq_zero_of_not_mem (hA : ℬ.indicator A = A) (hb : b ∉ ℬ) : A b = 0 := by
  rw [← hA]
  exact indicator_of_notMem hb A
theorem twisted_eq_zero_off_image (hB : PullbackData σ j) (hℬ : IsReversalClosed ℬ)
    (hA : ℬ.indicator A = A) (hb : b ∉ bondSetTransport σ ℬ) :
    twistedTransportForm σ V A b = 0 := by
  have h₁ : bondPreimage σ b ∉ ℬ := fun h => hb ((mem_bondSetImage_iff hB).2 h)
  have h₂ : (bondPreimage σ b).opposite ∉ ℬ := fun h => h₁ (by
    simpa [opposite_opposite] using hℬ _ h)
  rw [twisted_congr hB (V' := V) (A' := 0) (eq_zero_of_not_mem hA h₁)
    (eq_zero_of_not_mem hA h₂) rfl rfl, twisted_zero]
  rfl
theorem indicator_twisted (hB : PullbackData σ j) (hℬ : IsReversalClosed ℬ)
    (hA : ℬ.indicator A = A) :
    (bondSetTransport σ ℬ).indicator (twistedTransportForm σ V A) =
      twistedTransportForm σ V A := by
  funext c
  by_cases hc : c ∈ bondSetTransport σ ℬ
  · exact indicator_of_mem hc _
  · rw [indicator_of_notMem hc, twisted_eq_zero_off_image hB hℬ hA hc]
theorem twisted_isBondForm (hH : OrientationDichotomy L m j)
    (hV : IsGaugeField complexGaugeGroup ℬ V) (hA : A ∈ complexFormsOn ℬ) :
    IsBondForm complexLieAlgebra (twistedTransportForm σ V A) := by
  refine ⟨fun c hc => ?_, fun c => twisted_opposite hH c⟩
  by_cases hp : (bondPreimage σ c).IsPositivelyOriented
  · rw [twisted_of_pos_pos hc hp]
    exact hA.1.1 _ hp
  · rw [twisted_of_pos_neg hc hp]
    have hr := (opposite_positive_iff hH _).2 hp
    refine ComplexMatrix2.traceless.neg_mem ?_
    by_cases hm : (bondPreimage σ c).opposite ∈ ℬ
    · exact conjugateBy_mem (inv_mem_gaugeGroup (hV.1 _ hm)) (hA.1.1 _ hr)
    · rw [eq_zero_of_not_mem hA.2 hm, conjugateBy_zero]
      exact ComplexMatrix2.traceless.zero_mem
theorem twisted_mem_complexFormsOn (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hℬ : IsReversalClosed ℬ) (hV : IsGaugeField complexGaugeGroup ℬ V)
    (hA : A ∈ complexFormsOn ℬ) :
    twistedTransportForm σ V A ∈ complexFormsOn (bondSetTransport σ ℬ) :=
  ⟨twisted_isBondForm hH hV hA, indicator_twisted hB hℬ hA.2⟩
theorem twisted_symm_twisted (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hℬ : IsReversalClosed ℬ) (hV : IsGaugeField complexGaugeGroup ℬ V)
    (hA : A ∈ complexFormsOn ℬ) :
    twistedTransportForm σ.symm (transportGaugeField σ V)
      (twistedTransportForm σ V A) = A := by
  have hpos : ∀ c : Bond L m j, c.IsPositivelyOriented →
      twistedTransportForm σ.symm (transportGaugeField σ V)
        (twistedTransportForm σ V A) c = A c := by
    intro c hc
    by_cases hi : (bondImage σ c).IsPositivelyOriented
    · rw [twisted_of_pos_pos (σ := σ.symm) hc hi]
      change twistedTransportForm σ V A (bondImage σ c) = A c
      rw [twisted_of_pos_pos hi (by rw [hB.preimage_image]; exact hc), hB.preimage_image]
    · rw [twisted_of_pos_neg (σ := σ.symm) hc hi]
      change -ComplexMatrix2.conjugateBy (V (bondPreimage σ (bondImage σ c).opposite))⁻¹
        (twistedTransportForm σ V A (bondImage σ c).opposite) = A c
      have hr := (opposite_positive_iff hH _).2 hi
      have e : bondPreimage σ (bondImage σ c).opposite = c.opposite := by
        rw [hB.preimage_opposite, hB.preimage_image]
      have hnc : ¬ (bondPreimage σ (bondImage σ c).opposite).IsPositivelyOriented := by
        rw [e, opposite_positive_iff hH]
        exact not_not.2 hc
      rw [twisted_of_pos_neg hr hnc, e, opposite_opposite, conjugateBy_neg, neg_neg]
      by_cases hm : c ∈ ℬ
      · rw [hV.2 c hm, inv_inv_of_mem (hV.1 c hm), conjugateBy_conjugateBy_inv (hV.1 c hm)]
      · rw [eq_zero_of_not_mem hA.2 hm, conjugateBy_zero, conjugateBy_zero]
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hr := (opposite_positive_iff hH c).2 hc
    have h₁ := hpos _ hr
    rw [twisted_opposite hH c, hA.1.2 c] at h₁
    exact neg_injective h₁
theorem twisted_twisted_symm (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hℬ : IsReversalClosed ℬ) (hV : IsGaugeField complexGaugeGroup ℬ V)
    {A' : Bond L m j → ComplexMatrix2} (hA : A' ∈ complexFormsOn (bondSetTransport σ ℬ)) :
    twistedTransportForm σ V
      (twistedTransportForm σ.symm (transportGaugeField σ V) A') = A' := by
  have hB' := hB.symm hB.image_opposite
  have h := twisted_symm_twisted (σ := σ.symm) (V := transportGaugeField σ V) hH hB'
    (bondSetImage_reversalClosed hB hℬ) (transport_isGaugeField hB hV) hA
  rw [transport_symm_transport hB] at h
  exact h
theorem twisted_symm_mem (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hℬ : IsReversalClosed ℬ) (hV : IsGaugeField complexGaugeGroup ℬ V)
    {A' : Bond L m j → ComplexMatrix2} (hA : A' ∈ complexFormsOn (bondSetTransport σ ℬ)) :
    twistedTransportForm σ.symm (transportGaugeField σ V) A' ∈ complexFormsOn ℬ := by
  have hB' := hB.symm hB.image_opposite
  have h := twisted_mem_complexFormsOn (σ := σ.symm) (V := transportGaugeField σ V) hH hB'
    (bondSetImage_reversalClosed hB hℬ) (transport_isGaugeField hB hV) hA
  rwa [bondSetImage_symm_image hB] at h
theorem twisted_bijOn (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hℬ : IsReversalClosed ℬ) (hV : IsGaugeField complexGaugeGroup ℬ V) :
    BijOn (twistedTransportForm σ V) (complexFormsOn ℬ)
      (complexFormsOn (bondSetTransport σ ℬ)) := by
  refine InvOn.bijOn (f' := twistedTransportForm σ.symm (transportGaugeField σ V))
    ⟨fun A hA => twisted_symm_twisted hH hB hℬ hV hA,
      fun A hA => twisted_twisted_symm hH hB hℬ hV hA⟩
    (fun A hA => twisted_mem_complexFormsOn hH hB hℬ hV hA)
    (fun A hA => twisted_symm_mem hH hB hℬ hV hA)
def positiveRep (b : Bond L m j) : Bond L m j :=
  open Classical in if b.IsPositivelyOriented then b else b.opposite
theorem positiveRep_of_pos (hb : b.IsPositivelyOriented) : positiveRep b = b := if_pos hb
theorem positiveRep_of_not_pos (hb : ¬ b.IsPositivelyOriented) : positiveRep b = b.opposite :=
  if_neg hb
theorem positiveRep_isPositive (b : Bond L m j) : (positiveRep b).IsPositivelyOriented := by apply _root_.YangMills.DeltaSharedProofs.p500474 <;> assumption
theorem positiveRep_preimage_positiveRep_image (hH : OrientationDichotomy L m j)
    (hB : PullbackData σ j) (hb : b.IsPositivelyOriented) :
    positiveRep (bondPreimage σ (positiveRep (bondImage σ b))) = b := by
  by_cases hc : (bondImage σ b).IsPositivelyOriented
  · rw [positiveRep_of_pos hc, hB.preimage_image, positiveRep_of_pos hb]
  · have hn : ¬ b.opposite.IsPositivelyOriented := by
      rw [opposite_positive_iff hH]
      exact not_not.2 hb
    rw [positiveRep_of_not_pos hc, hB.preimage_opposite, hB.preimage_image,
      positiveRep_of_not_pos hn, opposite_opposite]
def positiveRepEquiv (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    {p p' : Bond L m j → Prop}
    (hp : ∀ b, p b → b.IsPositivelyOriented) (hp' : ∀ b, p' b → b.IsPositivelyOriented)
    (h₁ : ∀ b, p b → p' (positiveRep (bondImage σ b)))
    (h₂ : ∀ b, p' b → p (positiveRep (bondPreimage σ b))) : {b // p b} ≃ {b // p' b} where
  toFun b := ⟨positiveRep (bondImage σ b.1), h₁ _ b.2⟩
  invFun b := ⟨positiveRep (bondPreimage σ b.1), h₂ _ b.2⟩
  left_inv b := Subtype.ext (positiveRep_preimage_positiveRep_image hH hB (hp _ b.2))
  right_inv b := Subtype.ext
    (positiveRep_preimage_positiveRep_image (σ := σ.symm) hH (hB.symm hB.image_opposite)
      (hp' _ b.2))
theorem halfTracePairing_twisted (hV : IsGaugeField complexGaugeGroup ℬ V)
    {A₁ A₂ : Bond L m j → ComplexMatrix2}
    (h₁ : ℬ.indicator A₁ = A₁) (h₂ : ℬ.indicator A₂ = A₂) (hb : b.IsPositivelyOriented) :
    halfTracePairing (twistedTransportForm σ V A₁ b) (twistedTransportForm σ V A₂ b) =
      halfTracePairing (A₁ (positiveRep (bondPreimage σ b)))
        (A₂ (positiveRep (bondPreimage σ b))) := by
  by_cases hp : (bondPreimage σ b).IsPositivelyOriented
  · rw [twisted_of_pos_pos hb hp, twisted_of_pos_pos hb hp, positiveRep_of_pos hp]
  · rw [twisted_of_pos_neg hb hp, twisted_of_pos_neg hb hp, positiveRep_of_not_pos hp]
    have e : ∀ X Y : ComplexMatrix2, halfTracePairing (-X) (-Y) = halfTracePairing X Y :=
      fun X Y => by simp [halfTracePairing]
    rw [e]
    by_cases hm : (bondPreimage σ b).opposite ∈ ℬ
    · exact halfTracePairing_conjugateBy (inv_mem_gaugeGroup (hV.1 _ hm)) _ _
    · rw [eq_zero_of_not_mem h₁ hm, eq_zero_of_not_mem h₂ hm, conjugateBy_zero]
theorem bondFormInner_twisted (hF : LieInnerProduct.PeriodicLatticePairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) < j)
    (hH : OrientationDichotomy L m j) (hB : PullbackData σ j) (hℬ : IsReversalClosed ℬ)
    (hV : IsGaugeField complexGaugeGroup ℬ V) {A₁ A₂ : Bond L m j → ComplexMatrix2}
    (h₁ : A₁ ∈ complexFormsOn ℬ) (h₂ : A₂ ∈ complexFormsOn ℬ) {ξ : ℝ} (hξ : 0 < ξ) :
    bondFormInner ξ (twistedTransportForm σ V A₁) (twistedTransportForm σ V A₂) =
      bondFormInner ξ A₁ A₂ := by
  obtain ⟨h₃, h₄, h₅, hfs, -⟩ := hF L m j ξ hL hm hj hξ
  have t₁ : IsBondForm complexLieAlgebra (twistedTransportForm σ V A₁) :=
    twisted_isBondForm hH hV h₁
  have t₂ : IsBondForm complexLieAlgebra (twistedTransportForm σ V A₂) :=
    twisted_isBondForm hH hV h₂
  have e₁ := hfs.2.2.2.1 ⟨twistedTransportForm σ V A₁, t₁⟩ ⟨twistedTransportForm σ V A₂, t₂⟩
  have e₂ := hfs.2.2.2.1 ⟨A₁, h₁.1⟩ ⟨A₂, h₂.1⟩
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  let e : PositivelyOrientedBond L m j ≃ PositivelyOrientedBond L m j :=
    positiveRepEquiv (σ := σ) hH hB (p := Bond.IsPositivelyOriented)
      (p' := Bond.IsPositivelyOriented)
      (fun _ h => h) (fun _ h => h) (fun _ _ => positiveRep_isPositive _)
      (fun _ _ => positiveRep_isPositive _)
  let g : PositivelyOrientedBond L m j → ℂ := fun c => halfTracePairing (A₁ c.1) (A₂ c.1)
  have hg : ∀ c : PositivelyOrientedBond L m j,
      halfTracePairing (twistedTransportForm σ V A₁ c.1)
        (twistedTransportForm σ V A₂ c.1) = g (e.symm c) :=
    fun c => halfTracePairing_twisted hV h₁.2 h₂.2 c.2
  have hs : ∑ᶠ c : PositivelyOrientedBond L m j,
      halfTracePairing (twistedTransportForm σ V A₁ c.1)
        (twistedTransportForm σ V A₂ c.1) = ∑ᶠ c, g c :=
    (finsum_congr hg).trans (finsum_comp_equiv e.symm)
  exact congrArg (fun z => ((ξ ^ 4 : ℝ) : ℂ) * z) hs
theorem expTwist_of_pos {U : Bond L m j → ComplexMatrix2} (hb : b.IsPositivelyOriented) :
    expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by
  simp only [expTwist, if_pos hb]
theorem expTwist_of_not_pos {U : Bond L m j → ComplexMatrix2} (hb : ¬ b.IsPositivelyOriented) :
    expTwist A U b = (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by
  simp only [expTwist, if_neg hb]
theorem matExp_conjugate_mul (h₇ : ComplexMatrix2.OperatorNormUnderConjugation)
    {W : ComplexMatrix2} (hW : W ∈ complexGaugeGroup) (a : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • (-ComplexMatrix2.conjugateBy W a)) * W =
      W * ComplexMatrix2.matExp (-(Complex.I • a)) := by
  have h := h₇.2.2.2.2.1 W (-(Complex.I • a))
    ((Matrix.isUnit_iff_isUnit_det W).2 (isUnit_det_of_mem hW))
  have e : Complex.I • (-ComplexMatrix2.conjugateBy W a) = W * (-(Complex.I • a)) * W⁻¹ := by
    simp [ComplexMatrix2.conjugateBy]
  rw [e, ← h, mul_assoc, inv_mul_of_mem hW, mul_one]
theorem expTwist_opposite (hH : OrientationDichotomy L m j) {d : Bond L m j}
    (hA : IsBondForm complexLieAlgebra A)
    (hd : d.IsPositivelyOriented → V d ∈ complexGaugeGroup) :
    expTwist A V d = (expTwist A V d.opposite)⁻¹ := by
  by_cases hp : d.IsPositivelyOriented
  · have hn : ¬ d.opposite.IsPositivelyOriented := by
      rw [opposite_positive_iff hH]
      exact not_not.2 hp
    rw [expTwist_of_not_pos hn, opposite_opposite, expTwist_of_pos hp]
    exact (inv_inv_of_mem (mul_mem_gaugeGroup (matExp_mem_gaugeGroup (hA.1 d hp)) (hd hp))).symm
  · have hr := (opposite_positive_iff hH d).2 hp
    rw [expTwist_of_not_pos hp, expTwist_of_pos hr]
theorem expTwist_isGaugeField (hH : OrientationDichotomy L m j) (hℬ : IsReversalClosed ℬ)
    (hV : IsGaugeField complexGaugeGroup ℬ V) (hA : IsBondForm complexLieAlgebra A) :
    IsGaugeField complexGaugeGroup ℬ (expTwist A V) := by
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · by_cases hp : c.IsPositivelyOriented
    · rw [expTwist_of_pos hp]
      exact mul_mem_gaugeGroup (matExp_mem_gaugeGroup (hA.1 c hp)) (hV.1 c hc)
    · rw [expTwist_of_not_pos hp]
      have hr := (opposite_positive_iff hH c).2 hp
      exact inv_mem_gaugeGroup
        (mul_mem_gaugeGroup (matExp_mem_gaugeGroup (hA.1 _ hr)) (hV.1 _ (hℬ c hc)))
  · have h := expTwist_opposite (V := V) (d := c.opposite) hH hA (fun _ => hV.1 _ (hℬ c hc))
    rwa [opposite_opposite] at h
theorem transport_expTwist_of_pos (h₇ : ComplexMatrix2.OperatorNormUnderConjugation)
    (hB : PullbackData σ j) (hV : IsGaugeField complexGaugeGroup ℬ V)
    (hℬ : IsReversalClosed ℬ) (hb : b.IsPositivelyOriented) (hm : b ∈ bondSetTransport σ ℬ) :
    transportGaugeField σ (expTwist A V) b =
      expTwist (twistedTransportForm σ V A) (transportGaugeField σ V) b := by
  change expTwist A V (bondPreimage σ b) = _
  rw [expTwist_of_pos hb]
  have hm' := (mem_bondSetImage_iff hB).1 hm
  by_cases hp : (bondPreimage σ b).IsPositivelyOriented
  · rw [expTwist_of_pos hp, twisted_of_pos_pos hb hp]
    rfl
  · rw [expTwist_of_not_pos hp, twisted_of_pos_neg hb hp]
    have hc := hℬ _ hm'
    have e : V (bondPreimage σ b) = (V (bondPreimage σ b).opposite)⁻¹ := by
      have := hV.2 _ hc
      rwa [opposite_opposite] at this
    change _ = _ * V (bondPreimage σ b)
    rw [e, matExp_conjugate_mul h₇ (inv_mem_gaugeGroup (hV.1 _ hc)), Matrix.mul_inv_rev,
      matExp_inv]
theorem transport_expTwist (h₇ : ComplexMatrix2.OperatorNormUnderConjugation)
    (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hV : IsGaugeField complexGaugeGroup ℬ V)
    (hℬ : IsReversalClosed ℬ) (hA : IsBondForm complexLieAlgebra A)
    (hm : b ∈ bondSetTransport σ ℬ) :
    transportGaugeField σ (expTwist A V) b =
      expTwist (twistedTransportForm σ V A) (transportGaugeField σ V) b := by
  by_cases hb : b.IsPositivelyOriented
  · exact transport_expTwist_of_pos h₇ hB hV hℬ hb hm
  · have hr := (opposite_positive_iff hH b).2 hb
    have hm' := (mem_bondSetImage_iff hB).1 hm
    rw [expTwist_of_not_pos hb]
    have h := transport_expTwist_of_pos (A := A) h₇ hB hV hℬ hr
      (bondSetImage_reversalClosed hB hℬ b hm)
    change expTwist A V (bondPreimage σ b) = _
    change expTwist A V (bondPreimage σ b.opposite) = _ at h
    have e : expTwist (twistedTransportForm σ V A) (transportGaugeField σ V) b.opposite =
        ComplexMatrix2.matExp (Complex.I • twistedTransportForm σ V A b.opposite) *
          transportGaugeField σ V b.opposite := expTwist_of_pos hr
    rw [← e, ← h, hB.preimage_opposite]
    exact expTwist_opposite hH hA (fun _ => hV.1 _ hm')
theorem toFourTorus_add (x y : Fin 4 → ℝ) :
    toFourTorus L m (x + y) = toFourTorus L m x + toFourTorus L m y := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.toFourTorus_add <;> assumption
theorem toFourTorus_surjective : Function.Surjective (toFourTorus L m) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.toFourTorus_surjective <;> assumption
theorem pointOnAxis_eq (μ : Fin 4) (t : ℝ) :
    pointOnAxis L m μ t = toFourTorus L m (Pi.single μ t) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.pointOnAxis_eq_toFourTorus <;> assumption
theorem actOnVector_add (r : SignedFrame) (x y : Fin 4 → ℝ) :
    r.actOnVector (x + y) = r.actOnVector x + r.actOnVector y := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.actOnVector_add <;> assumption
theorem actOnVector_single (π : Equiv.Perm (Fin 4)) (μ : Fin 4) (t : ℝ) :
    SignedFrame.actOnVector (π, 1) (Pi.single μ t) = Pi.single (π.symm μ) t := by
  funext κ
  by_cases h : κ = π.symm μ
  · subst h
    simp [SignedFrame.actOnVector]
  · have h' : π κ ≠ μ := fun e => h (by rw [← e]; simp)
    simp [SignedFrame.actOnVector, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
theorem map_add_pointOnAxis {π : Equiv.Perm (Fin 4)} {v : Fin 4 → ℝ}
    (hind : IsInducedByAffine σ (π, 1) v) (y : FourTorus L m) (μ : Fin 4) (t : ℝ) :
    σ (y + pointOnAxis L m μ t) = σ y + pointOnAxis L m (π.symm μ) t := by
  obtain ⟨x, rfl⟩ := toFourTorus_surjective y
  rw [pointOnAxis_eq, ← toFourTorus_add, hind, hind, actOnVector_add, actOnVector_single,
    add_right_comm, toFourTorus_add, ← pointOnAxis_eq]
theorem bondImage_isPositive {π : Equiv.Perm (Fin 4)} (hl : HasLinearPart σ (π, 1))
    (hc : PreservesCells σ j) (hb : b.IsPositivelyOriented) :
    (bondImage σ b).IsPositivelyOriented := by
  obtain ⟨v, hv⟩ := hl
  obtain ⟨μ, hμ⟩ := hb
  refine ⟨π.symm μ, ?_⟩
  have hh : (b.target : FourTorus L m) = b.source + pointOnAxis L m μ (meshSize L j) := by
    have : b.target = b.source + unitStep L m j μ := by rw [← hμ]; abel
    rw [this]
    rfl
  have h₁ : ((bondImage σ b).target : FourTorus L m) = σ b.target := by
    rw [(hc.2.2.2.1 b).2, hc.1]
  have h₂ : ((bondImage σ b).source : FourTorus L m) = σ b.source := by
    rw [(hc.2.2.2.1 b).1, hc.1]
  apply Subtype.ext
  change ((bondImage σ b).target : FourTorus L m) - ((bondImage σ b).source : FourTorus L m) =
    pointOnAxis L m (π.symm μ) (meshSize L j)
  rw [h₁, h₂, hh, map_add_pointOnAxis hv]
  abel
theorem bondPreimage_isPositive (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hp : ∀ c : Bond L m j, c.IsPositivelyOriented → (bondImage σ c).IsPositivelyOriented)
    (hb : b.IsPositivelyOriented) : (bondPreimage σ b).IsPositivelyOriented := by
  by_contra hn
  have hr := (opposite_positive_iff hH _).2 hn
  have h := hp _ hr
  rw [hB.image_opposite, hB.image_preimage, opposite_positive_iff hH] at h
  exact h hb
theorem twisted_eq_transportForm (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hp : ∀ c : Bond L m j, c.IsPositivelyOriented → (bondImage σ c).IsPositivelyOriented)
    (hA : ∀ c : Bond L m j, A c.opposite = -A c) :
    twistedTransportForm σ V A = transportForm σ A := by
  have hpos : ∀ c : Bond L m j, c.IsPositivelyOriented →
      twistedTransportForm σ V A c = A (bondPreimage σ c) :=
    fun c hc => twisted_of_pos_pos hc (bondPreimage_isPositive hH hB hp hc)
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hr := (opposite_positive_iff hH c).2 hc
    have h := hpos _ hr
    rw [twisted_opposite hH c, hB.preimage_opposite, hA] at h
    exact neg_injective h
theorem twisted_trivial (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hA : ∀ c : Bond L m j, A c.opposite = -A c) :
    twistedTransportForm σ trivialGaugeField A = transportForm σ A := by
  have hpos : ∀ c : Bond L m j, c.IsPositivelyOriented →
      twistedTransportForm σ trivialGaugeField A c = A (bondPreimage σ c) := by
    intro c hc
    by_cases hp : (bondPreimage σ c).IsPositivelyOriented
    · exact twisted_of_pos_pos hc hp
    · rw [twisted_of_pos_neg hc hp]
      have e : ComplexMatrix2.conjugateBy ((trivialGaugeField : Bond L m j → ComplexMatrix2)
          (bondPreimage σ c).opposite)⁻¹ (A (bondPreimage σ c).opposite) =
          A (bondPreimage σ c).opposite := by
        simp [ComplexMatrix2.conjugateBy, trivialGaugeField]
      have h := hA (bondPreimage σ c).opposite
      rw [opposite_opposite] at h
      rw [e, h]
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hr := (opposite_positive_iff hH c).2 hc
    have h := hpos _ hr
    rw [twisted_opposite hH c, hB.preimage_opposite, hA] at h
    exact neg_injective h
theorem mem_complexGaugeGroup {W : ComplexMatrix2} (hW : W ∈ compactGaugeGroup) :
    W ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hW).2
theorem mem_unitaryGroup {W : ComplexMatrix2} (hW : W ∈ compactGaugeGroup) :
    W ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hW).1
theorem inv_mem_compactGaugeGroup {W : ComplexMatrix2} (hW : W ∈ compactGaugeGroup) :
    W⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem conjugateBy_mem_hermitianTraceless {W X : ComplexMatrix2} (hW : W ∈ compactGaugeGroup)
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy W X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
theorem operatorNorm_conjugateBy (h₇ : ComplexMatrix2.OperatorNormUnderConjugation)
    {W : ComplexMatrix2} (hW : W ∈ compactGaugeGroup) (X : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy W X) =
      ComplexMatrix2.operatorNorm X :=
  h₇.2.1 X W (mem_unitaryGroup hW)
theorem mem_complexFormsOn_of_real (hA : A ∈ realFormsOn ℬ) : A ∈ complexFormsOn ℬ :=
  ⟨⟨fun c hc => (hA.1.1 c hc).2, hA.1.2⟩, hA.2⟩
theorem isGaugeField_complex_of_compact (hV : IsGaugeField compactGaugeGroup ℬ V) :
    IsGaugeField complexGaugeGroup ℬ V :=
  ⟨fun c hc => mem_complexGaugeGroup (hV.1 c hc), hV.2⟩
theorem twisted_mem_realFormsOn (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hℬ : IsReversalClosed ℬ) (hV : IsGaugeField compactGaugeGroup ℬ V)
    (hA : A ∈ realFormsOn ℬ) :
    twistedTransportForm σ V A ∈ realFormsOn (bondSetTransport σ ℬ) := by
  refine ⟨⟨fun c hc => ?_, fun c => twisted_opposite hH c⟩, indicator_twisted hB hℬ hA.2⟩
  by_cases hp : (bondPreimage σ c).IsPositivelyOriented
  · rw [twisted_of_pos_pos hc hp]
    exact hA.1.1 _ hp
  · rw [twisted_of_pos_neg hc hp]
    have hr := (opposite_positive_iff hH _).2 hp
    refine ComplexMatrix2.hermitianTraceless.neg_mem ?_
    by_cases hm : (bondPreimage σ c).opposite ∈ ℬ
    · exact conjugateBy_mem_hermitianTraceless (inv_mem_compactGaugeGroup (hV.1 _ hm))
        (hA.1.1 _ hr)
    · rw [eq_zero_of_not_mem hA.2 hm, conjugateBy_zero]
      exact ComplexMatrix2.hermitianTraceless.zero_mem
theorem twisted_bijOn_real (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hℬ : IsReversalClosed ℬ) (hV : IsGaugeField compactGaugeGroup ℬ V) :
    BijOn (twistedTransportForm σ V) (realFormsOn ℬ)
      (realFormsOn (bondSetTransport σ ℬ)) := by
  have hV' := isGaugeField_complex_of_compact hV
  refine InvOn.bijOn (f' := twistedTransportForm σ.symm (transportGaugeField σ V))
    ⟨fun A hA => twisted_symm_twisted hH hB hℬ hV' (mem_complexFormsOn_of_real hA),
      fun A hA => twisted_twisted_symm hH hB hℬ hV' (mem_complexFormsOn_of_real hA)⟩
    (fun A hA => twisted_mem_realFormsOn hH hB hℬ hV hA) (fun A hA => ?_)
  have hB' := hB.symm hB.image_opposite
  have h := twisted_mem_realFormsOn (σ := σ.symm) (V := transportGaugeField σ V) hH hB'
    (bondSetImage_reversalClosed hB hℬ) (transport_isGaugeField hB hV) hA
  rwa [bondSetImage_symm_image hB] at h
theorem operatorNorm_twisted_image (h₇ : ComplexMatrix2.OperatorNormUnderConjugation)
    (hH : OrientationDichotomy L m j)
    (hB : PullbackData σ j) (hℬ : IsReversalClosed ℬ) (hV : IsGaugeField compactGaugeGroup ℬ V)
    (hA : ∀ c : Bond L m j, A c.opposite = -A c) (hb : b ∈ ℬ) :
    ComplexMatrix2.operatorNorm (twistedTransportForm σ V A (bondImage σ b)) =
      ComplexMatrix2.operatorNorm (A b) := by
  have hn : ∀ X : ComplexMatrix2, ComplexMatrix2.operatorNorm (-X) =
      ComplexMatrix2.operatorNorm X := fun X => norm_neg X
  have hr : ComplexMatrix2.operatorNorm (A b.opposite) = ComplexMatrix2.operatorNorm (A b) := by
    rw [hA, hn]
  by_cases hc : (bondImage σ b).IsPositivelyOriented
  · by_cases hp : b.IsPositivelyOriented
    · rw [twisted_of_pos_pos hc (by rw [hB.preimage_image]; exact hp), hB.preimage_image]
    · rw [twisted_of_pos_neg hc (by rw [hB.preimage_image]; exact hp), hB.preimage_image, hn,
        operatorNorm_conjugateBy h₇ (inv_mem_compactGaugeGroup (hV.1 _ (hℬ b hb))), hr]
  · rw [twisted_of_neg hc, hn]
    unfold twistedFormValue
    rw [hB.preimage_opposite, hB.preimage_image]
    by_cases hp : b.opposite.IsPositivelyOriented
    · rw [if_pos hp, hr]
    · rw [if_neg hp, hn, opposite_opposite,
        operatorNorm_conjugateBy h₇ (inv_mem_compactGaugeGroup (hV.1 _ hb))]
theorem lieElement_ext {X Y : ComplexMatrix2.LieElement} (h : X.toMatrix = Y.toMatrix) : X = Y :=
  Subtype.ext (p := (· ∈ ComplexMatrix2.hermitianTraceless)) h
theorem lieElement_mem (X : ComplexMatrix2.LieElement) :
    X.toMatrix ∈ ComplexMatrix2.hermitianTraceless :=
  Subtype.property (p := (· ∈ ComplexMatrix2.hermitianTraceless)) X
def conjugateLinearEquiv {W : ComplexMatrix2} (hW : W ∈ compactGaugeGroup) :
    ComplexMatrix2.LieElement ≃ₗ[ℝ] ComplexMatrix2.LieElement where
  toFun Y := (⟨ComplexMatrix2.conjugateBy W Y.toMatrix,
    conjugateBy_mem_hermitianTraceless hW (lieElement_mem Y)⟩ : ComplexMatrix2.hermitianTraceless)
  invFun Y := (⟨ComplexMatrix2.conjugateBy W⁻¹ Y.toMatrix,
    conjugateBy_mem_hermitianTraceless (inv_mem_compactGaugeGroup hW) (lieElement_mem Y)⟩ :
      ComplexMatrix2.hermitianTraceless)
  map_add' X Y := lieElement_ext (conjugateBy_add W X.toMatrix Y.toMatrix)
  map_smul' c X := lieElement_ext (by
    change ComplexMatrix2.conjugateBy W (c • X.toMatrix) =
      c • ComplexMatrix2.conjugateBy W X.toMatrix
    simp [ComplexMatrix2.conjugateBy])
  left_inv Y := lieElement_ext (by
    change ComplexMatrix2.conjugateBy W⁻¹ (ComplexMatrix2.conjugateBy W Y.toMatrix) = Y.toMatrix
    have h := conjugateBy_conjugateBy_inv (inv_mem_gaugeGroup (mem_complexGaugeGroup hW))
      Y.toMatrix
    rwa [inv_inv_of_mem (mem_complexGaugeGroup hW)] at h)
  right_inv Y := lieElement_ext (conjugateBy_conjugateBy_inv (mem_complexGaugeGroup hW) Y.toMatrix)
def negConjugateIsometry
    (hN : ∀ Y : ComplexMatrix2.LieElement, ‖Y‖ = ComplexMatrix2.operatorNorm Y.toMatrix)
    (h₇ : ComplexMatrix2.OperatorNormUnderConjugation) {W : ComplexMatrix2}
    (hW : W ∈ compactGaugeGroup) :
    ComplexMatrix2.LieElement ≃ₗᵢ[ℝ] ComplexMatrix2.LieElement :=
  (LinearIsometryEquiv.mk (conjugateLinearEquiv hW) (fun Y => by
    rw [hN, hN]
    exact operatorNorm_conjugateBy h₇ hW Y.toMatrix)).trans (LinearIsometryEquiv.neg ℝ)
theorem negConjugateIsometry_toMatrix
    (hN : ∀ Y : ComplexMatrix2.LieElement, ‖Y‖ = ComplexMatrix2.operatorNorm Y.toMatrix)
    (h₇ : ComplexMatrix2.OperatorNormUnderConjugation) {W : ComplexMatrix2}
    (hW : W ∈ compactGaugeGroup) (Y : ComplexMatrix2.LieElement) :
    (negConjugateIsometry hN h₇ hW Y).toMatrix = -ComplexMatrix2.conjugateBy W Y.toMatrix := rfl
theorem positiveRep_mem (hℬ : IsReversalClosed ℬ) (hb : b ∈ ℬ) : positiveRep b ∈ ℬ := by
  by_cases hp : b.IsPositivelyOriented
  · rwa [positiveRep_of_pos hp]
  · rw [positiveRep_of_not_pos hp]
    exact hℬ b hb
def positiveBondOfEquiv (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hℬ : IsReversalClosed ℬ) : PositiveBondOf ℬ ≃ PositiveBondOf (bondSetTransport σ ℬ) :=
  positiveRepEquiv (σ := σ) hH hB (p := fun b => b ∈ ℬ ∧ b.IsPositivelyOriented)
    (p' := fun b => b ∈ bondSetTransport σ ℬ ∧ b.IsPositivelyOriented)
    (fun _ h => h.2) (fun _ h => h.2)
    (fun b h => ⟨positiveRep_mem (bondSetImage_reversalClosed hB hℬ) ⟨b, h.1, rfl⟩,
      positiveRep_isPositive _⟩)
    (fun _ h => ⟨positiveRep_mem hℬ ((mem_bondSetImage_iff hB).1 h.1), positiveRep_isPositive _⟩)
section Values
variable (a : PositiveBondOf ℬ → ComplexMatrix2.LieElement)
theorem realFormOfPositiveValues_of_pos {c : Bond L m j} (h : c ∈ ℬ ∧ c.IsPositivelyOriented) :
    realFormOfPositiveValues ℬ a c = (a ⟨c, h⟩).toMatrix := by
  simp only [realFormOfPositiveValues, bondFormOfPositive, if_pos h.2, dif_pos h]
theorem realFormOfPositiveValues_opposite (hH : OrientationDichotomy L m j) (c : Bond L m j) :
    realFormOfPositiveValues ℬ a c.opposite = -realFormOfPositiveValues ℬ a c := by
  have key : ∀ g : Bond L m j → ComplexMatrix2,
      bondFormOfPositive g c.opposite = -bondFormOfPositive g c := by
    intro g
    unfold bondFormOfPositive
    by_cases hc : c.IsPositivelyOriented
    · have hn : ¬ c.opposite.IsPositivelyOriented := by
        rw [opposite_positive_iff hH]
        exact not_not.2 hc
      simp only [if_pos hc, if_neg hn, opposite_opposite]
    · have hr := (opposite_positive_iff hH c).2 hc
      simp only [if_pos hr, if_neg hc, neg_neg]
  exact key _
theorem realFormOfPositiveValues_of_not_mem (hℬ : IsReversalClosed ℬ) {c : Bond L m j}
    (hc : c ∉ ℬ) : realFormOfPositiveValues ℬ a c = 0 := by
  have hn : ∀ d : Bond L m j, d ∉ ℬ → (open Classical in
      if h : d ∈ ℬ ∧ d.IsPositivelyOriented then (a ⟨d, h⟩).toMatrix else 0) = 0 :=
    fun d hd => dif_neg fun h => hd h.1
  unfold realFormOfPositiveValues bondFormOfPositive
  by_cases hp : c.IsPositivelyOriented
  · simp only [if_pos hp]
    exact hn c hc
  · simp only [if_neg hp]
    rw [hn c.opposite fun h => hc (by simpa [opposite_opposite] using hℬ _ h), neg_zero]
theorem indicator_realFormOfPositiveValues (hℬ : IsReversalClosed ℬ) :
    ℬ.indicator (realFormOfPositiveValues ℬ a) = realFormOfPositiveValues ℬ a := by
  funext c
  by_cases hc : c ∈ ℬ
  · exact indicator_of_mem hc _
  · rw [indicator_of_notMem hc, realFormOfPositiveValues_of_not_mem a hℬ hc]
end Values
theorem exists_measurePreserving_twisted
    (hN : ∀ Y : ComplexMatrix2.LieElement, ‖Y‖ = ComplexMatrix2.operatorNorm Y.toMatrix)
    (h₇ : ComplexMatrix2.OperatorNormUnderConjugation) (hfin : Finite (Bond L m j))
    (hH : OrientationDichotomy L m j) (hB : PullbackData σ j) (hℬ : IsReversalClosed ℬ)
    (hV : IsGaugeField compactGaugeGroup ℬ V) :
    ∃ (_ : Fintype (PositiveBondOf ℬ)) (_ : Fintype (PositiveBondOf (bondSetTransport σ ℬ)))
      (T : (PositiveBondOf ℬ → ComplexMatrix2.LieElement) →
        PositiveBondOf (bondSetTransport σ ℬ) → ComplexMatrix2.LieElement),
      MeasurePreserving T (Measure.pi fun _ => ComplexMatrix2.lieLebesgue)
          (Measure.pi fun _ => ComplexMatrix2.lieLebesgue) ∧
        ∀ a, realFormOfPositiveValues (bondSetTransport σ ℬ) (T a) =
          twistedTransportForm σ V (realFormOfPositiveValues ℬ a) := by
  classical
  let f₁ : Fintype (PositiveBondOf ℬ) := Fintype.ofFinite _
  let f₂ : Fintype (PositiveBondOf (bondSetTransport σ ℬ)) := Fintype.ofFinite _
  let E := positiveBondOfEquiv (σ := σ) hH hB hℬ
  have hpb : ∀ c : PositiveBondOf (bondSetTransport σ ℬ), (bondPreimage σ c.1) ∈ ℬ :=
    fun c => (mem_bondSetImage_iff hB).1 c.2.1
  let s : PositiveBondOf (bondSetTransport σ ℬ) →
      (ComplexMatrix2.LieElement ≃ₗᵢ[ℝ] ComplexMatrix2.LieElement) :=
    fun c => if hp : (bondPreimage σ c.1).IsPositivelyOriented then LinearIsometryEquiv.refl ℝ _
      else negConjugateIsometry hN h₇ (inv_mem_compactGaugeGroup (hV.1 _ (hℬ _ (hpb c))))
  have hE := measurePreserving_piCongrLeft (α := fun _ => ComplexMatrix2.LieElement)
    (fun _ => ComplexMatrix2.lieLebesgue) E
  have hC := measurePreserving_pi
    (fun _ : PositiveBondOf (bondSetTransport σ ℬ) => ComplexMatrix2.lieLebesgue)
    (fun _ => ComplexMatrix2.lieLebesgue) (fun c => (s c).measurePreserving)
  have hval : ∀ (a : PositiveBondOf ℬ → ComplexMatrix2.LieElement) c,
      MeasurableEquiv.piCongrLeft (fun _ => ComplexMatrix2.LieElement) E a c = a (E.symm c) := by
    intro a c
    obtain ⟨d, rfl⟩ := E.surjective c
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply, E.symm_apply_apply]
  refine ⟨f₁, f₂, fun a c =>
    s c (MeasurableEquiv.piCongrLeft (fun _ => ComplexMatrix2.LieElement) E a c),
    hC.comp hE, fun a => ?_⟩
  set R := realFormOfPositiveValues ℬ a with hR
  set T := (fun c => s c (MeasurableEquiv.piCongrLeft (fun _ => ComplexMatrix2.LieElement) E a c))
    with hT
  have hEv : ∀ c : PositiveBondOf (bondSetTransport σ ℬ),
      R (positiveRep (bondPreimage σ c.1)) = (a (E.symm c)).toMatrix := fun c =>
    realFormOfPositiveValues_of_pos a (E.symm c).2
  have hpos : ∀ c : Bond L m j, c.IsPositivelyOriented →
      realFormOfPositiveValues (bondSetTransport σ ℬ) T c = twistedTransportForm σ V R c := by
    intro c hc
    by_cases hm : c ∈ bondSetTransport σ ℬ
    · rw [realFormOfPositiveValues_of_pos T ⟨hm, hc⟩]
      change (s ⟨c, hm, hc⟩ (MeasurableEquiv.piCongrLeft (fun _ => ComplexMatrix2.LieElement) E a
        ⟨c, hm, hc⟩)).toMatrix = _
      rw [hval]
      have he := hEv ⟨c, hm, hc⟩
      by_cases hp : (bondPreimage σ c).IsPositivelyOriented
      · rw [twisted_of_pos_pos hc hp]
        have : s ⟨c, hm, hc⟩ = LinearIsometryEquiv.refl ℝ _ := dif_pos hp
        rw [this]
        rw [positiveRep_of_pos hp] at he
        exact he.symm
      · rw [twisted_of_pos_neg hc hp]
        have : s ⟨c, hm, hc⟩ = negConjugateIsometry hN h₇
            (inv_mem_compactGaugeGroup (hV.1 _ (hℬ _ (hpb ⟨c, hm, hc⟩)))) := dif_neg hp
        rw [this, negConjugateIsometry_toMatrix]
        rw [positiveRep_of_not_pos hp] at he
        change _ = -ComplexMatrix2.conjugateBy _ (R (bondPreimage σ c).opposite)
        rw [he]
    · rw [realFormOfPositiveValues_of_not_mem T (bondSetImage_reversalClosed hB hℬ) hm,
        twisted_eq_zero_off_image hB hℬ (indicator_realFormOfPositiveValues a hℬ) hm]
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hr := (opposite_positive_iff hH c).2 hc
    have h := hpos _ hr
    rw [realFormOfPositiveValues_opposite T hH, twisted_opposite hH c] at h
    exact neg_injective h
theorem fullTrace_inv_mul {X Y : ComplexMatrix2} (hX : X ∈ complexGaugeGroup)
    (hY : ComplexMatrix2.fullTrace Y = 0) :
    ComplexMatrix2.fullTrace (X⁻¹ * Y) = -ComplexMatrix2.fullTrace (X * Y) := by
  have h₁ : X⁻¹ = Matrix.adjugate X := by
    rw [Matrix.inv_def, det_eq_one_of_mem hX]
    simp
  have h₂ : Y 1 1 = -Y 0 0 := by
    have : Y 0 0 + Y 1 1 = 0 := by
      simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using hY
    linear_combination this
  rw [h₁, Matrix.adjugate_fin_two]
  simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, h₂]
  ring
theorem hasDerivAt_matExp_mul (Z W : ComplexMatrix2) :
    HasDerivAt (fun z : ℂ => ComplexMatrix2.matExp (z • Z) * W) (Z * W) 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) Z (0 : ℂ)).mul_const W
  simpa using h
theorem hasDerivAt_mul_matExp_neg (Z W : ComplexMatrix2) :
    HasDerivAt (fun z : ℂ => W * ComplexMatrix2.matExp (z • (-Z))) (W * (-Z)) 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) (-Z) (0 : ℂ)).const_mul W
  simpa using h
theorem hasDerivAt_fullTrace_plaquette (Z₁ Z₂ Z₃ Z₄ W₁ W₂ W₃ W₄ : ComplexMatrix2)
    (hW : W₄ ∈ complexGaugeGroup) (hW₁ : W₁ ∈ complexGaugeGroup) :
    HasDerivAt (fun z : ℂ => ComplexMatrix2.fullTrace
      ((ComplexMatrix2.matExp (z • Z₁) * W₁) * ((ComplexMatrix2.matExp (z • Z₂) * W₂) *
        ((W₃⁻¹ * ComplexMatrix2.matExp (z • (-Z₃))) *
          (W₄⁻¹ * ComplexMatrix2.matExp (z • (-Z₄)))))))
      (ComplexMatrix2.fullTrace ((W₁ * W₂ * W₃⁻¹ * W₄⁻¹) *
        (Z₁ + ComplexMatrix2.conjugateBy W₁ Z₂ - ComplexMatrix2.conjugateBy W₄ Z₃ - Z₄))) 0 := by
  let trC : ComplexMatrix2 →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  have d₁ := hasDerivAt_matExp_mul Z₁ W₁
  have d₂ := hasDerivAt_matExp_mul Z₂ W₂
  have d₃ := hasDerivAt_mul_matExp_neg Z₃ W₃⁻¹
  have d₄ := hasDerivAt_mul_matExp_neg Z₄ W₄⁻¹
  have d := d₁.mul (d₂.mul (d₃.mul d₄))
  have g := trC.hasFDerivAt.comp_hasDerivAt (0 : ℂ) d
  refine HasDerivAt.congr_deriv g ?_
  simp only [Pi.mul_apply, zero_smul, ComplexMatrix2.matExp, NormedSpace.exp_zero, one_mul,
    mul_one]
  have htr : ∀ M : ComplexMatrix2, trC M = Matrix.trace M := fun _ => rfl
  rw [htr]
  symm
  unfold ComplexMatrix2.conjugateBy ComplexMatrix2.fullTrace
  have c₂ : Matrix.trace (W₁ * W₂ * W₃⁻¹ * W₄⁻¹ * (W₁ * Z₂ * W₁⁻¹)) =
      Matrix.trace (W₁ * (Z₂ * W₂ * (W₃⁻¹ * W₄⁻¹))) := by
    have e : W₁ * W₂ * W₃⁻¹ * W₄⁻¹ * (W₁ * Z₂ * W₁⁻¹) =
        (W₁ * W₂ * W₃⁻¹ * W₄⁻¹ * W₁) * (Z₂ * W₁⁻¹) := by simp only [mul_assoc]
    rw [e, Matrix.trace_mul_comm]
    have e' : Z₂ * W₁⁻¹ * (W₁ * W₂ * W₃⁻¹ * W₄⁻¹ * W₁) =
        Z₂ * (W₁⁻¹ * W₁) * W₂ * W₃⁻¹ * W₄⁻¹ * W₁ := by simp only [mul_assoc]
    rw [e', inv_mul_of_mem hW₁, mul_one, Matrix.trace_mul_comm]
    simp only [mul_assoc]
  have c₃ : Matrix.trace (W₁ * W₂ * W₃⁻¹ * W₄⁻¹ * (W₄ * Z₃ * W₄⁻¹)) =
      Matrix.trace (W₁ * W₂ * W₃⁻¹ * Z₃ * W₄⁻¹) := by
    have e : W₁ * W₂ * W₃⁻¹ * W₄⁻¹ * (W₄ * Z₃ * W₄⁻¹) =
        W₁ * W₂ * W₃⁻¹ * (W₄⁻¹ * W₄) * Z₃ * W₄⁻¹ := by simp only [mul_assoc]
    rw [e, inv_mul_of_mem hW, mul_one]
  have c₁ : Matrix.trace (W₁ * W₂ * W₃⁻¹ * W₄⁻¹ * Z₁) =
      Matrix.trace (Z₁ * (W₁ * (W₂ * (W₃⁻¹ * W₄⁻¹)))) := by
    rw [Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [mul_sub, mul_sub, mul_add, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add, c₁, c₂, c₃]
  simp only [mul_add, mul_neg, neg_mul, Matrix.trace_add, Matrix.trace_neg, mul_assoc]
  ring
def firstEdge (p : Plaquette L m j) : Bond L m j := Bond.forwardFrom p.origin p.firstAxis
def secondEdge (p : Plaquette L m j) : Bond L m j :=
  Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis
def thirdEdgeReversed (p : Plaquette L m j) : Bond L m j :=
  Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis
def fourthEdgeReversed (p : Plaquette L m j) : Bond L m j :=
  Bond.forwardFrom p.origin p.secondAxis
theorem forwardFrom_isPositive (x : Site L m j) (μ : Fin 4) :
    (Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [Bond.forwardFrom]⟩
theorem plaquetteHolonomy_eq (U : Bond L m j → ComplexMatrix2) (p : Plaquette L m j) :
    plaquetteHolonomy U p =
      U (firstEdge p) * (U (secondEdge p) *
        (U (thirdEdgeReversed p).opposite * U (fourthEdgeReversed p).opposite)) := by
  simp [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, firstEdge, secondEdge,
    thirdEdgeReversed, fourthEdgeReversed]
theorem plaquetteHolonomy_mem {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ c, U c ∈ complexGaugeGroup) (p : Plaquette L m j) :
    plaquetteHolonomy U p ∈ complexGaugeGroup := by
  rw [plaquetteHolonomy_eq]
  exact mul_mem_gaugeGroup (hU _) (mul_mem_gaugeGroup (hU _) (mul_mem_gaugeGroup (hU _) (hU _)))
theorem curvature_isPlaquetteForm {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ c, U c ∈ complexGaugeGroup) (ξ : ℝ) :
    IsPlaquetteForm complexLieAlgebra (curvature ξ U) := by
  have hat : ∀ q : Plaquette L m j, curvatureAt ξ U q ∈ complexLieAlgebra := by
    intro q
    have hX := plaquetteHolonomy_mem hU q
    refine ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.smul_mem _ ?_)
    change Matrix.trace (plaquetteHolonomy U q - (plaquetteHolonomy U q)⁻¹) = 0
    have hX' : (plaquetteHolonomy U q).det = 1 := hX
    rw [Matrix.inv_def, hX', Ring.inverse_one, one_smul, Matrix.adjugate_fin_two,
      Matrix.trace_sub]
    simp [Matrix.trace_fin_two]
    ring
  refine ⟨fun μ ν x h => ?_, fun μ ν x => ?_⟩
  · unfold curvature plaquetteFormOf
    simp only [dif_pos h]
    exact hat _
  · unfold curvature plaquetteFormOf
    rcases lt_trichotomy μ ν with h | h | h
    · simp [dif_pos h, not_lt.2 h.le]
    · subst h
      simp
    · simp [dif_pos h, not_lt.2 h.le]
theorem bondFormComponent_mem (hA : IsBondForm complexLieAlgebra A)
    (μ : Fin 4) (x : Site L m j) : bondFormComponent A μ x ∈ complexLieAlgebra :=
  hA.1 _ (forwardFrom_isPositive x μ)
theorem covExteriorDeriv_isPlaquetteForm
    {U : Bond L m j → ComplexMatrix2} (hU : ∀ c, U c ∈ complexGaugeGroup)
    (hA : IsBondForm complexLieAlgebra A) (ξ : ℝ) :
    IsPlaquetteForm complexLieAlgebra (covExteriorDeriv ξ U A) := by
  have hc : ∀ μ ν x, covDeriv ξ U μ (bondFormComponent A ν) x ∈ complexLieAlgebra := by
    intro μ ν x
    refine ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.sub_mem
      (conjugateBy_mem (hU _) (bondFormComponent_mem hA _ _)) (bondFormComponent_mem hA _ _))
  exact ⟨fun μ ν x _ => ComplexMatrix2.traceless.sub_mem (hc _ _ _) (hc _ _ _),
    fun μ ν x => (neg_sub _ _).symm⟩
theorem hasDerivAt_plaquetteEnergy (hH : OrientationDichotomy L m j)
    {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup univ U) {ξ : ℝ} (hξ : 0 < ξ)
    (hA : IsBondForm complexLieAlgebra A) (p : Plaquette L m j) :
    HasDerivAt (fun t : ℝ =>
        plaquetteEnergy (expTwist (((t * ξ : ℝ) : ℂ) • A) U) p)
      (((ξ ^ 4 : ℝ) : ℂ) * halfTracePairing (curvatureAt ξ U p)
        (covExteriorDeriv ξ U A p.firstAxis p.secondAxis p.origin)) 0 := by
  have hUm : ∀ c, U c ∈ complexGaugeGroup := fun c => hU.1 c (mem_univ c)
  have hn : ∀ x μ, ¬ (Bond.forwardFrom x μ : Bond L m j).opposite.IsPositivelyOriented :=
    fun x μ => by
      rw [opposite_positive_iff hH]
      exact not_not.2 (forwardFrom_isPositive x μ)
  let Zf : Bond L m j → ComplexMatrix2 := fun c => (Complex.I * (ξ : ℂ)) • A c
  have hfwd : ∀ (z : ℂ) (c : Bond L m j), Complex.I • ((z * (ξ : ℂ)) • A) c = z • Zf c := by
    intro z c
    simp only [Pi.smul_apply, Zf, smul_smul]
    congr 1
    ring
  let G : ℂ → ℂ := fun z => 1 - (1 / 2) * ComplexMatrix2.fullTrace
    ((ComplexMatrix2.matExp (z • Zf (firstEdge p)) * U (firstEdge p)) *
      ((ComplexMatrix2.matExp (z • Zf (secondEdge p)) * U (secondEdge p)) *
        (((U (thirdEdgeReversed p))⁻¹ * ComplexMatrix2.matExp (z • (-Zf (thirdEdgeReversed p)))) *
          ((U (fourthEdgeReversed p))⁻¹ *
            ComplexMatrix2.matExp (z • (-Zf (fourthEdgeReversed p)))))))
  have hval : ∀ t : ℝ, plaquetteEnergy (expTwist (((t * ξ : ℝ) : ℂ) • A) U) p =
      G (t : ℂ) := by
    intro t
    have hc : ((t * ξ : ℝ) : ℂ) = (t : ℂ) * (ξ : ℂ) := by push_cast; ring
    have hinv : ∀ c : Bond L m j, c.IsPositivelyOriented → ¬ c.opposite.IsPositivelyOriented →
        expTwist (((t * ξ : ℝ) : ℂ) • A) U c.opposite =
          (U c)⁻¹ * ComplexMatrix2.matExp ((t : ℂ) • (-Zf c)) := by
      intro c _ hc'
      rw [expTwist_of_not_pos hc', opposite_opposite, Matrix.mul_inv_rev, matExp_inv, hc, hfwd,
        smul_neg]
    unfold plaquetteEnergy
    rw [plaquetteHolonomy_eq, expTwist_of_pos (b := firstEdge p) (forwardFrom_isPositive _ _),
      expTwist_of_pos (b := secondEdge p) (forwardFrom_isPositive _ _),
      hinv (thirdEdgeReversed p) (forwardFrom_isPositive _ _) (hn _ _),
      hinv (fourthEdgeReversed p) (forwardFrom_isPositive _ _) (hn _ _),
      hc, hfwd, hfwd]
  have hd := hasDerivAt_fullTrace_plaquette (Zf (firstEdge p)) (Zf (secondEdge p))
    (Zf (thirdEdgeReversed p)) (Zf (fourthEdgeReversed p)) (U (firstEdge p)) (U (secondEdge p))
    (U (thirdEdgeReversed p)) (U (fourthEdgeReversed p)) (hUm _) (hUm _)
  have hG := (hd.const_mul (1 / 2 : ℂ)).const_sub 1
  have hz : ((0 : ℝ) : ℂ) = 0 := Complex.ofReal_zero
  rw [← hz] at hG
  have hR : HasDerivAt (fun t : ℝ => G (t : ℂ)) _ (0 : ℝ) := hG.comp_ofReal
  have hf : (fun t : ℝ => plaquetteEnergy (expTwist (((t * ξ : ℝ) : ℂ) • A) U) p) =
      fun t : ℝ => G (t : ℂ) := funext hval
  rw [hf]
  refine hR.congr_deriv ?_
  set X := plaquetteHolonomy U p with hX
  have hXe : U (firstEdge p) * U (secondEdge p) * (U (thirdEdgeReversed p))⁻¹ *
      (U (fourthEdgeReversed p))⁻¹ = X := by
    rw [hX, plaquetteHolonomy_eq, hU.2 _ (mem_univ _), hU.2 _ (mem_univ _)]
    simp only [mul_assoc]
  set Y := A (firstEdge p) + ComplexMatrix2.conjugateBy (U (firstEdge p)) (A (secondEdge p)) -
    ComplexMatrix2.conjugateBy (U (fourthEdgeReversed p)) (A (thirdEdgeReversed p)) -
      A (fourthEdgeReversed p) with hY
  have hZ : Zf (firstEdge p) + ComplexMatrix2.conjugateBy (U (firstEdge p)) (Zf (secondEdge p)) -
      ComplexMatrix2.conjugateBy (U (fourthEdgeReversed p)) (Zf (thirdEdgeReversed p)) -
        Zf (fourthEdgeReversed p) =
      (Complex.I * (ξ : ℂ)) • Y := by
    simp only [Zf, conjugateBy_smul, hY, smul_sub, smul_add]
  have hD : covExteriorDeriv ξ U A p.firstAxis p.secondAxis p.origin = ((ξ⁻¹ : ℝ) : ℂ) • Y := by
    unfold covExteriorDeriv covDeriv
    rw [← smul_sub]
    congr 1
    simp only [hY, bondFormComponent, firstEdge, secondEdge, thirdEdgeReversed,
      fourthEdgeReversed]
    abel
  have hYtr : ComplexMatrix2.fullTrace Y = 0 := by
    have h₁ := bondFormComponent_mem hA p.firstAxis p.origin
    have h₂ := bondFormComponent_mem hA p.secondAxis (p.origin + unitStep L m j p.firstAxis)
    have h₃ := bondFormComponent_mem hA p.firstAxis (p.origin + unitStep L m j p.secondAxis)
    have h₄ := bondFormComponent_mem hA p.secondAxis p.origin
    exact ComplexMatrix2.traceless.sub_mem (ComplexMatrix2.traceless.sub_mem
      (ComplexMatrix2.traceless.add_mem h₁ (conjugateBy_mem (hUm _) h₂))
      (conjugateBy_mem (hUm _) h₃)) h₄
  have hXm : X ∈ complexGaugeGroup := plaquetteHolonomy_mem hUm p
  have htr : ComplexMatrix2.fullTrace ((X - X⁻¹) * Y) = 2 * ComplexMatrix2.fullTrace (X * Y) := by
    have h := fullTrace_inv_mul hXm hYtr
    unfold ComplexMatrix2.fullTrace at h ⊢
    rw [sub_mul, Matrix.trace_sub, h]
    ring
  have hξ' : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  rw [hXe, hZ, hD]
  unfold halfTracePairing curvatureAt ComplexMatrix2.halfTrace
  rw [← hX]
  simp only [Matrix.mul_smul, Matrix.smul_mul, ComplexMatrix2.fullTrace, Matrix.trace_smul,
    smul_eq_mul]
  have htr' : Matrix.trace ((X - X⁻¹) * Y) = 2 * Matrix.trace (X * Y) := htr
  rw [htr']
  have hI : (2 * Complex.I)⁻¹ = -(Complex.I / 2) := by
    rw [_root_.mul_inv, Complex.inv_I]
    ring
  rw [hI]
  push_cast
  field_simp
theorem hasDerivAt_totalEnergy (hF : LieInnerProduct.PeriodicLatticePairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) < j)
    (hH : OrientationDichotomy L m j) {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup univ U) {ξ : ℝ} (hξ : 0 < ξ)
    (hA : IsBondForm complexLieAlgebra A) :
    HasDerivAt (fun t : ℝ => totalEnergy (expTwist (((t * ξ : ℝ) : ℂ) • A) U))
      (plaquetteFormInner ξ (curvature ξ U) (covExteriorDeriv ξ U A)) 0 := by
  classical
  have hUm : ∀ c, U c ∈ complexGaugeGroup := fun c => hU.1 c (mem_univ c)
  obtain ⟨h₃, h₄, h₅, hfs, -⟩ := hF L m j ξ hL hm hj hξ
  let f : Fintype (Plaquette L m j) := Fintype.ofFinite _
  have e := hfs.2.2.2.2 ⟨curvature ξ U, curvature_isPlaquetteForm hUm ξ⟩
    ⟨covExteriorDeriv ξ U A, covExteriorDeriv_isPlaquetteForm hUm hA ξ⟩
  have hs := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Plaquette L m j)))
    (fun p _ => hasDerivAt_plaquetteEnergy hH hU hξ hA p)
  have hval : ∑ p : Plaquette L m j, ((ξ ^ 4 : ℝ) : ℂ) * halfTracePairing (curvatureAt ξ U p)
        (covExteriorDeriv ξ U A p.firstAxis p.secondAxis p.origin) =
      plaquetteFormInner ξ (curvature ξ U) (covExteriorDeriv ξ U A) := by
    rw [e, ← Finset.mul_sum]
    unfold scaledPairingSum
    rw [finsum_eq_sum_of_fintype]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    have : curvature ξ U p.firstAxis p.secondAxis p.origin = curvatureAt ξ U p := by
      unfold curvature plaquetteFormOf
      rw [dif_pos p.firstAxis_lt_secondAxis]
    change _ = halfTracePairing (curvature ξ U p.firstAxis p.secondAxis p.origin) _
    rw [this]
    rfl
  rw [← hval]
  have hfun : (fun t : ℝ => totalEnergy (expTwist (((t * ξ : ℝ) : ℂ) • A) U)) =
      fun t : ℝ => ∑ p : Plaquette L m j,
        plaquetteEnergy (expTwist (((t * ξ : ℝ) : ℂ) • A) U) p := by
    funext t
    exact finsum_eq_sum_of_fintype _
  rw [hfun]
  exact hs
theorem bondSetImage_univ (hB : PullbackData σ j) :
    bondSetTransport σ (univ : Set (Bond L m j)) = univ :=
  eq_univ_of_forall fun c => (mem_bondSetImage_iff hB).2 (mem_univ _)
theorem mem_complexFormsOn_univ (hA : IsBondForm complexLieAlgebra A) :
    A ∈ complexFormsOn (univ : Set (Bond L m j)) :=
  ⟨hA, indicator_univ A⟩
theorem yangMillsCurrent_transport (hF : LieInnerProduct.PeriodicLatticePairings)
    (h₇ : ComplexMatrix2.OperatorNormUnderConjugation)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) < j)
    (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hact : ∀ U : Bond L m j → ComplexMatrix2, IsGaugeField complexGaugeGroup univ U →
      totalEnergy (transportGaugeField σ U) = totalEnergy U)
    {U : Bond L m j → ComplexMatrix2} (hU : IsGaugeField complexGaugeGroup univ U)
    {ξ : ℝ} (hξ : 0 < ξ) :
    yangMillsCurrent ξ (transportGaugeField σ U) =
      twistedTransportForm σ U (yangMillsCurrent ξ U) := by
  have hcl : IsReversalClosed (univ : Set (Bond L m j)) := fun _ _ => mem_univ _
  have hU' : IsGaugeField complexGaugeGroup univ (transportGaugeField σ U) := by
    have h := transport_isGaugeField hB hU
    rwa [bondSetImage_univ hB] at h
  obtain ⟨h₃, h₄, h₅, hfs, hT⟩ := hF L m j ξ hL hm hj hξ
  obtain ⟨-, -, -, -, -, hiff⟩ := hT U hU
  obtain ⟨-, -, -, -, -, hiff'⟩ := hT _ hU'
  have hUm : ∀ c, U c ∈ complexGaugeGroup := fun c => hU.1 c (mem_univ c)
  have hUm' : ∀ c, transportGaugeField σ U c ∈ complexGaugeGroup :=
    fun c => hU'.1 c (mem_univ c)
  have spec := (hiff ⟨curvature ξ U, curvature_isPlaquetteForm hUm ξ⟩ _).2 rfl
  have hJ : yangMillsCurrent ξ U ∈ complexFormsOn (univ : Set (Bond L m j)) :=
    mem_complexFormsOn_univ spec.1
  refine ((hiff' ⟨curvature ξ _, curvature_isPlaquetteForm hUm' ξ⟩ _).1
    ⟨twisted_isBondForm hH hU hJ, fun A' hA' => ?_⟩).symm
  have hA'm : A' ∈ complexFormsOn (bondSetTransport σ (univ : Set (Bond L m j))) := by
    rw [bondSetImage_univ hB]
    exact mem_complexFormsOn_univ hA'
  set A := twistedTransportForm σ.symm (transportGaugeField σ U) A' with hAdef
  have hAm : A ∈ complexFormsOn univ := twisted_symm_mem hH hB hcl hU hA'm
  have hTA : twistedTransportForm σ U A = A' := twisted_twisted_symm hH hB hcl hU hA'm
  have d₁ := hasDerivAt_totalEnergy hF hL hm hj hH hU hξ hAm.1
  have d₂ := hasDerivAt_totalEnergy hF hL hm hj hH hU' hξ hA'
  have hfun : (fun t : ℝ => totalEnergy (expTwist (((t * ξ : ℝ) : ℂ) • A')
      (transportGaugeField σ U))) =
      fun t : ℝ => totalEnergy (expTwist (((t * ξ : ℝ) : ℂ) • A) U) := by
    funext t
    have hc : IsBondForm complexLieAlgebra (((t * ξ : ℝ) : ℂ) • A) :=
      ⟨fun _ hc => ComplexMatrix2.traceless.smul_mem _ (hAm.1.1 _ hc), fun c => by
        simp only [Pi.smul_apply, hAm.1.2 c, smul_neg]⟩
    have he : expTwist (((t * ξ : ℝ) : ℂ) • A') (transportGaugeField σ U) =
        transportGaugeField σ (expTwist (((t * ξ : ℝ) : ℂ) • A) U) := by
      funext c
      have h := transport_expTwist (b := c) h₇ hH hB hU hcl hc
        (by rw [bondSetImage_univ hB]; exact mem_univ c)
      rw [h, twisted_smul, hTA]
    rw [he]
    exact hact _ (expTwist_isGaugeField hH hcl hU hc)
  rw [hfun] at d₂
  have hfin : plaquetteFormInner ξ (curvature ξ (transportGaugeField σ U))
      (covExteriorDeriv ξ (transportGaugeField σ U) A') =
      plaquetteFormInner ξ (curvature ξ U) (covExteriorDeriv ξ U A) := d₂.unique d₁
  change _ = plaquetteFormInner ξ (curvature ξ (transportGaugeField σ U))
    (covExteriorDeriv ξ (transportGaugeField σ U) A')
  rw [hfin, ← spec.2 A hAm.1, ← hTA]
  exact bondFormInner_twisted hF hL hm hj hH hB hcl hU hJ hAm hξ
theorem mem_boundaryBonds_iff (p : Plaquette L m j) (c : Bond L m j) :
    c ∈ p.boundaryBonds ↔ c = firstEdge p ∨ c = secondEdge p ∨
      c = (thirdEdgeReversed p).opposite ∨ c = (fourthEdgeReversed p).opposite := by
  simp [Plaquette.boundaryBonds, firstEdge, secondEdge, thirdEdgeReversed, fourthEdgeReversed]
def EndsAtVertices (p : Plaquette L m j) (c : Bond L m j) : Prop :=
  c.source ∈ p.vertices ∧ c.target ∈ p.vertices
theorem endsAtVertices_of_mem_boundary {p : Plaquette L m j} {c : Bond L m j}
    (h : c ∈ p.boundaryBonds) : EndsAtVertices p c := by
  rcases (mem_boundaryBonds_iff p c).1 h with rfl | rfl | rfl | rfl
  · exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨Or.inr (Or.inr (Or.inl (add_right_comm _ _ _))), Or.inr (Or.inr (Or.inr rfl))⟩
  · exact ⟨Or.inr (Or.inr (Or.inr rfl)), Or.inl rfl⟩
theorem endsAtVertices_of_hasBond {p : Plaquette L m j} {c : Bond L m j} (h : p.HasBond c) :
    EndsAtVertices p c := by
  rcases h with h | h
  · exact endsAtVertices_of_mem_boundary h
  · exact (endsAtVertices_of_mem_boundary h).symm
theorem meshSize_ne_zero (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : -(m : ℤ) < j) :
    ((meshSize L j : ℝ) : AddCircle (torusSide L m)) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h
  have hL1 : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have hs : 0 < meshSize L j := zpow_pos (by linarith) _
  have hp : 0 < torusSide L m := by
    unfold torusSide
    positivity
  have hlt : meshSize L j < torusSide L m := by
    have h₁ : (L : ℝ) ^ (-j) ≤ (L : ℝ) ^ (m : ℤ) := zpow_le_zpow_right₀ hL1 (by omega)
    rw [zpow_natCast] at h₁
    have h₂ : (0 : ℝ) < (L : ℝ) ^ m := by positivity
    unfold meshSize torusSide
    linarith
  rw [zsmul_eq_mul] at hn
  by_cases h1 : 1 ≤ n
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h1
    nlinarith
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast (by omega : n ≤ 0)
    nlinarith
theorem unitStep_apply_self (μ : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      ((meshSize L j : ℝ) : AddCircle (torusSide L m)) := by apply _root_.YangMills.SharedProofs.p39116 <;> assumption
theorem unitStep_apply_of_ne {μ ν : Fin 4} (h : ν ≠ μ) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) ν = 0 := by
  simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h]
theorem ne_unitStep_of_two_coords {w : Site L m j} {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hμ : (w : FourTorus L m) μ ≠ 0) (hν : (w : FourTorus L m) ν ≠ 0) (κ : Fin 4) :
    w ≠ unitStep L m j κ ∧ w ≠ -unitStep L m j κ := by
  have key : ∀ κ' : Fin 4, ((unitStep L m j κ : Site L m j) : FourTorus L m) κ' ≠ 0 →
      κ' = κ := by
    intro κ' h
    by_contra hne
    exact h (unitStep_apply_of_ne hne)
  constructor
  · rintro rfl
    exact hμν ((key μ hμ).trans (key ν hν).symm)
  · rintro rfl
    have h₁ : ((unitStep L m j κ : Site L m j) : FourTorus L m) μ ≠ 0 :=
      fun h => hμ (by simp [h])
    have h₂ : ((unitStep L m j κ : Site L m j) : FourTorus L m) ν ≠ 0 :=
      fun h => hν (by simp [h])
    exact hμν ((key μ h₁).trans (key ν h₂).symm)
theorem hasBond_of_endsAtVertices (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : -(m : ℤ) < j) {p : Plaquette L m j} {c : Bond L m j} (h : EndsAtVertices p c) :
    p.HasBond c := by
  have ha := meshSize_ne_zero (L := L) (m := m) (j := j) hL hj
  have hμν : p.firstAxis ≠ p.secondAxis := p.firstAxis_lt_secondAxis.ne
  set x := p.origin with hx
  set u := unitStep L m j p.firstAxis with hu
  set v := unitStep L m j p.secondAxis with hv
  have hu₁ : (u : FourTorus L m) p.firstAxis = ((meshSize L j : ℝ) : AddCircle (torusSide L m)) :=
    unitStep_apply_self _
  have hu₂ : (u : FourTorus L m) p.secondAxis = 0 := unitStep_apply_of_ne hμν.symm
  have hv₁ : (v : FourTorus L m) p.firstAxis = 0 := unitStep_apply_of_ne hμν
  have hv₂ : (v : FourTorus L m) p.secondAxis =
      ((meshSize L j : ℝ) : AddCircle (torusSide L m)) := unitStep_apply_self _
  have bad₀ : c.target - c.source ≠ 0 := by
    intro h0
    obtain ⟨κ, hκ | hκ⟩ := c.isNeighbour
    · rw [h0] at hκ
      have := congrArg (fun w : Site L m j => (w : FourTorus L m) κ) hκ
      simp only [unitStep_apply_self] at this
      exact ha (by simpa using this.symm)
    · rw [h0] at hκ
      have := congrArg (fun w : Site L m j => (w : FourTorus L m) κ) hκ
      simp only [AddSubgroup.coe_neg, Pi.neg_apply, unitStep_apply_self] at this
      exact ha (by simpa using this.symm)
  have bad : ∀ w : Site L m j, (w : FourTorus L m) p.firstAxis ≠ 0 →
      (w : FourTorus L m) p.secondAxis ≠ 0 → c.target - c.source ≠ w := by
    intro w h₁ h₂ hw
    obtain ⟨κ, hκ | hκ⟩ := c.isNeighbour
    · exact (ne_unitStep_of_two_coords hμν h₁ h₂ κ).1 (hw ▸ hκ)
    · exact (ne_unitStep_of_two_coords hμν h₁ h₂ κ).2 (hw ▸ hκ)
  have bpp : c.target - c.source ≠ u + v :=
    bad _ (by simp [hu₁, hv₁, ha]) (by simp [hu₂, hv₂, ha])
  have bnn : c.target - c.source ≠ -(u + v) :=
    bad _ (by simp [hu₁, hv₁, ha]) (by simp [hu₂, hv₂, ha])
  have bpn : c.target - c.source ≠ u - v :=
    bad _ (by simp [hu₁, hv₁, ha]) (by simp [hu₂, hv₂, ha])
  have bnp : c.target - c.source ≠ v - u :=
    bad _ (by simp [hu₁, hv₁, ha]) (by simp [hu₂, hv₂, ha])
  have left : ∀ d : Bond L m j, (d = firstEdge p ∨ d = secondEdge p ∨
      d = (thirdEdgeReversed p).opposite ∨ d = (fourthEdgeReversed p).opposite) →
      d ∈ p.boundaryBonds := fun d hd => (mem_boundaryBonds_iff p d).2 hd
  obtain ⟨ht, hh⟩ := h
  rcases ht with ht | ht | ht | ht <;> rcases hh with hh | hh | hh | hh
  · exact absurd (by rw [ht, hh]; abel) bad₀
  · exact Or.inl (left _ (Or.inl (Bond.ext ht hh)))
  · exact absurd (by rw [ht, hh]; abel) bpp
  · exact Or.inr (left _ (Or.inr (Or.inr (Or.inr (Bond.ext hh ht)))))
  · exact Or.inr (left _ (Or.inl (Bond.ext hh ht)))
  · exact absurd (by rw [ht, hh]; abel) bad₀
  · exact Or.inl (left _ (Or.inr (Or.inl (Bond.ext ht hh))))
  · exact absurd (by rw [ht, hh]; abel) bnp
  · exact absurd (by rw [ht, hh]; abel) bnn
  · exact Or.inr (left _ (Or.inr (Or.inl (Bond.ext hh ht))))
  · exact absurd (by rw [ht, hh]; abel) bad₀
  · exact Or.inl (left _ (Or.inr (Or.inr (Or.inl
      (Bond.ext (ht.trans (add_right_comm _ _ _)) hh)))))
  · exact Or.inl (left _ (Or.inr (Or.inr (Or.inr (Bond.ext ht hh)))))
  · exact absurd (by rw [ht, hh]; abel) bpn
  · exact Or.inr (left _ (Or.inr (Or.inr (Or.inl
      (Bond.ext (hh.trans (add_right_comm _ _ _)) ht)))))
  · exact absurd (by rw [ht, hh]; abel) bad₀
theorem bondImage_mem_currentDomain (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : -(m : ℤ) < j) (hc : PreservesCells σ j) (hc' : PreservesCells σ.symm j)
    (hB : PullbackData σ j) (hℬ : IsReversalClosed ℬ) (hb : b ∈ currentDomain ℬ) :
    bondImage σ b ∈ currentDomain (bondSetTransport σ ℬ) := by
  intro p' hp' c' hc'b
  have hcor : ∀ x : Site L m j, x ∈ (plaquetteImage σ.symm p').vertices ↔
      siteImage σ x ∈ p'.vertices := by
    intro x
    have h := hc'.2.2.2.2.2.1 p'
    constructor
    · intro hx
      have h₁ : (x : FourTorus L m) ∈ (fun y : Site L m j => (y : FourTorus L m)) ''
          (plaquetteImage σ.symm p').vertices := ⟨x, hx, rfl⟩
      rw [h] at h₁
      obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := h₁
      have : siteImage σ x = y := by
        apply Subtype.ext
        rw [hc.1, ← hxy]
        simp
      rwa [this]
    · intro hx
      have h₁ : (x : FourTorus L m) ∈ σ.symm '' ((fun y : Site L m j => (y : FourTorus L m)) ''
          p'.vertices) := ⟨_, ⟨_, hx, rfl⟩, by simp [hc.1]⟩
      rw [← h] at h₁
      obtain ⟨y, hy, hxy⟩ := h₁
      have : y = x := Subtype.ext hxy
      rwa [← this]
  have hends : ∀ d : Bond L m j, EndsAtVertices (plaquetteImage σ.symm p') d ↔
      EndsAtVertices p' (bondImage σ d) := by
    intro d
    unfold EndsAtVertices
    rw [(hc.2.2.2.1 d).1, (hc.2.2.2.1 d).2, hcor, hcor]
  have hq : plaquetteImage σ.symm p' ∈ plaquettesThrough b :=
    hasBond_of_endsAtVertices hL hj ((hends b).2 (endsAtVertices_of_hasBond hp'))
  have hcarry := hb _ hq
  rw [mem_bondSetImage_iff hB]
  have he : EndsAtVertices p' (bondImage σ (bondPreimage σ c')) := by
    rw [hB.image_preimage]
    exact endsAtVertices_of_mem_boundary hc'b
  rcases hasBond_of_endsAtVertices hL hj ((hends _).2 he) with h | h
  · exact hcarry _ h
  · have := hℬ _ (hcarry _ h)
    rwa [opposite_opposite] at this
theorem currentDomain_bondSetImage (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : -(m : ℤ) < j) (hc : PreservesCells σ j) (hc' : PreservesCells σ.symm j)
    (hB : PullbackData σ j) (hℬ : IsReversalClosed ℬ) :
    currentDomain (bondSetTransport σ ℬ) = bondSetTransport σ (currentDomain ℬ) := by
  have hB' := hB.symm hB.image_opposite
  ext c
  constructor
  · intro h
    have h₁ := bondImage_mem_currentDomain hL hj hc' hc hB'
      (bondSetImage_reversalClosed hB hℬ) h
    rw [bondSetImage_symm_image hB] at h₁
    exact ⟨_, h₁, hB.image_preimage c⟩
  · rintro ⟨d, hd, rfl⟩
    exact bondImage_mem_currentDomain hL hj hc hc' hB hℬ hd
theorem mem_of_mem_currentDomain (hH : OrientationDichotomy L m j) (hℬ : IsReversalClosed ℬ)
    (hb : b ∈ currentDomain ℬ) : b ∈ ℬ := by
  have key : ∀ d : Bond L m j, d.IsPositivelyOriented → (d = b ∨ d = b.opposite) → b ∈ ℬ := by
    intro d hd hdb
    obtain ⟨p, hp⟩ := Bond.exists_plaquette_containsBond hd
    have hcon : p.HasBond b := by
      rcases hdb with rfl | rfl
      · exact hp
      · rcases hp with h | h
        · exact Or.inr h
        · rw [opposite_opposite] at h
          exact Or.inl h
    have hcarry := hb p hcon
    rcases hcon with h | h
    · exact hcarry _ h
    · have := hℬ _ (hcarry _ h)
      rwa [opposite_opposite] at this
  by_cases hp : b.IsPositivelyOriented
  · exact key b hp (Or.inl rfl)
  · exact key _ ((opposite_positive_iff hH b).2 hp) (Or.inr rfl)
theorem transport_extendByOne (hB : PullbackData σ j) (ℬ : Set (Bond L m j))
    (V : Bond L m j → ComplexMatrix2) :
    transportGaugeField σ (extendByOne ℬ V) =
      extendByOne (bondSetTransport σ ℬ) (transportGaugeField σ V) := by
  classical
  funext c
  change extendByOne ℬ V (bondPreimage σ c) = _
  unfold extendByOne
  by_cases hc : bondPreimage σ c ∈ ℬ
  · rw [if_pos hc, if_pos ((mem_bondSetImage_iff hB).2 hc)]
    rfl
  · rw [if_neg hc, if_neg fun h => hc ((mem_bondSetImage_iff hB).1 h)]
theorem extendByOne_isGaugeField (hℬ : IsReversalClosed ℬ)
    (hV : IsGaugeField complexGaugeGroup ℬ V) :
    IsGaugeField complexGaugeGroup univ (extendByOne ℬ V) := by
  classical
  refine ⟨fun c _ => ?_, fun c _ => ?_⟩
  · unfold extendByOne
    by_cases hc : c ∈ ℬ
    · rw [if_pos hc]
      exact hV.1 c hc
    · rw [if_neg hc]
      exact Matrix.det_one
  · unfold extendByOne
    by_cases hc : c ∈ ℬ
    · rw [if_pos hc, if_pos (hℬ c hc)]
      exact hV.2 c hc
    · have hr : c.opposite ∉ ℬ := fun h => hc (by simpa [opposite_opposite] using hℬ _ h)
      rw [if_neg hc, if_neg hr]
      simp
theorem extendByOne_of_mem (hc : b ∈ ℬ) : extendByOne ℬ V b = V b := by
  classical
  unfold extendByOne
  rw [if_pos hc]
theorem yangMillsCurrent_extend_transport (hF : LieInnerProduct.PeriodicLatticePairings)
    (h₇ : ComplexMatrix2.OperatorNormUnderConjugation)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) < j)
    (hH : OrientationDichotomy L m j) (hB : PullbackData σ j)
    (hact : ∀ U : Bond L m j → ComplexMatrix2, IsGaugeField complexGaugeGroup univ U →
      totalEnergy (transportGaugeField σ U) = totalEnergy U)
    (hℬ : IsReversalClosed ℬ) (hV : IsGaugeField complexGaugeGroup ℬ V)
    {ξ : ℝ} (hξ : 0 < ξ) (hb : b ∈ currentDomain (bondSetTransport σ ℬ)) :
    yangMillsCurrent ξ (extendByOne (bondSetTransport σ ℬ) (transportGaugeField σ V)) b =
      twistedTransportForm σ V (yangMillsCurrent ξ (extendByOne ℬ V)) b := by
  have hm' := (mem_bondSetImage_iff hB).1
    (mem_of_mem_currentDomain hH (bondSetImage_reversalClosed hB hℬ) hb)
  rw [← transport_extendByOne hB, yangMillsCurrent_transport hF h₇ hL hm hj hH hB hact
    (extendByOne_isGaugeField hℬ hV) hξ]
  exact twisted_congr hB rfl rfl (extendByOne_of_mem hm') (extendByOne_of_mem (hℬ _ hm'))
end Forms
section Actions
variable {σ : FourTorus L m ≃ FourTorus L m} {A : Bond L m j → ComplexMatrix2} {b : Bond L m j}
theorem mem_bondsInside_of_boundary {X : Set (FourTorus L m)} {p : Plaquette L m j}
    (hp : p ∈ (plaquettesInside X : Set (Plaquette L m j))) {c : Bond L m j}
    (hc : c ∈ p.boundaryBonds) : c ∈ (bondsInside X : Set (Bond L m j)) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.boundaryBonds_mem_bondsInside <;> assumption
theorem plaquetteHolonomy_congr {U U' : Bond L m j → ComplexMatrix2} {p : Plaquette L m j}
    (h : ∀ c ∈ p.boundaryBonds, U c = U' c) : plaquetteHolonomy U p = plaquetteHolonomy U' p := by apply _root_.YangMills.Construction.PeriodicLattice.CentredAverageSmallFields.plaquetteHolonomy_congr <;> assumption
theorem interiorEnergy_congr {X : Set (FourTorus L m)} {U U' : Bond L m j → ComplexMatrix2}
    (h : ∀ c ∈ (bondsInside X : Set (Bond L m j)), U c = U' c) :
    interiorEnergy X U = interiorEnergy X U' := by
  unfold interiorEnergy
  refine finsum_mem_congr rfl fun p hp => ?_
  unfold plaquetteEnergy
  rw [plaquetteHolonomy_congr fun c hc => h c (mem_bondsInside_of_boundary hp hc)]
theorem actionInside_congr {K : ℕ} {X : Set (FourTorus L m)}
    {U U' : BondAtLevel L m K 0 → ComplexMatrix2}
    (h : ∀ c ∈ (bondsInside X : Set (BondAtLevel L m K 0)), U c = U' c) :
    actionInside K X U = actionInside K X U' := by
  unfold actionInside
  refine finsum_mem_congr rfl fun p hp => ?_
  unfold plaquetteCost
  rw [plaquetteHolonomy_congr fun c hc => h c (mem_bondsInside_of_boundary hp hc)]
theorem matExp_mem_compactGaugeGroup {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ compactGaugeGroup := by
  refine SpinHarmonics.matExp_mem_of_skewAdjoint ?_ ?_
  · have h : star X = X := by
      rw [Matrix.star_eq_conjTranspose]
      exact hX.1.symm
    rw [star_smul, h]
    simp
  · have h : ComplexMatrix2.fullTrace X = 0 := hX.2
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul] at h ⊢
    rw [h, mul_zero]
theorem expTwist_isGaugeField_compact {V : Bond L m j → ComplexMatrix2} {ℬ : Set (Bond L m j)}
    (hH : OrientationDichotomy L m j) (hℬ : IsReversalClosed ℬ)
    (hV : IsGaugeField compactGaugeGroup ℬ V) (hA : IsBondForm compactLieAlgebra A) :
    IsGaugeField compactGaugeGroup ℬ (expTwist A V) := by
  have hA' : IsBondForm complexLieAlgebra A := ⟨fun c hc => (hA.1 c hc).2, hA.2⟩
  refine ⟨fun c hc => ?_,
    (expTwist_isGaugeField hH hℬ (isGaugeField_complex_of_compact hV) hA').2⟩
  by_cases hp : c.IsPositivelyOriented
  · rw [expTwist_of_pos hp]
    exact ComplexMatrix2.specialUnitary.mul_mem (matExp_mem_compactGaugeGroup (hA.1 c hp)) (hV.1 c hc)
  · rw [expTwist_of_not_pos hp]
    have hr := (opposite_positive_iff hH c).2 hp
    exact inv_mem_compactGaugeGroup (ComplexMatrix2.specialUnitary.mul_mem
      (matExp_mem_compactGaugeGroup (hA.1 _ hr)) (hV.1 _ (hℬ c hc)))
end Actions
section Hessians
variable {K : ℕ} {σ : FourTorus L m ≃ FourTorus L m} {Ω₀ : Set (FourTorus L m)}
  {ℬ : Set (BondAtLevel L m K 0)}
theorem wilsonHessian_transport (h₇ : ComplexMatrix2.OperatorNormUnderConjugation)
    (hH : OrientationDichotomy L m (levelDepth K 0)) (hB : PullbackData σ (levelDepth K 0))
    (hinner : (bondsInside (σ '' Ω₀) : Set (BondAtLevel L m K 0)) =
      bondImage σ '' bondsInside Ω₀)
    (hsub : bondsInside Ω₀ ⊆ ℬ) (hℬ : IsReversalClosed ℬ)
    (hreal : ∀ U : BondAtLevel L m K 0 → ComplexMatrix2,
      IsGaugeField compactGaugeGroup (bondsInside Ω₀) U →
      actionInside K (σ '' Ω₀) (transportGaugeField σ U) = actionInside K Ω₀ U)
    {ξ : ℝ} {V₀ A : BondAtLevel L m K 0 → ComplexMatrix2}
    (hV : IsGaugeField compactGaugeGroup ℬ V₀) (hA : A ∈ realFormsOn ℬ) :
    wilsonHessian ξ K (σ '' Ω₀) (transportGaugeField σ V₀) (twistedTransportForm σ V₀ A) =
      wilsonHessian ξ K Ω₀ V₀ A := by
  unfold wilsonHessian
  congr 1
  funext t
  have hreal' : IsBondForm compactLieAlgebra (((t * ξ : ℝ) : ℂ) • A) := by
    refine ⟨fun c hc => ?_, fun c => ?_⟩
    · change ((t * ξ : ℝ) : ℂ) • A c ∈ ComplexMatrix2.hermitianTraceless
      rw [Complex.coe_smul]
      exact ComplexMatrix2.hermitianTraceless.smul_mem _ (hA.1.1 c hc)
    · simp only [Pi.smul_apply, hA.1.2 c, smul_neg]
  have hcomplex : IsBondForm complexLieAlgebra (((t * ξ : ℝ) : ℂ) • A) :=
    ⟨fun c hc => (hreal'.1 c hc).2, hreal'.2⟩
  have hE := expTwist_isGaugeField_compact hH hℬ hV hreal'
  rw [← hreal _ ⟨fun c hc => hE.1 c (hsub hc), fun c hc => hE.2 c (hsub hc)⟩]
  refine actionInside_congr fun c hc => ?_
  rw [← twisted_smul]
  refine (transport_expTwist h₇ hH hB (isGaugeField_complex_of_compact hV) hℬ hcomplex ?_).symm
  rw [hinner] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  exact ⟨d, hsub hd, rfl⟩
theorem regionEnergyHessian_transport (h₇ : ComplexMatrix2.OperatorNormUnderConjugation)
    (hH : OrientationDichotomy L m (levelDepth K 0)) (hB : PullbackData σ (levelDepth K 0))
    (hinner : (bondsInside (σ '' Ω₀) : Set (BondAtLevel L m K 0)) =
      bondImage σ '' bondsInside Ω₀)
    (hsub : bondsInside Ω₀ ⊆ ℬ) (hℬ : IsReversalClosed ℬ)
    (hcx : ∀ U ∈ complexGaugeFields (bondsInside Ω₀ : Set (BondAtLevel L m K 0)),
      interiorEnergy (σ '' Ω₀) (transportGaugeField σ U) = interiorEnergy Ω₀ U)
    (k : ℕ) {U A₁ A₂ : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup ℬ U)
    (h₁ : A₁ ∈ complexFormsOn ℬ) (h₂ : A₂ ∈ complexFormsOn ℬ) :
    regionEnergyHessian k (σ '' Ω₀) (transportGaugeField σ U)
        (twistedTransportForm σ U A₁) (twistedTransportForm σ U A₂) =
      regionEnergyHessian k Ω₀ U A₁ A₂ := by
  have key : ∀ s s' : ℝ,
      interiorEnergy (σ '' Ω₀) (bareTwist k ((s : ℂ) • twistedTransportForm σ U A₁ +
        (s' : ℂ) • twistedTransportForm σ U A₂) (transportGaugeField σ U)) =
      interiorEnergy Ω₀ (bareTwist k ((s : ℂ) • A₁ + (s' : ℂ) • A₂) U) := by
    intro s s'
    set c : ℂ := ((finestMeshInLevelUnits L k : ℝ) : ℂ) with hc
    have hC : IsBondForm complexLieAlgebra (c • ((s : ℂ) • A₁ + (s' : ℂ) • A₂)) := by
      refine ⟨fun d hd => ?_, fun d => ?_⟩
      · exact ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.add_mem
          (ComplexMatrix2.traceless.smul_mem _ (h₁.1.1 d hd))
          (ComplexMatrix2.traceless.smul_mem _ (h₂.1.1 d hd)))
      · simp only [Pi.smul_apply, Pi.add_apply, h₁.1.2 d, h₂.1.2 d, smul_neg, smul_add, neg_add]
    have hE := expTwist_isGaugeField hH hℬ hU hC
    have hW : bareTwist k ((s : ℂ) • A₁ + (s' : ℂ) • A₂) U ∈
        complexGaugeFields (bondsInside Ω₀ : Set (BondAtLevel L m K 0)) :=
      ⟨fun d hd => hE.1 d (hsub hd), fun d hd => hE.2 d (hsub hd)⟩
    rw [← hcx _ hW]
    refine interiorEnergy_congr fun d hd => ?_
    have hT : (fun b => c • ((s : ℂ) • twistedTransportForm σ U A₁ +
        (s' : ℂ) • twistedTransportForm σ U A₂) b) =
        twistedTransportForm σ U (c • ((s : ℂ) • A₁ + (s' : ℂ) • A₂)) := by
      rw [twisted_smul, twisted_add, twisted_smul, twisted_smul]
      rfl
    unfold bareTwist
    rw [← hc, hT]
    refine (transport_expTwist h₇ hH hB hU hℬ hC ?_).symm
    rw [hinner] at hd
    obtain ⟨e, he, rfl⟩ := hd
    exact ⟨e, hsub he, rfl⟩
  unfold regionEnergyHessian
  congr 1
  funext s
  congr 1
  funext s'
  exact key s s'
end Hessians
end TwistedTransport
open TwistedTransport in
theorem twistedTransportIsometryInvariance_holds
    (h₁ : LatticeIsometryGroupActionStatement)
    (h₂ : IsometriesPreserveCells)
    (h₃ : IsometryCovariance.Statement)
    (h₄ : ComplexEnergiesIsometryInvariant)
    (h₅ : BondOrientationDichotomy)
    (h₆ : LieInnerProduct.Statement)
    (h₇ : ComplexMatrix2.OperatorNormUnderConjugation) :
    TwistedTransportIsometryInvariance := by
  obtain ⟨ε, h₃⟩ := h₃
  intro L m i σ hL hm hi hσ
  have hg := h₁ L m i hL hm hi
  have hσ' : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨⟨H, hH⟩, -⟩ := hg.1
    have t : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    have t' := H.inv_mem t
    rw [← hH]
    exact t'
  have hC : ∀ j : ℤ, i ≤ j → PreservesCells σ j :=
    fun j hj => h₂ L m i j σ hL hm hi hσ hj
  have hC' : ∀ j : ℤ, i ≤ j → PreservesCells σ.symm j :=
    fun j hj => h₂ L m i j σ.symm hL hm hi hσ' hj
  have hBM : ∀ j : ℤ, i ≤ j → PullbackData σ j :=
    fun j hj => PullbackData.of_preservesCells (hC j hj) (hC' j hj)
  have hF := h₆.2.2.2.2.2.2.2
  have hN := h₆.1.2.2.2
  have hact : ∀ j : ℤ, i ≤ j → ∀ U : Bond L m j → ComplexMatrix2,
      IsGaugeField complexGaugeGroup univ U →
      totalEnergy (transportGaugeField σ U) = totalEnergy U := by
    intro j hj U hU
    have h := (h₄ L m i σ hL hm hi hσ j hj).2.1 (fun _ => 1)
    have e : ∀ W : Bond L m j → ComplexMatrix2,
        plaquetteWeightedEnergy (fun _ => (1 : ℂ)) W = totalEnergy W := by
      intro W
      simp [plaquetteWeightedEnergy, totalEnergy]
    have h' := h.2.2.1 U ⟨hU, hU⟩
    change plaquetteWeightedEnergy (fun _ => (1 : ℂ)) _ =
      plaquetteWeightedEnergy (fun _ => (1 : ℂ)) _ at h'
    rwa [e, e] at h'
  refine ⟨fun hlin j hjm hij b hb => ?_, fun j hij ℬ hℬ U => ?_,
    fun j hjm hij ℬ hℬ => ?_, fun K hK hiK i' hii' hi'K Ω₀ hreg ℬ hℬ hsub => ?_⟩
  · rcases hlin with hl | ⟨π, hl⟩
    · exact bondImage_isPositive (π := 1) hl (hC j hij) hb
    · exact bondImage_isPositive hl (hC j hij) hb
  · exact ⟨fun h => transport_isGaugeField (hBM j hij) h,
      fun h => transport_isGaugeField (hBM j hij) h⟩
  · have hH : OrientationDichotomy L m j := h₅ L m hL hm j hjm
    have hB := hBM j hij
    refine ⟨fun A hA => twisted_trivial hH hB hA.1.2,
      fun hp V₀ A hA => twisted_eq_transportForm hH hB hp hA.1.2,
      fun V₀ hV => ?_, fun V₀ hV => ?_⟩
    · exact
        { transport_expTwist := fun A hA b' hb' => transport_expTwist h₇ hH hB hV hℬ hA.1 hb'
          map_add := fun A _ B _ => twisted_add A B
          map_smul := fun c A _ => twisted_smul c A
          bijOn := twisted_bijOn hH hB hℬ hV
          inner_eq := fun ξ hξ A hA B hB' =>
            bondFormInner_twisted hF hL hm hjm hH hB hℬ hV hA hB' hξ
          currentDomain_image := currentDomain_bondSetImage hL hjm (hC j hij) (hC' j hij) hB hℬ
          current_transport := fun ξ hξ b' hb' =>
            yangMillsCurrent_extend_transport hF h₇ hL hm hjm hH hB (hact j hij) hℬ hV hξ hb' }
    · have hfin : Finite (Bond L m j) := by
        obtain ⟨h₈, -⟩ := hF L m j 1 hL hm hjm one_pos
        exact Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun b b' hb =>
          Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
      exact
        { bijOn := twisted_bijOn_real hH hB hℬ hV
          inner_eq := fun ξ hξ A hA B hB' =>
            bondFormInner_twisted hF hL hm hjm hH hB hℬ (isGaugeField_complex_of_compact hV)
              (mem_complexFormsOn_of_real hA) (mem_complexFormsOn_of_real hB') hξ
          operatorNorm_eq := fun A hA b hb => operatorNorm_twisted_image h₇ hH hB hℬ hV hA.1.2 hb
          measurePreserving := exists_measurePreserving_twisted hN h₇ hfin hH hB hℬ hV }
  · have hH : OrientationDichotomy L m (levelDepth K 0) := h₅ L m hL hm _ hK
    have hB := hBM _ hiK
    have hinner : (bondsInside (σ '' Ω₀) : Set (BondAtLevel L m K 0)) =
        bondImage σ '' bondsInside Ω₀ := ((hC _ hiK).2.2.2.2.2.2 Ω₀).2.2
    exact
      { wilson := fun ξ _ V₀ hV A hA => wilsonHessian_transport h₇ hH hB hinner hsub hℬ
          (fun U hU => (h₃ L m hL hm i hi σ hσ).2 K i' Ω₀ U hiK hii' hreg hU) hV hA
        regionEnergy := fun k U hU A₁ h₁' A₂ h₂' =>
          regionEnergyHessian_transport h₇ hH hB hinner hsub hℬ
            (fun W hW => ((h₄ L m i σ hL hm hi hσ _ hiK).1 i' Ω₀ hii' hreg).2.2.1 W ⟨hW, hW⟩)
            k hU h₁' h₂' }
end PeriodicLattice
end YangMills.Construction
