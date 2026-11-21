import YangMills.Construction.Lattice.CovarianceOfComplexAveragingOfDeterminingSetsProof
import YangMills.Construction.Lattice.CovarianceOfFormsAtComplexConfigurations
import YangMills.Construction.Lattice.LinearisedConstraintAtAFormedBond
import YangMills.Construction.Lattice.OneStepIdentitiesAtAnImageBond
import YangMills.Construction.Lattice.SeriesLogarithmOnTheComplexGroup
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
namespace TransportAtImageBond
open ComplexTransport
variable {L m : ℕ} {j : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := Bond.ext rfl rfl
theorem positivelyOriented_eq_self {b : Bond L m j} (hb : b.IsPositivelyOriented) :
    b.positivelyOriented = b :=
  if_pos hb
theorem bondPreimage_bondImage (hc : PreservesCells σ j) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexDeterminingAveragingCovariance.bondPreimage_bondImage <;> assumption
theorem twistedFormValue_smul (t : ℂ) (V A : Bond L m j → ComplexMatrix2) (b' : Bond L m j) :
    twistedFormValue σ V (t • A) b' = t • twistedFormValue σ V A b' := by
  unfold twistedFormValue
  split_ifs
  · rfl
  · simp [ComplexMatrix2.conjugateBy, Pi.smul_apply]
theorem twistedTransportForm_smul (t : ℂ) (V A : Bond L m j → ComplexMatrix2) :
    twistedTransportForm σ V (t • A) = t • twistedTransportForm σ V A := by
  funext b'
  simp only [twistedTransportForm, Pi.smul_apply]
  split_ifs
  · exact twistedFormValue_smul t V A b'
  · rw [twistedFormValue_smul, smul_neg]
theorem twistedTransportForm_add (V A A' : Bond L m j → ComplexMatrix2) :
    twistedTransportForm σ V (A + A') =
      twistedTransportForm σ V A + twistedTransportForm σ V A' := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.twisted_add <;> assumption
theorem isBondForm_smul (t : ℂ) {A : Bond L m j → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A) : IsBondForm complexLieAlgebra (t • A) :=
  ⟨fun b hb => ComplexMatrix2.traceless.smul_mem t (hA.1 b hb), fun b => by
    simp only [Pi.smul_apply, hA.2 b, smul_neg]⟩
theorem isBondForm_add {A A' : Bond L m j → ComplexMatrix2} (hA : IsBondForm complexLieAlgebra A)
    (hA' : IsBondForm complexLieAlgebra A') : IsBondForm complexLieAlgebra (A + A') :=
  ⟨fun b hb => ComplexMatrix2.traceless.add_mem (hA.1 b hb) (hA'.1 b hb), fun b => by
    simp only [Pi.add_apply, hA.2 b, hA'.2 b, neg_add]⟩
theorem isBondForm_twistedTransportForm
    (hX : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (V : Bond L m j → ComplexMatrix2) {A : Bond L m j → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A) :
    IsBondForm complexLieAlgebra (twistedTransportForm σ V A) := by
  have hv : ∀ b', twistedFormValue σ V A b' ∈ complexLieAlgebra := by
    intro b'
    unfold twistedFormValue
    split_ifs with h
    · exact hA.1 _ h
    · have hp : (bondPreimage σ b').opposite.IsPositivelyOriented := by
        rcases hX (bondPreimage σ b') with h' | h'
        · exact absurd h'.1 h
        · exact h'.1
      exact ComplexMatrix2.traceless.neg_mem
        (conjugationLinearMap (V (bondPreimage σ b').opposite)⁻¹ ⟨_, hA.1 _ hp⟩).2
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [twistedTransportForm, if_pos hb]
    exact hv b
  · simp only [twistedTransportForm]
    rcases hX b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [if_neg h₂, if_pos h₁, opposite_opposite]
    · rw [if_pos h₁, if_neg h₂, neg_neg]
theorem singleBondForm_self (b : Bond L m j) (Y : ComplexMatrix2) : singleBondForm b Y b = Y := by
  simp only [singleBondForm, if_true]
theorem singleBondForm_of_ne {b d : Bond L m j} (Y : ComplexMatrix2) (h₁ : d ≠ b)
    (h₂ : d ≠ b.opposite) : singleBondForm b Y d = 0 := by
  simp only [singleBondForm, if_neg h₁, if_neg h₂]
theorem singleBondForm_opposite {b : Bond L m j} (hne : b.opposite ≠ b) (Y : ComplexMatrix2)
    (d : Bond L m j) : singleBondForm b Y d.opposite = -singleBondForm b Y d := by
  by_cases h₁ : d = b
  · rw [h₁, singleBondForm_self]
    simp only [singleBondForm, if_neg hne, if_true]
  · by_cases h₂ : d = b.opposite
    · rw [h₂, opposite_opposite, singleBondForm_self]
      simp only [singleBondForm, if_neg hne, if_true, neg_neg]
    · have h₃ : d.opposite ≠ b := fun h => h₂ (by rw [← h, opposite_opposite])
      have h₄ : d.opposite ≠ b.opposite := fun h => h₁ (by
        rw [← opposite_opposite d, h, opposite_opposite])
      rw [singleBondForm_of_ne Y h₃ h₄, singleBondForm_of_ne Y h₁ h₂, neg_zero]
theorem isBondForm_singleBondForm {b : Bond L m j} (hne : b.opposite ≠ b)
    (X : ↥ComplexMatrix2.traceless) :
    IsBondForm complexLieAlgebra (singleBondForm b (X : ComplexMatrix2)) := by
  refine ⟨fun d _ => ?_, fun d => singleBondForm_opposite hne _ d⟩
  simp only [singleBondForm]
  split_ifs
  · exact X.2
  · exact ComplexMatrix2.traceless.neg_mem X.2
  · exact ComplexMatrix2.traceless.zero_mem
theorem twistedTransportForm_singleBondForm (hc : PreservesCells σ j)
    (hX : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (V : Bond L m j → ComplexMatrix2)
    {b b' : Bond L m j} (hb : b.IsPositivelyOriented) (hb' : b'.IsPositivelyOriented)
    (hbb : b' = bondImage σ b ∨ b' = (bondImage σ b).opposite) (X : ↥ComplexMatrix2.traceless) :
    twistedTransportForm σ V (singleBondForm b (X : ComplexMatrix2)) =
      singleBondForm b' ((twistedLinkMap σ V b X : ↥ComplexMatrix2.traceless) : ComplexMatrix2) := by
  have hinj : Function.Injective (bondImage σ : Bond L m j → Bond L m j) := hc.2.2.1.1
  have hsurj : Function.Surjective (bondImage σ : Bond L m j → Bond L m j) := hc.2.2.1.2
  have hopp : ∀ e : Bond L m j, bondImage σ e.opposite = (bondImage σ e).opposite :=
    hc.2.2.2.2.1
  have notBoth : ∀ d : Bond L m j, d.IsPositivelyOriented → ¬d.opposite.IsPositivelyOriented :=
    fun d hd => by
      rcases hX d with h | h
      · exact h.2
      · exact absurd hd h.2
  have oneOf : ∀ d : Bond L m j, ¬d.IsPositivelyOriented → d.opposite.IsPositivelyOriented :=
    fun d hd => by
      rcases hX d with h | h
      · exact absurd h.1 hd
      · exact h.1
  have hneb' : b'.opposite ≠ b' := fun h => notBoth b' hb' (h ▸ hb')
  have hpos : ∀ e', e'.IsPositivelyOriented →
      twistedFormValue σ V (singleBondForm b (X : ComplexMatrix2)) e' =
        singleBondForm b' ((twistedLinkMap σ V b X : ↥ComplexMatrix2.traceless) : ComplexMatrix2) e' := by
    intro e' he'
    obtain ⟨e, rfl⟩ := hsurj e'
    unfold twistedFormValue
    rw [bondPreimage_bondImage hc]
    rcases hbb with hbb | hbb
    · have hσ : (bondImage σ b).IsPositivelyOriented := hbb ▸ hb'
      have hZ : ((twistedLinkMap σ V b X : ↥ComplexMatrix2.traceless) : ComplexMatrix2) = X := by
        simp only [twistedLinkMap, if_pos hσ, LinearMap.id_apply]
      rw [hZ, hbb]
      by_cases he : e.IsPositivelyOriented
      · rw [if_pos he]
        by_cases h₁ : e = b
        · rw [h₁, singleBondForm_self, singleBondForm_self]
        · have h₂ : e ≠ b.opposite := fun h => notBoth b hb (h ▸ he)
          have h₃ : bondImage σ e ≠ bondImage σ b := fun h => h₁ (hinj h)
          have h₄ : bondImage σ e ≠ (bondImage σ b).opposite := fun h =>
            notBoth _ hσ (h ▸ he')
          rw [singleBondForm_of_ne _ h₁ h₂, singleBondForm_of_ne _ h₃ h₄]
      · rw [if_neg he]
        have h₁ : e ≠ b := fun h => he (h ▸ hb)
        have h₃ : bondImage σ e ≠ bondImage σ b := fun h => h₁ (hinj h)
        have h₄ : bondImage σ e ≠ (bondImage σ b).opposite := fun h => notBoth _ hσ (h ▸ he')
        have h₅ : e.opposite ≠ b := fun h => h₄ (by rw [← hopp, ← h, opposite_opposite])
        have h₆ : e.opposite ≠ b.opposite := fun h => h₁ (by
          rw [← opposite_opposite e, h, opposite_opposite])
        rw [singleBondForm_of_ne _ h₅ h₆, singleBondForm_of_ne _ h₃ h₄]
        simp [ComplexMatrix2.conjugateBy]
    · have hσ : ¬(bondImage σ b).IsPositivelyOriented := fun h => notBoth _ h (hbb ▸ hb')
      have hZ : ((twistedLinkMap σ V b X : ↥ComplexMatrix2.traceless) : ComplexMatrix2) =
          -ComplexMatrix2.conjugateBy (V b)⁻¹ X := by
        simp only [twistedLinkMap, if_neg hσ, LinearMap.neg_apply]
        rfl
      rw [hZ, hbb]
      by_cases he : e.IsPositivelyOriented
      · rw [if_pos he]
        have h₁ : e ≠ b := fun h => hσ (h ▸ he')
        have h₂ : e ≠ b.opposite := fun h => notBoth b hb (h ▸ he)
        have h₃ : bondImage σ e ≠ (bondImage σ b).opposite := fun h =>
          h₂ (hinj (h.trans (hopp b).symm))
        have h₄ : bondImage σ e ≠ (bondImage σ b).opposite.opposite := fun h =>
          h₁ (hinj (h.trans (opposite_opposite _)))
        rw [singleBondForm_of_ne _ h₁ h₂, singleBondForm_of_ne _ h₃ h₄]
      · rw [if_neg he]
        have h₀ : e ≠ b := fun h => he (h ▸ hb)
        by_cases h₁ : e.opposite = b
        · have h₂ : bondImage σ e = (bondImage σ b).opposite := by
            rw [← hopp, ← h₁, opposite_opposite]
          rw [h₁, h₂, singleBondForm_self, singleBondForm_self]
        · have h₂ : e.opposite ≠ b.opposite := fun h => h₀ (by
            rw [← opposite_opposite e, h, opposite_opposite])
          have h₃ : bondImage σ e ≠ (bondImage σ b).opposite := fun h => h₁ (by
            have : e = b.opposite := hinj (h.trans (hopp b).symm)
            rw [this, opposite_opposite])
          have h₄ : bondImage σ e ≠ (bondImage σ b).opposite.opposite := fun h =>
            h₀ (hinj (h.trans (opposite_opposite _)))
          rw [singleBondForm_of_ne _ h₁ h₂, singleBondForm_of_ne _ h₃ h₄]
          simp [ComplexMatrix2.conjugateBy]
  funext d'
  simp only [twistedTransportForm]
  split_ifs with hd
  · exact hpos d' hd
  · rw [hpos _ (oneOf d' hd), singleBondForm_opposite hneb', neg_neg]
theorem expTwist_congr {S : Set (Bond L m j)} (hS : IsReversalClosed S)
    {A A' : Bond L m j → ComplexMatrix2} (h : ∀ d ∈ S, A d = A' d) (U : Bond L m j → ComplexMatrix2)
    {b : Bond L m j} (hb : b ∈ S) : expTwist A U b = expTwist A' U b := by
  simp only [expTwist]
  split_ifs
  · rw [h b hb]
  · rw [h _ (hS b hb)]
theorem twistedTransportForm_congr (hc : PreservesCells σ j) {P P' : Set (Bond L m j)}
    (hP : IsReversalClosed P) (hP' : IsReversalClosed P') (himg : bondImage σ '' P = P')
    {A A' : Bond L m j → ComplexMatrix2} (h : ∀ d ∈ P, A d = A' d)
    (V : Bond L m j → ComplexMatrix2) :
    ∀ d' ∈ P', twistedTransportForm σ V A d' = twistedTransportForm σ V A' d' := by
  have htv : ∀ e' ∈ P', twistedFormValue σ V A e' = twistedFormValue σ V A' e' := by
    intro e' he'
    rw [← himg] at he'
    obtain ⟨e, he, rfl⟩ := he'
    simp only [twistedFormValue, bondPreimage_bondImage hc]
    split_ifs
    · exact h e he
    · rw [h _ (hP e he)]
  intro d' hd'
  simp only [twistedTransportForm]
  split_ifs
  · exact htv d' hd'
  · rw [htv _ (hP' d' hd')]
theorem transportGaugeField_expTwist (hc : PreservesCells σ j) {P P' : Set (Bond L m j)}
    (hP : IsReversalClosed P) (hP' : IsReversalClosed P') (himg : bondImage σ '' P = P')
    (hE : ComplexTransportIdentities σ P) {V B : Bond L m j → ComplexMatrix2}
    (hV : IsGaugeField complexGaugeGroup P V) (hB : IsBondForm complexLieAlgebra B) :
    ∀ b' ∈ P', transportGaugeField σ (expTwist B V) b' =
      expTwist (twistedTransportForm σ V B) (transportGaugeField σ V) b' := by
  intro b' hb'
  have hb'' := hb'
  rw [← himg] at hb''
  obtain ⟨b, hb, rfl⟩ := hb''
  have hagree : ∀ d ∈ P, P.indicator B d = B d := fun d hd => Set.indicator_of_mem hd B
  have hA₀ : IsComplexBondFormSupportedOn P (P.indicator B) := by
    refine ⟨⟨fun d hd => ?_, fun d => ?_⟩, by simp [Set.indicator_indicator]⟩
    · by_cases h : d ∈ P
      · rw [hagree d h]
        exact hB.1 d hd
      · rw [Set.indicator_of_notMem h]
        exact ComplexMatrix2.traceless.zero_mem
    · by_cases h : d ∈ P
      · rw [hagree d h, hagree _ (hP d h), hB.2 d]
      · have h' : d.opposite ∉ P := fun h' => h (by simpa [opposite_opposite] using hP _ h')
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h', neg_zero]
  have h := hE.exp_transport V hV _ hA₀ b hb
  have l₁ : transportGaugeField σ (expTwist (P.indicator B) V) (bondImage σ b) =
      transportGaugeField σ (expTwist B V) (bondImage σ b) := by
    simp only [transportGaugeField, bondPreimage_bondImage hc]
    exact expTwist_congr hP hagree V hb
  rw [← l₁, h]
  exact expTwist_congr hP' (twistedTransportForm_congr hc hP hP' himg hagree V) _ hb'
def negConjugateEquiv (Y : ComplexMatrix2) (hY : IsUnit Y.det) :
    ComplexMatrix2 ≃ₗ[ℂ] ComplexMatrix2 where
  toFun Z := -ComplexMatrix2.conjugateBy Y Z
  invFun Z := -(Y⁻¹ * Z * Y)
  map_add' A B := by
    simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul, neg_add]
  map_smul' t A := by
    simp [ComplexMatrix2.conjugateBy]
  left_inv Z := by
    simp only [ComplexMatrix2.conjugateBy, mul_neg, neg_mul, neg_neg, mul_assoc,
      Matrix.nonsing_inv_mul _ hY, mul_one]
    simp only [← mul_assoc, Matrix.nonsing_inv_mul _ hY, one_mul]
  right_inv Z := by
    simp only [ComplexMatrix2.conjugateBy, mul_neg, neg_mul, neg_neg, mul_assoc,
      Matrix.mul_nonsing_inv _ hY, mul_one]
    simp only [← mul_assoc, Matrix.mul_nonsing_inv _ hY, one_mul]
theorem exists_linearEquiv_twistedLinkMap (σ : FourTorus L m ≃ FourTorus L m)
    (V₀ : Bond L m j → ComplexMatrix2) (b : Bond L m j) (hu : IsUnit (V₀ b).det) :
    ∃ e : ↥ComplexMatrix2.traceless ≃ₗ[ℂ] ↥ComplexMatrix2.traceless,
      ∀ x, e x = twistedLinkMap σ V₀ b x := by
  by_cases h : (bondImage σ b).IsPositivelyOriented
  · refine ⟨LinearEquiv.refl _ _, fun x => ?_⟩
    simp only [twistedLinkMap, if_pos h, LinearEquiv.refl_apply, LinearMap.id_apply]
  · have hY : IsUnit ((V₀ b)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hu
    refine ⟨LinearEquiv.ofLinearMap (-conjugationLinearMap (V₀ b)⁻¹)
      (-conjugationLinearMap (V₀ b)) ?_ ?_, fun x => ?_⟩
    · refine LinearMap.ext fun x => Subtype.ext ?_
      have := (negConjugateEquiv (V₀ b)⁻¹ hY).right_inv (x : ComplexMatrix2)
      simp only [negConjugateEquiv, Matrix.nonsing_inv_nonsing_inv _ hu] at this
      simpa [conjugationLinearMap, ComplexMatrix2.conjugateBy,
        Matrix.nonsing_inv_nonsing_inv _ hu] using this
    · refine LinearMap.ext fun x => Subtype.ext ?_
      have := (negConjugateEquiv (V₀ b)⁻¹ hY).left_inv (x : ComplexMatrix2)
      simp only [negConjugateEquiv, Matrix.nonsing_inv_nonsing_inv _ hu] at this
      simpa [conjugationLinearMap, ComplexMatrix2.conjugateBy,
        Matrix.nonsing_inv_nonsing_inv _ hu] using this
    · simp only [twistedLinkMap, if_neg h]
      rfl
variable {K k : ℕ}
theorem iteratedDeriv_two_continuousLinearEquiv_comp (T : ComplexMatrix2 ≃L[ℂ] ComplexMatrix2)
    (f : ℂ → ComplexMatrix2) :
    iteratedDeriv 2 (fun t => T (f t)) 0 = T (iteratedDeriv 2 f 0) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have h := T.iteratedFDeriv_comp_left (f := f) (x := (0 : ℂ)) (i := 2)
  have h₂ : (fun t => T (f t)) = T ∘ f := rfl
  rw [h₂, h]
  rfl
theorem linearized_and_bilinear_of_constraintMap {V : BondAtLevel L m K k → ComplexMatrix2}
    {c c' : BondAtLevel L m K (k + 1)} (T : ComplexMatrix2 ≃L[ℂ] ComplexMatrix2) (hL : (L : ℂ) ≠ 0)
    (hF : LinearizedConstraintProperties V c)
    (hF' : LinearizedConstraintProperties (transportGaugeField σ V) c')
    (hform : ∀ A : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra A →
      IsBondForm complexLieAlgebra (twistedTransportForm σ V A))
    (hC : ∀ B : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra B →
      ConstraintMapDefined V B c →
      ConstraintMapDefined (transportGaugeField σ V) (twistedTransportForm σ V B) c' →
      constraintMap (transportGaugeField σ V) (twistedTransportForm σ V B) c' =
        T (constraintMap V B c)) :
    (∀ A : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra A →
      linearizedConstraint (transportGaugeField σ V) (twistedTransportForm σ V A) c' =
        T (linearizedConstraint V A c)) ∧
    ∀ B₁ B₂ : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra B₁ →
      IsBondForm complexLieAlgebra B₂ →
      constraintBilinear (transportGaugeField σ V)
          (twistedTransportForm σ V B₁) (twistedTransportForm σ V B₂) c' =
        T (constraintBilinear V B₁ B₂ c) := by
  have hev : ∀ B : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra B →
      (fun t : ℂ => constraintMap (transportGaugeField σ V)
          (t • twistedTransportForm σ V B) c') =ᶠ[𝓝 0]
        fun t : ℂ => T (constraintMap V (t • B) c) := by
    intro B hB
    filter_upwards [hF.eventually_constraintMapDefined B hB,
      hF'.eventually_constraintMapDefined _ (hform B hB)] with t h₁ h₂
    rw [← twistedTransportForm_smul] at h₂ ⊢
    exact hC (t • B) (isBondForm_smul t hB) h₁ h₂
  have hquad : ∀ B : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra B →
      constraintQuadratic (transportGaugeField σ V) (twistedTransportForm σ V B) c' =
        T (constraintQuadratic V B c) := by
    intro B hB
    simp only [constraintQuadratic]
    rw [(hev B hB).iteratedDeriv_eq 2, iteratedDeriv_two_continuousLinearEquiv_comp, map_smul]
  refine ⟨fun A hA => ?_, fun B₁ B₂ h₁ h₂ => ?_⟩
  · have d₁ := hF'.hasDerivAt_constraintMap _ (hform A hA)
    have d₂ := (T : ComplexMatrix2 →L[ℂ] ComplexMatrix2).hasFDerivAt.comp_hasDerivAt (0 : ℂ)
      (hF.hasDerivAt_constraintMap A hA)
    have d₃ : HasDerivAt (fun t : ℂ => constraintMap (transportGaugeField σ V)
        (t • twistedTransportForm σ V A) c') (T ((L : ℂ) • linearizedConstraint V A c)) 0 :=
      d₂.congr_of_eventuallyEq (hev A hA)
    have h := d₁.unique d₃
    rw [map_smul] at h
    exact smul_right_injective _ hL h
  · simp only [constraintBilinear]
    rw [← twistedTransportForm_add, hquad _ (isBondForm_add h₁ h₂), hquad _ h₁, hquad _ h₂,
      map_smul, map_sub, map_sub]
theorem transportIdentitiesAt_of_constraintMap {V : BondAtLevel L m K k → ComplexMatrix2}
    {W : BondAtLevel L m K (k + 1) → ComplexMatrix2} {c c' : BondAtLevel L m K (k + 1)}
    (cF : PreservesCells σ (levelDepth K k))
    (xF : ∀ b : BondAtLevel L m K k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (T : ComplexMatrix2 ≃L[ℂ] ComplexMatrix2) (hL : (L : ℂ) ≠ 0)
    (hF : LinearizedConstraintProperties V c)
    (hF' : LinearizedConstraintProperties (transportGaugeField σ V) c')
    (hT : ∀ f : BondAtLevel L m K (k + 1) → ComplexMatrix2, twistedFormValue σ W f c' = T (f c))
    (hTO : ∀ Y : ↥ComplexMatrix2.traceless,
      T (Y : ComplexMatrix2) = (twistedLinkMap σ W c Y : ↥ComplexMatrix2.traceless))
    (hC : ∀ B : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra B →
      ConstraintMapDefined V B c →
      ConstraintMapDefined (transportGaugeField σ V) (twistedTransportForm σ V B) c' →
      constraintMap (transportGaugeField σ V) (twistedTransportForm σ V B) c' =
        T (constraintMap V B c))
    (hb₀ : (pivot c : BondAtLevel L m K k).IsPositivelyOriented)
    (hb₀' : (pivot c' : BondAtLevel L m K k).IsPositivelyOriented)
    (hbb : (pivot c' : BondAtLevel L m K k) = bondImage σ (pivot c) ∨
      (pivot c' : BondAtLevel L m K k) = (bondImage σ (pivot c)).opposite)
    (hub : IsUnit (V (pivot c)).det) (huc : IsUnit (W c).det) :
    TransportIdentitiesAt σ V W c c' := by
  obtain ⟨hlin, hbil⟩ := linearized_and_bilinear_of_constraintMap T hL hF hF'
    (fun A hA => isBondForm_twistedTransportForm xF V hA) hC
  have hne : (pivot c : BondAtLevel L m K k).opposite ≠ pivot c := fun h => by
    rcases xF (pivot c) with h' | h'
    · exact h'.2 (h ▸ h'.1)
    · exact h'.2 hb₀
  have hmem : ∀ X : ↥ComplexMatrix2.traceless,
      pivotCoeff V c (X : ComplexMatrix2) ∈ ComplexMatrix2.traceless := fun X =>
    hF.mem_complexLieAlgebra _ (isBondForm_singleBondForm hne X)
  have hpiv : ∀ X : ↥ComplexMatrix2.traceless, pivotCoeff (transportGaugeField σ V) c'
      (twistedLinkMap σ V (pivot c) X : ↥ComplexMatrix2.traceless) =
      (twistedLinkMap σ W c ⟨pivotCoeff V c (X : ComplexMatrix2), hmem X⟩ :
        ↥ComplexMatrix2.traceless) := by
    intro X
    have h := hlin _ (isBondForm_singleBondForm hne X)
    rw [twistedTransportForm_singleBondForm cF xF V hb₀ hb₀' hbb X] at h
    exact h.trans (hTO ⟨_, hmem X⟩)
  obtain ⟨eb, heb⟩ := exists_linearEquiv_twistedLinkMap σ V (pivot c) hub
  obtain ⟨ec, hec⟩ := exists_linearEquiv_twistedLinkMap σ W c huc
  refine
    { linearized := fun A hA => (hlin A hA).trans (hT _).symm
      constraint_map := fun B hB h₁ h₂ => (hC B hB h₁ h₂).trans (hT _).symm
      pivotCoeff_conj := fun X => ⟨⟨_, hmem X⟩, rfl, hpiv X⟩
      invertible_iff := ⟨?_, ?_⟩
      bilinear := fun B₁ B₂ h₁ h₂ => (hbil B₁ B₂ h₁ h₂).trans (hT _).symm }
  · rintro ⟨T₀, hT₀⟩
    refine ⟨(eb.symm.trans T₀).trans ec, fun Z => ?_⟩
    have h₁ : T₀ (eb.symm Z) =
        ⟨pivotCoeff V c (eb.symm Z : ↥ComplexMatrix2.traceless), hmem _⟩ :=
      Subtype.ext (hT₀ _)
    simp only [LinearEquiv.trans_apply]
    rw [h₁, hec, ← hpiv, ← heb, LinearEquiv.apply_symm_apply]
  · rintro ⟨T₁, hT₁⟩
    refine ⟨(eb.trans T₁).trans ec.symm, fun X => ?_⟩
    have h₁ : T₁ (eb X) = ec ⟨pivotCoeff V c (X : ComplexMatrix2), hmem X⟩ :=
      Subtype.ext (by rw [hT₁, heb, hpiv, hec])
    simp only [LinearEquiv.trans_apply, h₁, LinearEquiv.symm_apply_apply]
end TransportAtImageBond
open TransportAtImageBond in
theorem transportIdentitiesAtImageBond_holds
    (hO : BondOrientationDichotomy)
    (hB : IsometriesPreserveCells)
    (hBL : IsometryInvariance.InvariantUnderIsometries)
    (hPv : PivotOfEveryBond)
    (hR : ComplexAverageIsLocal)
    (hA : ComplexAverageEquivariance)
    (hE : ComplexTransportCovariance)
    (hQ : LinearizedConstraintAtBond.Statement)
    (hG : LogSeriesInComplexGroupStatement)
    (hLog : ComplexMatrix2.LogSeriesConjugateInverse) :
    TransportIdentitiesAtImageBond := by
  intro L m K k i σ hL hm hi hσ hk hik V W c c' hc hc' hcc hV hV' hW
  have hfine : i ≤ levelDepth K k := by
    simp only [levelDepth] at hik ⊢
    push_cast at hik
    omega
  have hcoarse₀ : -(m : ℤ) < levelDepth K (k + 1) := by
    simp only [levelDepth]
    push_cast
    omega
  have hfine₀ : -(m : ℤ) < levelDepth K k := by
    simp only [levelDepth]
    omega
  have cF := hB L m i (levelDepth K k) σ hL hm hi hσ hfine
  have cC := hB L m i (levelDepth K (k + 1)) σ hL hm hi hσ hik
  have xF := hO L m hL hm _ hfine₀
  have xC := hO L m hL hm _ hcoarse₀
  have obj := (hBL L m hL hm i hi σ hσ).2.1 K k hk hik c
  have piv : ∀ d : BondAtLevel L m K (k + 1), PivotProperties d :=
    hPv ⟨L, hL, ⟨K, by omega⟩, ⟨m, hm⟩⟩ k hk
  have hLne : (L : ℂ) ≠ 0 := by
    have : L ≠ 0 := by
      have := hL.2
      omega
    exact_mod_cast this
  set P : Set (BondAtLevel L m K k) := bondsInDoubleBlock c with hPdef
  set P' : Set (BondAtLevel L m K k) := bondsInDoubleBlock c' with hP'def
  have hPc : IsReversalClosed P := fun b hb => ⟨hb.2, hb.1⟩
  have hP'c : IsReversalClosed P' := fun b hb => ⟨hb.2, hb.1⟩
  have hpos' : (bondImage σ c).positivelyOriented = c' := by
    rcases hcc with h | h
    · rw [← h]
      exact positivelyOriented_eq_self hc'
    · have hn : ¬(bondImage σ c).IsPositivelyOriented := by
        intro hp
        rcases xC (bondImage σ c) with h' | h'
        · exact h'.2 (h ▸ hc')
        · exact h'.2 hp
      rw [h, Bond.positivelyOriented, if_neg hn]
  have himg : bondImage σ '' P = P' := by
    have h := obj.2.2.2
    rw [positivelyOriented_eq_self hc, hpos'] at h
    exact h
  have hVc : IsGaugeField complexGaugeGroup P V := hV.1.1
  have hE' := hE L m i σ hL hm hi hσ (levelDepth K k) hfine₀ hfine P hPc
  have hexp : ∀ B : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra B →
      ∀ b' ∈ P', transportGaugeField σ (expTwist B V) b' =
        expTwist (twistedTransportForm σ V B) (transportGaugeField σ V) b' :=
    fun B hB => transportGaugeField_expTwist cF hPc hP'c himg hE' hVc hB
  have hR' := hR L m K k hL.1 hL.2 hm hk c' hc'
  have hU : ∀ B : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra B →
      ConstraintMapDefined (transportGaugeField σ V) (twistedTransportForm σ V B) c' →
      transportGaugeField σ (expTwist B V) ∈
          (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
        complexBlockAverage
            (expTwist (twistedTransportForm σ V B) (transportGaugeField σ V)) c' =
          complexBlockAverage (transportGaugeField σ (expTwist B V)) c' := by
    intro B hB h
    have hag := hexp B hB
    refine ⟨(hR'.mem_domain_iff _ _ hag).2 h.1, ?_⟩
    simp only [complexBlockAverage, if_pos hc']
    exact (hR'.average_eq _ _ hag).symm
  have hav : ∀ U : BondAtLevel L m K k → ComplexMatrix2,
      U ∈ (complexAveragingDomainNearOne c : Set _) → ComplexAverageRelation σ U c c' :=
    fun U hU' => hA L m K k i σ hL hm hi hσ hk hik U c c' hc hc' hcc hU'.1.1
  have hgrp : ∀ U : BondAtLevel L m K k → ComplexMatrix2,
      U ∈ (complexAveragingDomainNearOne c : Set _) → (complexBlockAverage U c).det = 1 :=
    fun U hU' => (hG.2 L hL m K k hm hk c hc).1 U hU'
  have hF := hQ L m K k hL hm hk V c hc hV
  have hF' := hQ L m K k hL hm hk _ c' hc' hV'
  have hb₀ : (pivot c : BondAtLevel L m K k).IsPositivelyOriented :=
    (piv c).isPositivelyOriented_iff.2 hc
  have hb₀' : (pivot c' : BondAtLevel L m K k).IsPositivelyOriented :=
    (piv c').isPositivelyOriented_iff.2 hc'
  have himgP : bondImage σ (pivot c : BondAtLevel L m K k) = pivot (bondImage σ c) :=
    obj.2.2.1
  have hbb : (pivot c' : BondAtLevel L m K k) = bondImage σ (pivot c) ∨
      (pivot c' : BondAtLevel L m K k) = (bondImage σ (pivot c)).opposite := by
    rcases hcc with h | h
    · exact Or.inl (by rw [himgP, h])
    · exact Or.inr (by rw [himgP, h, (piv _).pivot_opposite])
  have hub : IsUnit (V (pivot c)).det := by
    have hp := (piv c).isPivot.1
    have hmemP : (pivot c : BondAtLevel L m K k) ∈ P := ⟨Or.inl hp.1, Or.inr hp.2⟩
    have hdet : (V (pivot c)).det = 1 := hVc.1 _ hmemP
    rw [hdet]
    exact isUnit_one
  have hWdet : (W c).det = 1 := by
    rw [hW]
    exact hgrp V hV
  have huc : IsUnit (W c).det := by
    rw [hWdet]
    exact isUnit_one
  rcases hcc with hcc | hcc
  · refine transportIdentitiesAt_of_constraintMap cF xF
      (ContinuousLinearEquiv.refl ℂ ComplexMatrix2) hLne hF hF'
      (fun f => ?_) (fun Y => ?_) (fun B hB h₁ h₂ => ?_) hb₀ hb₀' hbb hub huc
    · have hpull : bondPreimage σ c' = c := by
        rw [hcc, bondPreimage_bondImage cC]
      unfold twistedFormValue
      rw [if_pos (by rw [hpull]; exact hc), hpull]
      rfl
    · have hσc : (bondImage σ c).IsPositivelyOriented := hcc ▸ hc'
      simp only [twistedLinkMap, if_pos hσc]
      rfl
    · obtain ⟨-, hm'⟩ := hU B hB h₂
      have a₁ := (hav _ h₁.1).average_image hcc h₁.1
      have a₂ := (hav _ hV).average_image hcc hV
      simp only [constraintMap]
      rw [hm', a₁, a₂]
      rfl
  · have hσc : ¬(bondImage σ c).IsPositivelyOriented := by
      intro hp
      rcases xC (bondImage σ c) with h' | h'
      · exact h'.2 (hcc ▸ hc')
      · exact h'.2 hp
    have hco : ¬c.opposite.IsPositivelyOriented := by
      rcases xC c with h' | h'
      · exact h'.2
      · exact absurd hc h'.2
    have hY : IsUnit ((W c)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ huc
    refine transportIdentitiesAt_of_constraintMap cF xF
      (negConjugateEquiv (W c)⁻¹ hY).toContinuousLinearEquiv hLne hF hF'
      (fun f => ?_) (fun Y => ?_) (fun B hB h₁ h₂ => ?_) hb₀ hb₀' hbb hub huc
    · have hpull : bondPreimage σ c' = c.opposite := by
        rw [hcc, ← cC.2.2.2.2.1 c, bondPreimage_bondImage cC]
      unfold twistedFormValue
      rw [if_neg (by rw [hpull]; exact hco), hpull, opposite_opposite]
      rfl
    · simp only [twistedLinkMap, if_neg hσc]
      rfl
    · obtain ⟨hd, hm'⟩ := hU B hB h₂
      have a₁ := (hav _ h₁.1).average_opposite hcc h₁.1 hd
      have a₂ := (hav _ hV).average_opposite hcc hV hV'
      have hdom := h₂.2
      rw [hm', a₁, a₂] at hdom
      have hX : IsUnit (complexBlockAverage V c).det := by
        rw [hgrp V hV]
        exact isUnit_one
      have hX₁ : IsUnit (complexBlockAverage (expTwist B V) c).det := by
        rw [hgrp _ h₁.1]
        exact isUnit_one
      have hXi : IsUnit ((complexBlockAverage V c)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hX
      have e : (complexBlockAverage V c)⁻¹ *
            (complexBlockAverage (expTwist B V) c * (complexBlockAverage V c)⁻¹)⁻¹ *
            ((complexBlockAverage V c)⁻¹)⁻¹ =
          (complexBlockAverage (expTwist B V) c)⁻¹ * ((complexBlockAverage V c)⁻¹)⁻¹ := by
        rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hX, ← mul_assoc,
          Matrix.nonsing_inv_mul _ hX, one_mul]
      have hlog := hLog (complexBlockAverage (expTwist B V) c * (complexBlockAverage V c)⁻¹)
        (complexBlockAverage V c)⁻¹
        ((Matrix.isUnit_iff_isUnit_det _).2 (by
          rw [Matrix.det_mul]
          exact hX₁.mul hXi))
        ((Matrix.isUnit_iff_isUnit_det _).2 hXi) h₁.2 (by rw [e]; exact hdom)
      rw [e] at hlog
      simp only [constraintMap]
      rw [hm', a₁, a₂, hlog]
      change _ = -ComplexMatrix2.conjugateBy (W c)⁻¹ _
      rw [hW]
      simp [ComplexMatrix2.conjugateBy]
end YangMills.Construction.PeriodicLattice
