import YangMills.Construction.Towers.FieldsAndTheirValues
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.SaddleOperatorsOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.StabilityOfTheSaddleSystemNearZeroProof
import YangMills.Construction.Towers.SymbolsOfTheTwoOperatorFunctionsAreInvertible
import YangMills.Construction.Towers.TheBackgroundKernelAtZero
import YangMills.Construction.Towers.TransposesAndRelationsOfTheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ZeroFieldSymbols
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FreeCoercivity
open YangMills.Construction.Tower.RescaledConditions (sumDiagScale)
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
theorem quotWeight_pos {I : PeriodicData} (hI : IsPeriodic I) (c : I.UnitQuot) :
    0 < I.quotWeight 1 c := by apply _root_.YangMills.SharedProofs.p9241 <;> assumption
section Coercive
variable {A B : PeriodicData}
theorem components_eq_zero_of_coercive [Finite A.UnitQuot] [Finite B.UnitQuot]
    (hA : ∀ c, 0 < A.quotWeight 1 c) (hB : ∀ c, 0 < B.quotWeight 1 c)
    {P Ξ K G : QuotHom A A} {Q : QuotHom A B} {Qt : QuotHom B A} {c c' : ℝ}
    (hc : 0 < c) (hc' : 0 < c')
    (hΞ : LoewnerLE ((c : ℂ) • (K + scalarQuotHom A 1)) Ξ)
    (hK : LoewnerLE (scalarQuotHom A 0) K)
    (hadj : IsAdjointQuotHom Q Qt)
    (hS : LoewnerLE (scalarQuotHom B c') (Q.comp (G.comp Qt)))
    (hP : ∀ b, Q b = 0 → P b = Ξ b) {t : ℂ} (ht : t ≠ 0) {b : A.UnitQuot → ℂ} {n : B.UnitQuot → ℂ}
    (h₁ : P b + t • Qt n = 0) (h₂ : Q b = 0) : b = 0 ∧ n = 0 := by
  exact _root_.YangMills.Construction.Tower.SaddleStability.saddle_kernel_trivial hA hB hc hc' hΞ hK hadj hS hP ht h₁ h₂
end Coercive
section DisjointSum
variable {A B : PeriodicData}
def quotSplit : (A.disjSum B).UnitQuot → A.UnitQuot ⊕ B.UnitQuot :=
  Quot.lift (Sum.map (A.mkQuot 1) (B.mkQuot 1)) (by
    rintro (a | a) _ ⟨n, rfl⟩
    · exact congrArg Sum.inl (Quot.sound ⟨n, rfl⟩)
    · exact congrArg Sum.inr (Quot.sound ⟨n, rfl⟩))
def inlQuot : A.UnitQuot → (A.disjSum B).UnitQuot :=
  Quot.lift (fun a => (A.disjSum B).mkQuot 1 (Sum.inl a)) (by
    rintro a _ ⟨n, rfl⟩
    exact Quot.sound ⟨n, rfl⟩)
def inrQuot : B.UnitQuot → (A.disjSum B).UnitQuot :=
  Quot.lift (fun a => (A.disjSum B).mkQuot 1 (Sum.inr a)) (by
    rintro a _ ⟨n, rfl⟩
    exact Quot.sound ⟨n, rfl⟩)
theorem quotSplit_inlQuot (c : A.UnitQuot) : quotSplit (B := B) (inlQuot c) = Sum.inl c := by
  obtain ⟨a, rfl⟩ := Quot.exists_rep c
  rfl
theorem quotSplit_inrQuot (c : B.UnitQuot) : quotSplit (A := A) (inrQuot c) = Sum.inr c := by
  obtain ⟨a, rfl⟩ := Quot.exists_rep c
  rfl
def quotSumEquiv : A.UnitQuot ⊕ B.UnitQuot ≃ (A.disjSum B).UnitQuot where
  toFun := Sum.elim inlQuot inrQuot
  invFun := quotSplit
  left_inv := by
    rintro (c | c)
    · exact quotSplit_inlQuot c
    · exact quotSplit_inrQuot c
  right_inv := by
    intro c
    obtain ⟨a | a, rfl⟩ := Quot.exists_rep c
    · rfl
    · rfl
instance finite_disjSum_unitQuot [Finite A.UnitQuot] [Finite B.UnitQuot] :
    Finite (A.disjSum B).UnitQuot :=
  Finite.of_equiv _ quotSumEquiv
def blockMatrixEntry (M₁₁ : QuotHom A A) (M₁₂ : QuotHom B A) (M₂₁ : QuotHom A B) :
    A.UnitQuot ⊕ B.UnitQuot → A.UnitQuot ⊕ B.UnitQuot → ℂ
  | .inl d', .inl d => linearMapEntry M₁₁ d' d
  | .inl d', .inr d => linearMapEntry M₁₂ d' d
  | .inr d', .inl d => linearMapEntry M₂₁ d' d
  | .inr _, .inr _ => 0
theorem linearMap_apply_eq_sum_entry {J J' : Type} [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (b : J → ℂ)
    (c' : J') : M b c' = ∑ c, linearMapEntry M c' c * b c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.apply_eq_sum_linearMapEntry <;> assumption
theorem symbolHom_apply_of_blocks [Finite A.UnitQuot] [Finite B.UnitQuot]
    {T : (A.disjSum B).Carrier → (A.disjSum B).Carrier → ℂ} {κ : Fin 4 → ℂ}
    {M₁₁ : QuotHom A A} {M₁₂ : QuotHom B A} {M₂₁ : QuotHom A B}
    (h₁₁ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inl a') (Sum.inl a) =
      carrierEntry M₁₁ a' a)
    (h₁₂ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inl a') (Sum.inr a) =
      carrierEntry M₁₂ a' a)
    (h₂₁ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inr a') (Sum.inl a) =
      carrierEntry M₂₁ a' a)
    (h₂₂ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inr a') (Sum.inr a) = 0)
    (f : (A.disjSum B).UnitQuot → ℂ) :
    (∀ c', symbolHom (A.disjSum B) (A.disjSum B) T κ f (inlQuot c') =
      M₁₁ (f ∘ inlQuot) c' + M₁₂ (f ∘ inrQuot) c') ∧
    ∀ c', symbolHom (A.disjSum B) (A.disjSum B) T κ f (inrQuot c') =
      M₂₁ (f ∘ inlQuot) c' := by
  let := Fintype.ofFinite A.UnitQuot
  let := Fintype.ofFinite B.UnitQuot
  let E : (A.disjSum B).UnitQuot → (A.disjSum B).UnitQuot → ℂ := fun c' c =>
    blockMatrixEntry M₁₁ M₁₂ M₂₁ (quotSplit c') (quotSplit c)
  have hspec : ∀ (c' c : (A.disjSum B).UnitQuot) (ι' ι : (A.disjSum B).Carrier), (A.disjSum B).mkQuot 1 ι' = c' → (A.disjSum B).mkQuot 1 ι = c →
      fourierSymbol (A.disjSum B) (A.disjSum B) T κ ι' ι = E c' c := by
    rintro _ _ (a' | a') (a | a) rfl rfl
    · exact h₁₁ a' a
    · exact h₁₂ a' a
    · exact h₂₁ a' a
    · exact h₂₂ a' a
  have hE : descendMatrix (A.disjSum B) (A.disjSum B) 1 (fourierSymbol (A.disjSum B) (A.disjSum B) T κ) = E := by
    funext c' c
    obtain ⟨ι', rfl⟩ := Quot.exists_rep c'
    obtain ⟨ι, rfl⟩ := Quot.exists_rep c
    have hz : ∃ z, ∀ j' j, (A.disjSum B).mkQuot 1 j' = Quot.mk _ ι' → (A.disjSum B).mkQuot 1 j = Quot.mk _ ι →
        fourierSymbol (A.disjSum B) (A.disjSum B) T κ j' j = z := ⟨_, hspec _ _⟩
    have e := Classical.epsilon_spec hz ι' ι rfl rfl
    exact e.symm.trans (hspec _ _ ι' ι rfl rfl)
  have hmap : ∀ c', symbolHom (A.disjSum B) (A.disjSum B) T κ f c' =
      ∑ d : A.UnitQuot ⊕ B.UnitQuot, E c' (quotSumEquiv d) * f (quotSumEquiv d) := by
    intro c'
    rw [symbolHom, hE, linearMapOfEntries_eq_applyKernel, applyKernel, ← (quotSumEquiv (A := A) (B := B)).tsum_eq,
      tsum_fintype]
  constructor
  · intro c'
    rw [hmap, Fintype.sum_sum_type, linearMap_apply_eq_sum_entry M₁₁, linearMap_apply_eq_sum_entry M₁₂]
    congr 1
    · refine Finset.sum_congr rfl fun d _ => ?_
      show blockMatrixEntry M₁₁ M₁₂ M₂₁ (quotSplit (inlQuot c')) (quotSplit (inlQuot d)) * _ = _
      rw [quotSplit_inlQuot, quotSplit_inlQuot]
      rfl
    · refine Finset.sum_congr rfl fun d _ => ?_
      show blockMatrixEntry M₁₁ M₁₂ M₂₁ (quotSplit (inlQuot c')) (quotSplit (inrQuot d)) * _ = _
      rw [quotSplit_inlQuot, quotSplit_inrQuot]
      rfl
  · intro c'
    rw [hmap, Fintype.sum_sum_type, linearMap_apply_eq_sum_entry M₂₁]
    have e : ∀ d, E (inrQuot c') (quotSumEquiv (Sum.inr d)) = 0 := fun d => by
      show blockMatrixEntry M₁₁ M₁₂ M₂₁ (quotSplit (inrQuot c')) (quotSplit (inrQuot d)) = 0
      rw [quotSplit_inrQuot, quotSplit_inrQuot]
      rfl
    simp only [e, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun d _ => ?_
    show blockMatrixEntry M₁₁ M₁₂ M₂₁ (quotSplit (inrQuot c')) (quotSplit (inlQuot d)) * _ = _
    rw [quotSplit_inrQuot, quotSplit_inlQuot]
    rfl
theorem isInvertible_of_blocks [Finite A.UnitQuot] [Finite B.UnitQuot]
    {T : (A.disjSum B).Carrier → (A.disjSum B).Carrier → ℂ} {κ : Fin 4 → ℂ}
    {M₁₁ : QuotHom A A} {M₁₂ : QuotHom B A} {M₂₁ : QuotHom A B}
    (h₁₁ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inl a') (Sum.inl a) =
      carrierEntry M₁₁ a' a)
    (h₁₂ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inl a') (Sum.inr a) =
      carrierEntry M₁₂ a' a)
    (h₂₁ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inr a') (Sum.inl a) =
      carrierEntry M₂₁ a' a)
    (h₂₂ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inr a') (Sum.inr a) = 0)
    (hinj : ∀ b n, M₁₁ b + M₁₂ n = 0 → M₂₁ b = 0 → b = 0 ∧ n = 0) :
    IsInvertibleQuotHom (symbolHom (A.disjSum B) (A.disjSum B) T κ) := by
  set M := symbolHom (A.disjSum B) (A.disjSum B) T κ with hM
  have hker : ∀ f, M f = 0 → f = 0 := by
    intro f hf
    obtain ⟨hl, hr⟩ := symbolHom_apply_of_blocks h₁₁ h₁₂ h₂₁ h₂₂ f
    have e₁ : M₁₁ (f ∘ inlQuot) + M₁₂ (f ∘ inrQuot) = 0 := by
      funext c'
      have := hl c'
      rw [← hM, hf] at this
      exact this.symm
    have e₂ : M₂₁ (f ∘ inlQuot) = 0 := by
      funext c'
      have := hr c'
      rw [← hM, hf] at this
      exact this.symm
    obtain ⟨hb, hn⟩ := hinj _ _ e₁ e₂
    funext c
    obtain ⟨d | d, rfl⟩ := quotSumEquiv.surjective c
    · exact congrFun hb d
    · exact congrFun hn d
  have hinjM : Function.Injective M := by
    intro f f' e
    have := hker (f - f') (by rw [map_sub, e, sub_self])
    exact sub_eq_zero.1 this
  have hsurj : Function.Surjective M := LinearMap.injective_iff_surjective.1 hinjM
  intro g
  obtain ⟨f, hf⟩ := hsurj g
  exact ⟨f, hf, fun f' hf' => hinjM (hf'.trans hf.symm)⟩
theorem carrierEntry_smul {I I' : PeriodicData} (c : ℂ) (M : QuotHom I I') (ι' : I'.Carrier)
    (ι : I.Carrier) : carrierEntry (c • M) ι' ι = c * carrierEntry M ι' ι := by
  simp [carrierEntry, linearMapEntry]
theorem saddleMatrix_symbol_invertible [Finite A.UnitQuot] [Finite B.UnitQuot]
    {X : A.Carrier → A.Carrier → ℂ} {Qt : A.Carrier → B.Carrier → ℂ} {Q : B.Carrier → A.Carrier → ℂ}
    {κ : Fin 4 → ℂ} {x y x' y' : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hx' : x' ≠ 0) (hy' : y' ≠ 0)
    (eX : ∀ ι' ι, carrierEntry (symbolHom A A X κ) ι' ι = fourierSymbol A A X κ ι' ι)
    (eQt : ∀ ι' ι, carrierEntry (symbolHom B A Qt κ) ι' ι = fourierSymbol B A Qt κ ι' ι)
    (eQ : ∀ ι' ι, carrierEntry (symbolHom A B Q κ) ι' ι = fourierSymbol A B Q κ ι' ι)
    (hinj : ∀ (t : ℂ), t ≠ 0 → ∀ b n, symbolHom A A X κ b + t • symbolHom B A Qt κ n = 0 →
      symbolHom A B Q κ b = 0 → b = 0 ∧ n = 0) :
    IsInvertibleQuotHom (symbolHom (A.disjSum B) (A.disjSum B)
      (sumDiagScale x y x' y' (PeriodicOperators.saddleMatrix X Qt Q)) κ) := by
  refine isInvertible_of_blocks (M₁₁ := (x * x') • symbolHom A A X κ)
    (M₁₂ := (x * y') • symbolHom B A Qt κ) (M₂₁ := (y * x') • symbolHom A B Q κ) ?_ ?_ ?_ ?_ ?_
  · intro a' a
    rw [carrierEntry_smul, eX]
    show (∑' n, symbolSummand _ _ _ κ _ _ n) = _ * ∑' n, symbolSummand A A X κ a' a n
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    show x * X a' (A.translate n a) * x' * _ = (x * x') * (X a' (A.translate n a) * _)
    ring_nf
    rfl
  · intro a' a
    rw [carrierEntry_smul, eQt]
    show (∑' n, symbolSummand _ _ _ κ _ _ n) = _ * ∑' n, symbolSummand B A Qt κ a' a n
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    show x * Qt a' (B.translate n a) * y' * _ = (x * y') * (Qt a' (B.translate n a) * _)
    ring_nf
    rfl
  · intro a' a
    rw [carrierEntry_smul, eQ]
    show (∑' n, symbolSummand _ _ _ κ _ _ n) = _ * ∑' n, symbolSummand A B Q κ a' a n
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    show y * Q a' (A.translate n a) * x' * _ = (y * x') * (Q a' (A.translate n a) * _)
    ring_nf
    rfl
  · intro a' a
    show (∑' n, symbolSummand _ _ _ κ _ _ n) = 0
    refine (tsum_congr fun n => ?_).trans tsum_zero
    show y * 0 * y' * _ = 0
    simp
  · intro b n h₁ h₂
    have hxx : x * x' ≠ 0 := mul_ne_zero hx hx'
    have hyx : y * x' ≠ 0 := mul_ne_zero hy hx'
    refine hinj (y' / x') (div_ne_zero hy' hx') b n ?_ ?_
    · have e := congrArg (fun g => (x * x')⁻¹ • g) h₁
      simp only [LinearMap.smul_apply, smul_add, smul_zero, smul_smul] at e
      rw [inv_mul_cancel₀ hxx, one_smul] at e
      have e' : (x * x')⁻¹ * (x * y') = y' / x' := by
        field_simp
      rwa [e'] at e
    · have e := congrArg (fun g => (y * x')⁻¹ • g) h₂
      simp only [LinearMap.smul_apply, smul_zero, smul_smul] at e
      rwa [inv_mul_cancel₀ hyx, one_smul] at e
end DisjointSum
section ZeroField
variable {L k : ℕ}
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeffs_zero (hL : 0 < L) : (0 : FullField L k).pauliCoeffs hL = 0 := by
  funext ι
  obtain ⟨p, ι⟩ := ι
  cases p
  · exact pauliCoeff_zero _
  · exact pauliCoeff_zero _
  · exact pauliCoeff_zero _
theorem gaugeField_zero : (0 : FullField L k).gaugeField = fun _ => 1 := by
  funext b
  by_cases h : b.IsPositivelyOriented <;>
    simp [FullField.gaugeField, expForm, expTwist, h, NormedSpace.exp_zero]
theorem opFns_at_zero (hKernel : KernelAtZeroSources.ZeroSourceKernel)
    (hValues : FieldValues.FieldsAndValuesClaim) (hL : 0 < L) (hS : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hone : (fun _ => (1 : Matrices.ComplexMatrix2)) ∈ smallIterateFields L k) :
    vectorOpFn L k hL 0 = backgroundSaddle L k (fun _ => 1) ∧
      ghostOpFn L k hL 0 = laplacianSaddle L k (fun _ => 1) := by
  have hv := ((hValues L hL k).1 (0 : FullField L k)).2.2.2.1
  have hg := ((hValues L hL k).1 (0 : FullField L k)).2.2.2.2.1
  rw [pauliCoeffs_zero] at hv hg
  obtain ⟨-, -, -, -, -, -, -, hlast⟩ := hKernel L hS k hk _ hone
  have hb := hlast (0 : FullField L k) rfl rfl gaugeField_zero
  constructor
  · rw [hv]
    unfold vectorOp hessianSaddle
    rw [hb, gaugeField_zero]
    rfl
  · rw [hg]
    unfold ghostOp
    rw [gaugeField_zero]
end ZeroField
theorem symbolsInvertibleAtZero_holds (hCoercive : FreeOperatorsCoercive)
    (hReal : FreeSymbolsAtRealPoints)
    (hSaddle : RescaledSaddleScaling)
    (hKernel : KernelAtZeroSources.ZeroSourceKernel)
    (hFacts : RescaledConditions.Holds)
    (hValues : FieldValues.FieldsAndValuesClaim)
    (hIndex : PeriodicOperators.TowerIndexSets.Claim)
    (hSymbols : StripSymbols.Claim) : SymbolsInvertibleAtZero := by
  intro L hL hS k hk
  obtain ⟨cXi, hcXi, cY, hcY, cC, hcC, hc⟩ := hCoercive
  obtain ⟨hops, -, -, hreal⟩ := hc L hS k hk
  obtain ⟨hS0, hB0, -⟩ := hIndex L hS k 0 (Nat.zero_le k)
  obtain ⟨hSk, hBk, -⟩ := hIndex L hS k k le_rfl
  obtain ⟨-, -, -, hone, -⟩ := (hFacts L hS k hk).2
  obtain ⟨hsv, hsg⟩ := hSaddle L hS k hk _ hone
  obtain ⟨hzv, hzg⟩ := opFns_at_zero hKernel hValues hL hS hk hone
  have hη : (((trivialRescaledOperators L k).eta : ℝ) : ℂ) ≠ 0 := by
    have hw : (0 : ℝ) < meshAt L k 0 ^ 4 := hB0.weight_pos ()
    refine Complex.ofReal_ne_zero.2 fun h => ?_
    have h' : meshAt L k 0 = 0 := h
    rw [h'] at hw
    simp at hw
  have : Finite (colourEdges L k 0).UnitQuot := hB0.finite_quot
  have : Finite (colourEdges L k k).UnitQuot := hBk.finite_quot
  have : Finite (colourVertices L k 0).UnitQuot := hS0.finite_quot
  have : Finite (colourVertices L k k).UnitQuot := hSk.finite_quot
  have facts : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ), IsPeriodicKernel I I' T →
        SymbolSummableAt I I' T κ → StripSymbols.PointwiseCalculus I I' T κ :=
    fun hI hI' T κ hT hf => (hSymbols.2.1 _ _ hI hI').2.1 T κ hT hf
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · obtain ⟨-, hr⟩ := hreal κ hκ
    obtain ⟨hK, -, hadj, -, hQt, -⟩ := hReal L hS k hk κ hκ
    have fQ := hops.Q.2.2 κ (Set.mem_univ κ)
    have fQt := hops.Qt.2.2 κ (Set.mem_univ κ)
    have fXi := hops.Xi.2.2 κ (Set.mem_univ κ)
    have FQ := facts hB0 hBk _ κ hops.Q.1 fQ
    have FQt := facts hBk hB0 _ κ hops.Qt.1 fQt
    have FXi := facts hB0 hB0 _ κ hops.Xi.1 fXi
    obtain ⟨-, hper, hform, hprod⟩ := FQt.comp (colourEdges L k 0) hB0 _ hops.Q.1 fQ
    obtain ⟨hperX, hformX, hmapX⟩ := FXi.linComb _ hper hform 1 (-1)
    have eX : StripSymbols.linCombKernel 1 (-1) (trivialRescaledOperators L k).Xi
        (compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q) = (trivialRescaledOperators L k).X := by
      funext a b
      simp [StripSymbols.linCombKernel, RescaledOperators.X, sub_eq_add_neg]
    have hperX' : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X :=
      Eq.mp (congrArg (fun T => IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0) T) eX)
        hperX
    have hformX' : SymbolSummableAt (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ :=
      Eq.mp (congrArg (fun T => SymbolSummableAt (colourEdges L k 0) (colourEdges L k 0) T κ) eX)
        hformX
    have hmapX' := (congrArg (fun T => symbolHom (colourEdges L k 0) (colourEdges L k 0) T κ)
      eX).symm.trans hmapX
    have FX := facts hB0 hB0 _ κ hperX' hformX'
    have hP : ∀ b, symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ b = 0 →
        symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ b =
          symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi κ b := by
      intro b hb
      rw [hmapX', hprod]
      simp [hb]
    have hav := hr.edge_lower
    unfold edgeResolventConjugate at hav
    rw [hQt] at hav
    have hinv := saddleMatrix_symbol_invertible (A := colourEdges L k 0) (B := colourEdges L k k)
      (x := (((trivialRescaledOperators L k).eta : ℝ) : ℂ) ^ 2) (y := (((trivialRescaledOperators L k).eta : ℝ) : ℂ)⁻¹)
      (x' := 1) (y' := (((trivialRescaledOperators L k).eta : ℝ) : ℂ)) (pow_ne_zero 2 hη) (inv_ne_zero hη)
      one_ne_zero hη FX.carrierEntry_symbolHom FQt.carrierEntry_symbolHom FQ.carrierEntry_symbolHom
      (fun t ht b n h₁ h₂ => components_eq_zero_of_coercive (quotWeight_pos hB0) (quotWeight_pos hBk)
        hcXi.1 hcC.1 hr.Xi_lower hK hadj hav hP ht h₁ h₂)
    have e : vectorOpFn L k hL 0 = sumDiagScale
        ((((trivialRescaledOperators L k).eta : ℝ) : ℂ) ^ 2) (((trivialRescaledOperators L k).eta : ℝ) : ℂ)⁻¹ 1
        (((trivialRescaledOperators L k).eta : ℝ) : ℂ)
        (saddleMatrix (trivialRescaledOperators L k).X (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q) :=
      hzv.trans hsv
    rw [e]
    exact hinv
  · obtain ⟨-, hr⟩ := hreal κ hκ
    obtain ⟨-, hK, -, hadj, -, hRt⟩ := hReal L hS k hk κ hκ
    have fR := hops.R.2.2 κ (Set.mem_univ κ)
    have fRt := hops.Rt.2.2 κ (Set.mem_univ κ)
    have fDelta := hops.Delta.2.2 κ (Set.mem_univ κ)
    have FR := facts hS0 hSk _ κ hops.R.1 fR
    have FRt := facts hSk hS0 _ κ hops.Rt.1 fRt
    have FDelta := facts hS0 hS0 _ κ hops.Delta.1 fDelta
    obtain ⟨-, hper, hform, hprod⟩ := FRt.comp (colourVertices L k 0) hS0 _ hops.R.1 fR
    obtain ⟨-, -, hmapY⟩ := FDelta.linComb _ hper hform 1 1
    have eY : StripSymbols.linCombKernel 1 1 (trivialRescaledOperators L k).Delta
        (compKernel (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R) = (trivialRescaledOperators L k).Y := by
      funext a b
      simp [StripSymbols.linCombKernel, RescaledOperators.Y]
    have hmapY' := (congrArg (fun T => symbolHom (colourVertices L k 0) (colourVertices L k 0) T κ)
      eY).symm.trans hmapY
    have hP : ∀ b, symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ b = 0 →
        symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Delta κ b =
          symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Y κ b := by
      intro b hb
      rw [hmapY', hprod]
      simp [hb]
    have hav := hr.vertex_lower
    unfold vertexResolventConjugate at hav
    rw [hRt] at hav
    have hinv := saddleMatrix_symbol_invertible (A := colourVertices L k 0) (B := colourVertices L k k)
      (x := (((trivialRescaledOperators L k).eta : ℝ) : ℂ) ^ 2) (y := 1)
      (x' := 1) (y' := (((trivialRescaledOperators L k).eta : ℝ) : ℂ) ^ 2) (pow_ne_zero 2 hη) one_ne_zero
      one_ne_zero (pow_ne_zero 2 hη) FDelta.carrierEntry_symbolHom FRt.carrierEntry_symbolHom FR.carrierEntry_symbolHom
      (fun t ht b n h₁ h₂ => components_eq_zero_of_coercive (quotWeight_pos hS0) (quotWeight_pos hSk)
        hcY.1 hcC.1 hr.Y_lower hK hadj hav hP ht h₁ h₂)
    have e : ghostOpFn L k hL 0 = sumDiagScale
        ((((trivialRescaledOperators L k).eta : ℝ) : ℂ) ^ 2) 1 1 ((((trivialRescaledOperators L k).eta : ℝ) : ℂ) ^ 2)
        (saddleMatrix (trivialRescaledOperators L k).Delta (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R) :=
      hzg.trans hsg
    rw [e]
    exact hinv
end YangMills.Construction.Tower.FullSpace.ZeroFieldSymbols
end
