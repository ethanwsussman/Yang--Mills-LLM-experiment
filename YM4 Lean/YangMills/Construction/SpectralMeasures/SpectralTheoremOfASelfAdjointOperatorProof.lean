import YangMills.Construction.HilbertSpaces.BoundedFunctionalsBoundedFormsAdjointsAndOrthogonalVectors
import YangMills.Construction.SpectralMeasures.ProjectionValuedMeasureOfAUnitaryOperator
import YangMills.Construction.SpectralMeasures.RulesForTheSpectralMeasureProof
import YangMills.Construction.SpectralMeasures.UniquenessOfComplexMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanBorel.CayleySpectral
open FormsOperators (IsExtendedBy IsSelfAdj Commutes UnitaryMap addConst adj adj_spec
  adjValue_unique ofCLM unboundedOp_eq_iff IsSeqClosedSubmodule)
open SpectralTheory (UnboundedOp)
open BoundedRepresentation (EqTopOfOrthogonalTrivial)
section Shifts
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem mem_domain_of_inner_eq {A : UnboundedOp H} (hA : IsSelfAdj A) {φ φ' : H}
    (h : ∀ χ : A.domain, ⟪φ, A χ⟫_ℂ = ⟪φ', (χ : H)⟫_ℂ) : ∃ hφ : φ ∈ A.domain, A ⟨φ, hφ⟩ = φ' := by
  obtain ⟨hd, he⟩ := hA
  obtain ⟨hdom, hval⟩ := (unboundedOp_eq_iff _ _).1 he
  have hmem : φ ∈ (adj A hd).domain := ⟨φ', h⟩
  refine ⟨hdom ▸ hmem, ?_⟩
  have h₁ := hval ⟨φ, hmem⟩
  refine h₁.trans (adjValue_unique hd (fun χ => adj_spec A hd ⟨φ, hmem⟩ χ) h)
theorem inner_map_symm {A : UnboundedOp H} (hA : IsSelfAdj A) (φ χ : A.domain) :
    ⟪(φ : H), A χ⟫_ℂ = ⟪A φ, (χ : H)⟫_ℂ := by
  obtain ⟨hd, he⟩ := hA
  obtain ⟨hdom, hval⟩ := (unboundedOp_eq_iff _ _).1 he
  have hmem : (φ : H) ∈ (adj A hd).domain := hdom.symm ▸ φ.2
  have h₁ := hval ⟨φ, hmem⟩
  have h₂ := adj_spec A hd ⟨φ, hmem⟩ χ
  rw [← h₁] at h₂
  exact h₂
theorem norm_add_smul_sq {A : UnboundedOp H} (hA : IsSelfAdj A) {c : ℂ} (hc : conj c = -c)
    (hn : ‖c‖ = 1) (χ : A.domain) :
    ‖A χ + c • (χ : H)‖ ^ 2 = ‖A χ‖ ^ 2 + ‖(χ : H)‖ ^ 2 := by
  have hre : c.re = 0 := by
    have := congrArg Complex.re hc
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  have him : (⟪A χ, (χ : H)⟫_ℂ).im = 0 := by
    have h₁ : ⟪(χ : H), A χ⟫_ℂ = ⟪A χ, (χ : H)⟫_ℂ := inner_map_symm hA χ χ
    rw [← inner_conj_symm] at h₁
    have := congrArg Complex.im h₁
    simp only [Complex.conj_im] at this
    linarith
  have hcross : (⟪A χ, c • (χ : H)⟫_ℂ).re = 0 := by
    rw [inner_smul_right, Complex.mul_re, hre, him]
    ring
  have := @norm_add_sq ℂ _ _ _ _ (A χ) (c • (χ : H))
  rw [norm_smul, hn, one_mul] at this
  rw [this]
  have h₂ : RCLike.re (⟪A χ, c • (χ : H)⟫_ℂ) = 0 := hcross
  rw [h₂]
  ring
theorem norm_le_norm_add_smul {A : UnboundedOp H} (hA : IsSelfAdj A) {c : ℂ}
    (hc : conj c = -c) (hn : ‖c‖ = 1) (χ : A.domain) : ‖(χ : H)‖ ≤ ‖A χ + c • (χ : H)‖ := by
  have := norm_add_smul_sq hA hc hn χ
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  nlinarith [sq_nonneg ‖A χ‖]
theorem addConst_injective {A : UnboundedOp H} (hA : IsSelfAdj A) {c : ℂ}
    (hc : conj c = -c) (hn : ‖c‖ = 1) : Function.Injective (addConst A c).toFun := by
  refine (injective_iff_map_eq_zero _).2 fun χ h => ?_
  have h₀ : A χ + c • ((χ : A.domain) : H) = 0 := h
  have := norm_le_norm_add_smul hA hc hn χ
  rw [h₀, norm_zero] at this
  exact Subtype.ext (norm_le_zero_iff.1 this)
theorem addConst_surjective {A : UnboundedOp H} (hA : IsSelfAdj A)
    (hK : EqTopOfOrthogonalTrivial H) {c : ℂ}
    (hc : conj c = -c) (hn : ‖c‖ = 1) : Function.Surjective (addConst A c).toFun := by
  have hclosed : IsSeqClosedSubmodule (LinearMap.range (addConst A c).toFun) := by
    intro u ψ hu hl
    have hex : ∀ k, ∃ x : A.domain, A x + c • (x : H) = u k := fun k => by
      obtain ⟨x, hx⟩ := LinearMap.mem_range.1 (hu k)
      exact ⟨x, hx⟩
    choose χ hval using hex
    have hcs : CauchySeq fun k => ((χ k : A.domain) : H) := by
      refine Metric.cauchySeq_iff.2 fun ε hε => ?_
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hl.cauchySeq ε hε
      refine ⟨N, fun m hm k hk => lt_of_le_of_lt ?_ (hN m hm k hk)⟩
      have h₁ := norm_le_norm_add_smul hA hc hn (χ m - χ k)
      rw [dist_eq_norm, dist_eq_norm, ← hval m, ← hval k]
      have h₂ : A (χ m - χ k) + c • ((χ m - χ k : A.domain) : H) =
          A (χ m) + c • ((χ m : A.domain) : H) - (A (χ k) + c • ((χ k : A.domain) : H)) := by
        rw [LinearPMap.map_sub, Submodule.coe_sub, smul_sub]
        abel
      rw [h₂] at h₁
      exact h₁
    obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcs
    have hAv : Tendsto (fun k => A (χ k)) atTop (𝓝 (ψ - c • v)) := by
      have := hl.sub (hv.const_smul c)
      refine this.congr fun k => ?_
      rw [← hval k]
      abel
    have hinner : ∀ φ : A.domain, ⟪v, A φ⟫_ℂ = ⟪ψ - c • v, (φ : H)⟫_ℂ := by
      intro φ
      have h₁ : Tendsto (fun k => ⟪((χ k : A.domain) : H), A φ⟫_ℂ) atTop (𝓝 ⟪v, A φ⟫_ℂ) :=
        hv.inner tendsto_const_nhds
      have h₂ : Tendsto (fun k => ⟪A (χ k), (φ : H)⟫_ℂ) atTop (𝓝 ⟪ψ - c • v, (φ : H)⟫_ℂ) :=
        hAv.inner tendsto_const_nhds
      refine tendsto_nhds_unique h₁ (h₂.congr fun k => ?_)
      exact (inner_map_symm hA (χ k) φ).symm
    obtain ⟨hvd, hAv'⟩ := mem_domain_of_inner_eq hA hinner
    refine LinearMap.mem_range.2 ⟨⟨v, hvd⟩, ?_⟩
    change A ⟨v, hvd⟩ + c • v = ψ
    rw [hAv']
    abel
  have htop := hK _ hclosed fun φ hφ => by
    have hi : ∀ χ : A.domain, ⟪φ, A χ⟫_ℂ = ⟪c • φ, (χ : H)⟫_ℂ := by
      intro χ
      have h₁ : ⟪φ, A χ + c • (χ : H)⟫_ℂ = 0 := hφ _ ⟨χ, rfl⟩
      rw [inner_add_right, inner_smul_right] at h₁
      rw [inner_smul_left, hc]
      linear_combination h₁
    obtain ⟨hd, hAφ⟩ := mem_domain_of_inner_eq hA hi
    have hc' : conj (-c) = - -c := by rw [map_neg, hc]
    have hn' : ‖-c‖ = 1 := by rwa [norm_neg]
    have h₂ := norm_le_norm_add_smul hA hc' hn' ⟨φ, hd⟩
    rw [hAφ] at h₂
    simpa using h₂
  exact LinearMap.range_eq_top.1 htop
theorem addConst_bijective {A : UnboundedOp H} (hA : IsSelfAdj A)
    (hK : EqTopOfOrthogonalTrivial H) {c : ℂ}
    (hc : conj c = -c) (hn : ‖c‖ = 1) : Function.Bijective (addConst A c).toFun :=
  ⟨addConst_injective hA hc hn, addConst_surjective hA hK hc hn⟩
theorem conj_I_eq_neg_I : conj Complex.I = -Complex.I := Complex.conj_I
theorem conj_neg_I_eq_neg_neg_I : conj (-Complex.I) = - -Complex.I := by simp
theorem norm_neg_I_eq_one : ‖-Complex.I‖ = 1 := by simp
theorem exists_boundedInverse {A : UnboundedOp H} (hA : IsSelfAdj A)
    (hK : EqTopOfOrthogonalTrivial H) :
    ∃ R : H →L[ℂ] H, IsBoundedInverse R (addConst A Complex.I) := by
  have hb := addConst_bijective hA hK conj_I_eq_neg_I Complex.norm_I
  let e := LinearEquiv.ofBijective (addConst A Complex.I).toFun hb
  have hshift : ∀ ψ, addConst A Complex.I (e.symm ψ) = ψ := fun ψ => e.apply_symm_apply ψ
  let L : H →ₗ[ℂ] H := (addConst A Complex.I).domain.subtype ∘ₗ e.symm.toLinearMap
  have hbound : ∀ ψ, ‖L ψ‖ ≤ 1 * ‖ψ‖ := by
    intro ψ
    have h₁ := norm_le_norm_add_smul hA conj_I_eq_neg_I Complex.norm_I (e.symm ψ)
    have h₂ : A (e.symm ψ) + Complex.I • ((e.symm ψ : A.domain) : H) = ψ := hshift ψ
    rw [h₂] at h₁
    rw [one_mul]
    exact h₁
  refine ⟨L.mkContinuous 1 hbound, fun ψ => ⟨(e.symm ψ).2, hshift ψ⟩, fun χ => ?_⟩
  have h₃ : e.symm (addConst A Complex.I χ) = χ := e.symm_apply_apply χ
  exact congrArg Subtype.val h₃
theorem resolventAtI_spec {A : UnboundedOp H} (hA : IsSelfAdj A)
    (hK : EqTopOfOrthogonalTrivial H) :
    IsBoundedInverse (resolventAtI A) (addConst A Complex.I) :=
  Classical.epsilon_spec (exists_boundedInverse hA hK)
theorem boundedInverse_right {A : UnboundedOp H} {R : H →L[ℂ] H}
    (hR : IsBoundedInverse R (addConst A Complex.I)) (ψ : H) :
    ∃ h : R ψ ∈ A.domain, A ⟨R ψ, h⟩ + Complex.I • R ψ = ψ :=
  hR.1 ψ
theorem boundedInverse_left {A : UnboundedOp H} {R : H →L[ℂ] H}
    (hR : IsBoundedInverse R (addConst A Complex.I)) (χ : A.domain) :
    R (A χ + Complex.I • (χ : H)) = χ :=
  hR.2 χ
theorem boundedInverse_injective {A : UnboundedOp H} {R : H →L[ℂ] H}
    (hR : IsBoundedInverse R (addConst A Complex.I)) : Function.Injective R := by
  intro ψ ψ' h
  obtain ⟨h₁, e₁⟩ := boundedInverse_right hR ψ
  obtain ⟨h₂, e₂⟩ := boundedInverse_right hR ψ'
  have h₃ : (⟨R ψ, h₁⟩ : A.domain) = ⟨R ψ', h₂⟩ := Subtype.ext h
  rw [← e₁, ← e₂, h₃, h]
theorem exists_cayleyTransform {A : UnboundedOp H} (hA : IsSelfAdj A)
    (hK : EqTopOfOrthogonalTrivial H) :
    ∃ U : UnitaryMap H H, IsCayleyTransform A U := by
  have hR := resolventAtI_spec hA hK
  set R := resolventAtI A with hRdef
  let V : H →L[ℂ] H := 1 - (2 * Complex.I) • R
  have hVapply : ∀ ψ, V ψ = ψ - (2 * Complex.I) • R ψ := fun ψ => rfl
  have hVshift : ∀ (ψ : H) (h : R ψ ∈ A.domain), A ⟨R ψ, h⟩ + Complex.I • R ψ = ψ →
      V ψ = A ⟨R ψ, h⟩ + (-Complex.I) • R ψ := by
    intro ψ h e'
    rw [hVapply]
    nth_rewrite 1 [← e']
    rw [two_mul, add_smul, neg_smul]
    abel
  have hnorm : ∀ ψ, ‖V ψ‖ = ‖ψ‖ := by
    intro ψ
    obtain ⟨h, e⟩ := boundedInverse_right hR ψ
    have h₁ := norm_add_smul_sq hA conj_I_eq_neg_I Complex.norm_I ⟨R ψ, h⟩
    have h₂ := norm_add_smul_sq hA conj_neg_I_eq_neg_neg_I norm_neg_I_eq_one ⟨R ψ, h⟩
    rw [hVshift ψ h e]
    have h₃ : ‖A ⟨R ψ, h⟩ + (-Complex.I) • R ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
      have h₄ : ‖ψ‖ ^ 2 = ‖A ⟨R ψ, h⟩ + Complex.I • R ψ‖ ^ 2 := by rw [e]
      rw [h₄]
      exact h₂.trans h₁.symm
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h₃
  have hsurj : Function.Surjective V := by
    intro φ
    have hex : ∃ x : A.domain, A x + (-Complex.I) • (x : H) = φ := by
      obtain ⟨x, hx⟩ := addConst_surjective hA hK conj_neg_I_eq_neg_neg_I norm_neg_I_eq_one φ
      exact ⟨x, hx⟩
    obtain ⟨χ, hχ'⟩ := hex
    refine ⟨A χ + Complex.I • (χ : H), ?_⟩
    rw [hVapply, boundedInverse_left hR χ, ← hχ', two_mul, add_smul, neg_smul]
    abel
  let W : H →ₗᵢ[ℂ] H := ⟨V.toLinearMap, hnorm⟩
  let U : UnitaryMap H H := LinearIsometryEquiv.ofSurjective W hsurj
  have hU : ∀ ψ, U ψ = V ψ := fun ψ => rfl
  refine ⟨U, fun ψ => ?_⟩
  obtain ⟨h, e⟩ := boundedInverse_right hR ψ
  refine ⟨⟨h, ?_⟩, hU ψ⟩
  rw [hU, hVshift ψ h e]
  rfl
theorem eq_of_isExtendedBy {A A' : UnboundedOp H} (hA : IsSelfAdj A)
    (hA' : IsSelfAdj A') (hc : IsExtendedBy A A') : A' = A := by
  obtain ⟨hle, hv⟩ := hc
  have hmem : ∀ φ : A'.domain, ∃ hφ : (φ : H) ∈ A.domain, A ⟨φ, hφ⟩ = A' φ := by
    intro φ
    refine mem_domain_of_inner_eq hA fun χ => ?_
    rw [← hv χ]
    exact inner_map_symm hA' φ ⟨χ, hle χ.2⟩
  have hdom : A'.domain = A.domain :=
    le_antisymm (fun φ hφ => (hmem ⟨φ, hφ⟩).1) hle
  refine (unboundedOp_eq_iff _ _).2 ⟨hdom, fun χ => ?_⟩
  exact (hmem χ).2
end Shifts
section BoundedCalculus
set_option linter.unusedSectionVars false
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
  {E : BorelSubset n → H →L[ℂ] H}
theorem isBoundedMeasurableFn_const (c : ℂ) : IsBoundedMeasurableFn fun _ : Space n => c :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩
theorem isBoundedMeasurableFn_indicator (Δ : BorelSubset n) :
    IsBoundedMeasurableFn (Δ.1.indicator fun _ => (1 : ℂ)) := by apply _root_.YangMills.Construction.EuclideanBorel.FunctionalCalculus.boundedFn_indicator <;> assumption
theorem isBoundedMeasurableFn_add_mul {f g : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) (c : ℂ) : IsBoundedMeasurableFn fun y => f y + c * g y := by apply _root_.YangMills.Construction.PositiveFormReconstruction.CompletionEnergyBound.isBoundedMeasurableFn_add_mul <;> assumption
theorem isBoundedMeasurableFn_mul {f g : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (hg : IsBoundedMeasurableFn g) : IsBoundedMeasurableFn fun y => f y * g y := by apply _root_.YangMills.Construction.PositiveFormReconstruction.CompletionEnergyBound.isBoundedMeasurableFn_mul <;> assumption
theorem boundedCalculus_apply_eq (ht : CutoffsConverge E) {f : Space n → ℂ}
    (hf : IsBoundedMeasurableFn f) {B : H → H} (h : SpectralIntegralIs E f B) (ψ : H) :
    boundedCalculus E f ψ = B ψ := by
  have hmem : ψ ∈ sqIntegrableDomain E f := by
    rw [h.1]
    exact mem_univ ψ
  rw [← h.2 ⟨ψ, hmem⟩, spectralIntegral_eq_boundedCalculus ht hf]
theorem boundedCalculus_one (hr : BoundedCalculusProperties E) (hE : IsPVM E) :
    boundedCalculus E (fun _ => (1 : ℂ)) = 1 := by
  have h := hr.2.2.1 ⊤
  rw [hE.map_top] at h
  have he : ((⊤ : BorelSubset n).1.indicator fun _ => (1 : ℂ)) = fun _ => 1 := by
    funext y
    exact Set.indicator_of_mem (show y ∈ (⊤ : BorelSubset n).1 from mem_univ y) _
  rwa [he] at h
theorem boundedCalculus_zero (hr : BoundedCalculusProperties E) :
    boundedCalculus E (fun _ => (0 : ℂ)) = 0 := by
  have h := (hr.1 (fun _ => 0) (fun _ => 0) (-1) (isBoundedMeasurableFn_const 0)
    (isBoundedMeasurableFn_const 0)).1
  simp only [mul_zero, add_zero] at h
  simpa using h
theorem boundedCalculus_const_mul (hr : BoundedCalculusProperties E) {g : Space n → ℂ}
    (hg : IsBoundedMeasurableFn g) (c : ℂ) :
    boundedCalculus E (fun y => c * g y) = c • boundedCalculus E g := by
  have h := (hr.1 (fun _ => 0) g c (isBoundedMeasurableFn_const 0) hg).1
  simp only [zero_add] at h
  rw [h, boundedCalculus_zero hr, zero_add]
theorem map_eq_zero_of_empty (hr : BoundedCalculusProperties E) (Δ : BorelSubset n) (h : Δ.1 = ∅) :
    E Δ = 0 := by
  rw [← hr.2.2.1 Δ, h, Set.indicator_empty]
  exact boundedCalculus_zero hr
theorem isSpectralIntegralOp_of_flip {E : BorelSubset n → H →L[ℂ] H} {f : Space n → ℂ}
    {A : UnboundedOp H} (h : RealizesSpectralIntegral E f A) : IsSpectralIntegralOp A E f := by apply _root_.YangMills.Construction.PositiveFormReconstruction.PositiveContractionGenerator.isSpectralIntegralOp_of_isOp <;> assumption
theorem isSpectralIntegralOp_flip {E : BorelSubset n → H →L[ℂ] H} {f : Space n → ℂ}
    {A : UnboundedOp H} (h : IsSpectralIntegralOp A E f) : RealizesSpectralIntegral E f A := by apply _root_.YangMills.Construction.EuclideanBorel.SpectralRules.op_of_integralOp <;> assumption
theorem spectralIntegralIs_of_eq {m : ℕ} {E₁ : BorelSubset m → H →L[ℂ] H}
    {f₁ : Space m → ℂ} {f₂ : Space n → ℂ} {A : UnboundedOp H} {B : H → H}
    (h₁ : RealizesSpectralIntegral E₁ f₁ A) (h₂ : RealizesSpectralIntegral E f₂ A)
    (h : SpectralIntegralIs E f₂ B) : SpectralIntegralIs E₁ f₁ B := by
  refine ⟨h₁.1.symm.trans (h₂.1.trans h.1), fun ψ => ?_⟩
  have hA : (ψ : H) ∈ A.domain := by
    exact show (ψ : H) ∈ (A.domain : Set H) from by
      rw [h₁.1]
      exact ψ.2
  obtain ⟨a₁, e₁⟩ := h₁.2 ⟨ψ, hA⟩
  obtain ⟨a₂, e₂⟩ := h₂.2 ⟨ψ, hA⟩
  refine e₁.trans (e₂.symm.trans ?_)
  exact h.2 ⟨ψ, a₂⟩
end BoundedCalculus
section Circle
theorem measurable_apply_coord {n : ℕ} (i : Fin n) :
    Measurable (β := ℝ) fun y : Space n => y i :=
  (by fun_prop : Continuous fun y : Space n => y i).measurable
theorem norm_eq_one_iff_sq_add_sq (y : Space 2) : ‖y‖ = 1 ↔ y 0 ^ 2 + y 1 ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]
def circleMinusOne : Set (Space 2) := {y | ‖y‖ = 1 ∧ y 0 ≠ 1}
theorem measurableSet_circleMinusOne : MeasurableSet circleMinusOne :=
  (measurableSet_eq_fun measurable_norm measurable_const).inter
    (measurableSet_eq_fun (measurable_apply_coord 0) measurable_const).compl
def cayleyCoord (y : Space 2) : ℝ :=
  circleMinusOne.indicator (fun y : Space 2 => -y 1 / (1 - y 0)) y
theorem measurable_cayleyCoord : Measurable cayleyCoord :=
  (((measurable_apply_coord 1).neg).div
    (measurable_const.sub (measurable_apply_coord 0))).indicator measurableSet_circleMinusOne
def circleToReal (y : Space 2) : Space 1 := WithLp.toLp 2 fun _ => cayleyCoord y
theorem measurable_circleToReal : Measurable circleToReal :=
  (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_lambda _ fun _ => measurable_cayleyCoord)
def realToCircle (y : Space 1) : Space 2 :=
  WithLp.toLp 2 ![(y 0 ^ 2 - 1) / (y 0 ^ 2 + 1), -(2 * y 0) / (y 0 ^ 2 + 1)]
theorem realToCircle_apply_zero (y : Space 1) :
    realToCircle y 0 = (y 0 ^ 2 - 1) / (y 0 ^ 2 + 1) := rfl
theorem realToCircle_apply_one (y : Space 1) :
    realToCircle y 1 = -(2 * y 0) / (y 0 ^ 2 + 1) := rfl
theorem measurable_realToCircle : Measurable realToCircle := by
  have h₀ := measurable_apply_coord (n := 1) 0
  have hd : Measurable fun y : Space 1 => y 0 ^ 2 + 1 := (h₀.pow_const 2).add_const 1
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun i => ?_)
  fin_cases i
  · exact ((h₀.pow_const 2).sub_const 1).div hd
  · exact ((h₀.const_mul 2).neg).div hd
theorem realToCircle_mem (y : Space 1) : realToCircle y ∈ circleMinusOne := by
  have hpos : y 0 ^ 2 + 1 ≠ 0 := by positivity
  refine ⟨(norm_eq_one_iff_sq_add_sq _).2 ?_, ?_⟩
  · rw [realToCircle_apply_zero, realToCircle_apply_one]
    field_simp
    ring
  · rw [realToCircle_apply_zero]
    intro h
    field_simp at h
    linarith
theorem circleToReal_realToCircle (y : Space 1) : circleToReal (realToCircle y) = y := by
  have hpos : y 0 ^ 2 + 1 ≠ 0 := by positivity
  have h : cayleyCoord (realToCircle y) = y 0 := by
    rw [cayleyCoord, Set.indicator_of_mem (realToCircle_mem y), realToCircle_apply_zero,
      realToCircle_apply_one]
    have h₁ : 1 - (y 0 ^ 2 - 1) / (y 0 ^ 2 + 1) = 2 / (y 0 ^ 2 + 1) := by
      field_simp
      ring
    rw [h₁]
    field_simp
  ext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact h
def toComplexPoint (y : Space 2) : ℂ := (y 0 : ℂ) + Complex.I * (y 1 : ℂ)
theorem measurable_toComplexPoint : Measurable toComplexPoint :=
  (Complex.measurable_ofReal.comp (measurable_apply_coord 0)).add
    ((Complex.measurable_ofReal.comp (measurable_apply_coord 1)).const_mul Complex.I)
theorem norm_toComplexPoint {y : Space 2} (hy : ‖y‖ = 1) : ‖toComplexPoint y‖ = 1 := by
  have h := (norm_eq_one_iff_sq_add_sq y).1 hy
  rw [toComplexPoint, mul_comm, Complex.norm_add_mul_I, h, Real.sqrt_one]
theorem circleChar_of_norm_eq_one (k : ℤ) {y : Space 2} (hy : ‖y‖ = 1) :
    circleChar k y = toComplexPoint y ^ k :=
  Set.indicator_of_mem (show y ∈ planeUnitCircle from hy) _
theorem circleChar_of_norm_ne_one (k : ℤ) {y : Space 2} (hy : ‖y‖ ≠ 1) :
    circleChar k y = 0 :=
  Set.indicator_of_notMem (show y ∉ planeUnitCircle from hy) _
theorem measurable_circleChar (k : ℤ) : Measurable (circleChar k) :=
  (measurable_toComplexPoint.pow_const k).indicator planeUnitCircleBorel.2
theorem isBoundedMeasurableFn_circleChar (k : ℤ) : IsBoundedMeasurableFn (circleChar k) := by apply _root_.YangMills.Construction.EuclideanBorel.MeasureUniqueness.isBoundedMeasurableFn_circleChar <;> assumption
def circleResolvent (y : Space 2) : ℂ :=
  (2 * Complex.I)⁻¹ * (circleChar 0 y + -1 * circleChar 1 y)
def circleHalfSum (y : Space 2) : ℂ :=
  (1 / 2) * (circleChar 0 y + 1 * circleChar 1 y)
theorem isBoundedMeasurableFn_circleResolvent : IsBoundedMeasurableFn circleResolvent :=
  isBoundedMeasurableFn_mul (isBoundedMeasurableFn_const _)
    (isBoundedMeasurableFn_add_mul (isBoundedMeasurableFn_circleChar 0)
      (isBoundedMeasurableFn_circleChar 1) (-1))
theorem isBoundedMeasurableFn_circleHalfSum : IsBoundedMeasurableFn circleHalfSum :=
  isBoundedMeasurableFn_mul (isBoundedMeasurableFn_const _)
    (isBoundedMeasurableFn_add_mul (isBoundedMeasurableFn_circleChar 0)
      (isBoundedMeasurableFn_circleChar 1) 1)
theorem circleResolvent_of_not_mem {y : Space 2} (hy : y ∉ circleMinusOne) :
    circleResolvent y = 0 := by
  rw [circleResolvent]
  by_cases h : ‖y‖ = 1
  · have h₀ : y 0 = 1 := by
      by_contra h'
      exact hy ⟨h, h'⟩
    have h₁ : y 1 = 0 := by
      have h₂ := (norm_eq_one_iff_sq_add_sq y).1 h
      rw [h₀] at h₂
      nlinarith
    rw [circleChar_of_norm_eq_one _ h, circleChar_of_norm_eq_one _ h, toComplexPoint, h₀, h₁]
    simp
  · rw [circleChar_of_norm_ne_one _ h, circleChar_of_norm_ne_one _ h]
    simp
theorem cayleyCoord_mul_circleResolvent {y : Space 2} (hy : y ∈ circleMinusOne) :
    (cayleyCoord y : ℂ) * circleResolvent y = circleHalfSum y := by
  obtain ⟨hn, h₀⟩ := id hy
  have hsq : ((y 0 : ℝ) : ℂ) ^ 2 + ((y 1 : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      (norm_eq_one_iff_sq_add_sq y).1 hn, Complex.ofReal_one]
  have hne : 1 - ((y 0 : ℝ) : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (Ne.symm h₀)
  rw [circleResolvent, circleHalfSum, cayleyCoord, Set.indicator_of_mem hy,
    circleChar_of_norm_eq_one _ hn, circleChar_of_norm_eq_one _ hn, zpow_zero, zpow_one,
    toComplexPoint]
  push_cast
  have key : -((y 1 : ℝ) : ℂ) * (1 + -1 * (((y 0 : ℝ) : ℂ) + Complex.I * ((y 1 : ℝ) : ℂ))) =
      Complex.I * (1 - ((y 0 : ℝ) : ℂ)) *
        (1 + 1 * (((y 0 : ℝ) : ℂ) + Complex.I * ((y 1 : ℝ) : ℂ))) := by
    linear_combination Complex.I * hsq - ((y 1 : ℝ) : ℂ) * (1 - ((y 0 : ℝ) : ℂ)) * Complex.I_sq
  have h₁ : -((y 1 : ℝ) : ℂ) / (1 - ((y 0 : ℝ) : ℂ)) * ((2 * Complex.I)⁻¹ *
      (1 + -1 * (((y 0 : ℝ) : ℂ) + Complex.I * ((y 1 : ℝ) : ℂ)))) =
      (-((y 1 : ℝ) : ℂ) * (1 + -1 * (((y 0 : ℝ) : ℂ) + Complex.I * ((y 1 : ℝ) : ℂ)))) /
        ((1 - ((y 0 : ℝ) : ℂ)) * (2 * Complex.I)) := by
    field_simp
  rw [h₁, key]
  field_simp
def realResolvent (y : Space 1) : ℂ := (lineCoord y + Complex.I)⁻¹
theorem lineCoord_apply (y : Space 1) : lineCoord y = ((y 0 : ℝ) : ℂ) := rfl
theorem measurable_lineCoord : Measurable lineCoord :=
  Complex.measurable_ofReal.comp (measurable_apply_coord 0)
theorem one_le_norm_lineCoord_add_I (y : Space 1) : 1 ≤ ‖lineCoord y + Complex.I‖ := by
  have h := Complex.abs_im_le_norm (lineCoord y + Complex.I)
  simpa [lineCoord_apply] using h
theorem lineCoord_add_I_ne_zero (y : Space 1) : lineCoord y + Complex.I ≠ 0 := by
  intro h
  have := one_le_norm_lineCoord_add_I y
  rw [h, norm_zero] at this
  linarith
theorem isBoundedMeasurableFn_realResolvent : IsBoundedMeasurableFn realResolvent := by
  refine ⟨(measurable_lineCoord.add_const _).inv, 1, fun y => ?_⟩
  rw [realResolvent, norm_inv]
  exact inv_le_one_of_one_le₀ (one_le_norm_lineCoord_add_I y)
def lineCoordMulResolvent (y : Space 1) : ℂ := lineCoord y * realResolvent y
theorem isBoundedMeasurableFn_lineCoordMulResolvent :
    IsBoundedMeasurableFn lineCoordMulResolvent := by
  refine ⟨measurable_lineCoord.mul isBoundedMeasurableFn_realResolvent.1, 1, fun y => ?_⟩
  have hpos : 0 < ‖lineCoord y + Complex.I‖ :=
    lt_of_lt_of_le one_pos (one_le_norm_lineCoord_add_I y)
  rw [lineCoordMulResolvent, realResolvent, norm_mul, norm_inv, ← div_eq_mul_inv, div_le_one hpos]
  have h := Complex.abs_re_le_norm (lineCoord y + Complex.I)
  simpa [lineCoord_apply] using h
def cayleyFn (y : Space 1) : ℂ := 1 + -(2 * Complex.I) * realResolvent y
theorem measurable_cayleyFn : Measurable cayleyFn :=
  measurable_const.add (isBoundedMeasurableFn_realResolvent.1.const_mul _)
theorem toComplexPoint_realToCircle (y : Space 1) :
    toComplexPoint (realToCircle y) = cayleyFn y := by
  have hne := lineCoord_add_I_ne_zero y
  rw [lineCoord_apply] at hne
  have hsq : ((y 0 : ℝ) : ℂ) ^ 2 + 1 =
      (((y 0 : ℝ) : ℂ) + Complex.I) * (((y 0 : ℝ) : ℂ) - Complex.I) := by
    linear_combination Complex.I_sq
  have hne₂ : ((y 0 : ℝ) : ℂ) - Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  rw [toComplexPoint, realToCircle_apply_zero, realToCircle_apply_one, cayleyFn, realResolvent,
    lineCoord_apply]
  push_cast
  rw [hsq]
  field_simp
  linear_combination -Complex.I_sq
theorem norm_cayleyFn (y : Space 1) : ‖cayleyFn y‖ = 1 := by
  rw [← toComplexPoint_realToCircle]
  exact norm_toComplexPoint (realToCircle_mem y).1
theorem cayleyFn_ne_zero (y : Space 1) : cayleyFn y ≠ 0 := by
  intro h
  have := norm_cayleyFn y
  rw [h, norm_zero] at this
  exact zero_ne_one this
theorem isBoundedMeasurableFn_cayleyFn_zpow (k : ℤ) :
    IsBoundedMeasurableFn fun y => cayleyFn y ^ k := by
  refine ⟨measurable_cayleyFn.pow_const k, 1, fun y => ?_⟩
  rw [norm_zpow, norm_cayleyFn, one_zpow]
theorem circleChar_comp_realToCircle (k : ℤ) :
    circleChar k ∘ realToCircle = fun y => cayleyFn y ^ k := by
  funext y
  rw [Function.comp_apply, circleChar_of_norm_eq_one k (realToCircle_mem y).1,
    toComplexPoint_realToCircle]
end Circle
section Main
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem isSpectralResolution_pushforward (hcal : FunctionalCalculus.Statement)
    (hint : BoundedBorelCalculusTheorem) {A : UnboundedOp H}
    (hA : IsSelfAdj A) (hK : EqTopOfOrthogonalTrivial H)
    {U : UnitaryMap H H} (hU : IsCayleyTransform A U) {E : BorelSubset 2 → H →L[ℂ] H}
    (hEU : IsUnitarySpectralMeasure U E) :
    IsSpectralResolution A (pushforward E circleToReal measurable_circleToReal) := by
  obtain ⟨hE, -, hk⟩ := hEU
  obtain ⟨-, -, -, -, hr, ht⟩ := hint 2 (by norm_num) H E hE
  have hR := resolventAtI_spec hA hK
  set R := resolventAtI A
  have hUa : ∀ ψ, U ψ = ψ - (2 * Complex.I) • R ψ := fun ψ => (hU ψ).2
  have hI : (2 * Complex.I) ≠ 0 := by simp
  have hb₀ := isBoundedMeasurableFn_circleChar 0
  have hb₁ := isBoundedMeasurableFn_circleChar 1
  have hB₀ : ∀ ψ, boundedCalculus E (circleChar 0) ψ = ψ := fun ψ => by
    rw [boundedCalculus_apply_eq ht hb₀ (hk 0) ψ, zpow_zero]
    rfl
  have hB₁ : ∀ ψ, boundedCalculus E (circleChar 1) ψ = U ψ := fun ψ => by
    rw [boundedCalculus_apply_eq ht hb₁ (hk 1) ψ, zpow_one]
  have hbg := isBoundedMeasurableFn_circleResolvent
  have hBg : ∀ ψ, boundedCalculus E circleResolvent ψ = R ψ := fun ψ => by
    have h₁ : boundedCalculus E circleResolvent = (2 * Complex.I)⁻¹ •
        boundedCalculus E (fun y => circleChar 0 y + -1 * circleChar 1 y) :=
      boundedCalculus_const_mul hr (isBoundedMeasurableFn_add_mul hb₀ hb₁ (-1)) _
    rw [h₁, (hr.1 _ _ (-1) hb₀ hb₁).1]
    simp only [smul_apply, add_apply]
    rw [hB₀, hB₁, hUa]
    have h₂ : ψ + (-1 : ℂ) • (ψ - (2 * Complex.I) • R ψ) = (2 * Complex.I) • R ψ := by module
    rw [h₂, smul_smul, inv_mul_cancel₀ hI, one_smul]
  have hBh : ∀ ψ, boundedCalculus E circleHalfSum ψ = (1 / 2 : ℂ) • (ψ + U ψ) := fun ψ => by
    have h₁ : boundedCalculus E circleHalfSum = (1 / 2 : ℂ) •
        boundedCalculus E (fun y => circleChar 0 y + 1 * circleChar 1 y) :=
      boundedCalculus_const_mul hr (isBoundedMeasurableFn_add_mul hb₀ hb₁ 1) _
    rw [h₁, (hr.1 _ _ 1 hb₀ hb₁).1]
    simp only [smul_apply, add_apply, one_smul]
    rw [hB₀, hB₁]
  let X : BorelSubset 2 := ⟨circleMinusOne, measurableSet_circleMinusOne⟩
  let Z : BorelSubset 2 := ⟨circleMinusOneᶜ, measurableSet_circleMinusOne.compl⟩
  have hEZ : E Z = 0 := by
    have hzero : (fun y => circleResolvent y * Z.1.indicator (fun _ => (1 : ℂ)) y) =
        fun _ => 0 := by
      funext y
      by_cases hy : y ∈ circleMinusOne
      · have h₁ : y ∉ Z.1 := fun h => h hy
        rw [Set.indicator_of_notMem h₁, mul_zero]
      · rw [circleResolvent_of_not_mem hy, zero_mul]
    have hp := (hr.1 circleResolvent (Z.1.indicator fun _ => (1 : ℂ)) 0 hbg
      (isBoundedMeasurableFn_indicator Z)).2
    rw [hzero, boundedCalculus_zero hr, hr.2.2.1 Z] at hp
    refine ContinuousLinearMap.ext fun ψ => boundedInverse_injective hR ?_
    have h₁ := congrArg (fun T : H →L[ℂ] H => T ψ) hp
    simp only [zero_apply, mul_apply_eq_comp] at h₁
    rw [hBg] at h₁
    simpa using h₁.symm
  have hEX : E X = 1 := by
    have hone : (fun y => X.1.indicator (fun _ => (1 : ℂ)) y +
        1 * Z.1.indicator (fun _ => (1 : ℂ)) y) = fun _ => 1 := by
      funext y
      by_cases hy : y ∈ circleMinusOne
      · have h₁ : y ∉ Z.1 := fun h => h hy
        have h₂ : y ∈ X.1 := hy
        rw [Set.indicator_of_notMem h₁, Set.indicator_of_mem h₂]
        simp
      · have h₁ : y ∈ Z.1 := hy
        have h₂ : y ∉ X.1 := hy
        rw [Set.indicator_of_mem h₁, Set.indicator_of_notMem h₂]
        simp
    have hs := (hr.1 (X.1.indicator fun _ => (1 : ℂ)) (Z.1.indicator fun _ => (1 : ℂ)) 1
      (isBoundedMeasurableFn_indicator X) (isBoundedMeasurableFn_indicator Z)).1
    rw [hone, boundedCalculus_one hr hE, hr.2.2.1 X, hr.2.2.1 Z, hEZ] at hs
    simpa using hs.symm
  let kc : Space 2 → ℂ := lineCoord ∘ circleToReal
  have hkc : Measurable kc := measurable_lineCoord.comp measurable_circleToReal
  have hkcapply : ∀ y, kc y = (cayleyCoord y : ℂ) := fun _ => rfl
  have hprodfun : (fun y => kc y * circleResolvent y) =
      fun y => circleHalfSum y * X.1.indicator (fun _ => (1 : ℂ)) y := by
    funext y
    rw [hkcapply]
    by_cases hy : y ∈ circleMinusOne
    · have h₂ : y ∈ X.1 := hy
      rw [cayleyCoord_mul_circleResolvent hy, Set.indicator_of_mem h₂, mul_one]
    · have h₂ : y ∉ X.1 := hy
      rw [circleResolvent_of_not_mem hy, Set.indicator_of_notMem h₂, mul_zero, mul_zero]
  have hbkg : IsBoundedMeasurableFn fun y => kc y * circleResolvent y := by
    rw [hprodfun]
    exact isBoundedMeasurableFn_mul isBoundedMeasurableFn_circleHalfSum
      (isBoundedMeasurableFn_indicator X)
  have hBkg : ∀ ψ, boundedCalculus E (fun y => kc y * circleResolvent y) ψ =
      (1 / 2 : ℂ) • (ψ + U ψ) := fun ψ => by
    rw [hprodfun, (hr.1 _ _ 0 isBoundedMeasurableFn_circleHalfSum
      (isBoundedMeasurableFn_indicator X)).2, hr.2.2.1 X, hEX]
    simp only [mul_one]
    exact hBh ψ
  obtain ⟨hdom, -, hadj, hprod, -, -, -, himage, -, -, -⟩ :=
    hcal 2 1 H E hE kc circleResolvent hkc hbg.1 0
  have hiso := hdom.isOp
  have hsa : IsSelfAdj (spectralOp E kc) :=
    hadj.2 fun y => by rw [hkcapply]; exact Complex.ofReal_im _
  have key : ∀ χ : A.domain, ∃ h : (χ : H) ∈ (spectralOp E kc).domain,
      spectralOp E kc ⟨χ, h⟩ = A χ := by
    intro χ
    obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = A χ + Complex.I • (χ : H) := ⟨_, rfl⟩
    have hRψ : R ψ = χ := by rw [hψ]; exact boundedInverse_left hR χ
    have hgψ : ψ ∈ sqIntegrableDomain E circleResolvent := by
      rw [(ht.2 _ hbg).1]
      exact mem_univ ψ
    have hgval : spectralIntegral E circleResolvent ⟨ψ, hgψ⟩ = χ := by
      rw [spectralIntegral_eq_boundedCalculus ht hbg, hBg, hRψ]
    obtain ⟨-, hiff, hval⟩ := hprod ψ hgψ
    rw [hgval] at hiff hval
    have hkgψ : ψ ∈ sqIntegrableDomain E fun y => kc y * circleResolvent y := by
      rw [(ht.2 _ hbkg).1]
      exact mem_univ ψ
    have hχD := hiff.2 hkgψ
    have hχA : (χ : H) ∈ (spectralOp E kc).domain := by
      exact show (χ : H) ∈ ((spectralOp E kc).domain : Set H) from by
        rw [hiso.1]
        exact hχD
    refine ⟨hχA, ?_⟩
    obtain ⟨h₁, e₁⟩ := hiso.2 ⟨χ, hχA⟩
    obtain ⟨h₂, e₂⟩ := hval hχD
    rw [← e₁]
    refine e₂.symm.trans ?_
    have h₉ : (1 / 2 : ℂ) • (ψ + (ψ - (2 * Complex.I) • (χ : H))) = A χ := by
      rw [hψ]
      module
    rw [spectralIntegral_eq_boundedCalculus ht hbkg, hBkg, hUa, hRψ]
    exact h₉
  have hsub : IsExtendedBy A (spectralOp E kc) :=
    ⟨fun χ hχ => (key ⟨χ, hχ⟩).1, fun χ => (key χ).2⟩
  have hAeq := eq_of_isExtendedBy hA hsa hsub
  obtain ⟨hpv, hop⟩ := himage circleToReal measurable_circleToReal
  refine ⟨hpv, isSpectralIntegralOp_of_flip ?_⟩
  have hi := (hcal 1 1 H _ hpv lineCoord lineCoord measurable_lineCoord
    measurable_lineCoord 0).1.isOp
  rw [hop lineCoord measurable_lineCoord] at hi
  exact hAeq ▸ hi
theorem isUnitarySpectralMeasure_pushforward (hcal : FunctionalCalculus.Statement)
    (hint : BoundedBorelCalculusTheorem) {A : UnboundedOp H}
    (hA : IsSelfAdj A) (hK : EqTopOfOrthogonalTrivial H)
    {U : UnitaryMap H H} (hU : IsCayleyTransform A U) {E : BorelSubset 1 → H →L[ℂ] H}
    (hS : IsSpectralResolution A E) :
    IsUnitarySpectralMeasure U (pushforward E realToCircle measurable_realToCircle) := by
  obtain ⟨hE, hInt⟩ := hS
  obtain ⟨-, -, -, -, hr, ht⟩ := hint 1 le_rfl H E hE
  have hR := resolventAtI_spec hA hK
  set R := resolventAtI A
  have hop := isSpectralIntegralOp_flip hInt
  have hbg := isBoundedMeasurableFn_realResolvent
  have hbk := isBoundedMeasurableFn_lineCoordMulResolvent
  have h1 := isBoundedMeasurableFn_const (n := 1) (1 : ℂ)
  have hone := boundedCalculus_one hr hE
  obtain ⟨-, -, -, hprod, -, -, -, himage, -, -, -⟩ :=
    hcal 1 2 H E hE lineCoord realResolvent measurable_lineCoord hbg.1 0
  have hRg : ∀ ψ, R ψ = boundedCalculus E realResolvent ψ := by
    intro ψ
    have hgψ : ψ ∈ sqIntegrableDomain E realResolvent := by
      rw [(ht.2 _ hbg).1]
      exact mem_univ ψ
    obtain ⟨χ, hχ⟩ : ∃ χ, χ = boundedCalculus E realResolvent ψ := ⟨_, rfl⟩
    have hgval : spectralIntegral E realResolvent ⟨ψ, hgψ⟩ = χ := by
      rw [spectralIntegral_eq_boundedCalculus ht hbg, hχ]
    obtain ⟨-, hiff, hval⟩ := hprod ψ hgψ
    rw [hgval] at hiff hval
    have hkψ : ψ ∈ sqIntegrableDomain E fun y => lineCoord y * realResolvent y := by
      have := (ht.2 _ hbk).1
      unfold lineCoordMulResolvent at this
      rw [this]
      exact mem_univ ψ
    have hχD := hiff.2 hkψ
    have hχA : χ ∈ A.domain := by
      exact show χ ∈ (A.domain : Set H) from by
        rw [hop.1]
        exact hχD
    obtain ⟨h₁, e₁⟩ := hop.2 ⟨χ, hχA⟩
    obtain ⟨h₂, e₂⟩ := hval hχD
    have hAχ : A ⟨χ, hχA⟩ = boundedCalculus E lineCoordMulResolvent ψ := by
      rw [← e₁]
      refine e₂.symm.trans ?_
      exact spectralIntegral_eq_boundedCalculus ht hbk ⟨ψ, h₂⟩
    have hsum : A ⟨χ, hχA⟩ + Complex.I • χ = ψ := by
      have hfun : (fun y => lineCoordMulResolvent y + Complex.I * realResolvent y) =
          fun _ => (1 : ℂ) := by
        funext y
        rw [lineCoordMulResolvent, realResolvent, ← add_mul]
        exact mul_inv_cancel₀ (lineCoord_add_I_ne_zero y)
      have h₃ := (hr.1 lineCoordMulResolvent realResolvent Complex.I hbk hbg).1
      rw [hfun, hone] at h₃
      have h₄ := congrArg (fun T : H →L[ℂ] H => T ψ) h₃
      simp only [one_apply_eq_self, add_apply, smul_apply] at h₄
      rw [hAχ, hχ]
      exact h₄.symm
    have h₅ := boundedInverse_left hR ⟨χ, hχA⟩
    simp only at h₅
    rw [hsum] at h₅
    rw [h₅, hχ]
  have hζ : ∀ ψ, boundedCalculus E cayleyFn ψ = U ψ := by
    intro ψ
    have h₃ : boundedCalculus E cayleyFn = boundedCalculus E (fun _ => (1 : ℂ)) +
        (-(2 * Complex.I)) • boundedCalculus E realResolvent :=
      (hr.1 (fun _ => 1) realResolvent (-(2 * Complex.I)) h1 hbg).1
    rw [h₃, hone, (hU ψ).2]
    simp only [one_apply_eq_self, add_apply, smul_apply]
    rw [← hRg, neg_smul, sub_eq_add_neg]
  have hbζ : IsBoundedMeasurableFn cayleyFn := by
    have := isBoundedMeasurableFn_cayleyFn_zpow 1
    simpa only [zpow_one] using this
  have hbι : IsBoundedMeasurableFn fun y => (cayleyFn y)⁻¹ := by
    have := isBoundedMeasurableFn_cayleyFn_zpow (-1)
    simpa only [zpow_neg_one] using this
  have hW : ∀ φ, boundedCalculus E (fun y => (cayleyFn y)⁻¹) (U φ) = φ := by
    intro φ
    have hfun : (fun y => (cayleyFn y)⁻¹ * cayleyFn y) = fun _ => (1 : ℂ) := by
      funext y
      exact inv_mul_cancel₀ (cayleyFn_ne_zero y)
    have h₃ := (hr.1 _ _ 0 hbι hbζ).2
    rw [hfun, hone] at h₃
    have h₄ := congrArg (fun T : H →L[ℂ] H => T φ) h₃
    simp only [one_apply_eq_self, mul_apply_eq_comp] at h₄
    rw [hζ] at h₄
    exact h₄.symm
  have hWinv : ∀ φ, boundedCalculus E (fun y => (cayleyFn y)⁻¹) φ =
      (U⁻¹ : UnitaryMap H H) φ := by
    intro φ
    have h₃ : U ((U⁻¹ : UnitaryMap H H) φ) = φ := by
      exact show (U * U⁻¹ : UnitaryMap H H) φ = φ from by
        rw [mul_inv_cancel]
        rfl
    have h₄ := hW ((U⁻¹ : UnitaryMap H H) φ)
    rwa [h₃] at h₄
  have hzk : ∀ (k : ℤ) (ψ : H), boundedCalculus E (fun y => cayleyFn y ^ k) ψ =
      (U ^ k : UnitaryMap H H) ψ := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · intro ψ
      simp only [zpow_zero]
      rw [hone]
      rfl
    · intro i ih ψ
      have hfun : (fun y => cayleyFn y ^ ((i : ℤ) + 1)) =
          fun y => cayleyFn y ^ (i : ℤ) * cayleyFn y := by
        funext y
        exact zpow_add_one₀ (cayleyFn_ne_zero y) _
      rw [hfun, (hr.1 _ _ 0 (isBoundedMeasurableFn_cayleyFn_zpow i) hbζ).2,
        mul_apply_eq_comp, hζ, ih, zpow_add_one]
      rfl
    · intro i ih ψ
      have hfun : (fun y => cayleyFn y ^ (-(i : ℤ) - 1)) =
          fun y => cayleyFn y ^ (-(i : ℤ)) * (cayleyFn y)⁻¹ := by
        funext y
        exact zpow_sub_one₀ (cayleyFn_ne_zero y) _
      rw [hfun, (hr.1 _ _ 0 (isBoundedMeasurableFn_cayleyFn_zpow (-(i : ℤ))) hbι).2,
        mul_apply_eq_comp, hWinv, ih, zpow_sub_one]
      rfl
  obtain ⟨hpv, hop'⟩ := himage realToCircle measurable_realToCircle
  refine ⟨hpv, ?_, fun k => ?_⟩
  · refine map_eq_zero_of_empty hr _ ?_
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    exact hy (realToCircle_mem y).1
  · have hmk := measurable_circleChar k
    have hi₁ := (hcal 2 2 H _ hpv (circleChar k) (circleChar k) hmk hmk 0).1.isOp
    have hb := isBoundedMeasurableFn_cayleyFn_zpow k
    have hi₂ := (hcal 1 1 H E hE _ _ hb.1 hb.1 0).1.isOp
    rw [hop' (circleChar k) hmk, circleChar_comp_realToCircle] at hi₁
    exact spectralIntegralIs_of_eq hi₁ hi₂
      ⟨(ht.2 _ hb).1, fun ψ => (spectralIntegral_eq_boundedCalculus ht hb ψ).trans (hzk k ψ)⟩
theorem commutes_resolventAtI_of_ofCLM {A : UnboundedOp H} {R T B : H →L[ℂ] H}
    (hR : IsBoundedInverse R (addConst A Complex.I)) (hT : A = ofCLM T)
    (hB : Commutes B T) : Commutes B R := by
  subst hT
  refine ContinuousLinearMap.ext fun ψ => ?_
  have hTB : ∀ x, B (T x) = T (B x) := fun x =>
    congrArg (fun S : H →L[ℂ] H => S x) hB
  obtain ⟨h, e⟩ := boundedInverse_right hR ψ
  have e' : T (R ψ) + Complex.I • R ψ = ψ := e
  have h₁ := boundedInverse_left hR (A := ofCLM T) ⟨B (R ψ), Submodule.mem_top⟩
  have h₂ : ofCLM T ⟨B (R ψ), Submodule.mem_top⟩ + Complex.I • B (R ψ) = B ψ := by
    have h₃ : ofCLM T ⟨B (R ψ), Submodule.mem_top⟩ = T (B (R ψ)) := rfl
    rw [h₃, ← hTB, ← map_smul, ← map_add, e']
  simp only at h₁
  rw [h₂] at h₁
  exact h₁.symm
end Main
theorem spectralTheorem_holds (h₁ : FunctionalCalculus.Statement)
    (h₂ : BoundedBorelCalculusTheorem)
    (h₃ : BoundedRepresentation.Claim)
    (h₄ : UnitarySpectral.ExistsUnique) : SelfAdjoint.SpectralTheorem := by
  intro H _ _ _ A hA
  have hK := (h₃ H 0 le_rfl).2.2.2.2.1
  obtain ⟨U, hU⟩ := exists_cayleyTransform hA hK
  obtain ⟨huniq, hspec, hcomm⟩ := h₄ H U
  have hR := resolventAtI_spec hA hK
  have hex := isSpectralResolution_pushforward h₁ h₂ hA hK hU hspec
  have hun : ∀ E, IsSpectralResolution A E →
      E = pushforward (unitarySpectralMeasure U) circleToReal measurable_circleToReal := by
    intro E hE
    have he := huniq.unique (isUnitarySpectralMeasure_pushforward h₁ h₂ hA hK hU hE) hspec
    funext Δ
    rw [pushforward, ← he]
    refine congrArg E (Subtype.ext ?_)
    ext y
    change y ∈ Δ.1 ↔ circleToReal (realToCircle y) ∈ Δ.1
    rw [circleToReal_realToCircle]
  have hsm : IsSpectralResolution A (spectralResolution A) := Classical.epsilon_spec ⟨_, hex⟩
  have hs := hun _ hsm
  have hcomm' : ∀ B : H →L[ℂ] H, Commutes B (resolventAtI A) →
      ∀ Δ, Commutes B (spectralResolution A Δ) := by
    intro B hB Δ
    rw [hs]
    refine hcomm B ?_ _
    refine ContinuousLinearMap.ext fun ψ => ?_
    have hBR : B (resolventAtI A ψ) = resolventAtI A (B ψ) :=
      congrArg (fun S : H →L[ℂ] H => S ψ) hB
    change B (U ψ) = U (B ψ)
    rw [(hU ψ).2, (hU (B ψ)).2, map_sub, map_smul, hBR]
  exact ⟨addConst_bijective hA hK conj_I_eq_neg_I Complex.norm_I,
    addConst_bijective hA hK conj_neg_I_eq_neg_neg_I norm_neg_I_eq_one,
    fun χ => ⟨norm_add_smul_sq hA conj_I_eq_neg_I Complex.norm_I χ,
      norm_add_smul_sq hA conj_neg_I_eq_neg_neg_I norm_neg_I_eq_one χ⟩,
    hR, boundedInverse_injective hR, ⟨U, hU⟩, fun A' hA' hc => eq_of_isExtendedBy hA hA' hc,
    ⟨_, hex, fun E hE => hun E hE⟩, hsm, hcomm',
    fun T hT B hB => hcomm' B (commutes_resolventAtI_of_ofCLM hR hT hB)⟩
end YangMills.Construction.EuclideanBorel.CayleySpectral
