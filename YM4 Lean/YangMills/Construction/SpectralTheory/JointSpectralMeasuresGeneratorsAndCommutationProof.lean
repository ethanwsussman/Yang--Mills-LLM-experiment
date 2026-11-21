import YangMills.Construction.SpectralTheory.FactsOnResolvedOperators
import YangMills.Construction.SpectralTheory.JointSpectralMeasuresGeneratorsAndCommutation
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import YangMills.Construction.SpectralTheory.ProductOfTwoCommutingProjectionValuedMeasures
import YangMills.Construction.SpectralTheory.SemigroupsOfSelfAdjointContractionsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.JointSpectralConstruction
open HilbertSpaceBasics (UnboundedOp ofBounded)
open BorelSpectral (BorelSubsets SpectralMeasure realLineSet zeroExtend measurable_zeroExtend)
open BorelSpectral.SpectralMeasure (OpCommutes Commutes)
open SpectralTheorem
  (spectralIntegralOp spectralMeasure IsSpectralIntegralOf IsSpectralMeasureFor IntegralsAgree
    RealLineSet coordVar)
open SelfAdjointFunctions (fnCalc expI expNeg)
open ResolvedOps (IsDiagonalized expComplex boxSet IsJointSpectralMeasure jointSpectralMeasure
  StronglyCommute)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem eq_of_integralsAgree {n n' : ℕ} {Y : Set (Fin n → ℝ)} {Y' : Set (Fin n' → ℝ)}
    {E : SpectralMeasure Y H} {E' : SpectralMeasure Y' H} {g : Y → ℂ}
    {g' : Y' → ℂ} {A A' : UnboundedOp H} (h : IsSpectralIntegralOf A E g)
    (h' : IsSpectralIntegralOf A' E' g') (hs : IntegralsAgree E g E' g') : A = A' := by apply _root_.YangMills.Construction.ContractionSemigroups.op_eq_of_integralsAgree <;> assumption
theorem isSpectralMeasureFor_spectralMeasure {A : UnboundedOp H} (hA : IsDiagonalized A) :
    IsSpectralMeasureFor (spectralMeasure A) A :=
  Classical.epsilon_spec hA
theorem measurable_coordVar : Measurable (coordVar : RealLineSet → ℂ) :=
  Complex.measurable_ofReal.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
theorem eq_spectralIntegralOp_coordVar (hC : SpectralMeasureCalculus.CalculusTheorem)
    {A : UnboundedOp H} (hA : IsDiagonalized A) :
    A = spectralIntegralOp (spectralMeasure A) coordVar :=
  eq_of_integralsAgree (isSpectralMeasureFor_spectralMeasure hA)
    ((hC H 1 _ _).2.2.1.isIntegralOf _ measurable_coordVar) ⟨rfl, fun _ _ => rfl⟩
theorem isSelfAdjointOp_of_isDiagonalized (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : ResolvedFacts.DiagonalizedFacts) {A : UnboundedOp H} (hA : IsDiagonalized A) :
    HilbertSpaceBasics.IsSelfAdjointOp A := by
  have h := ((hF H).1 (spectralMeasure A)).1
  rw [← eq_spectralIntegralOp_coordVar hC hA] at h
  refine ⟨h.1, fun φ => ⟨fun hφ => ⟨A ⟨φ, hφ⟩, (h.2 φ _).1 ⟨hφ, rfl⟩⟩, ?_⟩, fun φ ψ =>
    (h.2 φ (A φ)).1 ⟨φ.2, rfl⟩ ψ⟩
  rintro ⟨η, hη⟩
  exact ((h.2 φ η).2 hη).1
theorem isDiagonalized_of_isSelfAdjointOp (hS : SpectralTheorem.SpectralTheoremHolds)
    {A : UnboundedOp H} (hA : HilbertSpaceBasics.IsSelfAdjointOp A) : IsDiagonalized A :=
  ⟨_, (hS H A hA).2.2.2.2.2.1⟩
theorem exists_eq_realLineSet (Δ : BorelSubsets RealLineSet) :
    ∃ D : BorelSubsets ℝ, Δ = realLineSet D := by
  have hm : Measurable fun x : ℝ => (⟨fun _ => x, mem_univ _⟩ : RealLineSet) :=
    Measurable.subtype_mk (measurable_pi_iff.mpr fun _ => measurable_id)
  refine ⟨⟨_, hm Δ.2⟩, Subtype.ext ?_⟩
  ext y
  have hy : y = ⟨fun _ => y.1 0, mem_univ _⟩ := by
    refine Subtype.ext (funext fun i => ?_)
    rw [Subsingleton.elim i 0]
  change y ∈ Δ.1 ↔ (⟨fun _ => y.1 0, mem_univ _⟩ : RealLineSet) ∈ Δ.1
  rw [← hy]
theorem isSelfAdjointContractionSemigroup_of {T : ℝ≥0 → H →L[ℂ] H}
    (h : OperatorTransport.IsContractionSemigroup T) :
    ContractionSemigroups.IsSelfAdjointContractionSemigroup T where
  semigroup := ⟨h.map_zero, h.map_add⟩
  selfAdjoint t := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun φ ψ =>
    (h.selfAdjoint t φ ψ).symm
  contraction := h.contraction
  tendsto_zero ψ := by
    have h₀ := ((h.continuous_apply ψ).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [h.map_zero] using h₀
theorem expComplex_ofReal_eq_expNeg (A : UnboundedOp H) (t : ℝ≥0) :
    expComplex A ((t : ℝ) : ℂ) = expNeg A t := by
  have h : (fun x : ℝ => Complex.exp (-(((t : ℝ) : ℂ)) * (x : ℂ))) =
      fun x : ℝ => Complex.exp ((-(t : ℝ) * x : ℝ) : ℂ) := by
    funext x
    push_cast
    rfl
  unfold expComplex expNeg
  rw [h]
theorem existsUnique_semigroupGenerator (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : ResolvedFacts.DiagonalizedFacts) (hS : SpectralTheorem.SpectralTheoremHolds)
    (hT : ContractionSemigroups.ContractionSemigroupTheorem) (T : ℝ≥0 → H →L[ℂ] H)
    (h : OperatorTransport.IsContractionSemigroup T) :
    ∃! A : UnboundedOp H, IsDiagonalized A ∧ OperatorTransport.IsNonnegUnbounded A ∧
      ∀ t : ℝ≥0, T t = expComplex A ((t : ℝ) : ℂ) := by
  obtain ⟨A, ⟨hA, hAT⟩, hu⟩ := (hT H T (isSelfAdjointContractionSemigroup_of h)).2.2.1.1
  refine ⟨A, ⟨isDiagonalized_of_isSelfAdjointOp hS hA.1, hA.2, fun t => ?_⟩, ?_⟩
  · rw [expComplex_ofReal_eq_expNeg]
    exact hAT t
  · rintro A' ⟨hr, hn, he⟩
    refine hu A' ⟨⟨isSelfAdjointOp_of_isDiagonalized hC hF hr, hn⟩, fun t => ?_⟩
    rw [he t, expComplex_ofReal_eq_expNeg]
theorem opCommutes_of_commute_expComplex (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : ResolvedFacts.DiagonalizedFacts)
    (hT : ContractionSemigroups.ContractionSemigroupTheorem) {A : UnboundedOp H}
    (hA : IsDiagonalized A) (hn : OperatorTransport.IsNonnegUnbounded A) (C : H →L[ℂ] H)
    (hc : ∀ t : ℝ≥0, Commute C (expComplex A ((t : ℝ) : ℂ))) :
    OpCommutes C (spectralMeasure A) := by
  have hs : OperatorTransport.IsContractionSemigroup
      (fun t : ℝ≥0 => expComplex A ((t : ℝ) : ℂ)) :=
    ((hF H).2.2.2.1 A hA hn).2.2.2.2.2.1
  have hall := hT H _ (isSelfAdjointContractionSemigroup_of hs)
  obtain ⟨A₀, -, hu⟩ := hall.2.2.1.1
  have h₁ : ContractionSemigroups.semigroupGenerator
      (fun t : ℝ≥0 => expComplex A ((t : ℝ) : ℂ)) = A₀ :=
    hu _ ⟨hall.2.2.1.2.1, hall.2.2.1.2.2.1⟩
  have h₂ : A = A₀ :=
    hu A ⟨⟨isSelfAdjointOp_of_isDiagonalized hC hF hA, hn⟩,
      fun t => expComplex_ofReal_eq_expNeg A t⟩
  have hcomm := (hall.2.2.2.2.1 C (hc 1)).1
  rw [h₁, ← h₂] at hcomm
  exact hcomm
def unitaryGroupCLM (U : ℝ → H →ₗ[ℂ] H) (h : OperatorTransport.IsUnitaryGroup U) (s : ℝ) :
    H →L[ℂ] H :=
  ((U s).isometryOfInner (h.unitary s).inner_map_map).toContinuousLinearMap
theorem isUnitaryOp_of_surjective_of_inner (A : H →L[ℂ] H) (hb : Function.Surjective A)
    (hi : ∀ φ ψ, ⟪A φ, A ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ) : HilbertSpaceBasics.IsUnitaryOp A := by
  have h₁ : star A * A = 1 := by
    ext x
    refine ext_inner_right ℂ fun y => ?_
    change ⟪star A (A x), y⟫_ℂ = ⟪x, y⟫_ℂ
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left, hi]
  refine ⟨h₁, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := hb y
  have h₂ : star A (A z) = z := by
    simpa using congrArg (fun T : H →L[ℂ] H => T z) h₁
  change A (star A (A z)) = A z
  rw [h₂]
theorem isContinuousUnitaryGroup_unitaryGroupCLM (U : ℝ → H →ₗ[ℂ] H)
    (h : OperatorTransport.IsUnitaryGroup U) :
    UnitaryGroups.IsContinuousUnitaryGroup (unitaryGroupCLM U h) := by
  refine ⟨⟨fun s => isUnitaryOp_of_surjective_of_inner _ (h.unitary s).bijective.2
    (h.unitary s).inner_map_map, ?_, ?_⟩, ?_⟩
  · ext ψ
    exact LinearMap.congr_fun h.map_zero ψ
  · intro a a'
    ext ψ
    exact LinearMap.congr_fun (h.map_add a a') ψ
  · intro ψ
    have h₀ := (h.continuous_apply ψ).tendsto 0
    rw [show U 0 ψ = ψ from LinearMap.congr_fun h.map_zero ψ] at h₀
    exact h₀
theorem existsUnique_stoneGenerator (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : ResolvedFacts.DiagonalizedFacts) (hS : SpectralTheorem.SpectralTheoremHolds)
    (hG : UnitaryGroups.StoneTheoremHolds) (U : ℝ → H →ₗ[ℂ] H)
    (h : OperatorTransport.IsUnitaryGroup U) :
    ∃! B : UnboundedOp H, IsDiagonalized B ∧ ∀ s : ℝ, U s = (expI B s : H →ₗ[ℂ] H) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨B, ⟨hB, hBU⟩, hu⟩, -⟩ :=
    (hG H).1 _ (isContinuousUnitaryGroup_unitaryGroupCLM U h)
  refine ⟨B, ⟨isDiagonalized_of_isSelfAdjointOp hS hB, fun s => ?_⟩, ?_⟩
  · ext ψ
    exact congrArg (fun T : H →L[ℂ] H => T ψ) (hBU s)
  · rintro B' ⟨hr, he⟩
    refine hu B' ⟨isSelfAdjointOp_of_isDiagonalized hC hF hr, fun s => ?_⟩
    ext ψ
    exact LinearMap.congr_fun (he s) ψ
theorem opCommutes_of_commute_expI (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : ResolvedFacts.DiagonalizedFacts) (hG : UnitaryGroups.StoneTheoremHolds)
    {B : UnboundedOp H} (hB : IsDiagonalized B) (C : H →L[ℂ] H)
    (hc : ∀ s : ℝ, Commute C (expI B s)) : OpCommutes C (spectralMeasure B) := by
  have hU := ((hF H).2.2.1 B hB).1
  have hV : ∀ s, unitaryGroupCLM _ hU s = expI B s := fun s => by
    ext ψ
    rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hP, hgen, -, hcomm⟩ :=
    (hG H).1 _ (isContinuousUnitaryGroup_unitaryGroupCLM _ hU)
  have h₁ : UnitaryGroups.stoneGenerator (unitaryGroupCLM _ hU) = B :=
    hP.unique hgen ⟨isSelfAdjointOp_of_isDiagonalized hC hF hB, hV⟩
  intro Δ
  obtain ⟨D, rfl⟩ := exists_eq_realLineSet Δ
  have h₂ := hcomm C (fun s => by rw [hV s]; exact hc s) D
  rw [h₁] at h₂
  exact h₂
theorem list_prod_ofFn_eq_of_eq_one {M : Type} [Monoid M] : ∀ {r : ℕ} (f : Fin r → M) (k : Fin r),
    (∀ j, j ≠ k → f j = 1) → (List.ofFn f).prod = f k := by
  intro r
  induction r with
  | zero => exact fun _ k => k.elim0
  | succ r ih =>
    intro f k hf
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun k' => ?_) k hf
    · intro hf
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact hf _ (Fin.succ_ne_zero i)
    · intro hf
      rw [hf 0 (Fin.succ_ne_zero k').symm, one_mul]
      exact ih (fun i => f i.succ) k' fun j hj => hf _ fun h => hj (Fin.succ_injective _ h)
theorem exists_jointMeasure (hP : SpectralProduct.ProductTheorem) : ∀ (n : ℕ)
    (F : Fin (n + 1) → SpectralMeasure RealLineSet H),
    (∀ j k, j ≠ k → Commutes (F j) (F k)) →
    ∃ E : SpectralMeasure (univ : Set (Fin (n + 1) → ℝ)) H,
      (∀ Δ : Fin (n + 1) → BorelSubsets ℝ,
        E (boxSet Δ) = (List.ofFn fun k => F k (realLineSet (Δ k))).prod) ∧
      ∀ B : H →L[ℂ] H, (∀ k, OpCommutes B (F k)) → OpCommutes B E := by
  intro n
  induction n with
  | zero =>
    intro F _
    refine ⟨F 0, fun Δ => ?_, fun B hB => hB 0⟩
    have hbox : boxSet Δ = realLineSet (Δ 0) := by
      refine Subtype.ext ?_
      ext y
      simp [boxSet, realLineSet]
    rw [hbox]
    simp
  | succ n ih =>
    intro F hF
    obtain ⟨E₀, hbox₀, hcomm₀⟩ := ih (fun k => F k.castSucc) fun j k hjk =>
      hF _ _ fun h => hjk (Fin.castSucc_injective _ h)
    have hc : Commutes E₀ (F (Fin.last _)) := fun Δ₁ Δ₂ =>
      (hcomm₀ _ (fun k Δ => hF (Fin.last _) k.castSucc (Fin.castSucc_lt_last k).ne' Δ₂ Δ) Δ₁).symm
    obtain ⟨⟨E, hE, -⟩, hB⟩ := hP H (n + 1) 1 E₀ (F (Fin.last _)) hc
    refine ⟨E, fun Δ => ?_, fun B hb => hB E hE B (hcomm₀ B fun k => hb _) (hb _)⟩
    have hbox : boxSet Δ =
        SpectralProduct.boxSet (boxSet fun k => Δ k.castSucc) (realLineSet (Δ (Fin.last _))) := by
      refine Subtype.ext ?_
      ext y
      change (∀ k, y.1 k ∈ (Δ k).1) ↔
        (∀ k : Fin (n + 1), y.1 (Fin.castAdd 1 k) ∈ (Δ k.castSucc).1) ∧
          y.1 (Fin.natAdd (n + 1) 0) ∈ (Δ (Fin.last _)).1
      rw [Fin.forall_fin_succ']
      exact Iff.rfl
    have hl := List.ofFn_succ' (fun k : Fin (n + 1 + 1) => F k (realLineSet (Δ k)))
    rw [hbox, hE, hbox₀, hl, List.prod_concat]
theorem ext_of_boxSet {r : ℕ} (E E' : SpectralMeasure (univ : Set (Fin r → ℝ)) H)
    (h : ∀ Δ : Fin r → BorelSubsets ℝ, E (boxSet Δ) = E' (boxSet Δ)) : E = E' := by
  have hm : ∀ ψ, (E.diagMeasure ψ).map Subtype.val = (E'.diagMeasure ψ).map Subtype.val := by
    intro ψ
    have : IsFiniteMeasure ((E.diagMeasure ψ).map Subtype.val) :=
      Measure.isFiniteMeasure_map _ _
    refine ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      have hpre : (Subtype.val : ↥(univ : Set (Fin r → ℝ)) → Fin r → ℝ) ⁻¹' (univ.pi t) =
          (boxSet fun k => (⟨t k, ht k (mem_univ k)⟩ : BorelSubsets ℝ)).1 := by
        ext y
        simp [boxSet, Set.mem_pi]
      have hmeas : MeasurableSet (univ.pi t) :=
        MeasurableSet.univ_pi fun k => ht k (mem_univ k)
      rw [Measure.map_apply measurable_subtype_coe hmeas,
        Measure.map_apply measurable_subtype_coe hmeas, hpre, E.diagMeasure_apply,
        E'.diagMeasure_apply, h]
    · rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
        Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ,
        E.diagMeasure_univ, E'.diagMeasure_univ]
  refine BorelSpectral.SpectralMeasure.ext_apply fun Δ => ?_
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).1 fun ψ => ?_)
  change ⟪E Δ ψ, ψ⟫_ℂ = ⟪E' Δ ψ, ψ⟫_ℂ
  have himg : MeasurableSet (Subtype.val '' Δ.1 : Set (Fin r → ℝ)) :=
    MeasurableSet.univ.subtype_image Δ.2
  have hpre : (Subtype.val : ↥(univ : Set (Fin r → ℝ)) → Fin r → ℝ) ⁻¹' (Subtype.val '' Δ.1) =
      Δ.1 := preimage_image_eq _ Subtype.val_injective
  have h₁ := congrArg (fun m : Measure (Fin r → ℝ) => m (Subtype.val '' Δ.1)) (hm ψ)
  simp only [Measure.map_apply measurable_subtype_coe himg, hpre] at h₁
  have h₂ : ⟪ψ, E Δ ψ⟫_ℂ = ⟪ψ, E' Δ ψ⟫_ℂ := by
    rw [E.inner_apply_self_eq_diagMeasure, E'.inner_apply_self_eq_diagMeasure, Measure.real,
      Measure.real, h₁]
  rw [← inner_conj_symm (E Δ ψ) ψ, ← inner_conj_symm (E' Δ ψ) ψ, h₂]
theorem coordMarginal_eq_spectralMeasure {r : ℕ} (A : Fin r → UnboundedOp H)
    (J : SpectralMeasure (univ : Set (Fin r → ℝ)) H) (hJ : IsJointSpectralMeasure A J)
    (k : Fin r) : J.coordMarginal k = spectralMeasure (A k) := by
  classical
  refine BorelSpectral.SpectralMeasure.ext_apply fun Δ => ?_
  obtain ⟨D, rfl⟩ := exists_eq_realLineSet Δ
  rw [BorelSpectral.SpectralMeasure.coordMarginal_realLineSet]
  let Δ' : Fin r → BorelSubsets ℝ := fun j => if j = k then D else ⟨univ, MeasurableSet.univ⟩
  have hset : (⟨{y | y.1 k ∈ D.1}, ((measurable_pi_apply k).comp measurable_subtype_coe) D.2⟩ :
      BorelSubsets (univ : Set (Fin r → ℝ))) = boxSet Δ' := by
    refine Subtype.ext ?_
    ext y
    change y.1 k ∈ D.1 ↔ ∀ j, y.1 j ∈ (Δ' j).1
    constructor
    · intro hy j
      by_cases hj : j = k
      · subst hj
        simpa [Δ'] using hy
      · simp [Δ', hj]
    · intro hy
      simpa [Δ'] using hy k
  rw [hset, hJ, list_prod_ofFn_eq_of_eq_one _ k]
  · simp [Δ']
  · intro j hj
    have hl : realLineSet (Δ' j) = ⟨univ, MeasurableSet.univ⟩ := by
      refine Subtype.ext ?_
      ext y
      simp [realLineSet, Δ', hj]
    rw [hl]
    exact (spectralMeasure (A j)).map_univ
theorem fnCalc_eq_spectralIntegralOp (hC : SpectralMeasureCalculus.CalculusTheorem) {r : ℕ}
    (A : UnboundedOp H) (J : SpectralMeasure (univ : Set (Fin r → ℝ)) H) (k : Fin r)
    (hk : J.coordMarginal k = spectralMeasure A) (u : ℝ → ℂ) (hu : Measurable u) :
    fnCalc A u = spectralIntegralOp J fun y => u (y.1 k) := by
  have hg : Measurable fun y : RealLineSet => u (y.1 0) :=
    hu.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
  have hg' : Measurable fun y : (univ : Set (Fin r → ℝ)) => u (y.1 k) :=
    hu.comp ((measurable_pi_apply k).comp measurable_subtype_coe)
  unfold fnCalc
  rw [← hk]
  exact eq_of_integralsAgree ((hC H 1 _ _).2.2.1.isIntegralOf _ hg)
    ((hC H r _ _).2.2.1.isIntegralOf _ hg')
    ((hC H r _ J).2.2.2.2.1.integral_image le_rfl MeasurableSet.univ _ _ _ hg)
theorem setIntegralOp_eq_ofBounded (hC : SpectralMeasureCalculus.CalculusTheorem) {r : ℕ}
    (J : SpectralMeasure (univ : Set (Fin r → ℝ)) H)
    (C : BorelSubsets (univ : Set (Fin r → ℝ))) (Φ : C.1 → ℂ) (hJ : J.IsCarriedBy C)
    (hΦ : Measurable Φ) (hb : ∃ c : ℝ, ∀ y, ‖Φ y‖ ≤ c) :
    J.setIntegralOp C Φ = ofBounded (J.integralOpOn C Φ) ∧
      ‖J.integralOpOn C Φ‖ ≤ ⨆ y, ‖Φ y‖ := by
  classical
  have hm := measurable_zeroExtend C.2 hΦ
  obtain ⟨c, hc⟩ := hb
  have hbd : ∀ y, ‖zeroExtend C.1 Φ y‖ ≤ max c 0 := fun y => by
    unfold zeroExtend
    split_ifs with hy
    · exact (hc _).trans (le_max_left _ _)
    · simp
  have hall := hC H r _ J
  obtain ⟨hdom, hval⟩ := hall.2.2.1.of_bounded _ hm ⟨_, hbd⟩
  constructor
  · refine eq_of_integralsAgree (hall.2.2.1.isIntegralOf _ hm)
      (⟨fun ψ => ?_, fun ψ => ?_⟩ : IsSpectralIntegralOf (ofBounded (J.integralOpOn C Φ)) J _)
      ⟨rfl, fun _ _ => rfl⟩
    · rw [hdom]
      simp [ofBounded]
    · rw [hval]
      rfl
  · refine (hall.2.1.norm_le _ C hm ⟨_, hbd⟩ hJ).trans (le_of_eq ?_)
    refine iSup_congr fun y => ?_
    unfold zeroExtend
    rw [dif_pos y.2]
theorem jointSpectralMeasure_properties (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hP : SpectralProduct.ProductTheorem) (r : ℕ) (hr : 1 ≤ r)
    (A : Fin r → UnboundedOp H) (hres : ∀ k, IsDiagonalized (A k))
    (hcomm : ∀ j k, j ≠ k → StronglyCommute (A j) (A k)) :
    (∃! E : SpectralMeasure (univ : Set (Fin r → ℝ)) H, IsJointSpectralMeasure A E) ∧
    IsJointSpectralMeasure A (jointSpectralMeasure hr A) ∧
    (∀ k, (jointSpectralMeasure hr A).coordMarginal k = spectralMeasure (A k)) ∧
    (∀ (k : Fin r) (u : ℝ → ℂ), Measurable u →
      fnCalc (A k) u = spectralIntegralOp (jointSpectralMeasure hr A) fun y => u (y.1 k)) ∧
    (∀ k, A k = spectralIntegralOp (jointSpectralMeasure hr A) fun y => ((y.1 k : ℝ) : ℂ)) ∧
    (∀ B : H →L[ℂ] H, (∀ k, OpCommutes B (spectralMeasure (A k))) →
      OpCommutes B (jointSpectralMeasure hr A)) ∧
    ∀ (C : BorelSubsets (univ : Set (Fin r → ℝ))) (Φ : C.1 → ℂ),
      (jointSpectralMeasure hr A).IsCarriedBy C → Measurable Φ → (∃ c : ℝ, ∀ y, ‖Φ y‖ ≤ c) →
        (jointSpectralMeasure hr A).setIntegralOp C Φ =
          ofBounded ((jointSpectralMeasure hr A).integralOpOn C Φ) ∧
        ‖(jointSpectralMeasure hr A).integralOpOn C Φ‖ ≤ ⨆ y, ‖Φ y‖ := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  obtain ⟨E₀, hE₀, hB₀⟩ := exists_jointMeasure hP n (fun k => spectralMeasure (A k)) hcomm
  have huniq : ∀ E E' : SpectralMeasure (univ : Set (Fin (n + 1) → ℝ)) H,
      IsJointSpectralMeasure A E → IsJointSpectralMeasure A E' → E = E' := fun E E' h h' =>
    ext_of_boxSet E E' fun Δ => (h Δ).trans (h' Δ).symm
  have hJ : IsJointSpectralMeasure A (jointSpectralMeasure hr A) :=
    Classical.epsilon_spec (p := IsJointSpectralMeasure A) ⟨E₀, hE₀⟩
  have hJ₀ : jointSpectralMeasure hr A = E₀ := huniq _ _ hJ hE₀
  have hmarg := coordMarginal_eq_spectralMeasure A _ hJ
  have hfun : ∀ (k : Fin (n + 1)) (u : ℝ → ℂ), Measurable u →
      fnCalc (A k) u = spectralIntegralOp (jointSpectralMeasure hr A) fun y => u (y.1 k) :=
    fun k u hu => fnCalc_eq_spectralIntegralOp hC (A k) _ k (hmarg k) u hu
  refine ⟨⟨E₀, hE₀, fun E hE => huniq _ _ hE hE₀⟩, hJ, hmarg, hfun, fun k => ?_, fun B hB => ?_,
    fun C Φ hc hΦ hb => setIntegralOp_eq_ofBounded hC _ C Φ hc hΦ hb⟩
  · exact (eq_spectralIntegralOp_coordVar hC (hres k)).trans (hfun k _ Complex.measurable_ofReal)
  · rw [hJ₀]
    exact hB₀ B hB
theorem jointMeasureGeneratorsCommutation (hC : SpectralMeasureCalculus.CalculusTheorem)
    (hF : ResolvedFacts.DiagonalizedFacts) (hP : SpectralProduct.ProductTheorem)
    (hS : SpectralTheorem.SpectralTheoremHolds)
    (hT : ContractionSemigroups.ContractionSemigroupTheorem)
    (hG : UnitaryGroups.StoneTheoremHolds) :
    JointSpectralGenerators.JointMeasureGeneratorsCommutation := by
  intro H _ _ _
  refine ⟨fun r hr A hres hcomm => jointSpectralMeasure_properties hC hP r hr A hres hcomm,
    fun T h => existsUnique_semigroupGenerator hC hF hS hT T h,
    fun U h => existsUnique_stoneGenerator hC hF hS hG U h, ?_, ?_, ?_⟩
  · intro A B hA hn hB hc Δ₁ Δ₂
    have h₁ : ∀ s, OpCommutes (expI B s) (spectralMeasure A) := fun s =>
      opCommutes_of_commute_expComplex hC hF hT hA hn _ fun t => (hc t s).symm
    exact (opCommutes_of_commute_expI hC hF hG hB _ (fun s => (h₁ s Δ₁).symm) Δ₂)
  · intro B B' hB hB' hc Δ₁ Δ₂
    have h₁ : ∀ s', OpCommutes (expI B' s') (spectralMeasure B) := fun s' =>
      opCommutes_of_commute_expI hC hF hG hB _ fun s => (hc s s').symm
    exact (opCommutes_of_commute_expI hC hF hG hB' _ (fun s' => (h₁ s' Δ₁).symm) Δ₂)
  · intro A B hA hn hB
    exact ⟨fun C hc => opCommutes_of_commute_expComplex hC hF hT hA hn C hc,
      fun C hc => opCommutes_of_commute_expI hC hF hG hB C hc⟩
end YangMills.Construction.JointSpectralConstruction
