import Reconstruction.MinkowskiSpace.FieldOnTheTensorVectors
import Reconstruction.MinkowskiSpace.LocalityOfTheTensorVectors
import Reconstruction.MinkowskiSpace.RepresentationOnTheTensorVectorsProof
import Reconstruction.MinkowskiSpace.SchwingerFunctionsOfATheoryWithTheValuesOfAForm
import Reconstruction.MinkowskiSpace.SeparabilityAndFixedVectorsOfTheTensorVectors
import Reconstruction.MinkowskiSpace.StrongContinuityOfTheRepresentationOnTheTensorVectors
import Reconstruction.MinkowskiSpace.TranslationsAndMeasureOnTheTensorVectors
import Reconstruction.MinkowskiSpace.WightmanTheoryOfAEuclideanFieldForm
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.FieldFormHilbert
open MinkowskiSpace FieldForms RealPointVectors WightmanTheory
  ProjectionMeasures FormsOperators OneLoopNotation
section Building
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K}
theorem tensorVec_mem_tensorDomainIn (hs : TensorVecInner.Conclusions E Ω A)
    {m : ℕ} (f : Fin m → TestFn) :
    tensorVec E Ω A f ∈ tensorDomainIn E Ω A := by apply _root_.YangMills.Construction.TensorPoincareRep.tensorVec_mem_domain <;> assumption
variable (E Ω A) in
def vacuumVec : tensorHilbert E Ω A :=
  tensorVec E Ω A (Fin.elim0 : Fin 0 → TestFn)
theorem coe_vacuumVec (hs : TensorVecInner.Conclusions E Ω A) :
    (vacuumVec E Ω A : K) = Ω :=
  hs.tensorVec_fin_zero _
def fieldOp (hf : TensorFieldOperators.FieldOperatorFacts E Ω A) (f : TestFn) :
    tensorDomainIn E Ω A →ₗ[ℂ] tensorDomainIn E Ω A :=
  (hf.exists_unique f).choose
theorem fieldOp_spec (hf : TensorFieldOperators.FieldOperatorFacts E Ω A) (f : TestFn) :
    IsFieldOp E Ω A (tensorDomainIn E Ω A) f (fieldOp hf f) :=
  (hf.exists_unique f).choose_spec.1
def poincareOp (hr : TensorPoincareRep.Conclusions E Ω A) (g : PoincareElt) :
    UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A) :=
  (hr.existsUnique_op g).choose
theorem poincareOp_spec (hr : TensorPoincareRep.Conclusions E Ω A)
    (g : PoincareElt) : IsPoincareOp E Ω A g (poincareOp hr g) :=
  (hr.existsUnique_op g).choose_spec.1
def theoryOfTensorVecs (hΩ : ‖Ω‖ = 1)
    (hs : TensorVecInner.Conclusions E Ω A)
    (hf : TensorFieldOperators.FieldOperatorFacts E Ω A)
    (hr : TensorPoincareRep.Conclusions E Ω A)
    (hc : ∀ ψ : tensorHilbert E Ω A, Continuous fun g => poincareOp hr g ψ) :
    HermitianScalarTheory (tensorHilbert E Ω A) where
  rep := poincareOp hr
  rep_mul := fun g g' g'' h =>
    hr.op_mul g g' g'' _ _ _ h (poincareOp_spec hr g) (poincareOp_spec hr g')
      (poincareOp_spec hr g'')
  rep_continuous := hc
  vacuum := vacuumVec E Ω A
  norm_vacuum := by
    have h : ‖vacuumVec E Ω A‖ = ‖(vacuumVec E Ω A : K)‖ := rfl
    rw [h, coe_vacuumVec hs, hΩ]
  rep_vacuum := fun g =>
    hr.op_vacuum g _ _ (poincareOp_spec hr g) (coe_vacuumVec hs)
  domain := tensorDomainIn E Ω A
  dense_domain := hs.dense_domain
  vacuum_mem_domain := tensorVec_mem_tensorDomainIn hs _
  rep_mem_domain := fun g ψ hψ =>
    hr.op_mem_domain g _ (poincareOp_spec hr g) ψ hψ
  field := fieldOp hf
  field_linear := fun a b f f' f'' h =>
    hf.linear a b f f' f'' _ _ _ h (fieldOp_spec hf f) (fieldOp_spec hf f')
      (fieldOp_spec hf f'')
  field_tempered := fun Ψ Ψ' => by
    obtain ⟨k, c, hk, hc, hb⟩ := hf.tempered Ψ Ψ'
    exact ⟨k, c, hk, hc, fun f => hb f _ (fieldOp_spec hf f)⟩
  field_hermitian := fun f =>
    ⟨⟨_, hs.conj_mem_schwartz f⟩, rfl,
      hf.hermitian f ⟨_, hs.conj_mem_schwartz f⟩ _ _ rfl (fieldOp_spec hf f)
        (fieldOp_spec hf _)⟩
  vacuum_cyclic := by
    have hrange : (fun p : Σ m : ℕ, (Fin m → TestFn) => tensorVec E Ω A p.2) =
        fun p : Σ m : ℕ, (Fin m → TestFn) =>
          ((fieldWord (fun f Ψ => fieldOp hf f Ψ) p.2
            ⟨vacuumVec E Ω A, tensorVec_mem_tensorDomainIn hs _⟩ :
              tensorDomainIn E Ω A) : tensorHilbert E Ω A) :=
      funext fun p => (hf.fieldWord_eq _ (fieldOp_spec hf) _ (coe_vacuumVec hs)
        p.1 p.2).symm
    have h := hs.dense_domain
    rw [hs.domain_eq_span, hrange] at h
    exact h
theorem fieldOp_comm (hs : TensorVecInner.Conclusions E Ω A)
    (hf : TensorFieldOperators.FieldOperatorFacts E Ω A) {f h : TestFn}
    (hloc : ∀ (m : ℕ) (u : Fin m → TestFn),
      tensorVec E Ω A (Fin.cons f (Fin.cons h u) : Fin (m + 2) → TestFn) =
        tensorVec E Ω A (Fin.cons h (Fin.cons f u) : Fin (m + 2) → TestFn))
    (Ψ : tensorDomainIn E Ω A) :
    fieldOp hf f (fieldOp hf h Ψ) = fieldOp hf h (fieldOp hf f Ψ) := by
  have key : ∀ v, v ∈ Submodule.span ℂ (Set.range fun p : Σ m : ℕ, (Fin m → TestFn) =>
      tensorVec E Ω A p.2) → ∀ hv : v ∈ tensorDomainIn E Ω A,
      fieldOp hf f (fieldOp hf h ⟨v, hv⟩) =
        fieldOp hf h (fieldOp hf f ⟨v, hv⟩) := by
    intro v hv'
    induction hv' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨m, u⟩, rfl⟩ := hx
      intro hv
      have e₁ : fieldOp hf h ⟨_, hv⟩ =
          ⟨tensorVec E Ω A (Fin.cons h u : Fin (m + 1) → TestFn),
            tensorVec_mem_tensorDomainIn hs _⟩ :=
        Subtype.ext (fieldOp_spec hf h m u hv)
      have e₂ : fieldOp hf f ⟨_, hv⟩ =
          ⟨tensorVec E Ω A (Fin.cons f u : Fin (m + 1) → TestFn),
            tensorVec_mem_tensorDomainIn hs _⟩ :=
        Subtype.ext (fieldOp_spec hf f m u hv)
      rw [e₁, e₂]
      apply Subtype.ext
      rw [fieldOp_spec hf f (m + 1) (Fin.cons h u) (tensorVec_mem_tensorDomainIn hs _),
        fieldOp_spec hf h (m + 1) (Fin.cons f u) (tensorVec_mem_tensorDomainIn hs _)]
      exact hloc m u
    | zero =>
      intro hv
      have e : (⟨0, hv⟩ : tensorDomainIn E Ω A) = 0 := rfl
      rw [e]
      simp only [map_zero]
    | add x y hx hy ihx ihy =>
      intro hv
      have hx' : x ∈ tensorDomainIn E Ω A := by rw [hs.domain_eq_span]; exact hx
      have hy' : y ∈ tensorDomainIn E Ω A := by rw [hs.domain_eq_span]; exact hy
      have e : (⟨x + y, hv⟩ : tensorDomainIn E Ω A) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
      rw [e]
      simp only [map_add]
      rw [ihx hx', ihy hy']
    | smul c x hx ih =>
      intro hv
      have hx' : x ∈ tensorDomainIn E Ω A := by rw [hs.domain_eq_span]; exact hx
      have e : (⟨c • x, hv⟩ : tensorDomainIn E Ω A) = c • ⟨x, hx'⟩ := rfl
      rw [e]
      simp only [map_smul]
      rw [ih hx']
  have hspan : ∀ v, v ∈ tensorDomainIn E Ω A → v ∈ Submodule.span ℂ
      (Set.range fun p : Σ m : ℕ, (Fin m → TestFn) => tensorVec E Ω A p.2) := by
    intro v hv
    rwa [hs.domain_eq_span] at hv
  exact key Ψ.1 (hspan _ Ψ.2) Ψ.2
theorem formTheoryProperties_theoryOfTensorVecs (hΩ : ‖Ω‖ = 1)
    (hs : TensorVecInner.Conclusions E Ω A)
    (hf : TensorFieldOperators.FieldOperatorFacts E Ω A)
    (hr : TensorPoincareRep.Conclusions E Ω A)
    (hc : ∀ ψ : tensorHilbert E Ω A, Continuous fun g => poincareOp hr g ψ)
    (ht : TensorTranslations.Properties E Ω A)
    (hl : ∀ (f h : TestFn) (m : ℕ) (u : Fin m → TestFn),
      (∀ x ∈ tsupport f.1, ∀ y ∈ tsupport h.1, x - y ∈ spacelikeSet) →
      tensorVec E Ω A (Fin.cons f (Fin.cons h u) : Fin (m + 2) → TestFn) =
        tensorVec E Ω A (Fin.cons h (Fin.cons f u) : Fin (m + 2) → TestFn))
    (hw : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : HermitianScalarTheory H),
      (∀ (k : ℕ) (f : Fin (k + 1) → TestFn),
        T.wightmanFn f = wightmanFunctional E Ω A (k + 1) (tensorVal fun i => (f i).1)) →
      ∀ S : ConfigSpace.FlatSequence,
        ConfigSpace.IsCLMSequence S →
        (∀ (k : ℕ) (φ : TestSpaces.PointTuple (k + 1) → ℂ),
          φ ∈ (TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus (k + 1)) :
            Set (TestSpaces.PointTuple (k + 1) → ℂ)) →
          ∀ h : φ ∈ ConfigSpace.schwartzFlatOffDiagonal (k + 1),
            S.atSucc k ⟨φ, h⟩ = integralSchwinger E Ω A k φ) →
        T.IsSchwingerSequence S ∧
          ∀ k : ℕ, ∃ (q : ℕ) (c : ℝ),
            IsAnalyticContinuationData T S k (vacuumExpectation E Ω A (k + 1)) q c
              (FieldForms.schwinger E Ω A k))
    (hv : TensorHilbertSeparable.Conclusions E Ω A) :
    FormTheoryProperties E Ω A (theoryOfTensorVecs hΩ hs hf hr hc) := by
  obtain ⟨F, hF, hpvm, hcarried, hint, hsemi⟩ := ht.exists_restriction
  have hspectral : (theoryOfTensorVecs hΩ hs hf hr hc).IsEnergyMomentumMeasure F :=
    ⟨hpvm, hcarried, fun a => hint a _ fun χ =>
      ht.translation_eq a _ (poincareOp_spec hr (pureTranslation a)) χ⟩
  have hW : ∀ (k : ℕ) (f : Fin (k + 1) → TestFn),
      (theoryOfTensorVecs hΩ hs hf hr hc).wightmanFn f =
        wightmanFunctional E Ω A (k + 1) (tensorVal fun i => (f i).1) := by
    intro k f
    have h := hf.fieldWord_eq _ (fieldOp_spec hf)
      ⟨vacuumVec E Ω A, tensorVec_mem_tensorDomainIn hs _⟩ (coe_vacuumVec hs) (k + 1) f
    change ⟪vacuumVec E Ω A, ((fieldWord (fun f Ψ => fieldOp hf f Ψ) f
      ⟨vacuumVec E Ω A, tensorVec_mem_tensorDomainIn hs _⟩ :
        tensorDomainIn E Ω A) : tensorHilbert E Ω A)⟫_ℂ = _
    rw [h, Submodule.coe_inner, coe_vacuumVec hs]
    rfl
  refine
    { isFormTheory :=
        { rep_eq := poincareOp_spec hr
          vacuum_eq := coe_vacuumVec hs
          domain_eq := rfl
          field_eq := fieldOp_spec hf }
      covariant := ?_
      spectrum := ⟨F, hspectral⟩
      local_field := ?_
      rep_translation := fun a χ =>
        ht.translation_eq a _ (poincareOp_spec hr (pureTranslation a)) χ
      exists_energyMomentum := ⟨F, hF, hspectral, hsemi⟩
      wightmanFn_eq := hW
      schwinger := hw _ hW
      uniqueVacuum := ?_ }
  · intro g f
    refine ⟨⟨_, hr.act_mem_schwartz g f⟩, ?_, fun Ψ => ?_⟩
    · funext x
      change poincarePullback g.1 (asOnePointFn f.1) (fun _ => x 0) = _
      congr 1
      funext i
      rw [Subsingleton.elim i 0]
    · exact ⟨⟨_, hr.op_symm_mem_domain g _ (poincareOp_spec hr g) Ψ Ψ.2⟩, rfl,
        hr.op_field_covariant g _ f ⟨_, hr.act_mem_schwartz g f⟩ _ _ (poincareOp_spec hr g) rfl
          (fieldOp_spec hf f) (fieldOp_spec hf _) Ψ _ rfl⟩
  · intro Ψ f h hsupp
    exact fieldOp_comm hs hf (fun m u => hl f h m u hsupp) Ψ
  · intro hfixed ψ hψ
    obtain ⟨c, hc'⟩ := hv.translation_invariant_eq_smul hfixed ψ fun a => by
      rw [← ht.translation_eq a _ (poincareOp_spec hr (pureTranslation a)) ψ]
      exact congrArg Subtype.val (hψ a)
    refine ⟨c, Subtype.ext ?_⟩
    rw [hc']
    change c • Ω = c • (vacuumVec E Ω A : K)
    rw [coe_vacuumVec hs]
end Building
theorem wightmanFromEuclideanForm_holds (h₁ : TensorVecInner.Claim)
    (h₂ : TensorFieldOperators.FieldOperatorsStatement)
    (h₃ : TensorPoincareRep.Claim)
    (h₄ : TensorRepContinuity.StronglyContinuous)
    (h₅ : TensorTranslations.Holds)
    (h₆ : TensorLocality.SpacelikeSwapInvariance)
    (h₇ : TheorySchwinger.Claim)
    (h₈ : TensorHilbertSeparable.Claim) : WightmanFromEuclideanForm := by
  intro K _ _ _ E Ω A ℘ C hform heuc
  have hs := h₁ E Ω A ℘ C hform
  have hf := h₂ E Ω A ℘ C hform
  have hr := h₃ E Ω A ℘ C hform heuc
  have hc := h₄ E Ω A ℘ C hform heuc (poincareOp hr) (poincareOp_spec hr)
  have ht := h₅ E Ω A ℘ C hform
  have hv := h₈ E Ω A ℘ C hform
  exact
    { poincareAct_mem := hr.act_mem_schwartz
      existsUnique_field := hf.exists_unique
      existsUnique_rep := hr.existsUnique_op
      exists_theory := ⟨theoryOfTensorVecs hform.norm_vacuum hs hf hr hc,
        formTheoryProperties_theoryOfTensorVecs hform.norm_vacuum hs hf hr hc ht
          (h₆ E Ω A ℘ C hform heuc) (h₇ E Ω A ℘ C hform heuc) hv⟩
      separable := hv.separableSpace }
end YangMills.Construction.FieldFormHilbert
