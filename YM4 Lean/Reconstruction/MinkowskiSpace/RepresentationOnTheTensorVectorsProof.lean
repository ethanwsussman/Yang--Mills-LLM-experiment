import Reconstruction.MinkowskiSpace.ConeTubeAndLorentzGroup
import Reconstruction.MinkowskiSpace.PoincareInvarianceOfTheWightmanValues
import Reconstruction.MinkowskiSpace.RepresentationOnTheTensorVectors
import Reconstruction.MinkowskiSpace.ScalarProductsAndDensityOfTheTensorVectors
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.TensorPoincareRep
open MinkowskiSpace RealPointVectors WightmanTheory FieldFormHilbert ProjectionMeasures
  FormsOperators OneLoopNotation ComplexHilbert
section Families
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*}
theorem norm_linComb_eq_of_gram (u w : ι → H) (hG : ∀ i j, ⟪u i, u j⟫_ℂ = ⟪w i, w j⟫_ℂ)
    (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ u c‖ = ‖Finsupp.linearCombination ℂ w c‖ := by
  have h : ⟪Finsupp.linearCombination ℂ u c, Finsupp.linearCombination ℂ u c⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ w c, Finsupp.linearCombination ℂ w c⟫_ℂ := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, inner_sum, sum_inner, inner_smul_left,
      inner_smul_right, hG]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖Finsupp.linearCombination ℂ u c‖ ^ 2 = ‖Finsupp.linearCombination ℂ w c‖ ^ 2 := by
    exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'
theorem exists_linearIsometryEquiv_of_gram (u w : ι → H)
    (hG : ∀ i j, ⟪u i, u j⟫_ℂ = ⟪w i, w j⟫_ℂ)
    (hu : Dense (Submodule.span ℂ (Set.range u) : Set H))
    (hw : Dense (Submodule.span ℂ (Set.range w) : Set H)) :
    ∃ U : H ≃ₗᵢ[ℂ] H, ∀ i, U (u i) = w i := by
  set Lu := Finsupp.linearCombination ℂ u with hLu
  set Lw := Finsupp.linearCombination ℂ w with hLw
  have hnorm : ∀ c, ‖Lu c‖ = ‖Lw c‖ := norm_linComb_eq_of_gram u w hG
  have hker : LinearMap.ker Lu ≤ LinearMap.ker Lw := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, ← hnorm, hc, norm_zero]
  let S₀ : LinearMap.range Lu →ₗ[ℂ] H :=
    (LinearMap.ker Lu).liftQ Lw hker ∘ₗ Lu.quotKerEquivRange.symm.toLinearMap
  have hS₀ : ∀ c (hc : Lu c ∈ LinearMap.range Lu), S₀ ⟨Lu c, hc⟩ = Lw c := by
    intro c hc
    simp only [S₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hS₀norm : ∀ x : LinearMap.range Lu, ‖S₀ x‖ = ‖(x : H)‖ := by
    intro x
    obtain ⟨c, hc⟩ := x.2
    have hx : x = ⟨Lu c, LinearMap.mem_range_self _ _⟩ := Subtype.ext hc.symm
    rw [hx, hS₀]
    exact (hnorm c).symm
  have hrange : (LinearMap.range Lu : Set H) = Submodule.span ℂ (Set.range u) := by
    rw [hLu, Finsupp.range_linearCombination]
  have hdense : DenseRange ((LinearMap.range Lu).subtypeL) := by
    have hd : Dense (LinearMap.range Lu : Set H) := hrange ▸ hu
    have hset : Set.range ((LinearMap.range Lu).subtypeL) = (LinearMap.range Lu : Set H) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    unfold DenseRange
    rw [hset]
    exact hd
  have hbound : ∃ C, ∀ x, ‖S₀ x‖ ≤ C * ‖(LinearMap.range Lu).subtypeL x‖ :=
    ⟨1, fun x => by simp [hS₀norm]⟩
  let S : H →L[ℂ] H := S₀.extendOfNorm (LinearMap.range Lu).subtypeL
  have hS : ∀ x : LinearMap.range Lu, S (x : H) = S₀ x := fun x =>
    LinearMap.extendOfNorm_eq hdense hbound x
  have hSnorm : ∀ x, ‖S x‖ = ‖x‖ := by
    intro x
    have hclosed : IsClosed {x : H | ‖S x‖ = ‖x‖} :=
      isClosed_eq (continuous_norm.comp S.continuous) continuous_norm
    have hd : Dense (LinearMap.range Lu : Set H) := hrange ▸ hu
    have hsub : (LinearMap.range Lu : Set H) ⊆ {x : H | ‖S x‖ = ‖x‖} := by
      intro y hy
      have := hS ⟨y, hy⟩
      show ‖S y‖ = ‖y‖
      rw [this, hS₀norm]
    exact hclosed.closure_subset_iff.2 hsub (hd x)
  let J : H →ₗᵢ[ℂ] H := ⟨S.toLinearMap, hSnorm⟩
  have hJ : ∀ i, J (u i) = w i := by
    intro i
    have hmem : Lu (Finsupp.single i 1) ∈ LinearMap.range Lu := ⟨_, rfl⟩
    have h1 : Lu (Finsupp.single i 1) = u i := by simp [hLu]
    have h2 : Lw (Finsupp.single i 1) = w i := by simp [hLw]
    have h3 := hS ⟨_, hmem⟩
    rw [hS₀] at h3
    rw [h2] at h3
    simpa [J, h1] using h3
  have hsurj : Function.Surjective J := by
    have hclosed : IsClosed (Set.range J) := J.isometry.isClosedEmbedding.isClosed_range
    have hsub : (Submodule.span ℂ (Set.range w) : Set H) ⊆ Set.range J := by
      have : Submodule.span ℂ (Set.range w) ≤ LinearMap.range J.toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact ⟨u i, hJ i⟩
      intro y hy
      obtain ⟨x, hx⟩ := this hy
      exact ⟨x, hx⟩
    intro y
    exact hclosed.closure_subset_iff.2 hsub (hw y)
  exact ⟨LinearIsometryEquiv.ofSurjective J hsurj, hJ⟩
theorem linearIsometryEquiv_ext_of_dense_span (u : ι → H)
    (hu : Dense (Submodule.span ℂ (Set.range u) : Set H)) {U U' : H ≃ₗᵢ[ℂ] H}
    (h : ∀ i, U (u i) = U' (u i)) : U = U' := by
  have hc : (U.toContinuousLinearEquiv : H →L[ℂ] H) = (U'.toContinuousLinearEquiv : H →L[ℂ] H) := by
    refine ContinuousLinearMap.ext_on hu ?_
    rintro _ ⟨i, rfl⟩
    exact h i
  ext x
  exact congrArg (fun B : H →L[ℂ] H => B x) hc
end Families
theorem poincareActR4_poincareActR4 (g g' g'' : PoincareElt)
    (h : g''.1 = poincareMul g.1 g'.1) (f : (Fin 4 → ℝ) → ℂ) :
    poincareActR4 g (poincareActR4 g' f) =
      poincareActR4 g'' f := by
  funext x
  have hdet : IsUnit g.1.2.det := by
    rw [g.2.2.2.1]
    exact isUnit_one
  simp only [poincareActR4, poincarePullback, asOnePointFn, h, poincareMul]
  congr 1
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  congr 1
  have h1 : g.1.2⁻¹.mulVec (g.1.2.mulVec g'.1.1) = g'.1.1 := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [show x - (g.1.1 + g.1.2.mulVec g'.1.1) = (x - g.1.1) - g.1.2.mulVec g'.1.1 by abel,
    Matrix.mulVec_sub _ (x - g.1.1), h1]
theorem poincareActR4_of_eq_one (g : PoincareElt) (h : g.1 = (0, 1)) (f : (Fin 4 → ℝ) → ℂ) :
    poincareActR4 g f = f := by
  funext x
  simp [poincareActR4, poincarePullback, asOnePointFn, h]
theorem asOnePointFn_poincareActR4 (g : PoincareElt) (f : (Fin 4 → ℝ) → ℂ) :
    asOnePointFn (poincareActR4 g f) = poincarePullback g.1 (asOnePointFn f) := by
  funext x
  simp only [poincareActR4, asOnePointFn, poincarePullback]
theorem tensorVal_poincareActR4 (g : PoincareElt) {n : ℕ}
    (F : Fin (n + 1) → (Fin 4 → ℝ) → ℂ) :
    (tensorVal (fun i => poincareActR4 g (F i)) : Motions.TensorVal ℂ (n + 1)) =
      poincarePullback g.1 (tensorVal F : Motions.TensorVal ℂ (n + 1)) := rfl
section Form
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K}
abbrev allTensorVecs (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) :
    (Σ n : ℕ, (Fin n → TestFn)) → tensorHilbert E Ω A :=
  fun p => tensorVec E Ω A p.2
def testAct (hm : ∀ (g : PoincareElt) (f : TestFn),
    poincareActR4 g f.1 ∈ WightmanTheory.schwartzR4)
    (g : PoincareElt) (f : TestFn) : TestFn :=
  ⟨poincareActR4 g f.1, hm g f⟩
variable (hs : TensorVecInner.Conclusions E Ω A)
  (hm : ∀ (g : PoincareElt) (f : TestFn),
    poincareActR4 g f.1 ∈ WightmanTheory.schwartzR4)
include hs in
theorem dense_span_allTensorVecs :
    Dense (Submodule.span ℂ (Set.range (allTensorVecs E Ω A)) : Set (tensorHilbert E Ω A)) := by
  have h := hs.dense_domain
  rw [hs.domain_eq_span] at h
  exact h
theorem testAct_testAct_of_mul_eq_one (g g' : PoincareElt) (h : poincareMul g.1 g'.1 = (0, 1))
    (f : TestFn) : testAct hm g (testAct hm g' f) = f :=
  Subtype.ext ((poincareActR4_poincareActR4 g g' (WightmanTheory.pureTranslation 0) h.symm f.1).trans
    (poincareActR4_of_eq_one (WightmanTheory.pureTranslation 0) rfl f.1))
theorem isPoincareOp_iff (g : PoincareElt)
    (U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A)) :
    IsPoincareOp E Ω A g U ↔ ∀ (n : ℕ) (f : Fin n → TestFn),
      U (tensorVec E Ω A f) = tensorVec E Ω A fun i => testAct hm g (f i) :=
  ⟨fun h n f => Subtype.ext (h n f), fun h n f => congrArg Subtype.val (h n f)⟩
theorem wightmanFunctional_tensorVal_poincareActR4
    (ht : ∀ (n : ℕ) (F : Fin n → (Fin 4 → ℝ) → ℂ), (∀ i, F i ∈ WightmanTheory.schwartzR4) →
      tensorVal F ∈ WightmanReconstruction.schwartzOfOrder n)
    (hW : ∀ (g : PoincareElt) (n : ℕ) (φ : TestSpaces.PointTuple (n + 1) → ℂ),
      φ ∈ TestSpaces.schwartzSet (n + 1) →
        wightmanFunctional E Ω A (n + 1) (poincarePullback g.1 φ) = wightmanFunctional E Ω A (n + 1) φ)
    (g : PoincareElt) (k : ℕ) (F : Fin k → (Fin 4 → ℝ) → ℂ)
    (hF : ∀ i, F i ∈ WightmanTheory.schwartzR4) :
    wightmanFunctional E Ω A k (tensorVal fun i => poincareActR4 g (F i)) =
      wightmanFunctional E Ω A k (tensorVal F) := by
  cases k with
  | zero =>
    have h : (fun i => poincareActR4 g (F i)) = F := funext fun i => i.elim0
    rw [h]
  | succ n =>
    rw [tensorVal_poincareActR4]
    exact hW g n _ (ht (n + 1) F hF)
include hs in
theorem inner_tensorVec_testAct
    (ht : ∀ (n : ℕ) (F : Fin n → (Fin 4 → ℝ) → ℂ), (∀ i, F i ∈ WightmanTheory.schwartzR4) →
      tensorVal F ∈ WightmanReconstruction.schwartzOfOrder n)
    (hW : ∀ (g : PoincareElt) (n : ℕ) (φ : TestSpaces.PointTuple (n + 1) → ℂ),
      φ ∈ TestSpaces.schwartzSet (n + 1) →
        wightmanFunctional E Ω A (n + 1) (poincarePullback g.1 φ) = wightmanFunctional E Ω A (n + 1) φ)
    (g : PoincareElt) {n' n : ℕ} (h : Fin n' → TestFn) (f : Fin n → TestFn) :
    ⟪tensorVec E Ω A h, tensorVec E Ω A f⟫_ℂ =
      ⟪tensorVec E Ω A (fun i => testAct hm g (h i)), tensorVec E Ω A fun i => testAct hm g (f i)⟫_ℂ := by
  set F : Fin (n' + n) → (Fin 4 → ℝ) → ℂ :=
    Fin.append (fun i x => conj ((h (Fin.rev i)).1 x)) fun i => (f i).1 with hFdef
  have hF : ∀ i, F i ∈ WightmanTheory.schwartzR4 := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hFdef, Fin.append_left]
      exact hs.conj_mem_schwartz _
    · rw [hFdef, Fin.append_right]
      exact (f i).2
  have hA : (Fin.append (fun i x => conj ((testAct hm g (h (Fin.rev i))).1 x))
      fun i => (testAct hm g (f i)).1 : Fin (n' + n) → (Fin 4 → ℝ) → ℂ) =
        fun i => poincareActR4 g (F i) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hFdef, Fin.append_left, Fin.append_left]
      rfl
    · rw [hFdef, Fin.append_right, Fin.append_right]
      rfl
  have e₁ : ⟪(tensorVec E Ω A h : K), (tensorVec E Ω A f : K)⟫_ℂ =
      wightmanFunctional E Ω A (n' + n) (tensorVal F) := hs.inner_tensorVec n' n h f
  have e₂ : ⟪(tensorVec E Ω A (fun i => testAct hm g (h i)) : K),
      (tensorVec E Ω A (fun i => testAct hm g (f i)) : K)⟫_ℂ =
      wightmanFunctional E Ω A (n' + n) (tensorVal
        (Fin.append (fun i x => conj ((testAct hm g (h (Fin.rev i))).1 x))
          fun i => (testAct hm g (f i)).1)) :=
    hs.inner_tensorVec n' n _ _
  rw [hA, wightmanFunctional_tensorVal_poincareActR4 ht hW g _ F hF] at e₂
  exact e₁.trans e₂.symm
theorem unitaryMap_eq_of_tensorVec (hs : TensorVecInner.Conclusions E Ω A)
    {U U' : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A)}
    (h : ∀ (n : ℕ) (f : Fin n → TestFn), U (tensorVec E Ω A f) = U' (tensorVec E Ω A f)) :
    U = U' :=
  linearIsometryEquiv_ext_of_dense_span (allTensorVecs E Ω A) (dense_span_allTensorVecs hs)
    fun p => h p.1 p.2
include hs in
theorem tensorVec_mem_domain {n : ℕ} (f : Fin n → TestFn) :
    tensorVec E Ω A f ∈ tensorDomainIn E Ω A := by
  rw [hs.domain_eq_span]
  exact Submodule.subset_span ⟨⟨n, f⟩, rfl⟩
include hs in
theorem unitaryMap_mapsTo_domain
    (U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A))
    (a : TestFn → TestFn)
    (hU : ∀ (n : ℕ) (f : Fin n → TestFn),
      U (tensorVec E Ω A f) = tensorVec E Ω A fun i => a (f i))
    (ψ : tensorHilbert E Ω A) (hψ : ψ ∈ tensorDomainIn E Ω A) :
    U ψ ∈ tensorDomainIn E Ω A := by
  rw [hs.domain_eq_span] at hψ
  refine Submodule.span_induction (p := fun x _ => U x ∈ tensorDomainIn E Ω A)
    ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨p, rfl⟩
    show U (tensorVec E Ω A p.2) ∈ _
    rw [hU]
    exact tensorVec_mem_domain hs _
  · rw [map_zero]
    exact zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx
include hs hm in
theorem conclusions_of_invariance
    (ht : ∀ (n : ℕ) (F : Fin n → (Fin 4 → ℝ) → ℂ), (∀ i, F i ∈ WightmanTheory.schwartzR4) →
      tensorVal F ∈ WightmanReconstruction.schwartzOfOrder n)
    (hW : ∀ (g : PoincareElt) (n : ℕ) (φ : TestSpaces.PointTuple (n + 1) → ℂ),
      φ ∈ TestSpaces.schwartzSet (n + 1) →
        wightmanFunctional E Ω A (n + 1) (poincarePullback g.1 φ) = wightmanFunctional E Ω A (n + 1) φ)
    (inv : PoincareElt → PoincareElt)
    (hinv : ∀ g : PoincareElt, poincareMul g.1 (inv g).1 = (0, 1)) :
    Conclusions E Ω A := by
  have hact : ∀ {g : PoincareElt}
      {U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A)},
      IsPoincareOp E Ω A g U → ∀ (n : ℕ) (f : Fin n → TestFn),
        U (tensorVec E Ω A f) = tensorVec E Ω A fun i => testAct hm g (f i) :=
    fun {g U} h => (isPoincareOp_iff hm g U).1 h
  have hsymm : ∀ {g : PoincareElt}
      {U : UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A)},
      IsPoincareOp E Ω A g U → ∀ (n : ℕ) (f : Fin n → TestFn),
        U.symm (tensorVec E Ω A f) = tensorVec E Ω A fun i => testAct hm (inv g) (f i) := by
    intro g U h n f
    have e : U (tensorVec E Ω A fun i => testAct hm (inv g) (f i)) = tensorVec E Ω A f := by
      rw [hact h]
      exact congrArg (tensorVec E Ω A)
        (funext fun i => testAct_testAct_of_mul_eq_one hm g _ (hinv g) (f i))
    rw [← e, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    have hdense := dense_span_allTensorVecs hs
    have hrange : Set.range (fun p : Σ n : ℕ, (Fin n → TestFn) =>
        tensorVec E Ω A fun i => testAct hm g (p.2 i)) = Set.range (allTensorVecs E Ω A) := by
      ext y
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨⟨p.1, fun i => testAct hm g (p.2 i)⟩, rfl⟩
      · rintro ⟨p, rfl⟩
        refine ⟨⟨p.1, fun i => testAct hm (inv g) (p.2 i)⟩, ?_⟩
        exact congrArg (tensorVec E Ω A)
          (funext fun i => testAct_testAct_of_mul_eq_one hm g _ (hinv g) (p.2 i))
    obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_of_gram (allTensorVecs E Ω A)
      (fun p => tensorVec E Ω A fun i => testAct hm g (p.2 i))
      (fun p q => inner_tensorVec_testAct hs hm ht hW g p.2 q.2) hdense (by rw [hrange]; exact hdense)
    refine ⟨U, (isPoincareOp_iff hm g U).2 fun n f => hU ⟨n, f⟩, fun U' hU' => ?_⟩
    refine unitaryMap_eq_of_tensorVec hs fun n f => ?_
    rw [hact hU' n f]
    exact (hU ⟨n, f⟩).symm
  · intro g g' g'' U U' U'' hg h h' h''
    refine unitaryMap_eq_of_tensorVec hs fun n f => ?_
    rw [hact h'' n f, LinearIsometryEquiv.coe_mul, Function.comp_apply, hact h' n f, hact h n]
    refine congrArg (tensorVec E Ω A) (funext fun i => Subtype.ext ?_)
    exact (poincareActR4_poincareActR4 g g' g'' hg (f i).1).symm
  · intro g U Ω' h hΩ
    let f₀ : Fin 0 → TestFn := fun i => i.elim0
    have h₀ : tensorVec E Ω A f₀ = Ω' := Subtype.ext ((hs.tensorVec_fin_zero f₀).trans hΩ.symm)
    rw [← h₀, hact h 0 f₀]
    exact congrArg (tensorVec E Ω A) (funext fun i => i.elim0)
  · intro g U h ψ hψ
    exact unitaryMap_mapsTo_domain hs U (testAct hm g) (hact h) ψ hψ
  · intro g U h ψ hψ
    exact unitaryMap_mapsTo_domain hs U.symm (testAct hm (inv g)) (hsymm h) ψ hψ
  · intro g U f f' L L' h hf' hL hL' Ψ Ψ' hΨ
    have hDsymm : ∀ ψ ∈ tensorDomainIn E Ω A, U.symm ψ ∈ tensorDomainIn E Ω A :=
      unitaryMap_mapsTo_domain hs U.symm (testAct hm (inv g)) (hsymm h)
    have hspan : ∀ x (hx : x ∈ Submodule.span ℂ (Set.range (allTensorVecs E Ω A))),
        ∀ hxD : x ∈ tensorDomainIn E Ω A,
        U ((L ⟨U.symm x, hDsymm x hxD⟩ : tensorDomainIn E Ω A) :
            tensorHilbert E Ω A) =
          ((L' ⟨x, hxD⟩ : tensorDomainIn E Ω A) : tensorHilbert E Ω A) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨p, rfl⟩ := hx
        intro hxD
        have hv : (⟨U.symm (tensorVec E Ω A p.2), hDsymm _ hxD⟩ : tensorDomainIn E Ω A) =
            ⟨tensorVec E Ω A (fun i => testAct hm (inv g) (p.2 i)),
              tensorVec_mem_domain hs _⟩ :=
          Subtype.ext (hsymm h p.1 p.2)
        show U ((L ⟨U.symm (tensorVec E Ω A p.2), hDsymm _ hxD⟩ : tensorDomainIn E Ω A) :
          tensorHilbert E Ω A) = ((L' ⟨tensorVec E Ω A p.2, hxD⟩ :
            tensorDomainIn E Ω A) : tensorHilbert E Ω A)
        rw [hv, hL p.1 _ (tensorVec_mem_domain hs _), hL' p.1 _ hxD, hact h]
        refine congrArg (tensorVec E Ω A) (funext fun i => ?_)
        refine Fin.cases ?_ (fun i => ?_) i
        · exact Subtype.ext hf'.symm
        · exact testAct_testAct_of_mul_eq_one hm g _ (hinv g) (p.2 i)
      | zero =>
        intro hxD
        have e₁ : (⟨U.symm 0, hDsymm 0 hxD⟩ : tensorDomainIn E Ω A) = 0 :=
          Subtype.ext (map_zero U.symm)
        have e₂ : (⟨0, hxD⟩ : tensorDomainIn E Ω A) = 0 := rfl
        rw [e₁, e₂, map_zero, map_zero]
        simp
      | add x y hx hy ihx ihy =>
        intro hxD
        have hxD' : x ∈ tensorDomainIn E Ω A := by
          rw [hs.domain_eq_span]
          exact hx
        have hyD' : y ∈ tensorDomainIn E Ω A := by
          rw [hs.domain_eq_span]
          exact hy
        have e₁ : (⟨U.symm (x + y), hDsymm _ hxD⟩ : tensorDomainIn E Ω A) =
            ⟨U.symm x, hDsymm x hxD'⟩ + ⟨U.symm y, hDsymm y hyD'⟩ :=
          Subtype.ext (map_add U.symm x y)
        have e₂ : (⟨x + y, hxD⟩ : tensorDomainIn E Ω A) = ⟨x, hxD'⟩ + ⟨y, hyD'⟩ := rfl
        rw [e₁, e₂, map_add, map_add]
        simp only [Submodule.coe_add, map_add]
        rw [ihx hxD', ihy hyD']
      | smul c x hx ih =>
        intro hxD
        have hxD' : x ∈ tensorDomainIn E Ω A := by
          rw [hs.domain_eq_span]
          exact hx
        have e₁ : (⟨U.symm (c • x), hDsymm _ hxD⟩ : tensorDomainIn E Ω A) =
            c • ⟨U.symm x, hDsymm x hxD'⟩ :=
          Subtype.ext (map_smul U.symm c x)
        have e₂ : (⟨c • x, hxD⟩ : tensorDomainIn E Ω A) = c • ⟨x, hxD'⟩ := rfl
        rw [e₁, e₂, map_smul, map_smul]
        simp only [Submodule.coe_smul, map_smul]
        rw [ih hxD']
    have hΨ' : (Ψ : tensorHilbert E Ω A) ∈
        Submodule.span ℂ (Set.range (allTensorVecs E Ω A)) :=
      (Submodule.ext_iff.1 hs.domain_eq_span _).1 Ψ.2
    have e : Ψ' = ⟨U.symm Ψ, hDsymm _ Ψ.2⟩ := Subtype.ext hΨ
    rw [e]
    exact hspan _ hΨ' Ψ.2
end Form
theorem claim_holds (hcone : MinkowskiSpace.ConeTubeLorentz.Statement)
    (hvec : RealPointVectors.BoundaryVectorsStatement)
    (hsc : TensorVecInner.Claim)
    (hinvar : WightmanPoincare.WightmanPoincareInvariance) : Claim := by
  intro K _ _ _ E Ω A ℘ C hb he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, hgroup, -⟩, -⟩ := hcone
  have hm : ∀ (g : PoincareElt) (f : TestFn),
      poincareActR4 g f.1 ∈ WightmanTheory.schwartzR4 := by
    intro g f
    show asOnePointFn (poincareActR4 g f.1) ∈ TestSpaces.schwartzSet 1
    rw [asOnePointFn_poincareActR4]
    exact (hinvar E Ω A ℘ C hb he g 0 (asOnePointFn f.1) f.2).1
  exact conclusions_of_invariance (hsc E Ω A ℘ C hb) hm (hvec E Ω A ℘ C hb).tensorVal_mem
    (fun g n φ hφ => (hinvar E Ω A ℘ C hb he g n φ hφ).2)
    (fun g => ⟨poincareInv g.1, (hgroup g.1 g.2).1⟩) (fun g => (hgroup g.1 g.2).2.1)
end YangMills.Construction.TensorPoincareRep
