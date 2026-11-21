import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import Reconstruction.MinkowskiSpace.FieldOnTheTensorVectors
import Reconstruction.MinkowskiSpace.ScalarProductsAndDensityOfTheTensorVectors
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.FieldOnTensorVecs
abbrev TestFnTuple : Type := Σ m : ℕ, (Fin m → WightmanTheory.TestFn)
def prependTuple (f : WightmanTheory.TestFn) (p : TestFnTuple) : TestFnTuple :=
  ⟨p.1 + 1, Fin.cons f p.2⟩
def IsTemperedFunctional (u : WightmanTheory.TestFn → ℂ) : Prop :=
  ∃ (k : ℕ) (c : ℝ), 0 < k ∧ 0 ≤ c ∧ ∀ f : WightmanTheory.TestFn,
    ENNReal.ofReal ‖u f‖ ≤ ENNReal.ofReal c * WightmanTheory.schwartzNorm k f.1
theorem schwartzNorm_mono (hF : TestSpaces.Elementary.BasicProperties) {k k' : ℕ} (hk : 0 < k)
    (hkk : k ≤ k') (f : WightmanTheory.TestFn) :
    WightmanTheory.schwartzNorm k f.1 ≤ WightmanTheory.schwartzNorm k' f.1 :=
  (((hF 1 one_pos).1.1 _ f.2 _ f.2 0 0).2.1 k k' hk hkk).1
theorem isTemperedFunctional_zero : IsTemperedFunctional fun _ => 0 :=
  ⟨1, 0, one_pos, le_rfl, fun f => by simp⟩
theorem IsTemperedFunctional.add (hF : TestSpaces.Elementary.BasicProperties)
    {u v : WightmanTheory.TestFn → ℂ} (hu : IsTemperedFunctional u) (hv : IsTemperedFunctional v) :
    IsTemperedFunctional fun f => u f + v f := by
  obtain ⟨k, c, hk, hc, hu'⟩ := hu
  obtain ⟨k', c', hk', hc', hv'⟩ := hv
  refine ⟨max k k', c + c', lt_max_of_lt_left hk, add_nonneg hc hc', fun f => ?_⟩
  calc ENNReal.ofReal ‖u f + v f‖
      ≤ ENNReal.ofReal (‖u f‖ + ‖v f‖) := ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖u f‖ + ENNReal.ofReal ‖v f‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ ENNReal.ofReal c * WightmanTheory.schwartzNorm k f.1 +
          ENNReal.ofReal c' * WightmanTheory.schwartzNorm k' f.1 :=
        add_le_add (hu' f) (hv' f)
    _ ≤ ENNReal.ofReal c * WightmanTheory.schwartzNorm (max k k') f.1 +
          ENNReal.ofReal c' * WightmanTheory.schwartzNorm (max k k') f.1 :=
        add_le_add (mul_le_mul_right (schwartzNorm_mono hF hk (le_max_left _ _) f) _)
          (mul_le_mul_right (schwartzNorm_mono hF hk' (le_max_right _ _) f) _)
    _ = ENNReal.ofReal (c + c') * WightmanTheory.schwartzNorm (max k k') f.1 := by
        rw [ENNReal.ofReal_add hc hc', add_mul]
theorem IsTemperedFunctional.const_mul {u : WightmanTheory.TestFn → ℂ}
    (hu : IsTemperedFunctional u) (a : ℂ) : IsTemperedFunctional fun f => a * u f := by
  obtain ⟨k, c, hk, hc, hu'⟩ := hu
  refine ⟨k, ‖a‖ * c, hk, mul_nonneg (norm_nonneg _) hc, fun f => ?_⟩
  rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _), mul_assoc]
  exact mul_le_mul_right (hu' f) _
theorem maxPartialL1_nonneg (k : ℕ) (g : (Fin 4 → ℝ) → ℂ) :
    0 ≤ RealPointVectors.maxPartialL1 k g := by
  refine le_trans ?_ (Finset.le_sup' _ (Finset.self_mem_range_succ k))
  exact MeasureTheory.integral_nonneg fun x => norm_nonneg _
set_option linter.unusedSectionVars false
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
  (A : ℝ → OneLoopNotation.BddOp K)
def domainVec (p : TestFnTuple) : FieldFormHilbert.tensorDomainIn E Ω A :=
  ⟨FieldFormHilbert.tensorVec E Ω A p.2,
    show ((FieldFormHilbert.tensorVec E Ω A p.2 : FieldFormHilbert.tensorHilbert E Ω A) : K) ∈
        RealPointVectors.tensorDomain E Ω A from
      Submodule.subset_span ⟨p.1, fun i => (p.2 i).1, fun i => (p.2 i).2, rfl⟩⟩
def tupleComb : (TestFnTuple →₀ ℂ) →ₗ[ℂ] FieldFormHilbert.tensorDomainIn E Ω A :=
  Finsupp.linearCombination ℂ (domainVec E Ω A)
def prependedComb (f : WightmanTheory.TestFn) :
    (TestFnTuple →₀ ℂ) →ₗ[ℂ] FieldFormHilbert.tensorDomainIn E Ω A :=
  Finsupp.linearCombination ℂ fun p => domainVec E Ω A (prependTuple f p)
theorem tupleComb_single (p : TestFnTuple) (a : ℂ) :
    tupleComb E Ω A (Finsupp.single p a) = a • domainVec E Ω A p := by
  simp [tupleComb, Finsupp.linearCombination_single]
theorem prependedComb_single (f : WightmanTheory.TestFn) (p : TestFnTuple) (a : ℂ) :
    prependedComb E Ω A f (Finsupp.single p a) = a • domainVec E Ω A (prependTuple f p) := by
  simp [prependedComb, Finsupp.linearCombination_single]
variable {E Ω A}
theorem tupleComb_surjective (hS : TensorVecInner.Conclusions E Ω A) :
    Function.Surjective (tupleComb E Ω A) := by
  have key : ∀ x ∈ Submodule.span ℂ
      (Set.range fun p : Σ m : ℕ, (Fin m → WightmanTheory.TestFn) =>
        FieldFormHilbert.tensorVec E Ω A p.2),
      ∃ c, ((tupleComb E Ω A c : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A) = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hmem =>
      obtain ⟨p, rfl⟩ := hmem
      exact ⟨Finsupp.single p 1, by rw [tupleComb_single, one_smul]; rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, by simp⟩
    | smul a x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨a • c, by simp⟩
  rintro ⟨x, hx⟩
  obtain ⟨c, hc⟩ := key x (hS.domain_eq_span ▸ hx)
  exact ⟨c, Subtype.ext hc⟩
theorem wightmanFunctional_congr {m m' : ℕ} (hm : m = m') (u : Fin m → (Fin 4 → ℝ) → ℂ)
    (u' : Fin m' → (Fin 4 → ℝ) → ℂ) (hu : ∀ i, u i = u' (Fin.cast hm i)) :
    RealPointVectors.wightmanFunctional E Ω A m (RealPointVectors.tensorVal u) =
      RealPointVectors.wightmanFunctional E Ω A m' (RealPointVectors.tensorVal u') := by
  subst hm
  have : u = u' := funext fun i => by simpa using hu i
  rw [this]
theorem inner_domainVec_prepend (hS : TensorVecInner.Conclusions E Ω A)
    (f f' : WightmanTheory.TestFn) (hf' : f'.1 = fun x => conj (f.1 x)) (p q : TestFnTuple) :
    ⟪((domainVec E Ω A p : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A),
      ((domainVec E Ω A (prependTuple f q) : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ =
    ⟪((domainVec E Ω A (prependTuple f' p) : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A),
      ((domainVec E Ω A q : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ := by
  obtain ⟨m', t⟩ := p
  obtain ⟨m, g⟩ := q
  change ⟪FieldFormHilbert.tensorVec E Ω A t,
      FieldFormHilbert.tensorVec E Ω A (Fin.cons f g : Fin (m + 1) → WightmanTheory.TestFn)⟫_ℂ =
    ⟪FieldFormHilbert.tensorVec E Ω A (Fin.cons f' t : Fin (m' + 1) → WightmanTheory.TestFn),
      FieldFormHilbert.tensorVec E Ω A g⟫_ℂ
  rw [Submodule.coe_inner, Submodule.coe_inner, hS.inner_tensorVec, hS.inner_tensorVec]
  refine wightmanFunctional_congr (by omega) _ _ fun i => ?_
  induction i using Fin.addCases with
  | left j =>
    have hi : Fin.cast (by omega : m' + (m + 1) = m' + 1 + m) (Fin.castAdd (m + 1) j) =
        Fin.castAdd m j.castSucc := Fin.ext rfl
    rw [hi, Fin.append_left, Fin.append_left, Fin.rev_castSucc, Fin.cons_succ]
  | right j =>
    induction j using Fin.cases with
    | zero =>
      have hi : Fin.cast (by omega : m' + (m + 1) = m' + 1 + m) (Fin.natAdd m' 0) =
          Fin.castAdd m (Fin.last m') := Fin.ext rfl
      rw [hi, Fin.append_right, Fin.append_left, Fin.rev_last, Fin.cons_zero, Fin.cons_zero, hf']
      funext x
      simp
    | succ j =>
      have hi : Fin.cast (by omega : m' + (m + 1) = m' + 1 + m) (Fin.natAdd m' j.succ) =
          Fin.natAdd (m' + 1) j := Fin.ext (by simp; omega)
      rw [hi, Fin.append_right, Fin.append_right, Fin.cons_succ]
theorem inner_tupleComb_prependedComb (hS : TensorVecInner.Conclusions E Ω A)
    (f f' : WightmanTheory.TestFn) (hf' : f'.1 = fun x => conj (f.1 x)) (c d : TestFnTuple →₀ ℂ) :
    ⟪((tupleComb E Ω A c : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A),
      ((prependedComb E Ω A f d : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ =
    ⟪((prependedComb E Ω A f' c : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A),
      ((tupleComb E Ω A d : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' hc hc' => simp only [map_add, Submodule.coe_add, inner_add_left, hc, hc']
  | single p a =>
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d d' hd hd' => simp only [map_add, Submodule.coe_add, inner_add_right, hd, hd']
    | single q b =>
      simp only [tupleComb_single, prependedComb_single, Submodule.coe_smul,
        inner_smul_left, inner_smul_right, inner_domainVec_prepend hS f f' hf' p q]
theorem prependedComb_eq_zero (hS : TensorVecInner.Conclusions E Ω A)
    (f : WightmanTheory.TestFn) (c : TestFnTuple →₀ ℂ) (hc : tupleComb E Ω A c = 0) :
    prependedComb E Ω A f c = 0 := by
  refine Subtype.ext (hS.eq_zero_of_inner_eq_zero _ (prependedComb E Ω A f c).2 fun m t => ?_)
  have h1 := inner_tupleComb_prependedComb hS f ⟨_, hS.conj_mem_schwartz f⟩ rfl
    (Finsupp.single ⟨m, t⟩ 1) c
  rw [hc, tupleComb_single, one_smul] at h1
  exact show ⟪((domainVec E Ω A ⟨m, t⟩ : FieldFormHilbert.tensorDomainIn E Ω A) :
      FieldFormHilbert.tensorHilbert E Ω A),
      ((prependedComb E Ω A f c : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ = 0 from by simpa using h1
theorem exists_fieldOp (hS : TensorVecInner.Conclusions E Ω A) (f : WightmanTheory.TestFn) :
    ∃ L : FieldFormHilbert.tensorDomainIn E Ω A →ₗ[ℂ] FieldFormHilbert.tensorDomainIn E Ω A,
      ∀ c, L (tupleComb E Ω A c) = prependedComb E Ω A f c := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (tupleComb E Ω A)
    (LinearMap.range_eq_top.2 (tupleComb_surjective hS))
  refine ⟨prependedComb E Ω A f ∘ₗ g, fun c => ?_⟩
  have h0 : tupleComb E Ω A (g (tupleComb E Ω A c) - c) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact LinearMap.congr_fun hg _
  have h1 := prependedComb_eq_zero hS f _ h0
  rw [map_sub, sub_eq_zero] at h1
  exact h1
theorem isFieldOp_of_tupleComb (f : WightmanTheory.TestFn)
    (L : FieldFormHilbert.tensorDomainIn E Ω A →ₗ[ℂ] FieldFormHilbert.tensorDomainIn E Ω A)
    (hL : ∀ c, L (tupleComb E Ω A c) = prependedComb E Ω A f c) :
    FieldFormHilbert.IsFieldOp E Ω A (FieldFormHilbert.tensorDomainIn E Ω A) f L := by
  intro m t hD
  have h1 := hL (Finsupp.single ⟨m, t⟩ 1)
  rw [tupleComb_single, prependedComb_single, one_smul, one_smul] at h1
  exact congrArg Subtype.val h1
theorem apply_tupleComb (f : WightmanTheory.TestFn)
    (L : FieldFormHilbert.tensorDomainIn E Ω A →ₗ[ℂ] FieldFormHilbert.tensorDomainIn E Ω A)
    (hL : FieldFormHilbert.IsFieldOp E Ω A (FieldFormHilbert.tensorDomainIn E Ω A) f L)
    (c : TestFnTuple →₀ ℂ) : L (tupleComb E Ω A c) = prependedComb E Ω A f c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' hc hc' => simp only [map_add, hc, hc']
  | single p a =>
    rw [tupleComb_single, prependedComb_single, map_smul]
    congr 1
    exact Subtype.ext (hL p.1 p.2 (domainVec E Ω A p).2)
def conjRevAppendCons {m' m : ℕ} (t : Fin m' → WightmanTheory.TestFn) (f : WightmanTheory.TestFn)
    (g : Fin m → WightmanTheory.TestFn) : Fin (m' + (m + 1)) → (Fin 4 → ℝ) → ℂ :=
  Fin.append (fun i x => conj ((t (Fin.rev i)).1 x))
    fun i => ((Fin.cons f g : Fin (m + 1) → WightmanTheory.TestFn) i).1
theorem conjRevAppendCons_mem (hS : TensorVecInner.Conclusions E Ω A)
    {m' m : ℕ} (t : Fin m' → WightmanTheory.TestFn) (f : WightmanTheory.TestFn)
    (g : Fin m → WightmanTheory.TestFn) (i : Fin (m' + (m + 1))) :
    conjRevAppendCons (m' := m') (m := m) t f g i ∈ WightmanTheory.schwartzR4 := by
  induction i using Fin.addCases with
  | left j =>
    rw [conjRevAppendCons, Fin.append_left]
    exact hS.conj_mem_schwartz (t (Fin.rev j))
  | right j =>
    rw [conjRevAppendCons, Fin.append_right]
    exact ((Fin.cons f g : Fin (m + 1) → WightmanTheory.TestFn) j).2
theorem isTemperedFunctional_inner_domainVec {℘ C : ℝ} (hC : 1 ≤ C)
    (hV : RealPointVectors.BoundaryVectorFacts E Ω A ℘ C)
    (hS : TensorVecInner.Conclusions E Ω A) (p q : TestFnTuple) :
    IsTemperedFunctional fun f =>
      ⟪((domainVec E Ω A p : FieldFormHilbert.tensorDomainIn E Ω A) :
          FieldFormHilbert.tensorHilbert E Ω A),
        ((domainVec E Ω A (prependTuple f q) : FieldFormHilbert.tensorDomainIn E Ω A) :
          FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ := by
  obtain ⟨m', t⟩ := p
  obtain ⟨m, g⟩ := q
  obtain ⟨k, hk⟩ : ∃ k, k = (FieldForms.boundOrder ℘ (m' + m + 1)).toNat := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = 4 * ((2 : ℝ) ^ ℘ * C) ^ (m' + m + 1) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = ((m' + m + 1 : ℕ) : ℝ) ^ (2 * k) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∏ i : Fin m',
      RealPointVectors.maxPartialL1 k fun x => conj ((t (Fin.rev i)).1 x) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∏ j : Fin m, RealPointVectors.maxPartialL1 k (g j).1 :=
    ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by
    rw [hc₁]
    have : (0 : ℝ) ≤ (2 : ℝ) ^ ℘ * C :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
    positivity
  have hc₂0 : 0 ≤ c₂ := by
    rw [hc₂]
    positivity
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact Finset.prod_nonneg fun i _ => maxPartialL1_nonneg _ _
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    exact Finset.prod_nonneg fun i _ => maxPartialL1_nonneg _ _
  have hB : 0 ≤ c₁ * (c₂ * (P * Q)) :=
    mul_nonneg hc₁0 (mul_nonneg hc₂0 (mul_nonneg hP0 hQ0))
  refine ⟨k + 6, c₁ * (c₂ * (P * Q)) * Real.pi ^ 2, by omega,
    mul_nonneg hB (by positivity), fun f => ?_⟩
  have hprod : ∏ i : Fin (m' + (m + 1)),
      RealPointVectors.maxPartialL1 k (conjRevAppendCons (m' := m') (m := m) t f g i) =
      P * (RealPointVectors.maxPartialL1 k f.1 * Q) := by
    rw [Fin.prod_univ_add, Fin.prod_univ_succ, hP, hQ]
    simp [conjRevAppendCons, Fin.append_left, Fin.append_right]
  have hvalue : ⟪((domainVec E Ω A ⟨m', t⟩ : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A),
      ((domainVec E Ω A (prependTuple f ⟨m, g⟩) : FieldFormHilbert.tensorDomainIn E Ω A) :
        FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ =
      RealPointVectors.wightmanFunctional E Ω A (m' + m + 1)
        (TestSpaces.tensorProd (conjRevAppendCons (m' := m') (m := m) t f g)) :=
    (Submodule.coe_inner _ _ _).trans (hS.inner_tensorVec m' (m + 1) t _)
  have hmem : TestSpaces.tensorProd (conjRevAppendCons (m' := m') (m := m) t f g) ∈
      TestSpaces.schwartzSet (m' + m + 1) :=
    hV.tensorVal_mem (m' + m + 1) _ (conjRevAppendCons_mem hS t f g)
  have h1 := hV.norm_wightmanFunctional_le (m' + m) _ hmem
  have h2 := hV.fieldFormNorm_tensorProd_le (m' + m) (conjRevAppendCons (m' := m') (m := m) t f g)
    (conjRevAppendCons_mem hS t f g)
  rw [← hk, ← hc₂] at h2
  have h2' : RealPointVectors.fieldFormNorm ℘
      (TestSpaces.tensorProd (conjRevAppendCons (m' := m') (m := m) t f g)) ≤
      c₂ * (P * (RealPointVectors.maxPartialL1 k f.1 * Q)) := by
    rw [← hprod]
    exact h2
  have h3 : ‖RealPointVectors.wightmanFunctional E Ω A (m' + m + 1)
      (TestSpaces.tensorProd (conjRevAppendCons (m' := m') (m := m) t f g))‖ ≤
      c₁ * (c₂ * (P * Q)) * RealPointVectors.maxPartialL1 k f.1 := by
    calc _ ≤ c₁ * RealPointVectors.fieldFormNorm ℘
          (TestSpaces.tensorProd (conjRevAppendCons (m' := m') (m := m) t f g)) := by
          rw [hc₁]
          exact h1
      _ ≤ c₁ * (c₂ * (P * (RealPointVectors.maxPartialL1 k f.1 * Q))) :=
          mul_le_mul_of_nonneg_left h2' hc₁0
      _ = _ := by ring
  have h4 := hV.maxPartialL1_le k f.1 f.2
  beta_reduce
  rw [hvalue]
  calc ENNReal.ofReal ‖RealPointVectors.wightmanFunctional E Ω A (m' + m + 1)
        (TestSpaces.tensorProd (conjRevAppendCons (m' := m') (m := m) t f g))‖
      ≤ ENNReal.ofReal (c₁ * (c₂ * (P * Q)) * RealPointVectors.maxPartialL1 k f.1) :=
        ENNReal.ofReal_le_ofReal h3
    _ = ENNReal.ofReal (c₁ * (c₂ * (P * Q))) *
          ENNReal.ofReal (RealPointVectors.maxPartialL1 k f.1) :=
        ENNReal.ofReal_mul hB
    _ ≤ ENNReal.ofReal (c₁ * (c₂ * (P * Q))) *
          (ENNReal.ofReal (Real.pi ^ 2) * WightmanTheory.schwartzNorm (k + 6) f.1) :=
        mul_le_mul_right h4 _
    _ = ENNReal.ofReal (c₁ * (c₂ * (P * Q)) * Real.pi ^ 2) *
          WightmanTheory.schwartzNorm (k + 6) f.1 := by
        rw [ENNReal.ofReal_mul hB, mul_assoc]
theorem isTemperedFunctional_inner_tupleComb (hF : TestSpaces.Elementary.BasicProperties)
    {℘ C : ℝ} (hC : 1 ≤ C) (hV : RealPointVectors.BoundaryVectorFacts E Ω A ℘ C)
    (hS : TensorVecInner.Conclusions E Ω A) (c d : TestFnTuple →₀ ℂ) :
    IsTemperedFunctional fun f =>
      ⟪((tupleComb E Ω A c : FieldFormHilbert.tensorDomainIn E Ω A) :
          FieldFormHilbert.tensorHilbert E Ω A),
        ((prependedComb E Ω A f d : FieldFormHilbert.tensorDomainIn E Ω A) :
          FieldFormHilbert.tensorHilbert E Ω A)⟫_ℂ := by
  induction c using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, ZeroMemClass.coe_zero, inner_zero_left]
    exact isTemperedFunctional_zero
  | add c c' hc hc' =>
    simp only [map_add, Submodule.coe_add, inner_add_left]
    exact hc.add hF hc'
  | single p a =>
    induction d using Finsupp.induction_linear with
    | zero =>
      simp only [map_zero, ZeroMemClass.coe_zero, inner_zero_right]
      exact isTemperedFunctional_zero
    | add d d' hd hd' =>
      simp only [map_add, Submodule.coe_add, inner_add_right]
      exact hd.add hF hd'
    | single q b =>
      simp only [tupleComb_single, prependedComb_single, Submodule.coe_smul,
        inner_smul_left, inner_smul_right]
      exact ((isTemperedFunctional_inner_domainVec hC hV hS p q).const_mul _).const_mul _
theorem prependedComb_linear {℘ C : ℝ} (hV : RealPointVectors.BoundaryVectorFacts E Ω A ℘ C)
    (a b : ℂ) (f f' f'' : WightmanTheory.TestFn) (hf : f''.1 = a • f.1 + b • f'.1)
    (c : TestFnTuple →₀ ℂ) :
    prependedComb E Ω A f'' c =
      a • prependedComb E Ω A f c + b • prependedComb E Ω A f' c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' hc hc' =>
    simp only [map_add, hc, hc', smul_add]
    abel
  | single p z =>
    have hmem : ∀ f₀ : WightmanTheory.TestFn,
        TestSpaces.tensorProd
          (fun i => ((Fin.cons f₀ p.2 : Fin (p.1 + 1) → WightmanTheory.TestFn) i).1) ∈
          TestSpaces.schwartzSet (p.1 + 1) := fun f₀ =>
      hV.tensorVal_mem (p.1 + 1) _
        fun i => ((Fin.cons f₀ p.2 : Fin (p.1 + 1) → WightmanTheory.TestFn) i).2
    have hT : TestSpaces.tensorProd
        (fun i => ((Fin.cons f'' p.2 : Fin (p.1 + 1) → WightmanTheory.TestFn) i).1) =
        a • TestSpaces.tensorProd
            (fun i => ((Fin.cons f p.2 : Fin (p.1 + 1) → WightmanTheory.TestFn) i).1) +
          b • TestSpaces.tensorProd
            (fun i => ((Fin.cons f' p.2 : Fin (p.1 + 1) → WightmanTheory.TestFn) i).1) := by
      funext x
      simp only [TestSpaces.tensorProd, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, hf,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hlin := hV.testState_linear p.1 _ _ (hmem f) (hmem f') a b
    rw [← hT] at hlin
    have hv : domainVec E Ω A (prependTuple f'' p) =
        a • domainVec E Ω A (prependTuple f p) + b • domainVec E Ω A (prependTuple f' p) :=
      Subtype.ext (Subtype.ext hlin)
    simp only [prependedComb_single, hv, smul_add]
    rw [smul_comm z a, smul_comm z b]
theorem fieldOperatorsStatement_holds (hV : RealPointVectors.BoundaryVectorsStatement)
    (hS : TensorVecInner.Claim) (hF : TestSpaces.Elementary.BasicProperties) :
    TensorFieldOperators.FieldOperatorsStatement := by
  intro K _ _ _ E Ω A ℘ C hform
  have hV' := hV E Ω A ℘ C hform
  have hS' := hS E Ω A ℘ C hform
  have hsurj := tupleComb_surjective hS'
  refine ⟨fun f => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := exists_fieldOp hS' f
    refine ⟨L, isFieldOp_of_tupleComb f L hL, fun L' hL' => LinearMap.ext fun v => ?_⟩
    obtain ⟨c, rfl⟩ := hsurj v
    rw [apply_tupleComb f L' hL', hL]
  · intro a b f f' f'' L L' L'' hf hL hL' hL''
    refine LinearMap.ext fun v => ?_
    obtain ⟨c, rfl⟩ := hsurj v
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      apply_tupleComb f L hL, apply_tupleComb f' L' hL', apply_tupleComb f'' L'' hL'']
    exact prependedComb_linear hV' a b f f' f'' hf c
  · intro f f' L L' hf' hL hL' Ψ Ψ'
    obtain ⟨c, rfl⟩ := hsurj Ψ
    obtain ⟨d, rfl⟩ := hsurj Ψ'
    rw [apply_tupleComb f L hL, apply_tupleComb f' L' hL']
    exact inner_tupleComb_prependedComb hS' f f' hf' c d
  · intro Ψ Ψ'
    obtain ⟨c, rfl⟩ := hsurj Ψ
    obtain ⟨d, rfl⟩ := hsurj Ψ'
    obtain ⟨k, c₀, hk, hc₀, hb⟩ :=
      isTemperedFunctional_inner_tupleComb hF hform.one_le_const hV' hS' c d
    refine ⟨k, c₀, hk, hc₀, fun f L hL => ?_⟩
    rw [apply_tupleComb f L hL]
    exact hb f
  · intro φ hφ Ω' hΩ' m
    induction m with
    | zero =>
      intro f
      refine Subtype.ext ?_
      rw [hS'.tensorVec_fin_zero f]
      simpa [WightmanTheory.fieldWord] using hΩ'
    | succ m ih =>
      intro f
      have hsplit : WightmanTheory.fieldWord (fun f Ψ => φ f Ψ) f Ω' =
          φ (f 0) (WightmanTheory.fieldWord (fun f Ψ => φ f Ψ) (Fin.tail f) Ω') := by
        simp only [WightmanTheory.fieldWord, List.ofFn_succ, List.foldr_cons]
        rfl
      have h2 : WightmanTheory.fieldWord (fun f Ψ => φ f Ψ) (Fin.tail f) Ω' =
          domainVec E Ω A ⟨m, Fin.tail f⟩ := Subtype.ext (ih (Fin.tail f))
      have h3 := hφ (f 0) m (Fin.tail f) (domainVec E Ω A ⟨m, Fin.tail f⟩).2
      rw [Fin.cons_self_tail] at h3
      rw [hsplit, h2]
      exact h3
end YangMills.Construction.FieldOnTensorVecs
