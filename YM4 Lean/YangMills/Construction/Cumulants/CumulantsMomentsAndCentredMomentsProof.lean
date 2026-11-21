import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionFacts
import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.Cumulants.TupleGeneratingFunctionAndItsLogarithm
import YangMills.Construction.Functions.DerivativeOfACompositeInDistinctVariables
import YangMills.Construction.SourcesAndGluing.CumulantsOfBoundedVariablesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.Cumulants.MomentCumulantFormulas
open YangMills.Construction.ComplexVariables YangMills.Construction.SetPartition YangMills.Construction.Probability
section Bounded
variable {Ω : Type} [MeasurableSpace Ω]
theorem isBoundedRealRV_add_const {x : Ω → ℝ} (hx : IsBoundedRealRV x) (c : ℝ) :
    IsBoundedRealRV fun ω => x ω + c := by
  obtain ⟨C, hC⟩ := hx.bounded
  refine ⟨hx.measurable.add_const c, C + |c|, fun ω => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hC ω) le_rfl)
theorem isBoundedRealRV_mul {x y : Ω → ℝ} (hx : IsBoundedRealRV x)
    (hy : IsBoundedRealRV y) : IsBoundedRealRV fun ω => x ω * y ω := by apply _root_.YangMills.Construction.SourcesAndGluing.BoundedCumulants.isBoundedRealRV_mul <;> assumption
theorem isBoundedRealRV_const (c : ℝ) : IsBoundedRealRV fun _ : Ω => c :=
  ⟨measurable_const, |c|, fun _ => le_rfl⟩
theorem isBoundedRealRV_linComb {x y : Ω → ℝ} (hx : IsBoundedRealRV x)
    (hy : IsBoundedRealRV y) (a b : ℝ) :
    IsBoundedRealRV fun ω => a * x ω + b * y ω := by
  obtain ⟨C, hC⟩ := (isBoundedRealRV_mul (isBoundedRealRV_const a) hx).bounded
  obtain ⟨D, hD⟩ := (isBoundedRealRV_mul (isBoundedRealRV_const b) hy).bounded
  refine ⟨((isBoundedRealRV_mul (isBoundedRealRV_const a) hx).measurable).add
    ((isBoundedRealRV_mul (isBoundedRealRV_const b) hy).measurable), C + D, fun ω => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hC ω) (hD ω))
theorem isBoundedRealRV_prod {ι : Type} (s : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, IsBoundedRealRV (f i)) :
    IsBoundedRealRV fun ω => ∏ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isBoundedRealRV_const (Ω := Ω) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact isBoundedRealRV_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
theorem integrable_of_isBoundedRealRV {x : Ω → ℝ} (hx : IsBoundedRealRV x) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Integrable x μ := by
  obtain ⟨C, hC⟩ := hx.bounded
  exact Integrable.of_bound hx.measurable.aestronglyMeasurable C
    (ae_of_all _ fun ω => by simpa using hC ω)
end Bounded
section OneVariable
theorem iteratedDeriv_succ_logPrincipal (k : ℕ) {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    iteratedDeriv (k + 1) logPrincipal w =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) * (w ^ (k + 1))⁻¹ := by
  induction k generalizing w with
  | zero =>
    rw [iteratedDeriv_one]
    have hd : HasDerivAt logPrincipal w⁻¹ w := Complex.hasDerivAt_log hw
    simpa using hd.deriv
  | succ k ih =>
    have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
    have hev : iteratedDeriv (k + 1) logPrincipal =ᶠ[nhds w]
        fun v => (-1 : ℂ) ^ k * (k.factorial : ℂ) * (v ^ (k + 1))⁻¹ :=
      Filter.eventually_of_mem (Complex.isOpen_slitPlane.mem_nhds hw) fun v hv => ih hv
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hd : HasDerivAt (fun v : ℂ => (-1 : ℂ) ^ k * (k.factorial : ℂ) * (v ^ (k + 1))⁻¹)
        ((-1 : ℂ) ^ k * (k.factorial : ℂ) *
          (-(((k + 1 : ℕ) : ℂ) * w ^ (k + 1 - 1)) / (w ^ (k + 1)) ^ 2)) w :=
      ((hasDerivAt_pow (k + 1) w).inv (pow_ne_zero _ hw0)).const_mul _
    rw [hd.deriv, Nat.factorial_succ]
    push_cast
    field_simp
    ring
theorem iteratedDeriv_cexp_apply (k : ℕ) (w : ℂ) :
    iteratedDeriv k Complex.exp w = Complex.exp w := by
  rw [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]
theorem isHolomorphicVia_of_differentiableOn {W : Set ℂ} {g : ℂ → ℂ} (hW : IsOpen W)
    (hg : DifferentiableOn ℂ g W) :
    Coordinates.ComplexCoordinates.IsHolomorphicVia (Equiv.funUnique (Fin 1) ℂ).symm
      (Equiv.funUnique (Fin 1) ℂ).symm W g := by
  have he : ∀ (x : ℂ) (i : Fin 1), (Equiv.funUnique (Fin 1) ℂ).symm x i = x := by
    intro x i
    simp [Equiv.funUnique]
  have hs : ∀ z : Fin 1 → ℂ, (Equiv.funUnique (Fin 1) ℂ) z = z 0 := by
    intro z
    simp [Equiv.funUnique]
  have himg : (Equiv.funUnique (Fin 1) ℂ).symm '' W = (fun z : Fin 1 → ℂ => z 0) ⁻¹' W := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [he] using hw
    · intro hz
      refine ⟨z 0, hz, ?_⟩
      funext i
      rw [he, Subsingleton.elim i 0]
  have hf : ((Equiv.funUnique (Fin 1) ℂ).symm ∘ g ∘ (Equiv.funUnique (Fin 1) ℂ).symm.symm) =
      fun z _ => g (z 0) := by
    funext z i
    simp only [Function.comp, Equiv.symm_symm, he, hs]
  unfold Coordinates.ComplexCoordinates.IsHolomorphicVia
    Coordinates.ComplexCoordinates.IsHolomorphicIn
  rw [himg, hf]
  have hc : Continuous fun z : Fin 1 → ℂ => z 0 := continuous_apply 0
  refine ⟨hW.preimage hc, ?_, ?_⟩
  · refine continuousOn_pi.2 fun _ => ?_
    exact hg.continuousOn.comp hc.continuousOn fun z hz => hz
  · intro a ha j
    have hcont : Continuous fun ζ : ℂ =>
        (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0 := by
      fun_prop
    have hmem : ∀ᶠ ζ in nhds (0 : ℂ),
        (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0 ∈ W := by
      refine hcont.continuousAt.eventually_mem (hW.mem_nhds ?_)
      simpa using ha
    filter_upwards [hmem] with ζ hζ
    refine differentiableAt_pi.2 fun _ => ?_
    have hd : DifferentiableAt ℂ g
        ((a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0) :=
      (hg _ hζ).differentiableAt (hW.mem_nhds hζ)
    have hl : DifferentiableAt ℂ
        (fun ζ : ℂ => (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0) ζ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    exact DifferentiableAt.comp ζ hd hl
end OneVariable
section Moments
variable {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
theorem finsetMoment_eq_integral (μ : Measure Ω) [IsProbabilityMeasure μ] (y : Fin n → Ω → ℝ)
    (J : Finset (Fin n)) :
    finsetMoment μ y J = ((∫ ω, ∏ l ∈ J, y l ω ∂μ : ℝ) : ℂ) := by
  unfold finsetMoment
  split_ifs with hJ
  · subst hJ
    simp
  · exact integral_complex_ofReal
theorem finsetMoment_update_of_notMem (μ : Measure Ω) [IsProbabilityMeasure μ]
    (y : Fin n → Ω → ℝ) (j : Fin n) (u : Ω → ℝ) {J : Finset (Fin n)} (hj : j ∉ J) :
    finsetMoment μ (Function.update y j u) J = finsetMoment μ y J := by
  rw [finsetMoment_eq_integral, finsetMoment_eq_integral]
  congr 2
  funext ω
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (ne_of_mem_of_not_mem hl hj)]
theorem finsetMoment_update_linComb (μ : Measure Ω) [IsProbabilityMeasure μ]
    (y : Fin n → Ω → ℝ) (y' : Ω → ℝ) (hy : ∀ i, IsBoundedRealRV (y i))
    (hy' : IsBoundedRealRV y') (j : Fin n) (a a' : ℝ) {J : Finset (Fin n)}
    (hj : j ∈ J) :
    finsetMoment μ (Function.update y j fun ω => a * y j ω + a' * y' ω) J =
      (a : ℂ) * finsetMoment μ y J + (a' : ℂ) * finsetMoment μ (Function.update y j y') J := by
  set p : Ω → ℝ := fun ω => ∏ l ∈ J.erase j, y l ω with hp
  have hpb : IsBoundedRealRV p := isBoundedRealRV_prod _ fun i _ => hy i
  have hsplit : ∀ (u : Ω → ℝ) (ω : Ω), ∏ l ∈ J, Function.update y j u l ω = u ω * p ω := by
    intro u ω
    rw [← Finset.mul_prod_erase J _ hj, Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have hsplit' : ∀ ω, ∏ l ∈ J, y l ω = y j ω * p ω := by
    intro ω
    rw [← Finset.mul_prod_erase J _ hj]
  have i1 : Integrable (fun ω => y j ω * p ω) μ :=
    integrable_of_isBoundedRealRV (isBoundedRealRV_mul (hy j) hpb) μ
  have i2 : Integrable (fun ω => y' ω * p ω) μ :=
    integrable_of_isBoundedRealRV (isBoundedRealRV_mul hy' hpb) μ
  simp only [finsetMoment_eq_integral, hsplit, hsplit']
  have hint : ∫ ω, (a * y j ω + a' * y' ω) * p ω ∂μ =
      a * ∫ ω, y j ω * p ω ∂μ + a' * ∫ ω, y' ω * p ω ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (i1.const_mul a) (i2.const_mul a')]
    congr 1
    funext ω
    ring
  rw [hint]
  push_cast
  rfl
theorem finsetMoment_comp_perm (μ : Measure Ω) [IsProbabilityMeasure μ] (y : Fin n → Ω → ℝ)
    (σ : Equiv.Perm (Fin n)) (J : Finset (Fin n)) :
    finsetMoment μ (fun i => y (σ i)) J = finsetMoment μ y (J.map σ.toEmbedding) := by
  rw [finsetMoment_eq_integral, finsetMoment_eq_integral]
  simp [Finset.prod_map]
end Moments
section Permutation
variable {n : ℕ}
def permPartition (σ : Equiv.Perm (Fin n)) (π : PartitionsFin n) : PartitionsFin n :=
  ⟨π.parts.image (Finset.map σ.toEmbedding),
    Finset.supIndep_iff_pairwiseDisjoint.2 (by
      intro A hA B hB hne
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hA)
      obtain ⟨K, hK, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hB)
      have hJK : J ≠ K := fun e => hne (by rw [e])
      exact (Finset.disjoint_map _).2 (π.disjoint hJ hK hJK)),
    by
      rw [Finset.sup_eq_biUnion]
      ext l
      simp only [Finset.mem_biUnion, Finset.mem_image, id, Finset.mem_univ, iff_true]
      obtain ⟨J, hJ, hl⟩ := π.exists_mem (Finset.mem_univ (σ.symm l))
      exact ⟨_, ⟨J, hJ, rfl⟩, Finset.mem_map.2 ⟨σ.symm l, hl, by simp⟩⟩,
    by
      intro h
      obtain ⟨J, hJ, hJ0⟩ := Finset.mem_image.1 h
      have hJe : J = ∅ := Finset.map_eq_empty.1 hJ0
      exact (π.nonempty_of_mem_parts hJ).ne_empty hJe⟩
theorem permPartition_parts (σ : Equiv.Perm (Fin n)) (π : PartitionsFin n) :
    (permPartition σ π).parts = π.parts.image (Finset.map σ.toEmbedding) := rfl
theorem permPartition_permPartition (σ τ : Equiv.Perm (Fin n)) (h : ∀ l, τ (σ l) = l)
    (π : PartitionsFin n) : permPartition τ (permPartition σ π) = π := by
  refine Finpartition.ext ?_
  rw [permPartition_parts, permPartition_parts, Finset.image_image]
  have hid : Finset.map τ.toEmbedding ∘ Finset.map σ.toEmbedding = id := by
    funext J
    ext l
    simp only [Function.comp, Finset.mem_map, Equiv.coe_toEmbedding, id]
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      rwa [h]
    · intro hl
      refine ⟨σ l, ⟨l, hl, rfl⟩, h l⟩
  rw [hid, Finset.image_id]
def permPartitionEquiv (σ : Equiv.Perm (Fin n)) : PartitionsFin n ≃ PartitionsFin n where
  toFun := permPartition σ
  invFun := permPartition σ.symm
  left_inv := permPartition_permPartition σ σ.symm fun l => by simp
  right_inv := permPartition_permPartition σ.symm σ fun l => by simp
theorem blockCount_permPartition (σ : Equiv.Perm (Fin n)) (π : PartitionsFin n) :
    blockCount (permPartition σ π) = blockCount π := by
  unfold blockCount
  rw [permPartition_parts, Finset.card_image_of_injective _ (Finset.map_injective _)]
end Permutation
section Formulas
variable {Ω : Type} [MeasurableSpace Ω]
theorem holomorphic_restrict (hHol : HolomorphicFacts.StandardFacts) {n : ℕ} (hn : 1 ≤ n)
    {U U' : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {F G : Coordinates.ComplexCoordinates n → ℂ}
    (hF : IsHolomorphicScalar U F) (hU' : IsOpen U') (hs : U' ⊆ U) (hG : EqOn G F U') :
    IsHolomorphicScalar U' G ∧
      ∀ J : Finset (Fin n), EqOn (partialOverFinset J G) (partialOverFinset J F) U' :=
  ((hHol n hn U hU).1 F hF).2.2.2.2.2.2.2 U' hU' hs G hG
theorem blockCount_pos {q : ℕ} (hq : 1 ≤ q) (π : PartitionsFin q) :
    0 < blockCount π := by
  obtain ⟨J, hJ, -⟩ := π.exists_mem (Finset.mem_univ (⟨0, hq⟩ : Fin q))
  exact Finset.card_pos.2 ⟨J, hJ⟩
theorem mixedCumulant_eq_sum_moments (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hChain : CompositeDerivative.PartitionChainRule)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 1 ≤ q) (x : Fin q → Ω → ℝ) (hx : ∀ i, IsBoundedRealRV (x i)) :
    mixedCumulant μ x = ∑ π : PartitionsFin q, (-1 : ℂ) ^ (blockCount π - 1) *
      ((blockCount π - 1).factorial : ℂ) * ∏ J ∈ π.parts, finsetMoment μ x J := by
  obtain ⟨hE, hL, -, -, -⟩ := hMGF Ω μ q x hq hx
  have hΓ : IsHolomorphicScalar (logDomain μ x) (tupleMomentGeneratingFunction μ x) :=
    (holomorphic_restrict hHol hq isOpen_univ hE.entire hL.isOpen (subset_univ _)
      (fun _ _ => rfl)).1
  have hW : IsOpen {w : ℂ | ‖w - 1‖ < 1} :=
    isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
  have hsub : {w : ℂ | ‖w - 1‖ < 1} ⊆ Complex.slitPlane := by
    intro w hw
    have hm := Complex.mem_slitPlane_of_norm_lt_one (z := w - 1) hw
    simpa using hm
  have hdiff : DifferentiableOn ℂ logPrincipal {w : ℂ | ‖w - 1‖ < 1} := fun w hw =>
    (Complex.hasDerivAt_log (hsub hw)).differentiableAt.differentiableWithinAt
  obtain ⟨-, -, hform⟩ := hChain q hq (logDomain μ x) {w : ℂ | ‖w - 1‖ < 1}
    (tupleMomentGeneratingFunction μ x) logPrincipal hL.isOpen hW (fun z hz => hz) hΓ
    (isHolomorphicVia_of_differentiableOn hW hdiff) Finset.univ
    ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  have h0 := hform 0 hL.zero_mem
  rw [hL.mixedCumulant_eq]
  refine (h0.trans ?_)
  refine Finset.sum_congr rfl fun π _ => ?_
  have hk : blockCount π = (blockCount π - 1) + 1 := by
    have hp := blockCount_pos hq π
    omega
  have hone : (1 : ℂ) ∈ Complex.slitPlane := by simp
  rw [hE.apply_zero]
  conv_lhs => rw [hk]
  rw [iteratedDeriv_succ_logPrincipal _ hone]
  simp only [one_pow, inv_one, mul_one]
  congr 1
  exact Finset.prod_congr rfl fun J _ => hE.partial_apply_zero J
theorem moment_eq_sum_mixedCumulants (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hChain : CompositeDerivative.PartitionChainRule)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 1 ≤ q) (x : Fin q → Ω → ℝ) (hx : ∀ i, IsBoundedRealRV (x i)) :
    (complexExpectation μ fun ω => ((∏ l, x l ω : ℝ) : ℂ)) =
      ∑ π : PartitionsFin q, ∏ J ∈ π.parts, finsetCumulant μ x J := by
  obtain ⟨hE, hL, -, hS, -⟩ := hMGF Ω μ q x hq hx
  have hdiff : DifferentiableOn ℂ Complex.exp univ := Complex.differentiable_exp.differentiableOn
  obtain ⟨-, -, hform⟩ := hChain q hq (logDomain μ x) univ (logMomentGeneratingFunction μ x)
    Complex.exp hL.isOpen isOpen_univ (mapsTo_univ _ _) hL.holomorphic
    (isHolomorphicVia_of_differentiableOn isOpen_univ hdiff) Finset.univ
    ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  have heq : EqOn (Complex.exp ∘ logMomentGeneratingFunction μ x)
      (tupleMomentGeneratingFunction μ x) (logDomain μ x) := fun z hz => hL.exp_log z hz
  have hr := (holomorphic_restrict hHol hq isOpen_univ hE.entire hL.isOpen (subset_univ _)
    heq).2 Finset.univ hL.zero_mem
  have hm := hE.partial_apply_zero Finset.univ
  have hne : (Finset.univ : Finset (Fin q)) ≠ ∅ :=
    Finset.Nonempty.ne_empty ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  rw [finsetMoment, if_neg hne] at hm
  rw [← hm, ← hr, hform 0 hL.zero_mem]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [iteratedDeriv_cexp_apply, hL.apply_zero, Complex.exp_zero, one_mul]
  refine Finset.prod_congr rfl fun J hJ => ?_
  exact (hS.finsetCumulant_eq J (π.nonempty_of_mem_parts hJ).ne_empty).symm
end Formulas
section Consequences
variable {Ω : Type} [MeasurableSpace Ω]
theorem mixedCumulant_im (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hChain : CompositeDerivative.PartitionChainRule)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 1 ≤ n) (y : Fin n → Ω → ℝ) (hy : ∀ i, IsBoundedRealRV (y i)) :
    (mixedCumulant μ y).im = 0 := by
  rw [mixedCumulant_eq_sum_moments hMGF hChain hHol μ hn y hy]
  have hreal : (∑ π : PartitionsFin n, (-1 : ℂ) ^ (blockCount π - 1) *
      ((blockCount π - 1).factorial : ℂ) * ∏ J ∈ π.parts, finsetMoment μ y J) =
      ((∑ π : PartitionsFin n, (-1 : ℝ) ^ (blockCount π - 1) *
      ((blockCount π - 1).factorial : ℝ) * ∏ J ∈ π.parts,
        ∫ ω, ∏ l ∈ J, y l ω ∂μ : ℝ) : ℂ) := by
    push_cast
    simp only [finsetMoment_eq_integral]
  rw [hreal]
  exact Complex.ofReal_im _
theorem mixedCumulant_comp_perm (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hChain : CompositeDerivative.PartitionChainRule)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 1 ≤ n) (y : Fin n → Ω → ℝ) (hy : ∀ i, IsBoundedRealRV (y i))
    (σ : Equiv.Perm (Fin n)) : mixedCumulant μ (fun i => y (σ i)) = mixedCumulant μ y := by
  rw [mixedCumulant_eq_sum_moments hMGF hChain hHol μ hn (fun i => y (σ i)) (fun i => hy _),
    mixedCumulant_eq_sum_moments hMGF hChain hHol μ hn y hy]
  refine Fintype.sum_equiv (permPartitionEquiv σ) _ _ fun π => ?_
  change _ = (-1 : ℂ) ^ (blockCount (permPartition σ π) - 1) *
      ((blockCount (permPartition σ π) - 1).factorial : ℂ) *
        ∏ J ∈ (permPartition σ π).parts, finsetMoment μ y J
  rw [blockCount_permPartition, permPartition_parts,
    Finset.prod_image fun _ _ _ _ h => Finset.map_injective _ h]
  simp only [finsetMoment_comp_perm]
theorem prod_finsetMoment_update_linComb (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (y : Fin n → Ω → ℝ) (y' : Ω → ℝ) (hy : ∀ i, IsBoundedRealRV (y i))
    (hy' : IsBoundedRealRV y') (j : Fin n) (a a' : ℝ) (π : PartitionsFin n) :
    ∏ J ∈ π.parts, finsetMoment μ (Function.update y j fun ω => a * y j ω + a' * y' ω) J =
      (a : ℂ) * ∏ J ∈ π.parts, finsetMoment μ y J +
        (a' : ℂ) * ∏ J ∈ π.parts, finsetMoment μ (Function.update y j y') J := by
  obtain ⟨B, hB, hjB⟩ := π.exists_mem (Finset.mem_univ j)
  have hother : ∀ J ∈ π.parts.erase B, j ∉ J := fun J hJ hjJ =>
    Finset.disjoint_left.1
      (π.disjoint (Finset.mem_of_mem_erase hJ) hB (Finset.ne_of_mem_erase hJ)) hjJ hjB
  rw [← Finset.mul_prod_erase π.parts
      (fun J => finsetMoment μ (Function.update y j fun ω => a * y j ω + a' * y' ω) J) hB,
    ← Finset.mul_prod_erase π.parts (fun J => finsetMoment μ y J) hB,
    ← Finset.mul_prod_erase π.parts (fun J => finsetMoment μ (Function.update y j y') J) hB,
    finsetMoment_update_linComb μ y y' hy hy' j a a' hjB]
  have e1 : ∏ J ∈ π.parts.erase B,
      finsetMoment μ (Function.update y j fun ω => a * y j ω + a' * y' ω) J =
      ∏ J ∈ π.parts.erase B, finsetMoment μ y J :=
    Finset.prod_congr rfl fun J hJ => finsetMoment_update_of_notMem μ y j _ (hother J hJ)
  have e2 : ∏ J ∈ π.parts.erase B, finsetMoment μ (Function.update y j y') J =
      ∏ J ∈ π.parts.erase B, finsetMoment μ y J :=
    Finset.prod_congr rfl fun J hJ => finsetMoment_update_of_notMem μ y j _ (hother J hJ)
  rw [e1, e2]
  ring
theorem isBoundedRealRV_update {n : ℕ} {y : Fin n → Ω → ℝ} (hy : ∀ i, IsBoundedRealRV (y i))
    (j : Fin n) {u : Ω → ℝ} (hu : IsBoundedRealRV u) (i : Fin n) :
    IsBoundedRealRV (Function.update y j u i) := by apply _root_.YangMills.Construction.SourcesAndGluing.BoundedCumulants.isBoundedRealRV_update <;> assumption
theorem mixedCumulant_update_linComb (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hChain : CompositeDerivative.PartitionChainRule)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 1 ≤ n) (y : Fin n → Ω → ℝ) (y' : Ω → ℝ)
    (hy : ∀ i, IsBoundedRealRV (y i)) (hy' : IsBoundedRealRV y')
    (j : Fin n) (a a' : ℝ) :
    mixedCumulant μ (Function.update y j fun ω => a * y j ω + a' * y' ω) =
      (a : ℂ) * mixedCumulant μ y + (a' : ℂ) * mixedCumulant μ (Function.update y j y') := by
  rw [mixedCumulant_eq_sum_moments hMGF hChain hHol μ hn _
      (isBoundedRealRV_update hy j (isBoundedRealRV_linComb (hy j) hy' a a')),
    mixedCumulant_eq_sum_moments hMGF hChain hHol μ hn y hy,
    mixedCumulant_eq_sum_moments hMGF hChain hHol μ hn _ (isBoundedRealRV_update hy j hy'),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [prod_finsetMoment_update_linComb μ y y' hy hy' j a a' π]
  ring
theorem parts_eq_of_fin_one (π : PartitionsFin 1) : π.parts = {Finset.univ} := by
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun K hK => ?_⟩
  · obtain ⟨J, hJ, h0⟩ := π.exists_mem (Finset.mem_univ (0 : Fin 1))
    have hJu : J = Finset.univ := by
      ext l
      simp [Subsingleton.elim l 0, h0]
    exact hJu ▸ hJ
  · obtain ⟨l, hl⟩ := π.nonempty_of_mem_parts hK
    ext m
    have hm : m = l := Subsingleton.elim m l
    subst hm
    exact ⟨fun _ => Finset.mem_univ _, fun _ => hl⟩
theorem mixedCumulant_fin_one (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hChain : CompositeDerivative.PartitionChainRule)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ) (hu : IsBoundedRealRV u) :
    mixedCumulant μ (fun _ : Fin 1 => u) = complexExpectation μ fun ω => (u ω : ℂ) := by
  rw [mixedCumulant_eq_sum_moments hMGF hChain hHol μ le_rfl _ (fun _ => hu)]
  have hsub : Subsingleton (PartitionsFin 1) :=
    ⟨fun a b => Finpartition.ext (by rw [parts_eq_of_fin_one, parts_eq_of_fin_one])⟩
  rw [Fintype.sum_subsingleton _ (⊥ : PartitionsFin 1)]
  simp only [blockCount, parts_eq_of_fin_one, Finset.card_singleton, Nat.sub_self, pow_zero,
    Nat.factorial_zero, Nat.cast_one, one_mul, Finset.prod_singleton]
  rw [finsetMoment_eq_integral]
  simp [complexExpectation, integral_complex_ofReal]
theorem mixedCumulant_of_eq_one (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hChain : CompositeDerivative.PartitionChainRule)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : n = 1) (y : Fin n → Ω → ℝ) (u : Ω → ℝ) (hu : IsBoundedRealRV u)
    (hyu : ∀ i, y i = u) : mixedCumulant μ y = complexExpectation μ fun ω => (u ω : ℂ) := by
  subst hn
  have hyc : y = fun _ => u := funext hyu
  subst hyc
  exact mixedCumulant_fin_one hMGF hChain hHol μ u hu
theorem finsetCumulant_singleton (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hChain : CompositeDerivative.PartitionChainRule)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q : ℕ} (x : Fin q → Ω → ℝ) (hx : ∀ i, IsBoundedRealRV (x i)) (l : Fin q) :
    finsetCumulant μ x {l} = complexExpectation μ fun ω => (x l ω : ℂ) := by
  refine mixedCumulant_of_eq_one hMGF hChain hHol μ (Finset.card_singleton l)
    (restrictTuple x {l}) (x l) (hx l) fun a => ?_
  have h := Finset.orderEmbOfFin_mem ({l} : Finset (Fin q)) rfl a
  rw [Finset.mem_singleton] at h
  change x _ = x l
  rw [h]
end Consequences
section Constants
variable {Ω : Type} [MeasurableSpace Ω]
theorem partialOverFinset_univ_eq (hHol : HolomorphicFacts.StandardFacts) {n : ℕ}
    (hn : 1 ≤ n) {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {F : Coordinates.ComplexCoordinates n → ℂ}
    (hF : IsHolomorphicScalar U F) {j s : Fin n} (hjs : j ≠ s) :
    EqOn (partialOverFinset Finset.univ F)
      (partialOverFinset ((Finset.univ.erase j).erase s) (partialDeriv s (partialDeriv j F)))
      U := by
  have hnd : (((Finset.univ.erase j).erase s).sort ++ [s, j]).Nodup := by
    refine List.Nodup.append (Finset.sort_nodup _ _) ?_ ?_
    · simp [hjs.symm]
    · intro a ha hb
      simp only [Finset.mem_sort, Finset.mem_erase, Finset.mem_univ, and_true] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact ha.1 rfl
      · exact ha.2 rfl
  have hperm : (((Finset.univ.erase j).erase s).sort ++ [s, j]).Perm
      (Finset.univ : Finset (Fin n)).sort := by
    refine (List.perm_ext_iff_of_nodup hnd (Finset.sort_nodup _ _)).2 fun a => ?_
    simp only [List.mem_append, Finset.mem_sort, Finset.mem_erase, Finset.mem_univ, and_true,
      List.mem_cons, List.not_mem_nil, or_false, iff_true]
    tauto
  have h := (((hHol n hn U hU).1 F hF).2.2.2.2.1 Finset.univ _ hperm).2
  intro z hz
  rw [← h hz]
  simp only [iteratedPartials, partialOverFinset, List.foldr_append, List.foldr_cons,
    List.foldr_nil]
theorem mixedCumulant_shiftTuple (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) (y : Fin n → Ω → ℝ) (hy : ∀ i, IsBoundedRealRV (y i))
    (c : Fin n → ℝ) : mixedCumulant μ (shiftTuple y c) = mixedCumulant μ y := by
  have h1 : 1 ≤ n := by omega
  obtain ⟨-, hLy, -, -, hShift⟩ := hMGF Ω μ n y h1 hy
  have hSh := hShift c
  obtain ⟨-, hLs, -, -, -⟩ := hMGF Ω μ n (shiftTuple y c) h1
    (fun i => isBoundedRealRV_add_const (hy i) (c i))
  have hU := hSh.isOpen
  have h0 := hSh.zero_mem
  set U := logDomain μ y ∩ logDomain μ (shiftTuple y c) with hUdef
  set Ly := logMomentGeneratingFunction μ y with hLydef
  set Ls := logMomentGeneratingFunction μ (shiftTuple y c) with hLsdef
  let j : Fin n := ⟨0, by omega⟩
  let s : Fin n := ⟨1, by omega⟩
  have hjs : j ≠ s := by simp [j, s, Fin.ext_iff]
  have hHy : IsHolomorphicScalar U Ly :=
    (holomorphic_restrict hHol h1 hLy.isOpen hLy.holomorphic hU inter_subset_left
      fun _ _ => rfl).1
  have hHs : IsHolomorphicScalar U Ls :=
    (holomorphic_restrict hHol h1 hLs.isOpen hLs.holomorphic hU inter_subset_right
      fun _ _ => rfl).1
  have hDy : IsHolomorphicScalar U (partialDeriv j Ly) := (((hHol n h1 U hU).1 Ly hHy).1 j).2
  have sp := (hHol n h1 U hU).2.1
  have hlin := sp.2.2.2.2.1 (fun _ => (c j : ℂ)) (partialDeriv j Ly) (sp.1 _).1 hDy 1 1
  have hDC : EqOn (partialDeriv j Ls)
      (fun z => 1 * (c j : ℂ) + 1 * partialDeriv j Ly z) U := fun z hz => by
    simpa using hSh.partialDeriv_shift j z hz
  have hs1 : EqOn (partialDeriv s (partialDeriv j Ls))
      (partialDeriv s fun z => 1 * (c j : ℂ) + 1 * partialDeriv j Ly z) U := by
    have hr := (holomorphic_restrict hHol h1 hU hlin.1 hU subset_rfl hDC).2 {s}
    simpa [partialOverFinset, iteratedPartials] using hr
  have hs2 : EqOn (partialDeriv s fun z => 1 * (c j : ℂ) + 1 * partialDeriv j Ly z)
      (partialDeriv s (partialDeriv j Ly)) U := fun z hz => by
    have e := (hlin.2.2 s).1 hz
    have e0 := ((sp.1 (c j : ℂ)).2 s) hz
    simp only at e e0
    rw [e, e0]
    ring
  have hHyy : IsHolomorphicScalar U (partialDeriv s (partialDeriv j Ly)) :=
    (((hHol n h1 U hU).1 _ hDy).1 s).2
  have hfin := (holomorphic_restrict hHol h1 hU hHyy hU subset_rfl (hs1.trans hs2)).2
    ((Finset.univ.erase j).erase s)
  rw [hLs.mixedCumulant_eq, hLy.mixedCumulant_eq]
  exact ((partialOverFinset_univ_eq hHol h1 hU hHs hjs h0).trans (hfin h0)).trans
    (partialOverFinset_univ_eq hHol h1 hU hHy hjs h0).symm
theorem finsetCumulant_shiftTuple (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q : ℕ} (x : Fin q → Ω → ℝ) (hx : ∀ i, IsBoundedRealRV (x i))
    (J : Finset (Fin q)) (c : Fin q → ℝ) (hJ : 2 ≤ J.card) :
    finsetCumulant μ (shiftTuple x c) J = finsetCumulant μ x J :=
  mixedCumulant_shiftTuple hMGF hHol μ hJ (restrictTuple x J) (fun _ => hx _)
    fun a => c (J.orderEmbOfFin rfl a)
end Constants
section Centred
variable {Ω : Type} [MeasurableSpace Ω]
theorem centredMoment_eq_sum_mixedCumulants (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hChain : CompositeDerivative.PartitionChainRule)
    (hHol : HolomorphicFacts.StandardFacts) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 1 ≤ q) (x : Fin q → Ω → ℝ) (hx : ∀ i, IsBoundedRealRV (x i)) :
    (complexExpectation μ fun ω =>
        ∏ l, ((x l ω : ℂ) - complexExpectation μ fun ω' => (x l ω' : ℂ))) =
      ∑ π ∈ singletonFree q, ∏ J ∈ π.parts, finsetCumulant μ x J := by
  set c : Fin q → ℝ := fun l => -∫ ω, x l ω ∂μ with hc
  have hb : ∀ i, IsBoundedRealRV (shiftTuple x c i) :=
    fun i => isBoundedRealRV_add_const (hx i) (c i)
  have hE : ∀ l, (complexExpectation μ fun ω' => (x l ω' : ℂ)) = ((∫ ω, x l ω ∂μ : ℝ) : ℂ) :=
    fun l => integral_complex_ofReal
  have hfun : (fun ω => ∏ l, ((x l ω : ℂ) - complexExpectation μ fun ω' => (x l ω' : ℂ))) =
      fun ω => ((∏ l, shiftTuple x c l ω : ℝ) : ℂ) := by
    funext ω
    push_cast
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hE]
    simp [shiftTuple, hc, sub_eq_add_neg]
  rw [hfun, moment_eq_sum_mixedCumulants hMGF hChain hHol μ hq _ hb, singletonFree]
  have hzero : ∀ l, finsetCumulant μ (shiftTuple x c) {l} = 0 := by
    intro l
    rw [finsetCumulant_singleton hMGF hChain hHol μ _ hb l]
    have hi : ∫ ω, shiftTuple x c l ω ∂μ = 0 := by
      simp only [shiftTuple]
      rw [integral_add (integrable_of_isBoundedRealRV (hx l) μ) (integrable_const _)]
      simp [hc]
    have hce : (complexExpectation μ fun ω => (shiftTuple x c l ω : ℂ)) =
        ((∫ ω, shiftTuple x c l ω ∂μ : ℝ) : ℂ) := integral_complex_ofReal
    rw [hce, hi]
    simp
  rw [← Finset.sum_filter_of_ne (s := Finset.univ)
    (p := fun π : PartitionsFin q => ∀ J ∈ π.parts, J.card ≠ 1)]
  · refine Finset.sum_congr rfl fun π hπ => Finset.prod_congr rfl fun J hJ => ?_
    have h1 := (Finset.mem_filter.1 hπ).2 J hJ
    have h2 : 0 < J.card := Finset.card_pos.2 (π.nonempty_of_mem_parts hJ)
    exact finsetCumulant_shiftTuple hMGF hHol μ x hx J c (by omega)
  · intro π _ hne J hJ h1
    obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h1
    exact hne (Finset.prod_eq_zero hJ (hzero l))
theorem parts_eq_of_fin_zero (π : PartitionsFin 0) : π.parts = ∅ :=
  parts_eq_empty_of_empty π
theorem sum_partitionsFin_zero (f : PartitionsFin 0 → ℂ) (h : ∀ π, f π = 1) :
    ∑ π, f π = 1 := by
  have hsub : Subsingleton (PartitionsFin 0) :=
    ⟨fun a b => Finpartition.ext (by rw [parts_eq_of_fin_zero, parts_eq_of_fin_zero])⟩
  rw [Fintype.sum_subsingleton _ (⊥ : PartitionsFin 0), h]
end Centred
theorem cumulantMomentRelations (hMGF : TupleLogMGF.TupleMGFAndLogTheorem)
    (hChain : CompositeDerivative.PartitionChainRule)
    (hHol : HolomorphicFacts.StandardFacts) :
    CumulantMomentRelations := by
  intro Ω _ μ _ q x hx
  refine ⟨?_, finsetCumulant_singleton hMGF hChain hHol μ x hx,
    fun J c hJ => finsetCumulant_shiftTuple hMGF hHol μ x hx J c hJ,
    fun n y c hn hy => mixedCumulant_shiftTuple hMGF hHol μ hn y hy c, ?_, ?_, fun hq =>
      mixedCumulant_eq_sum_moments hMGF hChain hHol μ hq x hx⟩
  · intro n y y' hn hy hy'
    exact ⟨mixedCumulant_im hMGF hChain hHol μ hn y hy,
      mixedCumulant_comp_perm hMGF hChain hHol μ hn y hy,
      fun j a a' => mixedCumulant_update_linComb hMGF hChain hHol μ hn y y' hy hy' j a a'⟩
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · rw [sum_partitionsFin_zero _ fun π => by rw [parts_eq_of_fin_zero, Finset.prod_empty]]
      simp [complexExpectation]
    · exact moment_eq_sum_mixedCumulants hMGF hChain hHol μ hq x hx
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · have hw : singletonFree 0 = Finset.univ :=
        Finset.eq_univ_iff_forall.2 mem_singletonFree_zero
      rw [hw, sum_partitionsFin_zero _ fun π => by rw [parts_eq_of_fin_zero, Finset.prod_empty]]
      simp [complexExpectation]
    · exact centredMoment_eq_sum_mixedCumulants hMGF hChain hHol μ hq x hx
end YangMills.Construction.Cumulants.MomentCumulantFormulas
