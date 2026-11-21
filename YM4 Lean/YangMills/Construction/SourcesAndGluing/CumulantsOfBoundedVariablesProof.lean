import YangMills.Construction.InfiniteLattice.AllLatticeIsometriesAndTheMeanOfThePlaquetteFunctionProof
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentativesProof
import YangMills.Construction.ReflectionPositivity.SpaceOfConfigurationsAndPlaquetteEnergiesAtOneCutoff
import YangMills.Construction.SourcesAndGluing.CumulantsOfBoundedVariables
import YangMills.Construction.SourcesAndGluing.GeneratingFunctionOfBoundedVariables
import YangMills.Construction.SourcesAndGluing.MomentCumulantFormula
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.BoundedCumulants
open YangMills.Construction.Probability
section Products
variable {Ω : Type} [MeasurableSpace Ω]
theorem isBoundedRealRV_mul {x y : Ω → ℝ} (hx : IsBoundedRealRV x)
    (hy : IsBoundedRealRV y) : IsBoundedRealRV fun ω => x ω * y ω := by
  obtain ⟨C, hC⟩ := hx.bounded
  obtain ⟨C', hC'⟩ := hy.bounded
  refine ⟨hx.measurable.mul hy.measurable, C * C', fun ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC ω) (hC' ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))
theorem isBoundedRealRV_prod {n : ℕ} {X : Fin n → Ω → ℝ} (hX : ∀ i, IsBoundedRealRV (X i))
    (J : Finset (Fin n)) : IsBoundedRealRV fun ω => ∏ p ∈ J, X p ω := by
  induction J using Finset.induction_on with
  | empty => exact ⟨by simp, 1, fun ω => by simp⟩
  | insert a s ha ih =>
    have h := isBoundedRealRV_mul (hX a) ih
    have e : (fun ω => ∏ p ∈ insert a s, X p ω) = fun ω => X a ω * ∏ p ∈ s, X p ω := by
      funext ω
      exact Finset.prod_insert ha
    rw [e]
    exact h
theorem integrable_of_isBoundedRealRV (μ : Measure Ω) [IsProbabilityMeasure μ] {x : Ω → ℝ}
    (hx : IsBoundedRealRV x) : Integrable x μ := by
  obtain ⟨C, hC⟩ := hx.bounded
  exact Integrable.of_bound hx.measurable.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by simpa using hC ω)
end Products
section Cumulant
variable {Ω : Type} [MeasurableSpace Ω]
theorem cumulant_eq_sum_partitions (hΓ : BoundedMGF.Statement)
    (hM : MomentCumulant.Claim) (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (hn : 1 ≤ n) {X : Fin n → Ω → ℝ} (hX : ∀ i, IsBoundedRealRV (X i)) :
    cumulant μ X = ∑ π : IndexPartition n,
      (-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
        ∏ J ∈ π.parts, ((∫ ω, ∏ p ∈ J, X p ω ∂μ : ℝ) : ℂ) := by
  choose C hC using fun i => (hX i).bounded
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hC₀ : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hb : ∀ p ω, |X p ω| ≤ ∑ i, |C i| := fun p ω =>
    ((hC p ω).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p))
  obtain ⟨hser, hpart, -⟩ :=
    (hΓ Ω μ).1 (Fin n) X (∑ i, |C i|) (fun i => (hX i).measurable) hC₀ hb
  have h := (hM n hn).1 Set.univ (famMGF μ X) isOpen_univ (Set.mem_univ _)
    hser.entire hser.value_at_zero
  rw [cumulant, ← famMGF_eq_momentGeneratingFunction, h]
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun J _ => hpart J
theorem integral_prod_update_of_mem (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    {v : Fin n → Ω → ℝ} (hv : ∀ j, IsBoundedRealRV (v j)) {i : Fin n}
    {x y : Ω → ℝ} (hx : IsBoundedRealRV x) (hy : IsBoundedRealRV y)
    (s t : ℝ) {J : Finset (Fin n)} (hi : i ∈ J) :
    ∫ ω, ∏ p ∈ J, Function.update v i (s • x + t • y) p ω ∂μ =
      s * (∫ ω, ∏ p ∈ J, Function.update v i x p ω ∂μ) +
        t * ∫ ω, ∏ p ∈ J, Function.update v i y p ω ∂μ := by
  have e : ∀ (z : Ω → ℝ) (ω : Ω), ∏ p ∈ J, Function.update v i z p ω =
      z ω * ∏ p ∈ J.erase i, v p ω := by
    intro z ω
    rw [← Finset.mul_prod_erase J _ hi, Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hp)]
  simp only [e]
  have hR := isBoundedRealRV_prod hv (J.erase i)
  have ix := integrable_of_isBoundedRealRV μ (isBoundedRealRV_mul hx hR)
  have iy := integrable_of_isBoundedRealRV μ (isBoundedRealRV_mul hy hR)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (ix.const_mul s) (iy.const_mul t)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
omit [MeasurableSpace Ω] in
theorem prod_update_of_notMem {n : ℕ} (v : Fin n → Ω → ℝ) {i : Fin n} (z : Ω → ℝ) (ω : Ω)
    {J : Finset (Fin n)} (hi : i ∉ J) :
    ∏ p ∈ J, Function.update v i z p ω = ∏ p ∈ J, v p ω := by
  refine Finset.prod_congr rfl fun p hp => ?_
  have h : p ≠ i := fun h => hi (h ▸ hp)
  rw [Function.update_of_ne h]
theorem prod_moments_update (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    {v : Fin n → Ω → ℝ} (hv : ∀ j, IsBoundedRealRV (v j)) {i : Fin n}
    {x y : Ω → ℝ} (hx : IsBoundedRealRV x) (hy : IsBoundedRealRV y)
    (s t : ℝ) (π : IndexPartition n) :
    ∏ J ∈ π.parts, ((∫ ω, ∏ p ∈ J, Function.update v i (s • x + t • y) p ω ∂μ : ℝ) : ℂ) =
      (s : ℂ) * (∏ J ∈ π.parts, ((∫ ω, ∏ p ∈ J, Function.update v i x p ω ∂μ : ℝ) : ℂ)) +
        (t : ℂ) * ∏ J ∈ π.parts, ((∫ ω, ∏ p ∈ J, Function.update v i y p ω ∂μ : ℝ) : ℂ) := by
  have hmem : π.part i ∈ π.parts := π.part_mem.2 (Finset.mem_univ i)
  have hi : i ∈ π.part i := π.mem_part (Finset.mem_univ i)
  have hoff : ∀ J ∈ π.parts.erase (π.part i), i ∉ J := by
    intro J hJ hiJ
    exact Finset.ne_of_mem_erase hJ (π.eq_of_mem_parts (Finset.mem_of_mem_erase hJ) hmem hiJ hi)
  have hrest : ∀ z : Ω → ℝ,
      ∏ J ∈ π.parts.erase (π.part i), ((∫ ω, ∏ p ∈ J, Function.update v i z p ω ∂μ : ℝ) : ℂ) =
        ∏ J ∈ π.parts.erase (π.part i), ((∫ ω, ∏ p ∈ J, v p ω ∂μ : ℝ) : ℂ) := by
    intro z
    refine Finset.prod_congr rfl fun J hJ => ?_
    simp only [prod_update_of_notMem v z _ (hoff J hJ)]
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
    ← Finset.mul_prod_erase _ _ hmem, hrest, hrest, hrest,
    integral_prod_update_of_mem μ hv hx hy s t hi]
  push_cast
  ring
end Cumulant
theorem isBoundedRealRV_update {Ω : Type} [MeasurableSpace Ω] {n : ℕ} {v : Fin n → Ω → ℝ}
    (hv : ∀ j, IsBoundedRealRV (v j)) (i : Fin n) {z : Ω → ℝ}
    (hz : IsBoundedRealRV z) (j : Fin n) :
    IsBoundedRealRV (Function.update v i z j) := by
  by_cases h : j = i
  · subst h
    simpa using hz
  · simpa [Function.update_of_ne h] using hv j
theorem multilinear (hΓ : BoundedMGF.Statement)
    (hM : MomentCumulant.Claim) : Multilinear := by
  intro Ω _ μ _ n hn v hv i x hx y hy s t
  have hv' : ∀ j, IsBoundedRealRV (v j) := hv
  have hx' : IsBoundedRealRV x := hx
  have hy' : IsBoundedRealRV y := hy
  have hz : IsBoundedRealRV (s • x + t • y) :=
    (boundedRVSubspace Ω).add_mem ((boundedRVSubspace Ω).smul_mem s hx)
      ((boundedRVSubspace Ω).smul_mem t hy)
  show cumulant μ (Function.update v i (s • x + t • y)) =
    s • cumulant μ (Function.update v i x) + t • cumulant μ (Function.update v i y)
  rw [cumulant_eq_sum_partitions hΓ hM μ hn (isBoundedRealRV_update hv' i hz),
    cumulant_eq_sum_partitions hΓ hM μ hn (isBoundedRealRV_update hv' i hx'),
    cumulant_eq_sum_partitions hΓ hM μ hn (isBoundedRealRV_update hv' i hy'),
    Complex.real_smul, Complex.real_smul, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [prod_moments_update μ hv' hx' hy' s t π]
  ring
theorem factorialBound (hΓ : BoundedMGF.Statement)
    (hM : MomentCumulant.Claim) : FactorialBound := by
  intro Ω _ μ n X b hX hb hXb
  have := hX.isProbabilityMeasure
  have hn := hX.one_le
  have hcount := (hM n hn).2.1
  have hmoment : ∀ J : Finset (Fin n),
      ‖((∫ ω, ∏ p ∈ J, X p ω ∂μ : ℝ) : ℂ)‖ ≤ ∏ p ∈ J, b p := by
    intro J
    rw [Complex.norm_real]
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => ∏ p ∈ J, X p ω)
      (C := ∏ p ∈ J, b p) (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Finset.abs_prod]
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p _ => hXb p ω)
    simpa using h
  have hblocks : ∀ π : IndexPartition n, ∏ J ∈ π.parts, ∏ p ∈ J, b p = ∏ i, b i := by
    intro π
    calc ∏ J ∈ π.parts, ∏ p ∈ J, b p = ∏ p ∈ π.parts.biUnion id, b p :=
          (Finset.prod_biUnion π.disjoint).symm
      _ = ∏ i, b i := by rw [π.biUnion_parts]
  have hB : 0 ≤ ∏ i, b i := Finset.prod_nonneg fun i _ => hb i
  have hterm : ∀ π : IndexPartition n,
      ‖(-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
          ∏ J ∈ π.parts, ((∫ ω, ∏ p ∈ J, X p ω ∂μ : ℝ) : ℂ)‖ ≤
        (((blockCount π - 1).factorial * ∏ J ∈ π.parts, J.card.factorial : ℕ) : ℝ) *
          ∏ i, b i := by
    intro π
    have hprod : ‖∏ J ∈ π.parts, ((∫ ω, ∏ p ∈ J, X p ω ∂μ : ℝ) : ℂ)‖ ≤ ∏ i, b i := by
      rw [norm_prod, ← hblocks π]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun J _ => hmoment J
    have hone : (1 : ℝ) ≤ ((∏ J ∈ π.parts, J.card.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2
        (Finset.prod_ne_zero_iff.2 fun J _ => Nat.factorial_ne_zero _)
    have hfac : (0 : ℝ) ≤ ((blockCount π - 1).factorial : ℝ) := Nat.cast_nonneg _
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast,
      Nat.cast_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hfac
    calc _ ≤ ∏ i, b i := hprod
      _ = 1 * ∏ i, b i := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hone hB
  have hX' : ∀ i, IsBoundedRealRV (X i) := hX.isBounded
  rw [cumulant_eq_sum_partitions hΓ hM μ hn hX']
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun π _ => hterm π).trans (le_of_eq ?_))
  rw [← Finset.sum_mul, ← Nat.cast_sum, hcount, Nat.cast_mul, Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  ring
theorem isMultilinearOnSubspace_comp {V Ω : Type*} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace Ω] (A : Submodule ℝ V) {O : V → Ω → ℝ}
    (hmem : ∀ f ∈ A, O f ∈ boundedRVSubspace Ω) (hlin : IsLinearOnSubspace A O) {n : ℕ}
    {G : (Fin n → Ω → ℝ) → ℂ} (hG : IsMultilinearOnSubspace (boundedRVSubspace Ω) G) :
    IsMultilinearOnSubspace A fun f : Fin n → V => G fun i => O (f i) := by
  intro v hv i x hx y hy s t
  have e : ∀ z, (fun j => O (Function.update v i z j)) =
      Function.update (fun j => O (v j)) i (O z) := by
    intro z
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
  show G _ = s • G _ + t • G _
  rw [e, e, e, hlin x hx y hy s t]
  exact hG (fun j => O (v j)) (fun j => hmem _ (hv j)) i (O x) (hmem x hx) (O y) (hmem y hy) s t
section Infinite
open YangMills.Construction.InfiniteLattice YangMills.Construction.Matrices
variable {a : ℝ}
theorem abs_re_fullTrace_le (V : ComplexMatrix2.specialUnitary) :
    |(ComplexMatrix2.fullTrace (V : ComplexMatrix2)).re| ≤ 2 := by
  have hu := Matrix.specialUnitaryGroup_le_unitaryGroup V.2
  have h₀ := entry_norm_bound_of_unitary hu 0 0
  have h₁ := entry_norm_bound_of_unitary hu 1 1
  have h₂ := Complex.abs_re_le_norm ((V : ComplexMatrix2) 0 0)
  have h₃ := Complex.abs_re_le_norm ((V : ComplexMatrix2) 1 1)
  rw [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Complex.add_re]
  calc |((V : ComplexMatrix2) 0 0).re + ((V : ComplexMatrix2) 1 1).re|
      ≤ |((V : ComplexMatrix2) 0 0).re| + |((V : ComplexMatrix2) 1 1).re| := abs_add_le _ _
    _ ≤ 2 := by linarith
theorem abs_faceEnergy_le (U : Link a → ComplexMatrix2.specialUnitary) (p : ElementaryPlaquette a) :
    |faceEnergy U p| ≤ 2 := by
  have h := abs_le.mp (abs_re_fullTrace_le (faceHolonomy U p))
  rw [faceEnergy, abs_le]
  constructor <;> linarith [h.1, h.2]
theorem continuous_faceEnergy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceEnergy U p := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.continuous_faceEnergy <;> assumption
theorem finite_faces_center_mem (ha : 0 < a) {K : Set AmbientSpace} (hK : Bornology.IsBounded K) :
    {p : ElementaryPlaquette a | p.center ∈ K}.Finite := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.finite_center_mem_of_isBounded <;> assumption
theorem smearedEnergy_eq_sum {f : AmbientSpace → ℝ} {F : Finset (ElementaryPlaquette a)}
    (hF : ∀ p : ElementaryPlaquette a, p.center ∈ tsupport f → p ∈ F) (U : GaugeField a) :
    smearedEnergy f U = ∑ p ∈ F, faceEnergy U p * f p.center := by
  rw [smearedEnergy, finsum_eq_sum_of_support_subset (s := F)]
  · simp only [smul_eq_mul]
  · intro p hp
    have h : f p.center ≠ 0 := fun h => hp (by simp [h])
    exact hF p (subset_tsupport _ h)
theorem isBoundedRealRV_smearedEnergy (ha : 0 < a) {f : AmbientSpace → ℝ}
    (hf : IsBoundedBorelCompactlySupported f) :
    IsBoundedRealRV fun U : GaugeField a => smearedEnergy f U := by
  obtain ⟨-, ⟨C, hC⟩, hc⟩ := hf
  have hfin := finite_faces_center_mem (a := a) ha hc.isCompact.isBounded
  have hF : ∀ p : ElementaryPlaquette a, p.center ∈ tsupport f → p ∈ hfin.toFinset :=
    fun p hp => hfin.mem_toFinset.2 hp
  have e : (fun U : GaugeField a => smearedEnergy f U) =
      fun U : GaugeField a => ∑ p ∈ hfin.toFinset, faceEnergy U p * f p.center :=
    funext (smearedEnergy_eq_sum hF)
  rw [e]
  refine ⟨(continuous_finsetSum _ fun p _ =>
    (continuous_faceEnergy p).mul continuous_const).measurable,
    ∑ _p ∈ hfin.toFinset, 2 * C, fun U => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  have hp := hC p.center
  rw [Real.norm_eq_abs] at hp
  exact mul_le_mul (abs_faceEnergy_le _ p) hp (abs_nonneg _) (by norm_num)
theorem smearedEnergy_linear (ha : 0 < a) :
    IsLinearOnSubspace compactBorelSubspace
      (fun (f : AmbientSpace → ℝ) (U : GaugeField a) => smearedEnergy f U) := by
  intro x hx y hy s t
  have hz : s • x + t • y ∈ compactBorelSubspace :=
    compactBorelSubspace.add_mem (compactBorelSubspace.smul_mem s hx)
      (compactBorelSubspace.smul_mem t hy)
  have hx' : IsBoundedBorelCompactlySupported x := hx
  have hy' : IsBoundedBorelCompactlySupported y := hy
  have hz' : IsBoundedBorelCompactlySupported (s • x + t • y) := hz
  have hfin := finite_faces_center_mem (a := a) ha
    ((hx'.2.2.isCompact.union hy'.2.2.isCompact).union hz'.2.2.isCompact).isBounded
  funext U
  have hFx : ∀ p : ElementaryPlaquette a, p.center ∈ tsupport x → p ∈ hfin.toFinset :=
    fun p hp => hfin.mem_toFinset.2 (Or.inl (Or.inl hp))
  have hFy : ∀ p : ElementaryPlaquette a, p.center ∈ tsupport y → p ∈ hfin.toFinset :=
    fun p hp => hfin.mem_toFinset.2 (Or.inl (Or.inr hp))
  have hFz : ∀ p : ElementaryPlaquette a, p.center ∈ tsupport (s • x + t • y) →
      p ∈ hfin.toFinset :=
    fun p hp => hfin.mem_toFinset.2 (Or.inr hp)
  show smearedEnergy (s • x + t • y) U = s * smearedEnergy x U + t * smearedEnergy y U
  rw [smearedEnergy_eq_sum hFz, smearedEnergy_eq_sum hFx, smearedEnergy_eq_sum hFy,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
end Infinite
theorem mesh_pos (D : GluingSetup) : 0 < D.mesh := by
  have h := D.isAdmissible.2
  exact zpow_pos (by exact_mod_cast (by omega : 0 < D.L)) _
theorem periodic_facts
    (h : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
    (D : GluingSetup) : Finite (PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)) ∧
      (∀ f : D.Torus → ℝ, IsBoundedRealRV (D.smearedOnGaugeFields f)) ∧
      IsProbabilityMeasure D.wilsonOnGaugeFields := by
  obtain ⟨⟨-, -, hfin, -, -, -, htop, -, -, -⟩, -, -, hobs, -, -, -, -, -, -, -, -, -, hprob⟩ :=
    h ⟨D.toStandingParameters, D.β, D.beta_pos, 0⟩
  refine ⟨hfin, fun f => ?_, hprob⟩
  obtain ⟨hc, C, hC⟩ := hobs f
  unfold ReflectionPositivity.CutoffMirrors.MirrorData.ContinuousForProduct at hc
  rw [htop] at hc
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hc' : Continuous (D.smearedOnGaugeFields f) := hc
  exact ⟨hc'.measurable, C, fun U => (Real.norm_eq_abs _).symm.le.trans (hC U)⟩
theorem smearedOnGaugeFields_linear (D : GluingSetup)
    (hfin : Finite (PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ))) :
    IsLinearOnSubspace (boundedFunSubspace D.Torus) D.smearedOnGaugeFields := by
  intro x _ y _ s t
  funext U
  have := Fintype.ofFinite (PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ))
  show PeriodicLattice.smearedObservable (s • x + t • y) U.1 =
    s * PeriodicLattice.smearedObservable x U.1 + t * PeriodicLattice.smearedObservable y U.1
  simp only [PeriodicLattice.smearedObservable, finsum_eq_sum_of_fintype, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem smearedLinear
    (h : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
    (hlin : Multilinear) : SmearedLinear := by
  intro D
  obtain ⟨hfin, hbdd, hprob⟩ := periodic_facts h D
  have hlinT := smearedOnGaugeFields_linear D hfin
  have ha := mesh_pos D
  have hlinI := smearedEnergy_linear ha
  refine ⟨fun f _ => hbdd f, fun f hf => isBoundedRealRV_smearedEnergy ha hf, hlinT, hlinI,
    fun n hn => ?_, fun ν hν n hn => ?_⟩
  · exact isMultilinearOnSubspace_comp _ (fun f _ => hbdd f) hlinT
      (hlin D.gaugeFields D.wilsonOnGaugeFields n hn)
  · have := hν.1
    exact isMultilinearOnSubspace_comp _ (fun f hf => isBoundedRealRV_smearedEnergy ha hf) hlinI
      (hlin D.GridField ν n hn)
theorem corollary (h₁ : BoundedMGF.Statement) (h₂ : MomentCumulant.Claim)
    (h₃ : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement) : Corollary :=
  ⟨multilinear h₁ h₂, factorialBound h₁ h₂, smearedLinear h₃ (multilinear h₁ h₂)⟩
end YangMills.Construction.SourcesAndGluing.BoundedCumulants
end
