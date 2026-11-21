import YangMills.Construction.Matrices.PauliMatricesAreAnOrthonormalBasisProof
import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Matrices.UnitaryLogConjugation
import YangMills.Construction.OneLoop.PauliMatrixComputations
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
open YangMills.Construction.Matrices YangMills.Construction.Coordinates
noncomputable section
namespace YangMills.Construction.Tower.LeftChartFields
theorem leftExpMul_hasDerivAt_complex (X V : ComplexMatrix2) :
    HasDerivAt (fun t : ℂ => leftExpMul (t • X) V) (Complex.I • X * V) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • X) (0 : ℂ)
  have h2 := h.mul_const V
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [leftExpMul, ComplexMatrix2.matExp, smul_comm Complex.I t X]
theorem leftExpMul_hasDerivAt_real (X V : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => leftExpMul ((t : ℂ) • X) V) (Complex.I • X * V) 0 := by
  have h : HasDerivAt (fun t : ℂ => leftExpMul (t • X) V) (Complex.I • X * V)
      (Complex.ofRealCLM (0 : ℝ)) := by
    simpa using leftExpMul_hasDerivAt_complex X V
  have h2 := HasDerivAt.scomp (0 : ℝ) h Complex.ofRealCLM.hasDerivAt
  simpa [Function.comp_def] using h2
theorem leftExpMul_mem_compact (hil : ComplexMatrix2.UnitaryLogConjugationProperties)
    {X V : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (hV : V ∈ PeriodicLattice.compactGaugeGroup) :
    leftExpMul X V ∈ PeriodicLattice.compactGaugeGroup :=
  ComplexMatrix2.specialUnitary.mul_mem (hil.1 X hX).2.2 hV
theorem leftExpMul_mem_complexGroup (hel : ComplexMatrix2.ExpLogEstimates)
    {X V : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hV : V ∈ PeriodicLattice.complexGaugeGroup) :
    leftExpMul X V ∈ PeriodicLattice.complexGaugeGroup := by
  have hdet := hel.2.2.2.2.2.1 (Complex.I • X)
  have htr : ComplexMatrix2.fullTrace (Complex.I • X) = 0 :=
    ComplexMatrix2.traceless.smul_mem Complex.I hX
  have hV' : V.det = 1 := hV
  change (ComplexMatrix2.matExp (Complex.I • X) * V).det = 1
  rw [Matrix.det_mul, hdet, htr, Complex.exp_zero, one_mul, hV']
theorem inv_mem_compactGaugeGroup {M : ComplexMatrix2}
    (hM : M ∈ PeriodicLattice.compactGaugeGroup) :
    M⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem det_eq_one_of_mem_compact {M : ComplexMatrix2}
    (hM : M ∈ PeriodicLattice.compactGaugeGroup) : M.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem inv_mem_complexGaugeGroup {M : ComplexMatrix2}
    (hM : M ∈ PeriodicLattice.complexGaugeGroup) :
    M⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
theorem logSeries_hasFDerivAt_one (hel : ComplexMatrix2.ExpLogEstimates) (𝕜 : Type)
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ComplexMatrix2] :
    HasFDerivAt ComplexMatrix2.logSeries (ContinuousLinearMap.id 𝕜 ComplexMatrix2) 1 := by
  refine HasFDerivAt.of_isLittleO ?_
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have ht : Tendsto (fun A : ComplexMatrix2 => ‖A - 1‖) (𝓝 1) (𝓝 0) := by
    have h : Continuous fun A : ComplexMatrix2 => ‖A - 1‖ :=
      (continuous_id.sub continuous_const).norm
    simpa using h.tendsto (1 : ComplexMatrix2)
  have hball : ∀ᶠ A : ComplexMatrix2 in 𝓝 1, ‖A - 1‖ < min (9 / 10) (c / 10) :=
    ht.eventually (gt_mem_nhds (lt_min (by norm_num) (by positivity)))
  filter_upwards [hball] with A hA
  have h9 : ‖A - 1‖ < 9 / 10 := lt_of_lt_of_le hA (min_le_left _ _)
  have hc10 : ‖A - 1‖ < c / 10 := lt_of_lt_of_le hA (min_le_right _ _)
  have hb := (hel.2.2.2.2.2.2.2.2.1 ‖A - 1‖ A 1 (norm_nonneg _) (by linarith) le_rfl
    (by simp)).2.2.1
  have hε := norm_nonneg (A - 1)
  simp only [ContinuousLinearMap.id_apply]
  have hb' : ‖ComplexMatrix2.logSeries A - ComplexMatrix2.logSeries 1 - (A - 1)‖ ≤
      ‖A - 1‖ / (1 - ‖A - 1‖) * ‖A - 1‖ := hb
  refine hb'.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hε
  rw [div_le_iff₀ (by linarith)]
  nlinarith
theorem curveLogDerivative_of_closed (hel : ComplexMatrix2.ExpLogEstimates) (𝕜 : Type)
    [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ComplexMatrix2]
    (D : Set 𝕜) (hD : D ∈ 𝓝 (0 : 𝕜)) (𝒢 𝔥 S : Set ComplexMatrix2)
    (hunit : ∀ V ∈ 𝒢, IsUnit V.det) (hq : ∀ V ∈ 𝒢, ∀ V' ∈ 𝒢, V * V'⁻¹ ∈ 𝒢)
    (hS : IsClosed S) (hsm : ∀ (c : 𝕜), ∀ A ∈ S, c • A ∈ S)
    (hlog : ∀ X ∈ 𝒢, ‖X - 1‖ ≤ 9 / 10 → ComplexMatrix2.logSeries X ∈ S)
    (hh : ∀ A ∈ S, Complex.I⁻¹ • A ∈ 𝔥) :
    CurveLogDerivative 𝕜 D 𝒢 𝔥 := by
  intro W hW hdiff
  have h0 : (0 : 𝕜) ∈ D := mem_of_mem_nhds hD
  have hV := hW h0
  have hX : HasDerivAt (fun t => W t * (W 0)⁻¹) (deriv W 0 * (W 0)⁻¹) 0 :=
    hdiff.hasDerivAt.mul_const _
  have hX1 : W 0 * (W 0)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hunit _ hV)
  have hlogd : HasDerivAt (fun t => ComplexMatrix2.logSeries (W t * (W 0)⁻¹))
      (deriv W 0 * (W 0)⁻¹) 0 := by
    have h1 : HasFDerivAt ComplexMatrix2.logSeries (ContinuousLinearMap.id 𝕜 ComplexMatrix2)
        (W 0 * (W 0)⁻¹) := by
      rw [hX1]
      exact logSeries_hasFDerivAt_one hel 𝕜
    exact h1.comp_hasDerivAt (0 : 𝕜) hX
  have hclose : ∀ᶠ t in 𝓝 (0 : 𝕜), ‖W t * (W 0)⁻¹ - 1‖ < 9 / 10 := by
    have ht : Tendsto (fun t => ‖W t * (W 0)⁻¹ - 1‖) (𝓝 0) (𝓝 0) := by
      have h := (hX.continuousAt.tendsto.sub_const (1 : ComplexMatrix2)).norm
      simpa [hX1] using h
    exact ht.eventually (gt_mem_nhds (by norm_num))
  refine ⟨hclose.mono fun t ht => ht.trans (by norm_num), hlogd.differentiableAt, ?_, ?_⟩
  · rw [hlogd.deriv]
  apply hh
  have hslope := hlogd.tendsto_slope_zero
  refine hS.mem_of_tendsto hslope ?_
  have hev : ∀ᶠ t in 𝓝[≠] (0 : 𝕜), ‖W t * (W 0)⁻¹ - 1‖ < 9 / 10 ∧ t ∈ D :=
    nhdsWithin_le_nhds (hclose.and hD)
  filter_upwards [hev] with t ht
  have hlt : ComplexMatrix2.logSeries (W (0 + t) * (W 0)⁻¹) ∈ S := by
    rw [zero_add]
    exact hlog _ (hq _ (hW ht.2) _ hV) ht.1.le
  simp only [hX1, logSeries_one, sub_zero]
  exact hsm _ _ hlt
theorem isClosed_hermitianTraceless :
    IsClosed (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) :=
  Submodule.closed_of_finiteDimensional ComplexMatrix2.hermitianTraceless
theorem isClosed_traceless : IsClosed (ComplexMatrix2.traceless : Set ComplexMatrix2) :=
  Submodule.closed_of_finiteDimensional ComplexMatrix2.traceless
theorem curveLogDerivative_compact (hel : ComplexMatrix2.ExpLogEstimates) (D : Set ℝ)
    (hD : D ∈ 𝓝 (0 : ℝ)) :
    CurveLogDerivative ℝ D PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra := by
  refine curveLogDerivative_of_closed hel ℝ D hD _ _
    {A | Complex.I⁻¹ • A ∈ ComplexMatrix2.hermitianTraceless}
    (fun V hV => by rw [det_eq_one_of_mem_compact hV]; exact isUnit_one)
    (fun V hV V' hV' => ComplexMatrix2.specialUnitary.mul_mem hV (inv_mem_compactGaugeGroup hV'))
    (isClosed_hermitianTraceless.preimage (continuous_const_smul _)) ?_ ?_ (fun A hA => hA)
  · intro c A hA
    have h := ComplexMatrix2.hermitianTraceless.smul_mem c hA
    change Complex.I⁻¹ • c • A ∈ ComplexMatrix2.hermitianTraceless
    rwa [smul_comm]
  · intro X hX h9
    obtain ⟨H, -, hlog, -, -, -, hdet⟩ := hel.2.2.2.2.2.2.2.1 X
      (Matrix.mem_specialUnitaryGroup_iff.1 hX).1 (by linarith)
    obtain ⟨-, -, ⟨Y, hY, hY'⟩, -⟩ := hdet (det_eq_one_of_mem_compact hX)
    change Complex.I⁻¹ • ComplexMatrix2.logSeries X ∈ ComplexMatrix2.hermitianTraceless
    rw [hY', smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    exact hY
theorem curveLogDerivative_complex (hel : ComplexMatrix2.ExpLogEstimates) (𝕜 : Type)
    [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ComplexMatrix2] (D : Set 𝕜)
    (hD : D ∈ 𝓝 (0 : 𝕜))
    (hsm : ∀ (c : 𝕜), ∀ A ∈ ComplexMatrix2.traceless, c • A ∈ ComplexMatrix2.traceless) :
    CurveLogDerivative 𝕜 D PeriodicLattice.complexGaugeGroup
      PeriodicLattice.complexLieAlgebra := by
  refine curveLogDerivative_of_closed hel 𝕜 D hD _ _ (ComplexMatrix2.traceless : Set ComplexMatrix2)
    (fun V hV => by
      have hV' : V.det = 1 := hV
      rw [hV']
      exact isUnit_one)
    (fun V hV V' hV' => ?_) isClosed_traceless hsm ?_ ?_
  · have h1 : V.det = 1 := hV
    have h2 : (V'⁻¹).det = 1 := inv_mem_complexGaugeGroup hV'
    change (V * V'⁻¹).det = 1
    rw [Matrix.det_mul, h1, h2, one_mul]
  · intro X hX h9
    exact (hel.2.2.2.2.2.2.1 X hX h9).2
  · intro A hA
    exact ComplexMatrix2.traceless.smul_mem _ hA
def pauliCoeff (Y : ComplexMatrix2) (a : Fin 3) : ℂ :=
  ComplexMatrix2.halfTrace (Y * ComplexMatrix2.pauliFamily a)
theorem pauliCoeff_pauliFamily (a b : Fin 3) :
    pauliCoeff (ComplexMatrix2.pauliFamily a) b = if a = b then 1 else 0 := by apply _root_.YangMills.Construction.Matrices.PauliBasis.halfTracePairing_pauli <;> assumption
theorem eq_sum_pauliCoeff {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.traceless) :
    Y = ∑ a, pauliCoeff Y a • ComplexMatrix2.pauliFamily a := by
  obtain ⟨h0, h1, h2⟩ := ComplexMatrix2.pauliFamily_apply
  have ht : Y 0 0 + Y 1 1 = 0 := by
    have h : ComplexMatrix2.fullTrace Y = 0 := hY
    simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using h
  have h11 : Y 1 1 = -Y 0 0 := by linear_combination ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCoeff, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Fin.sum_univ_three,
      h0, h1, h2, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h11] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring
theorem pauliFamily_mem_hermitian (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem mem_traceless_of_mem_hermitian {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) : Y ∈ ComplexMatrix2.traceless := hY.2
theorem pauliCoeff_im {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff Y a).im = 0 := by
  have h := pauliFamily_mem_hermitian a
  have hc : star (pauliCoeff Y a) = pauliCoeff Y a := by
    have h1 : (Y * ComplexMatrix2.pauliFamily a).conjTranspose =
        ComplexMatrix2.pauliFamily a * Y := by
      rw [Matrix.conjTranspose_mul, ← h.1, ← hY.1]
    simp only [pauliCoeff, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, star_mul']
    rw [← Matrix.trace_conjTranspose, h1, Matrix.trace_mul_comm]
    simp
  exact Complex.conj_eq_iff_im.1 hc
theorem mem_hermitian_of_pauliCoeff {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.traceless)
    (h : ∀ a, (pauliCoeff Y a).im = 0) : Y ∈ ComplexMatrix2.hermitianTraceless := by
  rw [eq_sum_pauliCoeff hY]
  refine ComplexMatrix2.hermitianTraceless.sum_mem fun a _ => ?_
  have h1 : pauliCoeff Y a = (((pauliCoeff Y a).re : ℝ) : ℂ) :=
    (Complex.ext rfl (by simp [h a]))
  rw [h1, Complex.coe_smul]
  exact ComplexMatrix2.hermitianTraceless.smul_mem _ (pauliFamily_mem_hermitian a)
theorem traceFinsumPairing_eq_sum_right {ι : Type*} (f g : ι → ComplexMatrix2) (s : Finset ι)
    (hs : ∀ i, i ∉ s → g i = 0) :
    traceFinsumPairing f g = ∑ i ∈ s, ComplexMatrix2.halfTrace (f i * g i) := by
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  by_contra h
  exact hi (by simp [hs i h, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace])
theorem traceFinsumPairing_eq_sum_left {ι : Type*} (f g : ι → ComplexMatrix2) (s : Finset ι)
    (hs : ∀ i, i ∉ s → f i = 0) :
    traceFinsumPairing f g = ∑ i ∈ s, ComplexMatrix2.halfTrace (f i * g i) := by
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  by_contra h
  exact hi (by simp [hs i h, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace])
theorem halfTrace_sum_pauli_mul (c : Fin 3 → ℂ) (Y : ComplexMatrix2) :
    ComplexMatrix2.halfTrace ((∑ a, c a • ComplexMatrix2.pauliFamily a) * Y) =
      ∑ a, c a * pauliCoeff Y a := by
  simp only [pauliCoeff, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Finset.sum_mul,
    Matrix.trace_sum, smul_mul_assoc, Matrix.trace_smul, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.trace_mul_comm]
  ring
theorem traceFinsumPairing_single {ι : Type*} [DecidableEq ι] (f : ι → ComplexMatrix2) (i : ι)
    (a : Fin 3) :
    traceFinsumPairing f (Pi.single i (ComplexMatrix2.pauliFamily a)) = pauliCoeff (f i) a := by
  rw [traceFinsumPairing_eq_sum_right f _ {i} (fun j hj => by
    simp [Pi.single_eq_of_ne (by simpa using hj : j ≠ i)])]
  simp [pauliCoeff]
theorem traceless_ext_pauliCoeff {Y Y' : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.traceless)
    (hY' : Y' ∈ ComplexMatrix2.traceless) (h : ∀ a, pauliCoeff Y a = pauliCoeff Y' a) :
    Y = Y' := by
  rw [eq_sum_pauliCoeff hY, eq_sum_pauliCoeff hY']
  exact Finset.sum_congr rfl fun a _ => by rw [h a]
theorem pauliCoeff_sum (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff (∑ e, c e • ComplexMatrix2.pauliFamily e) a = c a := by
  have h := halfTrace_sum_pauli_mul c (ComplexMatrix2.pauliFamily a)
  have h2 : ComplexMatrix2.halfTrace
      ((∑ e, c e • ComplexMatrix2.pauliFamily e) * ComplexMatrix2.pauliFamily a) =
    pauliCoeff (∑ e, c e • ComplexMatrix2.pauliFamily e) a := rfl
  rw [← h2, h]
  simp [pauliCoeff_pauliFamily]
theorem traceFinsumPairing_sum_right {ι κ : Type*} (g : ι → ComplexMatrix2) (s : Finset κ)
    (c : κ → ℂ) (h : κ → ι → ComplexMatrix2) (hh : ∀ k ∈ s, HasFiniteSupp (h k)) :
    traceFinsumPairing g (∑ k ∈ s, c k • h k) = ∑ k ∈ s, c k * traceFinsumPairing g (h k) := by
  classical
  let u : Finset ι := s.biUnion fun k =>
    if hk : k ∈ s then (hh k hk).toFinset else ∅
  have hu : ∀ k ∈ s, ∀ i, i ∉ u → h k i = 0 := by
    intro k hk i hi
    by_contra hne
    refine hi (Finset.mem_biUnion.2 ⟨k, hk, ?_⟩)
    rw [dif_pos hk]
    exact (hh k hk).mem_toFinset.2 hne
  rw [traceFinsumPairing_eq_sum_right g _ u (fun i hi => by
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_eq_zero fun k hk => by rw [hu k hk i hi, smul_zero])]
  have h2 : ∀ k ∈ s, traceFinsumPairing g (h k) =
      ∑ i ∈ u, ComplexMatrix2.halfTrace (g i * h k i) :=
    fun k hk => traceFinsumPairing_eq_sum_right g _ u (hu k hk)
  have h3 : ∑ k ∈ s, c k * traceFinsumPairing g (h k) =
      ∑ k ∈ s, c k * ∑ i ∈ u, ComplexMatrix2.halfTrace (g i * h k i) :=
    Finset.sum_congr rfl fun k hk => by rw [h2 k hk]
  rw [h3]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, Finset.mul_sum, mul_smul_comm,
    ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring
theorem traceFinsumPairing_add_left {ι : Type*} (g g' h : ι → ComplexMatrix2)
    (hh : HasFiniteSupp h) :
    traceFinsumPairing (g + g') h = traceFinsumPairing g h + traceFinsumPairing g' h := by
  classical
  have hs : ∀ i, i ∉ hh.toFinset → h i = 0 := fun i hi => by
    by_contra hne
    exact hi (hh.mem_toFinset.2 hne)
  rw [traceFinsumPairing_eq_sum_right _ _ _ hs, traceFinsumPairing_eq_sum_right _ _ _ hs,
    traceFinsumPairing_eq_sum_right _ _ _ hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, add_mul, Matrix.trace_add, mul_add]
theorem traceFinsumPairing_smul_left {ι : Type*} (c : ℂ) (g h : ι → ComplexMatrix2)
    (hh : HasFiniteSupp h) :
    traceFinsumPairing (c • g) h = c * traceFinsumPairing g h := by
  classical
  have hs : ∀ i, i ∉ hh.toFinset → h i = 0 := fun i hi => by
    by_contra hne
    exact hi (hh.mem_toFinset.2 hne)
  rw [traceFinsumPairing_eq_sum_right _ _ _ hs, traceFinsumPairing_eq_sum_right _ _ _ hs,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_mul_assoc, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_smul, smul_eq_mul]
  ring
theorem exists_unique_transpose (ι ι' : Type)
    (T : GroupLieProduct.tracelessFunctions ι →ₗ[ℂ] GroupLieProduct.tracelessFunctions ι')
    (hT : ∀ f : GroupLieProduct.tracelessFunctions ι, HasFiniteSupp (f : ι → ComplexMatrix2) →
      HasFiniteSupp (T f : ι' → ComplexMatrix2)) :
    ∃ T' : GroupLieProduct.tracelessFunctions ι' →ₗ[ℂ] GroupLieProduct.tracelessFunctions ι,
      (∀ (g : GroupLieProduct.tracelessFunctions ι')
        (f : GroupLieProduct.tracelessFunctions ι), HasFiniteSupp (f : ι → ComplexMatrix2) →
        traceFinsumPairing (T' g : ι → ComplexMatrix2) (f : ι → ComplexMatrix2) =
          traceFinsumPairing (g : ι' → ComplexMatrix2) (T f : ι' → ComplexMatrix2)) ∧
      ∀ R : GroupLieProduct.tracelessFunctions ι' → GroupLieProduct.tracelessFunctions ι,
        (∀ (g : GroupLieProduct.tracelessFunctions ι')
          (f : GroupLieProduct.tracelessFunctions ι), HasFiniteSupp (f : ι → ComplexMatrix2) →
          traceFinsumPairing (R g : ι → ComplexMatrix2) (f : ι → ComplexMatrix2) =
            traceFinsumPairing (g : ι' → ComplexMatrix2) (T f : ι' → ComplexMatrix2)) →
        R = T' := by
  classical
  have hδ : ∀ (σ : ι) (a : Fin 3),
      (Pi.single σ (ComplexMatrix2.pauliFamily a) : ι → ComplexMatrix2) ∈
        GroupLieProduct.tracelessFunctions ι := by
    intro σ a
    refine Submodule.mem_pi.2 fun τ _ => ?_
    by_cases h : τ = σ
    · subst h
      simpa using pauliFamily_mem_traceless a
    · simp [Pi.single_eq_of_ne h]
  let δ : ι → Fin 3 → GroupLieProduct.tracelessFunctions ι := fun σ a => ⟨_, hδ σ a⟩
  have hfs : ∀ σ a, HasFiniteSupp (T (δ σ a) : ι' → ComplexMatrix2) := fun σ a => hT _ (by
    refine (Set.finite_singleton σ).subset fun τ hτ => ?_
    by_contra h
    exact hτ (Pi.single_eq_of_ne h _))
  let F : GroupLieProduct.tracelessFunctions ι' → ι → ComplexMatrix2 := fun g σ =>
    ∑ a, traceFinsumPairing (g : ι' → ComplexMatrix2) (T (δ σ a) : ι' → ComplexMatrix2) •
      ComplexMatrix2.pauliFamily a
  have hmem : ∀ g, F g ∈ GroupLieProduct.tracelessFunctions ι := fun g =>
    Submodule.mem_pi.2 fun σ _ =>
      ComplexMatrix2.traceless.sum_mem fun a _ =>
        ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)
  have hFadd : ∀ g g', F (g + g') = F g + F g' := by
    intro g g'
    funext σ
    simp only [F, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Submodule.coe_add, traceFinsumPairing_add_left _ _ _ (hfs σ a), add_smul]
  have hFsmul : ∀ (c : ℂ) g, F (c • g) = c • F g := by
    intro c g
    funext σ
    simp only [F, Pi.smul_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Submodule.coe_smul, traceFinsumPairing_smul_left _ _ _ (hfs σ a), mul_smul]
  let T' : GroupLieProduct.tracelessFunctions ι' →ₗ[ℂ] GroupLieProduct.tracelessFunctions ι :=
    { toFun := fun g => ⟨F g, hmem g⟩
      map_add' := fun g g' => Subtype.ext (hFadd g g')
      map_smul' := fun c g => Subtype.ext (hFsmul c g) }
  have hT' : ∀ (g : GroupLieProduct.tracelessFunctions ι') σ,
      (T' g : ι → ComplexMatrix2) σ =
        ∑ a, traceFinsumPairing (g : ι' → ComplexMatrix2) (T (δ σ a) : ι' → ComplexMatrix2) •
          ComplexMatrix2.pauliFamily a :=
    fun _ _ => rfl
  have hsl : ∀ (f : GroupLieProduct.tracelessFunctions ι) σ,
      (f : ι → ComplexMatrix2) σ ∈ ComplexMatrix2.traceless := fun f σ =>
    Submodule.mem_pi.1 f.2 σ (Set.mem_univ _)
  have key : ∀ (g : GroupLieProduct.tracelessFunctions ι')
      (f : GroupLieProduct.tracelessFunctions ι),
      HasFiniteSupp (f : ι → ComplexMatrix2) →
      traceFinsumPairing (T' g : ι → ComplexMatrix2) (f : ι → ComplexMatrix2) =
        traceFinsumPairing (g : ι' → ComplexMatrix2) (T f : ι' → ComplexMatrix2) := by
    intro g f hf
    let s : Finset ι := hf.toFinset
    have hs : ∀ i, i ∉ s → (f : ι → ComplexMatrix2) i = 0 := fun i hi => by
      by_contra hne
      exact hi (hf.mem_toFinset.2 hne)
    have hfsum : f = ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin 3)),
        pauliCoeff ((f : ι → ComplexMatrix2) p.1) p.2 • δ p.1 p.2 := by
      refine Subtype.ext (funext fun τ => ?_)
      rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_product]
      by_cases hτ : τ ∈ s
      · rw [Finset.sum_eq_single τ]
        · simp only [Submodule.coe_smul, Pi.smul_apply, δ, Pi.single_eq_same]
          exact eq_sum_pauliCoeff (hsl f τ)
        · intro σ _ hne
          refine Finset.sum_eq_zero fun a _ => ?_
          simp [δ, Pi.single_eq_of_ne (Ne.symm hne)]
        · exact fun h => absurd hτ h
      · rw [hs τ hτ]
        refine (Finset.sum_eq_zero fun σ hσ => Finset.sum_eq_zero fun a _ => ?_).symm
        have hne : τ ≠ σ := fun h => hτ (h ▸ hσ)
        simp [δ, Pi.single_eq_of_ne hne]
    have hTf : (T f : ι' → ComplexMatrix2) = ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin 3)),
        pauliCoeff ((f : ι → ComplexMatrix2) p.1) p.2 • (T (δ p.1 p.2) : ι' → ComplexMatrix2) := by
      conv_lhs => rw [hfsum]
      rw [map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul]
      rfl
    rw [hTf, traceFinsumPairing_sum_right _ _ _ _ fun p _ => hfs p.1 p.2,
      traceFinsumPairing_eq_sum_right _ _ s hs, Finset.sum_product]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hT', halfTrace_sum_pauli_mul]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨T', fun g f hf => key g f hf, fun R hR => ?_⟩
  funext g
  refine Subtype.ext (funext fun σ => ?_)
  refine traceless_ext_pauliCoeff (hsl _ σ) (hsl _ σ) fun a => ?_
  have h1 := hR g (δ σ a) (by
    refine (Set.finite_singleton σ).subset fun τ hτ => ?_
    by_contra h
    exact hτ (Pi.single_eq_of_ne h _))
  have h2 := key g (δ σ a) (by
    refine (Set.finite_singleton σ).subset fun τ hτ => ?_
    by_contra h
    exact hτ (Pi.single_eq_of_ne h _))
  have h3 : traceFinsumPairing ((R g : GroupLieProduct.tracelessFunctions ι) : ι → ComplexMatrix2)
      (δ σ a : ι → ComplexMatrix2) =
      pauliCoeff (((R g : GroupLieProduct.tracelessFunctions ι) : ι → ComplexMatrix2) σ) a :=
    traceFinsumPairing_single _ _ _
  have h4 : traceFinsumPairing ((T' g : GroupLieProduct.tracelessFunctions ι) : ι → ComplexMatrix2)
      (δ σ a : ι → ComplexMatrix2) =
      pauliCoeff (((T' g : GroupLieProduct.tracelessFunctions ι) : ι → ComplexMatrix2) σ) a :=
    traceFinsumPairing_single _ _ _
  rw [← h3, ← h4]
  exact h1.trans h2.symm
theorem hasUniqueTranspose_pairedFunctions (ι ι' : Type) :
    HasUniqueTranspose (pairedFunctions ι) (pairedFunctions ι') :=
  fun T hT => exists_unique_transpose ι ι' T hT
namespace LatticeData
structure OrientedFacts (Λ : LatticeData) : Prop where
  onPositive_mem_hermitian : ∀ B ∈ Λ.forms, ∀ b, onPositive B b ∈ ComplexMatrix2.hermitianTraceless
  onPositive_mem_traceless : ∀ B ∈ Λ.cforms, ∀ b, onPositive B b ∈ ComplexMatrix2.traceless
  exists_real_form : ∀ g : Λ.PosLink → ComplexMatrix2,
    (∀ b, g b ∈ ComplexMatrix2.hermitianTraceless) → ∃ B ∈ Λ.forms, onPositive B = g
  exists_complex_form : ∀ g : Λ.PosLink → ComplexMatrix2, (∀ b, g b ∈ ComplexMatrix2.traceless) →
    ∃ B ∈ Λ.cforms, onPositive B = g
  form_ext_of_onPositive : ∀ B ∈ Λ.forms, ∀ B' ∈ Λ.forms, onPositive B = onPositive B' → B = B'
  field_onPositive_mem : ∀ (𝒢 : Set ComplexMatrix2), ∀ U ∈ Λ.fields 𝒢, ∀ b, onPositive U b ∈ 𝒢
  curve_props : ∀ (I : Set ℝ) (γ : ℝ → Λ.Link → ComplexMatrix2), Λ.IsCurve I γ →
    IsOpenIntervalAroundZero I ∧
      (∀ t ∈ I, ∀ b, γ t (Λ.incl b) ∈ PeriodicLattice.compactGaugeGroup) ∧
      ∀ b, DifferentiableOn ℝ (fun t => γ t (Λ.incl b)) I
  exists_curve_of_form : ∀ U ∈ Λ.fields PeriodicLattice.compactGaugeGroup, ∀ B ∈ Λ.forms,
    ∃ (I : Set ℝ) (γ : ℝ → Λ.Link → ComplexMatrix2), Λ.IsCurve I γ ∧ γ 0 = U ∧
      ∀ (t : ℝ) (b : Λ.PosLink),
        γ t (Λ.incl b) = leftExpMul ((t : ℂ) • onPositive B b) (onPositive U b)
variable {Λ : LatticeData}
theorem leftExpMulMemGroup_of_facts (hf : Λ.OrientedFacts)
    (hil : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hel : ComplexMatrix2.ExpLogEstimates) : Λ.LeftExpMulMemGroup := by
  refine ⟨fun U hU B hB b =>
      ⟨fun t => leftExpMul_mem_compact hil ?_ (hf.field_onPositive_mem _ U hU b),
        leftExpMul_hasDerivAt_real _ _⟩,
    fun U hU B hB b =>
      ⟨fun t => leftExpMul_mem_complexGroup hel ?_ (hf.field_onPositive_mem _ U hU b),
        leftExpMul_hasDerivAt_complex _ _⟩⟩
  · rw [Complex.coe_smul]
    exact ComplexMatrix2.hermitianTraceless.smul_mem t (hf.onPositive_mem_hermitian B hB b)
  · exact ComplexMatrix2.traceless.smul_mem t (hf.onPositive_mem_traceless B hB b)
theorem curveTangentsEqForms_of_facts (hf : Λ.OrientedFacts)
    (hel : ComplexMatrix2.ExpLogEstimates) : Λ.CurveTangentsEqForms := by
  intro U hU
  have hunit : ∀ b, (onPositive U b)⁻¹ * onPositive U b = 1 := fun b =>
    Matrix.nonsing_inv_mul _
      (by rw [det_eq_one_of_mem_compact (hf.field_onPositive_mem _ U hU b)]; exact isUnit_one)
  have hunit' : ∀ b, onPositive U b * (onPositive U b)⁻¹ = 1 := fun b =>
    Matrix.mul_nonsing_inv _
      (by rw [det_eq_one_of_mem_compact (hf.field_onPositive_mem _ U hU b)]; exact isUnit_one)
  refine ⟨fun Y => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨I, γ, hγ, h0, hY⟩
    obtain ⟨hI, hval, hd⟩ := hf.curve_props I γ hγ
    have hD : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
    have hg : ∀ b, Complex.I⁻¹ • (Y b * (onPositive U b)⁻¹) ∈
        ComplexMatrix2.hermitianTraceless := by
      intro b
      have hlog := curveLogDerivative_compact hel I hD (fun t => γ t (Λ.incl b))
        (fun t ht => hval t ht b) ((hd b).differentiableAt hD)
      have h := hlog.2.2.2
      simp only [hY b, h0] at h
      exact h
    obtain ⟨B, hB, hBv⟩ := hf.exists_real_form _ hg
    refine ⟨B, hB, fun b => ?_⟩
    rw [hBv, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, mul_assoc, hunit, mul_one]
  · rintro ⟨B, hB, hY⟩
    obtain ⟨I, γ, hγ, h0, hv⟩ := hf.exists_curve_of_form U hU B hB
    refine ⟨I, γ, hγ, h0, fun b => ?_⟩
    have h : (fun t => γ t (Λ.incl b)) =
        fun t : ℝ => leftExpMul ((t : ℂ) • onPositive B b) (onPositive U b) :=
      funext fun t => hv t b
    rw [h, (leftExpMul_hasDerivAt_real _ _).deriv, hY]
  · intro B hB B' hB' h
    refine hf.form_ext_of_onPositive B hB B' hB' (funext fun b => ?_)
    have h1 := congrArg (· * (onPositive U b)⁻¹) (h b)
    simp only [mul_assoc, hunit', mul_one] at h1
    exact smul_right_injective _ Complex.I_ne_zero h1
section GradientsAsPairings
variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
theorem leftDeriv_congr {r : ℕ} (bs : Fin r → Λ.PosLink)
    (f : (Fin r → ComplexMatrix2) → ℂ) (U B B' : Λ.Link → ComplexMatrix2)
    (h : ∀ i, onPositive B (bs i) = onPositive B' (bs i)) :
    leftDeriv 𝕜 bs f U B = leftDeriv 𝕜 bs f U B' := by
  have hp : ∀ c : ℂ, leftPoint bs U (c • B) = leftPoint bs U (c • B') := by
    intro c
    funext i
    have h' : B (Λ.incl (bs i)) = B' (Λ.incl (bs i)) := h i
    simp only [leftPoint, onPositive, Pi.smul_apply, h']
  simp only [leftDeriv, directionalDeriv, hp]
open Classical in
theorem pauliCoeff_of_isGradient [Module 𝕜 ComplexMatrix2]
    {𝔉 : Submodule 𝕜 (Λ.Link → ComplexMatrix2)} {r : ℕ}
    {bs : Fin r → Λ.PosLink} {f : (Fin r → ComplexMatrix2) → ℂ} {U : Λ.Link → ComplexMatrix2}
    {X : Λ.PosLink → ComplexMatrix2} (hX : IsGradient 𝕜 𝔉 bs f U X) (b : Λ.PosLink) (a : Fin 3)
    {B : Λ.Link → ComplexMatrix2} (hB : B ∈ 𝔉)
    (hv : onPositive B = Pi.single b (ComplexMatrix2.pauliFamily a)) :
    pauliCoeff (X b) a = leftDeriv 𝕜 bs f U B := by
  rw [← traceFinsumPairing_single X b a, ← hv]
  refine hX.2 B hB ?_
  rw [hv]
  refine (Set.finite_singleton b).subset fun τ hτ => ?_
  by_contra h
  exact hτ (Pi.single_eq_of_ne h _)
theorem leftDerivEqPair_of_linear [hm : Module 𝕜 ComplexMatrix2]
    (hsmul : ∀ (c : 𝕜) (M : ComplexMatrix2),
      hm.toDistribMulAction.toMulAction.toSMul.smul c M = algebraMap 𝕜 ℂ c • M)
    (𝔉 : Submodule 𝕜 (Λ.Link → ComplexMatrix2)) (base : Set ComplexMatrix2)
    (hform : ∀ g : Λ.PosLink → ComplexMatrix2, (∀ b, g b ∈ base) → ∃ B ∈ 𝔉, onPositive B = g)
    (hval : ∀ B ∈ 𝔉, ∀ b, onPositive B b ∈ base)
    (h0 : (0 : ComplexMatrix2) ∈ base) (hpauli : ∀ a, ComplexMatrix2.pauliFamily a ∈ base)
    (hsl : ∀ Y ∈ base, Y ∈ ComplexMatrix2.traceless)
    (hcoef : ∀ Y ∈ base, ∃ y : Fin 3 → 𝕜, ∀ a, pauliCoeff Y a = algebraMap 𝕜 ℂ (y a))
    {r : ℕ} (bs : Fin r → Λ.PosLink) (O : Set (Fin r → ComplexMatrix2))
    (f : (Fin r → ComplexMatrix2) → ℂ) (U : Λ.Link → ComplexMatrix2)
    (h1 : ∀ B ∈ 𝔉, ∀ᶠ t in 𝓝 (0 : 𝕜), leftPoint bs U (algebraMap 𝕜 ℂ t • B) ∈ O)
    (h2 : ∀ B ∈ 𝔉,
      DifferentiableAt 𝕜 (fun t : 𝕜 => f (leftPoint bs U (algebraMap 𝕜 ℂ t • B))) 0)
    (φ : 𝔉 →ₗ[𝕜] ℂ) (hφ : ∀ B : 𝔉, φ B = leftDeriv 𝕜 bs f U B) :
    LeftDerivEqPair 𝕜 𝔉 bs O f U := by
  classical
  have hsingle : ∀ (b : Λ.PosLink) (a : Fin 3),
      ∃ B ∈ 𝔉, onPositive B = Pi.single b (ComplexMatrix2.pauliFamily a) :=
    fun b a => hform _ fun b' => by
      by_cases h : b' = b
      · subst h
        simpa using hpauli a
      · simpa [Pi.single_eq_of_ne h] using h0
  choose δ hδ hδv using hsingle
  have hv : ∀ b a τ, δ b a (Λ.incl τ) =
      (Pi.single b (ComplexMatrix2.pauliFamily a) : Λ.PosLink → ComplexMatrix2) τ :=
    fun b a τ => congrFun (hδv b a) τ
  let c : Λ.PosLink → Fin 3 → ℂ := fun b a => φ ⟨δ b a, hδ b a⟩
  have hc : ∀ b a, c b a = leftDeriv 𝕜 bs f U (δ b a) := fun b a => hφ _
  let X : Λ.PosLink → ComplexMatrix2 := fun b => ∑ a, c b a • ComplexMatrix2.pauliFamily a
  have hXsl : ∀ b, X b ∈ ComplexMatrix2.traceless := fun b =>
    ComplexMatrix2.traceless.sum_mem fun a _ =>
      ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)
  have hkey : ∀ B ∈ 𝔉, ∀ s : Finset Λ.PosLink, (∀ b, b ∉ s → onPositive B b = 0) →
      traceFinsumPairing X (onPositive B) = leftDeriv 𝕜 bs f U B := by
    intro B hB s hs
    choose y hy using fun b => hcoef (onPositive B b) (hval B hB b)
    let B' : 𝔉 := ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin 3)),
      y p.1 p.2 • (⟨δ p.1 p.2, hδ p.1 p.2⟩ : 𝔉)
    have hB' : ∀ τ, onPositive (B' : Λ.Link → ComplexMatrix2) τ = onPositive B τ := by
      intro τ
      change (B' : Λ.Link → ComplexMatrix2) (Λ.incl τ) = _
      simp only [B', Submodule.coe_sum, Finset.sum_apply, Finset.sum_product, Submodule.coe_smul,
        Pi.smul_apply, hv]
      by_cases hτ : τ ∈ s
      · rw [Finset.sum_eq_single τ]
        · rw [eq_sum_pauliCoeff (hsl _ (hval B hB τ))]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Pi.single_eq_same, hy]
          exact hsmul _ _
        · intro σ _ hne
          refine Finset.sum_eq_zero fun a _ => ?_
          rw [Pi.single_eq_of_ne (Ne.symm hne)]
          exact (hsmul _ _).trans (smul_zero _)
        · exact fun h => absurd hτ h
      · rw [hs τ hτ]
        refine Finset.sum_eq_zero fun σ hσ => Finset.sum_eq_zero fun a _ => ?_
        have hne : τ ≠ σ := fun h => hτ (h ▸ hσ)
        rw [Pi.single_eq_of_ne hne]
        exact (hsmul _ _).trans (smul_zero _)
    have hdd : leftDeriv 𝕜 bs f U B = φ B' := by
      rw [hφ B']
      exact leftDeriv_congr bs f U _ _ fun i => (hB' (bs i)).symm
    rw [hdd, map_sum, traceFinsumPairing_eq_sum_right X _ s hs, Finset.sum_product]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hX : X b = ∑ a, c b a • ComplexMatrix2.pauliFamily a := rfl
    rw [hX, halfTrace_sum_pauli_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hy, Algebra.smul_def, mul_comm]
  have hvanish : ∀ b, b ∉ range bs → X b = 0 := by
    intro b hb
    refine Finset.sum_eq_zero fun a _ => ?_
    have hz : c b a = 0 := by
      rw [hc, leftDeriv_congr bs f U (δ b a) 0 fun i => ?_]
      · have h := hφ (0 : 𝔉)
        rw [map_zero] at h
        exact h.symm
      · have hne : bs i ≠ b := fun h => hb ⟨i, h⟩
        change δ b a (Λ.incl (bs i)) = 0
        rw [hv, Pi.single_eq_of_ne hne]
    rw [hz, zero_smul]
  have hall : ∀ B ∈ 𝔉, traceFinsumPairing X (onPositive B) = leftDeriv 𝕜 bs f U B := by
    intro B hB
    obtain ⟨B₀, hB₀, hv₀⟩ := hform (fun b => if b ∈ range bs then onPositive B b else 0)
      fun b => by
        by_cases h : b ∈ range bs
        · simpa [h] using hval B hB b
        · simpa [h] using h0
    let s : Finset Λ.PosLink := Finset.univ.image bs
    have hs : ∀ b, b ∉ s → b ∉ range bs := fun b hb h => hb (by
      obtain ⟨i, rfl⟩ := h
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have h1' := hkey B₀ hB₀ s fun b hb => by rw [hv₀]; simp [hs b hb]
    have h2' : leftDeriv 𝕜 bs f U B = leftDeriv 𝕜 bs f U B₀ :=
      leftDeriv_congr bs f U _ _ fun i => by rw [hv₀]; simp
    rw [h2', ← h1', traceFinsumPairing_eq_sum_left X _ s fun b hb => hvanish b (hs b hb),
      traceFinsumPairing_eq_sum_left X _ s fun b hb => hvanish b (hs b hb)]
    refine Finset.sum_congr rfl fun b hb => ?_
    by_cases h : b ∈ range bs
    · rw [hv₀]
      simp [h]
    · rw [hvanish b h]
      simp
  have hrep : IsGradient 𝕜 𝔉 bs f U X := ⟨hXsl, fun B hB hfin => hkey B hB hfin.toFinset
    fun b hb => by
      by_contra hne
      exact hb (hfin.mem_toFinset.2 hne)⟩
  have huniq : ∀ X', IsGradient 𝕜 𝔉 bs f U X' → X' = X := by
    intro X' hX'
    funext b
    refine traceless_ext_pauliCoeff (hX'.1 b) (hXsl b) fun a => ?_
    rw [pauliCoeff_of_isGradient hX' b a (hδ b a) (hδv b a), ← hc]
    exact (pauliCoeff_sum _ a).symm
  refine ⟨h1, h2, ⟨φ, hφ⟩, fun B _ B' _ h => leftDeriv_congr bs f U B B' h,
    ⟨X, hrep, huniq⟩, fun X' hX' => ?_⟩
  rw [huniq X' hX']
  exact ⟨hvanish, hall⟩
end GradientsAsPairings
end LatticeData
namespace LatticeData
variable {Λ : LatticeData}
theorem realGradientExists_of_facts (hf : Λ.OrientedFacts)
    (hch : PowerExpCharts.ExpChartsStatement) : Λ.RealGradientExists := by
  classical
  intro r hr bs O f U hO hdiff hU hmem
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨hformed, -, hder, -⟩ := (hch (Fin r) (Fin r)).2.2.1 O f hO
  have hder' := hder hdiff
  let p₀ : Fin r → ComplexMatrix2 := fun i => onPositive U (bs i)
  have hp₀ : p₀ ∈ O := hmem
  let Yf : Λ.forms → Fin r → ComplexMatrix2.LieElement := fun B i =>
    (⟨onPositive (B : Λ.Link → ComplexMatrix2) (bs i), hf.onPositive_mem_hermitian _ B.2 _⟩ :
      ComplexMatrix2.hermitianTraceless)
  have hpt : ∀ (B : Λ.forms) (t : ℝ),
      leftPoint bs U (algebraMap ℝ ℂ t • (B : Λ.Link → ComplexMatrix2)) =
        PowerExpCharts.expChartI p₀ (t • Yf B) := by
    intro B t
    funext i
    change ComplexMatrix2.matExp
        (Complex.I • ((t : ℂ) • onPositive (B : Λ.Link → ComplexMatrix2) (bs i))) *
          onPositive U (bs i) =
      ComplexMatrix2.matExp (Complex.I • (t • onPositive (B : Λ.Link → ComplexMatrix2) (bs i))) *
        p₀ i
    rw [Complex.coe_smul]
  let tf : Λ.forms →ₗ[ℝ] (Fin r → ComplexMatrix2) :=
    { toFun := fun B i => Complex.I • onPositive (B : Λ.Link → ComplexMatrix2) (bs i) * p₀ i
      map_add' := fun B B' => by
        funext i
        change Complex.I • (onPositive (B : Λ.Link → ComplexMatrix2) (bs i) +
          onPositive (B' : Λ.Link → ComplexMatrix2) (bs i)) * p₀ i = _
        rw [smul_add, add_mul]
        rfl
      map_smul' := fun c B => by
        funext i
        change Complex.I • (c • onPositive (B : Λ.Link → ComplexMatrix2) (bs i)) * p₀ i = _
        rw [smul_comm, smul_mul_assoc]
        rfl }
  have hmem_tf : ∀ B, tf B ∈
      EmbeddedSubmanifold.tangentSpace (specialUnitaryPower (Fin r)) p₀ :=
    fun B => (hder' p₀ hp₀ (Yf B)).2.choose
  let φ : Λ.forms →ₗ[ℝ] ℂ :=
    (EmbeddedSubmanifold.tangentDifferential (specialUnitaryPower (Fin r)) f p₀).comp
      (tf.codRestrict _ hmem_tf)
  have hHas : ∀ B : Λ.forms, HasDerivAt
      (fun t : ℝ => f (leftPoint bs U (algebraMap ℝ ℂ t • (B : Λ.Link → ComplexMatrix2))))
      (φ B) 0 := by
    intro B
    obtain ⟨-, h, hd⟩ := hder' p₀ hp₀ (Yf B)
    simp only [hpt]
    exact hd
  have h1 : ∀ B ∈ Λ.forms, ∀ᶠ t in 𝓝 (0 : ℝ), leftPoint bs U (algebraMap ℝ ℂ t • B) ∈ O := by
    intro B hB
    obtain ⟨N, hN, hfN⟩ := hformed p₀ hp₀
    have ht : Tendsto (fun t : ℝ => t • Yf ⟨B, hB⟩) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun t : ℝ => t • Yf ⟨B, hB⟩ := continuous_id.smul continuous_const
      simpa using hc.tendsto 0
    filter_upwards [ht hN] with t ht'
    have := hpt ⟨B, hB⟩ t
    simp only at this
    rw [this]
    exact hfN ht'
  have hφ : ∀ B : Λ.forms, φ B = leftDeriv ℝ bs f U B := fun B =>
    (hHas B).deriv.symm
  have hpair : LeftDerivEqPair ℝ Λ.forms bs O f U :=
    leftDerivEqPair_of_linear
      (fun c M => (Complex.coe_smul c M).symm) Λ.forms
      (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2)
      hf.exists_real_form hf.onPositive_mem_hermitian ComplexMatrix2.hermitianTraceless.zero_mem
      pauliFamily_mem_hermitian (fun Y hY => mem_traceless_of_mem_hermitian hY)
      (fun Y hY => ⟨fun a => (pauliCoeff Y a).re, fun a =>
        Complex.ext rfl (by simp [pauliCoeff_im hY a])⟩)
      bs O f U h1 (fun B hB => (hHas ⟨B, hB⟩).differentiableAt) φ hφ
  refine ⟨hpair, fun hre X hX b => mem_hermitian_of_pauliCoeff (hX.1 b) fun a => ?_⟩
  obtain ⟨B, hB, hv⟩ := hf.exists_real_form (Pi.single b (ComplexMatrix2.pauliFamily a))
    fun b' => by
      by_cases h : b' = b
      · subst h
        simpa using pauliFamily_mem_hermitian a
      · simp [Pi.single_eq_of_ne h]
  rw [pauliCoeff_of_isGradient hX b a hB hv, ← hφ ⟨B, hB⟩]
  have hd := hHas ⟨B, hB⟩
  have him : HasDerivAt (fun t : ℝ => (f (leftPoint bs U (algebraMap ℝ ℂ t • B))).im)
      (φ ⟨B, hB⟩).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have hz : HasDerivAt (fun t : ℝ => (f (leftPoint bs U (algebraMap ℝ ℂ t • B))).im) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      ((h1 B hB).mono fun t ht => hre _ ht)
  exact him.unique hz
end LatticeData
namespace LatticeData
variable {Λ : LatticeData}
theorem holomorphicGradientExists_of_facts (hf : Λ.OrientedFacts)
    (hh : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    Λ.HolomorphicGradientExists := by
  classical
  intro β r hr bs O f U hO hhol hU hmem
  let p₀ : Fin r → ComplexMatrix2 := fun i => onPositive U (bs i)
  obtain ⟨-, -, hpts⟩ := hhol
  obtain ⟨O', h0, hW, -, hH⟩ := hpts (GroupLieProduct.asGroupFactors p₀) ⟨p₀, hmem, rfl⟩
  let ν : (Fin r ⊕ Empty) ≃ Fin (Fintype.card (Fin r ⊕ Empty)) := Fintype.equivFin _
  let T := GroupLieProduct.tupleOfCoords β ν
  have hT0 : T 0 = 0 := by
    funext i
    simp [T, GroupLieProduct.tupleOfCoords, ComplexCoordinates.tracelessTuple]
  have hTs : ∀ (t : ℂ) (w : ComplexCoordinates (Fintype.card (Fin r ⊕ Empty) * 3)),
      T (t • w) = t • T w := by
    intro t w
    funext i
    simp [T, GroupLieProduct.tupleOfCoords, ComplexCoordinates.tracelessTuple, Finset.smul_sum,
      mul_smul]
  let A : Fin r → Λ.cforms →ₗ[ℂ] ComplexMatrix2.traceless := fun i =>
    LinearMap.codRestrict ComplexMatrix2.traceless
      { toFun := fun B => Complex.I • onPositive (B : Λ.Link → ComplexMatrix2) (bs i)
        map_add' := fun B B' => smul_add _ _ _
        map_smul' := fun c B =>
          smul_comm Complex.I c (onPositive (B : Λ.Link → ComplexMatrix2) (bs i)) }
      fun B => ComplexMatrix2.traceless.smul_mem _ (hf.onPositive_mem_traceless _ B.2 _)
  let Aof : (Fin r ⊕ Empty) → Λ.cforms →ₗ[ℂ] ComplexMatrix2.traceless :=
    Sum.elim A fun e => e.elim
  let wlin : Λ.cforms →ₗ[ℂ] ComplexCoordinates (Fintype.card (Fin r ⊕ Empty) * 3) :=
    LinearMap.pi fun k => (β.coord (finProdFinEquiv.symm k).2).comp
      (Aof (ν.symm (finProdFinEquiv.symm k).1))
  have hTw : ∀ (B : Λ.cforms) (i : Fin r),
      T (wlin B) (.inl i) = Complex.I • onPositive (B : Λ.Link → ComplexMatrix2) (bs i) := by
    intro B i
    have h := congrArg (Subtype.val : ComplexMatrix2.traceless → ComplexMatrix2)
      (β.sum_repr (A i B))
    rw [Submodule.coe_sum] at h
    have hk : ∀ c, wlin B (finProdFinEquiv (ν (.inl i), c)) = β.repr (A i B) c := by
      intro c
      have e : finProdFinEquiv.symm (finProdFinEquiv (ν (.inl i), c)) = (ν (.inl i), c) :=
        Equiv.symm_apply_apply _ _
      change β.coord (finProdFinEquiv.symm (finProdFinEquiv (ν (.inl i), c))).2
        (Aof (ν.symm (finProdFinEquiv.symm (finProdFinEquiv (ν (.inl i), c))).1) B) = _
      rw [e]
      simp only [Equiv.symm_apply_apply]
      rfl
    calc T (wlin B) (.inl i)
        = ∑ c, wlin B (finProdFinEquiv (ν (.inl i), c)) • (β c : ComplexMatrix2) := rfl
      _ = ∑ c, β.repr (A i B) c • (β c : ComplexMatrix2) :=
          Finset.sum_congr rfl fun c _ => by rw [hk c]
      _ = Complex.I • onPositive (B : Λ.Link → ComplexMatrix2) (bs i) := h
  have hH' := hH ν
  have hΩ := hH'.1
  have h0Ω : (0 : ComplexCoordinates (Fintype.card (Fin r ⊕ Empty) * 3)) ∈
      GroupLieProduct.tupleOfCoords β ν ⁻¹' O' := by
    change T 0 ∈ O'
    rw [hT0]
    exact h0
  obtain ⟨Lc, hL⟩ := ((hh.1 _ _ hΩ).1 1 _ hH').2.2.1 0 h0Ω
  have hL' := hasFDerivAt_of_restrictScalars ℝ hL rfl
  have hpt : ∀ (B : Λ.cforms) (t : ℂ),
      leftPoint bs U (algebraMap ℂ ℂ t • (B : Λ.Link → ComplexMatrix2)) =
        fun i => GroupLieProduct.expChartAt (GroupLieProduct.asGroupFactors p₀)
          (T (t • wlin B)) (.inl i) := by
    intro B t
    funext i
    have h1 : T (t • wlin B) (.inl i) =
        t • (Complex.I • onPositive (B : Λ.Link → ComplexMatrix2) (bs i)) := by
      rw [hTs]
      exact congrArg (t • ·) (hTw B i)
    change ComplexMatrix2.matExp
        (Complex.I • (t • onPositive (B : Λ.Link → ComplexMatrix2) (bs i))) *
          onPositive U (bs i) =
      ComplexMatrix2.matExp (T (t • wlin B) (.inl i)) * p₀ i
    rw [h1, smul_comm]
  have hline : ∀ w : ComplexCoordinates (Fintype.card (Fin r ⊕ Empty) * 3),
      HasDerivAt (fun t : ℂ => t • w) w 0 := by
    intro w
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const w
  have hHas : ∀ B : Λ.cforms, HasDerivAt
      (fun t : ℂ => f (leftPoint bs U (algebraMap ℂ ℂ t • (B : Λ.Link → ComplexMatrix2))))
      (Lc (wlin B) 0) 0 := by
    intro B
    have hat := hL'
    rw [← zero_smul ℂ (wlin B)] at hat
    have h2 := hat.comp_hasDerivAt (0 : ℂ) (hline (wlin B))
    have h3 := (hasDerivAt_pi.1 h2) 0
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [hpt]
    simp [scalarCoords, Function.comp_def]
    rfl
  let φ : Λ.cforms →ₗ[ℂ] ℂ := (LinearMap.proj 0).comp (Lc.toLinearMap.comp wlin)
  have h1 : ∀ B ∈ Λ.cforms, ∀ᶠ t in 𝓝 (0 : ℂ), leftPoint bs U (algebraMap ℂ ℂ t • B) ∈ O := by
    intro B hB
    have ht : Tendsto (fun t : ℂ => t • wlin ⟨B, hB⟩) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun t : ℂ => t • wlin ⟨B, hB⟩ := continuous_id.smul continuous_const
      simpa using hc.tendsto 0
    filter_upwards [ht (hΩ.mem_nhds h0Ω)] with t ht'
    obtain ⟨q, hq, hqe⟩ := hW _ ht'
    have hqp : q = leftPoint bs U (algebraMap ℂ ℂ t • B) := by
      rw [show leftPoint bs U (algebraMap ℂ ℂ t • B) = _ from hpt ⟨B, hB⟩ t]
      funext i
      exact congrFun hqe (.inl i)
    rwa [← hqp]
  exact leftDerivEqPair_of_linear (fun c M => rfl) Λ.cforms
    (ComplexMatrix2.traceless : Set ComplexMatrix2)
    hf.exists_complex_form hf.onPositive_mem_traceless ComplexMatrix2.traceless.zero_mem
    pauliFamily_mem_traceless (fun Y hY => hY)
    (fun Y _ => ⟨pauliCoeff Y, fun a => rfl⟩)
    bs O f U h1 (fun B hB => (hHas ⟨B, hB⟩).differentiableAt) φ (fun B => (hHas B).deriv.symm)
end LatticeData
theorem leftExpMul_differentiable (X V : ComplexMatrix2) :
    Differentiable ℝ fun t : ℝ => leftExpMul ((t : ℂ) • X) V := by
  intro t
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • X) (t : ℂ)
  have h2 := h.mul_const V
  have h3 : HasDerivAt (fun u : ℂ => leftExpMul (u • X) V)
      (NormedSpace.exp ((t : ℂ) • Complex.I • X) * (Complex.I • X) * V)
      (Complex.ofRealCLM t) :=
    h2.congr_of_eventuallyEq (Eventually.of_forall fun u => by
      simp only [leftExpMul, ComplexMatrix2.matExp, smul_comm Complex.I u X])
  exact (HasDerivAt.scomp t h3 Complex.ofRealCLM.hasDerivAt).differentiableAt
theorem inv_inv_of_mem_compact {M : ComplexMatrix2}
    (hM : M ∈ PeriodicLattice.compactGaugeGroup) : M⁻¹⁻¹ = M := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
namespace LatticeData
open Classical in
theorem OrientedFacts.of_orientation (hil : ComplexMatrix2.UnitaryLogConjugationProperties)
    {Λ : LatticeData}
    (rev : Λ.Link → Λ.Link) (pos : Λ.Link → Prop)
    (hrev : ∀ b, rev (rev b) = b) (hpos : ∀ b, pos (rev b) ↔ ¬ pos b)
    (hbond : ∀ p, pos (Λ.incl p)) (hmk : ∀ b, pos b → ∃ p, Λ.incl p = b)
    (hinj : Function.Injective Λ.incl)
    (hforms : ∀ B, B ∈ Λ.forms ↔
      (∀ b, pos b → B b ∈ ComplexMatrix2.hermitianTraceless) ∧ ∀ b, B (rev b) = -B b)
    (hcforms : ∀ B, B ∈ Λ.cforms ↔
      (∀ b, pos b → B b ∈ ComplexMatrix2.traceless) ∧ ∀ b, B (rev b) = -B b)
    (hconf : ∀ (𝒢 : Set ComplexMatrix2) U, U ∈ Λ.fields 𝒢 ↔
      (∀ b, U b ∈ 𝒢) ∧ ∀ b, U (rev b) = (U b)⁻¹)
    (hcurve : ∀ I γ, Λ.IsCurve I γ ↔ IsOpenIntervalAroundZero I ∧
      MapsTo γ I (Λ.fields PeriodicLattice.compactGaugeGroup) ∧
      ∀ b, pos b → DifferentiableOn ℝ (fun t => γ t b) I) :
    Λ.OrientedFacts := by
  choose get hget using hmk
  let ex : (Λ.PosLink → ComplexMatrix2) → Λ.Link → ComplexMatrix2 := fun g b =>
    if h : pos b then g (get b h) else -g (get (rev b) ((hpos b).2 h))
  have hgetb : ∀ (g : Λ.PosLink → ComplexMatrix2) (c b : Λ.Link) (hc : pos c) (hb : pos b),
      c = b → g (get c hc) = g (get b hb) := by
    intro g c b hc hb e
    subst e
    rfl
  have ex_rev : ∀ g b, ex g (rev b) = -ex g b := by
    intro g b
    by_cases h : pos b
    · have h' : ¬ pos (rev b) := fun h2 => (hpos b).1 h2 h
      simp only [ex, dif_neg h', dif_pos h]
      rw [hgetb g _ b _ h (hrev b)]
    · have h' : pos (rev b) := (hpos b).2 h
      simp only [ex, dif_neg h, dif_pos h', neg_neg]
  have ex_val : ∀ g, onPositive (ex g) = g := by
    intro g
    funext p
    change ex g (Λ.incl p) = g p
    simp only [ex, dif_pos (hbond p)]
    exact congrArg g (hinj (hget _ _))
  refine
    { onPositive_mem_hermitian := fun B hB b => ((hforms B).1 hB).1 _ (hbond b)
      onPositive_mem_traceless := fun B hB b => ((hcforms B).1 hB).1 _ (hbond b)
      exists_real_form := fun g hg =>
        ⟨ex g, (hforms _).2 ⟨fun b hb => ?_, ex_rev g⟩, ex_val g⟩
      exists_complex_form := fun g hg =>
        ⟨ex g, (hcforms _).2 ⟨fun b hb => ?_, ex_rev g⟩, ex_val g⟩
      form_ext_of_onPositive := ?_
      field_onPositive_mem := fun 𝒢 U hU b => ((hconf 𝒢 U).1 hU).1 _
      curve_props := fun I γ hγ => ?_
      exists_curve_of_form := ?_ }
  · simp only [ex, dif_pos hb]
    exact hg _
  · simp only [ex, dif_pos hb]
    exact hg _
  · intro B hB B' hB' h
    have hp : ∀ b, pos b → B b = B' b := fun b hb => by
      rw [← hget b hb]
      exact congrFun h _
    funext b
    by_cases hb : pos b
    · exact hp b hb
    · have h1 := ((hforms B).1 hB).2 (rev b)
      have h2 := ((hforms B').1 hB').2 (rev b)
      rw [hrev] at h1 h2
      rw [h1, h2, hp _ ((hpos b).2 hb)]
  · obtain ⟨hI, hM, hd⟩ := (hcurve I γ).1 hγ
    exact ⟨hI, fun t ht b => ((hconf _ _).1 (hM ht)).1 _, fun b => hd _ (hbond b)⟩
  · intro U hU B hB
    obtain ⟨hUv, hUr⟩ := (hconf _ _).1 hU
    obtain ⟨hBv, -⟩ := (hforms _).1 hB
    let γ : ℝ → Λ.Link → ComplexMatrix2 := fun t b =>
      if pos b then leftExpMul ((t : ℂ) • B b) (U b)
      else (leftExpMul ((t : ℂ) • B (rev b)) (U (rev b)))⁻¹
    have hval : ∀ (t : ℝ) b, pos b →
        leftExpMul ((t : ℂ) • B b) (U b) ∈ PeriodicLattice.compactGaugeGroup := by
      intro t b hb
      refine leftExpMul_mem_compact hil ?_ (hUv b)
      rw [Complex.coe_smul]
      exact ComplexMatrix2.hermitianTraceless.smul_mem t (hBv b hb)
    refine ⟨univ, γ, (hcurve _ _).2 ⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩,
      fun t _ => (hconf _ _).2 ⟨fun b => ?_, fun b => ?_⟩, fun b hb => ?_⟩, ?_, fun t p => ?_⟩
    · by_cases hb : pos b
      · simp only [γ, if_pos hb]
        exact hval t b hb
      · simp only [γ, if_neg hb]
        exact inv_mem_compactGaugeGroup (hval t _ ((hpos b).2 hb))
    · by_cases hb : pos b
      · have h' : ¬ pos (rev b) := fun h2 => (hpos b).1 h2 hb
        simp only [γ, if_neg h', if_pos hb, hrev]
      · have h' : pos (rev b) := (hpos b).2 hb
        simp only [γ, if_neg hb, if_pos h']
        exact (inv_inv_of_mem_compact (hval t _ h')).symm
    · have h : (fun t => γ t b) = fun t : ℝ => leftExpMul ((t : ℂ) • B b) (U b) :=
        funext fun t => if_pos hb
      rw [h]
      exact (leftExpMul_differentiable _ _).differentiableOn
    · funext b
      by_cases hb : pos b
      · simp [γ, hb, leftExpMul]
      · have h' := hUr b
        simp only [γ, if_neg hb]
        simp only [Complex.ofReal_zero, zero_smul, leftExpMul, smul_zero, ComplexMatrix2.matExp,
          NormedSpace.exp_zero, one_mul, h']
        exact inv_inv_of_mem_compact (hUv b)
    · exact if_pos (hbond p)
end LatticeData
section FiniteSide
variable {L n k j : ℕ}
theorem finite_isPos_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem finite_not_isPos_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem finite_opposite_isPos_iff (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j) :
    b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented :=
  ⟨fun h h' => finite_not_isPos_opposite hA hL hn hj b h' h,
    fun h => (finite_isPos_or_opposite b).resolve_left h⟩
theorem finiteData_orientedFacts (hil : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) : (finiteData L n k j).OrientedFacts :=
  LatticeData.OrientedFacts.of_orientation hil (Λ := finiteData L n k j)
    PeriodicLattice.Bond.opposite
    PeriodicLattice.Bond.IsPositivelyOriented (fun _ => rfl) (finite_opposite_isPos_iff hA hL hn hj)
    (fun p => p.2) (fun b h => ⟨⟨b, h⟩, rfl⟩) Subtype.val_injective
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (fun _ _ => ⟨fun h => ⟨fun b => h.1 b trivial, fun b => h.2 b trivial⟩,
      fun h => ⟨fun b _ => h.1 b, fun b _ => h.2 b⟩⟩)
    (fun _ _ => Iff.rfl)
end FiniteSide
section FullSide
theorem full_opposite_isPos_iff {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.link_opposite_positive_iff <;> assumption
theorem meshAt_pos {L k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.meshAt_pos <;> assumption
theorem fullData_orientedFacts (hil : ComplexMatrix2.UnitaryLogConjugationProperties)
    {L k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    (fullData L k j).OrientedFacts :=
  LatticeData.OrientedFacts.of_orientation hil (Λ := fullData L k j) InfiniteLattice.Link.opposite
    InfiniteLattice.Link.IsPositivelyOriented (fun _ => rfl) (full_opposite_isPos_iff (meshAt_pos hL))
    (fun p => p.2) (fun b h => ⟨⟨b, h⟩, rfl⟩) Subtype.val_injective
    (fun _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
end FullSide
theorem mem_tangentSpace_power_iff (hch : PowerExpCharts.ExpChartsStatement)
    (hel : ComplexMatrix2.ExpLogEstimates) {σ : Type} [Fintype σ] [Nonempty σ]
    {p : σ → ComplexMatrix2} (hp : p ∈ specialUnitaryPower σ) (Y : σ → ComplexMatrix2) :
    Y ∈ EmbeddedSubmanifold.tangentSpace (specialUnitaryPower σ) p ↔
      ∀ b, Complex.I⁻¹ • (Y b * (p b)⁻¹) ∈ ComplexMatrix2.hermitianTraceless := by
  let S : Submodule ℝ (σ → ComplexMatrix2) :=
    { carrier := {Y | ∀ b, Complex.I⁻¹ • (Y b * (p b)⁻¹) ∈ ComplexMatrix2.hermitianTraceless}
      add_mem' := fun {Y Y'} hY hY' b => by
        have h := ComplexMatrix2.hermitianTraceless.add_mem (hY b) (hY' b)
        rw [← smul_add, ← add_mul] at h
        exact h
      zero_mem' := fun b => by simp [ComplexMatrix2.hermitianTraceless.zero_mem]
      smul_mem' := fun c Y hY b => by
        have h := ComplexMatrix2.hermitianTraceless.smul_mem c (hY b)
        rw [smul_comm, ← smul_mul_assoc] at h
        exact h }
  have hle : EmbeddedSubmanifold.tangentSpace (specialUnitaryPower σ) p ≤ S := by
    refine iSup_le fun c => iSup_le fun u => iSup_le fun hu => ?_
    obtain ⟨hu, hpu⟩ := hu
    have hdomN : c.source ∈ 𝓝 u := c.isOpen_source.mem_nhds hu
    have hdiff : HasFDerivAt c.param (fderiv ℝ c.param u) u :=
      ((c.contDiffOn_param.differentiableOn (by simp)).differentiableAt
        hdomN).hasFDerivAt
    have hM : ∀ v ∈ c.source, c.param v ∈ specialUnitaryPower σ := by
      obtain ⟨O, -, hO⟩ := c.isRelativelyOpen_image c.source subset_rfl c.isOpen_source
      intro v hv
      have h : c.param v ∈ c.param '' c.source := ⟨v, hv, rfl⟩
      rw [hO] at h
      exact h.2
    rintro _ ⟨w, rfl⟩ b
    have hline : HasDerivAt (fun t : ℝ => u + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add u
    have hD : {t : ℝ | u + t • w ∈ c.source} ∈ 𝓝 (0 : ℝ) :=
      hline.continuousAt (by simpa using hdomN)
    have h1 : HasDerivAt (fun t : ℝ => c.param (u + t • w)) (fderiv ℝ c.param u w) 0 := by
      have hd' : HasFDerivAt c.param (fderiv ℝ c.param u) (u + (0 : ℝ) • w) := by
        simpa using hdiff
      exact hd'.comp_hasDerivAt (0 : ℝ) hline
    have hW := (hasDerivAt_pi.1 h1) b
    have hlog := curveLogDerivative_compact hel {t : ℝ | u + t • w ∈ c.source} hD
      (fun t => c.param (u + t • w) b) (fun t ht => hM _ ht b) hW.differentiableAt
    have h := hlog.2.2.2
    rw [hW.deriv] at h
    simp only [zero_smul, add_zero, hpu] at h
    exact h
  refine ⟨fun hY => hle hY, fun hY => ?_⟩
  let Yf : σ → ComplexMatrix2.LieElement := fun b =>
    (⟨_, hY b⟩ : ComplexMatrix2.hermitianTraceless)
  have hO : specialUnitaryPower.IsOpenSubset (specialUnitaryPower σ) :=
    ⟨univ, isOpen_univ, by simp⟩
  have hd : EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ)
      (specialUnitaryPower σ) (fun _ => (0 : ℂ)) := ⟨hO, fun c => differentiableOn_const 0⟩
  obtain ⟨-, h, -⟩ := ((hch σ σ).2.2.1 _ _ hO).2.2.1 hd p hp Yf
  have hYf : PowerExpCharts.tangentVectorAt p Yf = Y := by
    funext b
    have hu : (p b)⁻¹ * p b = 1 :=
      Matrix.nonsing_inv_mul _ (by rw [det_eq_one_of_mem_compact (hp b)]; exact isUnit_one)
    change (Complex.I • Complex.I⁻¹ • (Y b * (p b)⁻¹)) * p b = Y b
    rw [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, mul_assoc, hu, mul_one]
  rwa [hYf] at h
section FiniteSide
variable {L n k j : ℕ}
theorem finite_vertices_edges_faces (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Finite (Vertex L n k j) ∧ Finite (Edge L n k j) ∧ Finite (Face L n k j) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hs, hb, hp⟩ := (hA L hL n j k hn hj).2.1
  exact ⟨hs, hb, hp⟩
theorem finiteTangentSpaceEq_holds (hch : PowerExpCharts.ExpChartsStatement)
    (hil : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    FiniteTangentSpaceEq L n k j := by
  classical
  have hf := finiteData_orientedFacts (n := n) (k := k) (j := j) hil hA hL hn hj
  have hT := LatticeData.curveTangentsEqForms_of_facts hf hel
  have hfinB := (finite_vertices_edges_faces (n := n) (k := k) (j := j) hA hL hn hj).2.1
  have hrev := finite_opposite_isPos_iff (n := n) (k := k) (j := j) hA hL hn hj
  have hfin : Finite (PositiveEdge L n k j) := Subtype.finite
  have hne : Nonempty (PositiveEdge L n k j) :=
    ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩⟩
  refine ⟨hfin, ⟨fun U hU b => hU.1 b.1 trivial, ?_, ?_⟩, ?_⟩
  · intro U hU U' hU' h
    have hp : ∀ b : Edge L n k j, b.IsPositivelyOriented → U b = U' b := fun b hb =>
      congrFun h ⟨b, hb⟩
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact hp b hb
    · have h1 := hU.2 b.opposite trivial
      have h2 := hU'.2 b.opposite trivial
      have h3 : b.opposite.opposite = b := rfl
      rw [h3] at h1 h2
      rw [h1, h2, hp _ ((hrev b).2 hb)]
  · intro w hw
    have hw' : ∀ b, w b ∈ PeriodicLattice.compactGaugeGroup := hw
    refine ⟨fieldOfPositiveValues w, ⟨fun b _ => ?_, fun b _ => ?_⟩,
      funext fun b => dif_pos b.2⟩
    · by_cases hb : b.IsPositivelyOriented
      · simp only [fieldOfPositiveValues, dif_pos hb]
        exact hw' _
      · have h' := (hrev b).2 hb
        simp only [fieldOfPositiveValues, dif_neg hb, dif_pos h']
        exact inv_mem_compactGaugeGroup (hw' _)
    · by_cases hb : b.IsPositivelyOriented
      · have h' : ¬ b.opposite.IsPositivelyOriented := fun h => (hrev b).1 h hb
        have h3 : b.opposite.opposite = b := rfl
        simp only [fieldOfPositiveValues, dif_neg h', dif_pos hb, h3]
      · have h' := (hrev b).2 hb
        simp only [fieldOfPositiveValues, dif_neg hb, dif_pos h']
        exact (inv_inv_of_mem_compact (hw' _)).symm
  · intro _ U hU
    have hp : restrictToPositiveEdges U ∈ specialUnitaryPower (PositiveEdge L n k j) :=
      fun b => hf.field_onPositive_mem _ U hU b
    have hiff := mem_tangentSpace_power_iff hch hel hp
    have hT' := hT U hU
    have hu : ∀ b : PositiveEdge L n k j,
        (restrictToPositiveEdges U b)⁻¹ * restrictToPositiveEdges U b = 1 := fun b =>
      Matrix.nonsing_inv_mul _ (by rw [det_eq_one_of_mem_compact (hp b)]; exact isUnit_one)
    have hu' : ∀ b : PositiveEdge L n k j,
        restrictToPositiveEdges U b * (restrictToPositiveEdges U b)⁻¹ = 1 := fun b =>
      Matrix.mul_nonsing_inv _ (by rw [det_eq_one_of_mem_compact (hp b)]; exact isUnit_one)
    have hform : ∀ Y : PositiveEdge L n k j → ComplexMatrix2, Y ∈ tangentAt U ↔
        ∃ B ∈ edgeFormSpace L n k j, ∀ b : PositiveEdge L n k j,
          Y b = Complex.I • B b * restrictToPositiveEdges U b := by
      intro Y
      refine ⟨fun hY => ?_, ?_⟩
      · obtain ⟨B, hB, hBv⟩ := hf.exists_real_form _ ((hiff Y).1 hY)
        refine ⟨B, hB, fun b => ?_⟩
        have h := congrFun hBv b
        change B b.1 = _ at h
        rw [h, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, mul_assoc, hu, mul_one]
      · rintro ⟨B, hB, hY⟩
        refine (hiff Y).2 fun b => ?_
        rw [hY b, smul_mul_assoc, smul_mul_assoc, mul_assoc, hu', mul_one, smul_smul,
          inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
        exact hf.onPositive_mem_hermitian B hB b
    refine ⟨Set.ext fun Y => (hform Y).trans ?_, ?_⟩
    · exact (hT'.1 Y).symm
    let tf : edgeFormSpace L n k j →ₗ[ℝ] (PositiveEdge L n k j → ComplexMatrix2) :=
      { toFun := fun B b =>
          Complex.I • (B : Edge L n k j → ComplexMatrix2) b * restrictToPositiveEdges U b
        map_add' := fun B B' => by
          funext b
          change Complex.I • ((B : Edge L n k j → ComplexMatrix2) b +
            (B' : Edge L n k j → ComplexMatrix2) b) * restrictToPositiveEdges U b = _
          rw [smul_add, add_mul]
          rfl
        map_smul' := fun c B => by
          funext b
          change Complex.I • (c • (B : Edge L n k j → ComplexMatrix2) b) *
            restrictToPositiveEdges U b = _
          rw [smul_comm, smul_mul_assoc]
          rfl }
    have hmem : ∀ B, tf B ∈ tangentAt U := fun B => (hform _).2 ⟨B, B.2, fun _ => rfl⟩
    refine ⟨tf.codRestrict _ hmem, ⟨fun B B' h => ?_, fun Y => ?_⟩, fun B => ?_⟩
    · refine Subtype.ext (hT'.2 B.1 B.2 B'.1 B'.2 fun b => ?_)
      exact congrFun (congrArg Subtype.val h) b
    · obtain ⟨B, hB, hY⟩ := (hform Y).1 Y.2
      exact ⟨⟨B, hB⟩, Subtype.ext (funext fun b => (hY b).symm)⟩
    · funext b
      have h : (fun t : ℝ =>
          PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k j → ComplexMatrix2)) U b) =
          fun t : ℝ => leftExpMul ((t : ℂ) • (B : Edge L n k j → ComplexMatrix2) b) (U b) := by
        funext t
        simp only [PeriodicLattice.expTwist, if_pos b.2]
        rfl
      change _ = deriv (fun t : ℝ =>
        PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k j → ComplexMatrix2)) U b) 0
      rw [h, (leftExpMul_hasDerivAt_real _ _).deriv]
      rfl
theorem finiteCarrier_carrier_finite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (c : FiniteCarrier L n k) :
    Finite c.carrier := by
  cases c with
  | vertices j hj S =>
    have := (finite_vertices_edges_faces (n := n) (k := k) (j := j) hA hL hn hj).1
    exact Subtype.finite
  | edges j hj S =>
    have := (finite_vertices_edges_faces (n := n) (k := k) (j := j) hA hL hn hj).2.1
    exact Subtype.finite
  | faces j hj S =>
    have := (finite_vertices_edges_faces (n := n) (k := k) (j := j) hA hL hn hj).2.2
    exact Subtype.finite
end FiniteSide
theorem conditions_of_facts {Λ : LatticeData} (hf : Λ.OrientedFacts)
    (hch : PowerExpCharts.ExpChartsStatement)
    (hil : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hh : ComplexCoordinates.PowerSeriesHolomorphy.Properties) : Λ.Conditions :=
  ⟨LatticeData.leftExpMulMemGroup_of_facts hf hil hel,
    LatticeData.curveTangentsEqForms_of_facts hf hel,
    LatticeData.realGradientExists_of_facts hf hch,
    LatticeData.holomorphicGradientExists_of_facts hf hh⟩
theorem claim_holds (hil : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hch : PowerExpCharts.ExpChartsStatement)
    (hh : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties) :
    Claim := by
  refine ⟨fun I hI => ⟨curveLogDerivative_compact hel I (hI.1.mem_nhds hI.2.2),
      curveLogDerivative_complex hel ℝ I (hI.1.mem_nhds hI.2.2) fun c A hA' => ?_⟩,
    fun ρ hρ => curveLogDerivative_complex hel ℂ _ (Metric.ball_mem_nhds 0 hρ) fun c A hA' =>
      ComplexMatrix2.traceless.smul_mem c hA',
    fun L k j hL hj => ⟨fun n hn =>
        ⟨conditions_of_facts (finiteData_orientedFacts hil hA hL hn hj) hch hil hel hh,
        finiteTangentSpaceEq_holds hch hil hel hA hL hn hj,
        fun c c' => ⟨hasUniqueTranspose_pairedFunctions _ _, fun T f _ => ?_⟩⟩,
      conditions_of_facts (fullData_orientedFacts hil hL) hch hil hel hh,
      fun c c' => hasUniqueTranspose_pairedFunctions _ _⟩⟩
  · have h := ComplexMatrix2.traceless.smul_mem (c : ℂ) hA'
    rwa [Complex.coe_smul] at h
  · have := finiteCarrier_carrier_finite hA hL hn c'
    exact Set.toFinite _
end YangMills.Construction.Tower.LeftChartFields
