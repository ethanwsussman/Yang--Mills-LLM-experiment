import YangMills.Construction.Matrices.PartialCoefficientsOfASquareIntegrableFunctionForm
import YangMills.Construction.Matrices.PeterWeylFunctionsOfSeveralVariablesAndKernelsForm
import YangMills.Construction.Matrices.SeriesOfTheTensorOperatorConverges
import YangMills.Construction.Matrices.TensorProductsOfSquareIntegrableFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics.TensorOneSeries
section InnerPreserving
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]
theorem map_add_of_inner_preserving (U : V → W) (hU : ∀ u v, inner ℂ (U u) (U v) = inner ℂ u v)
    (u v : V) : U (u + v) = U u + U v := by
  have hz : inner ℂ (U (u + v) - U u - U v) (U (u + v) - U u - U v) = (0 : ℂ) := by
    simp only [inner_sub_left, inner_sub_right, hU, inner_add_left, inner_add_right]
    ring
  have hd := inner_self_eq_zero.mp hz
  rw [sub_sub, sub_eq_zero] at hd
  exact hd
theorem map_smul_of_inner_preserving (U : V → W) (hU : ∀ u v, inner ℂ (U u) (U v) = inner ℂ u v)
    (c : ℂ) (u : V) : U (c • u) = c • U u := by
  have hz : inner ℂ (U (c • u) - c • U u) (U (c • u) - c • U u) = (0 : ℂ) := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hU]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
theorem norm_map_of_inner_preserving (U : V → W) (hU : ∀ u v, inner ℂ (U u) (U v) = inner ℂ u v)
    (u : V) : ‖U u‖ = ‖u‖ := by
  have he := hU u u
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at he
  have hsq : ‖U u‖ ^ 2 = ‖u‖ ^ 2 := by exact_mod_cast he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
theorem summable_and_norm_sq_tsum_of_orthogonal [CompleteSpace V] {ι : Type*} (v : ι → V)
    (horth : Pairwise fun i j => inner ℂ (v i) (v j) = (0 : ℂ))
    (hs : Summable fun i => ‖v i‖ ^ 2) :
    Summable v ∧ ‖∑' i, v i‖ ^ 2 = ∑' i, ‖v i‖ ^ 2 := by
  classical
  have hfam : OrthogonalFamily ℂ (fun i => ↥(Submodule.span ℂ {v i}))
      (fun i => (Submodule.span ℂ {v i}).subtypeₗᵢ) := by
    intro i j hij x y
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [inner_smul_left, inner_smul_right, horth hij]
  let g : ∀ i, ↥(Submodule.span ℂ {v i}) := fun i => ⟨v i, Submodule.mem_span_singleton_self _⟩
  have hv : Summable v := (hfam.summable_iff_norm_sq_summable g).mpr hs
  refine ⟨hv, ?_⟩
  have hfin : ∀ s : Finset ι, ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 :=
    fun s => hfam.norm_sum g s
  have hto : Filter.Tendsto (fun s : Finset ι => ‖∑ i ∈ s, v i‖ ^ 2) Filter.atTop
      (nhds (‖∑' i, v i‖ ^ 2)) := (hv.hasSum.norm).pow 2
  have hto' : Filter.Tendsto (fun s : Finset ι => ‖∑ i ∈ s, v i‖ ^ 2) Filter.atTop
      (nhds (∑' i, ‖v i‖ ^ 2)) := by
    simp only [hfin]
    exact hs.hasSum
  exact tendsto_nhds_unique hto hto'
end InnerPreserving
section Classes
variable {J : Type} [Finite J]
theorem toHaarL2_coeFn (a : HaarL2 J) :
    toHaarL2 (a : (J → specialUnitary) → ℂ) = a := by
  unfold toHaarL2
  rw [dif_pos (Lp.memLp a)]
  exact Lp.toLp_coeFn a (Lp.memLp a)
theorem memLp_peterWeylFn (α : PeterWeylIndex J) :
    MemLp (peterWeylFn α : (J → specialUnitary) → ℂ) 2 (haarPi J) :=
  (Lp.memLp (peterWeylVec α)).ae_eq (ContinuousMap.coeFn_toLp (haarPi J) (peterWeylFn α))
theorem toHaarL2_peterWeylFn (α : PeterWeylIndex J) :
    toHaarL2 (peterWeylFn α : (J → specialUnitary) → ℂ) = peterWeylVec α := by
  unfold toHaarL2
  rw [dif_pos (memLp_peterWeylFn α)]
  exact Lp.ext ((memLp_peterWeylFn α).coeFn_toLp.trans
    (ContinuousMap.coeFn_toLp (haarPi J) (peterWeylFn α)).symm)
end Classes
theorem tensorOneSeriesConvergesForAll_of (hCoeff : PartialCoeffL2Properties)
    (hPW : PeterWeylOrthonormalAndKernel)
    (hTen : TensorFnMemL2Inner) : TensorOneSeriesConvergesForAll := by
  intro J _ _ B hne hB X
  have : Nonempty ↥Bᶜ := (Set.nonempty_compl.mpr hB).to_subtype
  obtain ⟨hmem, hproj, hpars⟩ := hCoeff J B hne hB
  choose Q hQ using hproj
  have hon : Orthonormal ℂ (peterWeylVec : PeterWeylIndex ↥Bᶜ → HaarL2 ↥Bᶜ) :=
    (hPW ↥Bᶜ fun _ => ⟨0⟩).1
  let E : PeterWeylIndex ↥Bᶜ → HaarL2 ↥B → HaarL2 J := fun γ a =>
    toHaarL2 (tensorFn B a (peterWeylFn γ))
  have hEinner : ∀ (γ γ' : PeterWeylIndex ↥Bᶜ) (a a' : HaarL2 ↥B),
      inner ℂ (E γ a) (E γ' a') =
        inner ℂ a a' * inner ℂ (peterWeylVec γ) (peterWeylVec γ') := by
    intro γ γ' a a'
    have h := (hTen J B a a' (peterWeylFn γ) (peterWeylFn γ') (Lp.memLp a) (Lp.memLp a')
      (memLp_peterWeylFn γ) (memLp_peterWeylFn γ')).2
    rwa [toHaarL2_coeFn, toHaarL2_coeFn, toHaarL2_peterWeylFn,
      toHaarL2_peterWeylFn] at h
  have hEkeep : ∀ (γ : PeterWeylIndex ↥Bᶜ) (a a' : HaarL2 ↥B),
      inner ℂ (E γ a) (E γ a') = inner ℂ a a' := by
    intro γ a a'
    rw [hEinner, inner_self_eq_norm_sq_to_K, hon.1 γ]
    simp
  let R : PeterWeylIndex ↥Bᶜ → HaarL2 J → HaarL2 J := fun γ F =>
    E γ (X (Q γ F))
  have hterm : ∀ F γ, tensorSeriesTerm B X F γ = R γ F := by
    intro F γ
    simp only [tensorSeriesTerm, R, E, hQ]
  have hRadd : ∀ γ F F', R γ (F + F') = R γ F + R γ F' := by
    intro γ F F'
    simp only [R, map_add]
    exact map_add_of_inner_preserving (E γ) (hEkeep γ) _ _
  have hRsmul : ∀ γ (c : ℂ) F, R γ (c • F) = c • R γ F := by
    intro γ c F
    simp only [R, map_smul]
    exact map_smul_of_inner_preserving (E γ) (hEkeep γ) _ _
  have hpars' : ∀ F, HasSum (fun γ => ‖Q γ F‖ ^ 2) (‖F‖ ^ 2) := by
    intro F
    simpa only [hQ] using hpars F
  have hRnorm : ∀ γ F, ‖R γ F‖ ^ 2 ≤ ‖X‖ ^ 2 * ‖Q γ F‖ ^ 2 := by
    intro γ F
    have he : ‖R γ F‖ = ‖X (Q γ F)‖ := norm_map_of_inner_preserving (E γ) (hEkeep γ) _
    rw [he, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (X.le_opNorm _) 2
  have hRsq : ∀ F, Summable fun γ => ‖R γ F‖ ^ 2 := fun F =>
    Summable.of_nonneg_of_le (fun _ => by positivity) (fun γ => hRnorm γ F)
      ((hpars' F).summable.mul_left _)
  have hRorth : ∀ F, Pairwise fun γ γ' => inner ℂ (R γ F) (R γ' F) = (0 : ℂ) := by
    intro F γ γ' hne'
    simp only [R]
    rw [hEinner, hon.2 hne', mul_zero]
  have hsum : ∀ F, Summable fun γ => R γ F := fun F =>
    (summable_and_norm_sq_tsum_of_orthogonal _ (hRorth F) (hRsq F)).1
  have hbound : ∀ F, ‖∑' γ, R γ F‖ ≤ ‖X‖ * ‖F‖ := by
    intro F
    have hn := (summable_and_norm_sq_tsum_of_orthogonal _ (hRorth F) (hRsq F)).2
    have hle : ∑' γ, ‖R γ F‖ ^ 2 ≤ ‖X‖ ^ 2 * ‖F‖ ^ 2 := by
      have hmul : HasSum (fun γ => ‖X‖ ^ 2 * ‖Q γ F‖ ^ 2) (‖X‖ ^ 2 * ‖F‖ ^ 2) :=
        (hpars' F).mul_left _
      exact hasSum_le (fun γ => hRnorm γ F) (hRsq F).hasSum hmul
    rw [← hn, ← mul_pow] at hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hle
  let L : HaarL2 J →ₗ[ℂ] HaarL2 J :=
    { toFun := fun F => ∑' γ, R γ F
      map_add' := fun F F' => by
        simp only [hRadd]
        exact (hsum F).tsum_add (hsum F')
      map_smul' := fun c F => by
        simp only [hRsmul, RingHom.id_apply]
        exact (hsum F).tsum_const_smul c }
  let A : HaarL2 J →L[ℂ] HaarL2 J := L.mkContinuous ‖X‖ hbound
  have hnotall : ¬∀ b, b ∈ B := fun h => hB (Set.eq_univ_of_forall h)
  have hvalue : ∀ F, tensorOneApply B X F = ∑' γ, R γ F := by
    intro F
    unfold tensorOneApply
    rw [dif_neg hnotall]
    simp only [hterm]
  have hA : ∀ F, A F = tensorOneApply B X F := fun F => (hvalue F).symm
  have hone : ∀ F, tensorOne B X F = tensorOneApply B X F := by
    unfold tensorOne
    exact Classical.epsilon_spec (p := fun T' : HaarL2 J →L[ℂ] HaarL2 J =>
      ∀ F, T' F = tensorOneApply B X F) ⟨A, hA⟩
  refine ⟨fun F => ⟨fun γ => ⟨hmem γ F, ?_⟩, ?_, ?_⟩, ?_⟩
  · have ha := Lp.memLp (X (toHaarL2 (partialCoeff B γ F)))
    exact (hTen J B _ _ (peterWeylFn γ) (peterWeylFn γ) ha ha
      (memLp_peterWeylFn γ) (memLp_peterWeylFn γ)).1
  · have h : tensorSeriesTerm B X F = fun γ => R γ F := funext (hterm F)
    rw [h]
    exact hsum F
  · exact hone F
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun F => ?_
    rw [hone, hvalue]
    exact hbound F
end YangMills.Construction.SpinHarmonics.TensorOneSeries
end
