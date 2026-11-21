import YangMills.Construction.LawByMomentsOfTheFlow.TheChainHasItsGaussian
import YangMills.Construction.ResponseInTheExpansion.GradientsUnderTheMaxwellFormProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace YangMills.Construction.MomentLaw
private theorem exists_isCanonicalGaussian_of_sq_norm {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]
    (T : V →ₗ[ℝ] EuclideanSpace ℝ ι) (Q : V → ℝ) (hQ : ∀ v, Q v = ‖T v‖ ^ 2) : ∃ μ : Measure V, IsCanonicalGaussian Q μ := by
  classical
  obtain ⟨R, hR⟩ := T.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict T)
  have hTR : ∀ y : LinearMap.range T, T (R y) = y := fun y => by
    have := congrArg Subtype.val (LinearMap.congr_fun hR y)
    simpa using this
  obtain ⟨P, hP⟩ : ∃ P : EuclideanSpace ℝ ι →L[ℝ] LinearMap.range T, P = (LinearMap.range T).orthogonalProjectionOnto := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : EuclideanSpace ℝ ι →ₗ[ℝ] V, Ψ = R ∘ₗ (P : EuclideanSpace ℝ ι →ₗ[ℝ] LinearMap.range T) := ⟨_, rfl⟩
  have hΨc : Continuous Ψ := LinearMap.continuous_of_finiteDimensional Ψ
  refine ⟨(stdGaussian (EuclideanSpace ℝ ι)).map Ψ, Measure.isProbabilityMeasure_map hΨc.aemeasurable, fun g hg => ?_⟩
  have hgR : ∀ v, g v = g (R (T.rangeRestrict v)) := by
    intro v
    have h1 : Q (v - R (T.rangeRestrict v)) = 0 := by
      rw [hQ, map_sub, hTR]
      simp
    have := hg _ h1
    rw [map_sub, sub_eq_zero] at this
    exact this
  obtain ⟨z, hz⟩ : ∃ z : LinearMap.range T, ∀ y : LinearMap.range T, g (R y) = ⟪z, y⟫_ℝ := by
    refine ⟨(InnerProductSpace.toDual ℝ (LinearMap.range T)).symm (LinearMap.toContinuousLinearMap (g ∘ₗ R)), fun y => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : StrongDual ℝ (EuclideanSpace ℝ ι), ℓ = innerSL ℝ (z : EuclideanSpace ℝ ι) := ⟨_, rfl⟩
  have hgΨ : (g ∘ Ψ) = ℓ := by
    funext ξ
    simp only [Function.comp, hΨ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hz, hℓ, innerSL_apply_apply]
    rw [hP, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have hgm : Measurable g := (LinearMap.continuous_of_finiteDimensional g).measurable
  have hvar : gaussianVariance Q g = ‖(z : EuclideanSpace ℝ ι)‖ ^ 2 := by
    have hgv : ∀ v, g v = ⟪(z : EuclideanSpace ℝ ι), T v⟫_ℝ := by
      intro v
      rw [hgR, hz]
      rfl
    unfold gaussianVariance
    rcases eq_or_ne (z : EuclideanSpace ℝ ι) 0 with h0 | h0
    · have hall : ∀ t ∈ {t | ∃ v, 0 < Q v ∧ t = g v ^ 2 / Q v}, t = 0 := by
        rintro t ⟨v, -, rfl⟩
        rw [hgv, h0]
        simp
      rw [h0, norm_zero]
      have h2 : sSup {t | ∃ v, 0 < Q v ∧ t = g v ^ 2 / Q v} = 0 :=
        le_antisymm (Real.sSup_nonpos fun t ht => (hall t ht).le) (Real.sSup_nonneg fun t ht => (hall t ht).ge)
      rw [h2]
      simp
    · have hpos : 0 < ‖(z : EuclideanSpace ℝ ι)‖ ^ 2 := by
        have := norm_pos_iff.mpr h0
        positivity
      have hgreat : IsGreatest {t | ∃ v, 0 < Q v ∧ t = g v ^ 2 / Q v} (‖(z : EuclideanSpace ℝ ι)‖ ^ 2) := by
        constructor
        · refine ⟨R z, ?_, ?_⟩
          · rw [hQ, hTR]
            exact hpos
          · rw [hQ, hTR, hz, real_inner_self_eq_norm_sq]
            simp only [Submodule.coe_norm]
            field_simp
        · rintro t ⟨v, hv, rfl⟩
          rw [div_le_iff₀ hv, hgv, hQ, ← mul_pow, ← sq_abs (⟪(z : EuclideanSpace ℝ ι), T v⟫_ℝ)]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
      exact hgreat.csSup_eq
  rw [Measure.map_map hgm hΨc.measurable, hgΨ, IsGaussian.map_eq_gaussianReal ℓ, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, hvar, hℓ, innerSL_apply_norm]
section LevelChains
variable {L : ℕ} [NeZero L]
private theorem finite_levelBond : ∀ (s n : ℕ) [NeZero n], Finite (LevelBond L s n)
  | 0, n, _ => inferInstanceAs (Finite (TorusFields.TorusBond n))
  | s + 1, n, _ => by
    haveI := finite_levelBond s (n * L)
    exact inferInstanceAs (Finite (LevelBond L s (n * L) ⊕ TorusFields.TorusBond n))
private theorem sumAlongWord_add {m : ℕ} (A B : TorusFields.TorusBond m → ℝ) (w : TorusPaths.BondWord m) :
    sumAlongWord (A + B) w = sumAlongWord A w + sumAlongWord B w := by
  unfold sumAlongWord
  rw [← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Pi.add_apply]
  split_ifs <;> ring
abbrev _root_.YangMills.SharedProofs.p21609 := @sumAlongWord_add
private theorem sumAlongWord_smul {m : ℕ} (r : ℝ) (A : TorusFields.TorusBond m → ℝ) (w : TorusPaths.BondWord m) :
    sumAlongWord (r • A) w = r * sumAlongWord A w := by
  unfold sumAlongWord
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring
abbrev _root_.YangMills.SharedProofs.p11298 := @sumAlongWord_smul
private theorem contourAverage_add {n : ℕ} [NeZero n] (A B : TorusFields.TorusBond (n * L) → ℝ) (c : TorusFields.TorusBond n) :
    contourAverage L (A + B) c = contourAverage L A c + contourAverage L B c := by
  unfold contourAverage
  rw [← mul_add, ← Finset.sum_add_distrib]
  simp only [sumAlongWord_add]
private theorem contourAverage_smul {n : ℕ} [NeZero n] (r : ℝ) (A : TorusFields.TorusBond (n * L) → ℝ) (c : TorusFields.TorusBond n) :
    contourAverage L (r • A) c = r * contourAverage L A c := by
  unfold contourAverage
  simp only [sumAlongWord_smul, ← Finset.mul_sum]
  ring
abbrev _root_.YangMills.SharedProofs.p14469 := @contourAverage_smul
private def chainLowerLinear (s n : ℕ) : LevelChain L (s + 1) n →ₗ[ℝ] LevelChain L s (n * L) where
  toFun := chainLower
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private theorem chainTop_add' : ∀ (s n : ℕ) (X Y : LevelChain L s n), chainTop s n (X + Y) = chainTop s n X + chainTop s n Y
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainTop_smul' : ∀ (s n : ℕ) (r : ℝ) (X : LevelChain L s n), chainTop s n (r • X) = r • chainTop s n X
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private def defectFunctional (s n : ℕ) [NeZero n] (e : Fin 3) (c : TorusFields.TorusBond n) : LevelChain L (s + 1) n →ₗ[ℝ] ℝ where
  toFun X := chainDefect X e c
  map_add' X Y := by
    unfold chainDefect
    have h1 : chainLower (X + Y) = chainLower X + chainLower Y := rfl
    have h2 := contourAverage_add (L := L) (chainTop s (n * L) (chainLower X) e) (chainTop s (n * L) (chainLower Y) e) c
    rw [h1, chainTop_add', chainTop_add']
    simp only [Pi.add_apply]
    rw [h2]
    ring
  map_smul' r X := by
    unfold chainDefect
    have h1 : chainLower (r • X) = r • chainLower X := rfl
    have h2 := contourAverage_smul (L := L) r (chainTop s (n * L) (chainLower X) e) c
    rw [h1, chainTop_smul', chainTop_smul']
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [h2]
    ring
private theorem curl_add' {n : ℕ} (A B : TorusFields.TorusBond n → ℝ) (p : TorusFields.TorusPlaquette n) :
    WeightedResponses.curl (A + B) p = WeightedResponses.curl A p + WeightedResponses.curl B p := by
  simp only [WeightedResponses.curl, Pi.add_apply]
  ring
abbrev _root_.YangMills.SharedProofs.p35838 := @curl_add'
private theorem curl_smul' {n : ℕ} (r : ℝ) (A : TorusFields.TorusBond n → ℝ) (p : TorusFields.TorusPlaquette n) :
    WeightedResponses.curl (r • A) p = r * WeightedResponses.curl A p := by apply _root_.YangMills.SharedProofs.p39240 <;> assumption
private def plaquetteCurlMap (n : ℕ) (e : Fin 3) (p : TorusFields.TorusPlaquette n) : LevelChain L 0 n →ₗ[ℝ] ℝ where
  toFun X := WeightedResponses.curl (X e) p
  map_add' X Y := curl_add' (X e) (Y e) p
  map_smul' r X := curl_smul' r (X e) p
private theorem levelEnergy_eq_sum_sq {a : ℝ} (ha : 0 < a) : ∀ (s n : ℕ) [NeZero n], ∃ (ι : Type) (_ : Fintype ι) (T : LevelChain L s n →ₗ[ℝ] (ι → ℝ)),
    ∀ X, levelEnergy a s n X = ∑ i, T X i ^ 2
  | 0, n, _ => by
    classical
    refine ⟨{p // p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n))} × Fin 3, inferInstance,
      LinearMap.pi fun q => plaquetteCurlMap n q.2 q.1.1, fun X => ?_⟩
    rw [Fintype.sum_prod_type]
    simp only [levelEnergy, LinearMap.pi_apply, plaquetteCurlMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold curlNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rfl
  | s + 1, n, _ => by
    classical
    obtain ⟨ι, hι, T, hT⟩ := levelEnergy_eq_sum_sq ha s (n * L)
    refine ⟨ι ⊕ (TorusFields.TorusBond n × Fin 3), inferInstance,
      LinearMap.pi fun q => Sum.elim (fun i => (LinearMap.proj i).comp (T.comp (chainLowerLinear s n)))
        (fun r => Real.sqrt a • defectFunctional s n r.2 r.1) q, fun X => ?_⟩
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [levelEnergy, LinearMap.pi_apply, Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt ha.le]
    rw [hT, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    rfl
end LevelChains
theorem levelChainCanonicalGaussian : levelChainCanonicalGaussianStatement := by
  intro L _ a ha s n _
  obtain ⟨ι, hι, T, hT⟩ := levelEnergy_eq_sum_sq (L := L) ha s n
  haveI := finite_levelBond (L := L) s n
  refine exists_isCanonicalGaussian_of_sq_norm (((WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι) ∘ₗ T) _ fun X => ?_
  rw [hT, EuclideanSpace.norm_sq_eq]
  simp
end YangMills.Construction.MomentLaw
end
