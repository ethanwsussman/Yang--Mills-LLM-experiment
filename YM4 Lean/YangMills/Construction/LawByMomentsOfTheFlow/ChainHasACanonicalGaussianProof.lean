import YangMills.Construction.LawByMomentsOfTheFlow.ChainHasACanonicalGaussian
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainHasItsGaussianProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusPaths WeightedResponses
private def IsSumOfSquares {V : Type} [AddCommGroup V] [Module ℝ V] (Q : V → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (φ : ι → V →ₗ[ℝ] ℝ), ∀ x, Q x = ∑ i, φ i x ^ 2
private theorem exists_isCanonicalGaussian_of_sum_sq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] (φ : ι → V →ₗ[ℝ] ℝ) (Q : V → ℝ)
    (hQ : ∀ x, Q x = ∑ i, φ i x ^ 2) : ∃ μ : Measure V, IsCanonicalGaussian Q μ := by
  classical
  let T : V →ₗ[ℝ] EuclideanSpace ℝ ι := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap ∘ₗ LinearMap.pi φ
  have hT : ∀ x, Q x = ‖T x‖ ^ 2 := by
    intro x
    rw [hQ, EuclideanSpace.norm_sq_eq]
    simp [T]
  obtain ⟨S, hS⟩ := T.rangeRestrict.exists_rightInverse_of_surjective T.range_rangeRestrict
  let P : EuclideanSpace ℝ ι →ₗ[ℝ] LinearMap.range T := (LinearMap.range T).orthogonalProjectionOnto.toLinearMap
  let G : EuclideanSpace ℝ ι →ₗ[ℝ] V := S ∘ₗ P
  have hGm : Measurable G := G.continuous_of_finiteDimensional.measurable
  have hTS : ∀ r : LinearMap.range T, T (S r) = r := by
    intro r
    have := congrArg (fun g => (g r : LinearMap.range T)) hS
    simpa using congrArg Subtype.val this
  have hTG : ∀ x, T (G (T x)) = T x := by
    intro x
    have hP : P (T x) = ⟨T x, LinearMap.mem_range_self T x⟩ :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨T x, LinearMap.mem_range_self T x⟩ : LinearMap.range T)
    simp only [G, LinearMap.comp_apply, hP, hTS]
  refine ⟨(stdGaussian (EuclideanSpace ℝ ι)).map G, ?_, ?_⟩
  · exact Measure.isProbabilityMeasure_map hGm.aemeasurable
  intro f hf
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  let ψ : StrongDual ℝ (EuclideanSpace ℝ ι) := LinearMap.toContinuousLinearMap (f ∘ₗ G)
  let w : EuclideanSpace ℝ ι := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm ψ
  have hw : ∀ v, f (G v) = inner ℝ w v := by
    intro v
    have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := v) (y := ψ)
    rw [this]
    rfl
  have hfT : ∀ x, f x = inner ℝ w (T x) := by
    intro x
    rw [← hw]
    have h0 : f (x - G (T x)) = 0 := by
      apply hf
      rw [hT, map_sub, hTG, sub_self]
      simp
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  have hwR : w ∈ LinearMap.range T := by
    have h2 : w ∈ (LinearMap.range T)ᗮᗮ := by
      rw [Submodule.mem_orthogonal]
      intro v hv
      have hPv : P v = 0 := Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv
      rw [real_inner_comm, ← hw]
      simp [G, hPv]
    rwa [Submodule.orthogonal_orthogonal] at h2
  obtain ⟨x₀, hx₀⟩ := hwR
  have hvar : gaussianVariance Q f = ‖w‖ ^ 2 := by
    have hb : ∀ r ∈ {r | ∃ x, 0 < Q x ∧ r = f x ^ 2 / Q x}, r ≤ ‖w‖ ^ 2 := by
      rintro r ⟨x, hx, rfl⟩
      rw [div_le_iff₀ hx, hT x, hfT x, ← mul_pow]
      exact sq_le_sq' (by
        have := abs_real_inner_le_norm w (T x)
        linarith [neg_abs_le (inner ℝ w (T x))]) (by
        have := abs_real_inner_le_norm w (T x)
        linarith [le_abs_self (inner ℝ w (T x))])
    apply le_antisymm (Real.sSup_le hb (by positivity))
    by_cases hw0 : w = 0
    · rw [hw0, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      apply Real.sSup_nonneg
      rintro r ⟨x, hx, rfl⟩
      exact div_nonneg (sq_nonneg _) hx.le
    · have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
      have hQ₀ : Q x₀ = ‖w‖ ^ 2 := by rw [hT, hx₀]
      refine le_csSup ⟨_, hb⟩ ⟨x₀, by rw [hQ₀]; positivity, ?_⟩
      rw [hQ₀, hfT, hx₀, real_inner_self_eq_norm_sq]
      field_simp
  have hmap : ((stdGaussian (EuclideanSpace ℝ ι)).map G).map f = (stdGaussian (EuclideanSpace ℝ ι)).map ψ := by
    rw [Measure.map_map hfm hGm]
    rfl
  have hn : ‖ψ‖ = ‖w‖ := by
    have : ψ = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι) w := by simp [w]
    rw [this, LinearIsometryEquiv.norm_map]
  rw [hmap, hvar, IsGaussian.map_eq_gaussianReal ψ, integral_strongDual_stdGaussian, variance_dual_stdGaussian, hn]
section Linearity
variable {m : ℕ}
private theorem sumAlongWord_add (A B : TorusBond m → ℝ) (γ : BondWord m) :
    sumAlongWord (A + B) γ = sumAlongWord A γ + sumAlongWord B γ := by apply _root_.YangMills.SharedProofs.p21609 <;> assumption
private theorem sumAlongWord_smul (r : ℝ) (A : TorusBond m → ℝ) (γ : BondWord m) :
    sumAlongWord (r • A) γ = r * sumAlongWord A γ := by apply _root_.YangMills.SharedProofs.p11298 <;> assumption
variable (L : ℕ) {n : ℕ} [NeZero n]
private theorem contourAverage_add (A B : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    contourAverage L (A + B) c = contourAverage L A c + contourAverage L B c := by
  simp only [contourAverage, sumAlongWord_add, Finset.sum_add_distrib, mul_add]
private theorem contourAverage_smul (r : ℝ) (A : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    contourAverage L (r • A) c = r * contourAverage L A c := by
  simp only [contourAverage, sumAlongWord_smul, ← Finset.mul_sum]
  ring
end Linearity
variable {L : ℕ} [NeZero L]
private theorem chainTop_add : ∀ (s n : ℕ) (X Y : LevelChain L s n), chainTop s n (X + Y) = chainTop s n X + chainTop s n Y
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem chainTop_smul : ∀ (s n : ℕ) (r : ℝ) (X : LevelChain L s n), chainTop s n (r • X) = r • chainTop s n X
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private def chainLowerₗ (s n : ℕ) : LevelChain L (s + 1) n →ₗ[ℝ] LevelChain L s (n * L) where
  toFun := chainLower
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def chainDefectₗ (s n : ℕ) [NeZero n] (e : Fin 3) (c : TorusBond n) : LevelChain L (s + 1) n →ₗ[ℝ] ℝ where
  toFun X := chainDefect X e c
  map_add' X Y := by
    have hb : chainLower (X + Y) = chainLower X + chainLower Y := rfl
    simp only [chainDefect, hb, chainTop_add, Pi.add_apply]
    rw [contourAverage_add]
    ring
  map_smul' r X := by
    have hb : chainLower (r • X) = r • chainLower X := rfl
    simp only [chainDefect, hb, chainTop_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [contourAverage_smul]
    ring
private theorem curl_add {n : ℕ} (A B : TorusBond n → ℝ) (p : TorusPlaquette n) : curl (A + B) p = curl A p + curl B p := by apply _root_.YangMills.SharedProofs.p35838 <;> assumption
private theorem curl_smul {n : ℕ} (r : ℝ) (A : TorusBond n → ℝ) (p : TorusPlaquette n) : curl (r • A) p = r * curl A p := by apply _root_.YangMills.SharedProofs.p39240 <;> assumption
private def curlₗ (n : ℕ) (e : Fin 3) (p : TorusPlaquette n) : LevelChain L 0 n →ₗ[ℝ] ℝ where
  toFun X := curl (chainTop 0 n X e) p
  map_add' X Y := curl_add (X e) (Y e) p
  map_smul' r X := curl_smul r (X e) p
private theorem levelEnergy_isSumOfSquares (a : ℝ) (ha : 0 ≤ a) :
    ∀ (s n : ℕ) [NeZero n], IsSumOfSquares (levelEnergy (L := L) a s n)
  | 0, n, _ => by
    refine ⟨{p // p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n))} × Fin 3, inferInstance,
      fun i => curlₗ n i.2 i.1.1, fun X => ?_⟩
    rw [Fintype.sum_prod_type, levelEnergy, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [curlNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rfl
  | s + 1, n, _ => by
    obtain ⟨ι, _, φ, h⟩ := levelEnergy_isSumOfSquares a ha s (n * L)
    refine ⟨ι ⊕ (TorusBond n × Fin 3), inferInstance,
      Sum.elim (fun i => φ i ∘ₗ chainLowerₗ s n) (fun i => Real.sqrt a • chainDefectₗ s n i.2 i.1), fun X => ?_⟩
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, levelEnergy, h, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Sum.elim_inr, LinearMap.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt ha]
    rfl
private theorem finite_levelBond (M : ℕ) [NeZero M] : ∀ (s n : ℕ) [NeZero n], Finite (LevelBond M s n)
  | 0, n, _ => inferInstanceAs (Finite (TorusBond n))
  | s + 1, n, _ => by
    have := finite_levelBond M s (n * M)
    exact inferInstanceAs (Finite (LevelBond M s (n * M) ⊕ TorusBond n))
theorem canonicalGaussian_exists : canonicalGaussianExistsStatement := by
  intro L _ a ha s n _
  have := finite_levelBond L s n
  letI := Fintype.ofFinite (LevelBond L s n)
  obtain ⟨ι, _, φ, h⟩ := levelEnergy_isSumOfSquares (L := L) a ha s n
  exact exists_isCanonicalGaussian_of_sum_sq φ _ h
end YangMills.Construction.MomentLaw
end
