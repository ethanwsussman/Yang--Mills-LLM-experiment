import YangMills.Construction.LawByMomentsOfTheFlow.EnergyOfAChainHasACanonicalGaussian
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainHasItsGaussianProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
section SumsOfSquares
variable {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
private def IsSumOfSquares (E : V → ℝ) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (l : J → V →ₗ[ℝ] ℝ), ∀ x, E x = ∑ j, l j x ^ 2
private theorem isSumOfSquares_zero : IsSumOfSquares (fun _ : V => (0 : ℝ)) :=
  ⟨Empty, inferInstance, Empty.elim, fun _ => by simp⟩
private theorem IsSumOfSquares.congr {E E' : V → ℝ} (h : IsSumOfSquares E) (hE : ∀ x, E' x = E x) :
    IsSumOfSquares E' := by
  obtain ⟨J, i, l, hl⟩ := h
  exact ⟨J, i, l, fun x => by rw [hE, hl]⟩
private theorem IsSumOfSquares.add {E E' : V → ℝ} (h : IsSumOfSquares E) (h' : IsSumOfSquares E') :
    IsSumOfSquares (fun x => E x + E' x) := by
  obtain ⟨J, i, l, hl⟩ := h
  obtain ⟨J', i', l', hl'⟩ := h'
  exact ⟨J ⊕ J', inferInstance, Sum.elim l l', fun x => by simp [hl, hl', Fintype.sum_sum_type]⟩
private theorem isSumOfSquares_finsetSum {ι : Type} (s : Finset ι) {E : ι → V → ℝ}
    (h : ∀ i ∈ s, IsSumOfSquares (E i)) : IsSumOfSquares (fun x => ∑ i ∈ s, E i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isSumOfSquares_zero.congr fun x => by simp
  | insert i s hi ih =>
    refine ((h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr fun x => ?_
    rw [Finset.sum_insert hi]
private theorem isSumOfSquares_sq (l : V →ₗ[ℝ] ℝ) : IsSumOfSquares (fun x => l x ^ 2) :=
  ⟨Unit, inferInstance, fun _ => l, fun _ => by simp⟩
private theorem IsSumOfSquares.const_mul {E : V → ℝ} (h : IsSumOfSquares E) {a : ℝ} (ha : 0 ≤ a) :
    IsSumOfSquares (fun x => a * E x) := by
  obtain ⟨J, i, l, hl⟩ := h
  refine ⟨J, i, fun j => Real.sqrt a • l j, fun x => ?_⟩
  show a * E x = _
  rw [hl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt ha]
private theorem IsSumOfSquares.comp {E : V → ℝ} (h : IsSumOfSquares E) (A : W →ₗ[ℝ] V) :
    IsSumOfSquares (fun x => E (A x)) := by
  obtain ⟨J, i, l, hl⟩ := h
  exact ⟨J, i, fun j => (l j).comp A, fun x => (hl (A x)).trans rfl⟩
end SumsOfSquares
section Gaussian
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]
private theorem exists_isCanonicalGaussian_of_isSumOfSquares {E : V → ℝ} (h : IsSumOfSquares E) :
    ∃ μ : Measure V, IsCanonicalGaussian E μ := by
  obtain ⟨J, _, l, hl⟩ := h
  let T : V →ₗ[ℝ] EuclideanSpace ℝ J := (WithLp.linearEquiv 2 ℝ (J → ℝ)).symm.toLinearMap ∘ₗ LinearMap.pi l
  have hT : ∀ x, E x = ‖T x‖ ^ 2 := by
    intro x
    rw [hl, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    rfl
  obtain ⟨S, hS⟩ := T.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict T)
  have hTS : ∀ w : LinearMap.range T, T.rangeRestrict (S w) = w := fun w => LinearMap.congr_fun hS w
  have hSc : Continuous S := S.continuous_of_finiteDimensional
  refine ⟨(stdGaussian (LinearMap.range T)).map S,
    ⟨Measure.isProbabilityMeasure_map hSc.aemeasurable, fun f hf => ?_⟩⟩
  have hfac : ∀ x, f x = f (S (T.rangeRestrict x)) := by
    intro x
    have h0 : E (x - S (T.rangeRestrict x)) = 0 := by
      have h1 : T (x - S (T.rangeRestrict x)) = 0 := by
        have h2 : T (S (T.rangeRestrict x)) = T x := congrArg Subtype.val (hTS (T.rangeRestrict x))
        rw [map_sub, h2, sub_self]
      rw [hT, h1, norm_zero]
      norm_num
    have h3 := hf _ h0
    rw [map_sub, sub_eq_zero] at h3
    exact h3
  let g : StrongDual ℝ (LinearMap.range T) := (f ∘ₗ S).toContinuousLinearMap
  let v : LinearMap.range T := (InnerProductSpace.toDual ℝ (LinearMap.range T)).symm g
  have hgv : ∀ w, f (S w) = inner ℝ v w := fun w =>
    (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := w) (y := g)).symm
  have hn : ‖v‖ = ‖g‖ := (InnerProductSpace.toDual ℝ (LinearMap.range T)).symm.norm_map g
  have hfv : ∀ x, f x = inner ℝ v (T.rangeRestrict x) := fun x => by rw [hfac x, hgv]
  have hnorm : ∀ x, ‖T.rangeRestrict x‖ = ‖T x‖ := fun _ => rfl
  have hvar : gaussianVariance E f = ‖g‖ ^ 2 := by
    unfold gaussianVariance
    rw [← hn]
    by_cases hv : v = 0
    · have hall : ∀ w ∈ {w | ∃ x, 0 < E x ∧ w = f x ^ 2 / E x}, w = 0 := by
        rintro w ⟨x, -, rfl⟩
        rw [hfv x, hv]
        simp
      rw [hv, norm_zero]
      norm_num
      exact le_antisymm (Real.sSup_le (fun w hw => (hall w hw).le) le_rfl)
        (Real.sSup_nonneg fun w hw => (hall w hw).ge)
    · have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hgreat : IsGreatest {w | ∃ x, 0 < E x ∧ w = f x ^ 2 / E x} (‖v‖ ^ 2) := by
        constructor
        · have hE : E (S v) = ‖v‖ ^ 2 := by
            rw [hT, ← hnorm, hTS]
          refine ⟨S v, by rw [hE]; positivity, ?_⟩
          rw [hE, hgv, real_inner_self_eq_norm_sq]
          field_simp
        · rintro w ⟨x, hx, rfl⟩
          rw [div_le_iff₀ hx, hT x, ← hnorm, hfv x]
          have h1 := abs_real_inner_le_norm v (T.rangeRestrict x)
          have h2 := sq_le_sq' (by linarith [abs_nonneg (inner ℝ v (T.rangeRestrict x)), neg_abs_le (inner ℝ v (T.rangeRestrict x))]) ((le_abs_self _).trans h1)
          rw [mul_pow] at h2
          exact h2
      exact hgreat.csSup_eq
  have hfm : Measurable f := (f.continuous_of_finiteDimensional).measurable
  have hmap : ((stdGaussian (LinearMap.range T)).map S).map f = (stdGaussian (LinearMap.range T)).map g := by
    rw [Measure.map_map hfm hSc.measurable]
    rfl
  rw [hmap, IsGaussian.map_eq_gaussianReal g, integral_strongDual_stdGaussian, variance_dual_stdGaussian, hvar]
end Gaussian
section Levels
variable {L : ℕ} [NeZero L]
private theorem sumAlongWord_add {m : ℕ} (A B : TorusFields.TorusBond m → ℝ) (w : TorusPaths.BondWord m) :
    sumAlongWord (A + B) w = sumAlongWord A w + sumAlongWord B w := by apply _root_.YangMills.SharedProofs.p21609 <;> assumption
private theorem sumAlongWord_smul {m : ℕ} (c : ℝ) (A : TorusFields.TorusBond m → ℝ) (w : TorusPaths.BondWord m) :
    sumAlongWord (c • A) w = c * sumAlongWord A w := by apply _root_.YangMills.SharedProofs.p11298 <;> assumption
private def chainTopLinear (s n : ℕ) : LevelChain L s n →ₗ[ℝ] ColourForm n where
  toFun := chainTop s n
  map_add' X Y := by cases s <;> rfl
  map_smul' c X := by cases s <;> rfl
private def chainLowerLinear (s n : ℕ) : LevelChain L (s + 1) n →ₗ[ℝ] LevelChain L s (n * L) where
  toFun := chainLower
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def curlLinear {n : ℕ} (e : Fin 3) (p : TorusFields.TorusPlaquette n) : ColourForm n →ₗ[ℝ] ℝ where
  toFun X := WeightedResponses.curl (X e) p
  map_add' X Y := by
    simp only [WeightedResponses.curl, Pi.add_apply]
    ring
  map_smul' c X := by
    simp only [WeightedResponses.curl, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
private def contourAverageLinear {n : ℕ} [NeZero n] (e : Fin 3) (c : TorusFields.TorusBond n) :
    ColourForm (n * L) →ₗ[ℝ] ℝ where
  toFun X := contourAverage L (X e) c
  map_add' X Y := by
    simp only [contourAverage, Pi.add_apply, sumAlongWord_add, Finset.sum_add_distrib]
    ring
  map_smul' r X := by
    simp only [contourAverage, Pi.smul_apply, sumAlongWord_smul, RingHom.id_apply, smul_eq_mul, ← Finset.mul_sum]
    ring
private def fluctuationLinear (s n : ℕ) [NeZero n] (e : Fin 3) (c : TorusFields.TorusBond n) :
    LevelChain L (s + 1) n →ₗ[ℝ] ℝ :=
  (LinearMap.proj c ∘ₗ LinearMap.proj e) ∘ₗ chainTopLinear (s + 1) n -
    contourAverageLinear e c ∘ₗ chainTopLinear s (n * L) ∘ₗ chainLowerLinear s n
private theorem isSumOfSquares_levelEnergy (a : ℝ) (ha : 0 ≤ a) :
    ∀ (s n : ℕ) [NeZero n], IsSumOfSquares (levelEnergy (L := L) a s n) := by
  intro s
  induction s with
  | zero =>
    intro n _
    refine (isSumOfSquares_finsetSum (TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)))
      (E := fun p X => ∑ e : Fin 3, (curlLinear e p ∘ₗ chainTopLinear (L := L) 0 n) X ^ 2) fun p _ =>
        isSumOfSquares_finsetSum Finset.univ fun e _ => isSumOfSquares_sq _).congr fun X => ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [curlNorm, Real.sq_sqrt (Finset.sum_nonneg fun e _ => sq_nonneg _)]
    rfl
  | succ s ih =>
    intro n _
    refine (((ih (n * L)).comp (chainLowerLinear s n)).add
      ((isSumOfSquares_finsetSum (Finset.univ : Finset (TorusFields.TorusBond n)) (E := fun c X =>
        ∑ e : Fin 3, fluctuationLinear (L := L) s n e c X ^ 2) fun c _ =>
          isSumOfSquares_finsetSum Finset.univ fun e _ => isSumOfSquares_sq _).const_mul ha)).congr fun X => ?_
    rfl
@[instance_reducible] private def levelBondFintype (L : ℕ) [NeZero L] :
    (s n : ℕ) → [NeZero n] → Fintype (LevelBond L s n)
  | 0, n, _ => inferInstanceAs (Fintype (TorusFields.TorusBond n))
  | s + 1, n, _ =>
    letI := levelBondFintype L s (n * L)
    inferInstanceAs (Fintype (LevelBond L s (n * L) ⊕ TorusFields.TorusBond n))
end Levels
theorem levelEnergy_has_canonicalGaussian : levelEnergyCanonicalGaussianStatement := by
  intro a ha L s n _ _
  let _ := levelBondFintype L s n
  exact exists_isCanonicalGaussian_of_isSumOfSquares (isSumOfSquares_levelEnergy a ha s n)
end YangMills.Construction.MomentLaw
end
