import YangMills.Construction.EuclideanAnalysis.ParametrixOfTheCubedLaplacianProof
import YangMills.Construction.LawByMomentsOfTheFlow.FourPointsNearALine
import YangMills.Construction.LawByMomentsOfTheFlow.OddProductsOfReflections
import YangMills.Construction.LawByMomentsOfTheFlow.TorusSumNearTheLatticeNumberProof
import YangMills.Construction.Torus.QuadruplesAboutCollinearCentres
import YangMills.Construction.TotalDensitiesGiveASystem.TheCyclicFormulaAtSeparatedTuples
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
namespace SeparatedTuples
private def liftToEuclidean (f : (Fin 4 → ℝ) → ℝ) : TestFunctions.EuclideanFourSpace → ℝ :=
  fun x => f (WithLp.ofLp x)
private theorem tsupport_liftToEuclidean (f : (Fin 4 → ℝ) → ℝ) {x : TestFunctions.EuclideanFourSpace}
    (hx : x ∈ tsupport (liftToEuclidean f)) : WithLp.ofLp x ∈ tsupport f :=
  tsupport_comp_subset_preimage f (PiLp.continuous_ofLp 2 _) hx
private theorem ne_add_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) (c : Fin n) : c ≠ c + 1 := by apply _root_.YangMills.SharedProofs.p48899 <;> assumption
private theorem cyclicMomentFormula_odd_eq_zero (hO : CyclicFormula.ExteriorSquareTraceOfOddInversionProduct)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (hodd : Odd n) (X : TestSpaces.SepTupleOfCard n) :
    CyclicFormula.cyclicMomentFormula n (fun k x => X.1 k (WithLp.ofLp x)) = 0 := by
  have hz : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → TestFunctions.EuclideanFourSpace),
      (∏ i, liftToEuclidean (X.1 i) (x i)) * CyclicFormula.cycleKernel σ x = 0 := by
    intro σ x
    by_cases hp : ∏ i, liftToEuclidean (X.1 i) (x i) = 0
    · rw [hp, zero_mul]
    have hall : ∀ i, X.1 i (WithLp.ofLp (x i)) ≠ 0 := fun i h => hp (Finset.prod_eq_zero (Finset.mem_univ i) h)
    have hne : ∀ c : Fin n, x (σ c) - x (σ (c + 1)) ≠ 0 := by
      intro c h
      have hneq : σ c ≠ σ (c + 1) := fun h' => ne_add_one hn c (σ.injective h')
      have hxy : x (σ c) = x (σ (c + 1)) := sub_eq_zero.1 h
      have h1 := subset_tsupport _ (hall (σ c))
      have h2 := subset_tsupport _ (hall (σ (c + 1)))
      rw [← hxy] at h2
      exact Set.disjoint_left.1 (X.2.2 hneq) h1 h2
    have ht : CyclicFormula.exteriorSquareTrace
        ((List.ofFn fun c : Fin n => x (σ c) - x (σ (c + 1))).map CyclicFormula.inversionMatrix).prod = 0 :=
      hO.2 _ (by simpa using hodd) (by
        intro v hv
        obtain ⟨c, rfl⟩ := (List.mem_ofFn' _ _).mp hv
        exact hne c)
    rw [List.map_ofFn] at ht
    have h4 : CyclicFormula.exteriorSquareTrace
        (List.ofFn fun c : Fin n => CyclicFormula.inversionMatrix (x (σ c) - x (σ (c + 1)))).prod = 0 := ht
    simp only [CyclicFormula.cycleKernel, h4, mul_zero]
  unfold CyclicFormula.cyclicMomentFormula
  rw [Finset.sum_eq_zero, mul_zero]
  intro σ _
  have hz' : ∀ x : Fin n → TestFunctions.EuclideanFourSpace,
      (∏ i, X.1 i (WithLp.ofLp (x i))) * CyclicFormula.cycleKernel σ x = 0 := hz σ
  simp only [hz', integral_zero]
private theorem cyclicMomentFormula_const_mul (c : ℝ) (φ : Fin 4 → TestFunctions.EuclideanFourSpace → ℝ) :
    CyclicFormula.cyclicMomentFormula 4 (fun i x => c * φ i x) = c ^ 4 * CyclicFormula.cyclicMomentFormula 4 φ := by
  have h : ∀ (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → TestFunctions.EuclideanFourSpace),
      (∏ i, c * φ i (x i)) * CyclicFormula.cycleKernel σ x
        = c ^ 4 * ((∏ i, φ i (x i)) * CyclicFormula.cycleKernel σ x) := by
    intro σ x
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_assoc]
  unfold CyclicFormula.cyclicMomentFormula
  simp only [h, integral_const_mul, ← Finset.mul_sum]
  ring
private theorem abs_sub_coord_le_supDist (x y : TestFunctions.EuclideanFourSpace) (a : Fin 4) :
    |x a - y a| ≤ MomentLaw.supDist x y :=
  le_ciSup (f := fun a : Fin 4 => |x a - y a|) (Set.finite_range _).bddAbove a
private theorem dist_le_two_mul_supDist (x y : TestFunctions.EuclideanFourSpace) :
    dist x y ≤ 2 * MomentLaw.supDist x y := by
  have hD : 0 ≤ MomentLaw.supDist x y := (abs_nonneg _).trans (abs_sub_coord_le_supDist x y 0)
  rw [EuclideanSpace.dist_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ a, dist (x a) (y a) ^ 2 ≤ ∑ _a : Fin 4, MomentLaw.supDist x y ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Real.dist_eq]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_coord_le_supDist x y a) 2
    _ = (2 * MomentLaw.supDist x y) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
private theorem tsupport_const_mul_subset (c : ℝ) (f : TestFunctions.EuclideanFourSpace → ℝ) :
    tsupport (fun x => c * f x) ⊆ tsupport f :=
  closure_mono fun x hx h => hx (by simp [h])
private theorem exists_scaled_isSupTestFamily {φ : Fin 4 → TestFunctions.EuclideanFourSpace → ℝ}
    (hl : ∀ i, ∃ C, LipschitzWith C (φ i)) (hc : ∀ i, HasCompactSupport (φ i))
    (ha : ∀ i j, i ≠ j → ∀ x ∈ tsupport (φ i), ∀ y ∈ tsupport (φ j), 1 ≤ dist x y) :
    ∃ c R : ℝ, 0 < c ∧ MomentLaw.IsSupTestFamily R (1 / 2) (fun i x => c * φ i x) := by
  choose C hC using hl
  have hb : ∀ i, ∃ M : ℝ, ∀ x, ‖φ i x‖ ≤ M := fun i => (hC i).continuous.bounded_above_of_compact_support (hc i)
  choose M hM using hb
  have hr : ∀ i, ∃ r : ℝ, tsupport (φ i) ⊆ Metric.closedBall 0 r := fun i =>
    (hc i).isCompact.isBounded.subset_closedBall 0
  choose r hr using hr
  have hterm : ∀ i, 0 ≤ |M i| + 2 * (C i : ℝ) := fun i => by positivity
  set A : ℝ := ∑ i, (|M i| + 2 * (C i : ℝ)) + 1 with hAdef
  have hA : ∀ i, |M i| + 2 * (C i : ℝ) ≤ A := fun i => by
    have := Finset.single_le_sum (f := fun i => |M i| + 2 * (C i : ℝ)) (fun i _ => hterm i) (Finset.mem_univ i)
    linarith
  have hA0 : 0 < A := by
    have : 0 ≤ ∑ i, (|M i| + 2 * (C i : ℝ)) := Finset.sum_nonneg fun i _ => hterm i
    linarith
  have hR : ∀ i, r i ≤ ∑ i, |r i| := fun i => by
    have := Finset.single_le_sum (f := fun i => |r i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    exact (le_abs_self _).trans this
  have hcb : ∀ i x, |A⁻¹ * φ i x| ≤ 1 := fun i x => by
    rw [abs_mul, abs_of_pos (inv_pos.2 hA0), inv_mul_le_iff₀ hA0, mul_one]
    have h1 : |φ i x| ≤ M i := hM i x
    have h2 := hA i
    have h3 := le_abs_self (M i)
    have h4 : (0 : ℝ) ≤ C i := by positivity
    linarith
  have hcl : ∀ i x y, |A⁻¹ * φ i x - A⁻¹ * φ i y| ≤ 1 / 2 * dist x y := fun i x y => by
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hA0), inv_mul_le_iff₀ hA0]
    have h1 : |φ i x - φ i y| ≤ C i * dist x y := by
      rw [← Real.dist_eq]
      exact (hC i).dist_le_mul x y
    have h2 := hA i
    have h3 : 2 * (C i : ℝ) ≤ A := by
      have := abs_nonneg (M i)
      linarith
    have h4 : 0 ≤ dist x y := dist_nonneg
    nlinarith
  refine ⟨A⁻¹, ∑ i, |r i|, inv_pos.2 hA0, ⟨hcb, fun i x y => ?_, fun i => ?_, fun i x hx a => ?_,
    fun i j hij x hx y hy => ?_⟩⟩
  · exact (hcl i x y).trans (by linarith [dist_le_two_mul_supDist x y])
  · exact IsCompact.of_isClosed_subset (hc i).isCompact (isClosed_tsupport _) (tsupport_const_mul_subset _ _)
  · have h1 : ‖x‖ ≤ r i := by
      simpa using hr i (tsupport_const_mul_subset _ _ hx)
    have h2 : |x a| ≤ ‖x‖ := by
      simpa using PiLp.norm_apply_le x a
    exact h2.trans (h1.trans (hR i))
  · have h1 := ha i j hij x (tsupport_const_mul_subset _ _ hx) y (tsupport_const_mul_subset _ _ hy)
    have h3 := dist_le_two_mul_supDist x y
    linarith
private theorem euclidNormVec_ofLp (z : TestFunctions.EuclideanFourSpace) :
    TorusMetric.euclidNormVec (WithLp.ofLp z) = ‖z‖ := by apply _root_.YangMills.Construction.EuclideanAnalysis.CubedLaplacian.ParametrixConstruction.euclidNormVec_ofLp <;> assumption
private theorem one_le_euclidNormVec_of_mem_pairsR4 {ϑ : ℝ} {f g : (Fin 4 → ℝ) → ℝ}
    (h : (f, g) ∈ QuadrupleClasses.pairsR4 1 ϑ) {u v : Fin 4 → ℝ}
    (hu : u ∈ tsupport f) (hv : v ∈ tsupport g) : 1 ≤ TorusMetric.euclidNormVec (u - v) := by
  obtain ⟨_, _, _, _, h1, _⟩ := h
  have h2 : TestFunctions.setDistR4 (tsupport f) (tsupport g)
      ≤ ENNReal.ofReal (TorusMetric.euclidNormVec (u - v)) :=
    iInf₂_le_of_le u hu (iInf₂_le v hv)
  have h3 := h1.trans h2
  exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).1 h3
private theorem cyclicMomentFormula_pos_of_collinearQuadsR4 (hF : MomentLaw.nearlyCollinearPositivityStatement)
    (hQ : QuadrupleClasses.CollinearCentres.CollinearCentresStatement) {ϑ : ℝ}
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) (X : TestSpaces.SepTupleOfCard 4) (hX : X.1 ∈ QuadrupleClasses.collinearQuadsR4 1 ϑ) :
    0 < CyclicFormula.cyclicMomentFormula 4 (fun k x => X.1 k (WithLp.ofLp x)) := by
  obtain ⟨e, c, _, _, he, hline⟩ : QuadrupleClasses.CollinearCentres.HasShapeAxisAlongCentres 1 X.1 :=
    (hQ.1 1 ϑ ⟨one_pos, hϑ⟩).2.1.2 _ hX
  have hq := hX.1.2
  have hnn : ∀ i y, 0 ≤ X.1 i y := fun i => (hq.1 i).2
  have hnz : ∀ i, ∃ y, X.1 i y ≠ 0 := fun i => by
    obtain ⟨_, _, h1, _⟩ := hq.2 i (i + 1) (ne_add_one (by norm_num) i)
    exact h1.2.2.1
  have hcd : ∀ i, ContDiff ℝ 1 (liftToEuclidean (X.1 i)) := fun i =>
    (X.2.1 i).1.comp (EuclideanSpace.equiv (Fin 4) ℝ).contDiff
  have hcs : ∀ i, HasCompactSupport (liftToEuclidean (X.1 i)) := fun i =>
    (X.2.1 i).2.1.comp_homeomorph (EuclideanSpace.equiv (Fin 4) ℝ).toHomeomorph
  have hl : ∀ i, ∃ C, LipschitzWith C (liftToEuclidean (X.1 i)) := fun i =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hcs i) (hcd i) (by norm_num)
  have ha : ∀ i j, i ≠ j → ∀ x ∈ tsupport (liftToEuclidean (X.1 i)),
      ∀ y ∈ tsupport (liftToEuclidean (X.1 j)), 1 ≤ dist x y := by
    intro i j hij x hx y hy
    have h := one_le_euclidNormVec_of_mem_pairsR4 (hq.2 i j hij)
      (tsupport_liftToEuclidean _ hx) (tsupport_liftToEuclidean _ hy)
    rwa [← WithLp.ofLp_sub, euclidNormVec_ofLp, ← dist_eq_norm] at h
  obtain ⟨s, R, hs0, hS⟩ := exists_scaled_isSupTestFamily hl hcs ha
  obtain ⟨E, hEdef⟩ : ∃ E : TestFunctions.EuclideanFourSpace, E = WithLp.toLp 2 e := ⟨_, rfl⟩
  have hEe : WithLp.ofLp E = e := by rw [hEdef]
  have hE : ‖E‖ = 1 := by
    rw [← euclidNormVec_ofLp, hEe]
    exact he
  have hnear : ∀ i j, i ≠ j → ∀ x ∈ tsupport (fun x => s * liftToEuclidean (X.1 i) x),
      ∀ y ∈ tsupport (fun x => s * liftToEuclidean (X.1 j) x),
      63 / 64 * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) E ^ 2 := by
    intro i j hij x hx y hy
    have h := hline i j hij _ (tsupport_liftToEuclidean _ (tsupport_const_mul_subset _ _ hx)) _
      (tsupport_liftToEuclidean _ (tsupport_const_mul_subset _ _ hy))
    obtain ⟨W, hW⟩ : ∃ W : TestFunctions.EuclideanFourSpace, W = x - y := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = inner ℝ W E := ⟨_, rfl⟩
    have hd : dotProduct (WithLp.ofLp x - WithLp.ofLp y) e = t := by
      rw [← WithLp.ofLp_sub, ← hW, ht, ← hEe]
      simp [PiLp.inner_apply, dotProduct, mul_comm]
    have hv : (WithLp.ofLp x - WithLp.ofLp y) - t • e = WithLp.ofLp (W - t • E) := by
      rw [hW, WithLp.ofLp_sub, WithLp.ofLp_sub, WithLp.ofLp_smul, hEe]
    have hw : WithLp.ofLp x - WithLp.ofLp y = WithLp.ofLp W := by rw [hW, WithLp.ofLp_sub]
    rw [hd, hv, hw, euclidNormVec_ofLp, euclidNormVec_ofLp] at h
    have hn : ‖W - t • E‖ ^ 2 = ‖W‖ ^ 2 - t ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, hE, mul_one, Real.norm_eq_abs, sq_abs, real_inner_smul_right, ← ht]
      ring
    have h2 : ‖W - t • E‖ ^ 2 ≤ (1 / 8 * ‖W‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [← hW, ← ht]
    nlinarith
  have hpos := (hF (fun i x => s * liftToEuclidean (X.1 i) x) R (1 / 2) (by norm_num) hS
    (fun i x => mul_nonneg hs0.le (hnn i _))
    (fun i => by
      obtain ⟨y, hy⟩ := hnz i
      exact ⟨WithLp.toLp 2 y, mul_ne_zero hs0.ne' hy⟩)
    E hE hnear).2
  rw [cyclicMomentFormula_const_mul] at hpos
  exact (mul_pos_iff_of_pos_left (by positivity)).1 hpos
end SeparatedTuples
theorem cyclicFormulaOnSeparatedTuples_holds (hO : CyclicFormula.ExteriorSquareTraceOfOddInversionProduct)
    (hF : MomentLaw.nearlyCollinearPositivityStatement)
    (hQ : QuadrupleClasses.CollinearCentres.CollinearCentresStatement) :
    CyclicFormulaOnSeparatedTuples :=
  ⟨fun _ _ hn hodd X => SeparatedTuples.cyclicMomentFormula_odd_eq_zero hO hn hodd X,
    fun _ hϑ X hX => SeparatedTuples.cyclicMomentFormula_pos_of_collinearQuadsR4 hF hQ hϑ X hX⟩
end YangMills.Construction.TotalDensitiesGiveASystem
end
