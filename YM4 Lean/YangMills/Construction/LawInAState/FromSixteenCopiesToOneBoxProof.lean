import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.InfiniteLattice.IsometriesOnPlaquetteTermsAndReflectionIdentities
import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import YangMills.Construction.LawInAState.DominationOnTheLeastTorusProof
import YangMills.Construction.LawInAState.AveragesInACell
import YangMills.Construction.LawInAState.ResponsesInOneBox
import Mathlib
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponses
import YangMills.Construction.LawInAState.TheArrayOfTwoCellsOnTheLeastTorus
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometries
import YangMills.Construction.MirrorGridsOfEverySide.FactsOfAMirrorGrid
import YangMills.Construction.ResponseInTheExpansion.TwoPointFunctionByTotalCovariance
set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open TorusFields WeightedResponses BoxResponses CellAverages ChessboardTori ReflectedCopies
open InfiniteLattice (AmbientSpace)
def gridImage {S : ChessboardSetup} (G : ReflectionGrid S) (c : Fin 4 → ℤ) (φ : AmbientSpace → ℝ) :
    AmbientSpace → ℝ :=
  fun x => φ ((G.mover (G.cell 0) (G.cell c)).1.symm x)
def IsInteriorBy {S : ChessboardSetup} (G : ReflectionGrid S) (ε : ℝ) (φ : AmbientSpace → ℝ) : Prop :=
  ∀ x ∈ tsupport φ, ∀ μ, ε ≤ x μ - G.origin μ ∧ x μ - G.origin μ ≤ 1 - ε
def reflectionNormToBoxStatement : Prop :=
  HoldsForShapes fun Tb y Kr Xi vt => ∃ C d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
    ∀ (S : ChessboardSetup) (α : ℕ → ℝ) (T : StageTower (Tb.stepParameters y)), S.L = (Tb.stepParameters y).side →
    IsStateChain Tb y Kr Xi d S.K S.β α T →
    ∀ (k m : ℕ) (x : ℝ), k = separationLevel (Tb.stepParameters y) S.β S.K d →
    x = couplingAtSeparation (Tb.stepParameters y) S.β S.K d →
    m = averagingRadius x → ∀ G : ReflectionGrid S, G.q = 0 → ∀ f h : AmbientSpace → ℝ,
    IsNormalizedTestPair d vt f h →
    (∀ v ∈ shiftSet m, IsInteriorBy G (d / 2) (translateBy S.L S.K k v f) ∧
      IsInteriorBy G (d / 2) (translateBy S.L S.K k v h)) →
      (∀ b : ℝ, 0 ≤ b →
        (∀ c ∈ (minimalCounts S).indexBox,
          eLpNorm (fun u => shiftAveragedProduct T S.β α S.K k m (fun v => gridImage G c (translateBy S.L S.K k v f))
              (fun v => gridImage G c (translateBy S.L S.K k v h)) u - unitTorusCovariance S.L S.K S.β f h) 16
            (stageLaw T S.β S.K k) ≤ ENNReal.ofReal b) →
        reflectionNorm G (averagedCovarianceDefect S.L S.K k m S.β f h) ≤
          b + markError (Tb.stepParameters y) C x ^ (1 / 16 : ℝ)) ∧
      (∀ (b : ℝ) (w : AmbientSpace → ℝ), 0 ≤ b → (w = f ∨ w = h) →
        (∀ c ∈ (minimalCounts S).indexBox,
          eLpNorm (shiftAveragedResponse T S.β α S.K k m fun v => gridImage G c (translateBy S.L S.K k v w)) 16
            (stageLaw T S.β S.K k) ≤ ENNReal.ofReal b) →
        reflectionNorm G (averagedCenteredObservable S.L S.K k m S.β w) ≤
          b + markError (Tb.stepParameters y) C x ^ (1 / 16 : ℝ)) ∧
      ∀ v ∈ shiftSet m,
        |unitTorusCovariance S.L S.K S.β f h -
          ∫ u, centeredBoxResponse T S.β α S.K k (translateBy S.L S.K k v f) u *
              centeredBoxResponse T S.β α S.K k (translateBy S.L S.K k v h) u ∂stageLaw T S.β S.K k| ≤
          markError (Tb.stepParameters y) C x
end YangMills.Construction.StateLaws
end

noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open TorusLumps RenormalizationStepParameters WeightedResponses ResponseInTheExpansion ChessboardTori ReflectedCopies CellAverages BoxResponses
open InfiniteLattice (AmbientSpace)
section ProductsOfAverages
variable {Ω Ω' ι V : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [DecidableEq ι]
private lemma prod_avg_sub_expand (Q : Finset V) (p : ι → V → ℝ) (κ : ℝ) :
    ∏ c, ((Q.card : ℝ)⁻¹ * ∑ v ∈ Q, (p c v - κ)) =
      ((Q.card : ℝ)⁻¹) ^ Fintype.card ι * ∑ w ∈ Fintype.piFinset fun _ : ι => Q,
        ∑ I ∈ (Finset.univ : Finset ι).powerset, (-κ) ^ (Fintype.card ι - I.card) * ∏ c ∈ I, p c (w c) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_univ_sum]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [sub_eq_add_neg]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, mul_comm]
private lemma sum_powerset_pow_eq (t : ℝ) :
    ∑ I ∈ (Finset.univ : Finset ι).powerset, t ^ (Fintype.card ι - I.card) = (1 + t) ^ Fintype.card ι := by
  have h := Finset.prod_add (fun _ : ι => (1 : ℝ)) (fun _ : ι => t) Finset.univ
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ] at h
  rw [h]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ]
private lemma integral_prod_avg_sub {X : Type*} [MeasurableSpace X] (ν : Measure X) (Q : Finset V) (r : ι → V → X → ℝ)
    (κ : ℝ) (hr : ∀ (w : ι → V) (I : Finset ι), Integrable (fun ω => ∏ c ∈ I, r c (w c) ω) ν) :
    ∫ ω, ∏ c, ((Q.card : ℝ)⁻¹ * ∑ v ∈ Q, (r c v ω - κ)) ∂ν =
      ((Q.card : ℝ)⁻¹) ^ Fintype.card ι * ∑ w ∈ Fintype.piFinset (fun _ : ι => Q), ∑ I ∈ (Finset.univ : Finset ι).powerset,
        (-κ) ^ (Fintype.card ι - I.card) * ∫ ω, ∏ c ∈ I, r c (w c) ω ∂ν := by
  simp_rw [fun ω => prod_avg_sub_expand Q (fun c v => r c v ω) κ]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun I _ => integral_const_mul _ _
    · exact fun I _ => (hr w I).const_mul _
  · exact fun w _ => integrable_finsetSum _ fun I _ => (hr w I).const_mul _
private lemma abs_integral_prod_avg_sub_le (P : Measure Ω) (P' : Measure Ω') (Q : Finset V) (hQ : Q.Nonempty)
    (p : ι → V → Ω → ℝ) (p' : ι → V → Ω' → ℝ) (κ ε : ℝ)
    (hi : ∀ (w : ι → V) (I : Finset ι), Integrable (fun ω => ∏ c ∈ I, p c (w c) ω) P)
    (hi' : ∀ (w : ι → V) (I : Finset ι), Integrable (fun ω => ∏ c ∈ I, p' c (w c) ω) P')
    (hc : ∀ w : ι → V, (∀ c, w c ∈ Q) → ∀ I : Finset ι,
      |∫ ω, ∏ c ∈ I, p c (w c) ω ∂P - ∫ ω, ∏ c ∈ I, p' c (w c) ω ∂P'| ≤ ε) :
    |∫ ω, ∏ c, ((Q.card : ℝ)⁻¹ * ∑ v ∈ Q, (p c v ω - κ)) ∂P -
        ∫ ω, ∏ c, ((Q.card : ℝ)⁻¹ * ∑ v ∈ Q, (p' c v ω - κ)) ∂P'| ≤
      ε * (1 + |κ|) ^ Fintype.card ι := by
  set n := Fintype.card ι with hn
  set q : ℝ := (Q.card : ℝ)⁻¹ with hq
  have hqpos : 0 < q := inv_pos.mpr (by exact_mod_cast hQ.card_pos)
  rw [integral_prod_avg_sub P Q p κ hi, integral_prod_avg_sub P' Q p' κ hi', ← hn, ← hq, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (pow_pos hqpos n)]
  have bound : ∀ w ∈ Fintype.piFinset (fun _ : ι => Q),
      |∑ I ∈ (Finset.univ : Finset ι).powerset, (-κ) ^ (n - I.card) * ∫ ω, ∏ c ∈ I, p c (w c) ω ∂P -
        ∑ I ∈ (Finset.univ : Finset ι).powerset, (-κ) ^ (n - I.card) * ∫ ω, ∏ c ∈ I, p' c (w c) ω ∂P'| ≤
      ε * (1 + |κ|) ^ n := by
    intro w hw
    rw [← Finset.sum_sub_distrib, hn, ← sum_powerset_pow_eq |κ|, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
    rw [← mul_sub, abs_mul, abs_pow, abs_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (hc w (fun c => (Fintype.mem_piFinset.mp hw) c) I) (pow_nonneg (abs_nonneg _) _)
  calc q ^ n * |∑ w ∈ Fintype.piFinset (fun _ : ι => Q), _|
      ≤ q ^ n * ∑ w ∈ Fintype.piFinset (fun _ : ι => Q), ε * (1 + |κ|) ^ n :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum bound))
          (pow_pos hqpos n).le
    _ = ε * (1 + |κ|) ^ n := by
        rw [Finset.sum_const, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, Nat.cast_pow, hq,
          ← mul_pow, inv_mul_cancel₀ (by exact_mod_cast hQ.card_pos.ne'), one_pow, one_mul]
omit [Fintype ι] [DecidableEq ι] in
private lemma enorm_prod_finset (J : Finset ι) (a : ι → ℝ) : ‖∏ j ∈ J, a j‖ₑ = ∏ j ∈ J, ‖a j‖ₑ := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, enorm_mul, ih]
omit [Fintype ι] [DecidableEq ι] in
private lemma lintegral_prod_enorm_le_eLpNorm {μ : Measure Ω'} (J : Finset ι) (hJ : J.Nonempty) (Φ : ι → Ω' → ℝ)
    (hΦ : ∀ j ∈ J, AEStronglyMeasurable (Φ j) μ) :
    ∫⁻ ω, ∏ j ∈ J, ‖Φ j ω‖ₑ ∂μ ≤ ∏ j ∈ J, eLpNorm (Φ j) (J.card : ENNReal) μ := by
  have hn0 : (J.card : ℝ) ≠ 0 := by exact_mod_cast hJ.card_pos.ne'
  have hn1 : (J.card : ENNReal) ≠ 0 := by exact_mod_cast hJ.card_pos.ne'
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) J
    (f := fun j ω => ‖Φ j ω‖ₑ ^ (J.card : ℝ))
    (fun j hj => (hΦ j hj).enorm.pow_const _) (p := fun _ => (J.card : ℝ)⁻¹)
    (by rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hn0]) (fun _ _ => by positivity)
  have h1 : ∀ j (ω : Ω'), (‖Φ j ω‖ₑ ^ (J.card : ℝ)) ^ (J.card : ℝ)⁻¹ = ‖Φ j ω‖ₑ := fun j ω => by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hn0, ENNReal.rpow_one]
  simp only [h1] at h
  refine h.trans (Finset.prod_le_prod' fun j _ => ?_)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hn1 (ENNReal.natCast_ne_top _)]
  simp
omit [Fintype ι] [DecidableEq ι] in
private lemma integrable_finset_prod_of_memLp {μ : Measure Ω'} [IsProbabilityMeasure μ] (J : Finset ι) (hJ : J.card ≤ 32)
    (Φ : ι → Ω' → ℝ) (hΦ : ∀ j ∈ J, MemLp (Φ j) 32 μ) : Integrable (fun ω => ∏ j ∈ J, Φ j ω) μ := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · simp
  have hm : ∀ j ∈ J, AEStronglyMeasurable (Φ j) μ := fun j hj => (hΦ j hj).aestronglyMeasurable
  refine ⟨Finset.aestronglyMeasurable_fun_prod _ hm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [enorm_prod_finset]
  refine (lintegral_prod_enorm_le_eLpNorm J hne Φ hm).trans_lt (ENNReal.prod_lt_top fun j hj => ?_)
  exact ((hΦ j hj).mono_exponent (by exact_mod_cast hJ)).eLpNorm_lt_top
omit [DecidableEq ι] in
private lemma abs_integral_prod_le_pow {μ : Measure Ω'} (n : ℕ) (hn : n ≠ 0) (hcard : Fintype.card ι = n) (Y : ι → Ω' → ℝ)
    (hY : ∀ c, AEStronglyMeasurable (Y c) μ) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ c, eLpNorm (Y c) (n : ENNReal) μ ≤ ENNReal.ofReal b) : |∫ ω, ∏ c, Y c ω ∂μ| ≤ b ^ n := by
  have hne : (Finset.univ : Finset ι).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff]
    omega
  have h := lintegral_prod_enorm_le_eLpNorm (μ := μ) Finset.univ hne Y fun c _ => hY c
  rw [Finset.card_univ, hcard] at h
  have h2 : ‖∫ ω, ∏ c, Y c ω ∂μ‖ₑ ≤ ENNReal.ofReal (b ^ n) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    simp only [enorm_prod_finset]
    refine h.trans ?_
    have : ∏ c : ι, eLpNorm (Y c) (n : ENNReal) μ ≤ ∏ _c : ι, ENNReal.ofReal b :=
      Finset.prod_le_prod' fun c _ => hb c
    refine this.trans (le_of_eq ?_)
    rw [Finset.prod_const, Finset.card_univ, hcard, ENNReal.ofReal_pow hb0]
  rw [← Real.norm_eq_abs]
  rw [← ofReal_norm] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
end ProductsOfAverages
section BoundedMeasurable
variable {Ω ι : Type*} [MeasurableSpace Ω]
private def IsMeasBdd (u : Ω → ℝ) : Prop := Measurable u ∧ ∃ C : ℝ, ∀ ω, |u ω| ≤ C
private lemma IsMeasBdd.const (c : ℝ) : IsMeasBdd (fun _ : Ω => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩
private lemma IsMeasBdd.sub {u v : Ω → ℝ} (hu : IsMeasBdd u) (hv : IsMeasBdd v) : IsMeasBdd (fun ω => u ω - v ω) := by
  obtain ⟨mu, C, hC⟩ := hu
  obtain ⟨mv, C', hC'⟩ := hv
  refine ⟨mu.sub mv, C + C', fun ω => ?_⟩
  have h1 := abs_le.mp (hC ω)
  have h2 := abs_le.mp (hC' ω)
  exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
private lemma IsMeasBdd.add {u v : Ω → ℝ} (hu : IsMeasBdd u) (hv : IsMeasBdd v) : IsMeasBdd (fun ω => u ω + v ω) := by
  obtain ⟨mu, C, hC⟩ := hu
  obtain ⟨mv, C', hC'⟩ := hv
  refine ⟨mu.add mv, C + C', fun ω => ?_⟩
  have h1 := abs_le.mp (hC ω)
  have h2 := abs_le.mp (hC' ω)
  exact abs_le.mpr ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
private lemma IsMeasBdd.mul {u v : Ω → ℝ} (hu : IsMeasBdd u) (hv : IsMeasBdd v) : IsMeasBdd (fun ω => u ω * v ω) := by
  obtain ⟨mu, C, hC⟩ := hu
  obtain ⟨mv, C', hC'⟩ := hv
  refine ⟨mu.mul mv, |C| * |C'|, fun ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hC ω).trans (le_abs_self _)) ((hC' ω).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
private lemma IsMeasBdd.prod (J : Finset ι) {u : ι → Ω → ℝ} (hu : ∀ j ∈ J, IsMeasBdd (u j)) :
    IsMeasBdd (fun ω => ∏ j ∈ J, u j ω) := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa using IsMeasBdd.const (Ω := Ω) 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hu i (Finset.mem_insert_self _ _)).mul (ih fun j hj => hu j (Finset.mem_insert_of_mem hj))
private lemma IsMeasBdd.sum (J : Finset ι) {u : ι → Ω → ℝ} (hu : ∀ j ∈ J, IsMeasBdd (u j)) :
    IsMeasBdd (fun ω => ∑ j ∈ J, u j ω) := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa using IsMeasBdd.const (Ω := Ω) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hu i (Finset.mem_insert_self _ _)).add (ih fun j hj => hu j (Finset.mem_insert_of_mem hj))
private lemma IsMeasBdd.integrable {u : Ω → ℝ} (hu : IsMeasBdd u) (μ : Measure Ω) [IsFiniteMeasure μ] : Integrable u μ := by
  obtain ⟨mu, C, hC⟩ := hu
  exact Integrable.of_bound mu.aestronglyMeasurable C (ae_of_all _ fun ω => by simpa using hC ω)
end BoundedMeasurable
section UnitBumps
open TorusMetric
private lemma abs_apply_le_euclid (v : AmbientSpace) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
abbrev _root_.YangMills.SharedProofs.p10398 := @abs_apply_le_euclid
private lemma euclid_norm_nonneg (v : AmbientSpace) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
private lemma euclid_le_two_mul_norm (v : AmbientSpace) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
abbrev _root_.YangMills.SharedProofs.p8643 := @euclid_le_two_mul_norm
private lemma euclid_norm_sub_comm (x y : AmbientSpace) : euclidNormVec (x - y) = euclidNormVec (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
abbrev _root_.YangMills.SharedProofs.p26380 := @euclid_norm_sub_comm
private lemma continuous_of_preservesDist {e : AmbientSpace → AmbientSpace} (he : PreservesDist e) : Continuous e := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun x y => ?_).continuous
  refine (dist_pi_le_iff (by positivity)).mpr fun μ => ?_
  rw [Real.dist_eq]
  have h1 : |e x μ - e y μ| ≤ euclidNormVec (e x - e y) := abs_apply_le_euclid (e x - e y) μ
  rw [he x y] at h1
  have h2 := euclid_le_two_mul_norm (x - y)
  rw [← dist_eq_norm] at h2
  simpa using h1.trans h2
private lemma preservesDist_symm {e : Equiv.Perm AmbientSpace} (he : PreservesDist e) : PreservesDist e.symm := fun x y => by
  have h := he (e.symm x) (e.symm y)
  simpa using h.symm
private lemma tsupport_comp_subset_preimage {φ : AmbientSpace → ℝ} {e : AmbientSpace → AmbientSpace} (he : Continuous e) :
    tsupport (φ ∘ e) ⊆ e ⁻¹' tsupport φ :=
  closure_minimal (fun _ hx => subset_tsupport φ hx) ((isClosed_tsupport φ).preimage he)
private structure IsUnitBump (d vt : ℝ) (φ : AmbientSpace → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  le_one : ∀ x, φ x ≤ 1
  slope : ∀ x x', |φ x - φ x'| ≤ euclidNormVec (x - x') / (vt * d)
  ball : ∃ c, tsupport φ ⊆ TestFunctions.closedBallR4 c d
private lemma isUnitBump_of_shaped {d vt : ℝ} {x₀ : AmbientSpace} {f : AmbientSpace → ℝ}
    (hb : TestFunctions.IsShapedBump TestFunctions.euclidDistR4 TestFunctions.closedBallR4 (fun f => ∫ x, f x) d vt x₀ f)
    (hs : TestFunctions.uniformNorm f = 1) : IsUnitBump d vt f := by
  obtain ⟨⟨C₀, hC₀, hC₀'⟩, hnn, -, hball, -, hlip⟩ := hb
  have hbdd : BddAbove (Set.range fun x => ‖f x‖) := by
    by_contra hn
    have h0 : TestFunctions.uniformNorm f = 0 := Real.iSup_of_not_bddAbove hn
    linarith
  refine ⟨hnn, fun x => ?_, fun x x' => ?_, x₀, hball⟩
  · have h1 : ‖f x‖ ≤ TestFunctions.uniformNorm f := le_ciSup hbdd x
    rw [hs] at h1
    exact (le_abs_self _).trans (by simpa using h1)
  · rw [hs] at hlip
    set S : Set ℝ := {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * TestFunctions.euclidDistR4 x y} with hS
    have hne : S.Nonempty := ⟨C₀, hC₀, hC₀'⟩
    have hlip' : sInf S ≤ 1 / (vt * d) := hlip
    have hD : 0 ≤ TestFunctions.euclidDistR4 x x' := euclid_norm_nonneg _
    have hmain : ‖f x - f x'‖ ≤ sInf S * TestFunctions.euclidDistR4 x x' := by
      rcases hD.eq_or_lt with h0 | h0
      · have := hC₀' x x'
        rw [← h0] at this ⊢
        simpa using this
      · rw [← div_le_iff₀ h0]
        refine le_csInf hne fun C hC => ?_
        rw [div_le_iff₀ h0]
        exact hC.2 x x'
    have h2 : sInf S * TestFunctions.euclidDistR4 x x' ≤ 1 / (vt * d) * TestFunctions.euclidDistR4 x x' :=
      mul_le_mul_of_nonneg_right hlip' hD
    have h3 : 1 / (vt * d) * TestFunctions.euclidDistR4 x x' = euclidNormVec (x - x') / (vt * d) := by
      rw [TestFunctions.euclidDistR4]
      ring
    rw [← h3, ← Real.norm_eq_abs]
    exact hmain.trans h2
private lemma IsUnitBump.comp {d vt : ℝ} {φ : AmbientSpace → ℝ} (hφ : IsUnitBump d vt φ) (e : Equiv.Perm AmbientSpace)
    (he : PreservesDist e) : IsUnitBump d vt (φ ∘ e) := by
  refine ⟨fun x => hφ.nonneg _, fun x => hφ.le_one _, fun x x' => ?_, ?_⟩
  · have h := hφ.slope (e x) (e x')
    rwa [he x x'] at h
  · obtain ⟨c, hc⟩ := hφ.ball
    refine ⟨e.symm c, fun y hy => ?_⟩
    have h1 := hc (tsupport_comp_subset_preimage (continuous_of_preservesDist he) hy)
    have h2 : euclidNormVec (e y - c) ≤ d := h1
    have h3 := he y (e.symm c)
    rw [Equiv.apply_symm_apply] at h3
    change euclidNormVec (y - e.symm c) ≤ d
    rwa [← h3]
private lemma IsUnitBump.isBoundedBorelCompactlySupported {d vt : ℝ} (hd : 0 < d) (hvt : 0 < vt) {φ : AmbientSpace → ℝ}
    (hφ : IsUnitBump d vt φ) : InfiniteLattice.IsBoundedBorelCompactlySupported φ := by
  have hc : Continuous φ := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (2 / (vt * d))) fun x y => ?_).continuous
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq]
    refine (hφ.slope x y).trans ?_
    have h2 := euclid_le_two_mul_norm (x - y)
    rw [← dist_eq_norm] at h2
    have hpos : 0 < vt * d := by positivity
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpos]
    exact h2
  refine ⟨hc.measurable, ⟨1, fun x => ?_⟩, ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_one x
  · obtain ⟨c, hsub⟩ := hφ.ball
    refine IsCompact.of_isClosed_subset (isCompact_closedBall c d) (isClosed_tsupport φ) fun x hx => ?_
    refine Metric.mem_closedBall.mpr ((dist_pi_le_iff hd.le).mpr fun μ => ?_)
    rw [Real.dist_eq]
    exact (abs_apply_le_euclid (x - c) μ).trans (hsub hx)
private lemma IsUnitBump.separatedFamily_one {d vt : ℝ} {φ : AmbientSpace → ℝ} (hφ : IsUnitBump d vt φ) :
    IsSeparatedBumpFamily d vt (fun _ : Fin 1 => φ) :=
  ⟨fun _ => hφ.nonneg, fun _ => hφ.le_one, fun _ => hφ.slope, fun _ => hφ.ball,
    fun i j hij => absurd (Subsingleton.elim i j) hij⟩
private lemma le_euclid_of_interior {d : ℝ} {o : AmbientSpace} {c c' z : Fin 4 → ℤ}
    (hc : ∀ μ, 0 ≤ c μ ∧ c μ < 2) (hc' : ∀ μ, 0 ≤ c' μ ∧ c' μ < 2) {x x' : AmbientSpace}
    (hx : ∀ μ, d / 2 ≤ x μ - (o μ + c μ) ∧ x μ - (o μ + c μ) ≤ 1 - d / 2)
    (hx' : ∀ μ, d / 2 ≤ x' μ - (o μ + c' μ) ∧ x' μ - (o μ + c' μ) ≤ 1 - d / 2)
    (hz : c ≠ c' ∨ z ≠ 0) : d ≤ euclidNormVec (fun a => x a - x' a + 2 * (z a : ℝ)) := by
  obtain ⟨μ, hμ⟩ : ∃ μ, c μ - c' μ + 2 * z μ ≠ 0 := by
    by_contra hall
    push Not at hall
    have h : ∀ μ, c μ = c' μ ∧ z μ = 0 := fun μ => by
      have h1 := hall μ
      have h2 := hc μ
      have h3 := hc' μ
      omega
    rcases hz with hz | hz
    · exact hz (funext fun μ => (h μ).1)
    · exact hz (funext fun μ => (h μ).2)
  refine le_trans ?_ (abs_apply_le_euclid _ μ)
  have hN : (1 : ℤ) ≤ |c μ - c' μ + 2 * z μ| := Int.one_le_abs hμ
  have hN' : (1 : ℝ) ≤ |(c μ : ℝ) - c' μ + 2 * z μ| := by exact_mod_cast hN
  have h1 := hx μ
  have h2 := hx' μ
  rcases le_abs.mp hN' with h3 | h3
  · exact le_abs.mpr (Or.inl (by linarith [h1.1, h1.2, h2.1, h2.2]))
  · exact le_abs.mpr (Or.inr (by linarith [h1.1, h1.2, h2.1, h2.2]))
end UnitBumps
section GridCells
open TorusMetric
variable {D : ChessboardSetup} (g : ReflectionGrid D)
private lemma cellSide_eq_one (hq : g.q = 0) : g.cellSide = 1 := by
  simp [ReflectionGrid.cellSide, hq]
private lemma hasAdmissibleSide_of_q_eq_zero (hq : g.q = 0) (hK : 2 ≤ (D.K : ℕ)) : g.HasAdmissibleSide := by apply _root_.YangMills.SharedProofs.p72971 <;> assumption
private lemma mover_image_cell (hG : MirrorGridsAllSides.ReflectionGridProperties) (hs : g.HasAdmissibleSide)
    (k k' : Fin 4 → ℤ) : (g.mover (g.cell k) (g.cell k')).1 '' g.cell k = g.cell k' := by
  obtain ⟨-, -, -, hgc, -⟩ := hG D g hs
  obtain ⟨-, h2, -⟩ := hgc
  exact Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' g.cell k = g.cell k') (h2 k k').exists
private lemma mover_cell_zero_self (hG : MirrorGridsAllSides.ReflectionGridProperties) (hs : g.HasAdmissibleSide) :
    g.mover (g.cell 0) (g.cell 0) = 1 := by
  obtain ⟨-, -, -, hgc, -⟩ := hG D g hs
  obtain ⟨-, h2, -⟩ := hgc
  refine (h2 0 0).unique (mover_image_cell g hG hs 0 0) ?_
  simp
private lemma preservesDist_of_mem (r : g.reflectionGroup) : PreservesDist r.1 :=
  (g.reflectionGroup_le_latticeSymGroup r.2).1
private lemma interior_margin_image (hq : g.q = 0) (r : g.reflectionGroup) (c : Fin 4 → ℤ) (hr : r.1 '' g.cell 0 = g.cell c)
    {δ : ℝ} {y : AmbientSpace} (hy : ∀ μ, δ ≤ y μ - g.origin μ ∧ y μ - g.origin μ ≤ 1 - δ) (hδ : 0 < δ) (μ : Fin 4) :
    δ ≤ r.1 y μ - (g.origin μ + c μ) ∧ r.1 y μ - (g.origin μ + c μ) ≤ 1 - δ := by
  have hside := cellSide_eq_one g hq
  have hiso := preservesDist_of_mem g r
  have hball : ∀ e : AmbientSpace, euclidNormVec e < δ → r.1 y + e ∈ g.cell c := by
    intro e he
    have hz : r.1 (r.1.symm (r.1 y + e)) = r.1 y + e := Equiv.apply_symm_apply _ _
    have hdist : euclidNormVec (r.1.symm (r.1 y + e) - y) < δ := by
      have h := hiso (r.1.symm (r.1 y + e)) y
      rw [hz, add_sub_cancel_left] at h
      rwa [← h]
    have hzc : r.1.symm (r.1 y + e) ∈ g.cell 0 := by
      intro ν
      have h1 := abs_le.mp ((abs_apply_le_euclid (r.1.symm (r.1 y + e) - y) ν).trans hdist.le)
      have h2 := hy ν
      simp only [Pi.sub_apply] at h1
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, add_zero, hside, Set.mem_Icc]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    rw [← hr]
    exact ⟨_, hzc, hz⟩
  set s := r.1 y μ - (g.origin μ + c μ) with hs
  have hcell : ∀ t : ℝ, |t| < δ → 0 ≤ s + t ∧ s + t ≤ 1 := by
    intro t ht
    have h := hball (Pi.single μ t) (by rwa [InfiniteLattice.euclidNormVec_single])
    have h1 := h μ
    simp only [Pi.add_apply, Pi.single_eq_same, hside, one_mul, Set.mem_Icc] at h1
    constructor <;> linarith [h1.1, h1.2]
  have h0 := hcell 0 (by simpa using hδ)
  constructor
  · by_contra hlt
    push Not at hlt
    have h1 := (hcell (-(s + δ) / 2) (abs_lt.mpr ⟨by linarith [h0.1], by linarith [h0.1]⟩)).1
    linarith
  · by_contra hlt
    push Not at hlt
    have h1 := (hcell ((1 - s + δ) / 2) (abs_lt.mpr ⟨by linarith [h0.2], by linarith⟩)).2
    linarith
private lemma gridImage_zero (hG : MirrorGridsAllSides.ReflectionGridProperties) (hs : g.HasAdmissibleSide)
    (u : AmbientSpace → ℝ) : gridImage g 0 u = u := by
  funext x
  rw [gridImage, mover_cell_zero_self g hG hs]
  rfl
end GridCells
section UnitTorus
open TorusMetric
open InfiniteLattice (IsBoundedBorelCompactlySupported)
variable {D : ChessboardSetup} (g : ReflectionGrid D)
private lemma smeared_isMeasBdd (hS : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main) {φ : AmbientSpace → ℝ}
    (hφ : IsBoundedBorelCompactlySupported φ) : IsMeasBdd (smearedObservable D.L D.K φ) := by
  obtain ⟨⟨-, h⟩, -⟩ := hS D.mesh D.mesh_pos
  obtain ⟨-, -, ⟨hm, C, hC⟩, -⟩ := h φ hφ
  refine ⟨?_, C, fun U => ?_⟩
  · have h2 : Measurable (fun U : InfiniteLattice.GaugeField D.mesh => InfiniteLattice.smearedEnergy φ U) := by
      simpa [Function.comp_def] using Complex.measurable_re.comp hm
    exact h2
  · have h2 := hC U
    rw [Complex.norm_real, Real.norm_eq_abs] at h2
    exact h2
private lemma smeared_pullback (hC : MultipleReflections.SymmetriesOnFacesAndReflectionIdentities.Statement)
    (s : D.LatticeSym) {φ : AmbientSpace → ℝ} (hφ : IsBoundedBorelCompactlySupported φ) (U : D.GaugeField) :
    smearedObservable D.L D.K φ (s.pullbackField U) = smearedObservable D.L D.K (s.pushforwardFun φ) U :=
  congrFun (((hC ⟨D.toStandingParameters, D.β, D.beta_pos⟩).1 s).2.1 φ hφ).2 U
private lemma pushforwardFun_of_reflection (r : g.reflectionGroup) (u : AmbientSpace → ℝ) :
    (g.toLatticeSym r).pushforwardFun u = u ∘ r.1.symm := by
  funext x
  have h := (g.toLatticeSym r).pushforwardFun_apply_toFun u (r.1.symm x)
  have e : (g.toLatticeSym r).toFun (r.1.symm x) = x := Equiv.apply_symm_apply r.1 x
  rw [e] at h
  exact h
private def shiftPoint (D : ChessboardSetup) (k : ℕ) (v : Fin 4 → ℤ) : InfiniteLattice.LatticePoint D.mesh :=
  ⟨latticeShift D.L D.K k v, fun i => v i * (D.L : ℤ) ^ k, fun μ => by
    have hL : (D.L : ℝ) ≠ 0 := by linarith [D.one_lt_factor]
    simp only [latticeShift, ChessboardSetup.mesh, PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
    push_cast
    field_simp⟩
private lemma pushforwardFun_shiftPoint (k : ℕ) (v : Fin 4 → ℤ) (u : AmbientSpace → ℝ) :
    (InfiniteLattice.shift (shiftPoint D k v)).pushforwardFun u = translateBy D.L D.K k v u := by
  funext x
  have h := (InfiniteLattice.shift (shiftPoint D k v)).pushforwardFun_apply_toFun u
    (x - latticeShift D.L D.K k v)
  have e : (InfiniteLattice.shift (shiftPoint D k v)).toFun (x - latticeShift D.L D.K k v) = x :=
    sub_add_cancel x (latticeShift D.L D.K k v)
  rw [e] at h
  exact h
private lemma integral_pullback_eq (hI : unitTorusMeasureSymmetricStatement) (s : D.LatticeSym)
    {F : D.GaugeField → ℝ} (hF : IsMeasBdd F) :
    ∫ U, F (s.pullbackField U) ∂unitTorusMeasure D.L D.K D.β = ∫ U, F U ∂unitTorusMeasure D.L D.K D.β := by
  obtain ⟨mF, C, hC⟩ := hF
  have h := (hI D).2 s (fun U => ((F U : ℝ) : ℂ))
    ⟨Complex.measurable_ofReal.comp mF, C, fun U => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC U⟩
  have h1 : ∫ U, ((F (s.pullbackField U) : ℝ) : ℂ) ∂unitTorusMeasure D.L D.K D.β =
      ((∫ U, F (s.pullbackField U) ∂unitTorusMeasure D.L D.K D.β : ℝ) : ℂ) := integral_complex_ofReal
  have h2 : ∫ U, ((F U : ℝ) : ℂ) ∂unitTorusMeasure D.L D.K D.β = ((∫ U, F U ∂unitTorusMeasure D.L D.K D.β : ℝ) : ℂ) :=
    integral_complex_ofReal
  refine Complex.ofReal_injective ?_
  rw [← h1, ← h2]
  exact h
private lemma reflectionNorm_eq (hA : LawInAState.twoCellPeriodicMeanStatement) (hq : g.q = 0) (G : D.GaugeField → ℝ)
    (hG : ∀ c ∈ (minimalCounts D).indexBox,
      IsMeasBdd fun U => G ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U)) :
    reflectionNorm g G =
      |∫ U, ∏ c ∈ (minimalCounts D).indexBox,
        G ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U)
        ∂unitTorusMeasure D.L D.K D.β| ^ (1 / 16 : ℝ) := by
  have hcopy : ∀ c V, g.transportTo (g.cell 0) (g.cell c) (fun U => ((G U : ℝ) : ℂ)) V =
      ((G ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField V) : ℝ) : ℂ) := by
    intro c V
    simp only [ReflectionGrid.transportTo, ReflectionGrid.transport, Conventions.signedConjFun, Conventions.signedConj,
      InfiniteLattice.LatticeSymmetry.actOn]
    split_ifs <;> simp [Complex.conj_ofReal]
  have hR := IsMeasBdd.prod (minimalCounts D).indexBox hG
  obtain ⟨mR, C, hC⟩ := hR
  have harr := hA D g hq
    (fun U => ((∏ c ∈ (minimalCounts D).indexBox,
      G ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp mR) ⟨C, fun U => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC U⟩
  have hint : ∫ U, ((∏ c ∈ (minimalCounts D).indexBox,
        G ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) : ℝ) : ℂ)
        ∂unitTorusMeasure D.L D.K D.β =
      ((∫ U, ∏ c ∈ (minimalCounts D).indexBox,
        G ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U)
        ∂unitTorusMeasure D.L D.K D.β : ℝ) : ℂ) := integral_complex_ofReal
  rw [reflectionNorm, tiledMean, tiledIntegral]
  simp only [hcopy, ← Complex.ofReal_prod]
  rw [harr, hint, Complex.norm_real, Real.norm_eq_abs]
end UnitTorus
section GridImages
open TorusMetric
open InfiniteLattice (IsBoundedBorelCompactlySupported)
variable {D : ChessboardSetup} (g : ReflectionGrid D)
private lemma isUnitBump_translateBy {d vt : ℝ} {u : AmbientSpace → ℝ} (hu : IsUnitBump d vt u) (k : ℕ) (v : Fin 4 → ℤ) :
    IsUnitBump d vt (translateBy D.L D.K k v u) :=
  hu.comp (Equiv.subRight (latticeShift D.L D.K k v)) fun x y => by
    simp only [Equiv.subRight_apply, sub_sub_sub_cancel_right]
private lemma isUnitBump_gridImage {d vt : ℝ} {u : AmbientSpace → ℝ} (hu : IsUnitBump d vt u) (c : Fin 4 → ℤ) :
    IsUnitBump d vt (gridImage g c u) :=
  hu.comp _ (preservesDist_symm (preservesDist_of_mem g _))
private def pairSelect (f h : AmbientSpace → ℝ) : Bool → AmbientSpace → ℝ
  | true => f
  | false => h
private lemma isUnitBump_of_testPair {d vt : ℝ} {f h : AmbientSpace → ℝ} (hp : IsNormalizedTestPair d vt f h) :
    IsUnitBump d vt f ∧ IsUnitBump d vt h ∧ ∀ a ∈ tsupport f, ∀ b ∈ tsupport h, d ≤ euclidNormVec (a - b) := by
  obtain ⟨x₁, x₂, h₁, h₂, hfar, -⟩ := hp.mem_class
  refine ⟨isUnitBump_of_shaped h₁ hp.norm_left, isUnitBump_of_shaped h₂ hp.norm_right, fun a ha b hb => ?_⟩
  have h3 : ENNReal.ofReal d ≤ ENNReal.ofReal (euclidNormVec (a - b)) :=
    hfar.trans (iInf₂_le_of_le a ha (iInf₂_le_of_le b hb le_rfl))
  by_contra hlt
  exact hlt ((ENNReal.ofReal_le_ofReal_iff (euclid_norm_nonneg _)).mp h3)
private lemma mem_indexBox_bounds {c : Fin 4 → ℤ} (hc : c ∈ (minimalCounts D).indexBox) (μ : Fin 4) :
    0 ≤ c μ ∧ c μ < 2 := by
  have h := Fintype.mem_piFinset.mp hc μ
  simpa [cubicCounts] using h
private lemma separated_of_selection (hG : MirrorGridsAllSides.ReflectionGridProperties) (hq : g.q = 0)
    (hs : g.HasAdmissibleSide) (k m : ℕ) {d vt : ℝ} (hd : 0 < d) {f h : AmbientSpace → ℝ}
    (hp : IsNormalizedTestPair d vt f h)
    (hin : ∀ v ∈ shiftSet m, IsInteriorBy g (d / 2) (translateBy D.L D.K k v f) ∧
      IsInteriorBy g (d / 2) (translateBy D.L D.K k v h))
    (w : ↥(minimalCounts D).indexBox → Fin 4 → ℤ) (hw : ∀ c, w c ∈ shiftSet m) {p : ℕ}
    (e : Fin p ≃ ↥(minimalCounts D).indexBox × Bool) :
    IsSeparatedBumpFamily d vt fun i => gridImage g (e i).1 (translateBy D.L D.K k (w (e i).1) (pairSelect f h (e i).2)) := by
  obtain ⟨hf, hh, hfar⟩ := isUnitBump_of_testPair hp
  have hmark : ∀ b, IsUnitBump d vt (pairSelect f h b) := fun b => by cases b <;> assumption
  have him : ∀ i, IsUnitBump d vt (gridImage g (e i).1 (translateBy D.L D.K k (w (e i).1) (pairSelect f h (e i).2))) :=
    fun i => isUnitBump_gridImage g (isUnitBump_translateBy (hmark _) k _) _
  refine ⟨fun i => (him i).nonneg, fun i => (him i).le_one, fun i => (him i).slope, fun i => (him i).ball, ?_⟩
  intro i j hij x hx x' hx' z
  have hins : ∀ (c : ↥(minimalCounts D).indexBox) (b : Bool),
      IsInteriorBy g (d / 2) (translateBy D.L D.K k (w c) (pairSelect f h b)) := fun c b => by
    cases b
    · exact (hin _ (hw c)).2
    · exact (hin _ (hw c)).1
  have hsupp : ∀ (c : Fin 4 → ℤ) (u : AmbientSpace → ℝ) {x : AmbientSpace}, x ∈ tsupport (gridImage g c u) →
      (g.mover (g.cell 0) (g.cell c)).1.symm x ∈ tsupport u := fun c u x hx =>
    tsupport_comp_subset_preimage (continuous_of_preservesDist (preservesDist_symm (preservesDist_of_mem g _))) hx
  have hy := hsupp _ _ hx
  have hy' := hsupp _ _ hx'
  have hmar : ∀ (c : ↥(minimalCounts D).indexBox) (b : Bool) {x : AmbientSpace},
      (g.mover (g.cell 0) (g.cell c)).1.symm x ∈ tsupport (translateBy D.L D.K k (w c) (pairSelect f h b)) → ∀ μ,
        d / 2 ≤ x μ - (g.origin μ + (c : Fin 4 → ℤ) μ) ∧ x μ - (g.origin μ + (c : Fin 4 → ℤ) μ) ≤ 1 - d / 2 := by
    intro c b x hx μ
    have h1 := interior_margin_image g hq _ c (mover_image_cell g hG hs 0 c) (hins c b _ hx) (half_pos hd) μ
    rwa [Equiv.apply_symm_apply] at h1
  by_cases hcz : ((e i).1 : Fin 4 → ℤ) ≠ (e j).1 ∨ z ≠ 0
  · exact le_euclid_of_interior (mem_indexBox_bounds (e i).1.2) (mem_indexBox_bounds (e j).1.2) (hmar _ _ hy)
      (hmar _ _ hy') hcz
  · push Not at hcz
    obtain ⟨hcc, rfl⟩ := hcz
    have hcc' : (e i).1 = (e j).1 := Subtype.ext hcc
    have hbb : (e i).2 ≠ (e j).2 := fun hb => hij (e.injective (Prod.ext hcc' hb))
    rw [← hcc'] at hy'
    have hsym := preservesDist_symm (preservesDist_of_mem g (g.mover (g.cell 0) (g.cell ((e i).1 : Fin 4 → ℤ))))
    have h1 : euclidNormVec (fun a => x a - x' a + 2 * (((0 : Fin 4 → ℤ) a : ℤ) : ℝ)) = euclidNormVec (x - x') := by
      congr 1
      funext a
      simp
    rw [h1, ← hsym x x']
    have hcont : Continuous (Equiv.subRight (latticeShift D.L D.K k (w (e i).1)) : AmbientSpace → AmbientSpace) :=
      continuous_id.sub continuous_const
    have ht : ∀ (u : AmbientSpace → ℝ) {y : AmbientSpace}, y ∈ tsupport (translateBy D.L D.K k (w (e i).1) u) →
        y - latticeShift D.L D.K k (w (e i).1) ∈ tsupport u :=
      fun u y hy => tsupport_comp_subset_preimage (φ := u) hcont hy
    have key : ∀ b₁ b₂ : Bool, b₁ ≠ b₂ → ∀ y y' : AmbientSpace,
        y ∈ tsupport (translateBy D.L D.K k (w (e i).1) (pairSelect f h b₁)) →
        y' ∈ tsupport (translateBy D.L D.K k (w (e i).1) (pairSelect f h b₂)) → d ≤ euclidNormVec (y - y') := by
      intro b₁ b₂ hb y y' hy hy'
      cases b₁ <;> cases b₂
      · exact absurd rfl hb
      · rw [euclid_norm_sub_comm, show y' - y = (y' - latticeShift D.L D.K k (w (e i).1)) -
          (y - latticeShift D.L D.K k (w (e i).1)) by abel]
        exact hfar _ (ht _ hy') _ (ht _ hy)
      · rw [show y - y' = (y - latticeShift D.L D.K k (w (e i).1)) - (y' - latticeShift D.L D.K k (w (e i).1)) by abel]
        exact hfar _ (ht _ hy) _ (ht _ hy')
      · exact absurd rfl hb
    exact key _ _ hbb _ _ hy hy'
private lemma smeared_gridImage (hC : MultipleReflections.SymmetriesOnFacesAndReflectionIdentities.Statement)
    {d vt : ℝ} (hd : 0 < d) (hvt : 0 < vt) {u : AmbientSpace → ℝ} (hu : IsUnitBump d vt u) (c : Fin 4 → ℤ)
    (U : D.GaugeField) :
    smearedObservable D.L D.K u ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) =
      smearedObservable D.L D.K (gridImage g c u) U := by
  rw [smeared_pullback hC _ (hu.isBoundedBorelCompactlySupported hd hvt), pushforwardFun_of_reflection]
  rfl
private lemma smeared_translateBy (hC : MultipleReflections.SymmetriesOnFacesAndReflectionIdentities.Statement)
    {d vt : ℝ} (hd : 0 < d) (hvt : 0 < vt) {u : AmbientSpace → ℝ} (hu : IsUnitBump d vt u) (k : ℕ) (v : Fin 4 → ℤ)
    (U : D.GaugeField) :
    smearedObservable D.L D.K u ((InfiniteLattice.shift (shiftPoint D k v)).pullbackField U) =
      smearedObservable D.L D.K (translateBy D.L D.K k v u) U := by
  rw [smeared_pullback hC _ (hu.isBoundedBorelCompactlySupported hd hvt), pushforwardFun_shiftPoint]
private lemma unitTorusMean_gridImage (hI : unitTorusMeasureSymmetricStatement)
    (hC : MultipleReflections.SymmetriesOnFacesAndReflectionIdentities.Statement)
    (hS : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main)
    {d vt : ℝ} (hd : 0 < d) (hvt : 0 < vt) {u : AmbientSpace → ℝ} (hu : IsUnitBump d vt u) (c : Fin 4 → ℤ) (k : ℕ)
    (v : Fin 4 → ℤ) :
    unitTorusMean D.L D.K D.β (gridImage g c (translateBy D.L D.K k v u)) = unitTorusMean D.L D.K D.β u := by
  have hm := isUnitBump_translateBy (D := D) hu k v
  calc ∫ U, smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v u)) U ∂unitTorusMeasure D.L D.K D.β
      = ∫ U, smearedObservable D.L D.K (translateBy D.L D.K k v u)
          ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) ∂unitTorusMeasure D.L D.K D.β :=
        integral_congr_ae (ae_of_all _ fun U => (smeared_gridImage g hC hd hvt hm c U).symm)
    _ = ∫ U, smearedObservable D.L D.K (translateBy D.L D.K k v u) U ∂unitTorusMeasure D.L D.K D.β :=
        integral_pullback_eq hI _ (smeared_isMeasBdd hS (hm.isBoundedBorelCompactlySupported hd hvt))
    _ = ∫ U, smearedObservable D.L D.K u ((InfiniteLattice.shift (shiftPoint D k v)).pullbackField U)
          ∂unitTorusMeasure D.L D.K D.β :=
        integral_congr_ae (ae_of_all _ fun U => (smeared_translateBy hC hd hvt hu k v U).symm)
    _ = ∫ U, smearedObservable D.L D.K u U ∂unitTorusMeasure D.L D.K D.β :=
        integral_pullback_eq hI _ (smeared_isMeasBdd hS (hu.isBoundedBorelCompactlySupported hd hvt))
private lemma covariance_gridImage (hI : unitTorusMeasureSymmetricStatement)
    (hC : MultipleReflections.SymmetriesOnFacesAndReflectionIdentities.Statement)
    (hS : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main)
    {d vt : ℝ} (hd : 0 < d) (hvt : 0 < vt) {f h : AmbientSpace → ℝ} (hf : IsUnitBump d vt f) (hh : IsUnitBump d vt h)
    (c : Fin 4 → ℤ) (k : ℕ) (v : Fin 4 → ℤ) :
    ∫ U, (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v f)) U - unitTorusMean D.L D.K D.β f) *
        (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v h)) U - unitTorusMean D.L D.K D.β h)
        ∂unitTorusMeasure D.L D.K D.β = unitTorusCovariance D.L D.K D.β f h := by
  have hmf := isUnitBump_translateBy (D := D) hf k v
  have hmh := isUnitBump_translateBy (D := D) hh k v
  have bb : ∀ {u : AmbientSpace → ℝ}, IsUnitBump d vt u → IsMeasBdd (smearedObservable D.L D.K u) := fun hu =>
    smeared_isMeasBdd hS (hu.isBoundedBorelCompactlySupported hd hvt)
  set cf := unitTorusMean D.L D.K D.β f
  set ch := unitTorusMean D.L D.K D.β h
  calc ∫ U, (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v f)) U - cf) *
        (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v h)) U - ch) ∂unitTorusMeasure D.L D.K D.β
      = ∫ U, (fun V => (smearedObservable D.L D.K (translateBy D.L D.K k v f) V - cf) *
            (smearedObservable D.L D.K (translateBy D.L D.K k v h) V - ch))
          ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) ∂unitTorusMeasure D.L D.K D.β :=
        integral_congr_ae (ae_of_all _ fun U => by
          simp only [smeared_gridImage g hC hd hvt hmf c U, smeared_gridImage g hC hd hvt hmh c U])
    _ = ∫ U, (smearedObservable D.L D.K (translateBy D.L D.K k v f) U - cf) *
            (smearedObservable D.L D.K (translateBy D.L D.K k v h) U - ch) ∂unitTorusMeasure D.L D.K D.β :=
        integral_pullback_eq hI _ (((bb hmf).sub (IsMeasBdd.const _)).mul ((bb hmh).sub (IsMeasBdd.const _)))
    _ = ∫ U, (fun V => (smearedObservable D.L D.K f V - cf) * (smearedObservable D.L D.K h V - ch))
          ((InfiniteLattice.shift (shiftPoint D k v)).pullbackField U) ∂unitTorusMeasure D.L D.K D.β :=
        integral_congr_ae (ae_of_all _ fun U => by
          simp only [smeared_translateBy hC hd hvt hf k v U, smeared_translateBy hC hd hvt hh k v U])
    _ = ∫ U, (smearedObservable D.L D.K f U - cf) * (smearedObservable D.L D.K h U - ch) ∂unitTorusMeasure D.L D.K D.β :=
        integral_pullback_eq hI _ (((bb hf).sub (IsMeasBdd.const _)).mul ((bb hh).sub (IsMeasBdd.const _)))
    _ = unitTorusCovariance D.L D.K D.β f h := rfl
end GridImages
section ReflectionNorms
private lemma rpow_sixteenth_le {A b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (h : |A| ≤ b ^ 16 + t) :
    |A| ^ (1 / 16 : ℝ) ≤ b + t ^ (1 / 16 : ℝ) := by
  have h1 : |A| ^ (1 / 16 : ℝ) ≤ (b ^ 16 + t) ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (abs_nonneg _) h (by norm_num)
  refine h1.trans ?_
  lift b to NNReal using hb
  lift t to NNReal using ht
  have h2 := NNReal.rpow_add_le_add_rpow (b ^ 16) t (p := 1 / 16) (by norm_num) (by norm_num)
  have h3 : ((b ^ 16 : NNReal) ^ (1 / 16 : ℝ)) = b := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    norm_num
  rw [h3] at h2
  exact_mod_cast h2
private lemma avg_sub_const {V : Type*} {Q : Finset V} (hQ : Q.Nonempty) (a : V → ℝ) (κ : ℝ) :
    (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, (a v - κ) = (Q.card : ℝ)⁻¹ * ∑ v ∈ Q, a v - κ := by
  have hc : (Q.card : ℝ) ≠ 0 := by exact_mod_cast hQ.card_pos.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
private lemma zero_mem_shiftSet (m : ℕ) : (0 : Fin 4 → ℤ) ∈ shiftSet m := by
  refine Fintype.mem_piFinset.mpr fun μ => ?_
  simp
variable {D : ChessboardSetup} (g : ReflectionGrid D)
private lemma card_indexBox : Fintype.card ↥(minimalCounts D).indexBox = 16 := by
  rw [Fintype.card_coe]
  simp [EvenIndexVector.indexBox, cubicCounts, Fintype.card_piFinset]
private lemma abs_sub_selection_le (hI : unitTorusMeasureSymmetricStatement)
    (hC : MultipleReflections.SymmetriesOnFacesAndReflectionIdentities.Statement)
    (hS : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main)
    (hG : MirrorGridsAllSides.ReflectionGridProperties) (hq : g.q = 0) (hs : g.HasAdmissibleSide)
    (k m : ℕ) {d vt : ℝ} (hd : 0 < d) (hvt : 0 < vt) {f h : AmbientSpace → ℝ} (hp : IsNormalizedTestPair d vt f h)
    (hin : ∀ v ∈ shiftSet m, IsInteriorBy g (d / 2) (translateBy D.L D.K k v f) ∧
      IsInteriorBy g (d / 2) (translateBy D.L D.K k v h))
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω') (Φ : (AmbientSpace → ℝ) → Ω' → ℝ) (ε : ℝ)
    (hcmp : ∀ (p : ℕ) (φ : Fin p → AmbientSpace → ℝ), p ≤ 32 → IsSeparatedBumpFamily d vt φ → ∀ I : Finset (Fin p),
      |∫ U, ∏ i ∈ I, (smearedObservable D.L D.K (φ i) U - unitTorusMean D.L D.K D.β (φ i)) ∂unitTorusMeasure D.L D.K D.β -
        ∫ u, ∏ i ∈ I, Φ (φ i) u ∂μ'| ≤ ε)
    (w : ↥(minimalCounts D).indexBox → Fin 4 → ℤ) (hw : ∀ c, w c ∈ shiftSet m)
    (J : Finset (↥(minimalCounts D).indexBox × Bool)) :
    |∫ U, ∏ j ∈ J, (smearedObservable D.L D.K (gridImage g j.1 (translateBy D.L D.K k (w j.1) (pairSelect f h j.2))) U -
        unitTorusMean D.L D.K D.β (pairSelect f h j.2)) ∂unitTorusMeasure D.L D.K D.β -
      ∫ u, ∏ j ∈ J, Φ (gridImage g j.1 (translateBy D.L D.K k (w j.1) (pairSelect f h j.2))) u ∂μ'| ≤ ε := by
  classical
  obtain ⟨hf, hh, -⟩ := isUnitBump_of_testPair hp
  have hmark : ∀ b, IsUnitBump d vt (pairSelect f h b) := fun b => by cases b <;> assumption
  have hp32 : Fintype.card (↥(minimalCounts D).indexBox × Bool) ≤ 32 := by
    simp [Fintype.card_prod, card_indexBox (D := D)]
  have hfam := separated_of_selection g hG hq hs k m hd hp hin w hw (Fintype.equivFin _).symm
  have h1 := hcmp _ _ hp32 hfam (J.map (Fintype.equivFin _).toEmbedding)
  simp only [Finset.prod_map, Equiv.coe_toEmbedding, Equiv.symm_apply_apply] at h1
  have hmean : ∀ j : ↥(minimalCounts D).indexBox × Bool,
      unitTorusMean D.L D.K D.β (gridImage g j.1 (translateBy D.L D.K k (w j.1) (pairSelect f h j.2))) =
        unitTorusMean D.L D.K D.β (pairSelect f h j.2) :=
    fun j => unitTorusMean_gridImage g hI hC hS hd hvt (hmark _) _ k _
  simpa only [hmean] using h1
private lemma centeredObservable_pullback (hC : MultipleReflections.SymmetriesOnFacesAndReflectionIdentities.Statement)
    {d vt : ℝ} (hd : 0 < d) (hvt : 0 < vt) {u : AmbientSpace → ℝ} (hu : IsUnitBump d vt u) (c : Fin 4 → ℤ) (k : ℕ)
    (v : Fin 4 → ℤ) (U : D.GaugeField) :
    centeredObservable D.L D.K k D.β v u ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) =
      smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v u)) U - unitTorusMean D.L D.K D.β u :=
  congrArg (fun t => t - unitTorusMean D.L D.K D.β u) (smeared_gridImage g hC hd hvt (isUnitBump_translateBy hu k v) c U)
set_option maxHeartbeats 1000000 in
private theorem unitTorus_bounds (hA : LawInAState.twoCellPeriodicMeanStatement)
    (hI : unitTorusMeasureSymmetricStatement)
    (hC : MultipleReflections.SymmetriesOnFacesAndReflectionIdentities.Statement)
    (hS : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main)
    (hG : MirrorGridsAllSides.ReflectionGridProperties) (hq : g.q = 0) (hK : 2 ≤ (D.K : ℕ))
    (k m : ℕ) {d vt : ℝ} (hd : 0 < d) (hvt : 0 < vt) {f h : AmbientSpace → ℝ} (hp : IsNormalizedTestPair d vt f h)
    (hin : ∀ v ∈ shiftSet m, IsInteriorBy g (d / 2) (translateBy D.L D.K k v f) ∧
      IsInteriorBy g (d / 2) (translateBy D.L D.K k v h))
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (Φ : (AmbientSpace → ℝ) → Ω' → ℝ)
    (ε M : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hmem : ∀ φ, IsUnitBump d vt φ → MemLp (Φ φ) 32 μ' ∧ eLpNorm (Φ φ) 32 μ' ≤ ENNReal.ofReal M)
    (hcmp : ∀ (p : ℕ) (φ : Fin p → AmbientSpace → ℝ), p ≤ 32 → IsSeparatedBumpFamily d vt φ → ∀ I : Finset (Fin p),
      |∫ U, ∏ i ∈ I, (smearedObservable D.L D.K (φ i) U - unitTorusMean D.L D.K D.β (φ i)) ∂unitTorusMeasure D.L D.K D.β -
        ∫ u, ∏ i ∈ I, Φ (φ i) u ∂μ'| ≤ ε) :
    (∀ b : ℝ, 0 ≤ b → (∀ c ∈ (minimalCounts D).indexBox,
        eLpNorm (fun u => ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
            Φ (gridImage g c (translateBy D.L D.K k v f)) u * Φ (gridImage g c (translateBy D.L D.K k v h)) u -
          unitTorusCovariance D.L D.K D.β f h) 16 μ' ≤ ENNReal.ofReal b) →
      reflectionNorm g (averagedCovarianceDefect D.L D.K k m D.β f h) ≤
        b + (ε * (1 + |unitTorusCovariance D.L D.K D.β f h|) ^ 16) ^ (1 / 16 : ℝ)) ∧
    (∀ (b : ℝ) (u₀ : AmbientSpace → ℝ), 0 ≤ b → (u₀ = f ∨ u₀ = h) → (∀ c ∈ (minimalCounts D).indexBox,
        eLpNorm (fun u => ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m, Φ (gridImage g c (translateBy D.L D.K k v u₀)) u)
          16 μ' ≤ ENNReal.ofReal b) →
      reflectionNorm g (averagedCenteredObservable D.L D.K k m D.β u₀) ≤ b + ε ^ (1 / 16 : ℝ)) ∧
    (∀ v ∈ shiftSet m, |unitTorusCovariance D.L D.K D.β f h -
      ∫ u, Φ (translateBy D.L D.K k v f) u * Φ (translateBy D.L D.K k v h) u ∂μ'| ≤ ε) ∧
    |unitTorusCovariance D.L D.K D.β f h| ≤ M ^ 2 + ε := by
  classical
  have hs : g.HasAdmissibleSide := hasAdmissibleSide_of_q_eq_zero g hq hK
  have : IsProbabilityMeasure (unitTorusMeasure D.L D.K D.β) := (hI D).1
  obtain ⟨hf, hh, -⟩ := isUnitBump_of_testPair hp
  have hQ : (shiftSet m).Nonempty := ⟨0, zero_mem_shiftSet m⟩
  have hcard := card_indexBox (D := D)
  have hmark : ∀ b, IsUnitBump d vt (pairSelect f h b) := fun b => by cases b <;> assumption
  have himg : ∀ {u : AmbientSpace → ℝ}, IsUnitBump d vt u → ∀ (c : Fin 4 → ℤ) (v : Fin 4 → ℤ),
      IsUnitBump d vt (gridImage g c (translateBy D.L D.K k v u)) :=
    fun hu c v => isUnitBump_gridImage g (isUnitBump_translateBy hu k v) c
  have hO : ∀ {u : AmbientSpace → ℝ}, IsUnitBump d vt u → ∀ (c : Fin 4 → ℤ) (v : Fin 4 → ℤ),
      IsMeasBdd (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v u))) :=
    fun hu c v => smeared_isMeasBdd hS ((himg hu c v).isBoundedBorelCompactlySupported hd hvt)
  have hcomp := abs_sub_selection_le g hI hC hS hG hq hs k m hd hvt hp hin μ' Φ ε hcmp
  have htwo : ∀ v ∈ shiftSet m, |unitTorusCovariance D.L D.K D.β f h -
      ∫ u, Φ (translateBy D.L D.K k v f) u * Φ (translateBy D.L D.K k v h) u ∂μ'| ≤ ε := by
    intro v hv
    have h0 : (0 : Fin 4 → ℤ) ∈ (minimalCounts D).indexBox := by
      refine Fintype.mem_piFinset.mpr fun μ => ?_
      simp [cubicCounts]
    have hne : ((⟨0, h0⟩ : ↥(minimalCounts D).indexBox), true) ≠ (⟨0, h0⟩, false) := by simp
    have h1 := hcomp (fun _ => v) (fun _ => hv) {(⟨0, h0⟩, true), (⟨0, h0⟩, false)}
    simp only [Finset.prod_pair hne, pairSelect, gridImage_zero g hG hs] at h1
    have hcv := covariance_gridImage g hI hC hS hd hvt hf hh 0 k v
    simp only [gridImage_zero g hG hs] at hcv
    rwa [hcv] at h1
  have hkap : |unitTorusCovariance D.L D.K D.β f h| ≤ M ^ 2 + ε := by
    have h1 := htwo 0 (zero_mem_shiftSet m)
    have hm : ∀ b, IsUnitBump d vt (translateBy D.L D.K k 0 (pairSelect f h b)) :=
      fun b => isUnitBump_translateBy (hmark b) k 0
    have h2 := abs_integral_prod_le_pow (ι := Bool) (μ := μ') 2 two_ne_zero (by simp)
      (fun b => Φ (translateBy D.L D.K k 0 (pairSelect f h b))) (fun b => (hmem _ (hm b)).1.aestronglyMeasurable) M hM
      (fun b => (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hmem _ (hm b)).1.aestronglyMeasurable).trans
        (hmem _ (hm b)).2)
    simp only [Fintype.prod_bool, pairSelect] at h2
    have h3 := abs_sub_abs_le_abs_sub (unitTorusCovariance D.L D.K D.β f h)
      (∫ u, Φ (translateBy D.L D.K k 0 f) u * Φ (translateBy D.L D.K k 0 h) u ∂μ')
    linarith
  refine ⟨fun b hb0 hbnd => ?_, fun b u₀ hb0 hu₀ hbnd => ?_, htwo, hkap⟩
  · have hi : ∀ (w : ↥(minimalCounts D).indexBox → Fin 4 → ℤ) (I : Finset ↥(minimalCounts D).indexBox),
        Integrable (fun U => ∏ c ∈ I,
          (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k (w c) f)) U - unitTorusMean D.L D.K D.β f) *
            (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k (w c) h)) U - unitTorusMean D.L D.K D.β h))
          (unitTorusMeasure D.L D.K D.β) := fun w I =>
      (IsMeasBdd.prod I fun c _ => ((hO hf c _).sub (IsMeasBdd.const _)).mul ((hO hh c _).sub (IsMeasBdd.const _))).integrable _
    have hi' : ∀ (w : ↥(minimalCounts D).indexBox → Fin 4 → ℤ) (I : Finset ↥(minimalCounts D).indexBox),
        Integrable (fun u => ∏ c ∈ I, Φ (gridImage g c (translateBy D.L D.K k (w c) f)) u *
          Φ (gridImage g c (translateBy D.L D.K k (w c) h)) u) μ' := fun w I => by
      have hJ : (I ×ˢ (Finset.univ : Finset Bool)).card ≤ 32 := by
        have h1 : I.card ≤ 16 := hcard ▸ Finset.card_le_univ I
        rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
        omega
      have h1 := integrable_finset_prod_of_memLp (μ := μ') (I ×ˢ (Finset.univ : Finset Bool)) hJ
        (fun j => Φ (gridImage g j.1 (translateBy D.L D.K k (w j.1) (pairSelect f h j.2))))
        (fun j _ => (hmem _ (himg (hmark _) _ _)).1)
      simpa only [Finset.prod_product, Fintype.prod_bool, pairSelect] using h1
    have hc : ∀ w : ↥(minimalCounts D).indexBox → Fin 4 → ℤ, (∀ c, w c ∈ shiftSet m) →
        ∀ I : Finset ↥(minimalCounts D).indexBox,
        |∫ U, ∏ c ∈ I,
            ((smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k (w c) f)) U - unitTorusMean D.L D.K D.β f) *
              (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k (w c) h)) U - unitTorusMean D.L D.K D.β h))
            ∂unitTorusMeasure D.L D.K D.β -
          ∫ u, ∏ c ∈ I, (Φ (gridImage g c (translateBy D.L D.K k (w c) f)) u *
            Φ (gridImage g c (translateBy D.L D.K k (w c) h)) u) ∂μ'| ≤ ε := fun w hw I => by
      have h1 := hcomp w hw (I ×ˢ (Finset.univ : Finset Bool))
      simpa only [Finset.prod_product, Fintype.prod_bool, pairSelect] using h1
    have hclose := abs_integral_prod_avg_sub_le (ι := ↥(minimalCounts D).indexBox) (unitTorusMeasure D.L D.K D.β) μ'
      (shiftSet m) hQ
      (fun c v U => (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v f)) U -
          unitTorusMean D.L D.K D.β f) *
        (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v h)) U - unitTorusMean D.L D.K D.β h))
      (fun c v u => Φ (gridImage g c (translateBy D.L D.K k v f)) u * Φ (gridImage g c (translateBy D.L D.K k v h)) u)
      (unitTorusCovariance D.L D.K D.β f h) ε hi hi' hc
    rw [hcard] at hclose
    have hval : ∀ (c : Fin 4 → ℤ) (U : D.GaugeField),
        averagedCovarianceDefect D.L D.K k m D.β f h
            ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) =
          ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
            ((smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v f)) U - unitTorusMean D.L D.K D.β f) *
              (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v h)) U - unitTorusMean D.L D.K D.β h) -
            unitTorusCovariance D.L D.K D.β f h) := by
      intro c U
      change ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
        (centeredObservable D.L D.K k D.β v f ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) *
          centeredObservable D.L D.K k D.β v h ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) -
          unitTorusCovariance D.L D.K D.β f h) = _
      refine congrArg (HMul.hMul ((shiftSet m).card : ℝ)⁻¹) (Finset.sum_congr rfl fun v _ => ?_)
      rw [centeredObservable_pullback g hC hd hvt hf c k v U, centeredObservable_pullback g hC hd hvt hh c k v U]
    have hMB : ∀ c ∈ (minimalCounts D).indexBox, IsMeasBdd fun U => averagedCovarianceDefect D.L D.K k m D.β f h
        ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) := by
      intro c _
      rw [show (fun U => averagedCovarianceDefect D.L D.K k m D.β f h
        ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U)) = _ from funext (hval c)]
      exact (IsMeasBdd.const _).mul (IsMeasBdd.sum _ fun v _ =>
        (((hO hf c v).sub (IsMeasBdd.const _)).mul ((hO hh c v).sub (IsMeasBdd.const _))).sub (IsMeasBdd.const _))
    rw [reflectionNorm_eq g hA hq _ hMB]
    have hA1 : ∫ U, ∏ c ∈ (minimalCounts D).indexBox, averagedCovarianceDefect D.L D.K k m D.β f h
          ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) ∂unitTorusMeasure D.L D.K D.β =
        ∫ U, ∏ c : ↥(minimalCounts D).indexBox, (((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
            ((smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v f)) U - unitTorusMean D.L D.K D.β f) *
              (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v h)) U - unitTorusMean D.L D.K D.β h) -
            unitTorusCovariance D.L D.K D.β f h)) ∂unitTorusMeasure D.L D.K D.β :=
      integral_congr_ae (ae_of_all _ fun U => by
        beta_reduce
        rw [← Finset.prod_coe_sort]
        exact Finset.prod_congr rfl fun c _ => hval c U)
    rw [hA1]
    simp only [avg_sub_const hQ] at hclose
    have hY := abs_integral_prod_le_pow (ι := ↥(minimalCounts D).indexBox) (μ := μ') 16 (by norm_num) hcard
      (fun c u => ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
        Φ (gridImage g c (translateBy D.L D.K k v f)) u * Φ (gridImage g c (translateBy D.L D.K k v h)) u -
          unitTorusCovariance D.L D.K D.β f h)
      (fun c => ((Finset.aestronglyMeasurable_fun_sum _ fun v _ =>
        (hmem _ (himg hf c v)).1.aestronglyMeasurable.mul (hmem _ (himg hh c v)).1.aestronglyMeasurable).const_mul _).sub
        aestronglyMeasurable_const)
      b hb0 (fun c => by rw [Nat.cast_ofNat]; exact hbnd c c.2)
    refine rpow_sixteenth_le hb0 (mul_nonneg hε (by positivity)) ?_
    simp only [avg_sub_const hQ]
    have h3 := abs_sub_abs_le_abs_sub
      (∫ U, ∏ c : ↥(minimalCounts D).indexBox, (((shiftSet m).card : ℝ)⁻¹ * (∑ v ∈ shiftSet m,
            ((smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v f)) U - unitTorusMean D.L D.K D.β f) *
              (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v h)) U - unitTorusMean D.L D.K D.β h))) -
            unitTorusCovariance D.L D.K D.β f h) ∂unitTorusMeasure D.L D.K D.β)
      (∫ u, ∏ c : ↥(minimalCounts D).indexBox, (((shiftSet m).card : ℝ)⁻¹ * (∑ v ∈ shiftSet m,
          Φ (gridImage g c (translateBy D.L D.K k v f)) u * Φ (gridImage g c (translateBy D.L D.K k v h)) u) -
          unitTorusCovariance D.L D.K D.β f h) ∂μ')
    linarith
  · obtain ⟨t, rfl⟩ : ∃ t, u₀ = pairSelect f h t := by
      rcases hu₀ with rfl | rfl
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    have hu := hmark t
    have hi : ∀ (w : ↥(minimalCounts D).indexBox → Fin 4 → ℤ) (I : Finset ↥(minimalCounts D).indexBox),
        Integrable (fun U => ∏ c ∈ I,
          (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k (w c) (pairSelect f h t))) U -
          unitTorusMean D.L D.K D.β (pairSelect f h t))) (unitTorusMeasure D.L D.K D.β) := fun w I =>
      (IsMeasBdd.prod I fun c _ => (hO hu c _).sub (IsMeasBdd.const _)).integrable _
    have hi' : ∀ (w : ↥(minimalCounts D).indexBox → Fin 4 → ℤ) (I : Finset ↥(minimalCounts D).indexBox),
        Integrable (fun u => ∏ c ∈ I, Φ (gridImage g c (translateBy D.L D.K k (w c) (pairSelect f h t))) u) μ' :=
      fun w I => by
      have h1 : I.card ≤ 16 := hcard ▸ Finset.card_le_univ I
      exact integrable_finset_prod_of_memLp (μ := μ') I (by omega)
        (fun c => Φ (gridImage g c (translateBy D.L D.K k (w c) (pairSelect f h t)))) (fun c _ => (hmem _ (himg hu _ _)).1)
    have hc : ∀ w : ↥(minimalCounts D).indexBox → Fin 4 → ℤ, (∀ c, w c ∈ shiftSet m) →
        ∀ I : Finset ↥(minimalCounts D).indexBox,
        |∫ U, ∏ c ∈ I, (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k (w c) (pairSelect f h t))) U -
              unitTorusMean D.L D.K D.β (pairSelect f h t)) ∂unitTorusMeasure D.L D.K D.β -
          ∫ u, ∏ c ∈ I, Φ (gridImage g c (translateBy D.L D.K k (w c) (pairSelect f h t))) u ∂μ'| ≤ ε := fun w hw I => by
      have h1 := hcomp w hw (I ×ˢ {t})
      simpa only [Finset.prod_product, Finset.prod_singleton] using h1
    have hclose := abs_integral_prod_avg_sub_le (ι := ↥(minimalCounts D).indexBox) (unitTorusMeasure D.L D.K D.β) μ'
      (shiftSet m) hQ
      (fun c v U => smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v (pairSelect f h t))) U -
        unitTorusMean D.L D.K D.β (pairSelect f h t))
      (fun c v u => Φ (gridImage g c (translateBy D.L D.K k v (pairSelect f h t))) u) 0 ε hi hi' hc
    simp only [sub_zero, abs_zero, add_zero, one_pow, mul_one] at hclose
    have hval : ∀ (c : Fin 4 → ℤ) (U : D.GaugeField),
        averagedCenteredObservable D.L D.K k m D.β (pairSelect f h t)
            ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) =
          ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
            (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v (pairSelect f h t))) U -
              unitTorusMean D.L D.K D.β (pairSelect f h t)) := by
      intro c U
      change ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
        centeredObservable D.L D.K k D.β v (pairSelect f h t)
          ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) = _
      refine congrArg (HMul.hMul ((shiftSet m).card : ℝ)⁻¹) (Finset.sum_congr rfl fun v _ => ?_)
      rw [centeredObservable_pullback g hC hd hvt hu c k v U]
    have hMB : ∀ c ∈ (minimalCounts D).indexBox, IsMeasBdd fun U =>
        averagedCenteredObservable D.L D.K k m D.β (pairSelect f h t)
        ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) := by
      intro c _
      rw [show (fun U => averagedCenteredObservable D.L D.K k m D.β (pairSelect f h t)
        ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U)) = _ from funext (hval c)]
      exact (IsMeasBdd.const _).mul (IsMeasBdd.sum _ fun v _ => (hO hu c v).sub (IsMeasBdd.const _))
    rw [reflectionNorm_eq g hA hq _ hMB]
    have hA1 : ∫ U, ∏ c ∈ (minimalCounts D).indexBox, averagedCenteredObservable D.L D.K k m D.β (pairSelect f h t)
          ((g.toLatticeSym (g.mover (g.cell 0) (g.cell c))).pullbackField U) ∂unitTorusMeasure D.L D.K D.β =
        ∫ U, ∏ c : ↥(minimalCounts D).indexBox, (((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
            (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v (pairSelect f h t))) U -
              unitTorusMean D.L D.K D.β (pairSelect f h t))) ∂unitTorusMeasure D.L D.K D.β :=
      integral_congr_ae (ae_of_all _ fun U => by
        beta_reduce
        rw [← Finset.prod_coe_sort]
        exact Finset.prod_congr rfl fun c _ => hval c U)
    rw [hA1]
    have hY := abs_integral_prod_le_pow (ι := ↥(minimalCounts D).indexBox) (μ := μ') 16 (by norm_num) hcard
      (fun c u => ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
        Φ (gridImage g c (translateBy D.L D.K k v (pairSelect f h t))) u)
      (fun c => (Finset.aestronglyMeasurable_fun_sum _ fun v _ =>
        (hmem _ (himg hu c v)).1.aestronglyMeasurable).const_mul _)
      b hb0 (fun c => by rw [Nat.cast_ofNat]; exact hbnd c c.2)
    refine rpow_sixteenth_le hb0 hε ?_
    have h3 := abs_sub_abs_le_abs_sub
      (∫ U, ∏ c : ↥(minimalCounts D).indexBox, (((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
            (smearedObservable D.L D.K (gridImage g c (translateBy D.L D.K k v (pairSelect f h t))) U -
              unitTorusMean D.L D.K D.β (pairSelect f h t))) ∂unitTorusMeasure D.L D.K D.β)
      (∫ u, ∏ c : ↥(minimalCounts D).indexBox, (((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m,
          Φ (gridImage g c (translateBy D.L D.K k v (pairSelect f h t))) u) ∂μ')
    linarith
end ReflectionNorms
section ErrorConstants
private lemma markError_absorbs (ℓ : TorusLumps.StepParameters) {x C₁ C₂ κ : ℝ} (hx : 3 ≤ x) (hrt : 0 < ℓ.rt)
    (hκ : |κ| ≤ (x ^ C₂) ^ 2 + markError ℓ C₁ x) :
    markError ℓ C₁ x ≤ markError ℓ (max C₁ 0 + 16 * (1 + 2 * max C₂ 0 + max C₁ 0)) x ∧
    markError ℓ C₁ x * (1 + |κ|) ^ 16 ≤
      markError ℓ (max C₁ 0 + 16 * (1 + 2 * max C₂ 0 + max C₁ 0)) x := by
  set A := max C₁ 0 with hA
  set B := max C₂ 0 with hB
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  set e := Real.exp (-(4 * ℓ.rt * (clusterRange x : ℝ))) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ 4 * ℓ.rt * (clusterRange x : ℝ) := by positivity
    linarith)
  have hE : ∀ C, markError ℓ C x = x ^ C * e := fun C => rfl
  have hmono : ∀ {u v : ℝ}, u ≤ v → x ^ u ≤ x ^ v := fun h => Real.rpow_le_rpow_of_exponent_le hx1 h
  have hone : ∀ {u : ℝ}, 0 ≤ u → 1 ≤ x ^ u := fun h => Real.one_le_rpow hx1 h
  have hεA : markError ℓ C₁ x ≤ x ^ A * e := by
    rw [hE]
    exact mul_le_mul_of_nonneg_right (hmono (le_max_left _ _)) he0.le
  have hsq : (x ^ C₂) ^ 2 ≤ x ^ (2 * B) := by
    have h1 : x ^ C₂ ≤ x ^ B := hmono (le_max_left _ _)
    have h2 : (x ^ B) ^ 2 = x ^ (2 * B) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      norm_num
      ring
    rw [← h2]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hεle : markError ℓ C₁ x ≤ x ^ A := hεA.trans (by
    have : 0 < x ^ A := by positivity
    nlinarith)
  have hbase : 1 + |κ| ≤ x ^ (1 + 2 * B + A) := by
    have h1 : x ^ (2 * B) ≤ x ^ (2 * B + A) := hmono (by linarith)
    have h2 : x ^ A ≤ x ^ (2 * B + A) := hmono (by linarith)
    have h3 : 1 ≤ x ^ (2 * B + A) := hone (by linarith)
    have h4 : x ^ (1 + 2 * B + A) = x * x ^ (2 * B + A) := by
      rw [add_assoc, Real.rpow_add hx0, Real.rpow_one]
    rw [h4]
    nlinarith
  have hpow : (1 + |κ|) ^ 16 ≤ x ^ (16 * (1 + 2 * B + A)) := by
    have h1 : (x ^ (1 + 2 * B + A)) ^ 16 = x ^ (16 * (1 + 2 * B + A)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      norm_num
      ring
    rw [← h1]
    exact pow_le_pow_left₀ (by positivity) hbase 16
  have hsplit : x ^ (A + 16 * (1 + 2 * B + A)) = x ^ A * x ^ (16 * (1 + 2 * B + A)) := Real.rpow_add hx0 _ _
  have hbig : 1 ≤ x ^ (16 * (1 + 2 * B + A)) := hone (by positivity)
  constructor
  · rw [hE (A + 16 * (1 + 2 * B + A)), hsplit]
    refine hεA.trans ?_
    have h1 : 0 < x ^ A := by positivity
    have h2 : x ^ A * e ≤ x ^ A * x ^ (16 * (1 + 2 * B + A)) * e := by
      have : x ^ A * 1 ≤ x ^ A * x ^ (16 * (1 + 2 * B + A)) := mul_le_mul_of_nonneg_left hbig h1.le
      nlinarith
    exact h2
  · rw [hE (A + 16 * (1 + 2 * B + A)), hsplit]
    have h1 : 0 ≤ x ^ A * e := by positivity
    calc markError ℓ C₁ x * (1 + |κ|) ^ 16
        ≤ (x ^ A * e) * x ^ (16 * (1 + 2 * B + A)) :=
          mul_le_mul hεA hpow (by positivity) h1
      _ = x ^ A * x ^ (16 * (1 + 2 * B + A)) * e := by ring
end ErrorConstants
theorem reflectionNormToBoxStatement_holds (hP : centeredProductsAtLevelStatement)
    (hM : centeredResponseMomentsStatement) (hA : LawInAState.twoCellPeriodicMeanStatement)
    (hI : unitTorusMeasureSymmetricStatement)
    (hC : MultipleReflections.SymmetriesOnFacesAndReflectionIdentities.Statement)
    (hS : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main)
    (hG : MirrorGridsAllSides.ReflectionGridProperties)
    (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) : reflectionNormToBoxStatement := by
  refine ((hP.and hM).and HoldsForShapes.params).mono fun Tb y Kr Xi vt hall => ?_
  obtain ⟨⟨gP, gM⟩, hD, hy, -, -, -, h0, -⟩ := hall
  obtain ⟨C₁, d₁, hd₁, k₁⟩ := gP
  obtain ⟨C₂, d₂, hd₂, k₂⟩ := gM
  refine ⟨max C₁ 0 + 16 * (1 + 2 * max C₂ 0 + max C₁ 0), min d₁ d₂, lt_min hd₁ hd₂,
    fun d hd hdle D al T hDL hCh k m x hk hx hm g hgq f h hp hin => ?_⟩
  obtain ⟨⟨L, hLs, K, mm⟩, β, hβ⟩ := D
  obtain rfl : L = (Tb.stepParameters y).side := hDL
  subst hk hx hm
  have hfits := hD.fits y hy
  have : IsProbabilityMeasure (stageLaw T β K (separationLevel (Tb.stepParameters y) β K d)) :=
    (hT (Tb.stepParameters y) hfits hD.L_gt T hCh.isCutoff_bottom hCh.marksMeasurable β al
      (separationLevel (Tb.stepParameters y) β K d) _).1
  have hx3 : 3 ≤ couplingAtSeparation (Tb.stepParameters y) β K d := by
    have h2 := hCh.isFlowDatum.le_coupling (separationLevel (Tb.stepParameters y) β K d)
      (by unfold separationLevel; exact @Nat.findGreatest_le _ (fun _ => Classical.propDecidable _) K)
    have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ 1600 :=
      le_trans (by norm_num : (3 : ℝ) ≤ (2 : ℝ) ^ 2) (pow_le_pow_right₀ (by norm_num) (by norm_num))
    have h4 : (2 : ℝ) ^ 1600 ≤ Tb.floorMin := le_max_right _ _
    exact ((h3.trans h4).trans hy).trans h2
  have hε : 0 ≤ markError (Tb.stepParameters y) C₁ (couplingAtSeparation (Tb.stepParameters y) β K d) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le
  obtain ⟨c1, c2, c3, c4⟩ := unitTorus_bounds g hA hI hC hS hG hgq hCh.isFlowDatum.two_le
    (separationLevel (Tb.stepParameters y) β K d)
    (averagingRadius (couplingAtSeparation (Tb.stepParameters y) β K d)) hd h0 hp hin
    (stageLaw T β K (separationLevel (Tb.stepParameters y) β K d))
    (fun φ => centeredBoxResponse T β al K (separationLevel (Tb.stepParameters y) β K d) φ)
    (markError (Tb.stepParameters y) C₁ (couplingAtSeparation (Tb.stepParameters y) β K d))
    (couplingAtSeparation (Tb.stepParameters y) β K d ^ C₂) hε (by positivity)
    (fun φ hφ => k₂ d hd (hdle.trans (min_le_right _ _)) K β al T hCh φ hφ.separatedFamily_one)
    (fun p φ hp32 hfam I => k₁ d hd (hdle.trans (min_le_left _ _)) K β al T hCh p φ hp32 hfam I)
  obtain ⟨e1, e2⟩ := markError_absorbs (Tb.stepParameters y) hx3 hD.rt_pos c4
  refine ⟨fun b hb0 hb => ?_, fun b w hb0 hw hb => ?_, fun v hv => ?_⟩
  · exact (c1 b hb0 hb).trans (add_le_add le_rfl (Real.rpow_le_rpow (mul_nonneg hε (by positivity)) e2 (by norm_num)))
  · exact (c2 b w hb0 hw hb).trans (add_le_add le_rfl (Real.rpow_le_rpow hε e1 (by norm_num)))
  · exact (c3 v hv).trans e1
end YangMills.Construction.StateLaws
end
