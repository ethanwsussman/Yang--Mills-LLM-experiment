import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacing
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import YangMills.Construction.Lattice.WilsonActionAsAPlaquetteSumAndSymmetriesOfProductHaar
import YangMills.Construction.Lattice.WilsonCumulantWellPosedness
import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsOfSeparatedFunctions
import Mathlib
import YangMills.Construction.SystemOfAdmissibleConstants.OneProductOfPieces
import YangMills.Construction.SystemOfAdmissibleConstants.SizeOfAnObservableOnABall
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSide
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.SeparatedMoments
open ChessboardTori ReflectedCopies
def FineCaseMomentBound : Prop :=
  ∀ (D : ChessboardSetup) (A b M R d l : ℝ) (n : ℕ), 1 ≤ A → 1 ≤ b → 1 ≤ M → 0 < R → 0 < d → d ≤ 1 → 2 ≤ n →
    CopyInequality D A b → IsMaximalScalePower D.L d l →
    max (2 ^ 6 * (n : ℝ)) ((D.L : ℝ) ^ 2) ≤ l / D.mesh →
      CentredMomentBound D M R d (fineConstant D.L A b R n d) n
end YangMills.Construction.SeparatedMoments
end

open MeasureTheory
noncomputable section
namespace YangMills.Construction
open TestFunctions TorusMetric ChessboardTori ReflectedCopies SeparatedMoments AdmissibleConstants
open InfiniteLattice (AmbientSpace periodicGibbsSet smearedEnergy)
namespace SystemOfAdmissibleConstants.FineCaseMoments
private def AEBounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  AEStronglyMeasurable X μ ∧ ∃ C : ℝ, ∀ᵐ ω ∂μ, |X ω| ≤ C
private theorem AEBounded.integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (h : AEBounded μ X) : Integrable X μ := by
  obtain ⟨hm, C, hC⟩ := h
  exact Integrable.of_bound hm C (hC.mono fun ω hω => by simpa [Real.norm_eq_abs] using hω)
private theorem AEBounded.sub_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (h : AEBounded μ X) (c : ℝ) : AEBounded μ fun ω => X ω - c := by
  obtain ⟨hm, C, hC⟩ := h
  refine ⟨hm.sub aestronglyMeasurable_const, C + |c|, hC.mono fun ω hω => ?_⟩
  exact (abs_sub _ _).trans (by linarith)
private theorem AEBounded.mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (h : AEBounded μ X) (h' : AEBounded μ Y) : AEBounded μ fun ω => X ω * Y ω := by
  obtain ⟨hm, C, hC⟩ := h
  obtain ⟨hm', C', hC'⟩ := h'
  refine ⟨hm.mul hm', C * C', ?_⟩
  filter_upwards [hC, hC'] with ω hω hω'
  rw [abs_mul]
  exact mul_le_mul hω hω' (abs_nonneg _) ((abs_nonneg _).trans hω)
private theorem AEBounded.prod {Ω κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (s : Finset κ)
    {F : κ → Ω → ℝ} (h : ∀ i ∈ s, AEBounded μ (F i)) : AEBounded μ fun ω => ∏ i ∈ s, F i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using aestronglyMeasurable_const, 1, by simp⟩
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
private theorem abs_integral_centred_prod_sum_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {k : ℕ} (P : Fin k → Finset ι) (Y : Fin k → ι → Ω → ℝ)
    (O : Fin k → Ω → ℝ) (W : Fin k → ι → ℝ) (hY : ∀ i, ∀ α ∈ P i, AEBounded μ (Y i α))
    (hO : ∀ i ω, O i ω = ∑ α ∈ P i, Y i α ω)
    (hB : ∀ c : Fin k → ι, (∀ i, c i ∈ P i) →
      |∫ ω, ∏ i, (Y i (c i) ω - ∫ ω', Y i (c i) ω' ∂μ) ∂μ| ≤ ∏ i, W i (c i)) :
    |∫ ω, ∏ i, (O i ω - ∫ ω', O i ω' ∂μ) ∂μ| ≤ ∏ i, ∑ α ∈ P i, W i α := by
  classical
  have hmean : ∀ i, ∫ ω, O i ω ∂μ = ∑ α ∈ P i, ∫ ω, Y i α ω ∂μ := fun i => by
    simp_rw [hO i]
    exact integral_finsetSum _ fun α hα => (hY i α hα).integrable
  have hcent : ∀ ω, ∏ i, (O i ω - ∫ ω', O i ω' ∂μ) =
      ∑ c ∈ Fintype.piFinset P, ∏ i, (Y i (c i) ω - ∫ ω', Y i (c i) ω' ∂μ) := fun ω => by
    rw [← Finset.prod_univ_sum P fun i α => Y i α ω - ∫ ω', Y i α ω' ∂μ]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hmean i, hO i ω, Finset.sum_sub_distrib]
  have hint : ∀ c ∈ Fintype.piFinset P,
      Integrable (fun ω => ∏ i, (Y i (c i) ω - ∫ ω', Y i (c i) ω' ∂μ)) μ := fun c hc =>
    (AEBounded.prod Finset.univ fun i _ =>
      (hY i _ (Fintype.mem_piFinset.1 hc i)).sub_const _).integrable
  simp_rw [hcent]
  rw [integral_finsetSum _ hint, Finset.prod_univ_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun c hc => hB c (Fintype.mem_piFinset.1 hc))
private theorem abs_integral_centred_prod_le_of_pieces {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (P : Fin n → Finset ι) (Y : Fin n → ι → Ω → ℝ)
    (O : Fin n → Ω → ℝ) (W : Fin n → ι → ℝ) (T : Fin n → ℝ)
    (hY : ∀ i, ∀ α ∈ P i, AEBounded μ (Y i α)) (hO : ∀ i ω, O i ω = ∑ α ∈ P i, Y i α ω)
    (hW : ∀ i, ∀ α ∈ P i, 0 ≤ W i α) (hT : ∀ i, ∑ α ∈ P i, W i α ≤ T i)
    (hB : ∀ (k : ℕ) (e : Fin k → Fin n), Function.Injective e → ∀ c : Fin k → ι,
      (∀ j, c j ∈ P (e j)) →
        |∫ ω, ∏ j, (Y (e j) (c j) ω - ∫ ω', Y (e j) (c j) ω' ∂μ) ∂μ| ≤ ∏ j, W (e j) (c j))
    (J : Finset (Fin n)) :
    |∫ ω, ∏ i ∈ J, (O i ω - ∫ ω', O i ω' ∂μ) ∂μ| ≤ ∏ i ∈ J, T i := by
  classical
  let e : Fin J.card ≃ J := J.equivFin.symm
  let e' : Fin J.card → Fin n := fun j => (e j : Fin n)
  have he' : Function.Injective e' := fun a b h => e.injective (Subtype.ext h)
  have hprod : ∀ g : Fin n → ℝ, ∏ i ∈ J, g i = ∏ j, g (e' j) := fun g => by
    rw [← Finset.prod_coe_sort J g]
    exact (Equiv.prod_comp e fun i : J => g i).symm
  have h1 : ∫ ω, ∏ i ∈ J, (O i ω - ∫ ω', O i ω' ∂μ) ∂μ =
      ∫ ω, ∏ j, (O (e' j) ω - ∫ ω', O (e' j) ω' ∂μ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      hprod fun i => O i ω - ∫ ω', O i ω' ∂μ)
  rw [h1, hprod T]
  refine (abs_integral_centred_prod_sum_le (fun j => P (e' j)) (fun j => Y (e' j)) (fun j => O (e' j))
    (fun j => W (e' j)) (fun j => hY _) (fun j => hO _)
    (fun c hc => hB _ e' he' c hc)).trans ?_
  exact Finset.prod_le_prod (fun j _ => Finset.sum_nonneg (hW _)) fun j _ => hT _
private theorem mul_rpow_one_twentieth_le (b v : ℝ) (hb : 0 ≤ b) (hv : 0 ≤ v) :
    b * v ^ ((1 : ℝ) / 20) ≤ v + b ^ ((20 : ℝ) / 19) := by
  rcases le_or_gt v (b ^ ((20 : ℝ) / 19)) with h | h
  · have h1 : v ^ ((1 : ℝ) / 20) ≤ b ^ ((1 : ℝ) / 19) := by
      calc v ^ ((1 : ℝ) / 20) ≤ (b ^ ((20 : ℝ) / 19)) ^ ((1 : ℝ) / 20) :=
            Real.rpow_le_rpow hv h (by norm_num)
        _ = b ^ ((1 : ℝ) / 19) := by
            rw [← Real.rpow_mul hb]
            norm_num
    have h2 : b * b ^ ((1 : ℝ) / 19) = b ^ ((20 : ℝ) / 19) := by
      rcases hb.eq_or_lt with rfl | hb'
      · rw [zero_mul, Real.zero_rpow (by norm_num)]
      · rw [show (20 : ℝ) / 19 = 1 + 1 / 19 by norm_num, Real.rpow_add hb', Real.rpow_one]
    have h3 := mul_le_mul_of_nonneg_left h1 hb
    linarith
  · have hw : 0 ≤ b ^ ((20 : ℝ) / 19) := Real.rpow_nonneg hb _
    have hvpos : 0 < v := lt_of_le_of_lt hw h
    have h1 : b ≤ v ^ ((19 : ℝ) / 20) := by
      calc b = (b ^ ((20 : ℝ) / 19)) ^ ((19 : ℝ) / 20) := by
            rw [← Real.rpow_mul hb]
            norm_num
        _ ≤ v ^ ((19 : ℝ) / 20) := Real.rpow_le_rpow hw h.le (by norm_num)
    have h2 : v ^ ((19 : ℝ) / 20) * v ^ ((1 : ℝ) / 20) = v := by
      rw [← Real.rpow_add hvpos]
      norm_num
    have h3 : 0 ≤ v ^ ((1 : ℝ) / 20) := Real.rpow_nonneg hv _
    have h4 := mul_le_mul_of_nonneg_right h1 h3
    linarith
private theorem copySize_le {A b l ε X : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) (hl : 0 < l) (hl1 : l ≤ 1)
    (hε : 0 < ε) (hρ : 1 ≤ 1 / (2 * ε)) (hX : 1 / (2 * ε) ≤ X) :
    copySize A b l (2 * ε) ≤ A * Real.exp (b + b ^ ((20 : ℝ) / 19)) * X := by
  unfold copySize
  have ht : 0 < 1 / (2 * ε) := by positivity
  have hv0 : 0 ≤ Real.log (1 / (2 * ε)) := Real.log_nonneg hρ
  have hv : TorusBound.logPos (1 / (2 * ε)) = Real.log (1 / (2 * ε)) :=
    max_eq_left hv0
  rw [hv]
  have h1 : b * l ^ 4 ≤ b := by
    have h : l ^ 4 ≤ 1 := pow_le_one₀ hl.le hl1
    nlinarith
  have h2 := mul_rpow_one_twentieth_le b _ hb hv0
  have h3 : Real.exp (b * l ^ 4 + b * Real.log (1 / (2 * ε)) ^ ((1 : ℝ) / 20)) ≤
      Real.exp (b + b ^ ((20 : ℝ) / 19)) * X := by
    calc Real.exp (b * l ^ 4 + b * Real.log (1 / (2 * ε)) ^ ((1 : ℝ) / 20))
        ≤ Real.exp ((b + b ^ ((20 : ℝ) / 19)) + Real.log (1 / (2 * ε))) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (b + b ^ ((20 : ℝ) / 19)) * (1 / (2 * ε)) := by
          rw [Real.exp_add, Real.exp_log ht]
      _ ≤ Real.exp (b + b ^ ((20 : ℝ) / 19)) * X :=
          mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le
  calc A * Real.exp (b * l ^ 4 + b * Real.log (1 / (2 * ε)) ^ ((1 : ℝ) / 20))
      ≤ A * (Real.exp (b + b ^ ((20 : ℝ) / 19)) * X) := mul_le_mul_of_nonneg_left h3 hA
    _ = A * Real.exp (b + b ^ ((20 : ℝ) / 19)) * X := by ring
private theorem card_mul_weight_le_fineConstant {L : ℕ} (hL : 1 ≤ L) {A b R d l ε : ℝ} {n : ℕ} (hA : 0 ≤ A)
    (hb : 0 ≤ b) (hR : 0 < R) (hd : 0 < d) (hd1 : d ≤ 1) (hn : 2 ≤ n) (hl : 0 < l)
    (hld : l ≤ d / 8) (hLl : d / 8 < L * l) (hε : ε = l / (2 ^ 7 * (n : ℝ))) :
    (2 * R / ε + 3) ^ 4 * (2 * copySize A b l (2 * ε) * 5) ≤ fineConstant L A b R n d := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hx : 2 ≤ (n : ℝ) / d := by
    rw [le_div_iff₀ hd]
    nlinarith
  have hu : 1 / l ≤ 8 * L / d := by
    rw [div_le_div_iff₀ hl hd]
    linarith
  have he : 1 / ε = 2 ^ 7 * (n : ℝ) * (1 / l) := by
    rw [hε]
    field_simp
  have he1 : 1 / ε ≤ 2 ^ 10 * L * ((n : ℝ) / d) := by
    rw [he]
    calc 2 ^ 7 * (n : ℝ) * (1 / l) ≤ 2 ^ 7 * (n : ℝ) * (8 * L / d) :=
          mul_le_mul_of_nonneg_left hu (by positivity)
      _ = 2 ^ 10 * L * ((n : ℝ) / d) := by ring
  have hLx : 2 ≤ (L : ℝ) * ((n : ℝ) / d) := by nlinarith
  have hl1 : l ≤ 1 := by linarith
  have hε1 : ε ≤ l := by
    rw [hε]
    refine div_le_self hl.le ?_
    nlinarith
  have hρ : 1 ≤ 1 / (2 * ε) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hX : 1 / (2 * ε) ≤ 2 ^ 9 * L * ((n : ℝ) / d) := by
    have h : 1 / (2 * ε) = (1 / ε) / 2 := by field_simp
    rw [h]
    linarith
  have hs := copySize_le hA hb hl hl1 hεpos hρ hX
  have hc : 2 * R / ε + 3 ≤ 2 ^ 11 * L * ((n : ℝ) / d) * (1 + R) := by
    have h1 : 2 * R / ε = 2 * R * (1 / ε) := by ring
    have h2 : 2 * R * (1 / ε) ≤ 2 * R * (2 ^ 10 * L * ((n : ℝ) / d)) :=
      mul_le_mul_of_nonneg_left he1 (by positivity)
    rw [h1]
    nlinarith
  have hc0 : 0 ≤ 2 * R / ε + 3 := by positivity
  have hc4 := pow_le_pow_left₀ hc0 hc 4
  have hs0 : 0 ≤ copySize A b l (2 * ε) := by
    unfold copySize
    positivity
  calc (2 * R / ε + 3) ^ 4 * (2 * copySize A b l (2 * ε) * 5)
      ≤ (2 ^ 11 * L * ((n : ℝ) / d) * (1 + R)) ^ 4 *
          (2 * (A * Real.exp (b + b ^ ((20 : ℝ) / 19)) * (2 ^ 9 * L * ((n : ℝ) / d))) * 5) := by
        refine mul_le_mul hc4 (by linarith) (by positivity) (by positivity)
    _ = fineConstant L A b R n d := by
        unfold fineConstant
        ring
private theorem sum_weights_le {ι : Type*} (P : Finset ι) (w : ι → ℝ) {c Sz Sh F : ℝ}
    (hcard : (P.card : ℝ) ≤ c) (hw : ∀ α ∈ P, w α ≤ 2 * (Sz * (5 * Sh))) (hSz : 0 ≤ Sz)
    (hSh : 0 ≤ Sh) (hF : c * (2 * Sz * 5) ≤ F) : ∑ α ∈ P, w α ≤ F * Sh := by
  calc ∑ α ∈ P, w α ≤ ∑ _α ∈ P, 2 * (Sz * (5 * Sh)) := Finset.sum_le_sum hw
    _ = (P.card : ℝ) * (2 * Sz * 5) * Sh := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ c * (2 * Sz * 5) * Sh := by
        refine mul_le_mul_of_nonneg_right ?_ hSh
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ F * Sh := mul_le_mul_of_nonneg_right hF hSh
private theorem pos_of_isMaximalScalePower {L : ℕ} (hL : 1 ≤ L) {d l : ℝ}
    (hl : IsMaximalScalePower L d l) : 0 < l := by
  obtain ⟨⟨j, rfl⟩, -⟩ := hl
  have : (0 : ℝ) < L := by exact_mod_cast hL
  exact zpow_pos this j
private theorem abs_apply_le_euclidNormVec (x : Fin 4 → ℝ) (μ : Fin 4) : |x μ| ≤ euclidNormVec x := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem isBounded_closedBallR4 (y : AmbientSpace) (r : ℝ) :
    Bornology.IsBounded (closedBallR4 y r) := by
  refine (Metric.isBounded_closedBall (x := y) (r := max r 0)).subset fun x hx => ?_
  have hx' : euclidNormVec (x - y) ≤ r := hx
  rw [Metric.mem_closedBall, dist_pi_le_iff (le_max_right _ _)]
  intro μ
  rw [Real.dist_eq]
  exact ((abs_apply_le_euclidNormVec (x - y) μ).trans hx').trans (le_max_left _ _)
private theorem isBoundedFun_of_tsupport_subset {f : AmbientSpace → ℝ} (hf : IsLipschitzFor euclidDistR4 f)
    {y : AmbientSpace} {R : ℝ} (hR : 0 < R) (hy : tsupport f ⊆ closedBallR4 y R) : IsBoundedFun f := by
  obtain ⟨C, hC, h⟩ := hf
  refine ⟨|f y| + C * R, fun x => ?_⟩
  have hpos : 0 ≤ |f y| + C * R := by positivity
  by_cases hx : f x = 0
  · simpa [hx] using hpos
  · have hx' : euclidNormVec (x - y) ≤ R := hy (subset_tsupport f hx)
    have h1 : ‖f x - f y‖ ≤ C * euclidNormVec (x - y) := h x y
    have h2 : C * euclidNormVec (x - y) ≤ C * R := mul_le_mul_of_nonneg_left hx' hC
    rw [Real.norm_eq_abs] at h1 ⊢
    have h3 := abs_sub_abs_le_abs_sub (f x) (f y)
    linarith
private theorem uniformNorm_nonneg {X : Type*} (f : X → ℝ) : 0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
private theorem copySize_nonneg {A b : ℝ} (hA : 0 ≤ A) (l ϱ : ℝ) : 0 ≤ copySize A b l ϱ := by
  unfold copySize
  positivity
private theorem copyBound_nonneg {A b : ℝ} (hA : 0 ≤ A) (l ϱ : ℝ) (h : AmbientSpace → ℝ) :
    0 ≤ copyBound A b l ϱ h :=
  mul_nonneg (copySize_nonneg hA l ϱ) ((uniformNorm_nonneg h).trans (le_max_left _ _))
private theorem hatPiece_bound (hT : hatPartitionOfUnity_prop) {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 < ε)
    (h2 : 2 * ε ≤ 1) {g : AmbientSpace → ℝ} (hgb : IsBoundedFun g) (hgl : IsLipschitzFor euclidDistR4 g)
    (α : AmbientSpace) {A b : ℝ} (hA : 0 ≤ A) (l : ℝ) :
    IsLipschitzFor euclidDistR4 (fun x => hatFunction ε α x * g x) ∧
      copyBound A b l (2 * ε) (fun x => hatFunction ε α x * g x) ≤
        copySize A b l (2 * ε) * (5 * sharpNormR4 M g) := by
  obtain ⟨h1, h3⟩ := (hT.1 ε hε).2.2.2.2.2.1 M hM h2 g hgb hgl α
  refine ⟨h1, mul_le_mul_of_nonneg_left ?_ (copySize_nonneg hA _ _)⟩
  unfold radiusNorm
  rw [min_eq_right h2]
  exact h3
private theorem eq_sum_hat_mul {X : Type*} (s : Set (Fin 4 → ℝ)) (t : (Fin 4 → ℝ) → X → ℝ)
    (P : Finset (Fin 4 → ℝ)) (hP : ∀ α ∈ P, α ∈ s) (x : X) (hs : ∑ᶠ α : s, t α x = 1)
    (f : X → ℝ) (hin : ∀ α ∈ s, t α x * f x ≠ 0 → α ∈ P) :
    f x = ∑ α ∈ P, t α x * f x := by
  rw [← Finset.sum_mul]
  by_cases h0 : f x = 0
  · simp [h0]
  have h1 : ∑ α ∈ P, t α x = 1 := by
    rw [← hs, finsum_set_coe_eq_finsum_mem (f := fun α => t α x) s]
    refine (finsum_mem_eq_sum_of_inter_support_eq _ ?_).symm
    ext α
    simp only [Set.mem_inter_iff, Function.mem_support, Finset.mem_coe]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨hin α h (mul_ne_zero h' h0), h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨hP α h, h'⟩
  rw [h1, one_mul]
private theorem finite_support_plaquettes
    (hS : InfiniteLattice.OneSpacing.AllFacts) (s : Conventions.StandingParameters)
    {g : AmbientSpace → ℝ} {y : AmbientSpace} {r : ℝ} (hg : ∀ x, g x ≠ 0 → x ∈ closedBallR4 y r) :
    {p : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)) |
      g p.center ≠ 0}.Finite :=
  (((hS s).2.2.2.2.1).1 _ (isBounded_closedBallR4 y r)).subset fun _ hp => hg _ hp
private theorem smearedEnergy_finset_sum {a : ℝ} {ι : Type*} (S : Finset ι) (g : ι → AmbientSpace → ℝ)
    (hg : ∀ α ∈ S, {p : InfiniteLattice.ElementaryPlaquette a | g α p.center ≠ 0}.Finite)
    (U : InfiniteLattice.GaugeField a) :
    smearedEnergy (fun x => ∑ α ∈ S, g α x) U = ∑ α ∈ S, smearedEnergy (g α) U := by
  unfold InfiniteLattice.smearedEnergy
  simp only [Finset.smul_sum]
  refine finsum_sum_comm S _ fun α hα => (hg α hα).subset fun p hp => ?_
  change g α p.center ≠ 0
  intro h0
  exact hp (by simp [h0])
private theorem continuous_smearedEnergy {a : ℝ} {g : AmbientSpace → ℝ}
    (hg : {p : InfiniteLattice.ElementaryPlaquette a | g p.center ≠ 0}.Finite) :
    Continuous (smearedEnergy g : InfiniteLattice.GaugeField a → ℝ) := by
  have h : (smearedEnergy g : InfiniteLattice.GaugeField a → ℝ) =
      fun U : InfiniteLattice.GaugeField a =>
        ∑ p ∈ hg.toFinset, InfiniteLattice.faceEnergy U p • g p.center := by
    funext U
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    rw [Set.Finite.coe_toFinset]
    change g p.center ≠ 0
    intro h0
    exact hp (by simp [h0])
  rw [h]
  exact continuous_finsetSum _ fun p _ =>
    (InfiniteLattice.continuous_faceEnergy p).smul continuous_const
private theorem aeBounded_smearedEnergy {a : ℝ} (ν : Measure (InfiniteLattice.GaugeField a))
    {g : AmbientSpace → ℝ}
    (hg : {p : InfiniteLattice.ElementaryPlaquette a | g p.center ≠ 0}.Finite) {C : ℝ}
    (hC : ∀ U : InfiniteLattice.GaugeField a, |smearedEnergy g U| ≤ C) :
    AEBounded ν (fun U => smearedEnergy g U) :=
  ⟨(continuous_smearedEnergy hg).measurable.aestronglyMeasurable, C, Filter.Eventually.of_forall hC⟩
private theorem le_euclidDistR4_of_separated {A B : Set (Fin 4 → ℝ)} {d : ℝ}
    (h : ENNReal.ofReal d ≤ setDistR4 A B) {x z : Fin 4 → ℝ} (hx : x ∈ A) (hz : z ∈ B) :
    d ≤ euclidDistR4 x z := by
  have h1 : ENNReal.ofReal d ≤ ENNReal.ofReal (euclidNormVec (x - z)) :=
    h.trans ((iInf₂_le x hx).trans (iInf₂_le z hz))
  exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).1 h1
private theorem centred_moment_gibbs (hT : hatPartitionOfUnity_prop) (hP : CenteredProductBound)
    (hZ : SmearedObservableBound)
    (hS : InfiniteLattice.OneSpacing.AllFacts)
    (D : ChessboardSetup) (A b M R d l : ℝ) (n : ℕ) (hA : 1 ≤ A) (hb : 1 ≤ b) (hM : 1 ≤ M) (hR : 0 < R)
    (hd : 0 < d) (hd1 : d ≤ 1) (hn : 2 ≤ n) (hI : CopyInequality D A b)
    (hl : IsMaximalScalePower D.L d l) (hq : max (2 ^ 6 * (n : ℝ)) ((D.L : ℝ) ^ 2) ≤ l / D.mesh)
    (ν : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))))
    (hν : ν ∈ periodicGibbsSet D.L D.K D.β) (f : Fin n → AmbientSpace → ℝ)
    (hf : ∀ i, IsLipschitzFor euclidDistR4 (f i)) (hball : ∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R)
    (hsep : HasSeparatedSupportsR4 f d) (J : Finset (Fin n)) :
    |∫ U, ∏ i ∈ J, (smearedEnergy (f i) U - ∫ V, smearedEnergy (f i) V ∂ν) ∂ν| ≤
      ∏ i ∈ J, fineConstant D.L A b R n d * sharpNormR4 M (f i) := by
  classical
  have hν' : InfiniteLattice.IsPeriodicGibbs D.β ν := hν
  have hprob : IsProbabilityMeasure ν := hν'.1.1
  have hL1 : 1 ≤ D.L := by linarith [D.isAdmissible.2]
  have hlpos : 0 < l := pos_of_isMaximalScalePower hL1 hl
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl8 : l ≤ d / 8 := hl.2.1
  set ε : ℝ := l / (2 ^ 7 * (n : ℝ)) with hεdef
  have hε : 0 < ε := by positivity
  have hεl : ε ≤ l := by
    refine div_le_self hlpos.le ?_
    nlinarith
  have h2ε : 2 * ε ≤ 1 := by linarith
  have hapos : 0 < PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ) := by
    unfold PeriodicLattice.meshSize
    have : (0 : ℝ) < D.L := by exact_mod_cast hL1
    exact zpow_pos this _
  choose y hy using hball
  have hfb : ∀ i, IsBoundedFun (f i) := fun i => isBoundedFun_of_tsupport_subset (hf i) hR (hy i)
  have hcnt := (hT.1 ε hε).2.2.2.2.2.2 R hR
  have hfin : ∀ i, {α | α ∈ scaledIntLattice ε ∧ ∃ x, hatFunction ε α x * f i x ≠ 0}.Finite := fun i =>
    (hcnt (f i) ⟨y i, hy i⟩).1
  let P : Fin n → Finset AmbientSpace := fun i => (hfin i).toFinset
  have hPmem : ∀ i α, α ∈ P i ↔ α ∈ scaledIntLattice ε ∧ ∃ x, hatFunction ε α x * f i x ≠ 0 :=
    fun i α => (hfin i).mem_toFinset
  let p : Fin n → AmbientSpace → AmbientSpace → ℝ := fun i α x => hatFunction ε α x * f i x
  have hpb : ∀ i α, IsLipschitzFor euclidDistR4 (p i α) ∧
      copyBound A b l (2 * ε) (p i α) ≤
        copySize A b l (2 * ε) * (5 * sharpNormR4 M (f i)) := fun i α =>
    hatPiece_bound hT hM hε h2ε (hfb i) (hf i) α (by linarith) l
  have hpsupp : ∀ i α x, p i α x ≠ 0 → f i x ≠ 0 := fun i α x h =>
    right_ne_zero_of_mul h
  have hpball : ∀ i α, tsupport (p i α) ⊆ closedBallR4 (y i) R := fun i α =>
    (tsupport_mul_subset_right (f := hatFunction ε α) (g := f i)).trans (hy i)
  have hpfin : ∀ i α, {q : InfiniteLattice.ElementaryPlaquette
      (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)) | p i α q.center ≠ 0}.Finite := fun i α =>
    finite_support_plaquettes hS D.toStandingParameters fun x hx => hpball i α (subset_tsupport _ hx)
  have hO : ∀ i (U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ))),
      smearedEnergy (f i) U = ∑ α ∈ P i, smearedEnergy (p i α) U := by
    intro i U
    have hfe : f i = fun x => ∑ α ∈ P i, p i α x := by
      funext x
      refine eq_sum_hat_mul (scaledIntLattice ε) (hatFunction ε) (P i)
        (fun α hα => ((hPmem i α).1 hα).1) x
        ((hT.1 ε hε).2.1 x).2 (f i) fun α hα h => (hPmem i α).2 ⟨hα, x, h⟩
    rw [← smearedEnergy_finset_sum (P i) (p i) fun α _ => hpfin i α]
    exact congrArg (fun h => smearedEnergy h U) hfe
  refine abs_integral_centred_prod_le_of_pieces (μ := ν) P (fun i α U => smearedEnergy (p i α) U)
    (fun i U => smearedEnergy (f i) U) (fun i α => 2 * copyBound A b l (2 * ε) (p i α))
    (fun i => fineConstant D.L A b R n d * sharpNormR4 M (f i)) ?_ hO ?_ ?_ ?_ J
  · intro i α _
    exact aeBounded_smearedEnergy ν (hpfin i α) (hZ.1 _ R hapos hR (p i α)
      (isBoundedFun_of_tsupport_subset (hpb i α).1 hR (hpball i α)) ⟨y i, hpball i α⟩)
  · intro i α _
    exact mul_nonneg zero_le_two (copyBound_nonneg (by linarith) _ _ _)
  · intro i
    refine sum_weights_le (P i) _ (c := (2 * R / ε + 3) ^ 4) ?_ (fun α _ => ?_)
      (copySize_nonneg (by linarith) _ _) ?_
      (card_mul_weight_le_fineConstant hL1 (by linarith) (by linarith) hR hd hd1 hn hlpos
        hl.2.1 hl.2.2 rfl)
    · rw [show (P i).card = {α | α ∈ scaledIntLattice ε ∧ ∃ x, hatFunction ε α x * f i x ≠ 0}.ncard from
        (Set.ncard_eq_toFinset_card _ (hfin i)).symm]
      exact (hcnt (f i) ⟨y i, hy i⟩).2
    · have := (hpb i α).2
      linarith
    · exact (uniformNorm_nonneg _).trans (le_max_left _ _)
  · intro k e he c hc
    have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective e he
    refine (hP D A b l ε n k (by linarith) (by linarith) hkn (by omega) hI hl.1 hq rfl
      (fun j => p (e j) (c j)) c (fun j => (hpb _ _).1) ?_ ?_).1 ν hν
    · intro j x hx μ
      exact ((hT.1 ε hε).2.2.1 (c j) x (left_ne_zero_of_mul hx) μ).le
    · intro j j' hjj x z hx hz
      have h8 : 8 * l ≤ d := by linarith
      exact h8.trans (le_euclidDistR4_of_separated (hsep.2 (e j) (e j') (fun h => hjj (he h)))
        (subset_tsupport _ (hpsupp _ _ _ hx)) (subset_tsupport _ (hpsupp _ _ _ hz)))
private theorem torusProj_sub (ℓ : ℝ) (x z : Fin 4 → ℝ) :
    torusProj ℓ x - torusProj ℓ z = torusProj ℓ (x - z) := by
  funext μ
  simp [torusProj]
abbrev _root_.YangMills.DeltaSharedProofs.p500829 := @torusProj_sub
abbrev _root_.YangMills.SharedProofs.p13492 := @torusProj_sub
private theorem torusEuclidNorm_proj_le (ℓ : ℝ) (v : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj ℓ v) ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
private theorem euclidDistTorus_proj_le (ℓ : ℝ) (x z : Fin 4 → ℝ) :
    euclidDistTorus (torusProj ℓ x) (torusProj ℓ z) ≤ euclidDistR4 x z := by
  unfold euclidDistTorus euclidDistR4
  rw [torusProj_sub]
  exact torusEuclidNorm_proj_le ℓ _
abbrev _root_.YangMills.DeltaSharedProofs.p50059 := @euclidDistTorus_proj_le
private theorem isLipschitzFor_lift {ℓ : ℝ} {F : Torus4 ℓ → ℝ}
    (hF : IsLipschitzFor euclidDistTorus F) :
    IsLipschitzFor euclidDistR4 fun x => F (torusProj ℓ x) := by
  obtain ⟨C, hC, h⟩ := hF
  exact ⟨C, hC, fun x z =>
    (h _ _).trans (mul_le_mul_of_nonneg_left (euclidDistTorus_proj_le ℓ x z) hC)⟩
private theorem isBoundedFun_of_torus_lipschitz {ℓ : ℝ} (hℓ : 0 < ℓ) {F : Torus4 ℓ → ℝ}
    (hF : IsLipschitzFor euclidDistTorus F) : IsBoundedFun F := by
  obtain ⟨C, hC, h⟩ := hF
  refine ⟨|F 0| + C * (2 * ℓ), fun y => ?_⟩
  choose v hv hv' using fun μ => exists_coe_eq_abs_eq_norm (y μ)
  have hy : y = torusProj ℓ v := funext fun μ => (hv μ).symm
  have hb : ∀ μ, |v μ| ≤ ℓ / 2 := fun μ => by
    rw [hv' μ]
    have h1 := AddCircle.norm_le_half_period (p := ℓ) (x := y μ) hℓ.ne'
    rwa [abs_of_pos hℓ] at h1
  have hsq : ∀ μ, v μ ^ 2 ≤ ℓ ^ 2 := fun μ => by
    rw [← sq_abs]
    nlinarith [hb μ, abs_nonneg (v μ)]
  have h1 : euclidNormVec v ≤ 2 * ℓ := by
    unfold euclidNormVec
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [Fin.sum_univ_four]
    nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]
  have h2 : euclidDistTorus y 0 ≤ 2 * ℓ := by
    unfold euclidDistTorus
    rw [sub_zero, hy]
    exact (torusEuclidNorm_proj_le ℓ v).trans h1
  have h3 : ‖F y - F 0‖ ≤ C * (2 * ℓ) :=
    (h y 0).trans (mul_le_mul_of_nonneg_left h2 hC)
  rw [Real.norm_eq_abs] at h3 ⊢
  have h4 := abs_sub_abs_le_abs_sub (F y) (F 0)
  linarith
abbrev _root_.YangMills.SharedProofs.p4953 := @isBoundedFun_of_torus_lipschitz
private theorem uniformNorm_lift_le {ℓ : ℝ} {F : Torus4 ℓ → ℝ} (hb : IsBoundedFun F) :
    uniformNorm (fun x => F (torusProj ℓ x)) ≤ uniformNorm F := by
  obtain ⟨C, hC⟩ := hb
  have hbd : BddAbove (Set.range fun y => ‖F y‖) := ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩
  unfold uniformNorm
  exact ciSup_le fun x => le_ciSup hbd (torusProj ℓ x)
private theorem lipConstR4_lift_le {ℓ : ℝ} {F : Torus4 ℓ → ℝ}
    (hF : IsLipschitzFor euclidDistTorus F) :
    lipConstR4 (fun x => F (torusProj ℓ x)) ≤ lipConstTorus F := by
  unfold lipConstR4 lipConstTorus bestLipschitzConstant
  refine le_csInf ?_ ?_
  · obtain ⟨C, hC, h⟩ := hF
    exact ⟨C, hC, h⟩
  · rintro C ⟨hC, h⟩
    exact csInf_le ⟨0, fun _ h => h.1⟩ ⟨hC, fun x z =>
      (h _ _).trans (mul_le_mul_of_nonneg_left (euclidDistTorus_proj_le ℓ x z) hC)⟩
private theorem sharpNormR4_lift_le {ℓ M : ℝ} (hM : 0 ≤ M) {F : Torus4 ℓ → ℝ} (hb : IsBoundedFun F)
    (hF : IsLipschitzFor euclidDistTorus F) :
    sharpNormR4 M (fun x => F (torusProj ℓ x)) ≤ sharpNormTorus M F :=
  max_le_max (uniformNorm_lift_le hb) (mul_le_mul_of_nonneg_left (lipConstR4_lift_le hF) (by positivity))
private theorem periodize_hat_mul_lift {ℓ ε : ℝ} (hε : 0 < ε) (hℓ : 3 * ε ≤ ℓ) (α : Fin 4 → ℝ)
    (F : Torus4 ℓ → ℝ) (y : Torus4 ℓ) :
    periodize ℓ (fun x => hatFunction ε α x * F (torusProj ℓ x)) y = torusHatFunction ε α y * F y := by
  have hℓ0 : 0 < ℓ := by linarith
  choose v hv hv' using fun μ => exists_coe_eq_abs_eq_norm (y μ - ((α μ : ℝ) : AddCircle ℓ))
  have hy : y = torusProj ℓ (v + α) := by
    funext μ
    have h1 := hv μ
    simp only [torusProj, Pi.add_apply, AddCircle.coe_add]
    rw [h1]
    abel
  have hhalf : ∀ μ, |v μ| ≤ ℓ / 2 := fun μ => by
    rw [hv' μ]
    have h1 := AddCircle.norm_le_half_period (p := ℓ)
      (x := y μ - ((α μ : ℝ) : AddCircle ℓ)) hℓ0.ne'
    rwa [abs_of_pos hℓ0] at h1
  have ht : torusHatFunction ε α y = hatFunction ε α (v + α) := by
    unfold torusHatFunction hatFunction
    refine Finset.prod_congr rfl fun μ _ => ?_
    rw [← hv' μ, Pi.add_apply, add_sub_cancel_right]
  have hk : ∀ k : Fin 4 → ℤ, k ≠ 0 → hatFunction ε α (v + α + latticeTranslate ℓ k) = 0 := by
    intro k hk
    obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hk
    unfold hatFunction
    refine Finset.prod_eq_zero (Finset.mem_univ μ) ?_
    have hk1 : (1 : ℝ) ≤ |(k μ : ℝ)| := by exact_mod_cast Int.one_le_abs hμ
    have e : (v + α + latticeTranslate ℓ k) μ - α μ = ℓ * (k μ : ℝ) + v μ := by
      simp only [Pi.add_apply, latticeTranslate]
      ring
    have h1 : ℓ ≤ |ℓ * (k μ : ℝ)| := by
      rw [abs_mul, abs_of_pos hℓ0]
      nlinarith
    have h2 := abs_sub_abs_le_abs_sub (ℓ * (k μ : ℝ)) (-v μ)
    rw [abs_neg, sub_neg_eq_add] at h2
    have h3 : ε ≤ |(v + α + latticeTranslate ℓ k) μ - α μ| := by
      rw [e]
      linarith [hhalf μ]
    have h4 : 1 ≤ |(v + α + latticeTranslate ℓ k) μ - α μ| / ε := (one_le_div hε).2 h3
    exact max_eq_left (by linarith)
  have hz : latticeTranslate ℓ 0 = 0 := by
    funext μ
    simp [latticeTranslate]
  have main : periodize ℓ (fun x => hatFunction ε α x * F (torusProj ℓ x)) (torusProj ℓ (v + α)) =
      hatFunction ε α (v + α) * F (torusProj ℓ (v + α)) := by
    rw [periodize_torusProj]
    unfold periodicSum
    refine (tsum_eq_single 0 fun k hk' => ?_).trans ?_
    · change hatFunction ε α (v + α + latticeTranslate ℓ k) * _ = 0
      rw [hk k hk', zero_mul]
    · change hatFunction ε α (v + α + latticeTranslate ℓ 0) *
        F (torusProj ℓ (v + α + latticeTranslate ℓ 0)) = _
      rw [hz, add_zero]
  calc periodize ℓ (fun x => hatFunction ε α x * F (torusProj ℓ x)) y
      = periodize ℓ (fun x => hatFunction ε α x * F (torusProj ℓ x)) (torusProj ℓ (v + α)) := by
        rw [← hy]
    _ = hatFunction ε α (v + α) * F (torusProj ℓ (v + α)) := main
    _ = torusHatFunction ε α y * F y := by rw [← hy, ht]
private theorem finite_scaledIntLatticeFundDomain {ℓ ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : ℓ = q * ε) :
    (scaledIntLatticeFundDomain ℓ ε).Finite := by
  have h : (Set.pi Set.univ fun _ : Fin 4 => (fun k : ℕ => ε * (k : ℝ)) '' Set.Iio q).Finite :=
    Set.Finite.pi fun _ => (Set.finite_Iio q).image _
  refine h.subset fun α hα μ _ => ?_
  obtain ⟨hα1, hα2⟩ := hα
  obtain ⟨k, hk⟩ := hα1 μ
  obtain ⟨h0, h1⟩ := hα2 μ
  have hk0 : (0 : ℝ) ≤ k := by
    rw [hk] at h0
    exact (mul_nonneg_iff_of_pos_left hε).1 h0
  have hk1 : (k : ℝ) < q := by
    rw [hk, hq, mul_comm (q : ℝ)] at h1
    exact lt_of_mul_lt_mul_left h1 hε.le
  have hk0' : 0 ≤ k := by exact_mod_cast hk0
  lift k to ℕ using hk0'
  exact ⟨k, by simpa using (by exact_mod_cast hk1 : k < q), by simpa using hk.symm⟩
private theorem le_euclidDistTorus_of_separated {ℓ d : ℝ} {A B : Set (Torus4 ℓ)}
    (h : ENNReal.ofReal d ≤ setEuclidDist A B) {x z : Torus4 ℓ} (hx : x ∈ A) (hz : z ∈ B) :
    d ≤ euclidDistTorus x z := by
  have h1 : ENNReal.ofReal d ≤ ENNReal.ofReal (torusEuclidNorm (x - z)) :=
    h.trans ((iInf₂_le x hx).trans (iInf₂_le z hz))
  refine (ENNReal.ofReal_le_ofReal_iff ?_).1 h1
  exact Real.sInf_nonneg (by rintro _ ⟨w, -, rfl⟩; exact Real.sqrt_nonneg _)
private theorem smearedObservable_finset_sum {L m : ℕ} {j : ℤ} [Finite (PeriodicLattice.Plaquette L m j)]
    {ι : Type*} (S : Finset ι) (g : ι → PeriodicLattice.FourTorus L m → ℝ)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    PeriodicLattice.smearedObservable (fun x => ∑ α ∈ S, g α x) U =
      ∑ α ∈ S, PeriodicLattice.smearedObservable (g α) U := by
  unfold PeriodicLattice.smearedObservable
  simp only [Finset.smul_sum]
  exact finsum_sum_comm S _ fun _ _ => Set.toFinite _
private theorem continuous_plaquetteCost {L m : ℕ} {j : ℤ} (p : PeriodicLattice.Plaquette L m j) :
    Continuous fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.plaquetteCost U p := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.continuous_plaquetteCost <;> assumption
private theorem measurable_smearedObservable {L m : ℕ} {j : ℤ} [Finite (PeriodicLattice.Plaquette L m j)]
    (f : PeriodicLattice.FourTorus L m → ℝ) :
    Measurable fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.smearedObservable f U := by
  cases nonempty_fintype (PeriodicLattice.Plaquette L m j)
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have e : (fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.smearedObservable f U) = fun U =>
      ∑ p, PeriodicLattice.plaquetteCost U p * f p.barycenter :=
    funext fun U => finsum_eq_sum_of_fintype _
  rw [e]
  exact Finset.measurable_sum _ fun p _ =>
    (continuous_plaquetteCost p).measurable.mul_const _
abbrev _root_.YangMills.DeltaSharedProofs.p502502 := @measurable_smearedObservable
private theorem centred_moment_torus (hT : hatPartitionOfUnity_prop) (hP : CenteredProductBound)
    (hZ : SmearedObservableBound)
    (hW : PeriodicLattice.WilsonCumulantWellPosedness.statement)
    (hF : PeriodicLattice.WilsonActionPlaquetteSumAndHaarSymmetry)
    (D : ChessboardSetup) (A b M R d l : ℝ) (n : ℕ) (hA : 1 ≤ A) (hb : 1 ≤ b) (hM : 1 ≤ M) (hR : 0 < R)
    (hd : 0 < d) (hd1 : d ≤ 1) (hn : 2 ≤ n) (hI : CopyInequality D A b)
    (hl : IsMaximalScalePower D.L d l) (hq : max (2 ^ 6 * (n : ℝ)) ((D.L : ℝ) ^ 2) ≤ l / D.mesh)
    (m : ℕ+) (f : Fin n → PeriodicLattice.FourTorus D.L m → ℝ)
    (hf : ∀ i, IsLipschitzFor euclidDistTorus (f i))
    (hball : ∀ i, ∃ x, tsupport (f i) ⊆ closedBallTorus x R)
    (hsep : HasSeparatedSupportsTorus f d) (J : Finset (Fin n)) :
    |∫ U, ∏ i ∈ J, (PeriodicLattice.smearedObservable (f i) U -
        ∫ V, PeriodicLattice.smearedObservable (f i) V ∂PeriodicLattice.wilsonGibbsMeasure D.L m D.K D.β)
      ∂PeriodicLattice.wilsonGibbsMeasure D.L m D.K D.β| ≤
      ∏ i ∈ J, fineConstant D.L A b R n d * sharpNormTorus M (f i) := by
  classical
  have hL13 : 13 ≤ D.L := D.isAdmissible.2
  have hL1 : 1 ≤ D.L := by omega
  have hL2 : 1 < D.L := by omega
  have hLr : (1 : ℝ) < D.L := by exact_mod_cast hL2
  have hprob : IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure D.L m D.K D.β) :=
    (hW.1 D.L m D.K D.β hL2 m.pos D.K.pos).2.2.2
  have hfinP : Finite (PeriodicLattice.Plaquette D.L m ((D.K : ℕ) : ℤ)) :=
    (hF D.L m _ hL2 m.pos (Int.natCast_nonneg _)).2.1
  have hlpos : 0 < l := pos_of_isMaximalScalePower hL1 hl
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl8 : l ≤ d / 8 := hl.2.1
  set ε : ℝ := l / (2 ^ 7 * (n : ℝ)) with hεdef
  have hε : 0 < ε := by positivity
  have hεl : ε ≤ l := by
    refine div_le_self hlpos.le ?_
    nlinarith
  have h2ε : 2 * ε ≤ 1 := by linarith
  have hLm : (1 : ℝ) ≤ (D.L : ℝ) ^ (m : ℕ) := one_le_pow₀ hLr.le
  obtain ⟨j, hj⟩ := hl.1
  have hj0 : j < 0 := by
    by_contra h
    have h1 : (1 : ℝ) ≤ (D.L : ℝ) ^ j := one_le_zpow₀ hLr.le (not_lt.1 h)
    linarith
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = -(t : ℤ) := ⟨(-j).toNat, by omega⟩
  have hlt : l * (D.L : ℝ) ^ t = 1 := by
    rw [hj, zpow_neg, zpow_natCast]
    exact inv_mul_cancel₀ (by positivity)
  let q : ℕ := 2 * D.L ^ (m : ℕ) * 2 ^ 7 * n * D.L ^ t
  have hq3 : 3 ≤ q := by
    have h1 : 1 ≤ D.L ^ (m : ℕ) * n * D.L ^ t :=
      Nat.succ_le_of_lt (by positivity)
    have h2 : q = 256 * (D.L ^ (m : ℕ) * n * D.L ^ t) := by
      simp only [q]
      ring
    omega
  have hside : PeriodicLattice.torusSide D.L m = q * ε := by
    have h1 : (q : ℝ) * ε = 2 * (D.L : ℝ) ^ (m : ℕ) * (l * (D.L : ℝ) ^ t) := by
      simp only [q, hεdef]
      push_cast
      field_simp
      norm_num
    rw [h1, hlt, mul_one]
    rfl
  have h3ε : 3 * ε ≤ PeriodicLattice.torusSide D.L m := by
    rw [hside]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq3) hε.le
  have hℓ : 0 < PeriodicLattice.torusSide D.L m := by linarith
  have hTt := hT.2 _ ε hε q hq3 hside
  choose y hy using hball
  have hfb : ∀ i, IsBoundedFun (f i) := fun i => isBoundedFun_of_torus_lipschitz hℓ (hf i)
  have hcnt := hTt.2.2.2.2.2 R hR
  have hfin : ∀ i, {α | α ∈ scaledIntLatticeFundDomain (PeriodicLattice.torusSide D.L m) ε ∧
      ∃ x, torusHatFunction ε α x * f i x ≠ 0}.Finite := fun i =>
    (finite_scaledIntLatticeFundDomain hε hside).subset fun _ h => h.1
  let P : Fin n → Finset AmbientSpace := fun i => (hfin i).toFinset
  have hPmem : ∀ i α, α ∈ P i ↔ α ∈ scaledIntLatticeFundDomain (PeriodicLattice.torusSide D.L m) ε ∧
      ∃ x, torusHatFunction ε α x * f i x ≠ 0 := fun i α => (hfin i).mem_toFinset
  let g : Fin n → AmbientSpace → ℝ := fun i x => f i (torusProj (PeriodicLattice.torusSide D.L m) x)
  have hgl : ∀ i, IsLipschitzFor euclidDistR4 (g i) := fun i => isLipschitzFor_lift (hf i)
  have hgb : ∀ i, IsBoundedFun (g i) := fun i => by
    obtain ⟨C, hC⟩ := hfb i
    exact ⟨C, fun x => hC _⟩
  let p : Fin n → AmbientSpace → AmbientSpace → ℝ := fun i α x => hatFunction ε α x * g i x
  have hpb : ∀ i α, IsLipschitzFor euclidDistR4 (p i α) ∧
      copyBound A b l (2 * ε) (p i α) ≤
        copySize A b l (2 * ε) * (5 * sharpNormR4 M (g i)) := fun i α =>
    hatPiece_bound hT hM hε h2ε (hgb i) (hgl i) α (by linarith) l
  have htr : ∀ i α, periodize (PeriodicLattice.torusSide D.L m) (p i α) =
      fun z => torusHatFunction ε α z * f i z := fun i α =>
    funext fun z => periodize_hat_mul_lift hε h3ε α (f i) z
  have hpsupp : ∀ i α x, p i α x ≠ 0 →
      torusProj (PeriodicLattice.torusSide D.L m) x ∈ tsupport (f i) := fun i α x h =>
    subset_tsupport _ (right_ne_zero_of_mul h)
  have hO : ∀ i (U : PeriodicLattice.Bond D.L m ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2),
      PeriodicLattice.smearedObservable (f i) U = ∑ α ∈ P i,
        PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide D.L m) (p i α)) U := by
    intro i U
    have hfe : f i = fun x => ∑ α ∈ P i, periodize (PeriodicLattice.torusSide D.L m) (p i α) x := by
      funext x
      simp only [htr]
      exact eq_sum_hat_mul (scaledIntLatticeFundDomain (PeriodicLattice.torusSide D.L m) ε)
        (fun α x => torusHatFunction ε α x) (P i) (fun α hα => ((hPmem i α).1 hα).1) x
        (hTt.2.1 x) (f i) fun α hα h => (hPmem i α).2 ⟨hα, x, h⟩
    rw [← smearedObservable_finset_sum (P i)
      (fun α => periodize (PeriodicLattice.torusSide D.L m) (p i α)) U]
    exact congrArg (fun h => PeriodicLattice.smearedObservable h U) hfe
  refine abs_integral_centred_prod_le_of_pieces
    (μ := PeriodicLattice.wilsonGibbsMeasure D.L m D.K D.β) P
    (fun i α U => PeriodicLattice.smearedObservable
      (periodize (PeriodicLattice.torusSide D.L m) (p i α)) U)
    (fun i U => PeriodicLattice.smearedObservable (f i) U)
    (fun i α => 2 * copyBound A b l (2 * ε) (p i α))
    (fun i => fineConstant D.L A b R n d * sharpNormTorus M (f i)) ?_ hO ?_ ?_ ?_ J
  · intro i α _
    have hbd : IsBoundedFun (periodize (PeriodicLattice.torusSide D.L m) (p i α)) := by
      rw [htr]
      obtain ⟨C, hC⟩ := hfb i
      refine ⟨C, fun z => ?_⟩
      have h1 := hTt.1 α z
      have h2 := hC z
      have h0 : 0 ≤ C := (norm_nonneg _).trans h2
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h1.1]
      nlinarith [norm_nonneg (f i z)]
    have hsub : ∃ x, tsupport (periodize (PeriodicLattice.torusSide D.L m) (p i α)) ⊆
        closedBallTorus x R := by
      refine ⟨y i, ?_⟩
      rw [htr]
      exact (tsupport_mul_subset_right (f := torusHatFunction ε α) (g := f i)).trans (hy i)
    exact ⟨(measurable_smearedObservable _).aestronglyMeasurable, _,
      hZ.2 D.L m D.K D.β R hL13 D.beta_pos hR _ hbd hsub⟩
  · intro i α _
    exact mul_nonneg zero_le_two (copyBound_nonneg (by linarith) _ _ _)
  · intro i
    refine sum_weights_le (P i) _ (c := (2 * R / ε + 3) ^ 4) ?_ (fun α _ => ?_)
      (copySize_nonneg (by linarith) _ _) ?_
      (card_mul_weight_le_fineConstant hL1 (by linarith) (by linarith) hR hd hd1 hn hlpos
        hl.2.1 hl.2.2 rfl)
    · rw [show (P i).card = {α | α ∈ scaledIntLatticeFundDomain (PeriodicLattice.torusSide D.L m) ε ∧
          ∃ x, torusHatFunction ε α x * f i x ≠ 0}.ncard from
        (Set.ncard_eq_toFinset_card _ (hfin i)).symm]
      exact (hcnt (f i) ⟨y i, hy i⟩).trans (min_le_left _ _)
    · have h1 := (hpb i α).2
      have h2 := mul_le_mul_of_nonneg_left
        (sharpNormR4_lift_le (by linarith : (0 : ℝ) ≤ M) (hfb i) (hf i))
        (by have := copySize_nonneg (b := b) (by linarith : (0 : ℝ) ≤ A) l (2 * ε); positivity :
          (0 : ℝ) ≤ 5 * copySize A b l (2 * ε))
      have h3 : sharpNormR4 M (g i) = sharpNormR4 M
          (fun x => f i (torusProj (PeriodicLattice.torusSide D.L m) x)) := rfl
      rw [← h3] at h2
      nlinarith
    · exact (uniformNorm_nonneg _).trans (le_max_left _ _)
  · intro k e he c hc
    have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective e he
    have h8 : 8 * l ≤ d := by linarith
    have hsp : ∀ j j', j ≠ j' → ∀ x z, p (e j) (c j) x ≠ 0 → p (e j') (c j') z ≠ 0 →
        8 * l ≤ euclidDistTorus (torusProj (PeriodicLattice.torusSide D.L m) x)
          (torusProj (PeriodicLattice.torusSide D.L m) z) := fun j j' hjj x z hx hz =>
      h8.trans (le_euclidDistTorus_of_separated (hsep.2 (e j) (e j') (fun h => hjj (he h)))
        (hpsupp _ _ _ hx) (hpsupp _ _ _ hz))
    refine (hP D A b l ε n k (by linarith) (by linarith) hkn (by omega) hI ⟨_, hj⟩ hq rfl
      (fun j => p (e j) (c j)) c (fun j => (hpb _ _).1) ?_ ?_).2 m ?_ hsp
    · intro j x hx μ
      exact ((hT.1 ε hε).2.2.1 (c j) x (left_ne_zero_of_mul hx) μ).le
    · intro j j' hjj x z hx hz
      exact (hsp j j' hjj x z hx hz).trans (euclidDistTorus_proj_le _ x z)
    · have h1 : (2 : ℝ) ≤ PeriodicLattice.torusSide D.L m := by
        unfold PeriodicLattice.torusSide
        linarith
      linarith
theorem fineCaseMomentBound_holds (h₁ : hatPartitionOfUnity_prop) (h₂ : CenteredProductBound)
    (h₃ : SmearedObservableBound)
    (h₄ : PeriodicLattice.WilsonCumulantWellPosedness.statement)
    (h₅ : PeriodicLattice.WilsonActionPlaquetteSumAndHaarSymmetry)
    (h₆ : InfiniteLattice.OneSpacing.AllFacts) :
    FineCaseMomentBound := by
  intro D A b M R d l n hA hb hM hR hd hd1 hn hI hl hq
  exact ⟨fun ν hν f hf hball hsep J _ =>
      centred_moment_gibbs h₁ h₂ h₃ h₆ D A b M R d l n hA hb hM hR hd hd1 hn hI hl hq ν hν f hf hball
        hsep J,
    fun m f hf hball hsep J _ =>
      centred_moment_torus h₁ h₂ h₃ h₄ h₅ D A b M R d l n hA hb hM hR hd hd1 hn hI hl hq m f hf hball
        hsep J⟩
end SystemOfAdmissibleConstants.FineCaseMoments
end YangMills.Construction
end
