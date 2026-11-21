import YangMills.Construction.ResponseInTheExpansion.CumulantsOfQuadraticFormsProof
import YangMills.Construction.Cumulants.MomentsLinearityBoundsAndTelescopingOfJointCumulants
import YangMills.Construction.FourPointCondition.CumulantOfAnObservable
import YangMills.Construction.ReflectionPositivity.CentredMomentsAreSumsOfCumulantsProof
import YangMills.Construction.SourcesAndGluing.CumulantsOfBoundedVariablesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ENNReal
namespace YangMills.Construction.FourPointCondition
open YangMills.Construction.ResponseInTheExpansion YangMills.Construction.BlockAverages
open YangMills.Construction.Probability (IsBoundedRealRV)
open YangMills.Construction.Cumulants
section Cumulants
variable {Ω : Type} [MeasurableSpace Ω]
private theorem mixedCumulant_congr_ae {ν : Measure Ω} {k : ℕ} {X Y : Fin k → Ω → ℝ}
    (h : ∀ i, X i =ᵐ[ν] Y i) : mixedCumulant ν X = mixedCumulant ν Y := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.CentredMomentExpansion.mixedCumulant_congr_ae <;> assumption
private theorem isBoundedRealRV_add {X Y : Ω → ℝ} (hX : IsBoundedRealRV X) (hY : IsBoundedRealRV Y) :
    IsBoundedRealRV fun ω => X ω + Y ω := by
  obtain ⟨a, ha⟩ := hX.bounded
  obtain ⟨b, hb⟩ := hY.bounded
  exact ⟨hX.measurable.add hY.measurable, a + b, fun ω => (abs_add_le _ _).trans (add_le_add (ha ω) (hb ω))⟩
private theorem isBoundedRealRV_const_mul {X : Ω → ℝ} (a : ℝ) (hX : IsBoundedRealRV X) :
    IsBoundedRealRV fun ω => a * X ω := by
  obtain ⟨b, hb⟩ := hX.bounded
  refine ⟨hX.measurable.const_mul a, |a| * b, fun ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg a)
abbrev _root_.YangMills.SharedProofs.p15020 := @isBoundedRealRV_const_mul
private theorem isBoundedRealRV_const (a : ℝ) : IsBoundedRealRV fun _ : Ω => a :=
  ⟨measurable_const, |a|, fun _ => le_rfl⟩
private theorem mixedCumulant_affine (hT : MixedCumulantFacts.MixedCumulantProperties) (ν : Measure Ω)
    [IsProbabilityMeasure ν] {k : ℕ} (hk : 2 ≤ k) (X : Fin k → Ω → ℝ)
    (hX : ∀ i, IsBoundedRealRV (X i)) (a : ℝ) (b : Fin k → ℝ) :
    mixedCumulant ν (fun i ω => a * (X i ω + b i)) = (a : ℂ) ^ k * mixedCumulant ν X := by
  classical
  have step : ∀ S : Finset (Fin k), mixedCumulant ν
      (fun i ω => if i ∈ S then a * (X i ω + b i) else X i ω) = (a : ℂ) ^ S.card * mixedCumulant ν X := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      set Z : Fin k → Ω → ℝ := fun j ω => if j ∈ S then a * (X j ω + b j) else X j ω with hZ
      have hZb : ∀ j, IsBoundedRealRV (Z j) := by
        intro j
        by_cases hj : j ∈ S
        · have : Z j = fun ω => a * (X j ω + b j) := by funext ω; simp [hZ, hj]
          rw [this]
          exact isBoundedRealRV_const_mul a (isBoundedRealRV_add (hX j) (isBoundedRealRV_const _))
        · have : Z j = X j := by funext ω; simp [hZ, hj]
          rw [this]
          exact hX j
      have hZi : Z i = X i := by funext ω; simp [hZ, hi]
      obtain ⟨_, h2, _, h4, _, _⟩ := hT Ω ν k Z Z (by omega) hZb hZb
      obtain ⟨_, _, _, h4', _, _⟩ := hT Ω ν k Z Z (by omega) hZb hZb
      have e1 : (fun j ω => if j ∈ insert i S then a * (X j ω + b j) else X j ω) =
          Function.update Z i fun ω => a * (X i ω + b i) + 0 * X i ω := by
        funext j ω
        by_cases hj : j = i
        · subst hj
          simp
        · simp [hZ, hj]
      have e2 := h2 i (fun ω => X i ω + b i) (X i) a 0 (isBoundedRealRV_add (hX i) (isBoundedRealRV_const _)) (hX i)
      have e3 : Function.update Z i (fun ω => X i ω + b i) = Function.update Z i fun ω => Z i ω + b i := by
        rw [hZi]
      have e4 := h4 (by omega) i (b i)
      have e5 : Function.update Z i (Z i) = Z := Function.update_eq_self _ _
      rw [e1, e2, e3, e4, Finset.card_insert_of_notMem hi, ih, pow_succ]
      push_cast
      ring
  have := step Finset.univ
  simpa using this
private theorem memLp_of_isBoundedRealRV (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : IsBoundedRealRV f) (p : ℝ≥0∞) : MemLp f p ν := by
  obtain ⟨C, hC⟩ := hf.bounded
  exact MemLp.of_bound hf.measurable.aestronglyMeasurable C
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC ω)
private theorem eLpNorm_four_le (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : IsBoundedRealRV f) {B : ℝ} (hB : 0 ≤ B) (h : ∫ ω, f ω ^ 4 ∂ν ≤ B ^ 4) :
    (eLpNorm f 4 ν).toReal ≤ B := by
  have hm := memLp_of_isBoundedRealRV ν hf 4
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), ENNReal.toReal_ofReal (by positivity)]
  have e : ∀ ω, ‖f ω‖ ^ (4 : ℝ≥0∞).toReal = f ω ^ 4 := by
    intro ω
    have : (4 : ℝ≥0∞).toReal = ((4 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast, Real.norm_eq_abs]
    exact Even.pow_abs (by decide) _
  simp only [e]
  have h4 : ((4 : ℝ≥0∞).toReal)⁻¹ = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [h4]
  calc (∫ ω, f ω ^ 4 ∂ν) ^ (((4 : ℕ) : ℝ)⁻¹) ≤ (B ^ 4) ^ (((4 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (integral_nonneg fun ω => by positivity) h (by positivity)
    _ = B := Real.pow_rpow_inv_natCast hB (by norm_num)
abbrev _root_.YangMills.SharedProofs.p27363 := @eLpNorm_four_le
private theorem eLpNorm_four_sum_le (ν : Measure Ω) [IsProbabilityMeasure ν] {ι : Type} (s : Finset ι)
    (f : ι → Ω → ℝ) (hf : ∀ i, IsBoundedRealRV (f i)) :
    (eLpNorm (fun ω => ∑ i ∈ s, f i ω) 4 ν).toReal ≤ ∑ i ∈ s, (eLpNorm (f i) 4 ν).toReal := by
  have e : (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, f i := by
    funext ω
    simp
  rw [e]
  have h1 := eLpNorm_sum_le (μ := ν) (s := s) (f := f) (p := 4)
    (fun i _ => (hf i).measurable.aestronglyMeasurable) (by norm_num)
  have h2 : ∀ i ∈ s, eLpNorm (f i) 4 ν ≠ ⊤ := fun i _ => (memLp_of_isBoundedRealRV ν (hf i) 4).eLpNorm_ne_top
  calc (eLpNorm (∑ i ∈ s, f i) 4 ν).toReal ≤ (∑ i ∈ s, eLpNorm (f i) 4 ν).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 h2) h1
    _ = ∑ i ∈ s, (eLpNorm (f i) 4 ν).toReal := ENNReal.toReal_sum h2
private theorem eLpNorm_four_add_le (ν : Measure Ω) [IsProbabilityMeasure ν] {f g : Ω → ℝ}
    (hf : IsBoundedRealRV f) (hg : IsBoundedRealRV g) :
    (eLpNorm (fun ω => f ω + g ω) 4 ν).toReal ≤ (eLpNorm f 4 ν).toReal + (eLpNorm g 4 ν).toReal := by
  have h1 := eLpNorm_add_le (μ := ν) (p := 4) hf.measurable.aestronglyMeasurable
    hg.measurable.aestronglyMeasurable (by norm_num)
  have hf' := (memLp_of_isBoundedRealRV ν hf 4).eLpNorm_ne_top
  have hg' := (memLp_of_isBoundedRealRV ν hg 4).eLpNorm_ne_top
  calc (eLpNorm (fun ω => f ω + g ω) 4 ν).toReal ≤ (eLpNorm f 4 ν + eLpNorm g 4 ν).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf', hg'⟩) h1
    _ = _ := ENNReal.toReal_add hf' hg'
abbrev _root_.YangMills.SharedProofs.p72579 := @eLpNorm_four_add_le
private theorem norm_mixedCumulant_sub_le (hT : MixedCumulantFacts.MixedCumulantProperties) (ν : Measure Ω)
    [IsProbabilityMeasure ν] {k : ℕ} (h1 : 1 ≤ k) (h4 : k ≤ 4) (Y Z : Fin k → Ω → ℝ)
    (hY : ∀ i, IsBoundedRealRV (Y i)) (hZ : ∀ i, IsBoundedRealRV (Z i))
    {ε A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hd : ∀ i, (eLpNorm (fun ω => Y i ω - Z i ω) 4 ν).toReal ≤ ε)
    (hYn : ∀ i, (eLpNorm (Y i) 4 ν).toReal ≤ A) (hZn : ∀ i, (eLpNorm (Z i) 4 ν).toReal ≤ A) :
    ‖mixedCumulant ν Y - mixedCumulant ν Z‖ ≤ 26 * k * (ε * A ^ (k - 1)) := by
  classical
  set D : Fin k → Ω → ℝ := fun i ω => Y i ω - Z i ω with hD
  have hDb : ∀ i, IsBoundedRealRV (D i) := fun i => by
    have := isBoundedRealRV_add (hY i) (isBoundedRealRV_const_mul (-1) (hZ i))
    have e : D i = fun ω => Y i ω + -1 * Z i ω := by funext ω; simp [hD]; ring
    rw [e]
    exact this
  obtain ⟨_, _, _, _, _, tel⟩ := hT Ω ν k Z D h1 hZ hDb
  have eY : (fun i ω => Z i ω + D i ω) = Y := by
    funext i ω
    simp [hD]
  rw [eY] at tel
  rw [tel]
  have each : ∀ i, ‖mixedCumulant ν (MixedCumulantFacts.telescopeTuple Z D i)‖ ≤
      26 * (ε * A ^ (k - 1)) := by
    intro i
    set E := MixedCumulantFacts.telescopeTuple Z D i with hE
    have hEb : ∀ j, IsBoundedRealRV (E j) := by
      intro j
      by_cases c1 : j < i
      · have : E j = Z j := by funext ω; simp [hE, MixedCumulantFacts.telescopeTuple, c1]
        rw [this]; exact hZ j
      · by_cases c2 : j = i
        · have : E j = D j := by funext ω; simp [hE, MixedCumulantFacts.telescopeTuple, c2]
          rw [this]; exact hDb j
        · have : E j = fun ω => Z j ω + D j ω := by
            funext ω; simp [hE, MixedCumulantFacts.telescopeTuple, c1, c2]
          rw [this]; exact isBoundedRealRV_add (hZ j) (hDb j)
    have hnorm : ∀ j, (eLpNorm (E j) 4 ν).toReal ≤ if j = i then ε else A := by
      intro j
      by_cases c1 : j < i
      · have e : E j = Z j := by funext ω; simp [hE, MixedCumulantFacts.telescopeTuple, c1]
        rw [e, if_neg (ne_of_lt c1)]; exact hZn j
      · by_cases c2 : j = i
        · have e : E j = D j := by funext ω; simp [hE, MixedCumulantFacts.telescopeTuple, c2]
          rw [e, if_pos c2]; exact hd j
        · have e : E j = Y j := by
            funext ω; simp [hE, MixedCumulantFacts.telescopeTuple, c1, c2, hD]
          rw [e, if_neg c2]; exact hYn j
    obtain ⟨_, _, _, _, bd, _⟩ := hT Ω ν k E E h1 hEb hEb
    have b0 := bd h4 ∅
    simp only [Finset.prod_empty, mul_one, Finset.compl_empty] at b0
    have hc : MixedCumulantFacts.cumulantBoundConst k ≤ 26 := by
      interval_cases k <;> norm_num [MixedCumulantFacts.cumulantBoundConst]
    have hc0 : 0 ≤ MixedCumulantFacts.cumulantBoundConst k := by
      interval_cases k <;> norm_num [MixedCumulantFacts.cumulantBoundConst]
    have hp : ∏ j, (eLpNorm (E j) 4 ν).toReal ≤ ε * A ^ (k - 1) := by
      calc ∏ j, (eLpNorm (E j) 4 ν).toReal ≤ ∏ j, (if j = i then ε else A) :=
            Finset.prod_le_prod (fun j _ => ENNReal.toReal_nonneg) fun j _ => hnorm j
        _ = ε * A ^ (k - 1) := by
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
            congr 1
            rw [Finset.prod_congr rfl (g := fun _ => A) (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
              Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hp0 : 0 ≤ ε * A ^ (k - 1) := by positivity
    calc _ ≤ _ := b0
      _ ≤ 26 * (ε * A ^ (k - 1)) := mul_le_mul hc hp (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg) (by norm_num)
  calc ‖∑ i, mixedCumulant ν (MixedCumulantFacts.telescopeTuple Z D i)‖
      ≤ ∑ i, ‖mixedCumulant ν (MixedCumulantFacts.telescopeTuple Z D i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, 26 * (ε * A ^ (k - 1)) := Finset.sum_le_sum fun i _ => each i
    _ = 26 * k * (ε * A ^ (k - 1)) := by simp; ring
end Cumulants
section QuadraticApproximation
variable {Ω : Type} [MeasurableSpace Ω]
private theorem isBoundedRealRV_quadraticForm {I : Type} [Fintype I] (κ : Matrix I I ℝ)
    (H : Ω → I → imaginaryQuaternions) {Bg : ℝ}
    (hm : ∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (H ω a))
    (hb : ∀ ω a e, |imaginaryComponent e (H ω a)| ≤ Bg) :
    IsBoundedRealRV fun ω => quadraticForm κ (H ω) := by
  refine ⟨?_, (1 / 2) * ∑ a, ∑ b, |κ a b| * ∑ _e : Fin 3, Bg * Bg, fun ω => ?_⟩
  · unfold quadraticForm
    refine measurable_const.mul (Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
      measurable_const.mul (Finset.measurable_sum _ fun e _ => (hm a e).mul (hm b e)))
  · unfold quadraticForm
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hb ω a e) (hb ω b e) (abs_nonneg _) ((abs_nonneg _).trans (hb ω a e))
abbrev _root_.YangMills.SharedProofs.p57896 := @isBoundedRealRV_quadraticForm
private theorem isBoundedRealRV_indicator {S : Set Ω} (hS : MeasurableSet S) {f : Ω → ℝ}
    (hf : IsBoundedRealRV f) : IsBoundedRealRV (S.indicator f) := by
  obtain ⟨C, hC⟩ := hf.bounded
  refine ⟨hf.measurable.indicator hS, |C|, fun ω => ?_⟩
  by_cases h : ω ∈ S
  · rw [Set.indicator_of_mem h]
    exact (hC ω).trans (le_abs_self _)
  · rw [Set.indicator_of_notMem h]
    simp
abbrev _root_.YangMills.SharedProofs.p34315 := @isBoundedRealRV_indicator
private theorem eLpNorm_four_indicator_quadraticForm_le (ν : Measure Ω) [IsProbabilityMeasure ν] {S : Set Ω}
    (hS : MeasurableSet S) {I : Type} [Fintype I] (κ : Matrix I I ℝ) (H : Ω → I → imaginaryQuaternions) {Bg K : ℝ}
    (hm : ∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (H ω a))
    (hb : ∀ ω a e, |imaginaryComponent e (H ω a)| ≤ Bg) (hK : 0 ≤ K)
    (h8 : ∀ (a b : I) (e : Fin 3), ∫ ω, S.indicator
      (fun ω => imaginaryComponent e (H ω a) ^ 4 * imaginaryComponent e (H ω b) ^ 4) ω ∂ν ≤ K ^ 4) :
    (eLpNorm (S.indicator fun ω => quadraticForm κ (H ω)) 4 ν).toReal ≤ 3 / 2 * (∑ a, ∑ b, |κ a b|) * K := by
  classical
  set f : I × I × Fin 3 → Ω → ℝ := fun t => S.indicator
    (fun ω => (1 / 2 * κ t.1 t.2.1) * (imaginaryComponent t.2.2 (H ω t.1) * imaginaryComponent t.2.2 (H ω t.2.1)))
    with hf
  have hfb : ∀ t, IsBoundedRealRV (f t) := by
    intro t
    refine isBoundedRealRV_indicator hS (isBoundedRealRV_const_mul _ ⟨(hm _ _).mul (hm _ _), Bg * Bg, fun ω => ?_⟩)
    rw [abs_mul]
    exact mul_le_mul (hb _ _ _) (hb _ _ _) (abs_nonneg _) ((abs_nonneg _).trans (hb ω t.1 t.2.2))
  have e : (S.indicator fun ω => quadraticForm κ (H ω)) = fun ω => ∑ t, f t ω := by
    funext ω
    by_cases h : ω ∈ S
    · simp only [hf, Set.indicator_of_mem h, quadraticForm, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    · simp [hf, Set.indicator_of_notMem h]
  rw [e]
  refine (eLpNorm_four_sum_le ν Finset.univ f hfb).trans ?_
  have each : ∀ t : I × I × Fin 3, (eLpNorm (f t) 4 ν).toReal ≤ 1 / 2 * |κ t.1 t.2.1| * K := by
    intro t
    refine eLpNorm_four_le ν (hfb t) (by positivity) ?_
    have e4 : ∀ ω, f t ω ^ 4 = (1 / 2 * κ t.1 t.2.1) ^ 4 * S.indicator
        (fun ω => imaginaryComponent t.2.2 (H ω t.1) ^ 4 * imaginaryComponent t.2.2 (H ω t.2.1) ^ 4) ω := by
      intro ω
      by_cases h : ω ∈ S
      · simp only [hf, Set.indicator_of_mem h]
        ring
      · simp [hf, Set.indicator_of_notMem h]
    simp only [e4]
    rw [integral_const_mul]
    have h4 : (1 / 2 * κ t.1 t.2.1) ^ 4 = (1 / 2 * |κ t.1 t.2.1|) ^ 4 := by
      rw [mul_pow, mul_pow, Even.pow_abs (by decide)]
    rw [h4, mul_pow (1 / 2 * |κ t.1 t.2.1|) K 4]
    exact mul_le_mul_of_nonneg_left (h8 _ _ _) (by positivity)
  refine (Finset.sum_le_sum fun t _ => each t).trans (le_of_eq ?_)
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring
abbrev _root_.YangMills.SharedProofs.p29187 := @eLpNorm_four_indicator_quadraticForm_le
private theorem mixedCumulant_near_quadraticForms (hT : MixedCumulantFacts.MixedCumulantProperties)
    (hCQ : quadraticFormCumulantsStatement) (q : ℕ) (Bt : ℝ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A E : Set Ω) (I : Type) [Fintype I] (H : Ω → I → imaginaryQuaternions) (Tc : Matrix I I ℝ) (ε₂ Bg : ℝ)
      (κ : Fin (q + 1) → Matrix I I ℝ) (X : Fin (q + 1) → Ω → ℝ) (a : ℝ) (b : Fin (q + 1) → ℝ)
      (ρ τ τ' K Kap : ℝ),
      MeasurableSet A → MeasurableSet E → E ⊆ A → (∀ i, (κ i).IsSymm) →
      (∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (H ω a)) →
      (∀ ω a e, |imaginaryComponent e (H ω a)| ≤ Bg) → Tc.IsSymm → (∀ a b, |Tc a b| ≤ Bt) → 0 ≤ ε₂ → ε₂ ≤ 1 →
      (∀ (r : ℕ) (a : Fin r → I) (e : Fin r → Fin 3), r ≤ 2 * (q + 1) →
        |∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (H ω (a i))) ω ∂μ -
          wickPairingSum fun i i' => if e i = e i' then Tc (a i) (a i') else 0| ≤ ε₂) →
      (∀ i, IsBoundedRealRV (X i)) → 0 ≤ ρ → 0 ≤ τ → 0 ≤ τ' → 0 ≤ K → 0 ≤ Kap →
      (∀ i, ∑ a, ∑ b, |κ i a b| ≤ Kap) →
      (∀ i, ∫ ω, E.indicator (fun ω => (a * (X i ω + b i) - quadraticForm (κ i) (H ω)) ^ 4) ω ∂μ ≤ ρ ^ 4) →
      (∀ i, ∫ ω, Eᶜ.indicator (fun ω => (a * (X i ω + b i)) ^ 4) ω ∂μ ≤ τ ^ 4) →
      (∀ (c d : I) (e : Fin 3), ∫ ω, A.indicator
        (fun ω => imaginaryComponent e (H ω c) ^ 4 * imaginaryComponent e (H ω d) ^ 4) ω ∂μ ≤ K ^ 4) →
      (∀ (c d : I) (e : Fin 3), ∫ ω, (A \ E).indicator
        (fun ω => imaginaryComponent e (H ω c) ^ 4 * imaginaryComponent e (H ω d) ^ 4) ω ∂μ ≤ τ' ^ 4) →
      ‖(a : ℂ) ^ (q + 1) * mixedCumulant μ X - ((cyclicTraceSum κ Tc : ℝ) : ℂ)‖ ≤
        26 * ((q : ℝ) + 1) * ((ρ + τ + 3 / 2 * Kap * τ') *
          (ρ + τ + 3 / 2 * Kap * τ' + 3 / 2 * Kap * K) ^ q) + C * Kap ^ (q + 1) * ε₂ := by
  obtain ⟨C, hC⟩ := hCQ q Bt hq1 hq3
  refine ⟨|C|, ?_⟩
  intro Ω _ μ _ A E I _ H Tc ε₂ Bg κ X a b ρ τ τ' K Kap hA hE hEA hκs hm hb hTs hTb hε0 hε1 hmom hX hρ hτ hτ' hK hKap
    hκ hnear htail h8A h8E
  set Y : Fin (q + 1) → Ω → ℝ := fun i ω => a * (X i ω + b i) with hY
  set Z : Fin (q + 1) → Ω → ℝ := fun i => A.indicator fun ω => quadraticForm (κ i) (H ω) with hZ
  have hYb : ∀ i, IsBoundedRealRV (Y i) := fun i =>
    isBoundedRealRV_const_mul a (isBoundedRealRV_add (hX i) (isBoundedRealRV_const _))
  have hQb : ∀ i, IsBoundedRealRV fun ω => quadraticForm (κ i) (H ω) := fun i =>
    isBoundedRealRV_quadraticForm _ _ hm hb
  have hZb : ∀ i, IsBoundedRealRV (Z i) := fun i => isBoundedRealRV_indicator hA (hQb i)
  have hZn : ∀ i, (eLpNorm (Z i) 4 μ).toReal ≤ 3 / 2 * Kap * K := fun i =>
    (eLpNorm_four_indicator_quadraticForm_le μ hA (κ i) H hm hb hK h8A).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hκ i) (by norm_num)) hK)
  set ε₁ : ℝ := ρ + τ + 3 / 2 * Kap * τ' with hε₁
  have hd : ∀ i, (eLpNorm (fun ω => Y i ω - Z i ω) 4 μ).toReal ≤ ε₁ := by
    intro i
    have p1 : IsBoundedRealRV (E.indicator fun ω => Y i ω - quadraticForm (κ i) (H ω)) := by
      refine isBoundedRealRV_indicator hE ?_
      have := isBoundedRealRV_add (hYb i) (isBoundedRealRV_const_mul (-1) (hQb i))
      have e : (fun ω => Y i ω - quadraticForm (κ i) (H ω)) =
          fun ω => Y i ω + -1 * quadraticForm (κ i) (H ω) := by funext ω; ring
      rw [e]; exact this
    have p2 : IsBoundedRealRV (Eᶜ.indicator (Y i)) := isBoundedRealRV_indicator hE.compl (hYb i)
    have p3 : IsBoundedRealRV ((A \ E).indicator fun ω => -1 * quadraticForm (κ i) (H ω)) :=
      isBoundedRealRV_indicator (hA.diff hE) (isBoundedRealRV_const_mul _ (hQb i))
    have e : (fun ω => Y i ω - Z i ω) = fun ω =>
        ((E.indicator fun ω => Y i ω - quadraticForm (κ i) (H ω)) ω + Eᶜ.indicator (Y i) ω) +
          (A \ E).indicator (fun ω => -1 * quadraticForm (κ i) (H ω)) ω := by
      funext ω
      by_cases h1 : ω ∈ E
      · have h2 := hEA h1
        simp [hZ, Set.indicator_of_mem h1, Set.indicator_of_mem h2, h1]
      · by_cases h2 : ω ∈ A
        · have h3 : ω ∈ A \ E := ⟨h2, h1⟩
          simp [hZ, Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Set.indicator_of_mem h3, h1, h2]
          ring
        · have h3 : ω ∉ A \ E := fun h => h2 h.1
          simp [hZ, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, Set.indicator_of_notMem h3, h1]
    rw [e]
    have n1 : (eLpNorm (E.indicator fun ω => Y i ω - quadraticForm (κ i) (H ω)) 4 μ).toReal ≤ ρ := by
      refine eLpNorm_four_le μ p1 hρ ((le_of_eq ?_).trans (hnear i))
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      by_cases h : ω ∈ E <;> simp [h, hY]
    have n2 : (eLpNorm (Eᶜ.indicator (Y i)) 4 μ).toReal ≤ τ := by
      refine eLpNorm_four_le μ p2 hτ ((le_of_eq ?_).trans (htail i))
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      by_cases h : ω ∈ E <;> simp [h, hY]
    have n3 : (eLpNorm ((A \ E).indicator fun ω => -1 * quadraticForm (κ i) (H ω)) 4 μ).toReal ≤
        3 / 2 * Kap * τ' := by
      have e3 : ((A \ E).indicator fun ω => -1 * quadraticForm (κ i) (H ω)) =
          fun ω => -1 * (A \ E).indicator (fun ω => quadraticForm (κ i) (H ω)) ω := by
        funext ω
        by_cases h : ω ∈ A \ E <;> simp [h]
      have e4 : (eLpNorm ((A \ E).indicator fun ω => -1 * quadraticForm (κ i) (H ω)) 4 μ) =
          eLpNorm ((A \ E).indicator fun ω => quadraticForm (κ i) (H ω)) 4 μ := by
        rw [e3]
        refine eLpNorm_congr_norm_ae (ae_of_all _ fun ω => ?_)
        simp
      rw [e4]
      exact (eLpNorm_four_indicator_quadraticForm_le μ (hA.diff hE) (κ i) H hm hb hτ' h8E).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hκ i) (by norm_num)) hτ')
    calc _ ≤ _ := eLpNorm_four_add_le μ (isBoundedRealRV_add p1 p2) p3
      _ ≤ (eLpNorm (fun ω => (E.indicator fun ω => Y i ω - quadraticForm (κ i) (H ω)) ω +
            Eᶜ.indicator (Y i) ω) 4 μ).toReal + 3 / 2 * Kap * τ' := by gcongr
      _ ≤ _ := by
        have := eLpNorm_four_add_le μ p1 p2
        rw [hε₁]
        linarith
  have hε₁0 : 0 ≤ ε₁ := by positivity
  have hYn : ∀ i, (eLpNorm (Y i) 4 μ).toReal ≤ ε₁ + 3 / 2 * Kap * K := by
    intro i
    have hDb : IsBoundedRealRV fun ω => Y i ω - Z i ω := by
      have := isBoundedRealRV_add (hYb i) (isBoundedRealRV_const_mul (-1) (hZb i))
      have e : (fun ω => Y i ω - Z i ω) = fun ω => Y i ω + -1 * Z i ω := by funext ω; ring
      rw [e]; exact this
    have e : Y i = fun ω => (Y i ω - Z i ω) + Z i ω := by funext ω; ring
    rw [e]
    exact (eLpNorm_four_add_le μ hDb (hZb i)).trans (add_le_add (hd i) (hZn i))
  have hclose := norm_mixedCumulant_sub_le hT μ (by omega : 1 ≤ q + 1) (by omega : q + 1 ≤ 4) Y Z hYb hZb hε₁0
    (by positivity : 0 ≤ ε₁ + 3 / 2 * Kap * K) hd hYn
    (fun i => (hZn i).trans (by linarith))
  have hGauss := hC Ω μ A I H Tc 1 ε₂ Bg κ hA hκs hm hb le_rfl hTs hTb hε0 hε1 (by
    intro r a e hr
    have := hmom r a e hr
    simpa using this)
  have hYc : mixedCumulant μ Y = (a : ℂ) ^ (q + 1) * mixedCumulant μ X :=
    mixedCumulant_affine hT μ (by omega) X hX a b
  rw [← hYc]
  have hone : ((((1 : ℝ) ^ (-((q : ℝ) + 1)) * cyclicTraceSum κ Tc : ℝ)) : ℂ) = ((cyclicTraceSum κ Tc : ℝ) : ℂ) := by
    simp
  rw [hone] at hGauss
  have hprod : ∏ i, ∑ a, ∑ b, |κ i a b| ≤ Kap ^ (q + 1) := by
    calc ∏ i, ∑ a, ∑ b, |κ i a b| ≤ ∏ _i : Fin (q + 1), Kap :=
          Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _)
            fun i _ => hκ i
      _ = Kap ^ (q + 1) := by simp
  have hg2 : ‖mixedCumulant μ Z - ((cyclicTraceSum κ Tc : ℝ) : ℂ)‖ ≤ |C| * Kap ^ (q + 1) * ε₂ := by
    refine hGauss.trans ?_
    have h0 : 0 ≤ ∏ i, ∑ a, ∑ b, |κ i a b| :=
      Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hprod h0 (abs_nonneg _)) hε0
  calc _ = ‖(mixedCumulant μ Y - mixedCumulant μ Z) +
        (mixedCumulant μ Z - ((cyclicTraceSum κ Tc : ℝ) : ℂ))‖ := by
        congr 1
        ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by
      refine add_le_add ?_ hg2
      refine hclose.trans (le_of_eq ?_)
      push_cast
      simp
abbrev _root_.YangMills.SharedProofs.p29850 := @mixedCumulant_near_quadraticForms
end QuadraticApproximation
structure QuadraticFourthMomentApproximation {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {I : Type} [Fintype I] {q : ℕ}
    (F : Fin (q + 1) → Ω → ℝ) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω) (K : Fin (q + 1) → Matrix I I ℝ)
    (T : Matrix I I ℝ) (c : Fin (q + 1) → ℝ) (x n C P M D : ℝ) : Prop where
  measurableSet_event : MeasurableSet A
  measurable_component : ∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (G ω a)
  abs_component_le : ∀ ω a e, |imaginaryComponent e (G ω a)| ≤ M
  gaussian_moments : ∀ (r : ℕ) (a : Fin r → I) (e : Fin r → Fin 3), r ≤ 16 →
    Integrable (Set.indicator A fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) μ ∧
    |∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) ω ∂μ -
      x ^ (-(r : ℝ) / 2) * wickPairingSum fun i j => if e i = e j then T (a i) (a j) else 0| ≤
      C * x ^ (-((r : ℝ) + 1) / 2 + 2 / 1000)
  covariance_isSymm : T.IsSymm
  abs_covariance_le : ∀ a b, |T a b| ≤ C
  kernel_isSymm : ∀ i, (K i).IsSymm
  kernel_sum_abs_le : ∀ i, ∑ a, ∑ b, |K i a b| ≤ C * n ^ 4 * Real.log x ^ 24
  lintegral_deviation_le : ∀ (i : Fin (q + 1)),
    ∫⁻ ω, ENNReal.ofReal (Set.indicator (A ∩ B)
        (fun ω => |F i ω - c i - quadraticForm (K i) (G ω)| ^ (2 * 2)) ω) ∂μ ≤
      ENNReal.ofReal ((D * n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000)) ^ (2 * 2))
  measureReal_compl_le : μ.real Aᶜ ≤ C * x ^ (-P)
  measureReal_inter_compl_le : μ.real (A ∩ Bᶜ) ≤ C * x ^ (-P)
section Approximation
variable {Ω : Type} [MeasurableSpace Ω]
private theorem integrable_of_isBoundedRealRV (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : IsBoundedRealRV f) : Integrable f ν := by apply _root_.YangMills.Construction.SourcesAndGluing.BoundedCumulants.integrable_of_isBoundedRealRV <;> assumption
private theorem isBoundedRealRV_pow {f : Ω → ℝ} (hf : IsBoundedRealRV f) (k : ℕ) :
    IsBoundedRealRV fun ω => f ω ^ k := by
  obtain ⟨C, hC⟩ := hf.bounded
  refine ⟨hf.measurable.pow_const k, |C| ^ k, fun ω => ?_⟩
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((hC ω).trans (le_abs_self _)) k
abbrev _root_.YangMills.SharedProofs.p10820 := @isBoundedRealRV_pow
private theorem integral_indicator_pow_four_le (ν : Measure Ω) [IsProbabilityMeasure ν] {S : Set Ω}
    (hS : MeasurableSet S) {f : Ω → ℝ} (hf : IsBoundedRealRV f) {t : ℝ} (ht : 0 < t) :
    ∫ ω, S.indicator (fun ω => f ω ^ 4) ω ∂ν ≤ (t * ν.real S + (∫ ω, f ω ^ 8 ∂ν) / t) / 2 := by
  have i1 : Integrable (S.indicator fun ω => f ω ^ 4) ν :=
    integrable_of_isBoundedRealRV ν (isBoundedRealRV_indicator hS (isBoundedRealRV_pow hf 4))
  have i2 : Integrable (S.indicator (1 : Ω → ℝ)) ν :=
    integrable_of_isBoundedRealRV ν (isBoundedRealRV_indicator hS (isBoundedRealRV_const (1 : ℝ)))
  have i3 : Integrable (fun ω => f ω ^ 8) ν := integrable_of_isBoundedRealRV ν (isBoundedRealRV_pow hf 8)
  have e : (t * ν.real S + (∫ ω, f ω ^ 8 ∂ν) / t) / 2 =
      ∫ ω, (t * S.indicator (1 : Ω → ℝ) ω + f ω ^ 8 / t) / 2 ∂ν := by
    rw [integral_div, integral_add (i2.const_mul t) (i3.div_const t), integral_const_mul, integral_div,
      integral_indicator_one hS]
  rw [e]
  refine integral_mono i1 (((i2.const_mul t).add (i3.div_const t)).div_const 2) fun ω => ?_
  by_cases h : ω ∈ S
  · simp only [Set.indicator_of_mem h, Pi.one_apply, mul_one]
    have : 2 * f ω ^ 4 ≤ t + f ω ^ 8 / t := by
      have e2 : t + f ω ^ 8 / t - 2 * f ω ^ 4 = (t - f ω ^ 4) ^ 2 / t := by
        field_simp
        ring
      have : 0 ≤ (t - f ω ^ 4) ^ 2 / t := by positivity
      linarith
    linarith
  · simp only [Set.indicator_of_notMem h, mul_zero, zero_add]
    positivity
abbrev _root_.YangMills.SharedProofs.p45780 := @integral_indicator_pow_four_le
private theorem integral_pow_four_eq (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : IsBoundedRealRV f) : ∫ ω, f ω ^ 4 ∂ν = (eLpNorm f 4 ν).toReal ^ 4 := by
  have hm := memLp_of_isBoundedRealRV ν hf 4
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), ENNReal.toReal_ofReal (by positivity)]
  have e : ∀ ω, ‖f ω‖ ^ (4 : ℝ≥0∞).toReal = f ω ^ 4 := by
    intro ω
    have : (4 : ℝ≥0∞).toReal = ((4 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast, Real.norm_eq_abs]
    exact Even.pow_abs (by decide) _
  simp only [e]
  have h4 : ((4 : ℝ≥0∞).toReal)⁻¹ = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [h4, Real.rpow_inv_natCast_pow (integral_nonneg fun ω => by positivity) (by norm_num)]
private theorem abs_le_two_mul_eLpNorm_four_indicator (ν : Measure Ω) [IsProbabilityMeasure ν] {E : Set Ω}
    (hE : MeasurableSet E) (hp : 1 / 2 ≤ ν.real E) (D : ℝ) :
    |D| ≤ 2 * (eLpNorm (E.indicator fun _ => D) 4 ν).toReal := by
  have hb := isBoundedRealRV_indicator hE (isBoundedRealRV_const (Ω := Ω) D)
  have e := integral_pow_four_eq ν hb
  have e1 : (fun ω => (E.indicator (fun _ => D) ω) ^ 4) = E.indicator (fun _ => D ^ 4) := by
    funext ω
    by_cases h : ω ∈ E <;> simp [h]
  rw [e1, integral_indicator_const _ hE] at e
  simp only [smul_eq_mul] at e
  have h0 : 0 ≤ (eLpNorm (E.indicator fun _ => D) 4 ν).toReal := ENNReal.toReal_nonneg
  have h1 : (|D| / 2) ^ 4 ≤ (eLpNorm (E.indicator fun _ => D) 4 ν).toReal ^ 4 := by
    rw [← e, div_pow, Even.pow_abs (by decide)]
    have : 0 ≤ D ^ 4 := by positivity
    nlinarith
  have := (pow_le_pow_iff_left₀ (by positivity) h0 (by norm_num)).1 h1
  linarith
abbrev _root_.YangMills.SharedProofs.p8036 := @abs_le_two_mul_eLpNorm_four_indicator
private theorem imaginaryComponent_smul (s : ℝ) (v : imaginaryQuaternions) (e : Fin 3) :
    imaginaryComponent e (s • v) = s * imaginaryComponent e v := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem quadraticForm_smul {I : Type} [Fintype I] (κ : Matrix I I ℝ) (s : ℝ)
    (G : I → imaginaryQuaternions) :
    quadraticForm κ (fun a => s • G a) = s ^ 2 * quadraticForm κ G := by
  unfold quadraticForm
  simp only [imaginaryComponent_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring
abbrev _root_.YangMills.SharedProofs.p23085 := @quadraticForm_smul
open Classical in
private def pairingCountBound (r : ℕ) (D : ℝ) : ℝ :=
  ∑ _π : Finpartition (Finset.univ : Finset (Fin r)), D ^ r
private theorem abs_wickPairingSum_le {r : ℕ} {g : Fin r → Fin r → ℝ} {D : ℝ} (hD : 1 ≤ D)
    (hg : ∀ i j, |g i j| ≤ D) : |wickPairingSum g| ≤ pairingCountBound r D := by apply _root_.YangMills.DeltaSharedProofs.p500570 <;> assumption
private def logPowerConst : ℝ := 5000 ^ 24
private theorem logPowerConst_nonneg : 0 ≤ logPowerConst := by
  unfold logPowerConst
  norm_num
private theorem log_pow_le_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 24 ≤ logPowerConst * x ^ ((24 : ℝ) / 5000) := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 := Real.log_le_rpow_div (by linarith : 0 ≤ x) (by norm_num : (0 : ℝ) < 1 / 5000)
  have h2 : Real.log x ≤ 5000 * x ^ ((1 : ℝ) / 5000) := by
    refine h1.trans (le_of_eq ?_)
    ring
  calc Real.log x ^ 24 ≤ (5000 * x ^ ((1 : ℝ) / 5000)) ^ 24 := pow_le_pow_left₀ h0 h2 24
    _ = logPowerConst * x ^ ((24 : ℝ) / 5000) := by
      unfold logPowerConst
      rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 5000)), ← Real.rpow_mul (by linarith)]
      norm_num
private theorem pairingCountBound_nonneg (r : ℕ) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ pairingCountBound r D := by
  classical
  unfold pairingCountBound
  exact Finset.sum_nonneg fun _ _ => by positivity
abbrev _root_.YangMills.DeltaSharedProofs.p500915 := @pairingCountBound_nonneg
private theorem add_pow_eight_le (a b : ℝ) : (a + b) ^ 8 ≤ 128 * (a ^ 8 + b ^ 8) := by
  have h1 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have h2 : (a ^ 2 + b ^ 2) ^ 2 ≤ 2 * (a ^ 4 + b ^ 4) := by nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  have h3 : (a ^ 4 + b ^ 4) ^ 2 ≤ 2 * (a ^ 8 + b ^ 8) := by nlinarith [sq_nonneg (a ^ 4 - b ^ 4)]
  have h4 : ((a + b) ^ 2) ^ 4 ≤ (2 * (a ^ 2 + b ^ 2)) ^ 4 := pow_le_pow_left₀ (sq_nonneg _) h1 4
  have h5 : ((a ^ 2 + b ^ 2) ^ 2) ^ 2 ≤ (2 * (a ^ 4 + b ^ 4)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
  have e1 : (a + b) ^ 8 = ((a + b) ^ 2) ^ 4 := by ring
  rw [e1]
  linarith
abbrev _root_.YangMills.SharedProofs.p54202 := @add_pow_eight_le
private theorem prod_addCases_const {I : Type} (m : ℕ) (f : I → ℝ) (c d : I) :
    ∏ i : Fin (m + m), f (Fin.addCases (motive := fun _ => I) (fun _ => c) (fun _ => d) i) =
      f c ^ m * f d ^ m := by
  rw [Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
set_option maxHeartbeats 2000000 in
theorem mixedCumulant_of_fourthMomentApproximation (hT : MixedCumulantFacts.MixedCumulantProperties)
    (hCQ : quadraticFormCumulantsStatement) (q : ℕ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) (D : ℝ) (Cq : ℕ → ℝ) (C : ℝ) :
    ∃ C' x₁ : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Type) [Fintype I]
      (F : Fin (q + 1) → Ω → ℝ) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω) (κ : Fin (q + 1) → Matrix I I ℝ)
      (Tc : Matrix I I ℝ) (c κ₀ : Fin (q + 1) → ℝ) (x n w Bg : ℝ),
      x₁ ≤ x → 1 ≤ n → n ≤ x ^ ((1 : ℝ) / 90) → 0 ≤ w → w ≤ x →
      QuadraticFourthMomentApproximation μ F G A B κ Tc c x n C 40 Bg D →
      (∀ i, Measurable (F i)) → (∀ i, ∃ Cb : ℝ, ∀ᵐ ω ∂μ, |F i ω| ≤ Cb) →
      (∀ i (r : ℕ), 1 ≤ r → ∫ ω, |F i ω - κ₀ i| ^ (2 * r) ∂μ ≤ (Cq r * w) ^ (2 * r)) →
      ‖(x : ℂ) ^ (q + 1) * mixedCumulant μ F - ((cyclicTraceSum κ Tc : ℝ) : ℂ)‖ ≤
        C' * x ^ (-(1 / 5 : ℝ)) := by
  classical
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = |C| := ⟨_, rfl⟩
  have hCc0 : 0 ≤ Cc := hCc ▸ abs_nonneg _
  have hCle : C ≤ Cc := hCc ▸ le_abs_self _
  obtain ⟨Dm, hDm⟩ : ∃ Dm : ℝ, Dm = Cc + 1 := ⟨_, rfl⟩
  have hDm1 : 1 ≤ Dm := by linarith
  obtain ⟨Cg, hCg⟩ := mixedCumulant_near_quadraticForms hT hCQ q Dm hq1 hq3
  obtain ⟨K16, hK16⟩ : ∃ K : ℝ, K = pairingCountBound (8 + 8) Dm + Cc := ⟨_, rfl⟩
  obtain ⟨K8, hK8⟩ : ∃ K : ℝ, K = pairingCountBound (4 + 4) Dm + Cc := ⟨_, rfl⟩
  have hK16_0 : 0 ≤ K16 := hK16 ▸ add_nonneg (pairingCountBound_nonneg _ (by linarith)) hCc0
  have hK8_0 : 0 ≤ K8 := hK8 ▸ add_nonneg (pairingCountBound_nonneg _ (by linarith)) hCc0
  obtain ⟨Kq, hKq⟩ : ∃ K : ℝ, K = 1 + K8 := ⟨_, rfl⟩
  have hKq1 : 1 ≤ Kq := by linarith
  obtain ⟨K1, hK1⟩ : ∃ K : ℝ, K = Cc * logPowerConst + 1 := ⟨_, rfl⟩
  have hK1_1 : 1 ≤ K1 := by
    have : 0 ≤ Cc * logPowerConst := mul_nonneg hCc0 logPowerConst_nonneg
    linarith
  have hK1_0 : 0 ≤ K1 := by linarith
  have hKq0 : 0 ≤ Kq := by linarith
  obtain ⟨Kt', hKt'⟩ : ∃ K : ℝ, K = 1 + Cc + K16 := ⟨_, rfl⟩
  have hKt'1 : 1 ≤ Kt' := by linarith
  have hKt'0 : 0 ≤ Kt' := by linarith
  have hKK : 0 ≤ 3 / 2 * K1 * Kq := mul_nonneg (mul_nonneg (by norm_num) hK1_0) hKq0
  have hKK' : 0 ≤ 3 / 2 * K1 * Kt' := mul_nonneg (mul_nonneg (by norm_num) hK1_0) hKt'0
  obtain ⟨Kd, hKd⟩ : ∃ K : ℝ, K = 2 * (|D| + |Cq 2| + 3 / 2 * K1 * Kq) := ⟨_, rfl⟩
  have hKd0 : 0 ≤ Kd := by
    have := abs_nonneg (D)
    have := abs_nonneg (Cq 2)
    rw [hKd]
    linarith
  obtain ⟨Ky, hKy⟩ : ∃ K : ℝ, K = 128 * (|Cq 4| ^ 8 + Kd ^ 8) := ⟨_, rfl⟩
  have hKy0 : 0 ≤ Ky := by
    have h1 := pow_nonneg (abs_nonneg (Cq 4)) 8
    have h2 := pow_nonneg hKd0 8
    rw [hKy]
    linarith
  obtain ⟨Kt, hKt⟩ : ∃ K : ℝ, K = 1 + Cc + Ky := ⟨_, rfl⟩
  have hKt1 : 1 ≤ Kt := by linarith
  obtain ⟨K7, hK7⟩ : ∃ K : ℝ, K = |D| + Kt + 3 / 2 * K1 * Kt' := ⟨_, rfl⟩
  have hK7_0 : 0 ≤ K7 := by
    have := abs_nonneg (D)
    rw [hK7]
    linarith
  obtain ⟨K9, hK9⟩ : ∃ K : ℝ, K = K7 + 3 / 2 * K1 * Kq + 1 := ⟨_, rfl⟩
  have hK9_1 : 1 ≤ K9 := by linarith
  refine ⟨104 * K7 * K9 ^ 3 + |Cg| * K1 ^ 4 * Cc, (4 * Cc + 2) ^ 5, ?_⟩
  intro Ω _ μ _ I _ F G A B κ Tc c κ₀ x n w Bg hx₁ hn1 hn hw0 hwx R hFm hFb hFmom
  have hM16 := R.gaussian_moments
  have hm := R.measurable_component
  have hb := R.abs_component_le
  have hx32 : (1 : ℝ) ≤ (4 * Cc + 2) ^ 5 := one_le_pow₀ (by linarith)
  have hx1 : 1 ≤ x := hx32.trans hx₁
  have hx0 : 0 < x := by linarith
  have hroot : 4 * Cc + 2 ≤ x ^ ((1 : ℝ) / 5) := by
    have h1 := Real.rpow_le_rpow (by positivity) hx₁ (by norm_num : (0 : ℝ) ≤ 1 / 5)
    have e : ((4 * Cc + 2) ^ 5 : ℝ) ^ ((1 : ℝ) / 5) = 4 * Cc + 2 := by
      have := Real.pow_rpow_inv_natCast (by positivity : 0 ≤ 4 * Cc + 2) (by norm_num : (5 : ℕ) ≠ 0)
      norm_num at this ⊢
      exact this
    rwa [e] at h1
  have xp : ∀ {a b : ℝ}, a ≤ b → x ^ a ≤ x ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hx1 h
  have xm : ∀ a b : ℝ, x ^ a * x ^ b = x ^ (a + b) := fun a b => (Real.rpow_add hx0 a b).symm
  have xpos : ∀ a : ℝ, 0 < x ^ a := fun a => Real.rpow_pos_of_pos hx0 a
  have x1le : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ x ^ a := fun h => Real.one_le_rpow hx1 h
  have xle1 : ∀ {a : ℝ}, a ≤ 0 → x ^ a ≤ 1 := fun h => Real.rpow_le_one_of_one_le_of_nonpos hx1 h
  have xnat : ∀ (a : ℝ) (k : ℕ), (x ^ a) ^ k = x ^ (a * k) := fun a k => by
    rw [Real.rpow_mul hx0.le, Real.rpow_natCast]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = x ^ ((1 : ℝ) / 2) := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ xpos _
  have hs2 : s ^ 2 = x := by
    rw [hs, xnat]
    norm_num
  obtain ⟨ε₂, hε₂⟩ : ∃ ε : ℝ, ε = Cc * x ^ (-(1 / 2 : ℝ) + 2 / 1000) := ⟨_, rfl⟩
  have hε₂0 : 0 ≤ ε₂ := hε₂ ▸ mul_nonneg hCc0 (xpos _).le
  have hε₂1 : ε₂ ≤ 1 := by
    have h1 : x ^ (-(1 / 2 : ℝ) + 2 / 1000) * x ^ ((1 : ℝ) / 5) ≤ 1 := by
      rw [xm]
      exact xle1 (by norm_num)
    have h2 : x ^ (-(1 / 2 : ℝ) + 2 / 1000) * Cc ≤ x ^ (-(1 / 2 : ℝ) + 2 / 1000) * x ^ ((1 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_left (by linarith) (xpos _).le
    rw [hε₂]
    linarith
  choose Cb hCb using hFb
  set X : Fin (q + 1) → Ω → ℝ := fun i ω => max (-|Cb i|) (min |Cb i| (F i ω)) with hX
  have hXb : ∀ i, IsBoundedRealRV (X i) := by
    intro i
    refine ⟨measurable_const.max (measurable_const.min (hFm i)), |Cb i|, fun ω => ?_⟩
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le ?_ (min_le_left _ _)⟩
    have := abs_nonneg (Cb i)
    linarith
  have hXF : ∀ i, X i =ᵐ[μ] F i := by
    intro i
    filter_upwards [hCb i] with ω h
    have h2 := abs_le.1 (h.trans (le_abs_self _))
    simp only [hX]
    rw [min_eq_right h2.2, max_eq_right h2.1]
  set A' : Set Ω := toMeasurable μ A with hA'
  have hA'm : MeasurableSet A' := measurableSet_toMeasurable _ _
  have hAA' : A ⊆ A' := subset_toMeasurable _ _
  have hAe : A' =ᵐ[μ] A := R.measurableSet_event.nullMeasurableSet.toMeasurable_ae_eq
  set E : Set Ω := (toMeasurable μ (A ∩ B)ᶜ)ᶜ with hE
  have hEm : MeasurableSet E := (measurableSet_toMeasurable _ _).compl
  have hEAB : E ⊆ A ∩ B := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hEA' : E ⊆ A' := fun ω h => hAA' (hEAB h).1
  have hδ : μ.real Eᶜ ≤ 2 * Cc * x ^ (-(40 : ℝ)) := by
    have e : μ.real Eᶜ = μ.real (A ∩ B)ᶜ := by
      simp only [hE, compl_compl, Measure.real, measure_toMeasurable]
    have h1 : μ.real (A ∩ B)ᶜ ≤ μ.real (Aᶜ ∪ (A ∩ Bᶜ)) := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      by_cases h : ω ∈ A
      · exact Or.inr ⟨h, fun hB => hω ⟨h, hB⟩⟩
      · exact Or.inl h
    have h2 := measureReal_union_le (μ := μ) Aᶜ (A ∩ Bᶜ)
    have h3 : C * x ^ (-(40 : ℝ)) ≤ Cc * x ^ (-(40 : ℝ)) :=
      mul_le_mul_of_nonneg_right hCle (xpos _).le
    have h4 := R.measureReal_compl_le
    have h5 := R.measureReal_inter_compl_le
    rw [e]
    linarith
  have hδ2 : μ.real Eᶜ ≤ 1 / 2 := by
    have h1 : x ^ (-(40 : ℝ)) * x ^ ((1 : ℝ) / 5) ≤ 1 := by
      rw [xm]
      exact xle1 (by norm_num)
    have h2 : x ^ (-(40 : ℝ)) * (4 * Cc + 2) ≤ x ^ (-(40 : ℝ)) * x ^ ((1 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_left hroot (xpos _).le
    have h3 := xpos (-(40 : ℝ))
    linarith
  have hE2 : 1 / 2 ≤ μ.real E := by
    have := probReal_compl_eq_one_sub (μ := μ) hEm
    linarith
  set H : Ω → I → imaginaryQuaternions := fun ω a => s • G ω a with hH
  have hHc : ∀ (e : Fin 3) ω a, imaginaryComponent e (H ω a) = s * imaginaryComponent e (G ω a) :=
    fun e ω a => imaginaryComponent_smul _ _ _
  have hHm : ∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (H ω a) := by
    intro a e
    simp only [hHc]
    exact (hm a e).const_mul s
  have hHb : ∀ ω a e, |imaginaryComponent e (H ω a)| ≤ s * Bg := by
    intro ω a e
    rw [hHc, abs_mul, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left (hb ω a e) hs0.le
  have hP : ∀ (r : ℕ) (a : Fin r → I) (e : Fin r → Fin 3),
      |wickPairingSum fun i i' => if e i = e i' then Tc (a i) (a i') else 0| ≤ pairingCountBound r Dm := by
    intro r a e
    refine abs_wickPairingSum_le hDm1 fun i j => ?_
    split_ifs
    · have := R.abs_covariance_le (a i) (a j)
      linarith
    · simp
      linarith
  have hMs : ∀ (r : ℕ) (a : Fin r → I) (e : Fin r → Fin 3), r ≤ 16 →
      |∫ ω, A'.indicator (fun ω => ∏ i, imaginaryComponent (e i) (H ω (a i))) ω ∂μ -
        wickPairingSum fun i i' => if e i = e i' then Tc (a i) (a i') else 0| ≤ ε₂ := by
    intro r a e hr
    obtain ⟨-, hv⟩ := hM16 r a e hr
    have e1 : ∫ ω, A'.indicator (fun ω => ∏ i, imaginaryComponent (e i) (H ω (a i))) ω ∂μ =
        s ^ r * ∫ ω, A.indicator (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) ω ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hAe] with ω hω
      have hiff : ω ∈ A' ↔ ω ∈ A := Iff.of_eq hω
      by_cases h : ω ∈ A
      · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h]
        simp only [hHc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]
        simp
    have hsr : s ^ r = x ^ ((r : ℝ) / 2) := by
      rw [hs, xnat]
      congr 1
      ring
    have e2 : s ^ r * x ^ (-(r : ℝ) / 2) = 1 := by
      rw [hsr, xm]
      have : (r : ℝ) / 2 + -(r : ℝ) / 2 = 0 := by ring
      rw [this, Real.rpow_zero]
    have e3 : s ^ r * x ^ (-((r : ℝ) + 1) / 2 + 2 / 1000) = x ^ (-(1 / 2 : ℝ) + 2 / 1000) := by
      rw [hsr, xm]
      congr 1
      ring
    set v := ∫ ω, A.indicator (fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i))) ω ∂μ with hvd
    set Pr := wickPairingSum fun i i' => if e i = e i' then Tc (a i) (a i') else 0 with hPr
    rw [e1]
    have e4 : s ^ r * v - Pr = s ^ r * (v - x ^ (-(r : ℝ) / 2) * Pr) := by
      have : s ^ r * (v - x ^ (-(r : ℝ) / 2) * Pr) = s ^ r * v - (s ^ r * x ^ (-(r : ℝ) / 2)) * Pr := by ring
      rw [this, e2, one_mul]
    rw [e4, abs_mul, abs_of_pos (by positivity : 0 < s ^ r)]
    calc s ^ r * |v - x ^ (-(r : ℝ) / 2) * Pr| ≤ s ^ r * (C * x ^ (-((r : ℝ) + 1) / 2 + 2 / 1000)) :=
          mul_le_mul_of_nonneg_left hv (by positivity)
      _ = C * x ^ (-(1 / 2 : ℝ) + 2 / 1000) := by
          rw [mul_left_comm, e3]
      _ ≤ ε₂ := by
          rw [hε₂]
          exact mul_le_mul_of_nonneg_right hCle (xpos _).le
  have hε₂le : ε₂ ≤ Cc := by
    have : x ^ (-(1 / 2 : ℝ) + 2 / 1000) ≤ 1 := xle1 (by norm_num)
    rw [hε₂]
    have h2 := mul_le_mul_of_nonneg_left this hCc0
    linarith
  have hmix : ∀ (m : ℕ), m + m ≤ 16 → ∀ (c' d : I) (e : Fin 3),
      ∫ ω, A'.indicator (fun ω => imaginaryComponent e (H ω c') ^ m * imaginaryComponent e (H ω d) ^ m) ω ∂μ ≤
        pairingCountBound (m + m) Dm + Cc := by
    intro m hm16 c' d e
    have h1 := hMs (m + m) (Fin.addCases (motive := fun _ => I) (fun _ => c') (fun _ => d)) (fun _ => e) hm16
    have h2 := hP (m + m) (Fin.addCases (motive := fun _ => I) (fun _ => c') (fun _ => d)) (fun _ => e)
    have e1 : (fun ω => ∏ i : Fin (m + m), imaginaryComponent e
        (H ω (Fin.addCases (motive := fun _ => I) (fun _ => c') (fun _ => d) i))) =
        fun ω => imaginaryComponent e (H ω c') ^ m * imaginaryComponent e (H ω d) ^ m := by
      funext ω
      exact prod_addCases_const m (fun z => imaginaryComponent e (H ω z)) c' d
    rw [e1] at h1
    have h3 := (abs_le.1 h1).2
    have h4 := (abs_le.1 h2).2
    linarith
  have h8A : ∀ (c' d : I) (e : Fin 3), ∫ ω, A'.indicator
      (fun ω => imaginaryComponent e (H ω c') ^ 4 * imaginaryComponent e (H ω d) ^ 4) ω ∂μ ≤ Kq ^ 4 := by
    intro c' d e
    have h1 := hmix 4 (by norm_num) c' d e
    have h2 : Kq ≤ Kq ^ 4 := le_self_pow₀ hKq1 (by norm_num)
    linarith
  have hcd_nonneg : ∀ (m : ℕ), Even m → ∀ (c' d : I) (e : Fin 3) ω,
      0 ≤ imaginaryComponent e (H ω c') ^ m * imaginaryComponent e (H ω d) ^ m := fun m hm c' d e ω =>
    mul_nonneg (hm.pow_nonneg _) (hm.pow_nonneg _)
  have hcdb : ∀ (c' d : I) (e : Fin 3), IsBoundedRealRV
      fun ω => imaginaryComponent e (H ω c') * imaginaryComponent e (H ω d) := fun c' d e =>
    ⟨(hHm c' e).mul (hHm d e), (s * Bg) * (s * Bg), fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hHb ω c' e) (hHb ω d e) (abs_nonneg _) ((abs_nonneg _).trans (hHb ω c' e))⟩
  have h8E' : ∀ (c' d : I) (e : Fin 3), ∫ ω, E.indicator
      (fun ω => imaginaryComponent e (H ω c') ^ 4 * imaginaryComponent e (H ω d) ^ 4) ω ∂μ ≤ Kq ^ 4 := by
    intro c' d e
    have hb4 : IsBoundedRealRV
        fun ω => imaginaryComponent e (H ω c') ^ 4 * imaginaryComponent e (H ω d) ^ 4 := by
      have := isBoundedRealRV_pow (hcdb c' d e) 4
      have e1 : (fun ω => (imaginaryComponent e (H ω c') * imaginaryComponent e (H ω d)) ^ 4) =
          fun ω => imaginaryComponent e (H ω c') ^ 4 * imaginaryComponent e (H ω d) ^ 4 := by
        funext ω
        rw [mul_pow]
      rwa [e1] at this
    refine le_trans (integral_mono (integrable_of_isBoundedRealRV μ (isBoundedRealRV_indicator hEm hb4))
      (integrable_of_isBoundedRealRV μ (isBoundedRealRV_indicator hA'm hb4)) ?_) (h8A c' d e)
    exact fun ω => Set.indicator_le_indicator_of_subset hEA' (fun ω => hcd_nonneg 4 (by decide) c' d e ω) ω
  have hx20 : (x ^ (20 : ℝ))⁻¹ = x ^ (-(20 : ℝ)) := (Real.rpow_neg hx0.le _).symm
  have hx2040 : x ^ (20 : ℝ) * x ^ (-(40 : ℝ)) = x ^ (-(20 : ℝ)) := by
    rw [xm]
    norm_num
  have hδ20 : x ^ (20 : ℝ) * μ.real Eᶜ ≤ 2 * Cc * x ^ (-(20 : ℝ)) := by
    calc x ^ (20 : ℝ) * μ.real Eᶜ ≤ x ^ (20 : ℝ) * (2 * Cc * x ^ (-(40 : ℝ))) :=
          mul_le_mul_of_nonneg_left hδ (xpos _).le
      _ = 2 * Cc * (x ^ (20 : ℝ) * x ^ (-(40 : ℝ))) := by ring
      _ = _ := by rw [hx2040]
  obtain ⟨τ', hτ'⟩ : ∃ t : ℝ, t = Kt' * x ^ (-(5 : ℝ)) := ⟨_, rfl⟩
  have hτ'0 : 0 ≤ τ' := hτ' ▸ mul_nonneg hKt'0 (xpos _).le
  have h8E : ∀ (c' d : I) (e : Fin 3), ∫ ω, (A' \ E).indicator
      (fun ω => imaginaryComponent e (H ω c') ^ 4 * imaginaryComponent e (H ω d) ^ 4) ω ∂μ ≤ τ' ^ 4 := by
    intro c' d e
    have hfb := isBoundedRealRV_indicator hA'm (hcdb c' d e)
    have ht := integral_indicator_pow_four_le μ hEm.compl hfb (xpos (20 : ℝ))
    have e1 : ∫ ω, (A' \ E).indicator
        (fun ω => imaginaryComponent e (H ω c') ^ 4 * imaginaryComponent e (H ω d) ^ 4) ω ∂μ =
        ∫ ω, Eᶜ.indicator (fun ω => (A'.indicator
          (fun ω => imaginaryComponent e (H ω c') * imaginaryComponent e (H ω d)) ω) ^ 4) ω ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      by_cases h1 : ω ∈ E
      · simp [h1]
      · by_cases h2 : ω ∈ A'
        · simp [h1, h2, mul_pow]
        · simp [h1, h2]
    have e2 : ∫ ω, (A'.indicator
        (fun ω => imaginaryComponent e (H ω c') * imaginaryComponent e (H ω d)) ω) ^ 8 ∂μ =
        ∫ ω, A'.indicator
          (fun ω => imaginaryComponent e (H ω c') ^ 8 * imaginaryComponent e (H ω d) ^ 8) ω ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      by_cases h2 : ω ∈ A'
      · simp [h2, mul_pow]
      · simp [h2]
    have h16 := hmix 8 (by norm_num) c' d e
    rw [e1]
    refine ht.trans ?_
    rw [e2]
    have h3 : (∫ ω, A'.indicator
        (fun ω => imaginaryComponent e (H ω c') ^ 8 * imaginaryComponent e (H ω d) ^ 8) ω ∂μ) / x ^ (20 : ℝ) ≤
        K16 * x ^ (-(20 : ℝ)) := by
      rw [div_eq_mul_inv, hx20]
      refine mul_le_mul_of_nonneg_right ?_ (xpos _).le
      linarith
    have h4 : (x ^ (-(5 : ℝ))) ^ 4 = x ^ (-(20 : ℝ)) := by
      rw [xnat]
      norm_num
    have h5 : Kt' ≤ Kt' ^ 4 := le_self_pow₀ hKt'1 (by norm_num)
    have h6 : τ' ^ 4 = Kt' ^ 4 * x ^ (-(20 : ℝ)) := by
      rw [hτ', mul_pow, h4]
    have hp := xpos (-(20 : ℝ))
    have h7 : Kt' * x ^ (-(20 : ℝ)) ≤ Kt' ^ 4 * x ^ (-(20 : ℝ)) := mul_le_mul_of_nonneg_right h5 hp.le
    have h8 : (Cc + K16) * x ^ (-(20 : ℝ)) ≤ Kt' * x ^ (-(20 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hp.le
    rw [h6]
    have h9 := mul_nonneg hK16_0 hp.le
    linarith
  obtain ⟨Kap, hKap⟩ : ∃ K : ℝ, K = K1 * x ^ ((1 : ℝ) / 20) := ⟨_, rfl⟩
  have hKap0 : 0 ≤ Kap := hKap ▸ mul_nonneg hK1_0 (xpos _).le
  have hn4 : n ^ 4 ≤ x ^ ((4 : ℝ) / 90) := by
    have h1 := pow_le_pow_left₀ (by linarith : 0 ≤ n) hn 4
    rw [xnat] at h1
    refine h1.trans (le_of_eq ?_)
    norm_num
  have hsize : ∀ i, ∑ a, ∑ b, |κ i a b| ≤ Kap := by
    intro i
    have hL := log_pow_le_rpow hx1
    have hL0 : 0 ≤ Real.log x ^ 24 := pow_nonneg (Real.log_nonneg hx1) _
    have hn40 : 0 ≤ n ^ 4 := by positivity
    calc ∑ a, ∑ b, |κ i a b| ≤ C * n ^ 4 * Real.log x ^ 24 := R.kernel_sum_abs_le i
      _ ≤ Cc * n ^ 4 * Real.log x ^ 24 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hn40) hL0
      _ ≤ Cc * x ^ ((4 : ℝ) / 90) * (logPowerConst * x ^ ((24 : ℝ) / 5000)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hn4 hCc0) hL hL0 ?_
          exact mul_nonneg hCc0 (xpos _).le
      _ = (Cc * logPowerConst) * (x ^ ((4 : ℝ) / 90) * x ^ ((24 : ℝ) / 5000)) := by ring
      _ ≤ (Cc * logPowerConst) * x ^ ((1 : ℝ) / 20) := by
          rw [xm]
          exact mul_le_mul_of_nonneg_left (xp (by norm_num)) (mul_nonneg hCc0 logPowerConst_nonneg)
      _ ≤ Kap := by
          rw [hKap, hK1]
          exact mul_le_mul_of_nonneg_right (by linarith) (xpos _).le
  obtain ⟨ρ, hρ⟩ : ∃ r : ℝ, r = x * (|D| * n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000)) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    exact mul_nonneg hx0.le (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) (xpos _).le)
  have hQ : ∀ (i : Fin (q + 1)) ω, quadraticForm (κ i) (H ω) = x * quadraticForm (κ i) (G ω) := by
    intro i ω
    have : H ω = fun a => s • G ω a := rfl
    rw [this, quadraticForm_smul, hs2]
  have hnear : ∀ i, ∫ ω, E.indicator
      (fun ω => (x * (X i ω + -c i) - quadraticForm (κ i) (H ω)) ^ 4) ω ∂μ ≤ ρ ^ 4 := by
    intro i
    have hQm : Measurable fun ω => quadraticForm (κ i) (G ω) :=
      (isBoundedRealRV_quadraticForm (κ i) G hm hb).measurable
    obtain ⟨B4, hB4d⟩ : ∃ b : ℝ, b = (D * n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000)) ^ (2 * 2) := ⟨_, rfl⟩
    have hB4 : 0 ≤ B4 := by
      rw [hB4d]
      exact Even.pow_nonneg (by decide) _
    obtain ⟨g1, hg1⟩ : ∃ g : Ω → ℝ, g = E.indicator
      (fun ω => |F i ω - c i - quadraticForm (κ i) (G ω)| ^ (2 * 2)) := ⟨_, rfl⟩
    have hg1m : Measurable g1 := by
      rw [hg1]
      exact ((continuous_abs.measurable.comp (((hFm i).sub_const (c i)).sub hQm)).pow_const _).indicator hEm
    have hg1n : ∀ ω, 0 ≤ g1 ω := fun ω => by
      rw [hg1]
      exact Set.indicator_nonneg (fun _ _ => pow_nonneg (abs_nonneg _) _) _
    have hl : ∫⁻ ω, ENNReal.ofReal (g1 ω) ∂μ ≤ ENNReal.ofReal B4 := by
      rw [hB4d]
      refine le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_) (R.lintegral_deviation_le i)
      rw [hg1]
      exact Set.indicator_le_indicator_of_subset hEAB (fun _ => pow_nonneg (abs_nonneg _) _) ω
    have hint : ∫ ω, g1 ω ∂μ ≤ B4 := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg1n) hg1m.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hB4 hl
    have e1 : ∫ ω, E.indicator (fun ω => (x * (X i ω + -c i) - quadraticForm (κ i) (H ω)) ^ 4) ω ∂μ =
        ∫ ω, x ^ 4 * g1 ω ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hXF i] with ω hω
      rw [hg1]
      by_cases h : ω ∈ E
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hω, hQ]
        have : (2 * 2 : ℕ) = 4 := by norm_num
        rw [this, Even.pow_abs (by decide)]
        ring
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
        simp
    rw [e1, integral_const_mul]
    have e2 : ρ ^ 4 = x ^ 4 * B4 := by
      rw [hρ, hB4d, mul_pow]
      congr 1
      have : (2 * 2 : ℕ) = 4 := by norm_num
      rw [this, mul_assoc (|D|), mul_assoc (D), mul_pow, mul_pow (D), Even.pow_abs (by decide)]
    rw [e2]
    exact mul_le_mul_of_nonneg_left hint (pow_nonneg hx0.le _)
  obtain ⟨τ, hτ⟩ : ∃ t : ℝ, t = Kt * x ^ (-(1 : ℝ)) := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := hτ ▸ mul_nonneg (by linarith) (xpos _).le
  have hx2 : x ≤ x ^ 2 := le_self_pow₀ hx1 (by norm_num)
  have hρx : ρ ≤ |D| * x ^ 2 := by
    have h1 : x * (n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000)) ≤ x ^ 2 := by
      have h2 : n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000) ≤ x ^ ((4 : ℝ) / 90) * x ^ (-(3 / 2 : ℝ) + 6 / 1000) :=
        mul_le_mul_of_nonneg_right hn4 (xpos _).le
      have h3 : x ^ ((4 : ℝ) / 90) * x ^ (-(3 / 2 : ℝ) + 6 / 1000) ≤ 1 := by
        rw [xm]
        exact xle1 (by norm_num)
      have h4 : n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000) ≤ 1 := h2.trans h3
      calc _ ≤ x * 1 := mul_le_mul_of_nonneg_left h4 hx0.le
        _ ≤ x ^ 2 := by linarith
    calc ρ = |D| * (x * (n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000))) := by rw [hρ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have htail : ∀ i, ∫ ω, Eᶜ.indicator (fun ω => (x * (X i ω + -c i)) ^ 4) ω ∂μ ≤ τ ^ 4 := by
    intro i
    obtain ⟨Dshift, hD⟩ : ∃ Dshift : ℝ, Dshift = x * (κ₀ i - c i) := ⟨_, rfl⟩
    have hYb : IsBoundedRealRV fun ω => x * (X i ω + -c i) :=
      isBoundedRealRV_const_mul x (isBoundedRealRV_add (hXb i) (isBoundedRealRV_const _))
    have hWb : IsBoundedRealRV fun ω => x * (X i ω + -κ₀ i) :=
      isBoundedRealRV_const_mul x (isBoundedRealRV_add (hXb i) (isBoundedRealRV_const _))
    have hYW : ∀ ω, x * (X i ω + -c i) = x * (X i ω + -κ₀ i) + Dshift := fun ω => by rw [hD]; ring
    have hWmom : ∀ r : ℕ, 1 ≤ r →
        ∫ ω, (x * (X i ω + -κ₀ i)) ^ (2 * r) ∂μ ≤ (x * (|Cq r| * x)) ^ (2 * r) := by
      intro r hr
      have e1 : ∫ ω, (x * (X i ω + -κ₀ i)) ^ (2 * r) ∂μ =
          ∫ ω, x ^ (2 * r) * |F i ω - κ₀ i| ^ (2 * r) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hXF i] with ω hω
        rw [hω, mul_pow, Even.pow_abs (even_two_mul r), sub_eq_add_neg]
      rw [e1, integral_const_mul, mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hx0.le _)
      refine (hFmom i r hr).trans ?_
      have h1 : (Cq r * w) ^ (2 * r) = (|Cq r| * w) ^ (2 * r) := by
        rw [mul_pow, mul_pow, Even.pow_abs (even_two_mul r)]
      rw [h1]
      exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hw0) (mul_le_mul_of_nonneg_left hwx (abs_nonneg _)) _
    have hW4 := hWmom 2 (by norm_num)
    have hW8 := hWmom 4 (by norm_num)
    have p1 : IsBoundedRealRV
        (E.indicator fun ω => x * (X i ω + -c i) - quadraticForm (κ i) (H ω)) := by
      refine isBoundedRealRV_indicator hEm ?_
      have := isBoundedRealRV_add hYb (isBoundedRealRV_const_mul (-1) (isBoundedRealRV_quadraticForm (κ i) H hHm hHb))
      have e : (fun ω => x * (X i ω + -c i) - quadraticForm (κ i) (H ω)) =
          fun ω => x * (X i ω + -c i) + -1 * quadraticForm (κ i) (H ω) := by funext ω; ring
      rw [e]; exact this
    have p2 : IsBoundedRealRV (E.indicator fun ω => -1 * (x * (X i ω + -κ₀ i))) :=
      isBoundedRealRV_indicator hEm (isBoundedRealRV_const_mul _ hWb)
    have p3 : IsBoundedRealRV (E.indicator fun ω => quadraticForm (κ i) (H ω)) :=
      isBoundedRealRV_indicator hEm (isBoundedRealRV_quadraticForm (κ i) H hHm hHb)
    have n1 : (eLpNorm (E.indicator fun ω => x * (X i ω + -c i) - quadraticForm (κ i) (H ω)) 4 μ).toReal ≤ ρ := by
      refine eLpNorm_four_le μ p1 hρ0 ((le_of_eq ?_).trans (hnear i))
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      by_cases h : ω ∈ E <;> simp [h]
    have n2 : (eLpNorm (E.indicator fun ω => -1 * (x * (X i ω + -κ₀ i))) 4 μ).toReal ≤ x * (|Cq 2| * x) := by
      refine eLpNorm_four_le μ p2 (mul_nonneg hx0.le (mul_nonneg (abs_nonneg _) hx0.le)) ?_
      refine le_trans ?_ hW4
      refine integral_mono (integrable_of_isBoundedRealRV μ (isBoundedRealRV_pow p2 4))
        (integrable_of_isBoundedRealRV μ (isBoundedRealRV_pow hWb (2 * 2))) fun ω => ?_
      by_cases h : ω ∈ E
      · simp only [Set.indicator_of_mem h]
        have : (2 * 2 : ℕ) = 4 := by norm_num
        rw [this]
        exact le_of_eq (by ring)
      · simp only [Set.indicator_of_notMem h]
        have : (0 : ℝ) ^ 4 = 0 := by norm_num
        rw [this]
        exact Even.pow_nonneg (by decide) _
    have n3 : (eLpNorm (E.indicator fun ω => quadraticForm (κ i) (H ω)) 4 μ).toReal ≤ 3 / 2 * Kap * Kq :=
      (eLpNorm_four_indicator_quadraticForm_le μ hEm (κ i) H hHm hHb hKq0 h8E').trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsize i) (by norm_num)) hKq0)
    have hDe : (E.indicator fun _ => Dshift) = fun ω =>
        ((E.indicator fun ω => x * (X i ω + -c i) - quadraticForm (κ i) (H ω)) ω +
          (E.indicator fun ω => -1 * (x * (X i ω + -κ₀ i))) ω) +
          (E.indicator fun ω => quadraticForm (κ i) (H ω)) ω := by
      funext ω
      by_cases h : ω ∈ E
      · simp only [Set.indicator_of_mem h]
        rw [hD]
        ring
      · simp only [Set.indicator_of_notMem h]
        ring
    have hDn : |Dshift| ≤ Kd * x ^ 2 := by
      have h1 := abs_le_two_mul_eLpNorm_four_indicator μ hEm hE2 Dshift
      rw [hDe] at h1
      have h2 := eLpNorm_four_add_le μ (isBoundedRealRV_add p1 p2) p3
      have h3 := eLpNorm_four_add_le μ p1 p2
      have h4 : Kap ≤ K1 * x ^ 2 := by
        rw [hKap]
        refine mul_le_mul_of_nonneg_left ?_ hK1_0
        calc x ^ ((1 : ℝ) / 20) ≤ x ^ (1 : ℝ) := xp (by norm_num)
          _ = x := Real.rpow_one x
          _ ≤ x ^ 2 := hx2
      have h5 : 3 / 2 * Kap * Kq ≤ 3 / 2 * K1 * Kq * x ^ 2 := by
        have := mul_le_mul_of_nonneg_right h4 hKq0
        linarith
      have h6 : x * (|Cq 2| * x) = |Cq 2| * x ^ 2 := by ring
      have h7 : Kd * x ^ 2 = 2 * (|D| * x ^ 2 + |Cq 2| * x ^ 2 + 3 / 2 * K1 * Kq * x ^ 2) := by
        rw [hKd]
        ring
      rw [h7]
      linarith
    have hD8 : Dshift ^ 8 ≤ Kd ^ 8 * x ^ 16 := by
      have h1 : Dshift ^ 8 = |Dshift| ^ 8 := (Even.pow_abs (by decide) _).symm
      have h2 : (Kd * x ^ 2) ^ 8 = Kd ^ 8 * x ^ 16 := by ring
      rw [h1, ← h2]
      exact pow_le_pow_left₀ (abs_nonneg _) hDn 8
    have hY8 : ∫ ω, (x * (X i ω + -c i)) ^ 8 ∂μ ≤ Ky * x ^ 16 := by
      have hW8' : ∫ ω, (x * (X i ω + -κ₀ i)) ^ 8 ∂μ ≤ |Cq 4| ^ 8 * x ^ 16 := by
        refine hW8.trans (le_of_eq ?_)
        have : (2 * 4 : ℕ) = 8 := by norm_num
        rw [this]
        ring
      have i1 : Integrable (fun ω => (x * (X i ω + -κ₀ i)) ^ 8) μ :=
        integrable_of_isBoundedRealRV μ (isBoundedRealRV_pow hWb 8)
      have h1 : ∫ ω, (x * (X i ω + -c i)) ^ 8 ∂μ ≤ ∫ ω, 128 * ((x * (X i ω + -κ₀ i)) ^ 8 + Dshift ^ 8) ∂μ := by
        refine integral_mono (integrable_of_isBoundedRealRV μ (isBoundedRealRV_pow hYb 8))
          ((i1.add (integrable_const _)).const_mul _) fun ω => ?_
        simp only [hYW]
        exact add_pow_eight_le _ _
      refine h1.trans ?_
      rw [integral_const_mul, integral_add i1 (integrable_const _), integral_const, probReal_univ, one_smul, hKy]
      have h2 : 128 * (∫ ω, (x * (X i ω + -κ₀ i)) ^ 8 ∂μ + Dshift ^ 8) ≤
          128 * (|Cq 4| ^ 8 * x ^ 16 + Kd ^ 8 * x ^ 16) := by linarith
      refine h2.trans (le_of_eq ?_)
      ring
    have ht := integral_indicator_pow_four_le μ hEm.compl hYb (xpos (20 : ℝ))
    refine ht.trans ?_
    have hpx : x ^ 16 * x ^ (-(20 : ℝ)) = x ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_natCast x 16, xm]
      norm_num
    have h3 : (∫ ω, (x * (X i ω + -c i)) ^ 8 ∂μ) / x ^ (20 : ℝ) ≤ Ky * x ^ (-(4 : ℝ)) := by
      rw [div_eq_mul_inv, hx20, ← hpx, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hY8 (xpos _).le
    have h4 : (x ^ (-(1 : ℝ))) ^ 4 = x ^ (-(4 : ℝ)) := by
      rw [xnat]
      norm_num
    have h5 : Kt ≤ Kt ^ 4 := le_self_pow₀ hKt1 (by norm_num)
    have h6 : τ ^ 4 = Kt ^ 4 * x ^ (-(4 : ℝ)) := by
      rw [hτ, mul_pow, h4]
    have hp := xpos (-(4 : ℝ))
    have h7 : Kt * x ^ (-(4 : ℝ)) ≤ Kt ^ 4 * x ^ (-(4 : ℝ)) := mul_le_mul_of_nonneg_right h5 hp.le
    have h8 : (Cc + Ky) * x ^ (-(4 : ℝ)) ≤ Kt * x ^ (-(4 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hp.le
    have h9 : x ^ (-(20 : ℝ)) ≤ x ^ (-(4 : ℝ)) := xp (by norm_num)
    have h10 := mul_le_mul_of_nonneg_left h9 hCc0
    have h11 := mul_nonneg hKy0 hp.le
    rw [h6]
    linarith
  have hcore := hCg Ω μ A' E I H Tc ε₂ (s * Bg) κ X x (fun i => -c i) ρ τ τ' Kq Kap hA'm hEm hEA'
    R.kernel_isSymm hHm hHb R.covariance_isSymm (fun a b => by have := R.abs_covariance_le a b; linarith)
    hε₂0 hε₂1 (fun r a e hr => hMs r a e (by omega)) hXb hρ0 hτ0 hτ'0 hKq0 hKap0 hsize hnear htail h8A h8E
  have hcum : mixedCumulant μ X = mixedCumulant μ F := mixedCumulant_congr_ae hXF
  rw [hcum] at hcore
  refine hcore.trans ?_
  have hU1 : 1 ≤ x ^ ((1 : ℝ) / 20) := x1le (by norm_num)
  have hE1 : x ^ (-(2 / 5 : ℝ)) ≤ 1 := xle1 (by norm_num)
  have hE0 := xpos (-(2 / 5 : ℝ))
  have hU0 := xpos ((1 : ℝ) / 20)
  have hρE : ρ ≤ |D| * x ^ (-(2 / 5 : ℝ)) := by
    have h2 : n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000) ≤ x ^ ((4 : ℝ) / 90) * x ^ (-(3 / 2 : ℝ) + 6 / 1000) :=
      mul_le_mul_of_nonneg_right hn4 (xpos _).le
    have h3 : x * (x ^ ((4 : ℝ) / 90) * x ^ (-(3 / 2 : ℝ) + 6 / 1000)) ≤ x ^ (-(2 / 5 : ℝ)) := by
      rw [xm]
      nth_rewrite 1 [← Real.rpow_one x]
      rw [xm]
      exact xp (by norm_num)
    calc ρ = |D| * (x * (n ^ 4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000))) := by rw [hρ]; ring
      _ ≤ |D| * (x * (x ^ ((4 : ℝ) / 90) * x ^ (-(3 / 2 : ℝ) + 6 / 1000))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hx0.le) (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  have hτE : τ ≤ Kt * x ^ (-(2 / 5 : ℝ)) := by
    rw [hτ]
    exact mul_le_mul_of_nonneg_left (xp (by norm_num)) (by linarith)
  have hKτ : 3 / 2 * Kap * τ' ≤ 3 / 2 * K1 * Kt' * x ^ (-(2 / 5 : ℝ)) := by
    have h1 : x ^ ((1 : ℝ) / 20) * x ^ (-(5 : ℝ)) ≤ x ^ (-(2 / 5 : ℝ)) := by
      rw [xm]
      exact xp (by norm_num)
    calc 3 / 2 * Kap * τ' = 3 / 2 * K1 * Kt' * (x ^ ((1 : ℝ) / 20) * x ^ (-(5 : ℝ))) := by
          rw [hKap, hτ']
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hKK'
  obtain ⟨ε₁, hε₁⟩ : ∃ e : ℝ, e = ρ + τ + 3 / 2 * Kap * τ' := ⟨_, rfl⟩
  rw [← hε₁]
  have hε₁0 : 0 ≤ ε₁ := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hKap0) hτ'0
    rw [hε₁]
    linarith
  have hε₁E : ε₁ ≤ K7 * x ^ (-(2 / 5 : ℝ)) := by
    rw [hε₁, hK7, add_mul, add_mul]
    linarith
  have hA1 : ε₁ + 3 / 2 * Kap * Kq ≤ K9 * x ^ ((1 : ℝ) / 20) := by
    have h1 : K7 * x ^ (-(2 / 5 : ℝ)) ≤ K7 * x ^ ((1 : ℝ) / 20) :=
      mul_le_mul_of_nonneg_left (hE1.trans hU1) hK7_0
    have h2 : 3 / 2 * Kap * Kq = 3 / 2 * K1 * Kq * x ^ ((1 : ℝ) / 20) := by
      rw [hKap]
      ring
    rw [h2, hK9, add_mul, add_mul]
    linarith
  have hV1 : 1 ≤ K9 * x ^ ((1 : ℝ) / 20) := by
    have := mul_le_mul hK9_1 hU1 (by norm_num) (by linarith)
    linarith
  have hA0 : 0 ≤ ε₁ + 3 / 2 * Kap * Kq :=
    add_nonneg hε₁0 (mul_nonneg (mul_nonneg (by norm_num) hKap0) hKq0)
  have hAq : (ε₁ + 3 / 2 * Kap * Kq) ^ q ≤ K9 ^ 3 * x ^ ((3 : ℝ) / 20) := by
    calc (ε₁ + 3 / 2 * Kap * Kq) ^ q ≤ (K9 * x ^ ((1 : ℝ) / 20)) ^ q := pow_le_pow_left₀ hA0 hA1 q
      _ ≤ (K9 * x ^ ((1 : ℝ) / 20)) ^ 3 := pow_le_pow_right₀ hV1 hq3
      _ = K9 ^ 3 * x ^ ((3 : ℝ) / 20) := by
        rw [mul_pow, xnat]
        norm_num
  have ht1 : 26 * ((q : ℝ) + 1) * (ε₁ * (ε₁ + 3 / 2 * Kap * Kq) ^ q) ≤
      (104 * K7 * K9 ^ 3) * x ^ (-(1 / 5 : ℝ)) := by
    have hq4 : (q : ℝ) + 1 ≤ 4 := by
      have : (q : ℝ) ≤ 3 := by exact_mod_cast hq3
      linarith
    have h1 : ε₁ * (ε₁ + 3 / 2 * Kap * Kq) ^ q ≤
        (K7 * x ^ (-(2 / 5 : ℝ))) * (K9 ^ 3 * x ^ ((3 : ℝ) / 20)) :=
      mul_le_mul hε₁E hAq (pow_nonneg hA0 _) (mul_nonneg hK7_0 hE0.le)
    have h2 : (K7 * x ^ (-(2 / 5 : ℝ))) * (K9 ^ 3 * x ^ ((3 : ℝ) / 20)) ≤
        K7 * K9 ^ 3 * x ^ (-(1 / 5 : ℝ)) := by
      have h3 : x ^ (-(2 / 5 : ℝ)) * x ^ ((3 : ℝ) / 20) ≤ x ^ (-(1 / 5 : ℝ)) := by
        rw [xm]
        exact xp (by norm_num)
      calc _ = K7 * K9 ^ 3 * (x ^ (-(2 / 5 : ℝ)) * x ^ ((3 : ℝ) / 20)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (mul_nonneg hK7_0 (pow_nonneg (by linarith) _))
    have h4 : 0 ≤ ε₁ * (ε₁ + 3 / 2 * Kap * Kq) ^ q := mul_nonneg hε₁0 (pow_nonneg hA0 _)
    calc _ ≤ 26 * 4 * (ε₁ * (ε₁ + 3 / 2 * Kap * Kq) ^ q) :=
          mul_le_mul_of_nonneg_right (by linarith) h4
      _ ≤ 26 * 4 * (K7 * K9 ^ 3 * x ^ (-(1 / 5 : ℝ))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by norm_num)
      _ = _ := by ring
  have ht2 : Cg * Kap ^ (q + 1) * ε₂ ≤ (|Cg| * K1 ^ 4 * Cc) * x ^ (-(1 / 5 : ℝ)) := by
    have hK1U : 1 ≤ K1 * x ^ ((1 : ℝ) / 20) := by
      have := mul_le_mul hK1_1 hU1 (by norm_num) hK1_0
      linarith
    have h1 : Kap ^ (q + 1) ≤ K1 ^ 4 * x ^ ((1 : ℝ) / 5) := by
      rw [hKap]
      calc (K1 * x ^ ((1 : ℝ) / 20)) ^ (q + 1) ≤ (K1 * x ^ ((1 : ℝ) / 20)) ^ 4 :=
            pow_le_pow_right₀ hK1U (by omega)
        _ = _ := by
          rw [mul_pow, xnat]
          norm_num
    have h2 : x ^ ((1 : ℝ) / 5) * x ^ (-(1 / 2 : ℝ) + 2 / 1000) ≤ x ^ (-(1 / 5 : ℝ)) := by
      rw [xm]
      exact xp (by norm_num)
    have h3 : Kap ^ (q + 1) * ε₂ ≤ K1 ^ 4 * Cc * x ^ (-(1 / 5 : ℝ)) := by
      calc Kap ^ (q + 1) * ε₂ ≤ (K1 ^ 4 * x ^ ((1 : ℝ) / 5)) * ε₂ :=
            mul_le_mul_of_nonneg_right h1 hε₂0
        _ = K1 ^ 4 * Cc * (x ^ ((1 : ℝ) / 5) * x ^ (-(1 / 2 : ℝ) + 2 / 1000)) := by
            rw [hε₂]
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (mul_nonneg (pow_nonneg hK1_0 _) hCc0)
    have h4 : 0 ≤ Kap ^ (q + 1) * ε₂ := mul_nonneg (pow_nonneg hKap0 _) hε₂0
    calc Cg * Kap ^ (q + 1) * ε₂ = Cg * (Kap ^ (q + 1) * ε₂) := by ring
      _ ≤ |Cg| * (Kap ^ (q + 1) * ε₂) := mul_le_mul_of_nonneg_right (le_abs_self _) h4
      _ ≤ |Cg| * (K1 ^ 4 * Cc * x ^ (-(1 / 5 : ℝ))) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = _ := by ring
  rw [add_mul]
  exact add_le_add ht1 ht2
private theorem mixedCumulant_of_quadraticFormApproximation (hT : MixedCumulantFacts.MixedCumulantProperties)
    (hCQ : quadraticFormCumulantsStatement) (q : ℕ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) (Cr Cq : ℕ → ℝ) (C : ℝ) :
    ∃ C' x₁ : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Type) [Fintype I]
      (F : Fin (q + 1) → Ω → ℝ) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω) (κ : Fin (q + 1) → Matrix I I ℝ)
      (Tc : Matrix I I ℝ) (c κ₀ : Fin (q + 1) → ℝ) (x n w Bg : ℝ),
      x₁ ≤ x → 1 ≤ n → n ≤ x ^ ((1 : ℝ) / 90) → 0 ≤ w → w ≤ x →
      QuadraticFormApproximation μ F G A B κ Tc c x n C 40 Bg Cr →
      (∀ i, Measurable (F i)) → (∀ i, ∃ Cb : ℝ, ∀ᵐ ω ∂μ, |F i ω| ≤ Cb) →
      (∀ i (r : ℕ), 1 ≤ r → ∫ ω, |F i ω - κ₀ i| ^ (2 * r) ∂μ ≤ (Cq r * w) ^ (2 * r)) →
      ‖(x : ℂ) ^ (q + 1) * mixedCumulant μ F - ((cyclicTraceSum κ Tc : ℝ) : ℂ)‖ ≤
        C' * x ^ (-(1 / 5 : ℝ)) := by
  obtain ⟨C', x₁, h⟩ := mixedCumulant_of_fourthMomentApproximation hT hCQ q hq1 hq3 (Cr 2) Cq C
  refine ⟨C', x₁, ?_⟩
  intro Ω _ μ _ I _ F G A B κ Tc c κ₀ x n w Bg hx hn1 hn hw0 hwx R hFm hFb hFmom
  exact h Ω μ I F G A B κ Tc c κ₀ x n w Bg hx hn1 hn hw0 hwx
    ⟨R.measurableSet_event, R.measurable_component, R.abs_component_le, R.gaussian_moments,
      R.covariance_isSymm, R.abs_covariance_le, R.kernel_isSymm, R.kernel_sum_abs_le,
      fun i => R.lintegral_deviation_le i 2 (by norm_num),
      R.measureReal_compl_le, R.measureReal_inter_compl_le⟩ hFm hFb hFmom
end Approximation
theorem cumulantOfQuadraticApproximationStatement_holds (hT : MixedCumulantFacts.MixedCumulantProperties)
    (hCQ : quadraticFormCumulantsStatement) : cumulantOfQuadraticApproximationStatement :=
  fun q Cr Cq C hq1 hq3 => mixedCumulant_of_quadraticFormApproximation hT hCQ q hq1 hq3 Cr Cq C
end YangMills.Construction.FourPointCondition
end
