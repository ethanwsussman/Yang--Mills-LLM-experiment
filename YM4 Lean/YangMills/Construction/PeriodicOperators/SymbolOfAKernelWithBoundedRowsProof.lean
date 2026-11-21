import YangMills.Construction.PeriodicOperators.SymbolOfAKernelWithBoundedRows
import YangMills.Construction.Towers.BoundsOfTheSymbolsOfTheAveragesProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BoundedExpansionSymbol
open Quotients (finiteNormSpace)
theorem sum_finset_rows_le_mul_tsum {J J' : Type} (s : J' → Finset J) (W : J → ℝ)
    (hW : ∀ i, 0 ≤ W i) (hs : Summable W) (m : ℕ) (hm : ∀ i, {j | i ∈ s j}.encard ≤ m)
    (S : Finset J') :
    ∑ j ∈ S, ∑ i ∈ s j, W i ≤ m * ∑' i, W i := by
  classical
  set U := S.biUnion s with hU
  have h1 : ∀ j ∈ S, ∑ i ∈ s j, W i = ∑ i ∈ U, if i ∈ s j then W i else 0 := by
    intro j hj
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem s hj)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ i ∈ U, ∑ j ∈ S, (if i ∈ s j then W i else 0) ≤ m * W i := by
    intro i _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((S.filter fun j => i ∈ s j).card : ℕ∞) ≤ m := by
      rw [← Set.encard_coe_eq_coe_finsetCard]
      refine le_trans (Set.encard_le_encard ?_) (hm i)
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hc' : (S.filter fun j => i ∈ s j).card ≤ m := by exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc') (hW i)
  calc ∑ i ∈ U, ∑ j ∈ S, (if i ∈ s j then W i else 0) ≤ ∑ i ∈ U, m * W i :=
        Finset.sum_le_sum h2
    _ = m * ∑ i ∈ U, W i := by rw [Finset.mul_sum]
    _ ≤ m * ∑' i, W i :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum U fun i _ => hW i) (Nat.cast_nonneg m)
theorem norm_cexp_bilinDot_le (θ v : InfiniteLattice.AmbientSpace) (r : ℝ)
    (hv : ∀ μ, |v μ| ≤ r) :
    ‖Complex.exp (bilinDot (toComplexVec θ) (toComplexVec v))‖ ≤
      Real.exp (r * ∑ μ, |θ μ|) := by
  have hdot : bilinDot (toComplexVec θ) (toComplexVec v) = ((∑ μ, θ μ * v μ : ℝ) : ℂ) := by
    simp [bilinDot, toComplexVec]
  rw [hdot, Complex.norm_exp, Complex.ofReal_re]
  apply Real.exp_le_exp.mpr
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  calc θ μ * v μ ≤ |θ μ * v μ| := le_abs_self _
    _ = |θ μ| * |v μ| := abs_mul _ _
    _ ≤ |θ μ| * r := mul_le_mul_of_nonneg_left (hv μ) (abs_nonneg _)
    _ = r * |θ μ| := mul_comm _ _
theorem weighted_sq_applyKernel_le {I I' : PeriodicData} (hI : IsPeriodic I)
    {T : I'.Carrier → I.Carrier → ℂ} {β : ℝ} (hβ : 0 ≤ β)
    (hT : Tower.SmoothingContraction.OpNormLE I I' T β)
    {h : I.Carrier → ℂ} (hh : h ∈ finiteNormSpace I) :
    ∑' ι', I'.weightOf ι' * ‖applyKernel T h ι'‖ ^ 2 ≤
      β ^ 2 * ∑' ι, I.weightOf ι * ‖h ι‖ ^ 2 := by
  have hw : ∀ ι, 0 < I.weightOf ι := fun ι => hI.weight_pos _
  have hsum : Summable fun ι => I.weightOf ι * ‖h ι‖ ^ 2 := summable_abs_iff.mp hh
  have hnn : ∀ ι, 0 ≤ I.weightOf ι * ‖h ι‖ ^ 2 := fun ι => by
    have := (hw ι).le
    positivity
  set A := ∑' ι, I.weightOf ι * ‖h ι‖ ^ 2 with hA
  have hA0 : 0 ≤ A := tsum_nonneg hnn
  rcases hA0.eq_or_lt with hz | hpos
  · have hs0 : HasSum (fun ι => I.weightOf ι * ‖h ι‖ ^ 2) 0 := by
      have := hsum.hasSum
      rwa [← hA, ← hz] at this
    have hz' := (hasSum_zero_iff_of_nonneg hnn).mp hs0
    have h0 : ∀ ι, h ι = 0 := by
      intro ι
      have e := congrFun hz' ι
      have e' : I.weightOf ι * ‖h ι‖ ^ 2 = 0 := e
      have e2 : ‖h ι‖ ^ 2 = 0 := (mul_eq_zero.mp e').resolve_left (hw ι).ne'
      exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp e2)
    have hk : ∀ ι', applyKernel T h ι' = 0 := by
      intro ι'
      simp [applyKernel, h0]
    simp [hk, ← hz]
  · set c := Real.sqrt A with hcdef
    have hc : 0 < c := Real.sqrt_pos.mpr hpos
    have hc2 : c ^ 2 = A := Real.sq_sqrt hA0
    let h₁ : I.Carrier → ℂ := fun ι => ((c⁻¹ : ℝ) : ℂ) * h ι
    have hn₁ : ∀ ι, I.weightOf ι * ‖h₁ ι‖ ^ 2 = (c⁻¹) ^ 2 * (I.weightOf ι * ‖h ι‖ ^ 2) := by
      intro ι
      simp only [h₁, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      ring
    have hs₁ : ∑' ι, I.weightOf ι * ‖h₁ ι‖ ^ 2 = 1 := by
      simp_rw [hn₁]
      rw [tsum_mul_left, ← hA, ← hc2]
      field_simp
    have hform : NormSummable I.weightOf h₁ := by
      refine summable_abs_iff.mpr ?_
      simp_rw [hn₁]
      exact hsum.mul_left _
    have hmem : h₁ ∈ wUnitBall I.weightOf (finiteNormSpace I) :=
      ⟨hform, hform, by simp [wNorm, hs₁]⟩
    have hle : ENNReal.ofReal (wNorm I'.weightOf (applyKernel T h₁)) ≤ ENNReal.ofReal β :=
      le_trans (le_iSup₂ (f := fun f (_ : f ∈ wUnitBall I.weightOf (finiteNormSpace I)) =>
        ENNReal.ofReal (wNorm I'.weightOf (applyKernel T f))) h₁ hmem) hT.2.2
    have hle' := (ENNReal.ofReal_le_ofReal_iff hβ).mp hle
    have hact : ∀ ι', applyKernel T h₁ ι' = ((c⁻¹ : ℝ) : ℂ) * applyKernel T h ι' := by
      intro ι'
      simp only [applyKernel, h₁]
      rw [← tsum_mul_left]
      exact tsum_congr fun ι => by ring
    have hB : ∑' ι', I'.weightOf ι' * ‖applyKernel T h₁ ι'‖ ^ 2 =
        (c⁻¹) ^ 2 * ∑' ι', I'.weightOf ι' * ‖applyKernel T h ι'‖ ^ 2 := by
      rw [← tsum_mul_left]
      refine tsum_congr fun ι' => ?_
      rw [hact]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      ring
    have hq := (Real.sqrt_le_iff.mp hle').2
    rw [hB] at hq
    rw [← hc2]
    have hc2pos : 0 < c ^ 2 := by positivity
    calc ∑' ι', I'.weightOf ι' * ‖applyKernel T h ι'‖ ^ 2
        = c ^ 2 * ((c⁻¹) ^ 2 * ∑' ι', I'.weightOf ι' * ‖applyKernel T h ι'‖ ^ 2) := by
          field_simp
      _ ≤ c ^ 2 * β ^ 2 := mul_le_mul_of_nonneg_left hq hc2pos.le
      _ = β ^ 2 * c ^ 2 := mul_comm _ _
theorem weighted_sq_row_le {I I' : PeriodicData} (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {Z : I'.Carrier → I.Carrier → ℂ} {B : I'.Carrier → Set I.Carrier}
    {K : I'.Carrier → I'.Carrier → I.Carrier → ℂ} {β r : ℝ} {m : ℕ} (hβ : 0 ≤ β)
    (hZ : RowsBounded I I' Z B K β r m) (θ : InfiniteLattice.AmbientSpace) (f : I.Carrier → ℂ)
    (ι' : I'.Carrier) :
    I'.weightOf ι' * ‖applyKernel (expConj I I' θ Z) f ι'‖ ^ 2 ≤
      β ^ 2 * (Real.exp (r * ∑ μ, |θ μ|) ^ 2 *
        ∑ ι ∈ (hZ.support_finite ι').toFinset, I.weightOf ι * ‖f ι‖ ^ 2) := by
  classical
  have hw : ∀ ι, 0 < I.weightOf ι := fun ι => hI.weight_pos _
  have hw' : ∀ ι', 0 < I'.weightOf ι' := fun ι' => hI'.weight_pos _
  set s := (hZ.support_finite ι').toFinset with hs
  set E := Real.exp (r * ∑ μ, |θ μ|) with hE
  let h : I.Carrier → ℂ := fun ι =>
    if ι ∈ s then
      Complex.exp (bilinDot (toComplexVec θ) (toComplexVec (I'.pos ι' - I.pos ι))) * f ι
    else 0
  have hact : applyKernel (expConj I I' θ Z) f ι' = applyKernel (K ι') h ι' := by
    unfold applyKernel
    refine tsum_congr fun ι => ?_
    by_cases hι : ι ∈ B ι'
    · have hm : ι ∈ s := (hZ.support_finite ι').mem_toFinset.mpr hι
      simp only [expConj, h, if_pos hm]
      rw [hZ.expansion_eq ι' ι hι]
      ring
    · have hm : ι ∉ s := fun e => hι ((hZ.support_finite ι').mem_toFinset.mp e)
      simp only [expConj, h, if_neg hm]
      rw [hZ.eq_zero_of_not_mem ι' ι hι]
      simp
  have hzero : ∀ ι, ι ∉ s → I.weightOf ι * ‖h ι‖ ^ 2 = 0 := by
    intro ι hι
    simp [h, if_neg hι]
  have hsum : ∑' ι, I.weightOf ι * ‖h ι‖ ^ 2 = ∑ ι ∈ s, I.weightOf ι * ‖h ι‖ ^ 2 :=
    tsum_eq_sum hzero
  have hfin : h ∈ finiteNormSpace I := by
    change Summable fun ι => |I.weightOf ι * ‖h ι‖ ^ 2|
    exact summable_of_ne_finset_zero (s := s) fun ι hι => by rw [hzero ι hι, abs_zero]
  have hbound := weighted_sq_applyKernel_le hI hβ (hZ.opNorm_le ι') hfin
  have hsummable : Summable fun j => I'.weightOf j * ‖applyKernel (K ι') h j‖ ^ 2 :=
    summable_abs_iff.mp ((hZ.opNorm_le ι').1 h hfin).2
  have hle : I'.weightOf ι' * ‖applyKernel (K ι') h ι'‖ ^ 2 ≤
      ∑' j, I'.weightOf j * ‖applyKernel (K ι') h j‖ ^ 2 :=
    hsummable.le_tsum ι' fun j _ => by
      have := (hw' j).le
      positivity
  have hterm : ∑ ι ∈ s, I.weightOf ι * ‖h ι‖ ^ 2 ≤
      E ^ 2 * ∑ ι ∈ s, I.weightOf ι * ‖f ι‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ι hι => ?_
    have hB : ι ∈ B ι' := (hZ.support_finite ι').mem_toFinset.mp hι
    have hexp : ‖Complex.exp (bilinDot (toComplexVec θ)
        (toComplexVec (I'.pos ι' - I.pos ι)))‖ ≤ E := by
      refine norm_cexp_bilinDot_le θ _ r fun μ => ?_
      have := hZ.dist_le ι' ι hB μ
      rw [abs_sub_comm] at this
      exact this
    have hsq : ‖Complex.exp (bilinDot (toComplexVec θ)
        (toComplexVec (I'.pos ι' - I.pos ι)))‖ ^ 2 ≤ E ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hexp 2
    have hwf : 0 ≤ I.weightOf ι * ‖f ι‖ ^ 2 := by
      have := (hw ι).le
      positivity
    have hh : ‖h ι‖ ^ 2 = ‖Complex.exp (bilinDot (toComplexVec θ)
        (toComplexVec (I'.pos ι' - I.pos ι)))‖ ^ 2 * ‖f ι‖ ^ 2 := by
      simp only [h, if_pos hι, norm_mul, mul_pow]
    calc I.weightOf ι * ‖h ι‖ ^ 2
        = ‖Complex.exp (bilinDot (toComplexVec θ)
            (toComplexVec (I'.pos ι' - I.pos ι)))‖ ^ 2 *
            (I.weightOf ι * ‖f ι‖ ^ 2) := by rw [hh]; ring
      _ ≤ E ^ 2 * (I.weightOf ι * ‖f ι‖ ^ 2) := mul_le_mul_of_nonneg_right hsq hwf
  rw [hact]
  calc I'.weightOf ι' * ‖applyKernel (K ι') h ι'‖ ^ 2
      ≤ β ^ 2 * ∑' ι, I.weightOf ι * ‖h ι‖ ^ 2 := hle.trans hbound
    _ = β ^ 2 * ∑ ι ∈ s, I.weightOf ι * ‖h ι‖ ^ 2 := by rw [hsum]
    _ ≤ β ^ 2 * (E ^ 2 * ∑ ι ∈ s, I.weightOf ι * ‖f ι‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hterm (by positivity)
theorem kernelOpNorm_expConj_le {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {Z : I'.Carrier → I.Carrier → ℂ} {B : I'.Carrier → Set I.Carrier}
    {K : I'.Carrier → I'.Carrier → I.Carrier → ℂ} {β r : ℝ} {m : ℕ} (hβ : 0 ≤ β)
    (hZ : RowsBounded I I' Z B K β r m) (θ : InfiniteLattice.AmbientSpace) :
    kernelOpNorm I I' (expConj I I' θ Z) ≤
      ENNReal.ofReal (Real.sqrt m * β * Real.exp (r * ∑ μ, |θ μ|)) := by
  unfold kernelOpNorm wOpNorm
  refine iSup₂_le fun f hf => ?_
  have hw : ∀ ι, 0 < I.weightOf ι := fun ι => hI.weight_pos _
  have hw' : ∀ ι', 0 < I'.weightOf ι' := fun ι' => hI'.weight_pos _
  set E := Real.exp (r * ∑ μ, |θ μ|) with hE
  have hW0 : ∀ ι, 0 ≤ I.weightOf ι * ‖f ι‖ ^ 2 := fun ι => by
    have := (hw ι).le
    positivity
  have hW : Summable fun ι => I.weightOf ι * ‖f ι‖ ^ 2 := summable_abs_iff.mp hf.2.1
  have hW1 : ∑' ι, I.weightOf ι * ‖f ι‖ ^ 2 ≤ 1 := by
    have h1 := (Real.sqrt_le_iff.mp hf.2.2).2
    simpa using h1
  have hrows : ∀ S : Finset I'.Carrier,
      ∑ ι' ∈ S, I'.weightOf ι' * ‖applyKernel (expConj I I' θ Z) f ι'‖ ^ 2 ≤
        (m : ℝ) * β ^ 2 * E ^ 2 := by
    intro S
    have hcount := sum_finset_rows_le_mul_tsum (fun ι' => (hZ.support_finite ι').toFinset)
      (fun ι => I.weightOf ι * ‖f ι‖ ^ 2) hW0 hW m (fun ι => by
        have hset : {j | ι ∈ (hZ.support_finite j).toFinset} = {ι' | ι ∈ B ι'} := by
          ext j
          simp
        rw [hset]
        exact hZ.encard_le ι) S
    have hm1 : (m : ℝ) * ∑' ι, I.weightOf ι * ‖f ι‖ ^ 2 ≤ m :=
      mul_le_of_le_one_right (Nat.cast_nonneg m) hW1
    calc ∑ ι' ∈ S, I'.weightOf ι' * ‖applyKernel (expConj I I' θ Z) f ι'‖ ^ 2
        ≤ ∑ ι' ∈ S, β ^ 2 * (E ^ 2 *
            ∑ ι ∈ (hZ.support_finite ι').toFinset, I.weightOf ι * ‖f ι‖ ^ 2) :=
          Finset.sum_le_sum fun ι' _ => weighted_sq_row_le hI hI' hβ hZ θ f ι'
      _ = β ^ 2 * E ^ 2 *
            ∑ ι' ∈ S, ∑ ι ∈ (hZ.support_finite ι').toFinset, I.weightOf ι * ‖f ι‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ι' _ => by ring
      _ ≤ β ^ 2 * E ^ 2 * m :=
          mul_le_mul_of_nonneg_left (hcount.trans hm1) (by positivity)
      _ = (m : ℝ) * β ^ 2 * E ^ 2 := by ring
  have htsum := Real.tsum_le_of_sum_le (f := fun ι' =>
    I'.weightOf ι' * ‖applyKernel (expConj I I' θ Z) f ι'‖ ^ 2)
    (fun ι' => by
      have := (hw' ι').le
      change 0 ≤ I'.weightOf ι' * _
      positivity) hrows
  apply ENNReal.ofReal_le_ofReal
  unfold wNorm
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  exact htsum
theorem quotHomNorm_symbolHom (I I' : PeriodicData) [Finite I.UnitQuot]
    (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ) :
    quotHomNorm (symbolHom I I' T κ) = quotOpNorm I I' (quotSymbol I I' T κ) := by apply _root_.YangMills.Construction.Tower.SymbolBounds.quotHomNorm_symbolHom <;> assumption
theorem quotHomNorm_symbolHom_le_kernelOpNorm (hshift : SymbolImShift.Claim)
    (hnorm : _root_.YangMills.Construction.PeriodicOperators.SymbolNormBound)
    {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {Z : I'.Carrier → I.Carrier → ℂ}
    (hZ : IsFiniteRangeAllRates I I' Z) (κ : Fin 4 → ℂ) :
    quotHomNorm (symbolHom I I' Z κ) ≤
      kernelOpNorm I I' (expConj I I' (imVec κ) Z) := by
  have : Finite I.UnitQuot := hI.finite_quot
  set θ := imVec κ with hθ
  set y : InfiniteLattice.AmbientSpace := fun μ => (κ μ).re with hy
  have hpos : 0 ≤ TorusMetric.euclidNormVec θ := Real.sqrt_nonneg _
  have hδ : 0 < TorusMetric.euclidNormVec θ + 1 := by linarith
  have hreal : TorusMetric.euclidNormVec (imVec (toComplexVec y)) = 0 := by
    simp [TorusMetric.euclidNormVec, imVec, toComplexVec]
  have hmem : toComplexVec y ∈ strictImStrip (TorusMetric.euclidNormVec θ + 1 -
      TorusMetric.euclidNormVec θ) := by
    change TorusMetric.euclidNormVec (imVec (toComplexVec y)) < _
    rw [hreal]
    linarith
  obtain ⟨hper, -, hsym⟩ :=
    hshift I I' hI hI' Z _ hZ.periodic (hZ.decays _ hδ) θ (by linarith) _ hmem
  have hpoint : addIVec (toComplexVec y) θ = κ := by
    funext μ
    apply Complex.ext <;> simp [addIVec, toComplexVec, hy, hθ, imVec]
  rw [hpoint] at hsym
  have hmat : quotSymbol I I' Z κ =
      quotSymbol I I' (expConj I I' θ Z) (toComplexVec y) := by
    unfold quotSymbol
    rw [hsym]
  rw [quotHomNorm_symbolHom, hmat]
  exact hnorm I I' hI hI' _ hper y
theorem symbolNormBound_holds (hshift : SymbolImShift.Claim)
    (hnorm : _root_.YangMills.Construction.PeriodicOperators.SymbolNormBound) :
    SymbolNormBound := by
  intro I I' hI hI' Z hZ B K β r m hβ _ hrows κ
  exact (quotHomNorm_symbolHom_le_kernelOpNorm hshift hnorm hI hI' hZ κ).trans
    (kernelOpNorm_expConj_le hI hI' hβ hrows (imVec κ))
end YangMills.Construction.PeriodicOperators.BoundedExpansionSymbol
end
