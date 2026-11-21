import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMomentsProof
import YangMills.Construction.Cumulants.MultilinearityShiftsAndMomentsOfJointCumulants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Cumulants.CumulantIdentities
section Transform
open MeasureTheory Filter Topology
variable {Ω : Type} [MeasurableSpace Ω] {P : Type} [Fintype P]
def linearPairing (Y : P → Ω → ℝ) (ω : Ω) : (P → ℂ) →L[ℂ] ℂ :=
  ∑ p, (Y p ω : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : P => ℂ) p
theorem linearPairing_apply (Y : P → Ω → ℝ) (ω : Ω) (t : P → ℂ) :
    linearPairing Y ω t = ∑ p, t p * (Y p ω : ℂ) := by
  simp [linearPairing, mul_comm]
def weightedTransform (ν : Measure Ω) (Y : P → Ω → ℝ) (w : Ω → ℂ) (t : P → ℂ) : ℂ :=
  ∫ ω, w ω * Complex.exp (linearPairing Y ω t) ∂ν
structure IsBoundedComplexFn (w : Ω → ℂ) : Prop where
  measurable : Measurable w
  bounded : ∃ C : ℝ, ∀ ω, ‖w ω‖ ≤ C
theorem IsBoundedComplexFn.mul {v w : Ω → ℂ} (hv : IsBoundedComplexFn v)
    (hw : IsBoundedComplexFn w) : IsBoundedComplexFn fun ω => v ω * w ω := by
  obtain ⟨a, ha⟩ := hv.bounded
  obtain ⟨b, hb⟩ := hw.bounded
  refine ⟨hv.measurable.mul hw.measurable, a * b, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (ha ω) (hb ω) (norm_nonneg _) ((norm_nonneg _).trans (ha ω))
theorem IsBoundedComplexFn.integrable {w : Ω → ℂ} (hw : IsBoundedComplexFn w) (ν : Measure Ω)
    [IsFiniteMeasure ν] : Integrable w ν := by
  obtain ⟨C, hC⟩ := hw.bounded
  exact Integrable.of_bound hw.measurable.aestronglyMeasurable C (ae_of_all _ hC)
theorem isBoundedComplexFn_one : IsBoundedComplexFn fun _ : Ω => (1 : ℂ) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem IsBoundedComplexFn.finset_prod {ι : Type} (s : Finset ι) {f : ι → Ω → ℂ}
    (h : ∀ i, IsBoundedComplexFn (f i)) : IsBoundedComplexFn fun ω => ∏ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isBoundedComplexFn_one
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih
structure IsBoundedRealFamily (Y : P → Ω → ℝ) : Prop where
  measurable : ∀ p, Measurable (Y p)
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ω, |Y p ω| ≤ C
variable {Y : P → Ω → ℝ}
theorem IsBoundedRealFamily.ofReal_coord (hY : IsBoundedRealFamily Y) (p : P) :
    IsBoundedComplexFn fun ω => (Y p ω : ℂ) := by
  obtain ⟨C, -, hC⟩ := hY.bounded
  refine ⟨Complex.measurable_ofReal.comp (hY.measurable p), C, fun ω => ?_⟩
  simpa using hC p ω
theorem IsBoundedRealFamily.measurable_linearPairing (hY : IsBoundedRealFamily Y) (t : P → ℂ) :
    Measurable fun ω => linearPairing Y ω t := by
  simp only [linearPairing_apply]
  exact Finset.measurable_fun_sum _ fun p _ => (hY.ofReal_coord p).measurable.const_mul _
theorem IsBoundedRealFamily.norm_linearPairing_le (hY : IsBoundedRealFamily Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : P → ℂ) ω, ‖linearPairing Y ω t‖ ≤ C * ‖t‖ := by
  obtain ⟨C, hC0, hC⟩ := hY.bounded
  refine ⟨Fintype.card P * C, by positivity, fun t ω => ?_⟩
  rw [linearPairing_apply]
  calc ‖∑ p, t p * (Y p ω : ℂ)‖ ≤ ∑ p, ‖t p * (Y p ω : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : P, ‖t‖ * C := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul]
        refine mul_le_mul (norm_le_pi_norm t p) ?_ (norm_nonneg _) (norm_nonneg _)
        simpa using hC p ω
    _ = Fintype.card P * C * ‖t‖ := by simp; ring
theorem IsBoundedRealFamily.linearPairing_bounded (hY : IsBoundedRealFamily Y) (t : P → ℂ) :
    IsBoundedComplexFn fun ω => linearPairing Y ω t := by
  obtain ⟨C, -, hC⟩ := hY.norm_linearPairing_le
  exact ⟨hY.measurable_linearPairing t, C * ‖t‖, fun ω => hC t ω⟩
theorem IsBoundedRealFamily.exp_linearPairing_bounded (hY : IsBoundedRealFamily Y) (t : P → ℂ) :
    IsBoundedComplexFn fun ω => Complex.exp (linearPairing Y ω t) := by
  obtain ⟨C, -, hC⟩ := hY.norm_linearPairing_le
  refine ⟨Complex.measurable_exp.comp (hY.measurable_linearPairing t), Real.exp (C * ‖t‖),
    fun ω => ?_⟩
  exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 (hC t ω))
variable {ν : Measure Ω} [IsProbabilityMeasure ν]
theorem hasFDerivAt_weightedTransform (hY : IsBoundedRealFamily Y) {w : Ω → ℂ}
    (hw : IsBoundedComplexFn w) (t₀ : P → ℂ) :
    HasFDerivAt (weightedTransform ν Y w)
      (∑ p, weightedTransform ν Y (fun ω => w ω * (Y p ω : ℂ)) t₀ •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : P => ℂ) p) t₀ := by
  obtain ⟨C, hC0, hC⟩ := hY.norm_linearPairing_le
  obtain ⟨D, hD0, hD⟩ := hY.bounded
  obtain ⟨B, hB⟩ := hw.bounded
  have hB0 : ∀ ω : Ω, 0 ≤ B := fun ω => (norm_nonneg _).trans (hB ω)
  set F' : (P → ℂ) → Ω → ((P → ℂ) →L[ℂ] ℂ) := fun t ω =>
    ∑ p, (w ω * Complex.exp (linearPairing Y ω t) * (Y p ω : ℂ)) •
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : P => ℂ) p with hF'
  have hproj : ∀ p : P, ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : P => ℂ) p‖ ≤ 1 :=
    fun p => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa using norm_le_pi_norm x p
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := ν)
    (F := fun t ω => w ω * Complex.exp (linearPairing Y ω t)) (F' := F') (x₀ := t₀)
    (s := Metric.ball t₀ 1)
    (bound := fun _ => Fintype.card P * (B * Real.exp (C * (‖t₀‖ + 1)) * D))
    (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun t =>
      (hw.mul (hY.exp_linearPairing_bounded t)).measurable.aestronglyMeasurable)
    ((hw.mul (hY.exp_linearPairing_bounded t₀)).integrable ν)
    (by
      refine Finset.aestronglyMeasurable_fun_sum _ fun p _ => ?_
      exact (((hw.mul (hY.exp_linearPairing_bounded t₀)).mul
        (hY.ofReal_coord p)).measurable.stronglyMeasurable.smul_const _).aestronglyMeasurable)
    (ae_of_all _ fun ω t ht => by
      have ht' : ‖t‖ ≤ ‖t₀‖ + 1 := by
        have : ‖t - t₀‖ < 1 := by simpa [dist_eq_norm] using ht
        calc ‖t‖ = ‖t₀ + (t - t₀)‖ := by simp
          _ ≤ ‖t₀‖ + ‖t - t₀‖ := norm_add_le _ _
          _ ≤ _ := by linarith
      have hexp : ‖Complex.exp (linearPairing Y ω t)‖ ≤ Real.exp (C * (‖t₀‖ + 1)) :=
        (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ((hC t ω).trans
          (mul_le_mul_of_nonneg_left ht' hC0)))
      calc ‖F' t ω‖ ≤ ∑ p, ‖(w ω * Complex.exp (linearPairing Y ω t) * (Y p ω : ℂ)) •
              ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : P => ℂ) p‖ := norm_sum_le _ _
        _ ≤ ∑ _p : P, B * Real.exp (C * (‖t₀‖ + 1)) * D := by
            refine Finset.sum_le_sum fun p _ => ?_
            rw [norm_smul, norm_mul, norm_mul]
            have h1 : ‖(Y p ω : ℂ)‖ ≤ D := by simpa using hD p ω
            calc _ ≤ ‖w ω‖ * ‖Complex.exp (linearPairing Y ω t)‖ * ‖(Y p ω : ℂ)‖ * 1 :=
                  mul_le_mul_of_nonneg_left (hproj p) (by positivity)
              _ ≤ _ := by
                  rw [mul_one]
                  have := hB0 ω
                  gcongr
                  · exact hB ω
        _ = _ := by simp)
    (integrable_const _)
    (ae_of_all _ fun ω t _ => by
      have h := (((linearPairing Y ω).hasFDerivAt (x := t)).cexp).const_mul (w ω)
      refine h.congr_fderiv ?_
      ext p
      simp [hF', linearPairing, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm])
  have hint : ∀ p : P,
      Integrable (fun ω => w ω * Complex.exp (linearPairing Y ω t₀) * (Y p ω : ℂ)) ν :=
    fun p => ((hw.mul (hY.exp_linearPairing_bounded t₀)).mul (hY.ofReal_coord p)).integrable ν
  have hval : ∫ ω, F' t₀ ω ∂ν = ∑ p, weightedTransform ν Y (fun ω => w ω * (Y p ω : ℂ)) t₀ •
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : P => ℂ) p := by
    simp only [hF']
    rw [integral_finsetSum _ fun p _ => (hint p).smul_const _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_smul_const]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    ring
  rw [← hval]
  exact hmain
theorem differentiable_weightedTransform (hY : IsBoundedRealFamily Y) {w : Ω → ℂ}
    (hw : IsBoundedComplexFn w) : Differentiable ℂ (weightedTransform ν Y w) :=
  fun t => (hasFDerivAt_weightedTransform hY hw t).differentiableAt
theorem fderiv_weightedTransform (hY : IsBoundedRealFamily Y) {w : Ω → ℂ}
    (hw : IsBoundedComplexFn w) :
    fderiv ℂ (weightedTransform ν Y w) = fun t =>
      ∑ p, weightedTransform ν Y (fun ω => w ω * (Y p ω : ℂ)) t •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : P => ℂ) p :=
  funext fun t => (hasFDerivAt_weightedTransform hY hw t).fderiv
theorem fderiv_weightedTransform_apply (hY : IsBoundedRealFamily Y) {w : Ω → ℂ}
    (hw : IsBoundedComplexFn w) (t v : P → ℂ) :
    fderiv ℂ (weightedTransform ν Y w) t v =
      weightedTransform ν Y (fun ω => w ω * linearPairing Y ω v) t := by
  rw [fderiv_weightedTransform hY hw]
  have hint : ∀ p : P, Integrable (fun ω => v p * (w ω * (Y p ω : ℂ) *
      Complex.exp (linearPairing Y ω t))) ν :=
    fun p => (((hw.mul (hY.ofReal_coord p)).mul (hY.exp_linearPairing_bounded t)).integrable
      ν).const_mul _
  simp only [_root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, weightedTransform]
  simp only [mul_comm (∫ ω, _ ∂ν) (v _), ← integral_const_mul]
  rw [← integral_finsetSum _ fun p _ => hint p]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [linearPairing_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring
theorem contDiff_weightedTransform (hY : IsBoundedRealFamily Y) (n : ℕ) :
    ∀ {w : Ω → ℂ}, IsBoundedComplexFn w → ContDiff ℂ n (weightedTransform ν Y w) := by
  induction n with
  | zero =>
    intro w hw
    exact contDiff_zero.2 (differentiable_weightedTransform hY hw).continuous
  | succ n ih =>
    intro w hw
    have : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [this, contDiff_succ_iff_fderiv]
    refine ⟨differentiable_weightedTransform hY hw, by simp, ?_⟩
    rw [fderiv_weightedTransform hY hw]
    exact ContDiff.sum fun p _ => (ih (hw.mul (hY.ofReal_coord p))).smul contDiff_const
theorem iteratedFDeriv_weightedTransform (hY : IsBoundedRealFamily Y) (k : ℕ) :
    ∀ {w : Ω → ℂ}, IsBoundedComplexFn w → ∀ (t : P → ℂ) (m : Fin k → P → ℂ),
      iteratedFDeriv ℂ k (weightedTransform ν Y w) t m =
        weightedTransform ν Y (fun ω => w ω * ∏ j, linearPairing Y ω (m j)) t := by
  induction k with
  | zero =>
    intro w hw t m
    simp
  | succ k ih =>
    intro w hw t m
    rw [iteratedFDeriv_succ_apply_left]
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k (weightedTransform ν Y w)) t :=
      ((contDiff_weightedTransform hY (k + 1) hw).differentiable_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_self k)) t
    have h1 := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => P → ℂ) ℂ
      (Fin.tail m)).hasFDerivAt.comp t hd.hasFDerivAt
    have h2 : (⇑(ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => P → ℂ) ℂ (Fin.tail m)) ∘
        iteratedFDeriv ℂ k (weightedTransform ν Y w)) =
        weightedTransform ν Y (fun ω => w ω * ∏ j, linearPairing Y ω (Fin.tail m j)) := by
      funext s
      exact ih hw s _
    rw [h2] at h1
    have hw' : IsBoundedComplexFn fun ω => w ω * ∏ j, linearPairing Y ω (Fin.tail m j) := by
      refine hw.mul ?_
      exact IsBoundedComplexFn.finset_prod Finset.univ fun j => hY.linearPairing_bounded _
    have h3 := congrArg (fun L => L (m 0)) h1.fderiv
    simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply] at h3
    erw [← h3, fderiv_weightedTransform_apply hY hw']
    congr 1
    funext ω
    rw [Fin.prod_univ_succ]
    simp only [Fin.tail]
    ring
end Transform
section Blocks
open Finset
variable {q : ℕ}
def partBlock (c : OrderedFinpartition q) (m : Fin c.length) : Finset (Fin q) :=
  univ.image (c.emb m)
def partMax (c : OrderedFinpartition q) (m : Fin c.length) : Fin q :=
  c.emb m ⟨c.partSize m - 1, Nat.sub_one_lt_of_lt (c.partSize_pos m)⟩
theorem partMax_strictMono (c : OrderedFinpartition q) : StrictMono (partMax c) :=
  c.parts_strictMono
theorem coe_partBlock (c : OrderedFinpartition q) (m : Fin c.length) :
    (partBlock c m : Set (Fin q)) = Set.range (c.emb m) := by
  simp [partBlock]
theorem card_partBlock (c : OrderedFinpartition q) (m : Fin c.length) :
    (partBlock c m).card = c.partSize m := by
  rw [partBlock, card_image_of_injective _ (c.emb_strictMono m).injective]
  simp
theorem partMax_mem (c : OrderedFinpartition q) (m : Fin c.length) :
    partMax c m ∈ partBlock c m :=
  mem_image_of_mem _ (mem_univ _)
theorem le_partMax (c : OrderedFinpartition q) {m : Fin c.length} {y : Fin q}
    (hy : y ∈ partBlock c m) : y ≤ partMax c m := by
  obtain ⟨i, -, rfl⟩ := mem_image.1 hy
  refine (c.emb_strictMono m).monotone ?_
  rw [Fin.le_def]
  have := i.2
  simp only
  omega
theorem disjoint_partBlock (c : OrderedFinpartition q) {m m' : Fin c.length} (h : m ≠ m') :
    Disjoint (partBlock c m) (partBlock c m') := by
  rw [← Finset.disjoint_coe, coe_partBlock, coe_partBlock]
  exact c.disjoint (Set.mem_univ _) (Set.mem_univ _) h
theorem partBlock_injective (c : OrderedFinpartition q) : Function.Injective (partBlock c) := by
  intro m m' h
  by_contra hne
  have := disjoint_partBlock c hne
  rw [h, disjoint_self] at this
  exact absurd (partMax_mem c m') (by simp [this])
def forgetOrder (c : OrderedFinpartition q) : Finpartition (univ : Finset (Fin q)) where
  parts := univ.image (partBlock c)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro B hB B' hB' hne
    obtain ⟨m, -, rfl⟩ := mem_image.1 (mem_coe.1 hB)
    obtain ⟨m', -, rfl⟩ := mem_image.1 (mem_coe.1 hB')
    exact disjoint_partBlock c fun h => hne (by rw [h])
  sup_parts := by
    ext x
    simp only [mem_sup, mem_image, mem_univ, true_and, id, iff_true]
    obtain ⟨m, hm⟩ := c.cover x
    exact ⟨partBlock c m, ⟨m, rfl⟩, by rw [← mem_coe, coe_partBlock]; exact hm⟩
  bot_notMem := by
    intro h
    obtain ⟨m, -, hm⟩ := mem_image.1 h
    have := partMax_mem c m
    rw [hm] at this
    simp at this
theorem orderedFinpartition_ext {c c' : OrderedFinpartition q} (hl : c.length = c'.length)
    (hp : ∀ m, c.partSize m = c'.partSize (Fin.cast hl m))
    (he : ∀ m i, c.emb m i = c'.emb (Fin.cast hl m) (Fin.cast (hp m) i)) : c = c' := by
  cases c with
  | mk l ps _ e _ _ _ _ =>
  cases c' with
  | mk l' ps' _ e' _ _ _ _ =>
  dsimp only at hl hp he
  subst hl
  have h1 : ps = ps' := funext fun m => by simpa using hp m
  subst h1
  have h2 : e = e' := by
    funext m i
    simpa using he m i
  subst h2
  rfl
theorem eq_of_image_partBlock {c c' : OrderedFinpartition q}
    (h : univ.image (partBlock c) = univ.image (partBlock c')) : c = c' := by
  have range_last : ∀ {d d' : OrderedFinpartition q},
      univ.image (partBlock d) = univ.image (partBlock d') →
      ∀ m, ∃ m', partBlock d m = partBlock d' m' ∧ partMax d m = partMax d' m' := by
    intro d d' h m
    have hm : partBlock d m ∈ univ.image (partBlock d') := h ▸ mem_image_of_mem _ (mem_univ _)
    obtain ⟨m', -, hm'⟩ := mem_image.1 hm
    refine ⟨m', hm'.symm, le_antisymm ?_ ?_⟩
    · exact le_partMax d' (hm' ▸ partMax_mem d m)
    · exact le_partMax d (hm' ▸ partMax_mem d' m')
  have hr : Set.range (partMax c) = Set.range (partMax c') := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      obtain ⟨m', -, h'⟩ := range_last h m
      exact ⟨m', h'.symm⟩
    · rintro ⟨m, rfl⟩
      obtain ⟨m', -, h'⟩ := range_last h.symm m
      exact ⟨m', h'.symm⟩
  have hcard : ∀ d : OrderedFinpartition q,
      (Set.range (partMax d)).ncard = d.length := by
    intro d
    rw [← Set.image_univ, Set.ncard_image_of_injective _ (partMax_strictMono d).injective]
    simp
  have hl : c.length = c'.length := by rw [← hcard c, ← hcard c', hr]
  have hlast : partMax c = partMax c' ∘ Fin.cast hl := by
    refine ((partMax_strictMono c).range_inj
      ((partMax_strictMono c').comp (fun _ _ h => h))).1 ?_
    rw [hr]
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨Fin.cast hl.symm m, by simp⟩
    · rintro ⟨m, rfl⟩
      exact ⟨Fin.cast hl m, rfl⟩
  have hblock : ∀ m, partBlock c m = partBlock c' (Fin.cast hl m) := by
    intro m
    obtain ⟨m', hb, h'⟩ := range_last h m
    have : m' = Fin.cast hl m :=
      (partMax_strictMono c').injective (by rw [← h', hlast]; rfl)
    rw [hb, this]
  have hp : ∀ m, c.partSize m = c'.partSize (Fin.cast hl m) := fun m => by
    rw [← card_partBlock, ← card_partBlock, hblock]
  refine orderedFinpartition_ext hl hp fun m i => ?_
  have : c.emb m = c'.emb (Fin.cast hl m) ∘ Fin.cast (hp m) := by
    refine ((c.emb_strictMono m).range_inj
      ((c'.emb_strictMono _).comp (fun _ _ h => h))).1 ?_
    rw [← coe_partBlock, hblock, coe_partBlock]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Fin.cast (hp m).symm a, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Fin.cast (hp m) a, rfl⟩
  exact congrFun this i
theorem forgetOrder_injective : Function.Injective (forgetOrder (q := q)) := by
  intro c c' h
  exact eq_of_image_partBlock (congrArg Finpartition.parts h)
def blockMaxima (π : Finpartition (univ : Finset (Fin q))) : Finset (Fin q) :=
  univ.filter fun x => ∀ y ∈ π.part x, y ≤ x
def nthMax (π : Finpartition (univ : Finset (Fin q))) (k : Fin (blockMaxima π).card) : Fin q :=
  (blockMaxima π).orderEmbOfFin rfl k
def nthBlock (π : Finpartition (univ : Finset (Fin q))) (k : Fin (blockMaxima π).card) :
    Finset (Fin q) :=
  π.part (nthMax π k)
theorem nthMax_strictMono (π : Finpartition (univ : Finset (Fin q))) : StrictMono (nthMax π) :=
  ((blockMaxima π).orderEmbOfFin rfl).strictMono
theorem nthMax_mem (π : Finpartition (univ : Finset (Fin q))) (k : Fin (blockMaxima π).card) :
    nthMax π k ∈ nthBlock π k :=
  π.mem_part_self.2 (mem_univ _)
theorem nthBlock_mem (π : Finpartition (univ : Finset (Fin q))) (k : Fin (blockMaxima π).card) :
    nthBlock π k ∈ π.parts :=
  π.part_mem.2 (mem_univ _)
theorem le_nthMax (π : Finpartition (univ : Finset (Fin q))) (k : Fin (blockMaxima π).card)
    {y : Fin q} (hy : y ∈ nthBlock π k) : y ≤ nthMax π k :=
  (mem_filter.1 (orderEmbOfFin_mem (blockMaxima π) rfl k)).2 y hy
theorem exists_nthBlock (π : Finpartition (univ : Finset (Fin q))) {B : Finset (Fin q)}
    (hB : B ∈ π.parts) : ∃ k, nthBlock π k = B := by
  have hne := π.nonempty_of_mem_parts hB
  have hu : B.max' hne ∈ B := max'_mem _ _
  have hp : π.part (B.max' hne) = B := π.part_eq_of_mem hB hu
  have ht : B.max' hne ∈ blockMaxima π := by
    refine mem_filter.2 ⟨mem_univ _, fun y hy => ?_⟩
    rw [hp] at hy
    exact le_max' _ _ hy
  have : B.max' hne ∈ Set.range ((blockMaxima π).orderEmbOfFin rfl) := by
    rw [range_orderEmbOfFin]
    exact ht
  obtain ⟨k, hk⟩ := this
  refine ⟨k, ?_⟩
  rw [nthBlock, nthMax, hk, hp]
theorem nthBlock_injective (π : Finpartition (univ : Finset (Fin q))) :
    Function.Injective (nthBlock π) := by
  intro k k' h
  refine (nthMax_strictMono π).injective (le_antisymm ?_ ?_)
  · exact le_nthMax π k' (h ▸ nthMax_mem π k)
  · exact le_nthMax π k (h ▸ nthMax_mem π k')
def orderByMax (π : Finpartition (univ : Finset (Fin q))) : OrderedFinpartition q where
  length := (blockMaxima π).card
  partSize k := (nthBlock π k).card
  partSize_pos k := card_pos.2 ⟨_, nthMax_mem π k⟩
  emb k := (nthBlock π k).orderEmbOfFin rfl
  emb_strictMono k := ((nthBlock π k).orderEmbOfFin rfl).strictMono
  parts_strictMono := by
    have : ∀ k, (nthBlock π k).orderEmbOfFin rfl
        ⟨(nthBlock π k).card - 1, Nat.sub_one_lt_of_lt (card_pos.2 ⟨_, nthMax_mem π k⟩)⟩ =
        nthMax π k := by
      intro k
      rw [orderEmbOfFin_last rfl (card_pos.2 ⟨_, nthMax_mem π k⟩)]
      exact le_antisymm (max'_le _ _ _ fun y hy => le_nthMax π k hy)
        (le_max' _ _ (nthMax_mem π k))
    intro k k' h
    simp only [this]
    exact nthMax_strictMono π h
  disjoint := by
    intro k _ k' _ hne
    have hd : Disjoint (nthBlock π k) (nthBlock π k') :=
      π.disjoint (mem_coe.2 (nthBlock_mem π k)) (mem_coe.2 (nthBlock_mem π k'))
        fun h => hne (nthBlock_injective π h)
    simp only [Function.onFun, range_orderEmbOfFin]
    exact Finset.disjoint_coe.2 hd
  cover x := by
    obtain ⟨k, hk⟩ := exists_nthBlock π (π.part_mem.2 (mem_univ x))
    refine ⟨k, ?_⟩
    rw [range_orderEmbOfFin, mem_coe, hk]
    exact π.mem_part_self.2 (mem_univ _)
theorem forgetOrder_surjective : Function.Surjective (forgetOrder (q := q)) := by
  intro π
  refine ⟨orderByMax π, Finpartition.ext ?_⟩
  have hb : ∀ k, partBlock (orderByMax π) k = nthBlock π k := fun k =>
    image_orderEmbOfFin_univ (nthBlock π k) rfl
  ext B
  constructor
  · intro h
    obtain ⟨k, -, rfl⟩ := mem_image.1 h
    rw [hb]
    exact nthBlock_mem π k
  · intro h
    obtain ⟨k, rfl⟩ := exists_nthBlock π h
    exact mem_image.2 ⟨k, mem_univ _, hb k⟩
theorem sum_ordered_eq_sum_finpartition (F : Finset (Fin q) → ℂ) :
    ∑ c : OrderedFinpartition q, ∏ m, F (partBlock c m) =
      ∑ π : Finpartition (univ : Finset (Fin q)), ∏ B ∈ π.parts, F B := by
  refine Fintype.sum_bijective _ ⟨forgetOrder_injective, forgetOrder_surjective⟩ _ _
    fun c => ?_
  change _ = ∏ B ∈ univ.image (partBlock c), F B
  rw [prod_image fun _ _ _ _ h => partBlock_injective c h]
end Blocks
section Cumulants
open MeasureTheory Filter Topology
open YangMills.Construction.Probability (IsBoundedRealRV)
variable {Ω : Type} [MeasurableSpace Ω] {P : Type} [Fintype P]
variable {Y : P → Ω → ℝ} {ν : Measure Ω} [IsProbabilityMeasure ν]
def laplaceTransform (ν : Measure Ω) (Y : P → Ω → ℝ) : (P → ℂ) → ℂ :=
  weightedTransform ν Y fun _ => 1
def logLaplace (ν : Measure Ω) (Y : P → Ω → ℝ) (t : P → ℂ) : ℂ :=
  Complex.log (laplaceTransform ν Y t)
def logDomain (ν : Measure Ω) (Y : P → Ω → ℝ) : Set (P → ℂ) :=
  laplaceTransform ν Y ⁻¹' Complex.slitPlane
theorem laplaceTransform_zero : laplaceTransform ν Y 0 = 1 := by
  simp [laplaceTransform, weightedTransform]
theorem contDiff_laplaceTransform (hY : IsBoundedRealFamily Y) (n : ℕ) :
    ContDiff ℂ n (laplaceTransform ν Y) :=
  contDiff_weightedTransform hY n isBoundedComplexFn_one
theorem continuous_laplaceTransform (hY : IsBoundedRealFamily Y) :
    Continuous (laplaceTransform ν Y) :=
  (differentiable_weightedTransform hY isBoundedComplexFn_one).continuous
theorem isOpen_logDomain (hY : IsBoundedRealFamily Y) : IsOpen (logDomain ν Y) :=
  Complex.isOpen_slitPlane.preimage (continuous_laplaceTransform hY)
theorem zero_mem_logDomain : (0 : P → ℂ) ∈ logDomain ν Y := by
  simp [logDomain, laplaceTransform_zero]
theorem contDiffOn_logLaplace (hY : IsBoundedRealFamily Y) (n : ℕ) :
    ContDiffOn ℂ n (logLaplace ν Y) (logDomain ν Y) :=
  fun t ht => by
    have h : ContDiffAt ℂ n (laplaceTransform ν Y) t :=
      (contDiff_laplaceTransform hY n).contDiffAt
    exact ((Complex.contDiffAt_log ht).comp t h).contDiffWithinAt
theorem mixedCumulant_eq_iteratedFDeriv {n : ℕ} (X : Fin n → Ω → ℝ) :
    mixedCumulant ν X = iteratedFDeriv ℂ n (logLaplace ν X) 0 fun i => Pi.single i 1 := by
  have : (fun t => Complex.log (momentGeneratingFunction ν X t)) = logLaplace ν X := by
    funext t
    simp [logLaplace, laplaceTransform, weightedTransform, momentGeneratingFunction,
      linearPairing_apply]
  rw [mixedCumulant, this]
def coeffMap {n : ℕ} (c : Fin n → P → ℝ) : (Fin n → ℂ) →L[ℂ] (P → ℂ) :=
  ContinuousLinearMap.pi fun p =>
    ∑ l, (c l p : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) l
theorem coeffMap_apply {n : ℕ} (c : Fin n → P → ℝ) (t : Fin n → ℂ) (p : P) :
    coeffMap c t p = ∑ l, t l * (c l p : ℂ) := by
  simp [coeffMap, mul_comm]
theorem linearPairing_coeffMap {n : ℕ} (c : Fin n → P → ℝ) (ω : Ω) (t : Fin n → ℂ) :
    linearPairing (fun l ω => ∑ p, c l p * Y p ω) ω t = linearPairing Y ω (coeffMap c t) := by
  simp only [linearPairing_apply, coeffMap_apply]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun l _ => by ring
theorem logLaplace_linearComb {n : ℕ} (c : Fin n → P → ℝ) :
    logLaplace ν (fun l ω => ∑ p, c l p * Y p ω) = logLaplace ν Y ∘ coeffMap c := by
  funext t
  simp only [logLaplace, laplaceTransform, weightedTransform, Function.comp,
    linearPairing_coeffMap]
theorem iteratedFDeriv_logLaplace_linearComb (hY : IsBoundedRealFamily Y) {n : ℕ}
    (c : Fin n → P → ℝ) (k : ℕ) (v : Fin k → Fin n → ℂ) :
    iteratedFDeriv ℂ k (logLaplace ν fun l ω => ∑ p, c l p * Y p ω) 0 v =
      iteratedFDeriv ℂ k (logLaplace ν Y) 0 fun j => coeffMap c (v j) := by
  have hs := isOpen_logDomain (ν := ν) hY
  have hx : coeffMap c 0 ∈ logDomain ν Y := by
    simpa using zero_mem_logDomain (ν := ν) (Y := Y)
  have h := (coeffMap c).iteratedFDerivWithin_comp_right
    (contDiffOn_logLaplace (ν := ν) hY k)
    hs.uniqueDiffOn (hs.preimage (coeffMap c).continuous).uniqueDiffOn hx (i := k) le_rfl
  have h1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := logLaplace ν Y ∘ coeffMap c) k
    (hs.preimage (coeffMap c).continuous) (show (0 : Fin n → ℂ) ∈ _ from hx)
  have h2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := logLaplace ν Y) k hs hx
  rw [logLaplace_linearComb, ← h1, h, h2]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def]
theorem mixedCumulant_linearComb (hY : IsBoundedRealFamily Y) {n : ℕ} (c : Fin n → P → ℝ) :
    mixedCumulant ν (fun l ω => ∑ p, c l p * Y p ω) =
      iteratedFDeriv ℂ n (logLaplace ν Y) 0 fun l p => (c l p : ℂ) := by
  rw [mixedCumulant_eq_iteratedFDeriv, iteratedFDeriv_logLaplace_linearComb hY]
  congr 1
  funext l p
  simp [coeffMap_apply, Pi.single_apply]
theorem mixedCumulant_comp [DecidableEq P] (hY : IsBoundedRealFamily Y) {n : ℕ} (r : Fin n → P) :
    mixedCumulant ν (fun l => Y (r l)) =
      iteratedFDeriv ℂ n (logLaplace ν Y) 0 fun l => Pi.single (r l) 1 := by
  have h : (fun l => Y (r l)) =
      fun l ω => ∑ p, (if p = r l then (1 : ℝ) else 0) * Y p ω := by
    funext l ω
    simp
  rw [h, mixedCumulant_linearComb hY]
  congr 1
  funext l p
  by_cases hp : p = r l <;> simp [Pi.single_apply, hp]
theorem mixedCumulant_multilinear (hY : IsBoundedRealFamily Y) {n : ℕ} (c : Fin n → P → ℝ) :
    mixedCumulant ν (fun l ω => ∑ p, c l p * Y p ω) =
      ∑ r : Fin n → P, ((∏ l, c l (r l) : ℝ) : ℂ) * mixedCumulant ν fun l => Y (r l) := by
  classical
  rw [mixedCumulant_linearComb hY]
  have h : (fun l p => (c l p : ℂ)) =
      fun l => ∑ p, (c l p : ℂ) • (Pi.single p 1 : P → ℂ) := by
    funext l p'
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, mixedCumulant_comp hY r]
  simp
theorem isBoundedRealFamily_of_forall (h : ∀ p, IsBoundedRealRV (Y p)) :
    IsBoundedRealFamily Y := by
  choose C hC using fun p => (h p).bounded
  refine ⟨fun p => (h p).measurable, ∑ p, |C p|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun p ω => (hC p ω).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun p => |C p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p)
theorem mixedCumulant_one {X : Ω → ℝ} (hX : IsBoundedRealRV X) :
    mixedCumulant ν (fun _ : Fin 1 => X) = ((∫ ω, X ω ∂ν : ℝ) : ℂ) := by
  have hY : IsBoundedRealFamily (fun _ : Fin 1 => X) :=
    isBoundedRealFamily_of_forall fun _ => hX
  have hG := (differentiable_weightedTransform (ν := ν) hY isBoundedComplexFn_one 0).hasFDerivAt
  have hl := HasFDerivAt.clog (x := 0) hG
    (by simpa [laplaceTransform, weightedTransform] using Complex.one_mem_slitPlane)
  rw [mixedCumulant_eq_iteratedFDeriv, iteratedFDeriv_one_apply]
  have : logLaplace ν (fun _ : Fin 1 => X) = fun t =>
      Complex.log (weightedTransform ν (fun _ : Fin 1 => X) (fun _ => 1) t) := rfl
  rw [this, hl.fderiv]
  have h0 : weightedTransform ν (fun _ : Fin 1 => X) (fun _ => 1) 0 = 1 := laplaceTransform_zero
  simp only [h0, inv_one, one_smul]
  rw [fderiv_weightedTransform_apply hY isBoundedComplexFn_one]
  simp only [weightedTransform, linearPairing_apply]
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp
theorem iteratedFDeriv_laplaceTransform_zero {q : ℕ} {X : Fin q → Ω → ℝ}
    (hX : IsBoundedRealFamily X) :
    iteratedFDeriv ℂ q (laplaceTransform ν X) 0 (fun l => Pi.single l 1) =
      ((∫ ω, ∏ l, X l ω ∂ν : ℝ) : ℂ) := by
  rw [laplaceTransform, iteratedFDeriv_weightedTransform hX q isBoundedComplexFn_one]
  simp only [weightedTransform, linearPairing_apply]
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp [Pi.single_apply]
theorem iteratedFDeriv_cexp_zero (k : ℕ) (w : Fin k → ℂ) :
    iteratedFDeriv ℂ k Complex.exp 0 w = ∏ i, w i := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  have : iteratedDeriv k Complex.exp = Complex.exp := by
    rw [iteratedDeriv_eq_iterate]
    exact Function.iterate_fixed Complex.deriv_exp k
  simp [this]
theorem logLaplace_zero : logLaplace ν Y 0 = 0 := by
  simp [logLaplace, laplaceTransform_zero]
theorem iteratedFDeriv_laplaceTransform_faaDiBruno (hY : IsBoundedRealFamily Y) (q : ℕ)
    (v : Fin q → P → ℂ) :
    iteratedFDeriv ℂ q (laplaceTransform ν Y) 0 v =
      ∑ c : OrderedFinpartition q, ∏ m,
        iteratedFDeriv ℂ (c.partSize m) (logLaplace ν Y) 0 (v ∘ c.emb m) := by
  have hs := isOpen_logDomain (ν := ν) hY
  have h0 := zero_mem_logDomain (ν := ν) (Y := Y)
  have hf := (contDiffOn_logLaplace (ν := ν) hY q).ftaylorSeriesWithin hs.uniqueDiffOn
  have hg := ((Complex.contDiff_exp (𝕜 := ℂ)).contDiffOn (s := Set.univ)
    (n := q)).ftaylorSeriesWithin uniqueDiffOn_univ
  have hc := hg.comp hf (Set.mapsTo_univ _ _)
  have he := hc.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs.uniqueDiffOn h0
  have hEq : iteratedFDerivWithin ℂ q (Complex.exp ∘ logLaplace ν Y) (logDomain ν Y) 0 =
      iteratedFDeriv ℂ q (laplaceTransform ν Y) 0 := by
    rw [iteratedFDerivWithin_of_isOpen q hs h0]
    refine Filter.EventuallyEq.eq_of_nhds (Filter.EventuallyEq.iteratedFDeriv ℂ ?_ q)
    filter_upwards [hs.mem_nhds h0] with t ht
    exact Complex.exp_log (Complex.slitPlane_ne_zero ht)
  rw [← hEq, ← he]
  simp only [FormalMultilinearSeries.taylorComp, ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ftaylorSeriesWithin, logLaplace_zero, iteratedFDerivWithin_univ,
    iteratedFDeriv_cexp_zero, OrderedFinpartition.applyOrderedFinpartition_apply]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [iteratedFDerivWithin_of_isOpen _ hs h0]
theorem mixedCumulant_block_eq {q : ℕ} (X : Fin q → Ω → ℝ) (B : Finset (Fin q)) {k : ℕ}
    (hk : B.card = k) (ρ : Fin k → Fin q) (hρ : StrictMono ρ) (hm : ∀ i, ρ i ∈ B) :
    mixedCumulant ν (fun i : Fin B.card => X (B.orderEmbOfFin rfl i)) =
      mixedCumulant ν fun i => X (ρ i) := by
  subst hk
  rw [Finset.orderEmbOfFin_unique rfl hm hρ]
theorem moment_eq_sum_partitions {q : ℕ} {X : Fin q → Ω → ℝ} (hX : IsBoundedRealFamily X) :
    ((∫ ω, ∏ l, X l ω ∂ν : ℝ) : ℂ) =
      ∑ π : SourcesAndGluing.IndexPartition q, ∏ B ∈ π.parts,
        mixedCumulant ν (fun k : Fin B.card => X (B.orderEmbOfFin rfl k)) := by
  rw [← iteratedFDeriv_laplaceTransform_zero hX, iteratedFDeriv_laplaceTransform_faaDiBruno hX q]
  refine Eq.trans ?_ (sum_ordered_eq_sum_finpartition fun B =>
    mixedCumulant ν (fun k : Fin B.card => X (B.orderEmbOfFin rfl k)))
  refine Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun m _ => ?_
  rw [mixedCumulant_block_eq X (partBlock c m) (card_partBlock c m) (c.emb m)
    (c.emb_strictMono m) fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _),
    mixedCumulant_comp hX (c.emb m)]
  rfl
def shiftFunctional {n : ℕ} (b : Fin n → ℝ) : (Fin n → ℂ) →L[ℂ] ℂ :=
  ∑ l, (b l : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) l
theorem laplaceTransform_add_const {n : ℕ} (X : Fin n → Ω → ℝ) (b : Fin n → ℝ)
    (t : Fin n → ℂ) :
    laplaceTransform ν (fun l ω => X l ω + b l) t =
      Complex.exp (shiftFunctional b t) * laplaceTransform ν X t := by
  simp only [laplaceTransform, weightedTransform, one_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only
  rw [← Complex.exp_add]
  congr 1
  simp only [linearPairing_apply, shiftFunctional, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  push_cast
  ring
theorem logLaplace_add_const {n : ℕ} {X : Fin n → Ω → ℝ} (hX : IsBoundedRealFamily X)
    (b : Fin n → ℝ) :
    logLaplace ν (fun l ω => X l ω + b l) =ᶠ[𝓝 0]
      fun t => shiftFunctional b t + logLaplace ν X t := by
  have h1 : Tendsto (fun t => Complex.arg (laplaceTransform ν X t)) (𝓝 0) (𝓝 0) := by
    have := (Complex.continuousAt_arg Complex.one_mem_slitPlane).tendsto.comp
      ((continuous_laplaceTransform (ν := ν) hX).tendsto' 0 1 laplaceTransform_zero)
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun t => (shiftFunctional b t).im) (𝓝 0) (𝓝 0) := by
    have : Continuous fun t => (shiftFunctional b t).im :=
      Complex.continuous_im.comp (shiftFunctional b).continuous
    simpa using this.tendsto 0
  have hI : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [h1 hI, h2 hI, (isOpen_logDomain (ν := ν) hX).mem_nhds zero_mem_logDomain]
    with t ha hb hs
  have hpi := Real.pi_gt_three
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hlog : Complex.log (Complex.exp (shiftFunctional b t)) = shiftFunctional b t :=
    Complex.log_exp (by linarith) (by linarith)
  have harg : Complex.arg (Complex.exp (shiftFunctional b t)) = (shiftFunctional b t).im := by
    rw [← Complex.log_im, hlog]
  rw [logLaplace, laplaceTransform_add_const, (Complex.log_mul_eq_add_log_iff
    (Complex.exp_ne_zero _) (Complex.slitPlane_ne_zero hs)).2, hlog, logLaplace]
  rw [harg]
  constructor <;> linarith
theorem iteratedFDeriv_clm_eq_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : E →L[ℂ] ℂ) {n : ℕ} (hn : 2 ≤ n) : iteratedFDeriv ℂ n B 0 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  ext v
  rw [iteratedFDeriv_succ_apply_right]
  have : (fun y => fderiv ℂ B y) = fun _ => B := by
    funext y
    exact B.fderiv
  rw [this, iteratedFDeriv_const_of_ne (by omega)]
  simp
theorem mixedCumulant_add_const {n : ℕ} {X : Fin n → Ω → ℝ} (hX : IsBoundedRealFamily X)
    (b : Fin n → ℝ) (hn : 2 ≤ n) :
    mixedCumulant ν (fun l ω => X l ω + b l) = mixedCumulant ν X := by
  rw [mixedCumulant_eq_iteratedFDeriv, mixedCumulant_eq_iteratedFDeriv]
  have h := ((logLaplace_add_const (ν := ν) hX b).iteratedFDeriv ℂ n).self_of_nhds
  have hl : ContDiffAt ℂ n (logLaplace ν X) 0 :=
    (contDiffOn_logLaplace hX n).contDiffAt ((isOpen_logDomain hX).mem_nhds zero_mem_logDomain)
  have hB : ContDiffAt ℂ n (shiftFunctional b) 0 := (shiftFunctional b).contDiff.contDiffAt
  rw [h, fun_iteratedFDeriv_add_apply hB hl, iteratedFDeriv_clm_eq_zero _ hn]
  simp
theorem isBoundedRealRV_add_const {X : Ω → ℝ} (hX : IsBoundedRealRV X) (b : ℝ) :
    IsBoundedRealRV fun ω => X ω + b := by apply _root_.YangMills.Construction.Cumulants.MomentCumulantFormulas.isBoundedRealRV_add_const <;> assumption
theorem mixedCumulant_card_one {k : ℕ} (hk : k = 1) (Z : Fin k → Ω → ℝ)
    (hZ : ∀ i, IsBoundedRealRV (Z i)) (a : Fin k) :
    mixedCumulant ν Z = ((∫ ω, Z a ω ∂ν : ℝ) : ℂ) := by
  subst hk
  have : Z = fun _ => Z a := by
    funext i
    rw [Subsingleton.elim i a]
  rw [this]
  exact mixedCumulant_one (hZ a)
theorem centralMoment_eq_sum_partitions {q : ℕ} {X : Fin q → Ω → ℝ}
    (hX : ∀ l, IsBoundedRealRV (X l)) :
    ((∫ ω, ∏ l, (X l ω - ∫ ω', X l ω' ∂ν) ∂ν : ℝ) : ℂ) =
      ∑ π ∈ SourcesAndGluing.partitionsNoSingletons q, ∏ B ∈ π.parts,
        mixedCumulant ν (fun k : Fin B.card => X (B.orderEmbOfFin rfl k)) := by
  set e : Fin q → ℝ := fun l => ∫ ω', X l ω' ∂ν with he
  set X' : Fin q → Ω → ℝ := fun l ω => X l ω + -e l with hX'
  have hb : ∀ l, IsBoundedRealRV (X' l) := fun l => isBoundedRealRV_add_const (hX l) _
  have h1 := moment_eq_sum_partitions (ν := ν) (isBoundedRealFamily_of_forall hb)
  have h2 : (fun ω => ∏ l, (X l ω - ∫ ω', X l ω' ∂ν)) = fun ω => ∏ l, X' l ω := by
    funext ω
    simp only [hX', he, sub_eq_add_neg]
  rw [h2, h1]
  symm
  have hzero : ∀ π : SourcesAndGluing.IndexPartition q, π ∈ Finset.univ →
      π ∉ SourcesAndGluing.partitionsNoSingletons q →
      ∏ B ∈ π.parts, mixedCumulant ν (fun k : Fin B.card => X' (B.orderEmbOfFin rfl k)) = 0 := by
    intro π _ hπ
    simp only [SourcesAndGluing.partitionsNoSingletons, Finset.mem_filter,
      Finset.mem_univ, true_and, not_forall, not_le] at hπ
    obtain ⟨B, hB, hcard⟩ := hπ
    have hpos := Finset.card_pos.2 (π.nonempty_of_mem_parts hB)
    have h1 : B.card = 1 := by omega
    refine Finset.prod_eq_zero hB ?_
    rw [mixedCumulant_card_one h1 _ (fun i => hb _) ⟨0, hpos⟩]
    have hint : Integrable (X (B.orderEmbOfFin rfl ⟨0, hpos⟩)) ν := by
      obtain ⟨C, hC⟩ := (hX (B.orderEmbOfFin rfl ⟨0, hpos⟩)).bounded
      exact Integrable.of_bound (hX _).measurable.aestronglyMeasurable C
        (ae_of_all _ fun ω => by simpa using hC ω)
    simp only [hX', he]
    rw [integral_add hint (integrable_const _)]
    simp
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero]
  refine Finset.sum_congr rfl fun π hπ => Finset.prod_congr rfl fun B hB => ?_
  have h2B : 2 ≤ B.card := (Finset.mem_filter.1 hπ).2 B hB
  exact (mixedCumulant_add_const (ν := ν) (X := fun k : Fin B.card => X (B.orderEmbOfFin rfl k))
    (isBoundedRealFamily_of_forall fun k => hX _) (fun k => -e (B.orderEmbOfFin rfl k)) h2B).symm
theorem holds : MomentCumulantRelations.Holds := by
  intro Ω _ ν _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P _ _ Y n c hY _
    exact mixedCumulant_multilinear (isBoundedRealFamily_of_forall hY) c
  · intro X hX
    exact mixedCumulant_one hX
  · intro n X b hn hX
    exact mixedCumulant_add_const (isBoundedRealFamily_of_forall hX) b hn
  · intro q X _ hX
    exact ⟨moment_eq_sum_partitions (isBoundedRealFamily_of_forall hX),
      centralMoment_eq_sum_partitions hX⟩
end Cumulants
end YangMills.Construction.Cumulants.CumulantIdentities
end
