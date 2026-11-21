import YangMills.Construction.ColdStepAtMirrorFrames.CurvesOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfTheGroupGap
import YangMills.Construction.ColdStepAtMirrorFrames.FaaDiBrunoAtAPoint
import YangMills.Construction.ColdStepAtMirrorFrames.SumsOverCellsAndBonds
import YangMills.Construction.SummableBoundsOfTheFlow.DecayOfTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.GroupGapHasItsTail
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheContoursAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheGapAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import YangMills.Construction.SummableBoundsOfTheFlow.TheTailOfTheGapIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Interpolation
namespace GapKernelProof
private def haarGapExp (q : ℝ) : ℝ := haarGap (Real.exp q)
private theorem contDiff_haarGapExp (hT : ScaledVariables.HaarGapTailSmooth)
    (hG : ScaledVariables.HaarGapLogTail) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) haarGapExp := by
  obtain ⟨h, hs, hp, he⟩ := hT
  have e : haarGapExp = fun q => 3 / 2 * q - Real.log (h (Real.exp (-q))) := by
    funext q
    have h1 := hG (Real.exp q) (Real.exp_pos q)
    have h2 : (0 : ℝ) ≤ 1 / Real.exp q := by positivity
    unfold haarGapExp
    rw [h1, Real.log_exp, he _ h2, one_div, ← Real.exp_neg]
    ring
  rw [e]
  refine (contDiff_const.mul contDiff_id).sub ?_
  exact ContDiff.log (hs.comp (Real.contDiff_exp.comp contDiff_neg))
    fun q => (hp _ (Real.exp_pos _).le).ne'
abbrev _root_.YangMills.DeltaSharedProofs.p501310 := @contDiff_haarGapExp
private theorem contDiffAt_haarGap (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) haarGapExp) (n : ℕ) (s : ℝ) (h0 : 0 < s) :
    ContDiffAt ℝ n haarGap s := by
  have e : haarGap =ᶠ[𝓝 s] haarGapExp ∘ Real.log := by
    filter_upwards [lt_mem_nhds h0] with u hu
    simp [haarGapExp, Real.exp_log hu]
  have h1 : ContDiffAt ℝ n haarGapExp (Real.log s) :=
    (hs.of_le (by exact_mod_cast le_top)).contDiffAt
  exact (h1.comp s (Real.contDiffAt_log.2 h0.ne')).congr_of_eventuallyEq e
abbrev _root_.YangMills.DeltaSharedProofs.p501026 := @contDiffAt_haarGap
private theorem iteratedFDeriv_exp_ones (m : ℕ) (q : ℝ) :
    iteratedFDeriv ℝ m Real.exp q (fun _ => (1 : ℝ)) = Real.exp q := by
  rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
private theorem norm_iteratedFDeriv_haarGapExp_le (hF : Calculus.FaaDiBrunoAt) (hD : HaarGapDerivBound)
    (hs : ∀ (n : ℕ) (s : ℝ), 0 < s → ContDiffAt ℝ n haarGap s) (k : ℕ) (hk : 1 ≤ k) :
    ∃ M : ℝ, ∀ q : ℝ, 0 ≤ q → ‖iteratedFDeriv ℝ k haarGapExp q‖ ≤ M := by
  choose! C hC using hD
  refine ⟨∑ c : OrderedFinpartition k, |C c.length|, fun q hq => ?_⟩
  have hs1 : 1 ≤ Real.exp q := Real.one_le_exp hq
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have e : iteratedFDeriv ℝ k haarGapExp q (fun _ => (1 : ℝ)) =
      ∑ c : OrderedFinpartition k, (Real.exp q) ^ c.length * iteratedDeriv c.length haarGap (Real.exp q) := by
    have h := hF ℝ ℝ ℝ haarGap Real.exp k q (hs k _ (Real.exp_pos q)) Real.contDiff_exp.contDiffAt (fun _ => 1)
    have h' : iteratedFDeriv ℝ k haarGapExp q (fun _ => (1 : ℝ)) =
        iteratedFDeriv ℝ k (haarGap ∘ Real.exp) q (fun _ => (1 : ℝ)) := rfl
    rw [h', h]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e1 : (fun i => iteratedFDeriv ℝ (c.partSize i) Real.exp q ((fun _ => (1 : ℝ)) ∘ c.emb i)) =
        fun _ : Fin c.length => Real.exp q • (1 : ℝ) := by
      funext i
      have := iteratedFDeriv_exp_ones (c.partSize i) q
      simpa [Function.comp_def] using this
    rw [e1]
    have e2 := (iteratedFDeriv ℝ c.length haarGap (Real.exp q)).map_smul_univ
      (fun _ => Real.exp q) (fun _ => (1 : ℝ))
    rw [e2, iteratedDeriv_eq_iteratedFDeriv]
    simp [Finset.prod_const]
  rw [e, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  exact (hC _ (c.length_pos hk) _ hs1).trans (le_abs_self _)
abbrev _root_.YangMills.DeltaSharedProofs.p502562 := @norm_iteratedFDeriv_haarGapExp_le
private theorem abs_iteratedFDeriv_comp_single_le (hF : Calculus.FaaDiBrunoAt) {n : ℕ} (g : ℝ → ℝ)
    (ρ : (Fin n → ℝ) → ℝ)
    (hg : ContDiffAt ℝ n g (ρ 0)) (hρ : ContDiffAt ℝ n ρ 0) (hn : 1 ≤ n) (M B r : ℝ) (w : Finset (Fin n) → ℝ)
    (hM0 : 0 ≤ M) (hB : 1 ≤ B) (hr : 0 ≤ r)
    (hM : ∀ k, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k g (ρ 0)‖ ≤ M)
    (hb : ∀ (k : ℕ) (e : Fin k → Fin n), StrictMono e → 1 ≤ k →
      |iteratedFDeriv ℝ k ρ 0 (fun i => Pi.single (e i) (1 : ℝ))| ≤
        B * Real.exp (-(r * w (Finset.univ.image e))))
    (hw : ∀ c : OrderedFinpartition n, w Finset.univ ≤ ∑ m, w (Finset.univ.image (c.emb m))) :
    |iteratedFDeriv ℝ n (g ∘ ρ) 0 (fun i => Pi.single i (1 : ℝ))| ≤
      (Fintype.card (OrderedFinpartition n) : ℝ) * (M * B ^ n * Real.exp (-(r * w Finset.univ))) := by
  rw [hF (Fin n → ℝ) ℝ ℝ g ρ n 0 hg hρ]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have key : ∀ c : OrderedFinpartition n,
      |iteratedFDeriv ℝ c.length g (ρ 0) fun i =>
        iteratedFDeriv ℝ (c.partSize i) ρ 0 ((fun i => Pi.single i (1 : ℝ)) ∘ c.emb i)| ≤
        M * B ^ n * Real.exp (-(r * w Finset.univ)) := by
    intro c
    set v : ∀ _ : Fin c.length, ℝ := fun i =>
      iteratedFDeriv ℝ (c.partSize i) ρ 0 ((fun i => Pi.single i (1 : ℝ)) ∘ c.emb i) with hv
    have h1 : ∀ m, ‖v m‖ ≤ B * Real.exp (-(r * w (Finset.univ.image (c.emb m)))) := fun m =>
      hb _ _ (c.emb_strictMono m) (c.partSize_pos m)
    have h2 := (iteratedFDeriv ℝ c.length g (ρ 0)).le_opNorm v
    have h3 : ‖iteratedFDeriv ℝ c.length g (ρ 0)‖ ≤ M :=
      hM _ (c.length_pos hn) c.length_le
    have h4 : ∏ m, ‖v m‖ ≤ ∏ m, (B * Real.exp (-(r * w (Finset.univ.image (c.emb m))))) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun m _ => h1 m
    have h5 : ∏ m, (B * Real.exp (-(r * w (Finset.univ.image (c.emb m))))) ≤
        B ^ n * Real.exp (-(r * w Finset.univ)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
      refine mul_le_mul (pow_le_pow_right₀ hB c.length_le) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      exact neg_le_neg (mul_le_mul_of_nonneg_left (hw c) hr)
    calc |iteratedFDeriv ℝ c.length g (ρ 0) v| = ‖iteratedFDeriv ℝ c.length g (ρ 0) v‖ := rfl
      _ ≤ ‖iteratedFDeriv ℝ c.length g (ρ 0)‖ * ∏ m, ‖v m‖ := h2
      _ ≤ M * (B ^ n * Real.exp (-(r * w Finset.univ))) :=
        mul_le_mul h3 (h4.trans h5) (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM0
      _ = M * B ^ n * Real.exp (-(r * w Finset.univ)) := by ring
  refine (Finset.sum_le_card_nsmul _ _ _ fun c _ => key c).trans (le_of_eq ?_)
  simp [Finset.card_univ, nsmul_eq_mul]
abbrev _root_.YangMills.SharedProofs.p4945 := @abs_iteratedFDeriv_comp_single_le
private def padSlots {k n : ℕ} (e : Fin k → Fin n) : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ∑ p, (ContinuousLinearMap.proj p : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (e p) (1 : ℝ))
private theorem padSlots_apply {k n : ℕ} (e : Fin k → Fin n) (σ : Fin k → ℝ) (i : Fin n) :
    padSlots e σ i = ∑ p, if e p = i then σ p else 0 := by
  simp only [padSlots, ContinuousLinearMap.sum_apply, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : e p = i
  · simp [h]
  · simp [h, Ne.symm h]
private theorem padSlots_single {k n : ℕ} (e : Fin k → Fin n) (he : Function.Injective e) (p : Fin k) :
    padSlots e (Pi.single p 1) = Pi.single (e p) 1 := by
  funext i
  rw [padSlots_apply, Finset.sum_eq_single p]
  · by_cases h : e p = i
    · simp [h]
    · simp [h, Ne.symm h]
  · intro q _ hq
    simp [hq]
  · simp
private theorem padSlots_apply_self {k n : ℕ} (e : Fin k → Fin n) (he : Function.Injective e) (σ : Fin k → ℝ)
    (p : Fin k) : padSlots e σ (e p) = σ p := by
  rw [padSlots_apply, Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [he.ne hq]
  · simp
private theorem padSlots_apply_of_not_mem {k n : ℕ} (e : Fin k → Fin n) (σ : Fin k → ℝ) (i : Fin n)
    (h : ∀ p, e p ≠ i) : padSlots e σ i = 0 := by
  rw [padSlots_apply]
  simp [h]
private theorem exists_split_of_strictMono {l j k : ℕ} (e : Fin k → Fin (l + j)) (he : StrictMono e) :
    ∃ (l' j' : ℕ) (hk : k = l' + j') (eb : Fin l' → Fin l) (ec : Fin j' → Fin j),
      Function.Injective eb ∧ Function.Injective ec ∧
      (∀ i, e (Fin.cast hk.symm (Fin.castAdd j' i)) = Fin.castAdd j (eb i)) ∧
      ∀ i, e (Fin.cast hk.symm (Fin.natAdd l' i)) = Fin.natAdd l (ec i) := by
  classical
  set A := Finset.univ.filter fun p : Fin k => (e p).1 < l with hA
  set l' := A.sup fun p => p.1 + 1 with hl'
  have hp : ∀ p : Fin k, p.1 < l' ↔ (e p).1 < l := by
    intro p
    constructor
    · intro h
      obtain ⟨q, hq, hpq⟩ := Finset.lt_sup_iff.1 h
      have hq' : (e q).1 < l := (Finset.mem_filter.1 hq).2
      have : p ≤ q := Fin.le_def.2 (by omega)
      have := he.monotone this
      exact lt_of_le_of_lt (Fin.le_def.1 this) hq'
    · intro h
      have h1 : p ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
      have h2 : p.1 + 1 ≤ l' := Finset.le_sup (f := fun p : Fin k => p.1 + 1) h1
      omega
  have hle : l' ≤ k := Finset.sup_le fun p _ => p.2
  have hk : k = l' + (k - l') := by omega
  have hn : ∀ i : Fin (k - l'), l ≤ (e ⟨l' + i.1, by omega⟩).1 := fun i => by
    by_contra h
    have := (hp _).2 (not_le.1 h)
    simp at this
  refine ⟨l', k - l', hk, fun i => ⟨(e ⟨i.1, by omega⟩).1, (hp _).1 i.2⟩,
    fun i => ⟨(e ⟨l' + i.1, by omega⟩).1 - l, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have h1 := (e ⟨l' + i.1, by omega⟩).2
    have h2 := hn i
    omega
  · intro a b hab
    have h1 : (e ⟨a.1, by omega⟩).1 = (e ⟨b.1, by omega⟩).1 := congrArg (fun z : Fin l => z.1) hab
    have h2 := he.injective (Fin.ext h1)
    exact Fin.ext (congrArg (fun z : Fin k => z.1) h2)
  · intro a b hab
    have h1 : (e ⟨l' + a.1, by omega⟩).1 - l = (e ⟨l' + b.1, by omega⟩).1 - l :=
      congrArg (fun z : Fin j => z.1) hab
    have ha := hn a
    have hb := hn b
    have h2 := he.injective (Fin.ext (by omega : (e ⟨l' + a.1, by omega⟩).1 = (e ⟨l' + b.1, by omega⟩).1))
    have h3 : l' + a.1 = l' + b.1 := congrArg (fun z : Fin k => z.1) h2
    exact Fin.ext (by omega)
  · intro i
    exact Fin.ext rfl
  · intro i
    have h2 := hn i
    refine Fin.ext ?_
    simp only [Fin.val_natAdd]
    have e1 : Fin.cast hk.symm (Fin.natAdd l' i) = ⟨l' + i.1, by omega⟩ := Fin.ext (by simp)
    rw [e1]
    omega
abbrev _root_.YangMills.SharedProofs.p26801 := @exists_split_of_strictMono
section Kernels
variable {F : BlockFrame}
private theorem jointDisplacement_comp_padSlots {E : Type} {l j l' j' : ℕ}
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → E)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions)
    (e : Fin (l' + j') → Fin (l + j)) (he : Function.Injective e) (eb : Fin l' → Fin l) (ec : Fin j' → Fin j)
    (hbi : Function.Injective eb) (hci : Function.Injective ec)
    (h1 : ∀ i, e (Fin.castAdd j' i) = Fin.castAdd j (eb i))
    (h2 : ∀ i, e (Fin.natAdd l' i) = Fin.natAdd l (ec i)) :
    (fun σ => jointDisplacement G η V b u c X (0 + padSlots e σ)) =
      jointDisplacement G η V (b ∘ eb) (u ∘ eb) (c ∘ ec) (X ∘ ec) := by
  classical
  funext σ
  have offb : ∀ i : Fin l, i ∉ Set.range eb → ∀ p, e p ≠ Fin.castAdd j i := by
    intro i hi p hp
    induction p using Fin.addCases with
    | left q =>
      rw [h1] at hp
      exact hi ⟨q, Fin.castAdd_injective _ _ hp⟩
    | right q =>
      rw [h2] at hp
      have h3 := congrArg (fun z : Fin (l + j) => z.1) hp
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h3
      have := i.2
      omega
  have offc : ∀ i : Fin j, i ∉ Set.range ec → ∀ p, e p ≠ Fin.natAdd l i := by
    intro i hi p hp
    induction p using Fin.addCases with
    | left q =>
      rw [h1] at hp
      have h3 := congrArg (fun z : Fin (l + j) => z.1) hp
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h3
      have := (eb q).2
      omega
    | right q =>
      rw [h2] at hp
      exact hi ⟨q, Fin.natAdd_injective _ _ hp⟩
  have hp : displacedPoint η b u (fun i => padSlots e σ (Fin.castAdd j i)) =
      displacedPoint η (b ∘ eb) (u ∘ eb) (fun i => σ (Fin.castAdd j' i)) := by
    unfold displacedPoint
    congr 1
    symm
    refine Fintype.sum_of_injective eb hbi _ _ (fun i hi => ?_) (fun i => ?_)
    · have h3 := padSlots_apply_of_not_mem e σ _ (offb i hi)
      simp [h3]
    · have h3 : padSlots e σ (Fin.castAdd j (eb i)) = σ (Fin.castAdd j' i) := by
        rw [← h1, padSlots_apply_self e he]
      simp [h3]
  have hs : bondSpread c X (fun i => padSlots e σ (Fin.natAdd l i)) =
      bondSpread (c ∘ ec) (X ∘ ec) (fun i => σ (Fin.natAdd l' i)) := by
    funext y i
    unfold bondSpread
    symm
    refine Fintype.sum_of_injective ec hci _ _ (fun m hm => ?_) (fun m => ?_)
    · have h3 := padSlots_apply_of_not_mem e σ _ (offc m hm)
      simp [h3]
    · have h3 : padSlots e σ (Fin.natAdd l (ec m)) = σ (Fin.natAdd l' m) := by
        rw [← h2, padSlots_apply_self e he]
      simp [h3]
  simp only [jointDisplacement, zero_add, hp, hs]
private def slotCell {l j : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (c : Fin j → F.Site F.top × Fin 4) :
    Fin (l + j) → F.Cell :=
  Fin.addCases (fun i => enclosingCell (b i).1.1) (fun i => (c i).1)
private theorem exists_slice_jointDisplacement (hS : SmoothSlices.IteratedFDerivSlices) {l j k : ℕ}
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions)
    (e : Fin k → Fin (l + j)) (he : StrictMono e)
    (hc : ContDiffAt ℝ (l + j : ℕ) (jointDisplacement G η V b u c X) 0) :
    ∃ (l' j' : ℕ) (eb : Fin l' → Fin l) (ec : Fin j' → Fin j), l' ≤ l ∧ j' ≤ j ∧ l' + j' = k ∧
      iteratedFDeriv ℝ k (jointDisplacement G η V b u c X) 0 (fun i => Pi.single (e i) (1 : ℝ)) =
        jointMixedDeriv G η V (b ∘ eb) (u ∘ eb) (c ∘ ec) (X ∘ ec) ∧
      ∀ p : Fin k, slotCell b c (e p) ∈ chordBondCells (b ∘ eb) ∪ topBondCells (c ∘ ec) := by
  classical
  obtain ⟨l', j', hk, eb, ec, hbi, hci, h1, h2⟩ := exists_split_of_strictMono e he
  subst hk
  simp only [Fin.cast_refl, id] at h1 h2
  have hinj := he.injective
  have hle : l' + j' ≤ l + j := by
    simpa using Fintype.card_le_of_injective e hinj
  refine ⟨l', j', eb, ec, by simpa using Fintype.card_le_of_injective eb hbi,
    by simpa using Fintype.card_le_of_injective ec hci, rfl, ?_, fun p => ?_⟩
  · have hcd : ContDiffAt ℝ (l' + j' : ℕ) (jointDisplacement G η V b u c X) (0 + padSlots e 0) := by
      rw [map_zero, add_zero]
      exact hc.of_le (by exact_mod_cast hle)
    have h3 := hS.1 (Fin (l + j) → ℝ) (Fin (l' + j') → ℝ) (jointDisplacement G η V b u c X) (padSlots e) 0 0
      (l' + j') (fun i => Pi.single i (1 : ℝ)) hcd
    rw [jointDisplacement_comp_padSlots G η V b u c X e hinj eb ec hbi hci h1 h2, map_zero, add_zero] at h3
    unfold jointMixedDeriv
    rw [h3]
    congr 1
    funext i
    exact (padSlots_single e hinj i).symm
  · induction p using Fin.addCases with
    | left q =>
      rw [h1]
      refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨q, Finset.mem_univ _, ?_⟩)
      simp [slotCell]
    | right q =>
      rw [h2]
      refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨q, Finset.mem_univ _, ?_⟩)
      simp [slotCell]
private theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
private theorem cellSetDiameter_mono {P Q : Finset F.Cell} (h : P ⊆ Q) : cellSetDiameter P ≤ cellSetDiameter Q :=
  Finset.sup_le fun _ hu => Finset.sup_le fun _ hv => cellSupDist_le_diameter (h hu) (h hv)
abbrev _root_.YangMills.SharedProofs.p30422 := @cellSetDiameter_mono
private theorem cellSetDiameter_le_sum (hs : ∀ i, 0 < F.extent i) {n : ℕ} (hn : 1 ≤ n) (c₀ : F.Cell)
    (cell : Fin n → F.Cell) (c : OrderedFinpartition n) :
    cellSetDiameter ({c₀} ∪ (Finset.univ : Finset (Fin n)).image cell) ≤
      ∑ m, cellSetDiameter ({c₀} ∪ (Finset.univ.image (c.emb m)).image cell) := by
  classical
  set P : Fin c.length → Finset F.Cell := fun m => {c₀} ∪ (Finset.univ.image (c.emb m)).image cell with hP
  have hz : ∀ m, c₀ ∈ P m := fun m => Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have hex : ∀ u ∈ {c₀} ∪ (Finset.univ : Finset (Fin n)).image cell, ∃ m, u ∈ P m := by
    intro u hu
    rcases Finset.mem_union.1 hu with h | h
    · rw [Finset.mem_singleton.1 h]
      exact ⟨⟨0, c.length_pos hn⟩, hz _⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      refine ⟨c.index i, Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, ?_, rfl⟩)⟩
      exact Finset.mem_image.2 ⟨c.invEmbedding i, Finset.mem_univ _, c.emb_invEmbedding i⟩
  have hone : ∀ m, cellSetDiameter (P m) ≤ ∑ m, cellSetDiameter (P m) := fun m =>
    Finset.single_le_sum (f := fun m => cellSetDiameter (P m)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  have htwo : ∀ m m', m ≠ m' → cellSetDiameter (P m) + cellSetDiameter (P m') ≤ ∑ m, cellSetDiameter (P m) := by
    intro m m' h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
    refine Nat.add_le_add_left ?_ _
    exact Finset.single_le_sum (f := fun m => cellSetDiameter (P m)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.2 ⟨h.symm, Finset.mem_univ m'⟩)
  refine Finset.sup_le fun u hu => Finset.sup_le fun v hv => ?_
  show cellSupDist u v ≤ ∑ m, cellSetDiameter (P m)
  obtain ⟨m, hm⟩ := hex u hu
  obtain ⟨m', hm'⟩ := hex v hv
  by_cases h : m = m'
  · subst h
    exact (cellSupDist_le_diameter hm hm').trans (hone m)
  · have h1 := CellSums.cellSupDist_triangle hs u c₀ v
    have h2 := cellSupDist_le_diameter hm (hz m)
    have h3 := cellSupDist_le_diameter (hz m') hm'
    have h4 := htwo m m' h
    omega
abbrev _root_.YangMills.SharedProofs.p75558 := @cellSetDiameter_le_sum
private theorem half_le_norm_contourAverage (hL : Odd F.blockSide) (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4)
    (h : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube F.blockSide →
      ‖((pathHolonomy W (refineSite c.1) (bondContour F.blockSide h π c.2) * (V c.1 c.2)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ := by
  classical
  have norm_unit : ∀ g : UnitQuaternion, ‖(g : ℍ[ℝ])‖ = 1 := fun g => by
    have h : star (g : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := Unitary.coe_star_mul_self g
    have h1 := congrArg norm h
    rw [norm_mul, Quaternion.norm_star, norm_one] at h1
    nlinarith [norm_nonneg (g : ℍ[ℝ])]
  have card_cube : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    unfold centredCube
    rw [Fintype.card_piFinset]
    have h : ∀ i : Fin 4, (Finset.Icc (-(((F.blockSide : ℤ) - 1) / 2)) (((F.blockSide : ℤ) - 1) / 2)).card =
        F.blockSide := by
      intro _
      obtain ⟨r, hr⟩ := hL
      rw [hr]
      have e : (((2 * r + 1 : ℕ) : ℤ) - 1) / 2 = r := by push_cast; omega
      rw [e, Int.card_Icc]
      omega
    rw [Finset.prod_congr rfl (fun i _ => h i)]
    simp
  set z : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) with hz
  set v : ℍ[ℝ] := (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hv
  have hnv : ‖v‖ = 1 := norm_unit _
  have hLpos : (0 : ℝ) < F.blockSide := by
    have := hL.pos
    exact_mod_cast this
  set n : ℝ := 24 * (F.blockSide : ℝ) ^ 4 with hn
  have hn0 : 0 < n := by positivity
  have hcount : ((centredCube F.blockSide).card : ℝ) * 24 = n := by
    rw [card_cube, hn]
    ring
  have hmean : _root_.YangMills.Construction.BlockAverages.contourAverage W c = (1 / n) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), z h π := rfl
  have hsum1 : ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) = n := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin]
    rw [← hcount]
    norm_num
  have e1 : _root_.YangMills.Construction.BlockAverages.contourAverage W c * v - 1 =
      (1 / n) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (z h π * v - 1) := by
    have h1 : (∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ])) = (n : ℝ) • (1 : ℍ[ℝ]) := by
      rw [← hsum1, Finset.sum_smul]
      refine Finset.sum_congr rfl fun h' _ => ?_
      rw [Finset.sum_smul]
      simp
    have h2 : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (z h π * v - 1) =
        (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), z h π) * v - (n : ℝ) • (1 : ℍ[ℝ]) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_mul]
      rw [h1]
    rw [hmean, h2, smul_sub, smul_smul, one_div, inv_mul_cancel₀ hn0.ne', one_smul, smul_mul_assoc]
  have e2 : ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v - 1‖ ≤ 1 / 2 := by
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h2 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (z h π * v - 1)‖ ≤ n * (1 / 2) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ h ∈ centredCube F.blockSide, ‖∑ π : Equiv.Perm (Fin 4), (z h π * v - 1)‖ ≤
          ∑ _π : Equiv.Perm (Fin 4), (1 / 2 : ℝ) := fun h' hh =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => h h' π hh)
      refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
      rw [← hsum1]
      simp
      ring
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 1 / n)
    have h4 : 1 / n * (n * (1 / 2)) = 1 / 2 := by field_simp
    linarith
  have e3 : ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v‖ = ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ := by rw [norm_mul, hnv, mul_one]
  have e4 : 1 - ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v‖ ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c * v - 1‖ := by
    have := norm_sub_norm_le (1 : ℍ[ℝ]) (_root_.YangMills.Construction.BlockAverages.contourAverage W c * v)
    rw [norm_one, norm_sub_rev] at this
    exact this
  linarith
end Kernels
private theorem eventually_parameter_bounds (Cz : ℝ → ℕ → ColdChainParameters → ℝ) :
    EventuallyInParameters fun T => 2 ≤ T.coupling ∧ 1 ≤ T.a ∧ Odd T.L ∧ 0 < T.κ ∧ 0 < T.σ ∧ 2 ≤ T.n₀ ∧
      5 * (T.L : ℝ) * (Cz T.a T.L T.chainParams * T.σ + 2 * T.ballRadius) ≤ 1 / 2 := by
  intro a ha
  refine ⟨0, fun L hL _ c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ hκ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ?_⟩⟩⟩⟩⟩
  refine ⟨1 / (10 * ((L : ℝ) + 1) * (|Cz a L c| + 1)), by positivity, fun σ hσ hσ' p _ =>
    ⟨0, fun Cs _ E _ => ⟨2, fun n₀ hn => ⟨0, fun CE _ => ⟨2, fun y₁ hy => ?_⟩⟩⟩⟩⟩
  refine ⟨hy, ha, hL, hκ, hσ, hn, ?_⟩
  show 5 * (L : ℝ) * (Cz a L c * σ + 2 * (σ / 64)) ≤ 1 / 2
  have h1 : σ * (10 * ((L : ℝ) + 1) * (|Cz a L c| + 1)) ≤ 1 := by
    rwa [le_div_iff₀ (by positivity)] at hσ'
  have h2 : Cz a L c * σ + 2 * (σ / 64) ≤ (|Cz a L c| + 1) * σ := by
    have := mul_le_mul_of_nonneg_right (le_abs_self (Cz a L c)) hσ.le
    nlinarith
  have h3 : 5 * (L : ℝ) * (Cz a L c * σ + 2 * (σ / 64)) ≤ 5 * (L : ℝ) * ((|Cz a L c| + 1) * σ) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 5 * (L : ℝ) * ((|Cz a L c| + 1) * σ) ≤ 5 * ((L : ℝ) + 1) * ((|Cz a L c| + 1) * σ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  nlinarith
abbrev _root_.YangMills.SharedProofs.p11759 := @eventually_parameter_bounds
section Means
variable {F : BlockFrame}
private theorem eventually_half_le_norm_contourAverage (hM : ChartShiftLipschitz) (hC : ChartedFieldContourBound)
    (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (s a ρA ρ Cσ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (c₀ : F.Site F.top × Fin 4) {l j : ℕ}
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) (hρ : 0 < ρ) (hη : ∀ b, ‖η b‖ ≤ ρ)
    (hframe : ∀ᶠ τ : Fin j → ℝ in 𝓝 0, ∀ d ∈ chordBonds (finiteCells F),
      ‖interpolatedFrame s a ρA m d (leftTranslate (bondSpread c X τ) V)‖ ≤ Cσ)
    (hC0 : 0 ≤ Cσ) (hsmall : 5 * (F.blockSide : ℝ) * (Cσ + 2 * ρ) ≤ 1 / 2) :
    ∀ᶠ τ : Fin (l + j) → ℝ in 𝓝 0, 1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s a ρA m
      (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V)
      (displacedPoint η b u fun i => τ (Fin.castAdd j i))) c₀‖ := by
  classical
  have hcont : Continuous fun τ : Fin (l + j) → ℝ => (fun i : Fin j => τ (Fin.natAdd l i)) :=
    continuous_pi fun i => continuous_apply _
  have e1 : ∀ᶠ τ : Fin (l + j) → ℝ in 𝓝 0, ∀ d ∈ chordBonds (finiteCells F),
      ‖interpolatedFrame s a ρA m d (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V)‖ ≤ Cσ :=
    (hcont.tendsto' 0 0 rfl).eventually hframe
  have hmp : Continuous fun τ : Fin (l + j) → ℝ => displacedPoint η b u fun i => τ (Fin.castAdd j i) := by
    unfold displacedPoint
    refine continuous_const.add (continuous_finsetSum _ fun i _ => ?_)
    show Continuous fun τ : Fin (l + j) → ℝ => Function.update (0 : StepVariable (finiteCells F)) (b i)
      (τ (Fin.castAdd j i) • u i)
    exact continuous_const.update _ ((continuous_apply _).smul continuous_const)
  have e2 : ∀ᶠ τ : Fin (l + j) → ℝ in 𝓝 0, ∀ d,
      ‖displacedPoint η b u (fun i => τ (Fin.castAdd j i)) d‖ ≤ 2 * ρ := by
    rw [Filter.eventually_all]
    intro d
    have h0 : ‖displacedPoint η b u (fun i => (0 : Fin (l + j) → ℝ) (Fin.castAdd j i)) d‖ < 2 * ρ := by
      have : displacedPoint η b u (fun i => (0 : Fin (l + j) → ℝ) (Fin.castAdd j i)) = η := by
        simp [displacedPoint]
      rw [this]
      linarith [hη d]
    have h1 : Continuous fun τ : Fin (l + j) → ℝ => ‖displacedPoint η b u (fun i => τ (Fin.castAdd j i)) d‖ :=
      ((continuous_apply d).comp hmp).norm
    exact (h1.continuousAt.eventually_lt continuousAt_const h0).mono fun _ h => h.le
  filter_upwards [e1, e2] with τ h1 h2
  have h3 := (hM F (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V) (fun _ _ => 0)
    (displacedPoint η b u fun i => τ (Fin.castAdd j i)) (2 * ρ) hL h2 (by positivity)).1
  refine half_le_norm_contourAverage hL _ (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V) c₀
    fun h π hh => ?_
  have h4 := hC F (interpolatedCoords s a ρA m (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V)
    (displacedPoint η b u fun i => τ (Fin.castAdd j i))) (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V)
    (Cσ + 2 * ρ) hL hs (by positivity)
    (fun d hd => (norm_add_le _ _).trans (add_le_add (h1 d hd) (h3 _ _))) c₀ h π hh
  exact h4.trans hsmall
abbrev _root_.YangMills.SharedProofs.p66855 := @eventually_half_le_norm_contourAverage
end Means
end GapKernelProof
theorem gapKernelBounds_holds (hC : contourKernelDerivBound)
    (hT : ScaledVariables.HaarGapTailSmooth) (hG : ScaledVariables.HaarGapLogTail)
    (hDG : HaarGapDerivBound) (hF : Calculus.FaaDiBrunoAt)
    (hS : SmoothSlices.IteratedFDerivSlices) (hD : SummableBounds.interpolatedFrameDecayStatement)
    (hM : ChartShiftLipschitz) (hCC : ChartedFieldContourBound) :
    gapKernelBounds := by
  open GapKernelProof in
  classical
  obtain ⟨D, pD, hC⟩ := hC
  obtain ⟨Cz, pCz, hD⟩ := hD
  have hsm := contDiff_haarGapExp hT hG
  have hgg := contDiffAt_haarGap hsm
  have hb := norm_iteratedFDeriv_haarGapExp_le hF hDG hgg
  choose! Mk hMk using hb
  set Mbar : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n + 1), |Mk k| with hMbar
  set Dhat : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℝ := fun T l j =>
    1 + ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (j + 1), D T p q with hDhat
  have hMbar0 : ∀ n, 0 ≤ Mbar n := fun n => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hMkle : ∀ n k, k ≤ n → |Mk k| ≤ Mbar n := fun n k hk =>
    Finset.single_le_sum (f := fun k => |Mk k|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  have hDhat1 : ∀ T l j, 1 ≤ Dhat T l j := fun T l j => by
    have : 0 ≤ ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (j + 1), D T p q :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => (pD _ _ _).le
    simp only [hDhat]
    linarith
  have hDle : ∀ T l j l' j', l' ≤ l → j' ≤ j → D T l' j' ≤ Dhat T l j := fun T l j l' j' h1 h2 => by
    have e1 : D T l' j' ≤ ∑ q ∈ Finset.range (j + 1), D T l' q :=
      Finset.single_le_sum (f := fun q => D T l' q) (fun _ _ => (pD _ _ _).le) (Finset.mem_range.2 (by omega))
    have e2 : ∑ q ∈ Finset.range (j + 1), D T l' q ≤
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (j + 1), D T p q :=
      Finset.single_le_sum (f := fun p => ∑ q ∈ Finset.range (j + 1), D T p q)
        (fun _ _ => Finset.sum_nonneg fun _ _ => (pD _ _ _).le) (Finset.mem_range.2 (by omega))
    simp only [hDhat]
    linarith
  refine ⟨fun T l j => (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar (l + j) * Dhat T l j ^ (l + j)) + 1,
    fun T l j => ?_, ?_⟩
  · have h1 := hMbar0 (l + j)
    have h2 : 0 < Dhat T l j := by linarith [hDhat1 T l j]
    positivity
  refine EventuallyInParameters.mono (EventuallyInParameters.and (eventually_parameter_bounds Cz)
    (EventuallyInParameters.and hD hC)) ?_
  rintro T ⟨⟨hy, ha, hLo, hκ, hσ, hn₀, hsm5⟩, gD, gC⟩ x t F V s η hx hTop hV hs hs' hη c₀ l j b u c X hlj hu hX
  obtain ⟨hLF, htF, N, hN, hN₀⟩ := id hTop
  have hside : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hN i]
    omega
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hside i
    omega
  have hOdd : Odd F.blockSide := hLF ▸ hLo
  have hCz : 0 ≤ Cz T.a T.L T.chainParams * T.σ := by
    have := pCz T.a T.L T.chainParams
    positivity
  have hframe : ∀ᶠ τ : Fin j → ℝ in 𝓝 0, ∀ d ∈ chordBonds (finiteCells F),
      ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) d (leftTranslate (bondSpread c X τ) V)‖ ≤
        Cz T.a T.L T.chainParams * T.σ := by
    filter_upwards [FrameCurves.eventually_isSmallCurvature hside c X hV] with τ hτ d hd
    exact (gD x t F _ s hx hTop hτ hs hs' d hd).1
  have hρ0 : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hlarge := eventually_half_le_norm_contourAverage hM hCC hOdd hside s T.a T.chainParams.ρA T.ballRadius
    (Cz T.a T.L T.chainParams * T.σ) (frameRadius x) V η c₀ b u c X hρ0 hη hframe hCz (by rw [hLF]; exact hsm5)
  have hA : 2 ≤ T.a * x := by nlinarith
  have hA0 : 0 < T.a * x := by linarith
  set G₁ : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ := fun ζ V' =>
    Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V' ζ) c₀‖ with hG₁
  set ρ := jointDisplacement G₁ η V b u c X with hρdef
  have hρ : ContDiffAt ℝ (l + j : ℕ) ρ 0 := (gC x t F V s η hx hTop hV hs hs' hη c₀ l j b u c X hlj hu hX).1
  set g : ℝ → ℝ := fun p => haarGapExp (p + Real.log (T.a * x)) with hg
  have hev : jointDisplacement (fun ζ V' => haarGap (T.a * x *
      ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V' ζ) c₀‖)) η V b u c X =ᶠ[𝓝 0]
        g ∘ ρ := by
    filter_upwards [hlarge] with τ hτ
    show haarGap (T.a * x * ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s T.a T.chainParams.ρA (frameRadius x)
        (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => τ (Fin.castAdd j i))) c₀‖) =
      haarGapExp (Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s T.a T.chainParams.ρA (frameRadius x)
        (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => τ (Fin.castAdd j i))) c₀‖ + Real.log (T.a * x))
    generalize ‖contourAverage (interpolatedField s T.a T.chainParams.ρA (frameRadius x)
        (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => τ (Fin.castAdd j i))) c₀‖ = r at hτ
    have hr : 0 < r := by linarith
    unfold haarGapExp
    rw [Real.exp_add, Real.exp_log hr, Real.exp_log hA0, mul_comm]
  have h0 : 0 ≤ ρ 0 + Real.log (T.a * x) := by
    have h1 := hlarge.self_of_nhds
    have e : ρ 0 = Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s T.a T.chainParams.ρA (frameRadius x)
        (leftTranslate (bondSpread c X fun i => (0 : Fin (l + j) → ℝ) (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => (0 : Fin (l + j) → ℝ) (Fin.castAdd j i))) c₀‖ := rfl
    rw [e]
    generalize ‖contourAverage (interpolatedField s T.a T.chainParams.ρA (frameRadius x)
        (leftTranslate (bondSpread c X fun i => (0 : Fin (l + j) → ℝ) (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => (0 : Fin (l + j) → ℝ) (Fin.castAdd j i))) c₀‖ = r at h1
    have hr : 0 < r := by linarith
    rw [← Real.log_mul hr.ne' hA0.ne']
    exact Real.log_nonneg (by nlinarith)
  have hgc : ContDiffAt ℝ (l + j : ℕ) g (ρ 0) :=
    ((hsm.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)).contDiffAt
  refine ⟨(hgc.comp 0 hρ).congr_of_eventuallyEq hev, ?_⟩
  have hr0 : (0 : ℝ) ≤ 2 ^ 8 * T.κ := by positivity
  set w : Finset (Fin (l + j)) → ℝ := fun S => (cellSetDiameter ({c₀.1} ∪ S.image (slotCell b c)) : ℝ) with hw
  have hcomp := abs_iteratedFDeriv_comp_single_le hF g ρ hgc hρ hlj (Mbar (l + j)) (Dhat (rateParameters T) l j)
    (2 ^ 8 * T.κ) w (hMbar0 _) (hDhat1 _ _ _) hr0
    (fun k hk hkn => by
      have e : iteratedFDeriv ℝ k g (ρ 0) = iteratedFDeriv ℝ k haarGapExp (ρ 0 + Real.log (T.a * x)) :=
        iteratedFDeriv_comp_add_right k (Real.log (T.a * x)) (ρ 0)
      rw [e]
      exact (hMk k hk _ h0).trans ((le_abs_self _).trans (hMkle _ _ hkn)))
    (fun k e he hk => by
      obtain ⟨l', j', eb, ec, hl', hj', hk', heq, hmem⟩ := exists_slice_jointDisplacement hS G₁ η V b u c X e he hρ
      rw [heq]
      have h := (gC x t F V s η hx hTop hV hs hs' hη c₀ l' j' (b ∘ eb) (u ∘ eb) (c ∘ ec) (X ∘ ec) (by omega)
        (fun i => hu _) (fun i => hX _)).2
      refine h.trans (mul_le_mul (hDle _ _ _ _ _ hl' hj') (Real.exp_le_exp.2 (neg_le_neg ?_)) (Real.exp_pos _).le
        (by linarith [hDhat1 (rateParameters T) l j]))
      refine mul_le_mul_of_nonneg_left ?_ hr0
      refine Nat.cast_le.2 (cellSetDiameter_mono fun v hv => ?_)
      rcases Finset.mem_union.1 hv with h1 | h1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
      · obtain ⟨y, hy', rfl⟩ := Finset.mem_image.1 h1
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy'
        rcases Finset.mem_union.1 (hmem p) with h2 | h2
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
        · exact Finset.mem_union_right _ h2)
    (fun cc => by
      have := cellSetDiameter_le_sum hpos hlj c₀.1 (slotCell b c) cc
      simp only [hw]
      exact_mod_cast this)
  have hsub : {c₀.1} ∪ chordBondCells b ∪ topBondCells c ⊆
      {c₀.1} ∪ (Finset.univ : Finset (Fin (l + j))).image (slotCell b c) := by
    intro v hv
    rcases Finset.mem_union.1 hv with h1 | h1
    · rcases Finset.mem_union.1 h1 with h2 | h2
      · exact Finset.mem_union_left _ h2
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h2
        refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨Fin.castAdd j i, Finset.mem_univ _, ?_⟩)
        simp [slotCell]
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h1
      refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨Fin.natAdd l i, Finset.mem_univ _, ?_⟩)
      simp [slotCell]
  have hexp : Real.exp (-(2 ^ 8 * T.κ * w Finset.univ)) ≤
      Real.exp (-(2 ^ 8 * T.κ * cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c))) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (Nat.cast_le.2 (cellSetDiameter_mono hsub)) hr0))
  have hcnt : 0 ≤ (Fintype.card (OrderedFinpartition (l + j)) : ℝ) *
      (Mbar (l + j) * Dhat (rateParameters T) l j ^ (l + j)) := by
    have h1 := hMbar0 (l + j)
    have h2 : 0 < Dhat (rateParameters T) l j := by linarith [hDhat1 (rateParameters T) l j]
    positivity
  unfold jointMixedDeriv
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev (l + j)).self_of_nhds]
  refine hcomp.trans ?_
  calc (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar (l + j) * Dhat (rateParameters T) l j ^ (l + j) *
        Real.exp (-(2 ^ 8 * T.κ * w Finset.univ)))
      = (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar (l + j) * Dhat (rateParameters T) l j ^ (l + j)) *
        Real.exp (-(2 ^ 8 * T.κ * w Finset.univ)) := by ring
    _ ≤ ((Fintype.card (OrderedFinpartition (l + j)) : ℝ) *
          (Mbar (l + j) * Dhat (rateParameters T) l j ^ (l + j)) + 1) *
        Real.exp (-(2 ^ 8 * T.κ * cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c))) :=
      mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by linarith)
end YangMills.Construction.Interpolation
end
