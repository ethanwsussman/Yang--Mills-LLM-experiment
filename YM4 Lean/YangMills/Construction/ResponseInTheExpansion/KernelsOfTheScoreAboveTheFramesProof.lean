import YangMills.Construction.ResponseInTheExpansion.KernelsOfTheScoreAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheGapAboveTheFramesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology ContDiff
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation
namespace ResponseInTheExpansion
namespace ScoreRemainderKernels
private def dilate (t : ℝ) (g : ℝ → ℝ) (p : ℝ) : ℝ := g (t * Real.exp (-p)) * Real.exp (-p)
private def dilateDerivKernel (g : ℝ → ℝ) (u : ℝ) : ℝ := -(u * deriv g u + g u)
private theorem contDiffOn_dilateDerivKernel {U : Set ℝ} (hU : IsOpen U) {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (dilateDerivKernel g) U := by
  have hd : ContDiffOn ℝ ∞ (deriv g) U := hg.deriv_of_isOpen hU (by simp)
  unfold dilateDerivKernel
  exact ((contDiffOn_id.mul hd).add hg).neg
private theorem hasDerivAt_dilate {U : Set ℝ} (hU : IsOpen U) {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g U) {t p : ℝ}
    (hu : t * Real.exp (-p) ∈ U) : HasDerivAt (dilate t g) (dilate t (dilateDerivKernel g) p) p := by
  have hd : HasDerivAt g (deriv g (t * Real.exp (-p))) (t * Real.exp (-p)) :=
    ((hg.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hu)).hasDerivAt
  have h0 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-p)) p := by
    have := (hasDerivAt_neg p).exp
    simpa using this
  have h1 : HasDerivAt (fun y : ℝ => t * Real.exp (-y)) (t * -Real.exp (-p)) p := h0.const_mul t
  have h2 := (hd.comp p h1).mul h0
  have e : dilate t (dilateDerivKernel g) p = deriv g (t * Real.exp (-p)) * (t * -Real.exp (-p)) * Real.exp (-p) +
      g (t * Real.exp (-p)) * -Real.exp (-p) := by
    unfold dilate dilateDerivKernel
    ring
  rw [e]
  exact h2
private theorem contDiffAt_dilate {U : Set ℝ} (hU : IsOpen U) {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g U) {t p : ℝ}
    (hu : t * Real.exp (-p) ∈ U) (n : ℕ) : ContDiffAt ℝ n (dilate t g) p := by
  have h0 : ContDiff ℝ n (fun y : ℝ => Real.exp (-y)) := Real.contDiff_exp.comp contDiff_neg
  have h1 : ContDiffAt ℝ n g (t * Real.exp (-p)) :=
    (hg.contDiffAt (hU.mem_nhds hu)).of_le (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℝ n (fun y : ℝ => t * Real.exp (-y)) p := (contDiff_const.mul h0).contDiffAt
  exact (h1.comp p h2).mul h0.contDiffAt
private theorem iteratedDeriv_dilate_bounded {U : Set ℝ} (hU : IsOpen U) (hsub : Set.Icc (0 : ℝ) 1 ⊆ U) (k : ℕ) :
    ∀ g : ℝ → ℝ, ContDiffOn ℝ ∞ g U → ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ p : ℝ, Real.exp (-p) ≤ 2 →
      |iteratedDeriv k (dilate t g) p| ≤ C := by
  induction k with
  | zero =>
    intro g hg
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn.mono hsub)
    refine ⟨|C| * 2, fun t ht ht2 p hp => ?_⟩
    have h0 : 0 < Real.exp (-p) := Real.exp_pos _
    have hu : t * Real.exp (-p) ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, by nlinarith⟩
    have h1 : |g (t * Real.exp (-p))| ≤ |C| :=
      (by simpa using hC _ hu : |g (t * Real.exp (-p))| ≤ C).trans (le_abs_self C)
    rw [iteratedDeriv_zero]
    unfold dilate
    rw [abs_mul, abs_of_pos h0]
    exact mul_le_mul h1 hp h0.le (abs_nonneg _)
  | succ k ih =>
    intro g hg
    obtain ⟨C, hC⟩ := ih (dilateDerivKernel g) (contDiffOn_dilateDerivKernel hU hg)
    refine ⟨C, fun t ht ht2 p hp => ?_⟩
    have h0 : 0 < Real.exp (-p) := Real.exp_pos _
    have hu : t * Real.exp (-p) ∈ U := hsub ⟨by positivity, by nlinarith⟩
    have hcont : Continuous fun y : ℝ => t * Real.exp (-y) :=
      continuous_const.mul (Real.continuous_exp.comp continuous_neg)
    have hev : deriv (dilate t g) =ᶠ[𝓝 p] dilate t (dilateDerivKernel g) := by
      filter_upwards [hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hu)] with y hy
      exact (hasDerivAt_dilate hU hg hy).deriv
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
    exact hC t ht ht2 p hp
private theorem iteratedFDeriv_comp_single_le (hF : Calculus.FaaDiBrunoAt) {n : ℕ} (g : ℝ → ℝ) (ρ : (Fin n → ℝ) → ℝ)
    (hg : ContDiffAt ℝ n g (ρ 0)) (hρ : ContDiffAt ℝ n ρ 0) (hn : 1 ≤ n) (M B r : ℝ) (w : Finset (Fin n) → ℝ)
    (hM0 : 0 ≤ M) (hB : 1 ≤ B) (hr : 0 ≤ r)
    (hM : ∀ k, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k g (ρ 0)‖ ≤ M)
    (hb : ∀ (k : ℕ) (e : Fin k → Fin n), StrictMono e → 1 ≤ k →
      |iteratedFDeriv ℝ k ρ 0 (fun i => Pi.single (e i) (1 : ℝ))| ≤
        B * Real.exp (-(r * w (Finset.univ.image e))))
    (hw : ∀ c : OrderedFinpartition n, w Finset.univ ≤ ∑ m, w (Finset.univ.image (c.emb m))) :
    |iteratedFDeriv ℝ n (g ∘ ρ) 0 (fun i => Pi.single i (1 : ℝ))| ≤
      (Fintype.card (OrderedFinpartition n) : ℝ) * (M * B ^ n * Real.exp (-(r * w Finset.univ))) := by apply _root_.YangMills.SharedProofs.p4945 <;> assumption
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
private theorem padSlots_apply_self {k n : ℕ} (e : Fin k → Fin n) (he : Function.Injective e) (σ : Fin k → ℝ) (p : Fin k) :
    padSlots e σ (e p) = σ p := by
  rw [padSlots_apply, Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [he.ne hq]
  · simp
private theorem padSlots_apply_of_not_mem {k n : ℕ} (e : Fin k → Fin n) (σ : Fin k → ℝ) (i : Fin n) (h : ∀ p, e p ≠ i) :
    padSlots e σ i = 0 := by
  rw [padSlots_apply]
  simp [h]
private theorem exists_split_of_strictMono {l j k : ℕ} (e : Fin k → Fin (l + j)) (he : StrictMono e) :
    ∃ (l' j' : ℕ) (hk : k = l' + j') (eb : Fin l' → Fin l) (ec : Fin j' → Fin j),
      Function.Injective eb ∧ Function.Injective ec ∧
      (∀ i, e (Fin.cast hk.symm (Fin.castAdd j' i)) = Fin.castAdd j (eb i)) ∧
      ∀ i, e (Fin.cast hk.symm (Fin.natAdd l' i)) = Fin.natAdd l (ec i) := by apply _root_.YangMills.SharedProofs.p26801 <;> assumption
section Kernels
variable {F : BlockFrame}
private theorem jointDisplacement_padSlots {E : Type} {l j l' j' : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → E)
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
    · have h3 : padSlots e σ (Fin.castAdd j (eb i)) = σ (Fin.castAdd j' i) := by rw [← h1, padSlots_apply_self e he]
      simp [h3]
  have hs : bondSpread c X (fun i => padSlots e σ (Fin.natAdd l i)) =
      bondSpread (c ∘ ec) (X ∘ ec) (fun i => σ (Fin.natAdd l' i)) := by
    funext y i
    unfold bondSpread
    symm
    refine Fintype.sum_of_injective ec hci _ _ (fun m hm => ?_) (fun m => ?_)
    · have h3 := padSlots_apply_of_not_mem e σ _ (offc m hm)
      simp [h3]
    · have h3 : padSlots e σ (Fin.natAdd l (ec m)) = σ (Fin.natAdd l' m) := by rw [← h2, padSlots_apply_self e he]
      simp [h3]
  simp only [jointDisplacement, zero_add, hp, hs]
private def slotCell {l j : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (c : Fin j → F.Site F.top × Fin 4) :
    Fin (l + j) → F.Cell :=
  Fin.addCases (fun i => enclosingCell (b i).1.1) (fun i => (c i).1)
private theorem iteratedFDeriv_jointDisplacement_slice (hS : SmoothSlices.IteratedFDerivSlices) {l j k : ℕ}
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
    have h3 := hS.1 (Fin (l + j) → ℝ) (Fin (l' + j') → ℝ) (jointDisplacement G η V b u c X) (padSlots e) 0 0 (l' + j')
      (fun i => Pi.single i (1 : ℝ)) hcd
    rw [jointDisplacement_padSlots G η V b u c X e hinj eb ec hbi hci h1 h2, map_zero, add_zero] at h3
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
private theorem cellSetDiameter_mono {P Q : Finset F.Cell} (h : P ⊆ Q) : cellSetDiameter P ≤ cellSetDiameter Q := by apply _root_.YangMills.SharedProofs.p30422 <;> assumption
private theorem cellSetDiameter_le_sum (hs : ∀ i, 0 < F.extent i) {n : ℕ} (hn : 1 ≤ n) (c₀ : F.Cell) (cell : Fin n → F.Cell)
    (c : OrderedFinpartition n) :
    cellSetDiameter ({c₀} ∪ (Finset.univ : Finset (Fin n)).image cell) ≤
      ∑ m, cellSetDiameter ({c₀} ∪ (Finset.univ.image (c.emb m)).image cell) := by apply _root_.YangMills.SharedProofs.p75558 <;> assumption
end Kernels
private theorem eventually_parameter_floors (Cz : ℝ → ℕ → ColdChainParameters → ℝ) :
    EventuallyInParameters fun T => 2 ≤ T.coupling ∧ 1 ≤ T.a ∧ Odd T.L ∧ 0 < T.κ ∧ 0 < T.σ ∧ 2 ≤ T.n₀ ∧
      5 * (T.L : ℝ) * (Cz T.a T.L T.chainParams * T.σ + 2 * T.ballRadius) ≤ 1 / 2 := by apply _root_.YangMills.SharedProofs.p11759 <;> assumption
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
      (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V) (displacedPoint η b u fun i => τ (Fin.castAdd j i))) c₀‖ := by apply _root_.YangMills.SharedProofs.p66855 <;> assumption
end Means
end ScoreRemainderKernels
theorem scoreRemainderKernelBounds_holds (hC : contourKernelDerivBound)
    (hT : ScaledVariables.HaarGapTailSmooth) (hF : Calculus.FaaDiBrunoAt)
    (hS : SmoothSlices.IteratedFDerivSlices) (hD : SummableBounds.interpolatedFrameDecayStatement)
    (hM : ChartShiftLipschitz) (hCC : ChartedFieldContourBound) :
    scoreRemainderKernelBoundsStatement := by
  open ScoreRemainderKernels in
  classical
  obtain ⟨D, pD, hC⟩ := hC
  obtain ⟨Cz, pCz, hD⟩ := hD
  obtain ⟨h, hsm, hpos, hlog⟩ := hT
  have hUo : IsOpen {u : ℝ | h u ≠ 0} := isOpen_ne_fun hsm.continuous continuous_const
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ {u : ℝ | h u ≠ 0} := fun u hu => (hpos u hu.1).ne'
  have hGs : ContDiffOn ℝ ∞ (fun u => -Real.log (h u)) {u : ℝ | h u ≠ 0} :=
    (hsm.contDiffOn.log (fun u hu => hu)).neg
  have hderiv : ∀ u : ℝ, 0 < u → deriv ScaledVariables.haarGapTail u = deriv (fun u => -Real.log (h u)) u := fun u hu => by
    have hev : ScaledVariables.haarGapTail =ᶠ[𝓝 u] fun u => -Real.log (h u) := by
      filter_upwards [lt_mem_nhds hu] with y hy
      exact hlog y hy.le
    exact hev.deriv_eq
  set Φ : ℝ → ℝ → ℝ := fun a u => -deriv (fun u => -Real.log (h u)) u / a ^ 2 with hΦ
  have hΦs : ∀ a, ContDiffOn ℝ ∞ (Φ a) {u : ℝ | h u ≠ 0} := fun a =>
    (hGs.deriv_of_isOpen hUo (by simp)).neg.div_const _
  have hb : ∀ a k, ∃ M : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ p : ℝ, Real.exp (-p) ≤ 2 →
      ‖iteratedFDeriv ℝ k (dilate t (Φ a)) p‖ ≤ M := fun a k => by
    obtain ⟨C, hC'⟩ := iteratedDeriv_dilate_bounded hUo hsub k (Φ a) (hΦs a)
    refine ⟨C, fun t ht ht2 p hp => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC' t ht ht2 p hp
  choose Mk hMk using hb
  set Mbar : ℝ → ℕ → ℝ := fun a n => ∑ k ∈ Finset.range (n + 1), |Mk a k| with hMbar
  set Dhat : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℝ := fun T l j =>
    1 + ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (j + 1), D T p q with hDhat
  have hMbar0 : ∀ a n, 0 ≤ Mbar a n := fun a n => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hMkle : ∀ a n k, k ≤ n → |Mk a k| ≤ Mbar a n := fun a n k hk =>
    Finset.single_le_sum (f := fun k => |Mk a k|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
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
  refine ⟨fun T l j => (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar T.a (l + j) * Dhat T l j ^ (l + j)) + 1,
    fun T l j => ?_, ?_⟩
  · have h1 := hMbar0 T.a (l + j)
    have h2 : 0 < Dhat T l j := by linarith [hDhat1 T l j]
    positivity
  refine EventuallyInParameters.mono (EventuallyInParameters.and (eventually_parameter_floors Cz)
    (EventuallyInParameters.and hD hC)) ?_
  rintro T ⟨⟨hy, ha, hLo, hκ, hσ, hn₀, hsm5⟩, gD, gC⟩ x t f F V η hx hTop hV hη c₀ l j b u c X hlj hu hX
  obtain ⟨hLF, htF, N, hN, hN₀⟩ := id hTop
  have hside : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hN i]
    omega
  have hpos' : ∀ i, 0 < F.extent i := fun i => by
    have := hside i
    omega
  have hOdd : Odd F.blockSide := hLF ▸ hLo
  have hCz : 0 ≤ Cz T.a T.L T.chainParams * T.σ := by
    have := pCz T.a T.L T.chainParams
    positivity
  have hframe : ∀ᶠ τ : Fin j → ℝ in 𝓝 0, ∀ d ∈ chordBonds (finiteCells F),
      ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) d (leftTranslate (bondSpread c X τ) V)‖ ≤
        Cz T.a T.L T.chainParams * T.σ := by
    filter_upwards [FrameCurves.eventually_isSmallCurvature hside c X hV] with τ hτ d hd
    exact (gD x t F _ 1 hx hTop hτ zero_le_one le_rfl d hd).1
  have hρ0 : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hlarge := eventually_half_le_norm_contourAverage hM hCC hOdd hside 1 T.a T.chainParams.ρA T.ballRadius
    (Cz T.a T.L T.chainParams * T.σ) (frameRadius x) V η c₀ b u c X hρ0 hη hframe hCz (by rw [hLF]; exact hsm5)
  have hA : 2 ≤ T.a * x := by nlinarith
  have hx0 : 0 < x := by linarith
  set tt : ℝ := 1 / (T.a * x) with htt
  have ht0 : 0 < tt := by positivity
  have ht2 : tt ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hA
  set G₁ : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ := fun ζ V' =>
    Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V' ζ) c₀‖ with hG₁
  set ρ := jointDisplacement G₁ η V b u c X with hρdef
  have hρ : ContDiffAt ℝ (l + j : ℕ) ρ 0 :=
    (gC x t F V 1 η hx hTop hV zero_le_one le_rfl hη c₀ l j b u c X hlj hu hX).1
  set g : ℝ → ℝ := dilate tt (Φ T.a) with hg
  have key : ∀ r : ℝ, 0 < r → (WeightedResponses.coldHalfLawAt T x f).scoreRemainder r = g (Real.log r) := fun r hr => by
    have e1 : Real.exp (-Real.log r) = r⁻¹ := by rw [Real.exp_neg, Real.exp_log hr]
    have e2 : tt * r⁻¹ = 1 / (T.a * x * r) := by
      rw [htt]
      field_simp
    show -deriv ScaledVariables.haarGapTail (1 / (T.a * x * r)) / (T.a ^ 2 * r) = g (Real.log r)
    simp only [hg, dilate, e1, e2, hΦ]
    rw [hderiv _ (by positivity)]
    field_simp
  have hev : jointDisplacement ((WeightedResponses.coldHalfLawAt T x f).scoreRemainderAt c₀) η V b u c X =ᶠ[𝓝 0] g ∘ ρ := by
    filter_upwards [hlarge] with τ hτ
    exact key _ (lt_of_lt_of_le (by norm_num) hτ)
  have h0 : Real.exp (-ρ 0) ≤ 2 := by
    have h1 := hlarge.self_of_nhds
    have e : ρ 0 = Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x)
        (leftTranslate (bondSpread c X fun i => (0 : Fin (l + j) → ℝ) (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => (0 : Fin (l + j) → ℝ) (Fin.castAdd j i))) c₀‖ := rfl
    rw [e]
    generalize ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x)
        (leftTranslate (bondSpread c X fun i => (0 : Fin (l + j) → ℝ) (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => (0 : Fin (l + j) → ℝ) (Fin.castAdd j i))) c₀‖ = r at h1
    have hr : 0 < r := by linarith
    rw [Real.exp_neg, Real.exp_log hr]
    rw [inv_le_comm₀ hr (by norm_num)]
    linarith
  have hmem : tt * Real.exp (-ρ 0) ∈ {u : ℝ | h u ≠ 0} := by
    exact hsub ⟨by positivity, by nlinarith⟩
  have hgc : ContDiffAt ℝ (l + j : ℕ) g (ρ 0) := contDiffAt_dilate hUo (hΦs T.a) hmem _
  refine ⟨(hgc.comp 0 hρ).congr_of_eventuallyEq hev, ?_⟩
  have hr0 : (0 : ℝ) ≤ 2 ^ 8 * T.κ := by positivity
  set w : Finset (Fin (l + j)) → ℝ := fun S => (cellSetDiameter ({c₀.1} ∪ S.image (slotCell b c)) : ℝ) with hw
  have hcomp := iteratedFDeriv_comp_single_le hF g ρ hgc hρ hlj (Mbar T.a (l + j)) (Dhat (rateParameters T) l j)
    (2 ^ 8 * T.κ) w (hMbar0 _ _) (hDhat1 _ _ _) hr0
    (fun k hk hkn => (hMk T.a k tt ht0 ht2 _ h0).trans ((le_abs_self _).trans (hMkle _ _ _ hkn)))
    (fun k e he hk => by
      obtain ⟨l', j', eb, ec, hl', hj', hk', heq, hmem'⟩ := iteratedFDeriv_jointDisplacement_slice hS G₁ η V b u c X e he hρ
      rw [heq]
      have h := (gC x t F V 1 η hx hTop hV zero_le_one le_rfl hη c₀ l' j' (b ∘ eb) (u ∘ eb) (c ∘ ec) (X ∘ ec) (by omega)
        (fun i => hu _) (fun i => hX _)).2
      refine h.trans (mul_le_mul (hDle _ _ _ _ _ hl' hj') (Real.exp_le_exp.2 (neg_le_neg ?_)) (Real.exp_pos _).le
        (by linarith [hDhat1 (rateParameters T) l j]))
      refine mul_le_mul_of_nonneg_left ?_ hr0
      refine Nat.cast_le.2 (cellSetDiameter_mono fun v hv => ?_)
      rcases Finset.mem_union.1 hv with h1 | h1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
      · obtain ⟨y, hy', rfl⟩ := Finset.mem_image.1 h1
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy'
        rcases Finset.mem_union.1 (hmem' p) with h2 | h2
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
        · exact Finset.mem_union_right _ h2)
    (fun cc => by
      have := cellSetDiameter_le_sum hpos' hlj c₀.1 (slotCell b c) cc
      simp only [hw]
      exact_mod_cast this)
  have hsub' : {c₀.1} ∪ chordBondCells b ∪ topBondCells c ⊆
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
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (Nat.cast_le.2 (cellSetDiameter_mono hsub')) hr0))
  have hcnt : 0 ≤ (Fintype.card (OrderedFinpartition (l + j)) : ℝ) *
      (Mbar T.a (l + j) * Dhat (rateParameters T) l j ^ (l + j)) := by
    have h1 := hMbar0 T.a (l + j)
    have h2 : 0 < Dhat (rateParameters T) l j := by linarith [hDhat1 (rateParameters T) l j]
    positivity
  unfold jointMixedDeriv
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev (l + j)).self_of_nhds]
  refine hcomp.trans ?_
  calc (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar T.a (l + j) * Dhat (rateParameters T) l j ^ (l + j) *
        Real.exp (-(2 ^ 8 * T.κ * w Finset.univ)))
      = (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar T.a (l + j) * Dhat (rateParameters T) l j ^ (l + j)) *
        Real.exp (-(2 ^ 8 * T.κ * w Finset.univ)) := by ring
    _ ≤ ((Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar T.a (l + j) * Dhat (rateParameters T) l j ^ (l + j)) + 1) *
        Real.exp (-(2 ^ 8 * T.κ * cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c))) :=
      mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by linarith)
end ResponseInTheExpansion
end YangMills.Construction
end
