import YangMills.Construction.RunningCouplingSlope.ContoursAboveGivenFrames
import YangMills.Construction.RunningCouplingSlope.GapAboveGivenFrames
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheGapAboveTheFramesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open ColdStepAtMirrorFrames Interpolation
open BlockAverages hiding bondSpread
namespace RunningCouplingSlope
namespace HaarGapOfAverageSteps
private def haarGapExp (q : ℝ) : ℝ := haarGap (Real.exp q)
private theorem haarGapExp_contDiff (hT : ScaledVariables.HaarGapTailSmooth)
    (hG : ScaledVariables.HaarGapLogTail) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) haarGapExp := by apply _root_.YangMills.DeltaSharedProofs.p501310 <;> assumption
private theorem haarGap_contDiffAt (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) haarGapExp) (n : ℕ) (s : ℝ) (h0 : 0 < s) :
    ContDiffAt ℝ n haarGap s := by apply _root_.YangMills.DeltaSharedProofs.p501026 <;> assumption
private theorem iteratedFDeriv_exp_ones (m : ℕ) (q : ℝ) :
    iteratedFDeriv ℝ m Real.exp q (fun _ => (1 : ℝ)) = Real.exp q := by
  rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
private theorem haarGapExp_iteratedFDeriv_bounded (hF : Calculus.FaaDiBrunoAt) (hD : HaarGapDerivBound)
    (hs : ∀ (n : ℕ) (s : ℝ), 0 < s → ContDiffAt ℝ n haarGap s) (k : ℕ) (hk : 1 ≤ k) :
    ∃ M : ℝ, ∀ q : ℝ, 0 ≤ q → ‖iteratedFDeriv ℝ k haarGapExp q‖ ≤ M := by apply _root_.YangMills.DeltaSharedProofs.p502562 <;> assumption
private theorem abs_iteratedFDeriv_comp_le (hF : Calculus.FaaDiBrunoAt) {n : ℕ} (g : ℝ → ℝ) (ρ : (Fin n → ℝ) → ℝ)
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
      ∀ i, e (Fin.cast hk.symm (Fin.natAdd l' i)) = Fin.natAdd l (ec i) := by apply _root_.YangMills.SharedProofs.p26801 <;> assumption
section Kernels
variable {F : BlockFrame}
private theorem jointDisplacement_padSlots {E : Type} {l j l' j' : ℕ}
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
    have h3 := hS.1 (Fin (l + j) → ℝ) (Fin (l' + j') → ℝ) (jointDisplacement G η V b u c X) (padSlots e) 0 0
      (l' + j') (fun i => Pi.single i (1 : ℝ)) hcd
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
private theorem cellSetDiameter_le_sum (hs : ∀ i, 0 < F.extent i) {n : ℕ} (hn : 1 ≤ n) (c₀ : F.Cell)
    (cell : Fin n → F.Cell) (c : OrderedFinpartition n) :
    cellSetDiameter ({c₀} ∪ (Finset.univ : Finset (Fin n)).image cell) ≤
      ∑ m, cellSetDiameter ({c₀} ∪ (Finset.univ.image (c.emb m)).image cell) := by apply _root_.YangMills.SharedProofs.p75558 <;> assumption
end Kernels
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
      (displacedPoint η b u fun i => τ (Fin.castAdd j i))) c₀‖ := by apply _root_.YangMills.SharedProofs.p66855 <;> assumption
end Means
end HaarGapOfAverageSteps
theorem haarGapOfAverageDerivBounds_holds (hC : logContourDerivBounds)
    (hT : ScaledVariables.HaarGapTailSmooth) (hG : ScaledVariables.HaarGapLogTail)
    (hDG : HaarGapDerivBound) (hF : Calculus.FaaDiBrunoAt)
    (hS : SmoothSlices.IteratedFDerivSlices)
    (hM : ChartShiftLipschitz) (hCC : ChartedFieldContourBound) :
    HaarGapOfAverageDerivBounds := by
  open HaarGapOfAverageSteps in
  classical
  intro K r κ L hK hκ0 hκ hLo
  obtain ⟨D, pD, hC⟩ := hC K r κ L hK hκ0 hκ hLo
  have hsm := haarGapExp_contDiff hT hG
  have hgg := haarGap_contDiffAt hsm
  have hb := haarGapExp_iteratedFDeriv_bounded hF hDG hgg
  choose! Mk hMk using hb
  set Mbar : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n + 1), |Mk k| with hMbar
  set Dhat : ℕ → ℕ → ℝ := fun l j =>
    1 + ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (j + 1), D p q with hDhat
  have hMbar0 : ∀ n, 0 ≤ Mbar n := fun n => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hMkle : ∀ n k, k ≤ n → |Mk k| ≤ Mbar n := fun n k hk =>
    Finset.single_le_sum (f := fun k => |Mk k|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  have hDhat1 : ∀ l j, 1 ≤ Dhat l j := fun l j => by
    have : 0 ≤ ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (j + 1), D p q :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => (pD _ _).le
    simp only [hDhat]
    linarith
  have hDle : ∀ l j l' j', l' ≤ l → j' ≤ j → D l' j' ≤ Dhat l j := fun l j l' j' h1 h2 => by
    have e1 : D l' j' ≤ ∑ q ∈ Finset.range (j + 1), D l' q :=
      Finset.single_le_sum (f := fun q => D l' q) (fun _ _ => (pD _ _).le) (Finset.mem_range.2 (by omega))
    have e2 : ∑ q ∈ Finset.range (j + 1), D l' q ≤
        ∑ p ∈ Finset.range (l + 1), ∑ q ∈ Finset.range (j + 1), D p q :=
      Finset.single_le_sum (f := fun p => ∑ q ∈ Finset.range (j + 1), D p q)
        (fun _ _ => Finset.sum_nonneg fun _ _ => (pD _ _).le) (Finset.mem_range.2 (by omega))
    simp only [hDhat]
    linarith
  refine ⟨fun l j => (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar (l + j) * Dhat l j ^ (l + j)) + 1,
    fun l j => ?_, ?_⟩
  · have h1 := hMbar0 (l + j)
    have h2 : 0 < Dhat l j := by linarith [hDhat1 l j]
    positivity
  intro F s a ρA x ρ' ε m V η hLF hcub hax hρ0 hε0 hsm5 hη hfr han hdec c₀ l j b u c X hlj hu hX
  obtain ⟨N, hN₀, hN⟩ := id hcub
  have hside : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hN i]
    omega
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hside i
    omega
  have hOdd : Odd F.blockSide := hLF ▸ hLo
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLo.pos
  have hLR : (F.blockSide : ℝ) = L := by exact_mod_cast hLF
  have hframe := hfr j c X
  have hlarge := eventually_half_le_norm_contourAverage hM hCC hOdd hside s a ρA ρ' ε m V η c₀ b u c X hρ0 hη
    hframe hε0 (by rw [hLR]; nlinarith)
  have hchart0 : ∀ d ∈ chordBonds (finiteCells F), ‖interpolatedFrame s a ρA m d V‖ ≤ ε := by
    have h0 := (hfr 0 Fin.elim0 Fin.elim0).self_of_nhds
    intro d hd
    have e : leftTranslate (bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions) (0 : Fin 0 → ℝ)) V = V := by
      have h0 : expUnit (0 : imaginaryQuaternions) = 1 := by
        apply Subtype.ext
        simp [expUnit]
      funext y i
      simp [leftTranslate, bondSpread, h0]
    have h1 := h0 d hd
    rwa [e] at h1
  have hcoord := (hM F V (interpolatedCoords s a ρA m V η) η ρ' hOdd hη hρ0.le).1
  have hsize : ∀ d ∈ chordBonds (finiteCells F), ‖interpolatedCoords s a ρA m V η d.1 d.2‖ ≤ ε + ρ' :=
    fun d hd => (norm_add_le _ _).trans (add_le_add (hchart0 d hd) (hcoord _ _))
  have gC := fun (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
      (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) (hlj : 1 ≤ l + j)
      (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) =>
    hC F s a ρA (ε + ρ') m V η hLF hcub (by positivity) (by nlinarith) hsize han hdec c₀ l j b u c X hlj hu hX
  have hA : 2 ≤ a * x := hax
  have hA0 : 0 < a * x := by linarith
  set G₁ : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ := fun ζ V' =>
    Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s a ρA m V' ζ) c₀‖ with hG₁
  set ρ := jointDisplacement G₁ η V b u c X with hρdef
  have hρ : ContDiffAt ℝ (l + j : ℕ) ρ 0 := (gC l j b u c X hlj hu hX).1
  set g : ℝ → ℝ := fun p => haarGapExp (p + Real.log (a * x)) with hg
  have hev : jointDisplacement (fun ζ V' => haarGap (a * x *
      ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s a ρA m V' ζ) c₀‖)) η V b u c X =ᶠ[𝓝 0] g ∘ ρ := by
    filter_upwards [hlarge] with τ hτ
    show haarGap (a * x * ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s a ρA m
        (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => τ (Fin.castAdd j i))) c₀‖) =
      haarGapExp (Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s a ρA m
        (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => τ (Fin.castAdd j i))) c₀‖ + Real.log (a * x))
    generalize ‖contourAverage (interpolatedField s a ρA m
        (leftTranslate (bondSpread c X fun i => τ (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => τ (Fin.castAdd j i))) c₀‖ = r at hτ
    have hr : 0 < r := by linarith
    unfold haarGapExp
    rw [Real.exp_add, Real.exp_log hr, Real.exp_log hA0, mul_comm]
  have h0 : 0 ≤ ρ 0 + Real.log (a * x) := by
    have h1 := hlarge.self_of_nhds
    have e : ρ 0 = Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField s a ρA m
        (leftTranslate (bondSpread c X fun i => (0 : Fin (l + j) → ℝ) (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => (0 : Fin (l + j) → ℝ) (Fin.castAdd j i))) c₀‖ := rfl
    rw [e]
    generalize ‖contourAverage (interpolatedField s a ρA m
        (leftTranslate (bondSpread c X fun i => (0 : Fin (l + j) → ℝ) (Fin.natAdd l i)) V)
        (displacedPoint η b u fun i => (0 : Fin (l + j) → ℝ) (Fin.castAdd j i))) c₀‖ = r at h1
    have hr : 0 < r := by linarith
    rw [← Real.log_mul hr.ne' hA0.ne']
    exact Real.log_nonneg (by nlinarith)
  have hgc : ContDiffAt ℝ (l + j : ℕ) g (ρ 0) :=
    ((hsm.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)).contDiffAt
  refine ⟨(hgc.comp 0 hρ).congr_of_eventuallyEq hev, ?_⟩
  have hr0 : (0 : ℝ) ≤ 2 ^ 8 * κ := by positivity
  set w : Finset (Fin (l + j)) → ℝ := fun S => (cellSetDiameter ({c₀.1} ∪ S.image (slotCell b c)) : ℝ) with hw
  have hcomp := abs_iteratedFDeriv_comp_le hF g ρ hgc hρ hlj (Mbar (l + j)) (Dhat l j) (2 ^ 8 * κ) w
    (hMbar0 _) (hDhat1 _ _) hr0
    (fun k hk hkn => by
      have e : iteratedFDeriv ℝ k g (ρ 0) = iteratedFDeriv ℝ k haarGapExp (ρ 0 + Real.log (a * x)) :=
        iteratedFDeriv_comp_add_right k (Real.log (a * x)) (ρ 0)
      rw [e]
      exact (hMk k hk _ h0).trans ((le_abs_self _).trans (hMkle _ _ hkn)))
    (fun k e he hk => by
      obtain ⟨l', j', eb, ec, hl', hj', hk', heq, hmem⟩ :=
        iteratedFDeriv_jointDisplacement_slice hS G₁ η V b u c X e he hρ
      rw [heq]
      have h := (gC l' j' (b ∘ eb) (u ∘ eb) (c ∘ ec) (X ∘ ec) (by omega)
        (fun i => hu _) (fun i => hX _)).2
      refine h.trans (mul_le_mul (hDle _ _ _ _ hl' hj') (Real.exp_le_exp.2 (neg_le_neg ?_)) (Real.exp_pos _).le
        (by linarith [hDhat1 l j]))
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
  have hexp : Real.exp (-(2 ^ 8 * κ * w Finset.univ)) ≤
      Real.exp (-(2 ^ 8 * κ * cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c))) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (Nat.cast_le.2 (cellSetDiameter_mono hsub)) hr0))
  have hcnt : 0 ≤ (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar (l + j) * Dhat l j ^ (l + j)) := by
    have h1 := hMbar0 (l + j)
    have h2 : 0 < Dhat l j := by linarith [hDhat1 l j]
    positivity
  unfold jointMixedDeriv
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev (l + j)).self_of_nhds]
  refine hcomp.trans ?_
  calc (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar (l + j) * Dhat l j ^ (l + j) *
        Real.exp (-(2 ^ 8 * κ * w Finset.univ)))
      = (Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar (l + j) * Dhat l j ^ (l + j)) *
        Real.exp (-(2 ^ 8 * κ * w Finset.univ)) := by ring
    _ ≤ ((Fintype.card (OrderedFinpartition (l + j)) : ℝ) * (Mbar (l + j) * Dhat l j ^ (l + j)) + 1) *
        Real.exp (-(2 ^ 8 * κ * cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c))) :=
      mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by linarith)
end RunningCouplingSlope
end YangMills.Construction
end
