import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.HaarExcessNearZero
import YangMills.Construction.ColdStepAtMirrorFrames.HaarsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorus
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenStayNear
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace HaarDensities
private def toImaginaryCLM : BondVector →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => toImaginary v
      map_add' := fun u v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = 0 + 0
          simp
        · change (u + v) 0 = u 0 + v 0
          simp
        · change (u + v) 1 = u 1 + v 1
          simp
        · change (u + v) 2 = u 2 + v 2
          simp
      map_smul' := fun c v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = c * 0
          simp
        · change (c • v) 0 = c * v 0
          simp
        · change (c • v) 1 = c * v 1
          simp
        · change (c • v) 2 = c * v 2
          simp }
private theorem toImaginaryCLM_apply (v : BondVector) : toImaginaryCLM v = toImaginary v := rfl
private theorem norm_toImaginaryCLM (v : BondVector) : ‖toImaginaryCLM v‖ = ‖v‖ := by
  have h1 : ‖toImaginaryCLM v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := Quaternion.normSq_eq_norm_mul_self ((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])
    rw [Quaternion.normSq_def'] at h
    have h2 : ‖(toImaginaryCLM v : imaginaryQuaternions)‖ = ‖((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
    rw [h2, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, pow_two]
    simp only [toImaginaryCLM_apply, toImaginary, Real.norm_eq_abs, sq_abs] at h ⊢
    linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
private def LogRatioDerivBounds (C : ℝ) : Prop :=
  ∀ v : imaginaryQuaternions, ‖v‖ ≤ 1 → ContDiffAt ℝ 3 haarLogRatio v ∧
    (∀ e : imaginaryQuaternions, |fderiv ℝ haarLogRatio v e| ≤ C * ‖e‖) ∧
    ∀ e e' : imaginaryQuaternions, |fderiv ℝ (fun z => fderiv ℝ haarLogRatio z e) v e'| ≤ C * ‖e‖ * ‖e'‖
private theorem logRatio_lipschitz {C : ℝ} (hC : 0 < C) (hH : LogRatioDerivBounds C)
    {u u' : imaginaryQuaternions} (hu : ‖u‖ ≤ 1)
    (hu' : ‖u'‖ ≤ 1) : |haarLogRatio u' - haarLogRatio u| ≤ C * ‖u' - u‖ := by
  have hs : Convex ℝ (Metric.closedBall (0 : imaginaryQuaternions) 1) := convex_closedBall _ _
  have hm : ∀ {v : imaginaryQuaternions}, ‖v‖ ≤ 1 → v ∈ Metric.closedBall (0 : imaginaryQuaternions) 1 :=
    fun hv => by simpa using hv
  have hn : ∀ {v : imaginaryQuaternions}, v ∈ Metric.closedBall (0 : imaginaryQuaternions) 1 → ‖v‖ ≤ 1 :=
    fun hv => by simpa using hv
  have := hs.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := haarLogRatio) (C := C)
    (fun v hv => ((hH v (hn hv)).1).differentiableAt (by norm_num))
    (fun v hv => ContinuousLinearMap.opNorm_le_bound _ hC.le fun e => by
      simpa using (hH v (hn hv)).2.1 e) (hm hu) (hm hu')
  simpa using this
private theorem fderiv_logRatio_lipschitz {C : ℝ} (hC : 0 < C) (hH : LogRatioDerivBounds C)
    {u u' : imaginaryQuaternions} (hu : ‖u‖ ≤ 1)
    (hu' : ‖u'‖ ≤ 1) : ‖fderiv ℝ haarLogRatio u' - fderiv ℝ haarLogRatio u‖ ≤ C * ‖u' - u‖ := by
  have hs : Convex ℝ (Metric.closedBall (0 : imaginaryQuaternions) 1) := convex_closedBall _ _
  have hm : ∀ {v : imaginaryQuaternions}, ‖v‖ ≤ 1 → v ∈ Metric.closedBall (0 : imaginaryQuaternions) 1 :=
    fun hv => by simpa using hv
  have hn : ∀ {v : imaginaryQuaternions}, v ∈ Metric.closedBall (0 : imaginaryQuaternions) 1 → ‖v‖ ≤ 1 :=
    fun hv => by simpa using hv
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
  have hdiff : ∀ v ∈ Metric.closedBall (0 : imaginaryQuaternions) 1,
      DifferentiableAt ℝ (fun z => fderiv ℝ haarLogRatio z e) v := by
    intro v hv
    have h2 : ContDiffAt ℝ 2 (fderiv ℝ haarLogRatio) v := (hH v (hn hv)).1.fderiv_right (by norm_num)
    exact (h2.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  have := hs.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun z => fderiv ℝ haarLogRatio z e)
    (C := C * ‖e‖) hdiff
    (fun v hv => ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e' => by
      simpa using (hH v (hn hv)).2.2 e e') (hm hu) (hm hu')
  calc ‖(fderiv ℝ haarLogRatio u' - fderiv ℝ haarLogRatio u) e‖
      = ‖fderiv ℝ haarLogRatio u' e - fderiv ℝ haarLogRatio u e‖ := rfl
    _ ≤ C * ‖e‖ * ‖u' - u‖ := this
    _ = C * ‖u' - u‖ * ‖e‖ := by ring
set_option linter.unusedSectionVars false
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem hasFDerivAt_logRatio_affine {u : imaginaryQuaternions} {A : BondField ι →L[ℝ] imaginaryQuaternions}
    {ξ : BondField ι} (hd : DifferentiableAt ℝ haarLogRatio (u + A ξ)) :
    HasFDerivAt (fun ζ => haarLogRatio (u + A ζ)) ((fderiv ℝ haarLogRatio (u + A ξ)).comp A) ξ :=
  HasFDerivAt.comp (g := haarLogRatio) (f := fun ζ => u + A ζ) ξ hd.hasFDerivAt (A.hasFDerivAt.const_add u)
private def logRatioDiffSum {P : Type} (S : Finset P) (w w' : P → imaginaryQuaternions)
    (R : P → BondField ι →L[ℝ] BondVector) (ξ : BondField ι) : ℝ :=
  ∑ p ∈ S, (haarLogRatio (w' p + (toImaginaryCLM.comp (R p)) ξ) - haarLogRatio (w p + (toImaginaryCLM.comp (R p)) ξ))
private theorem logRatioDiffSum_bounds {C ρ Θ : ℝ} (hC : 0 < C) (hH : LogRatioDerivBounds C) {P : Type}
    (S : Finset P) (w w' : P → imaginaryQuaternions) (R : P → BondField ι →L[ℝ] BondVector)
    (hw : ∀ p ∈ S, ‖w p‖ + ρ ≤ 1) (hw' : ∀ p ∈ S, ‖w' p‖ + ρ ≤ 1)
    (hR : ∀ p ∈ S, ∀ ξ ∈ openPolyball ι ρ, ‖R p ξ‖ ≤ ρ) (hθ : ∀ p ∈ S, ‖w' p - w p‖ ≤ Θ) :
    ContDiffOn ℝ 1 (logRatioDiffSum S w w' R) (openPolyball ι ρ) ∧
    (∀ ξ ∈ openPolyball ι ρ, |logRatioDiffSum S w w' R ξ| ≤ S.card * (C * Θ)) ∧
    ∀ ξ ∈ openPolyball ι ρ, ∀ k : ι, bondGradNorm (logRatioDiffSum S w w' R) k ξ ≤
      ∑ p ∈ S, C * Θ * ‖(R p).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) k)‖ := by
  have hball : ∀ p ∈ S, ∀ ξ ∈ openPolyball ι ρ, ‖w p + (toImaginaryCLM.comp (R p)) ξ‖ ≤ 1 ∧
      ‖w' p + (toImaginaryCLM.comp (R p)) ξ‖ ≤ 1 := by
    intro p hp ξ hξ
    have h1 : ‖(toImaginaryCLM.comp (R p)) ξ‖ ≤ ρ := by
      change ‖toImaginaryCLM (R p ξ)‖ ≤ ρ
      rw [norm_toImaginaryCLM]
      exact hR p hp ξ hξ
    exact ⟨(norm_add_le _ _).trans (by linarith [hw p hp]), (norm_add_le _ _).trans (by linarith [hw' p hp])⟩
  have hc : ∀ p ∈ S, ∀ ξ ∈ openPolyball ι ρ,
      ContDiffAt ℝ 1 (fun ζ => haarLogRatio (w' p + (toImaginaryCLM.comp (R p)) ζ) -
        haarLogRatio (w p + (toImaginaryCLM.comp (R p)) ζ)) ξ := by
    intro p hp ξ hξ
    obtain ⟨h1, h2⟩ := hball p hp ξ hξ
    have e1 : ContDiffAt ℝ 1 haarLogRatio (w p + (toImaginaryCLM.comp (R p)) ξ) := (hH _ h1).1.of_le (by norm_num)
    have e2 : ContDiffAt ℝ 1 haarLogRatio (w' p + (toImaginaryCLM.comp (R p)) ξ) := (hH _ h2).1.of_le (by norm_num)
    have a1 : ContDiffAt ℝ 1 (fun ζ : BondField ι => w p + (toImaginaryCLM.comp (R p)) ζ) ξ :=
      (contDiff_const.add (toImaginaryCLM.comp (R p)).contDiff).contDiffAt
    have a2 : ContDiffAt ℝ 1 (fun ζ : BondField ι => w' p + (toImaginaryCLM.comp (R p)) ζ) ξ :=
      (contDiff_const.add (toImaginaryCLM.comp (R p)).contDiff).contDiffAt
    exact (ContDiffAt.comp ξ e2 a2).sub (ContDiffAt.comp ξ e1 a1)
  refine ⟨?_, ?_, ?_⟩
  · intro ξ hξ
    have : ContDiffAt ℝ 1 (logRatioDiffSum S w w' R) ξ := by
      unfold logRatioDiffSum
      exact ContDiffAt.sum fun p hp => hc p hp ξ hξ
    exact this.contDiffWithinAt
  · intro ξ hξ
    unfold logRatioDiffSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ p ∈ S, |haarLogRatio (w' p + (toImaginaryCLM.comp (R p)) ξ) -
        haarLogRatio (w p + (toImaginaryCLM.comp (R p)) ξ)| ≤ C * Θ := by
      intro p hp
      obtain ⟨h1, h2⟩ := hball p hp ξ hξ
      refine (logRatio_lipschitz hC hH h1 h2).trans ?_
      have : w' p + (toImaginaryCLM.comp (R p)) ξ - (w p + (toImaginaryCLM.comp (R p)) ξ) = w' p - w p := by abel
      rw [this]
      exact mul_le_mul_of_nonneg_left (hθ p hp) hC.le
    simpa using Finset.sum_le_card_nsmul _ _ _ this
  · intro ξ hξ k
    set E := ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) k with hE
    have hder : ∀ p ∈ S, HasFDerivAt
        (fun ζ => haarLogRatio (w' p + (toImaginaryCLM.comp (R p)) ζ) -
          haarLogRatio (w p + (toImaginaryCLM.comp (R p)) ζ))
        ((fderiv ℝ haarLogRatio (w' p + (toImaginaryCLM.comp (R p)) ξ)).comp (toImaginaryCLM.comp (R p)) -
          (fderiv ℝ haarLogRatio (w p + (toImaginaryCLM.comp (R p)) ξ)).comp (toImaginaryCLM.comp (R p))) ξ := by
      intro p hp
      obtain ⟨h1, h2⟩ := hball p hp ξ hξ
      exact (hasFDerivAt_logRatio_affine (((hH _ h2).1).differentiableAt (by norm_num))).sub
        (hasFDerivAt_logRatio_affine (((hH _ h1).1).differentiableAt (by norm_num)))
    have hsum : HasFDerivAt (logRatioDiffSum S w w' R) (∑ p ∈ S,
        ((fderiv ℝ haarLogRatio (w' p + (toImaginaryCLM.comp (R p)) ξ)).comp (toImaginaryCLM.comp (R p)) -
          (fderiv ℝ haarLogRatio (w p + (toImaginaryCLM.comp (R p)) ξ)).comp (toImaginaryCLM.comp (R p)))) ξ := by
      unfold logRatioDiffSum
      exact HasFDerivAt.fun_sum hder
    unfold bondGradNorm
    have hcomp : ∀ X : P → (BondField ι →L[ℝ] ℝ), (∑ p ∈ S, X p).comp E = ∑ p ∈ S, (X p).comp E :=
      fun X => ContinuousLinearMap.ext fun e => by simp
    rw [hsum.fderiv, hcomp]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    obtain ⟨h1, h2⟩ := hball p hp ξ hξ
    have hg := fderiv_logRatio_lipschitz hC hH h1 h2
    have hdiff : w' p + (toImaginaryCLM.comp (R p)) ξ - (w p + (toImaginaryCLM.comp (R p)) ξ) = w' p - w p := by abel
    rw [hdiff] at hg
    have hg' : ‖fderiv ℝ haarLogRatio (w' p + (toImaginaryCLM.comp (R p)) ξ) -
        fderiv ℝ haarLogRatio (w p + (toImaginaryCLM.comp (R p)) ξ)‖ ≤
        C * Θ := hg.trans (mul_le_mul_of_nonneg_left (hθ p hp) hC.le)
    have hΘ : 0 ≤ C * Θ := (ContinuousLinearMap.opNorm_nonneg _).trans hg'
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
    have hval : ((((fderiv ℝ haarLogRatio (w' p + (toImaginaryCLM.comp (R p)) ξ)).comp (toImaginaryCLM.comp (R p)) -
        (fderiv ℝ haarLogRatio (w p + (toImaginaryCLM.comp (R p)) ξ)).comp (toImaginaryCLM.comp (R p)))).comp E) e =
        (fderiv ℝ haarLogRatio (w' p + (toImaginaryCLM.comp (R p)) ξ) -
          fderiv ℝ haarLogRatio (w p + (toImaginaryCLM.comp (R p)) ξ))
          (toImaginaryCLM ((R p).comp E e)) := rfl
    rw [hval]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_toImaginaryCLM]
    calc _ ≤ C * Θ * ‖(R p).comp E e‖ := mul_le_mul_of_nonneg_right hg' (norm_nonneg _)
      _ ≤ C * Θ * (‖(R p).comp E‖ * ‖e‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hΘ
      _ = _ := by ring
open Classical in
private def freeBondOffsets (L : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4) :=
  ((centredCube L) ×ˢ (Finset.univ : Finset (Fin 4))).filter fun p => ¬ IsTreeBondOffset L p.1 p.2
private theorem mem_freeBondOffsets {L : ℕ} {p : (Fin 4 → ℤ) × Fin 4} :
    p ∈ freeBondOffsets L ↔ p.1 ∈ centredCube L ∧ ¬ IsTreeBondOffset L p.1 p.2 := by
  simp [freeBondOffsets, Finset.mem_filter, Finset.mem_product]
private theorem fineBondAt_mem (hO : TorusOffsetsAboutCell) (F : BlockFrame) (r : ℕ) (Y : F.Cell) (o : Fin 4 → ℤ)
    (hodd : Odd F.blockSide) (hs : ∀ i, 2 * r + 2 < F.extent i) {p : (Fin 4 → ℤ) × Fin 4}
    (hp : p ∈ freeBondOffsets F.blockSide) :
    fineBondAt Y o p.1 p.2 ∈ chordBonds (finiteCells F) := by
  obtain ⟨c1, _, _, k1, _⟩ := hO F r Y hodd hs
  obtain ⟨hc, ht⟩ := mem_freeBondOffsets.1 hp
  have e := k1 (fineBondAt Y o p.1 p.2).1 p.2
  rw [(c1 o p.1 p.2 hc).2] at e
  exact e.2 ht
open Classical in
private theorem sum_over_block (hO : TorusOffsetsAboutCell) (F : BlockFrame) (r : ℕ) (Y : F.Cell) (o : Fin 4 → ℤ)
    (hodd : Odd F.blockSide) (hs : ∀ i, 2 * r + 2 < F.extent i) (ho : WithinRadius r o)
    (g : F.Site F.depth × Fin 4 → ℝ) :
    (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y + siteOfCoords F.top o then g b.1 else 0) =
      ∑ p ∈ freeBondOffsets F.blockSide, g (fineBondAt Y o p.1 p.2) := by
  obtain ⟨c1, u1, d1, k1, e1, _⟩ := hO F r Y hodd hs
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun p hp => ⟨fineBondAt Y o p.1 p.2, fineBondAt_mem hO F r Y o hodd hs hp⟩) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (c1 o p.1 p.2 (mem_freeBondOffsets.1 hp).1).1
  · intro p hp p' hp' h
    have h' : fineBondAt Y o p.1 p.2 = fineBondAt Y o p'.1 p'.2 := congrArg Subtype.val h
    have hk : p.2 = p'.2 := by
      have := congrArg Prod.snd h'
      exact this
    obtain ⟨_, hu⟩ := u1 o o p.1 p'.1 p.2 p'.2 ho ho (mem_freeBondOffsets.1 hp).1 (mem_freeBondOffsets.1 hp').1
      (congrArg Prod.fst h')
    exact Prod.ext hu hk
  · intro b hb
    have hcell : enclosingCell b.1.1 = Y + siteOfCoords F.top o := by
      simpa using hb
    have hd : cellSupDist (enclosingCell b.1.1) Y ≤ r := by
      rw [hcell, (d1 o ho).1]
      exact Finset.sup_le fun i _ => by
        have := ho i
        rw [Int.abs_eq_natAbs] at this
        omega
    obtain ⟨h, u, hh, hu, hlb⟩ := e1 b.1.1 hd
    have hb1 : fineBondAt Y h u b.1.2 = b.1 := (hlb b.1.2).trans rfl
    have hc2 : Y + siteOfCoords F.top h = Y + siteOfCoords F.top o := by
      have := (c1 h u b.1.2 hu).1
      rw [hb1] at this
      exact this.symm.trans hcell
    have hho : h = o := by
      refine (u1 h o u u b.1.2 b.1.2 hh ho hu hu ?_).1
      simp only [fineBondAt, hc2]
    subst hho
    have hnt : ¬ IsTreeBondOffset F.blockSide u b.1.2 := by
      have e := k1 b.1.1 b.1.2
      have hoff : cellOffset b.1.1 = u := by
        have := (c1 h u b.1.2 hu).2
        rwa [hb1] at this
      rw [hoff] at e
      exact e.1 b.2
    refine ⟨(u, b.1.2), mem_freeBondOffsets.2 ⟨hu, hnt⟩, Subtype.ext hb1⟩
  · intro p hp
    rfl
open Classical in
private def bondReadout {S : Type} (J : ι → S) (β : S) : BondField ι →L[ℝ] BondVector :=
  ∑ i, if J i = β then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) i else 0
open Classical in
private theorem bondReadout_apply {S : Type} (J : ι → S) (β : S) (ξ : BondField ι) :
    bondReadout J β ξ = ∑ i, if J i = β then ξ i else 0 := by
  unfold bondReadout
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl
open Classical in
private theorem bondReadout_single {S : Type} (J : ι → S) (β : S) (k : ι) (e : BondVector) :
    bondReadout J β (Pi.single k e) = if J k = β then e else 0 := by
  rw [bondReadout_apply, Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    simp [Pi.single_eq_of_ne hik]
  · intro h
    exact absurd (Finset.mem_univ k) h
open Classical in
private theorem bondReadout_comp_norm {S : Type} (J : ι → S) (β : S) (k : ι) :
    ‖(bondReadout J β).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) k)‖ ≤
      if J k = β then 1 else 0 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by split_ifs <;> norm_num) fun e => ?_
  change ‖bondReadout J β (Pi.single k e)‖ ≤ _
  rw [bondReadout_single]
  split_ifs <;> simp
private theorem bondReadout_norm {S : Type} {J : ι → S} (hJ : Function.Injective J) (β : S) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {ξ : BondField ι} (hξ : ξ ∈ openPolyball ι ρ) : ‖bondReadout J β ξ‖ ≤ ρ := by
  classical
  rw [bondReadout_apply]
  by_cases h : ∃ i, J i = β
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · rw [if_pos hi]
      exact (hξ i).le
    · intro i' _ hne
      exact if_neg fun h' => hne (hJ (h'.trans hi.symm))
    · intro hn
      exact absurd (Finset.mem_univ i) hn
  · rw [Finset.sum_eq_zero]
    · simpa using hρ
    · intro i _
      exact if_neg fun h' => h ⟨i, h'⟩
private theorem stepCoordinates_pushforward {F : BlockFrame} (j : ι → ↥(chordBonds (finiteCells F)))
    {β : F.Site F.depth × Fin 4} (hβ : β ∈ chordBonds (finiteCells F)) (ξ : BondField ι) :
    stepCoordinates (pushforwardField j ξ) β.1 β.2 =
      (toImaginaryCLM.comp (bondReadout (fun i => (j i).1) β)) ξ := by
  classical
  have h1 : stepCoordinates (pushforwardField j ξ) β.1 β.2 = toImaginary (pushforwardField j ξ ⟨β, hβ⟩) :=
    dif_pos hβ
  have h2 : (toImaginaryCLM.comp (bondReadout (fun i => (j i).1) β)) ξ =
      toImaginaryCLM (bondReadout (fun i => (j i).1) β ξ) := rfl
  rw [h1, h2, toImaginaryCLM_apply, bondReadout_apply]
  congr 1
  unfold pushforwardField
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (j i).1 = β
  · rw [if_pos h, if_pos (Subtype.ext h)]
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h')]
private theorem interpolatedHaarPart_eq (hO : TorusOffsetsAboutCell) (F : BlockFrame) (r : ℕ) (Y : F.Cell)
    (o : Fin 4 → ℤ) (hodd : Odd F.blockSide) (hs : ∀ i, 2 * r + 2 < F.extent i) (ho : WithinRadius r o)
    (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (j : ι → ↥(chordBonds (finiteCells F))) (ξ : BondField ι) :
    interpolatedHaarPart s a ρA m (Y + siteOfCoords F.top o) V (pushforwardField j ξ) =
      ∑ p ∈ freeBondOffsets F.blockSide, haarLogRatio (interpolatedFrame s a ρA m (fineBondAt Y o p.1 p.2) V +
        (toImaginaryCLM.comp (bondReadout (fun i => (j i).1) (fineBondAt Y o p.1 p.2))) ξ) := by
  unfold interpolatedHaarPart
  refine (sum_over_block hO F r Y o hodd hs ho
    (fun β => haarLogRatio (interpolatedCoords s a ρA m V (pushforwardField j ξ) β.1 β.2))).trans ?_
  refine Finset.sum_congr rfl fun p hp => ?_
  have hc := stepCoordinates_pushforward j (fineBondAt_mem hO F r Y o hodd hs hp) ξ
  change haarLogRatio (interpolatedFrame s a ρA m (fineBondAt Y o p.1 p.2) V +
    stepCoordinates (pushforwardField j ξ) (fineBondAt Y o p.1 p.2).1 (fineBondAt Y o p.1 p.2).2) = _
  rw [hc]
private theorem bondReadout_paired (hO : TorusOffsetsAboutCell) {F F' : BlockFrame} {Y : F.Cell} {Y' : F'.Cell}
    {q : ℕ} {o : Fin 4 → ℤ} (hL : F.blockSide = F'.blockSide) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 * q + 2 < F.extent i) (hs' : ∀ i, 2 * q + 2 < F'.extent i) (ho : WithinRadius q o)
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F')))
    (hp : ∀ i, ∃ (g u : Fin 4 → ℤ) (k : Fin 4), u ∈ centredCube F.blockSide ∧ WithinRadius q g ∧
      (j i).1 = fineBondAt Y g u k ∧ (j' i).1 = fineBondAt Y' g u k)
    {c : (Fin 4 → ℤ) × Fin 4} (hc : c.1 ∈ centredCube F.blockSide) :
    bondReadout (fun i => (j i).1) (fineBondAt Y o c.1 c.2) =
      bondReadout (fun i => (j' i).1) (fineBondAt Y' o c.1 c.2) := by
  classical
  obtain ⟨_, u1, _⟩ := hO F q Y hodd hs
  obtain ⟨_, u2, _⟩ := hO F' q Y' (hL ▸ hodd) hs'
  have hiff : ∀ i, ((j i).1 = fineBondAt Y o c.1 c.2 ↔ (j' i).1 = fineBondAt Y' o c.1 c.2) := by
    intro i
    obtain ⟨g, u, k, hu, hg, e1, e2⟩ := hp i
    constructor
    · intro h
      have h' : fineBondAt Y g u k = fineBondAt Y o c.1 c.2 := e1.symm.trans h
      have hk : k = c.2 := by
        have := congrArg Prod.snd h'
        exact this
      obtain ⟨rfl, rfl⟩ := u1 g o u c.1 k c.2 hg ho hu hc (congrArg Prod.fst h')
      rw [e2, hk]
    · intro h
      have h' : fineBondAt Y' g u k = fineBondAt Y' o c.1 c.2 := e2.symm.trans h
      have hk : k = c.2 := by
        have := congrArg Prod.snd h'
        exact this
      obtain ⟨rfl, rfl⟩ := u2 g o u c.1 k c.2 hg ho (hL ▸ hu) (hL ▸ hc) (congrArg Prod.fst h')
      rw [e1, hk]
  unfold bondReadout
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (j i).1 = fineBondAt Y o c.1 c.2
  · rw [if_pos h, if_pos ((hiff i).1 h)]
  · rw [if_neg h, if_neg fun h' => h ((hiff i).2 h')]
private def Requirement (C : ℝ) (T : StepParameters) : Prop :=
  0 < T.Ct ∧ 3 * ((freeBondOffsets T.L).card : ℝ) * C * T.σ ≤ 1 ∧ 2 ^ 6 * T.κ ≤ T.chainParams.δ₂ ∧
    2 ≤ T.blockIndex ∧ 1 ≤ T.n₀ ∧ 0 ≤ T.coupling
private theorem requirement_eventually {C : ℝ} (hC : 0 < C) : EventuallyInParameters (Requirement C) := by
  intro a _
  refine ⟨0, fun L _ _ c hc => ?_⟩
  obtain ⟨⟨_, _, _, _, hδ, _⟩, _⟩ := hc.classical
  have hN : 0 ≤ 3 * ((freeBondOffsets L).card : ℝ) * C := by positivity
  have hd : 0 < 3 * ((freeBondOffsets L).card : ℝ) * C + 1 := by linarith
  refine ⟨1, fun Ct hCt => ⟨c.δ₂ / 2 ^ 6, by positivity, fun κ _ hκ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨2, fun nss hn => ⟨1 / (3 * ((freeBondOffsets L).card : ℝ) * C + 1), by positivity, fun σ _ hσ p _ =>
      ⟨0, fun Cs _ E _ => ⟨1, fun n₀ hn₀ => ⟨0, fun CE _ => ⟨0, fun y₁ hy => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨by change 0 < Ct; linarith, ?_, ?_, hn, hn₀, hy⟩
  · change 3 * ((freeBondOffsets L).card : ℝ) * C * σ ≤ 1
    calc 3 * ((freeBondOffsets L).card : ℝ) * C * σ ≤
          3 * ((freeBondOffsets L).card : ℝ) * C * (1 / (3 * ((freeBondOffsets L).card : ℝ) * C + 1)) :=
          mul_le_mul_of_nonneg_left hσ hN
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one hd]
          linarith
  · change 2 ^ 6 * κ ≤ c.δ₂
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 6)).1 hκ
    linarith
private theorem compare_at (hO : TorusOffsetsAboutCell) {C : ℝ} (hC : 0 < C) (hH : LogRatioDerivBounds C)
    (T : StepParameters) (hT : T.IsOrdered)
    (hFr : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFramesControlledAt T t x)
    (hA : Requirement C T) : HaarDensitiesCompareAt T := by
  intro t x s h F F' V V' Y Y' q ι _ _ j j' o hS
  obtain ⟨hCt, hσC, hκ, hq, hn₀, hy⟩ := hA
  have hx : 0 ≤ x := hy.trans hS.coupling_le
  have hσ := hT.σ_pos
  obtain ⟨⟨_, hρ1, _, hδ, _⟩, _⟩ := hT.chain_admissible.classical
  obtain ⟨hFL, _, n, hside, hn⟩ := hS.top
  obtain ⟨hFL', _, n', hside', hn'⟩ := hS.top'
  have hs : ∀ i, 2 * q + 2 < F.extent i := fun i =>
    (hS.agree.1 i).resolve_left (by rw [hside i]; omega)
  have hs' : ∀ i, 2 * q + 2 < F'.extent i := fun i =>
    (hS.agree.2.1 i).resolve_left (by rw [hside' i]; omega)
  have hodd : Odd F.blockSide := hFL ▸ hT.odd_L
  have hodd' : Odd F'.blockSide := hFL' ▸ hT.odd_L
  have hLL : F.blockSide = F'.blockSide := hFL.trans hFL'.symm
  have ho8 : ∀ i, (o i).natAbs ≤ q / 8 := by
    intro i
    have := hS.offset_le i
    rw [Int.abs_eq_natAbs] at this
    omega
  have ho : WithinRadius q o := by
    intro i
    have := ho8 i
    rw [Int.abs_eq_natAbs]
    have : q / 8 ≤ q := Nat.div_le_self _ _
    omega
  have hsm := ((hFr t x hS.coupling_le).single F V s hS.top hS.small hS.interp_mem.1 hS.interp_mem.2).2
  have hsm' := ((hFr t x hS.coupling_le).single F' V' s hS.top' hS.small' hS.interp_mem.1 hS.interp_mem.2).2
  have hloc := (hFr t x hS.coupling_le).pair F F' V V' Y Y' q s hS.top hS.top' hS.small hS.small' hS.agree
    hS.interp_mem.1 hS.interp_mem.2
  obtain ⟨c1, _, d1, _, _, n1, n2, _⟩ := hO F q Y hodd hs
  have hcF : freeBondOffsets T.L = freeBondOffsets F.blockSide := by rw [hFL]
  have hcF' : freeBondOffsets T.L = freeBondOffsets F'.blockSide := by rw [hFL']
  set m := frameRadius x with hm
  set w : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions :=
    fun p => interpolatedFrame s T.a T.chainParams.ρA m (fineBondAt Y o p.1 p.2) V with hw
  set w' : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions :=
    fun p => interpolatedFrame s T.a T.chainParams.ρA m (fineBondAt Y' o p.1 p.2) V' with hw'
  set R : (Fin 4 → ℤ) × Fin 4 → BondField ι →L[ℝ] BondVector :=
    fun p => bondReadout (fun i => (j i).1) (fineBondAt Y o p.1 p.2) with hR
  have hfun : (fun ζ => interpolatedHaarPart s T.a T.chainParams.ρA m (Y' + siteOfCoords F'.top o) V' (pushforwardField j' ζ) -
      interpolatedHaarPart s T.a T.chainParams.ρA m (Y + siteOfCoords F.top o) V (pushforwardField j ζ)) =
      logRatioDiffSum (freeBondOffsets T.L) w w' R := by
    funext ζ
    rw [interpolatedHaarPart_eq hO F q Y o hodd hs ho, interpolatedHaarPart_eq hO F' q Y' o hodd' hs' ho,
      ← hcF, ← hcF']
    unfold logRatioDiffSum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hc : p.1 ∈ centredCube F.blockSide := (mem_freeBondOffsets.1 (hcF ▸ hp)).1
    rw [← bondReadout_paired hO hLL hodd hs hs' ho j j' hS.paired hc]
  have hdist : ∀ p : (Fin 4 → ℤ) × Fin 4, p.1 ∈ centredCube F.blockSide →
      8 * cellSupDist Y (enclosingCell (fineBondAt Y o p.1 p.2).1) ≤ q := by
    intro p hp
    rw [(c1 o p.1 p.2 hp).1, (d1 o ho).2]
    have : (Finset.univ.sup fun i => (o i).natAbs) ≤ q / 8 := Finset.sup_le fun i _ => ho8 i
    omega
  set E₁ : ℝ := Real.exp (-(T.chainParams.δ₂ / 4 * (7 * (q : ℝ) / 8))) with hE₁
  have hθ : ∀ p ∈ freeBondOffsets T.L, ‖w' p - w p‖ ≤ T.Ct * T.σ * E₁ := by
    intro p hp
    have hpF : p ∈ freeBondOffsets F.blockSide := hcF ▸ hp
    have hc : p.1 ∈ centredCube F.blockSide := (mem_freeBondOffsets.1 hpF).1
    have hd := hdist p hc
    have hbox : IsFineBondWithinRadius Y q o p.1 p.2 := by
      refine ⟨hc, fineBondAt_mem hO F q Y o hodd hs hpF, ho, by omega, ?_⟩
      have h1 := n1 (fineBondAt Y o p.1 p.2).1 p.2
      have hrad := hS.radius_le
      rw [n2] at h1
      rw [n2 (enclosingCell (fineBondAt Y o p.1 p.2).1) Y] at h1
      omega
    have hv := hloc.norm_sub_le o p.1 p.2 hbox
    rw [norm_sub_rev]
    refine hv.trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have hdr : (8 : ℝ) * cellSupDist Y (enclosingCell (fineBondAt Y o p.1 p.2).1) ≤ q := by exact_mod_cast hd
    have : T.chainParams.δ₂ / 4 * (7 * (q : ℝ) / 8) ≤
        T.chainParams.δ₂ / 4 * ((q : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y o p.1 p.2).1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hρ : T.ballRadius = T.σ / 64 := rfl
  have hρ0 : 0 ≤ T.ballRadius := by rw [hρ]; positivity
  have hroom : ∀ p ∈ freeBondOffsets T.L, ‖w p‖ + T.ballRadius ≤ 1 := by
    intro p hp
    have := hsm.norm_add_le _ (fineBondAt_mem hO F q Y o hodd hs (hcF ▸ hp))
    rw [hρ]
    linarith
  have hroom' : ∀ p ∈ freeBondOffsets T.L, ‖w' p‖ + T.ballRadius ≤ 1 := by
    intro p hp
    have := hsm'.norm_add_le _ (fineBondAt_mem hO F' q Y' o hodd' hs' (hcF' ▸ hp))
    rw [hρ]
    linarith
  obtain ⟨b1, b2, b3⟩ := logRatioDiffSum_bounds hC hH (freeBondOffsets T.L) w w' R hroom hroom'
    (fun p _ ξ hξ => bondReadout_norm (fun i i' hii => hS.injective (Subtype.ext hii)) _ hρ0 hξ) hθ
  have hE₁ε : E₁ ≤ Real.exp (-(4 * T.κ * q)) := by
    refine Real.exp_le_exp.2 ?_
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hκ hq0, mul_nonneg hδ.le hq0]
  set ε : ℝ := Real.exp (-(4 * T.κ * q)) with hε
  have hε0 : 0 < ε := Real.exp_pos _
  have hE0 : 0 < E₁ := Real.exp_pos _
  have hbig : ((freeBondOffsets T.L).card : ℝ) * (C * (T.Ct * T.σ * E₁)) ≤ T.Ct / 3 * ε := by
    have h1 : ((freeBondOffsets T.L).card : ℝ) * C * T.σ ≤ 1 / 3 := by linarith
    have h2 : ((freeBondOffsets T.L).card : ℝ) * C * T.σ * E₁ ≤ 1 / 3 * ε :=
      mul_le_mul h1 hE₁ε hE0.le (by norm_num)
    calc ((freeBondOffsets T.L).card : ℝ) * (C * (T.Ct * T.σ * E₁))
        = T.Ct * (((freeBondOffsets T.L).card : ℝ) * C * T.σ * E₁) := by ring
      _ ≤ T.Ct * (1 / 3 * ε) := mul_le_mul_of_nonneg_left h2 hCt.le
      _ = T.Ct / 3 * ε := by ring
  have hc0 : 0 ≤ T.Ct / 3 * ε := by positivity
  refine ⟨by rw [hfun]; exact b1, fun ξ hξ => ⟨?_, fun k => ?_⟩⟩
  · have hsq : 0 ≤ weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F) (Y + siteOfCoords F.top o) ξ :=
      Finset.sum_nonneg fun _ _ => by positivity
    have h1 : |interpolatedHaarPart s T.a T.chainParams.ρA m (Y' + siteOfCoords F'.top o) V' (pushforwardField j' ξ) -
        interpolatedHaarPart s T.a T.chainParams.ρA m (Y + siteOfCoords F.top o) V (pushforwardField j ξ)| ≤
        T.Ct / 3 * ε := by
      have h2 : interpolatedHaarPart s T.a T.chainParams.ρA m (Y' + siteOfCoords F'.top o) V' (pushforwardField j' ξ) -
          interpolatedHaarPart s T.a T.chainParams.ρA m (Y + siteOfCoords F.top o) V (pushforwardField j ξ) =
          logRatioDiffSum (freeBondOffsets T.L) w w' R ξ := congrFun hfun ξ
      rw [h2]
      exact (b2 ξ hξ).trans hbig
    refine h1.trans ?_
    exact le_mul_of_one_le_right hc0 (by nlinarith [mul_nonneg hx hsq])
  · rw [hfun]
    refine (b3 ξ hξ k).trans ?_
    have hsq : 0 ≤ Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F)
        (Y + siteOfCoords F.top o) ξ) :=
      Real.sqrt_nonneg _
    have hCΘ : 0 ≤ C * (T.Ct * T.σ * E₁) := by positivity
    by_cases hk : bondBlock F (j k) = Y + siteOfCoords F.top o
    · have hcell : blockDist F (bondBlock F (j k)) (Y + siteOfCoords F.top o) = 0 := by
        rw [hk]
        simp [blockDist, cellSupDist]
      rw [hcell]
      have hs1 : ∑ p ∈ freeBondOffsets T.L, C * (T.Ct * T.σ * E₁) *
          ‖(R p).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) k)‖ ≤
          ((freeBondOffsets T.L).card : ℝ) * (C * (T.Ct * T.σ * E₁)) := by
        have : ∀ p ∈ freeBondOffsets T.L, C * (T.Ct * T.σ * E₁) *
            ‖(R p).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) k)‖ ≤
            C * (T.Ct * T.σ * E₁) := by
          intro p _
          refine mul_le_of_le_one_right hCΘ ((bondReadout_comp_norm _ _ k).trans ?_)
          split_ifs <;> norm_num
        simpa using Finset.sum_le_card_nsmul _ _ _ this
      refine hs1.trans (hbig.trans ?_)
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      exact le_mul_of_one_le_right hc0 (by nlinarith [mul_nonneg hx hsq])
    · have hz : ∑ p ∈ freeBondOffsets T.L, C * (T.Ct * T.σ * E₁) *
          ‖(R p).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) k)‖ ≤ 0 := by
        refine Finset.sum_nonpos fun p hp => ?_
        have hne : ¬ (j k).1 = fineBondAt Y o p.1 p.2 := by
          intro he
          apply hk
          have hc : p.1 ∈ centredCube F.blockSide := (mem_freeBondOffsets.1 (hcF ▸ hp)).1
          change enclosingCell (j k).1.1 = _
          rw [he]
          exact (c1 o p.1 p.2 hc).1
        have h0 := bondReadout_comp_norm (fun i => (j i).1) (fineBondAt Y o p.1 p.2) k
        rw [if_neg hne] at h0
        exact mul_nonpos_of_nonneg_of_nonpos hCΘ h0
      refine hz.trans ?_
      have : 0 ≤ x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondBlock F (j k)) (blockDist F)
          (Y + siteOfCoords F.top o) ξ) + 1 := by
        positivity
      positivity
end HaarDensities
theorem haarDensitiesCompare_holds (hF : interpolatedFramesControlled) (hH : HaarLogRatioNearZero)
    (hO : TorusOffsetsAboutCell) (hj : EventuallyInParametersCombines) : HaarDensitiesCompare := by
  obtain ⟨C, hC, hH⟩ := hH
  refine hj.2 _ _ ?_ (hj.1 _ _ hF (HaarDensities.requirement_eventually hC))
  rintro T hT ⟨hFr, hA⟩
  exact HaarDensities.compare_at hO hC hH T hT hFr hA
end YangMills.Construction.ColdStepAtMirrorFrames
end
