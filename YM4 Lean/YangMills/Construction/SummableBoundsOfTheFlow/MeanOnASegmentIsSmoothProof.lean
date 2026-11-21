import YangMills.Construction.ColdStepAtMirrorFrames.SmoothOnATube
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnASegmentIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames Topology
namespace YangMills.Construction.GibbsInterpolation
namespace SliceLemmas
variable {k : ℕ} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
private theorem isOpen_setOf_contDiffAt (F : (Fin k → ℝ) × Q → ℝ) :
    IsOpen {z | ContDiffAt ℝ 3 F z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact (show ContDiffAt ℝ 3 F z from hz).eventually (by simp)
private theorem iteratedFDeriv_slice_eq {F : (Fin k → ℝ) × Q → ℝ} {q : Q}
    (hF : ContDiffAt ℝ 3 F (0, q)) {j : ℕ}
    (hj : j ≤ 3) (w : Fin j → Fin k → ℝ) :
    iteratedFDeriv ℝ j (fun t => F (t, q)) 0 w =
      iteratedFDeriv ℝ j F (0, q) fun i => (w i, 0) := by
  set U : Set ((Fin k → ℝ) × Q) := {z | ContDiffAt ℝ 3 F z} with hU
  have hUo : IsOpen U := isOpen_setOf_contDiffAt F
  have hFU : ContDiffOn ℝ 3 F U := fun z hz => (show ContDiffAt ℝ 3 F z from hz).contDiffWithinAt
  set e : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) × Q := ContinuousLinearMap.inl ℝ _ _ with he
  set f : (Fin k → ℝ) × Q → ℝ := fun z => F (z + (0, q)) with hf
  set s : Set ((Fin k → ℝ) × Q) := (fun z => z + ((0 : Fin k → ℝ), q)) ⁻¹' U with hs
  have hso : IsOpen s := hUo.preimage (continuous_add_const _)
  have hfs : ContDiffOn ℝ 3 f s :=
    hFU.comp (contDiff_id.add contDiff_const).contDiffOn (fun z hz => hz)
  have hslice : (fun t => F (t, q)) = f ∘ e := by
    funext t
    simp [hf, he]
  have h0 : e 0 ∈ s := by
    simpa [hs, he, hU] using hF
  have hcomp := e.iteratedFDerivWithin_comp_right hfs hso.uniqueDiffOn
    (hso.preimage e.continuous).uniqueDiffOn h0 (i := j) (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen j (hso.preimage e.continuous) h0,
    iteratedFDerivWithin_of_isOpen j hso h0] at hcomp
  have hadd : iteratedFDeriv ℝ j f (e 0) = iteratedFDeriv ℝ j F (e 0 + (0, q)) :=
    iteratedFDeriv_comp_add_right j (0, q) (e 0)
  rw [hslice, hcomp, hadd]
  simp [he]
private theorem continuousOn_iteratedFDeriv_slice {F : (Fin k → ℝ) × Q → ℝ} {K : Set Q}
    (hF : ∀ q ∈ K, ContDiffAt ℝ 3 F (0, q)) {j : ℕ} (hj : j ≤ 3) (w : Fin j → Fin k → ℝ) :
    ContinuousOn (fun q => iteratedFDeriv ℝ j (fun t => F (t, q)) 0 w) K := by
  set U : Set ((Fin k → ℝ) × Q) := {z | ContDiffAt ℝ 3 F z} with hU
  have hUo : IsOpen U := isOpen_setOf_contDiffAt F
  have hFU : ContDiffOn ℝ 3 F U := fun z hz => (show ContDiffAt ℝ 3 F z from hz).contDiffWithinAt
  have hc : ContinuousOn (iteratedFDeriv ℝ j F) U :=
    (hFU.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj)
      hUo.uniqueDiffOn).congr (fun z hz => (iteratedFDerivWithin_of_isOpen j hUo hz).symm)
  have h1 : ContinuousOn (fun q : Q => iteratedFDeriv ℝ j F (0, q)) K :=
    hc.comp (by fun_prop) fun q hq => hF q hq
  have h2 : ContinuousOn (fun q : Q => iteratedFDeriv ℝ j F (0, q) fun i => (w i, (0 : Q))) K :=
    (ContinuousMultilinearMap.apply ℝ _ ℝ fun i => (w i, (0 : Q))).continuous.comp_continuousOn h1
  exact h2.congr fun q hq => iteratedFDeriv_slice_eq (hF q hq) hj w
private theorem exists_ball_continuousOn_slice {F : (Fin k → ℝ) × Q → ℝ} {K : Set Q}
    (hK : IsCompact K) (hF : ∀ q ∈ K, ContDiffAt ℝ 3 F (0, q)) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Metric.ball (0 : Fin k → ℝ) r, ContinuousOn (fun q => F (t, q)) K := by
  set U : Set ((Fin k → ℝ) × Q) := {z | ContDiffAt ℝ 3 F z} with hU
  have hsub : ({0} : Set (Fin k → ℝ)) ×ˢ K ⊆ U := by
    rintro ⟨t, q⟩ ⟨ht, hq⟩
    obtain rfl : t = 0 := ht
    exact hF q hq
  obtain ⟨u, v, hu, hv, h0u, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hK (isOpen_setOf_contDiffAt F) hsub
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hu 0 (h0u rfl)
  refine ⟨r, hr, fun t ht q hq => ?_⟩
  have hz : (t, q) ∈ U := huv ⟨hball ht, hKv hq⟩
  have hc : ContinuousAt F (t, q) := (show ContDiffAt ℝ 3 F (t, q) from hz).continuousAt
  have h2 : ContinuousAt (fun q' : Q => (t, q')) q := by fun_prop
  exact (ContinuousAt.comp (f := fun q' : Q => (t, q')) hc h2).continuousWithinAt
private theorem isDominatedSmoothFamily_mono {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ} {B B' : Set (Fin k → ℝ)} {C C' : ℝ} {F : (Fin k → ℝ) → Ω → ℝ} (hB : B' ⊆ B)
    (hC : C ≤ C') (h : IsDominatedSmoothFamily μ 3 B C F) : IsDominatedSmoothFamily μ 3 B' C' F := by apply _root_.YangMills.Construction.InterpolatedBirths.IsDominatedSmoothFamily.mono <;> assumption
end SliceLemmas
open SliceLemmas in
theorem interpolatedGibbsMeanSmooth_of_bounds (hW : GibbsMeanDifferentiation)
    (hD : DominatedFamilyOnClosedBalls) (hS : UniformDerivBoundNearCompact) :
    InterpolatedGibbsMeanSmooth := by
  intro ι _ k ρ μ _ A R H hμ0 hμ hsm
  set π : (Fin (k + 1) → ℝ) × (ℝ × BondField ι) → (Fin k → ℝ) × BondField ι := fun z => (Fin.tail z.1, z.2.2) with hπ
  have htail : ContDiff ℝ 3 fun t' : Fin (k + 1) → ℝ => (Fin.tail t' : Fin k → ℝ) :=
    contDiff_pi.mpr fun i => contDiff_apply ℝ ℝ i.succ
  have hπs : ContDiff ℝ 3 π :=
    (htail.comp contDiff_fst).prodMk (contDiff_snd.comp contDiff_snd)
  have hπ0 : ∀ (v : ℝ) (η : BondField ι), π (0, v, η) = (0, η) := fun v η => by
    simp only [hπ]
    rfl
  have lift : ∀ {F : (Fin k → ℝ) × BondField ι → ℝ} (v : ℝ) (η : BondField ι), ContDiffAt ℝ 3 F (0, η) →
      ContDiffAt ℝ 3 (fun z => F (π z)) (0, v, η) := fun {F} v η hF =>
    ContDiffAt.comp (g := F) (f := π) (0, v, η) (by rwa [hπ0]) hπs.contDiffAt
  have hvs : ContDiff ℝ 3 fun z : (Fin (k + 1) → ℝ) × (ℝ × BondField ι) => z.2.1 + z.1 0 :=
    (contDiff_fst.comp contDiff_snd).add ((contDiff_apply ℝ ℝ (0 : Fin (k + 1))).comp contDiff_fst)
  obtain ⟨r₁, M₁, hr₁, hD₁⟩ := hD ι (k + 1) ρ μ
    (fun z => A (π z) - (z.2.1 + z.1 0) * R (π z)) hμ (fun v η _ hη =>
      (lift v η (hsm η hη).1).sub (hvs.contDiffAt.mul (lift v η (hsm η hη).2.1)))
  obtain ⟨r₂, M₂, hr₂, hD₂⟩ := hD ι (k + 1) ρ μ (fun z => H (π z)) hμ
    (fun v η _ hη => lift v η (hsm η hη).2.2)
  set r : ℝ := min r₁ r₂ with hr
  have hrpos : 0 < r := lt_min hr₁ hr₂
  have sub₁ : Metric.ball (0 : Fin (k + 1) → ℝ) r ⊆ Metric.ball 0 r₁ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have sub₂ : Metric.ball (0 : Fin (k + 1) → ℝ) r ⊆ Metric.ball 0 r₂ :=
    Metric.ball_subset_ball (min_le_right _ _)
  set P : (Fin k → ℝ) × ℝ → ℝ := fun z => interpolatedGibbsMean μ A R H z.2 z.1 with hP
  have hPs : ∀ v ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 P (0, v) := by
    intro v hv
    have hN := (hW.2 (BondField ι) μ (k + 1) (Metric.ball 0 r) (max M₁ M₂) _ _ Metric.isOpen_ball hμ0
      (isDominatedSmoothFamily_mono sub₁ (le_max_left _ _) (hD₁ v hv))
      (isDominatedSmoothFamily_mono sub₂ (le_max_right _ _) (hD₂ v hv))).1
    have hNa := hN.contDiffAt (Metric.ball_mem_nhds _ hrpos)
    set Lv : (Fin k → ℝ) × ℝ → Fin (k + 1) → ℝ := fun z => Fin.cons (z.2 - v) z.1 with hLv
    have hLs : ContDiff ℝ 3 Lv := by
      refine contDiff_pi.mpr fun i => ?_
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa [hLv] using (contDiff_snd.sub contDiff_const :
          ContDiff ℝ 3 fun z : (Fin k → ℝ) × ℝ => z.2 - v)
      · have hi : ContDiff ℝ 3 fun z : (Fin k → ℝ) × ℝ => z.1 i :=
          (contDiff_apply ℝ ℝ i).comp contDiff_fst
        simpa [hLv] using hi
    have hL0 : Lv (0, v) = 0 := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [hLv]
    have hcomp := ContDiffAt.comp (f := Lv) ((0 : Fin k → ℝ), v)
      (by rw [hL0]; exact hNa : ContDiffAt ℝ 3 _ (Lv (0, v))) hLs.contDiffAt
    refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp only [hP, interpolatedGibbsMean, Function.comp, hLv, hπ, Fin.tail_cons, Fin.cons_zero,
      add_sub_cancel]
  obtain ⟨r₃, M₃, hr₃, hT⟩ := hS k ℝ P (Set.Icc (0 : ℝ) 1) isCompact_Icc hPs
  obtain ⟨r₄, hr₄, hc⟩ := exists_ball_continuousOn_slice isCompact_Icc hPs
  set s : ℝ := min r₃ r₄ with hs
  have hspos : 0 < s := lt_min hr₃ hr₄
  set B := Metric.ball (0 : Fin k → ℝ) s with hB
  have hB0 : B ∈ 𝓝 (0 : Fin k → ℝ) := Metric.ball_mem_nhds _ hspos
  have hB₃ : B ⊆ Metric.ball 0 r₃ := Metric.ball_subset_ball (min_le_left _ _)
  have hB₄ : B ⊆ Metric.ball 0 r₄ := Metric.ball_subset_ball (min_le_right _ _)
  set F : (Fin k → ℝ) → ℝ → ℝ := fun t v => interpolatedGibbsMean μ A R H v t with hF
  set μ' : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ'
  have hsubI : Set.Ioc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := Set.Ioc_subset_Icc_self
  have hdom : IsDominatedSmoothFamily μ' 3 B M₃ F := by
    refine ⟨fun t ht => ?_, ?_, ?_⟩
    · exact ((hc t (hB₄ ht)).mono hsubI).aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun v hv => ?_)
      exact_mod_cast ((hT v (hsubI hv)).1).mono hB₃
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun v hv => ?_)
      intro j hj t ht
      exact (hT v (hsubI hv)).2 j hj t (hB₃ ht)
  obtain ⟨hI₁, hI₂⟩ := hW.1 ℝ μ' k 3 B M₃ F Metric.isOpen_ball hdom
  have hint : ∀ f : ℝ → ℝ, ∫ v in (0 : ℝ)..1, f v = ∫ v, f v ∂μ' := fun f =>
    intervalIntegral.integral_of_le zero_le_one
  refine ⟨fun v hv => ?_, ?_, fun j hj w => ⟨?_, ?_⟩⟩
  · have := hPs v hv
    have h2 : ContDiffAt ℝ 3 (fun t : Fin k → ℝ => (t, v)) 0 := by fun_prop
    exact ContDiffAt.comp (g := P) (f := fun t : Fin k → ℝ => (t, v)) 0 this h2
  · have := (show ContDiffOn ℝ 3 _ B by exact_mod_cast hI₁).contDiffAt hB0
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact hint _
  · exact continuousOn_iteratedFDeriv_slice hPs hj w
  · have h1 := hI₂ 0 (Metric.mem_ball_self hspos) j hj w
    have h2 : (fun t => ∫ v in (0 : ℝ)..1, interpolatedGibbsMean μ A R H v t) =
        fun t => ∫ v, F t v ∂μ' := funext fun t => hint _
    rw [h2, h1, hint]
    rfl
end YangMills.Construction.GibbsInterpolation
end
