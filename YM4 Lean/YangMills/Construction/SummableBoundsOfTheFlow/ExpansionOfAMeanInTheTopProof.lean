import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTop
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames SmoothSlices
namespace Estimates
variable {F : BlockFrame}
namespace GibbsMeanExpansionInField
theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
def sublistEmbedding {j k : ℕ} (e : Fin j → Fin k) : (Fin j → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ∑ l, if e l = i then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin j => ℝ) l else 0
theorem sublistEmbedding_apply {j k : ℕ} (e : Fin j → Fin k) (z : Fin j → ℝ) (i : Fin k) :
    sublistEmbedding e z i = ∑ l, if e l = i then z l else 0 := by
  simp only [sublistEmbedding, ContinuousLinearMap.coe_pi', _root_.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem sublistEmbedding_single {j k : ℕ} {e : Fin j → Fin k} (he : Function.Injective e) (l : Fin j) :
    sublistEmbedding e (Pi.single l 1) = Pi.single (e l) 1 := by
  funext i
  rw [sublistEmbedding_apply]
  by_cases hi : e l = i
  · subst hi
    rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (he h)]
    · simp
  · rw [Pi.single_eq_of_ne (Ne.symm hi)]
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h
    · have : b ≠ l := fun hb => hi (hb ▸ h)
      exact Pi.single_eq_of_ne this _
    · rfl
theorem bondSpread_sublistEmbedding {j k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (e : Fin j → Fin k) (z : Fin j → ℝ) :
    bondSpread c X (sublistEmbedding e z) = bondSpread (c ∘ e) (X ∘ e) z := by
  funext y i
  unfold bondSpread
  have h1 : ∀ l : Fin k, (if c l = (y, i) then sublistEmbedding e z l • X l else 0) =
      ∑ l', if e l' = l then (if c l = (y, i) then z l' • X l else 0) else 0 := fun l => by
    rw [sublistEmbedding_apply]
    split_ifs with hc
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l' _ => ?_
      split_ifs <;> simp
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [Finset.sum_ite_eq]
  simp
theorem iteratedFDeriv_sublist_eq_bondDeriv (hS : IteratedFDerivSlices) {j k : ℕ}
    (g : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) {e : Fin j → Fin k} (he : Function.Injective e)
    (hg : ContDiffAt ℝ j (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) V)) 0) :
    iteratedFDeriv ℝ j (fun τ : Fin k → ℝ => g (leftTranslate (bondSpread c X τ) V)) 0
        (fun l => Pi.single (e l) 1) = bondDeriv g V (c ∘ e) (X ∘ e) := by
  have h := hS.1 (Fin k → ℝ) (Fin j → ℝ) (fun τ => g (leftTranslate (bondSpread c X τ) V))
    (sublistEmbedding e) 0 0 j (fun l => Pi.single l 1) (by simpa using hg)
  simp only [map_zero, add_zero, zero_add, sublistEmbedding_single he, bondSpread_sublistEmbedding] at h
  rw [← h]
  rfl
theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
section Congr
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A f f' g g' h h' l l' : Ω → ℝ}
theorem gibbsCovariance_congr_ae (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    gibbsCovariance μ A f g = gibbsCovariance μ A f' g' := by
  unfold gibbsCovariance
  have e := fun {u u' : Ω → ℝ} (hu : u =ᵐ[μ] u') =>
    gibbsMean_congr_ae (μ := μ) (A := A) (A' := A) Filter.EventuallyEq.rfl hu
  have fg : (fun ω => f ω * g ω) =ᵐ[μ] fun ω => f' ω * g' ω := hf.mul hg
  rw [e fg, e hf, e hg]
theorem gibbsCumulantThree_congr_ae (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') (hh : h =ᵐ[μ] h') :
    gibbsCumulantThree μ A f g h = gibbsCumulantThree μ A f' g' h' := by
  unfold gibbsCumulantThree
  have e := fun {u u' : Ω → ℝ} (hu : u =ᵐ[μ] u') =>
    gibbsMean_congr_ae (μ := μ) (A := A) (A' := A) Filter.EventuallyEq.rfl hu
  have fg : (fun ω => f ω * g ω) =ᵐ[μ] fun ω => f' ω * g' ω := hf.mul hg
  have fh : (fun ω => f ω * h ω) =ᵐ[μ] fun ω => f' ω * h' ω := hf.mul hh
  have gh : (fun ω => g ω * h ω) =ᵐ[μ] fun ω => g' ω * h' ω := hg.mul hh
  have fgh : (fun ω => f ω * g ω * h ω) =ᵐ[μ] fun ω => f' ω * g' ω * h' ω := (hf.mul hg).mul hh
  rw [e fgh, e fg, e fh, e gh, e hf, e hg, e hh]
theorem gibbsCumulantFour_congr_ae (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') (hh : h =ᵐ[μ] h')
    (hl : l =ᵐ[μ] l') :
    gibbsCumulantFour μ A f g h l = gibbsCumulantFour μ A f' g' h' l' := by
  unfold gibbsCumulantFour
  have e := fun {u u' : Ω → ℝ} (hu : u =ᵐ[μ] u') =>
    gibbsMean_congr_ae (μ := μ) (A := A) (A' := A) Filter.EventuallyEq.rfl hu
  have fg : (fun ω => f ω * g ω) =ᵐ[μ] fun ω => f' ω * g' ω := hf.mul hg
  have fh : (fun ω => f ω * h ω) =ᵐ[μ] fun ω => f' ω * h' ω := hf.mul hh
  have fl : (fun ω => f ω * l ω) =ᵐ[μ] fun ω => f' ω * l' ω := hf.mul hl
  have gh : (fun ω => g ω * h ω) =ᵐ[μ] fun ω => g' ω * h' ω := hg.mul hh
  have gl : (fun ω => g ω * l ω) =ᵐ[μ] fun ω => g' ω * l' ω := hg.mul hl
  have hl2 : (fun ω => h ω * l ω) =ᵐ[μ] fun ω => h' ω * l' ω := hh.mul hl
  have fgh : (fun ω => f ω * g ω * h ω) =ᵐ[μ] fun ω => f' ω * g' ω * h' ω := (hf.mul hg).mul hh
  have fgl : (fun ω => f ω * g ω * l ω) =ᵐ[μ] fun ω => f' ω * g' ω * l' ω := (hf.mul hg).mul hl
  have fhl : (fun ω => f ω * h ω * l ω) =ᵐ[μ] fun ω => f' ω * h' ω * l' ω := (hf.mul hh).mul hl
  have ghl : (fun ω => g ω * h ω * l ω) =ᵐ[μ] fun ω => g' ω * h' ω * l' ω := (hg.mul hh).mul hl
  have fghl : (fun ω => f ω * g ω * h ω * l ω) =ᵐ[μ] fun ω => f' ω * g' ω * h' ω * l' ω :=
    ((hf.mul hg).mul hh).mul hl
  rw [e fghl, e fgh, e fgl, e fhl, e ghl, e fg, e hl2, e fh, e gl, e fl, e gh, e hf, e hg, e hh, e hl]
end Congr
end GibbsMeanExpansionInField
set_option maxHeartbeats 2000000 in
open GibbsMeanExpansionInField in
theorem gibbsMeanExpansionInField_holds (hS : IteratedFDerivSlices)
    (hW : GibbsMeanDifferentiation) (hDom : DominatedFamilyOnClosedBalls) :
    GibbsMeanExpansionInField := by
  intro F ρ μ V A H hfin hμ0 hμc hA hH
  obtain ⟨-, hMean⟩ := hW
  have := hfin
  have dom : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), JointlyContDiffOnBalls ρ V G →
      ∃ r M : ℝ, 0 < r ∧ IsDominatedSmoothFamily μ 3 (Metric.ball 0 r) M
        (fun τ η => G η (leftTranslate (bondSpread c X τ) V)) := by
    intro k c X G hG
    have hπ : ContDiff ℝ 3 (fun z : (Fin k → ℝ) × (ℝ × StepVariable (finiteCells F)) => (z.1, z.2.2)) :=
      contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
    obtain ⟨r, M, hr, hD⟩ := hDom ↥(chordBonds (finiteCells F)) k ρ μ
      (fun z => G z.2.2 (leftTranslate (bondSpread c X z.1) V)) hμc
      (fun v η _ hη => ContDiffAt.comp
        (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
        (0, v, η) (hG k c X η hη) hπ.contDiffAt)
    exact ⟨r, M, hr, hD 0 (by simp)⟩
  have mono : ∀ {k : ℕ} {B B' : Set (Fin k → ℝ)} {K K' : ℝ}
      {G : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ},
      B' ⊆ B → K ≤ K' → IsDominatedSmoothFamily μ 3 B K G → IsDominatedSmoothFamily μ 3 B' K' G := by
    intro k B B' K K' G hB hK h
    refine ⟨fun τ hτ => h.aestronglyMeasurable τ (hB hτ), ?_, ?_⟩
    · filter_upwards [h.contDiffOn] with ω hω using hω.mono hB
    · filter_upwards [h.norm_iteratedFDeriv_le] with ω hω j hj τ hτ using le_trans (hω j hj τ (hB hτ)) hK
  have pair : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ∃ (B : Set (Fin k → ℝ)) (K : ℝ), IsOpen B ∧ B ∈ 𝓝 (0 : Fin k → ℝ) ∧
        IsDominatedSmoothFamily μ 3 B K (fun τ η => A η (leftTranslate (bondSpread c X τ) V)) ∧
        IsDominatedSmoothFamily μ 3 B K (fun τ η => H η (leftTranslate (bondSpread c X τ) V)) := by
    intro k c X
    obtain ⟨r₁, M₁, h₁, d₁⟩ := dom k c X A hA
    obtain ⟨r₂, M₂, h₂, d₂⟩ := dom k c X H hH
    refine ⟨Metric.ball 0 (min r₁ r₂), max M₁ M₂, Metric.isOpen_ball,
      Metric.ball_mem_nhds _ (lt_min h₁ h₂), mono (Metric.ball_subset_ball (min_le_left _ _))
        (le_max_left _ _) d₁, mono (Metric.ball_subset_ball (min_le_right _ _)) (le_max_right _ _) d₂⟩
  have fam : ∀ {k j : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), JointlyContDiffOnBalls ρ V G → j ≤ 3 →
      ∀ (v : Fin j → Fin k → ℝ) (e : Fin j → Fin k) (c' : Fin j → F.Site F.top × Fin 4)
        (X' : Fin j → imaginaryQuaternions),
      Function.Injective e → v = (fun l => Pi.single (e l) 1) → c ∘ e = c' → X ∘ e = X' →
      paramIteratedDeriv (fun τ η => G η (leftTranslate (bondSpread c X τ) V)) v 0 =ᵐ[μ]
        fieldDeriv G V c' X' := by
    intro k j c X G hG hj v e c' X' he hv hc hX
    filter_upwards [hμc] with η hη
    have hs : ContDiffAt ℝ j (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) 0 := by
      have h3 := hG k c X η hη
      have hemb : ContDiff ℝ 3 (fun τ : Fin k → ℝ => (τ, η)) := contDiff_id.prodMk contDiff_const
      have := ContDiffAt.comp
        (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
        (0 : Fin k → ℝ) h3 hemb.contDiffAt
      exact ContDiffAt.of_le this (by exact_mod_cast hj)
    subst hv hc hX
    exact iteratedFDeriv_sublist_eq_bondDeriv hS (G η) V c X he hs
  have fam1 : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), JointlyContDiffOnBalls ρ V G → ∀ i : Fin k,
      paramIteratedDeriv (fun τ η => G η (leftTranslate (bondSpread c X τ) V)) ![Pi.single i 1] 0 =ᵐ[μ]
        fieldDerivOne G V c X i := by
    intro k c X G hG i
    exact fam (j := 1) c X G hG (by norm_num) _ ![i] _ _ (Function.injective_of_subsingleton _)
      (by funext l; fin_cases l; rfl) (by funext l; fin_cases l; rfl) (by funext l; fin_cases l; rfl)
  have fam2 : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), JointlyContDiffOnBalls ρ V G →
      ∀ i j : Fin k, i ≠ j →
      paramIteratedDeriv (fun τ η => G η (leftTranslate (bondSpread c X τ) V))
        ![Pi.single i 1, Pi.single j 1] 0 =ᵐ[μ] fieldDerivTwo G V c X i j := by
    intro k c X G hG i j hij
    exact fam (j := 2) c X G hG (by norm_num) _ ![i, j] _ _
      (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
      (by funext l; fin_cases l <;> rfl) (by funext l; fin_cases l <;> rfl)
      (by funext l; fin_cases l <;> rfl)
  have famFull : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), JointlyContDiffOnBalls ρ V G → k ≤ 3 →
      ∀ v : Fin k → Fin k → ℝ, v = (fun l => Pi.single l 1) →
      paramIteratedDeriv (fun τ η => G η (leftTranslate (bondSpread c X τ) V)) v 0 =ᵐ[μ]
        fieldDeriv G V c X := by
    intro k c X G hG hk v hv
    exact fam c X G hG hk v id c X Function.injective_id hv rfl rfl
  have h0 : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ),
      (fun η => G η (leftTranslate (bondSpread c X (0 : Fin k → ℝ)) V)) = fun η => G η V := by
    intro k c X G
    funext η
    rw [leftTranslate_bondSpread_zero]
  refine ⟨fun k c X => ?_, ?_⟩
  · obtain ⟨B, K, hBo, hB0, dA, dH⟩ := pair k c X
    exact (hMean (StepVariable (finiteCells F)) μ k B K _ _ hBo hμ0 dA dH).1.contDiffAt hB0
  constructor
  · intro c X
    obtain ⟨B, K, hBo, hB0, dA, dH⟩ := pair 1 c X
    have hM := (hMean (StepVariable (finiteCells F)) μ 1 B K _ _ hBo hμ0 dA dH).2 0 (mem_of_mem_nhds hB0)
      (Pi.single 0 1) (Pi.single 0 1) (Pi.single 0 1)
    have hu : (fun l : Fin 1 => (Pi.single l 1 : Fin 1 → ℝ)) = ![Pi.single 0 1] := by
      funext l
      fin_cases l
      rfl
    have e0 : bondDeriv (gibbsMeanAt μ A H) V c X = iteratedFDeriv ℝ 1 (fun τ : Fin 1 → ℝ =>
        gibbsMean μ (fun η => A η (leftTranslate (bondSpread c X τ) V))
          (fun η => H η (leftTranslate (bondSpread c X τ) V))) 0 ![Pi.single 0 1] := by
      unfold bondDeriv gibbsMeanAt
      rw [hu]
    rw [e0]
    refine hM.1.trans ?_
    beta_reduce
    rw [h0 c X A, h0 c X H]
    have eH0 : (fun η => H η V) =ᵐ[μ] fun η => H η V := Filter.EventuallyEq.rfl
    rw [gibbsMean_congr_ae Filter.EventuallyEq.rfl (famFull c X H hH (by norm_num) _ hu.symm),
      gibbsCovariance_congr_ae eH0 (famFull c X A hA (by norm_num) _ hu.symm)]
  · intro c X
    obtain ⟨B, K, hBo, hB0, dA, dH⟩ := pair 2 c X
    have hM := (hMean (StepVariable (finiteCells F)) μ 2 B K _ _ hBo hμ0 dA dH).2 0 (mem_of_mem_nhds hB0)
      (Pi.single 1 1) (Pi.single 0 1) (Pi.single 0 1)
    have hu : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
      funext l
      fin_cases l <;> rfl
    have e0 : bondDeriv (gibbsMeanAt μ A H) V c X = iteratedFDeriv ℝ 2 (fun τ : Fin 2 → ℝ =>
        gibbsMean μ (fun η => A η (leftTranslate (bondSpread c X τ) V))
          (fun η => H η (leftTranslate (bondSpread c X τ) V))) 0 ![Pi.single 0 1, Pi.single 1 1] := by
      unfold bondDeriv gibbsMeanAt
      rw [hu]
    rw [e0]
    refine hM.2.1.trans ?_
    beta_reduce
    rw [h0 c X A, h0 c X H]
    have eH0 : (fun η => H η V) =ᵐ[μ] fun η => H η V := Filter.EventuallyEq.rfl
    rw [gibbsMean_congr_ae Filter.EventuallyEq.rfl (famFull c X H hH (by norm_num) _ hu.symm),
      gibbsCovariance_congr_ae (fam1 c X H hH 1) (fam1 c X A hA 0),
      gibbsCovariance_congr_ae (fam1 c X H hH 0) (fam1 c X A hA 1),
      gibbsCovariance_congr_ae eH0 (famFull c X A hA (by norm_num) _ hu.symm),
      gibbsCumulantThree_congr_ae eH0 (fam1 c X A hA 1) (fam1 c X A hA 0)]
  · intro c X
    obtain ⟨B, K, hBo, hB0, dA, dH⟩ := pair 3 c X
    have hM := (hMean (StepVariable (finiteCells F)) μ 3 B K _ _ hBo hμ0 dA dH).2 0 (mem_of_mem_nhds hB0)
      (Pi.single 2 1) (Pi.single 1 1) (Pi.single 0 1)
    have hu : (fun l : Fin 3 => (Pi.single l 1 : Fin 3 → ℝ)) =
        ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] := by
      funext l
      fin_cases l <;> rfl
    have e0 : bondDeriv (gibbsMeanAt μ A H) V c X = iteratedFDeriv ℝ 3 (fun τ : Fin 3 → ℝ =>
        gibbsMean μ (fun η => A η (leftTranslate (bondSpread c X τ) V))
          (fun η => H η (leftTranslate (bondSpread c X τ) V))) 0
          ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] := by
      unfold bondDeriv gibbsMeanAt
      rw [hu]
    rw [e0]
    refine hM.2.2.trans ?_
    beta_reduce
    rw [h0 c X A, h0 c X H]
    have eH0 : (fun η => H η V) =ᵐ[μ] fun η => H η V := Filter.EventuallyEq.rfl
    rw [gibbsMean_congr_ae Filter.EventuallyEq.rfl (famFull c X H hH (by norm_num) _ hu.symm),
      gibbsCovariance_congr_ae (fam2 c X H hH 1 2 (by decide)) (fam1 c X A hA 0),
      gibbsCovariance_congr_ae (fam2 c X H hH 0 2 (by decide)) (fam1 c X A hA 1),
      gibbsCovariance_congr_ae (fam2 c X H hH 0 1 (by decide)) (fam1 c X A hA 2),
      gibbsCovariance_congr_ae (fam1 c X H hH 2) (fam2 c X A hA 0 1 (by decide)),
      gibbsCovariance_congr_ae (fam1 c X H hH 1) (fam2 c X A hA 0 2 (by decide)),
      gibbsCovariance_congr_ae (fam1 c X H hH 0) (fam2 c X A hA 1 2 (by decide)),
      gibbsCumulantThree_congr_ae (fam1 c X H hH 2) (fam1 c X A hA 1) (fam1 c X A hA 0),
      gibbsCumulantThree_congr_ae (fam1 c X H hH 1) (fam1 c X A hA 2) (fam1 c X A hA 0),
      gibbsCumulantThree_congr_ae (fam1 c X H hH 0) (fam1 c X A hA 2) (fam1 c X A hA 1),
      gibbsCovariance_congr_ae eH0 (famFull c X A hA (by norm_num) _ hu.symm),
      gibbsCumulantThree_congr_ae eH0 (fam2 c X A hA 1 2 (by decide)) (fam1 c X A hA 0),
      gibbsCumulantThree_congr_ae eH0 (fam2 c X A hA 0 2 (by decide)) (fam1 c X A hA 1),
      gibbsCumulantThree_congr_ae eH0 (fam2 c X A hA 0 1 (by decide)) (fam1 c X A hA 2),
      gibbsCumulantFour_congr_ae eH0 (fam1 c X A hA 2) (fam1 c X A hA 1) (fam1 c X A hA 0)]
end Estimates
end YangMills.Construction
end
