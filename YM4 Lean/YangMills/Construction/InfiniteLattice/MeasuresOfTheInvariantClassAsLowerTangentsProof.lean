import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayer
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.FactsOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.MeasuresOfTheInvariantClassAsLowerTangents
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.NormalFamilies
noncomputable section
namespace YangMills.Construction.InfiniteLattice.InvariantGibbsLowerTangent
theorem mean_mul_le_log_integral_exp_sub {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ρ f : X → ℝ) (s : ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hZ : 0 < ∫ x, ρ x ∂μ) (hρi : Integrable ρ μ)
    (hf : Integrable (fun x => f x * ρ x) μ)
    (hs : Integrable (fun x => ρ x * Real.exp (s * f x)) μ) :
    s * ((∫ x, f x * ρ x ∂μ) / ∫ x, ρ x ∂μ) ≤
      Real.log (∫ x, ρ x * Real.exp (s * f x) ∂μ) - Real.log (∫ x, ρ x ∂μ) := by
  set Z := ∫ x, ρ x ∂μ with hZdef
  set m := ∫ x, f x * ρ x ∂μ with hmdef
  set M := s * (m / Z) with hMdef
  have hpoint : ∀ x, (Real.exp M * (1 - M)) * ρ x + (Real.exp M * s) * (f x * ρ x) ≤
      ρ x * Real.exp (s * f x) := by
    intro x
    have h1 := Real.add_one_le_exp (s * f x - M)
    have h2 : Real.exp (s * f x) = Real.exp M * Real.exp (s * f x - M) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp M * (s * f x - M + 1) ≤ Real.exp (s * f x) := by
      rw [h2]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos M).le
    have h4 := mul_le_mul_of_nonneg_left h3 (hρ x)
    nlinarith [h4]
  have hint : Integrable (fun x => (Real.exp M * (1 - M)) * ρ x +
      (Real.exp M * s) * (f x * ρ x)) μ := (hρi.const_mul _).add (hf.const_mul _)
  have hmono := integral_mono hint hs hpoint
  have hval : ∫ x, ((Real.exp M * (1 - M)) * ρ x + (Real.exp M * s) * (f x * ρ x)) ∂μ =
      Real.exp M * Z := by
    rw [integral_add (hρi.const_mul _) (hf.const_mul _), integral_const_mul, integral_const_mul,
      ← hZdef, ← hmdef, hMdef]
    field_simp
    ring
  rw [hval] at hmono
  have hpos : 0 < Real.exp M * Z := mul_pos (Real.exp_pos M) hZ
  have hlog := Real.log_le_log hpos hmono
  rw [Real.log_mul (Real.exp_pos M).ne' hZ.ne', Real.log_exp] at hlog
  linarith
def windowObsSum (A : LocalObservableArray) (W : LinkWindow 1) (U : GaugeField 1) : ℝ :=
  ∑ᶠ i ∈ A.labelsTouching W, (A.translate i U).re
theorem windowEnergy_eq_sub (A : LocalObservableArray) (β s : ℝ) (W : LinkWindow 1)
    (U : GaugeField 1) :
    A.windowEnergy β s W U = A.windowEnergy β 0 W U - s * windowObsSum A W U := by
  simp [LocalObservableArray.windowEnergy, windowObsSum]
theorem integrable_mul_of_ofReal_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (h : Integrable (fun x => (f x : ℂ) * (g x : ℂ)) μ) :
    Integrable (fun x => f x * g x) μ := by
  have h' : Integrable (fun x => ((f x * g x : ℝ) : ℂ)) μ := by
    simpa only [Complex.ofReal_mul] using h
  exact h'.re.congr (Filter.Eventually.of_forall fun x => by
    simp only [RCLike.re_to_complex, Complex.ofReal_re])
theorem integrable_of_isBoundedObservable {ν : Measure (GaugeField 1)} [IsFiniteMeasure ν]
    {F : GaugeField 1 → ℂ} (h : IsBoundedObservable F) : Integrable F ν := by
  obtain ⟨hm, C, hC⟩ := h
  exact Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
theorem mul_tiltedKernel_le_log_windowPartition_sub (A : LocalObservableArray) (β s : ℝ)
    (W : LinkWindow 1)
    (h₀ : A.TiltedKernelWellDefined β 0) (hs : A.TiltedKernelWellDefined β s)
    (hW : IsBoundedObservable fun U => (windowObsSum A W U : ℂ)) (U' : GaugeField 1) :
    s * (A.tiltedKernel β 0 W (fun U => (windowObsSum A W U : ℂ)) U').re ≤
      Real.log (A.windowPartition β s W U') - Real.log (A.windowPartition β 0 W U') := by
  have hone : IsBoundedObservable (fun _ : GaugeField 1 => ((1 : ℝ) : ℂ)) :=
    ⟨measurable_const, 1, fun _ => by simp⟩
  set ρ : W.Assignments → ℝ := fun V => Real.exp (-A.windowEnergy β 0 W (W.glue one_pos V U'))
    with hρ
  set f : W.Assignments → ℝ := fun V => windowObsSum A W (W.glue one_pos V U') with hf
  have hIρ : Integrable ρ W.haarProd := by
    have := integrable_mul_of_ofReal_mul (h₀.integrable_weighted W _ hone U')
    simpa only [one_mul] using this
  have hIf : Integrable (fun V => f V * ρ V) W.haarProd :=
    integrable_mul_of_ofReal_mul (h₀.integrable_weighted W _ hW U')
  have hexp : ∀ V, Real.exp (-A.windowEnergy β s W (W.glue one_pos V U')) =
      ρ V * Real.exp (s * f V) := by
    intro V
    rw [hρ, hf]
    simp only
    rw [← Real.exp_add, windowEnergy_eq_sub A β s]
    ring_nf
  have hIs : Integrable (fun V => ρ V * Real.exp (s * f V)) W.haarProd := by
    have := integrable_mul_of_ofReal_mul (hs.integrable_weighted W _ hone U')
    simpa only [one_mul, hexp] using this
  have hZ₀ : A.windowPartition β 0 W U' = ∫ V, ρ V ∂W.haarProd := rfl
  have hZs : A.windowPartition β s W U' = ∫ V, ρ V * Real.exp (s * f V) ∂W.haarProd := by
    simp only [LocalObservableArray.windowPartition, hexp]
  have hpos : 0 < ∫ V, ρ V ∂W.haarProd := hZ₀ ▸ h₀.windowPartition_pos W U'
  have hker : (A.tiltedKernel β 0 W (fun U => (windowObsSum A W U : ℂ)) U').re =
      (∫ V, f V * ρ V ∂W.haarProd) / ∫ V, ρ V ∂W.haarProd := by
    have hnum : (∫ V, ((windowObsSum A W (W.glue one_pos V U') : ℝ) : ℂ) *
        ((Real.exp (-A.windowEnergy β 0 W (W.glue one_pos V U')) : ℝ) : ℂ) ∂W.haarProd) =
        ((∫ V, f V * ρ V ∂W.haarProd : ℝ) : ℂ) := by
      have hfun : (fun V => ((windowObsSum A W (W.glue one_pos V U') : ℝ) : ℂ) *
          ((Real.exp (-A.windowEnergy β 0 W (W.glue one_pos V U')) : ℝ) : ℂ)) =
          fun V => ((f V * ρ V : ℝ) : ℂ) := funext fun V => (Complex.ofReal_mul _ _).symm
      rw [hfun, integral_complex_ofReal]
    simp only [LocalObservableArray.tiltedKernel]
    rw [hnum, hZ₀, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hker, hZ₀, hZs]
  exact mean_mul_le_log_integral_exp_sub W.haarProd ρ f s (fun _ => (Real.exp_pos _).le) hpos
    hIρ hIf hIs
theorem lower_tangent_of_log_gap {t a n N κ D b L G β : ℝ} (hD : 0 < D) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (ha : |a| ≤ n) (hc : |N - κ * D| ≤ b * L)
    (hG : t * (N * a) - 12 * (2 * β + |t| * n) * b * L ≤ G) :
    t * κ * a - 24 * (β + |t| * n) * b * (L / D) ≤ 1 / D * G := by
  have hn : 0 ≤ n := (abs_nonneg a).trans ha
  have hbL : 0 ≤ b * L := mul_nonneg hb hL
  have h1 : |t * a * (N - κ * D)| ≤ |t| * n * (b * L) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ha (abs_nonneg t)) hc (abs_nonneg _)
      (mul_nonneg (abs_nonneg t) hn)
  have h2 := (abs_le.mp h1).1
  have h4 : 0 ≤ |t| * n * (b * L) := mul_nonneg (mul_nonneg (abs_nonneg t) hn) hbL
  have h3 : t * κ * D * a - 24 * (β + |t| * n) * b * L ≤ G := by
    nlinarith [h2, h4, hG]
  have h5 : t * κ * a - 24 * (β + |t| * n) * b * (L / D) =
      (t * κ * D * a - 24 * (β + |t| * n) * b * L) / D := by
    field_simp
  rw [h5, one_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right h3 hD.le
theorem shell_defect_le {c b L D r S : ℝ} (hc : 0 ≤ c) (hL₀ : 0 ≤ L) (hD : 0 < D) (hr : 0 ≤ r)
    (hb : b ≤ 17 * r ^ 4) (hL : L ≤ 4 * r * D * S) :
    24 * c * b * (L / D) ≤ 1632 * c * r ^ 5 * S := by
  have h1 : L / D ≤ 4 * r * S := by
    rw [div_le_iff₀ hD]
    linarith
  have h2 : b * (L / D) ≤ 17 * r ^ 4 * (4 * r * S) :=
    mul_le_mul hb h1 (div_nonneg hL₀ hD.le) (mul_nonneg (by norm_num) (pow_nonneg hr 4))
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) hc)
  nlinarith [h3]
open LocalObservableArray in
theorem invariantGibbsLowerTangentClaim_holds (hSurface : BoxTorusSurfaceBound.AllData)
    (hBox : FundamentalBox.RepresentsQuotientWithThinShell)
    (hFacts : ToriArraysAndTiltedMeasuresFacts)
    (hElem : ElementaryLatticeFacts) :
    InvariantGibbsLowerTangentClaim := by
  intro d β hβ ν hν t
  obtain ⟨⟨hprob, hgibbs⟩, hinv⟩ := hν
  have := hprob
  obtain ⟨hT, hArr, -, -⟩ := hFacts β hβ
  have hfaith := (hT 1 one_pos d.periodSublattice).1
  have hfi : d.periodSublattice.periods.FiniteIndex := hfaith.periods_finiteIndex
  obtain ⟨-, hcard, -, hshell⟩ :=
    hBox d.normalFrame d.sideLengths d.periodSublattice d.periodSublattice_isBoxShaped
  have hDfin : (d.normalFrame.fundamentalBox d.sideLengths).Finite :=
    Set.finite_of_encard_eq_coe hcard
  have hDcard : (d.normalFrame.fundamentalBox d.sideLengths).ncard =
      d.periodSublattice.periods.index := by
    rw [Set.ncard, hcard]
    simp
  have hDpos : (0 : ℝ) < ((d.normalFrame.fundamentalBox d.sideLengths).ncard : ℝ) := by
    rw [hDcard]
    exact_mod_cast Nat.pos_of_ne_zero hfi.index_ne_zero
  have hBfin : (d.normalFrame.boxLinks d.sideLengths).Finite := by
    refine ((hDfin.prod (Set.finite_univ (α := Fin 4))).image
      (fun q : LatticePoint 1 × Fin 4 => Link.forwardFrom q.1 q.2)).subset ?_
    rintro b ⟨x, hx, μ, rfl⟩
    exact ⟨(x, μ), ⟨hx, Set.mem_univ _⟩, rfl⟩
  let W : LinkWindow 1 := ⟨hBfin.toFinset, fun b hb => by
    obtain ⟨x, -, μ, rfl⟩ := hBfin.mem_toFinset.mp hb
    exact ⟨μ, add_sub_cancel_left x (axisStep 1 μ)⟩⟩
  have hWb : (W.links : Set (Link 1)) = d.normalFrame.boxLinks d.sideLengths :=
    hBfin.coe_toFinset
  obtain ⟨-, hanc, hsb⟩ := hSurface d β hβ
  obtain ⟨hlog, hcount⟩ := hsb W hWb
  obtain ⟨-, -, -, hLoc, -, -, -, hIso, -⟩ := hElem 1 β one_pos hβ
  obtain ⟨hadd, -, hconst, -⟩ := hLoc
  set A := d.obsArray with hA
  have hdef₀ := (hArr A 0).2.1
  have hdeft := (hArr A t).2.1
  have hfinI : (A.labelsTouching W).Finite :=
    (hArr A 0).1.finite_labelsTouching W
  have hterm : ∀ i : A.Label, A.translate i ∈ continuousLocalFunctions 1 := by
    intro i
    obtain ⟨-, -, -, -, himg, -, -⟩ := hIso (shift (i.1 : LatticePoint 1)) (shift (i.1 : LatticePoint 1))
    rw [← himg]
    exact Set.mem_image_of_mem _ d.obs_mem
  have hsum : (fun U => (windowObsSum A W U : ℂ)) =
      fun U => ∑ i ∈ hfinI.toFinset, A.translate i U := by
    funext U
    rw [windowObsSum, finsum_mem_eq_finite_toFinset_sum _ hfinI, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    apply Complex.ext
    · simp
    · rw [Complex.ofReal_im]
      exact (d.obs_im _).symm
  have hmemSum : ∀ s : Finset A.Label,
      (fun U => ∑ i ∈ s, A.translate i U) ∈ continuousLocalFunctions 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hconst 0
    | insert i s hi ih =>
      have := (hadd _ (hterm i) _ ih).1
      have hfun : (fun U => ∑ j ∈ insert i s, A.translate j U) =
          A.translate i + fun U => ∑ j ∈ s, A.translate j U := by
        funext U
        simp [Finset.sum_insert hi]
      rw [hfun]
      exact this
  have hmem : (fun U => (windowObsSum A W U : ℂ)) ∈ continuousLocalFunctions 1 := by
    rw [hsum]
    exact hmemSum _
  have hobs : IsBoundedObservable fun U => (windowObsSum A W U : ℂ) := hmem.1
  have hvalue : ∫ U, (windowObsSum A W U : ℂ) ∂ν =
      ((A.labelsTouching W).ncard : ℂ) * stateEval ν d.obs := by
    rw [hsum, integral_finsetSum _ fun i _ => integrable_of_isBoundedObservable (hterm i).1]
    have heach : ∀ i ∈ hfinI.toFinset, ∫ U, A.translate i U ∂ν = stateEval ν d.obs := by
      intro i _
      obtain ⟨-, -, -, -, -, -, hlast⟩ :=
        hIso (shift (i.1 : LatticePoint 1)) (shift (i.1 : LatticePoint 1))
      exact ((hlast ν hprob).2.2.mp (hinv _ i.1.2)) d.obs d.obs_mem
    rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul,
      Set.ncard_eq_toFinset_card _ hfinI]
  have hker : A.tiltedKernel β 0 W (fun U => (windowObsSum A W U : ℂ)) =
      W.conditionalExpectation one_pos β (fun U => (windowObsSum A W U : ℂ)) :=
    hdef₀.tiltedKernel_zero W _ hobs
  have hPobs := hdef₀.isBoundedObservable_tiltedKernel W _ hobs
  have hPint : Integrable (A.tiltedKernel β 0 W (fun U => (windowObsSum A W U : ℂ))) ν :=
    integrable_of_isBoundedObservable hPobs
  have hP : ∫ U, A.tiltedKernel β 0 W (fun U => (windowObsSum A W U : ℂ)) U ∂ν =
      ((A.labelsTouching W).ncard : ℂ) * stateEval ν d.obs := by
    rw [hker, hgibbs W _ hmem, hvalue]
  set n := observableSupNorm d.obs with hn
  set a := (stateEval ν d.obs).re with ha
  set N : ℝ := ((A.labelsTouching W).ncard : ℝ) with hN
  set b : ℝ := (boxCoverNumber d.boxWidth : ℝ) with hb
  set L : ℝ := ((d.normalFrame.boundaryShell d.sideLengths d.boxWidth).ncard : ℝ) with hL
  set D : ℝ := ((d.normalFrame.fundamentalBox d.sideLengths).ncard : ℝ) with hD
  set Zt := A.tiltedPartition d.periodSublattice β t with hZt
  set Z₀ := A.tiltedPartition d.periodSublattice β 0 with hZ₀
  have hn₀ : 0 ≤ n := Real.iSup_nonneg fun _ => norm_nonneg _
  have hb₀ : 0 ≤ b := Nat.cast_nonneg _
  have hL₀ : 0 ≤ L := Nat.cast_nonneg _
  have hbound : ∀ U, ‖d.obs U‖ ≤ n := by
    obtain ⟨-, C, hC⟩ := d.obs_mem.1
    exact fun U => le_ciSup (f := fun U => ‖d.obs U‖) ⟨C, by
      rintro _ ⟨U, rfl⟩
      exact hC U⟩ U
  have habs : |a| ≤ n := by
    have h1 : ‖stateEval ν d.obs‖ ≤ n := by
      have := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hbound)
      simpa [stateEval] using this
    exact (Complex.abs_re_le_norm _).trans h1
  have hper : ∀ U', t * (A.tiltedKernel β 0 W (fun U => (windowObsSum A W U : ℂ)) U').re ≤
      Real.log Zt - Real.log Z₀ + 12 * (2 * β + |t| * n) * b * L := by
    intro U'
    have h1 := mul_tiltedKernel_le_log_windowPartition_sub A β t W hdef₀ hdeft hobs U'
    have h2 := (abs_le.mp (hlog t U')).2
    have h3 := (abs_le.mp (hlog 0 U')).1
    simp only [abs_zero, zero_mul, add_zero] at h3
    have h12 : ((Constants.BoxTorus.surfaceNumber : ℕ) : ℝ) = 12 := by
      norm_num [Constants.BoxTorus.surfaceNumber]
    rw [h12] at h2 h3
    linarith
  have hG : t * (N * a) - 12 * (2 * β + |t| * n) * b * L ≤ Real.log Zt - Real.log Z₀ := by
    have hint := integral_mono (μ := ν)
      (f := fun U' => t * (A.tiltedKernel β 0 W (fun U => (windowObsSum A W U : ℂ)) U').re)
      (g := fun _ => Real.log Zt - Real.log Z₀ + 12 * (2 * β + |t| * n) * b * L)
      (hPint.re.const_mul t) (integrable_const _) hper
    have hre : ∫ U', (A.tiltedKernel β 0 W (fun U => (windowObsSum A W U : ℂ)) U').re ∂ν =
        N * a := by
      have := Complex.reCLM.integral_comp_comm hPint
      simp only [Complex.reCLM_apply] at this
      rw [this, hP, hN, ha]
      simp
    rw [integral_const_mul, hre, integral_const] at hint
    simp only [probReal_univ, one_smul] at hint
    linarith
  have hZtpos : 0 < Zt :=
    ((hArr A t).2.2 d.periodSublattice d.periods_le_translationGroup).tiltedPartition_pos
  have hZ₀pos : 0 < Z₀ :=
    ((hArr A 0).2.2 d.periodSublattice d.periods_le_translationGroup).tiltedPartition_pos
  have hc : 0 ≤ β + |t| * n := add_nonneg hβ.le (mul_nonneg (abs_nonneg t) hn₀)
  have h24 : ((Constants.BoxTorus.tangentNumber : ℕ) : ℝ) = 24 := by
    norm_num [Constants.BoxTorus.tangentNumber, Constants.BoxTorus.surfaceNumber]
  have h1632 : ((Constants.BoxTorus.tangentSideNumber : ℕ) : ℝ) = 1632 := by
    norm_num [Constants.BoxTorus.tangentSideNumber, Constants.BoxTorus.tangentNumber,
      Constants.BoxTorus.surfaceNumber, Constants.BoxTorus.anchorNumber,
      Constants.BoxTorus.layerNumber]
  have h17 : ((Constants.BoxTorus.anchorNumber : ℕ) : ℝ) = 17 := by
    norm_num [Constants.BoxTorus.anchorNumber]
  have h4 : ((Constants.BoxTorus.layerNumber : ℕ) : ℝ) = 4 := by
    norm_num [Constants.BoxTorus.layerNumber]
  have hlay := hshell d.boxWidth
  rw [h4] at hlay
  rw [h17] at hanc
  refine ⟨?_, ?_⟩
  · have := lower_tangent_of_log_gap (t := t) (a := a) (n := n) (N := N) (κ := A.invIndex)
      (D := D) (b := b) (L := L) (G := Real.log Zt - Real.log Z₀) (β := β) hDpos hb₀ hL₀ habs
      hcount hG
    simp only [LocalObservableArray.shellDefect, LocalObservableArray.logTiltRatioPerSite,
      LocalObservableArray.untiltedTorusPartition]
    rw [h24, Real.log_div hZtpos.ne' hZ₀pos.ne']
    exact this
  · have := shell_defect_le (c := β + |t| * n) (b := b) (L := L) (D := D)
      (r := ((d.boxWidth : ℕ) : ℝ)) (S := ∑ i, (((d.sideLengths i : ℕ) : ℝ))⁻¹) hc hL₀ hDpos
      (Nat.cast_nonneg _) hanc hlay
    simp only [LocalObservableArray.shellDefect, LocalObservableArray.sideDefect]
    rw [h24, h1632]
    linarith
end YangMills.Construction.InfiniteLattice.InvariantGibbsLowerTangent
