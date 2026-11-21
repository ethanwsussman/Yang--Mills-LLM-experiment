import YangMills.Construction.Lattice.BlockItsPathsAndALogarithm
import YangMills.Construction.Lattice.BondEndpointsAndFiniteness
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.EliminationMapOfAFormedSet
import YangMills.Construction.Lattice.LinearisedConstraintAtAFormedBond
import YangMills.Construction.Lattice.LinearisingCorrectionOfAFormedSet
import YangMills.Construction.Lattice.PivotOfBond
import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import YangMills.Construction.Lattice.SeriesLogarithmOnTheComplexGroup
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealFormProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Coordinates
namespace PeriodicLattice.LinearizingCorrection
theorem implicit_solution_of_rightInverse {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (g : E → W) (hg : ContDiffAt ℂ 1 g 0) (hg0 : g 0 = 0) (P : W →L[ℂ] E)
    (hP : ∀ y, fderiv ℂ g 0 (P y) = y) (S : Set E) (hS : S ∈ 𝓝 (0 : E)) :
    (∃ (d : E → W) (N : Set E), IsOpen N ∧ (0 : E) ∈ N ∧ d 0 = 0 ∧ DifferentiableOn ℂ d N ∧
      ∀ x ∈ N, x - P (d x) ∈ S ∧ g (x - P (d x)) = fderiv ℂ g 0 x) ∧
    ∀ d₁ d₂ : E → W, Tendsto d₁ (𝓝 0) (𝓝 0) → Tendsto d₂ (𝓝 0) (𝓝 0) →
      (∀ᶠ x in 𝓝 (0 : E), g (x - P (d₁ x)) = fderiv ℂ g 0 x) →
      (∀ᶠ x in 𝓝 (0 : E), g (x - P (d₂ x)) = fderiv ℂ g 0 x) →
      ∀ᶠ x in 𝓝 (0 : E), d₁ x = d₂ x := by
  set T : E →L[ℂ] W := fderiv ℂ g 0 with hTdef
  have hT : HasFDerivAt g T 0 :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt
  let lin : E × W →L[ℂ] E :=
    ContinuousLinearMap.fst ℂ E W - P.comp (ContinuousLinearMap.snd ℂ E W)
  let Φ : E × W → E × W := fun p => (p.1, g (lin p) - T p.1)
  have hlin0 : lin 0 = 0 := map_zero lin
  have hlin : ∀ p : E × W, lin p = p.1 - P p.2 := fun p => rfl
  have hΦ0 : Φ 0 = 0 := by
    simp [Φ, hlin0, hg0]
  let f' : E × W →L[ℂ] E × W :=
    (ContinuousLinearMap.fst ℂ E W).prod (-(ContinuousLinearMap.snd ℂ E W))
  let e : (E × W) ≃L[ℂ] (E × W) :=
    ContinuousLinearEquiv.equivOfInverse f' f'
      (fun p => by simp [f']) (fun p => by simp [f'])
  have hgl : HasFDerivAt (fun p => g (lin p)) (T.comp lin) (0 : E × W) := by
    have h1 : HasFDerivAt g T (lin 0) := by rwa [hlin0]
    exact h1.comp (0 : E × W) lin.hasFDerivAt
  have hΦd : HasFDerivAt Φ (e : E × W →L[ℂ] E × W) (0 : E × W) := by
    have h2 : HasFDerivAt (fun p : E × W => g (lin p) - T p.1)
        (T.comp lin - T.comp (ContinuousLinearMap.fst ℂ E W)) (0 : E × W) :=
      hgl.sub ((T.comp (ContinuousLinearMap.fst ℂ E W)).hasFDerivAt)
    have h3 := (ContinuousLinearMap.fst ℂ E W).hasFDerivAt (x := (0 : E × W)) |>.prodMk h2
    have heq : (e : E × W →L[ℂ] E × W) = (ContinuousLinearMap.fst ℂ E W).prod
        (T.comp lin - T.comp (ContinuousLinearMap.fst ℂ E W)) := by
      apply ContinuousLinearMap.ext
      intro p
      apply Prod.ext
      · simp [e, f']
      · simp [e, f', lin, hP]
    rw [heq]
    exact h3
  have hΦc : ContDiffAt ℂ 1 Φ (0 : E × W) := by
    have h1 : ContDiffAt ℂ 1 g (lin 0) := by rwa [hlin0]
    have h2 : ContDiffAt ℂ 1 (fun p => g (lin p)) (0 : E × W) :=
      h1.comp (0 : E × W) lin.contDiff.contDiffAt
    exact contDiffAt_fst.prodMk (h2.sub ((T.comp (ContinuousLinearMap.fst ℂ E W)).contDiff.contDiffAt))
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hs : HasStrictFDerivAt Φ (e : E × W →L[ℂ] E × W) (0 : E × W) :=
    hΦc.hasStrictFDerivAt' hΦd hn
  let Ψ := hΦc.localInverse hΦd hn
  have hΨc : ContDiffAt ℂ 1 Ψ (Φ 0) := hΦc.to_localInverse hΦd hn
  have hΨ0 : Ψ (Φ 0) = 0 := hΦc.localInverse_apply_image hΦd hn
  have hright : ∀ᶠ q in 𝓝 (Φ 0), Φ (Ψ q) = q := hs.eventually_right_inverse
  have hleft : ∀ᶠ p in 𝓝 (0 : E × W), Ψ (Φ p) = p := hs.eventually_left_inverse
  have hpath : ContDiffAt ℂ 1 (fun x : E => ((x, 0) : E × W)) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hpath0 : Tendsto (fun x : E => ((x, 0) : E × W)) (𝓝 0) (𝓝 (Φ 0)) := by
    rw [hΦ0]
    exact (hpath.continuousAt).tendsto
  have hdΨ : ContDiffAt ℂ 1 (fun x : E => Ψ (x, 0)) 0 := by
    have h1 : ContDiffAt ℂ 1 Ψ (((0 : E), (0 : W)) : E × W) := by
      have : (((0 : E), (0 : W)) : E × W) = Φ 0 := by rw [hΦ0]; rfl
      rwa [this]
    exact h1.comp (0 : E) hpath
  refine ⟨?_, ?_⟩
  · let d : E → W := fun x => (Ψ (x, 0)).2
    have hdc : ContDiffAt ℂ 1 d 0 := contDiffAt_snd.comp (0 : E) hdΨ
    have hd0 : d 0 = 0 := by
      have : Ψ ((0 : E), (0 : W)) = 0 := by
        have h0 : (((0 : E), (0 : W)) : E × W) = Φ 0 := by rw [hΦ0]; rfl
        rw [h0, hΨ0]
      simp [d, this]
    have hinv : ∀ᶠ x in 𝓝 (0 : E), Φ (Ψ (x, 0)) = (x, 0) := hpath0.eventually hright
    have hfst : ∀ᶠ x in 𝓝 (0 : E), (Ψ (x, 0)).1 = x := hinv.mono fun x hx => congrArg Prod.fst hx
    have heq : ∀ᶠ x in 𝓝 (0 : E), g (x - P (d x)) = T x := by
      filter_upwards [hinv, hfst] with x hx h1
      have h2 : g (lin (Ψ (x, 0))) - T (Ψ (x, 0)).1 = 0 := congrArg Prod.snd hx
      rw [hlin, h1] at h2
      exact sub_eq_zero.mp h2
    have hzero : Tendsto (fun x => x - P (d x)) (𝓝 0) (𝓝 0) := by
      have : ContinuousAt (fun x => x - P (d x)) 0 :=
        continuousAt_id.sub (P.continuous.continuousAt.comp hdc.continuousAt)
      simpa [ContinuousAt, hd0] using this
    have hinS : ∀ᶠ x in 𝓝 (0 : E), x - P (d x) ∈ S := hzero hS
    obtain ⟨u, hu, hdu⟩ := hdc.contDiffOn (m := 1) le_rfl (by simp)
    let N := interior (u ∩ {x | x - P (d x) ∈ S ∧ g (x - P (d x)) = T x})
    have hN0 : (0 : E) ∈ N := by
      refine mem_interior_iff_mem_nhds.mpr ?_
      exact inter_mem hu (hinS.and heq)
    refine ⟨d, N, isOpen_interior, hN0, hd0, ?_, ?_⟩
    · exact (hdu.differentiableOn (by norm_num)).mono
        (interior_subset.trans inter_subset_left)
    · intro x hx
      exact (interior_subset hx).2
  · intro d₁ d₂ h₁ h₂ e₁ e₂
    have key : ∀ d : E → W, Tendsto d (𝓝 0) (𝓝 0) →
        (∀ᶠ x in 𝓝 (0 : E), g (x - P (d x)) = T x) →
        ∀ᶠ x in 𝓝 (0 : E), Ψ (x, 0) = (x, d x) := by
      intro d hd he
      have hp : Tendsto (fun x => ((x, d x) : E × W)) (𝓝 0) (𝓝 (0 : E × W)) := (tendsto_id (x := 𝓝 (0 : E))).prodMk_nhds hd
      filter_upwards [hp.eventually hleft, he] with x hx hex
      have : Φ (x, d x) = (x, 0) := by
        change (x, g (lin (x, d x)) - T x) = (x, 0)
        rw [hlin]
        change (x, g (x - P (d x)) - T x) = (x, 0)
        rw [hex, sub_self]
      rwa [this] at hx
    filter_upwards [key d₁ h₁ e₁, key d₂ h₂ e₂] with x hx₁ hx₂
    have := hx₁.symm.trans hx₂
    exact congrArg Prod.snd this
def tracelessProjLinear : ComplexMatrix2 →ₗ[ℂ] ↥ComplexMatrix2.traceless where
  toFun X := ⟨X - ((1 / 2 : ℂ) * ComplexMatrix2.fullTrace X) • (1 : ComplexMatrix2), by
    change ComplexMatrix2.fullTrace _ = 0
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul, Nat.cast_ofNat]
    ring⟩
  map_add' X Y := by
    apply Subtype.ext
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_add, Submodule.coe_add]
    module
  map_smul' z X := by
    apply Subtype.ext
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul, RingHom.id_apply, Submodule.coe_smul,
      smul_eq_mul]
    module
def tracelessProj : ComplexMatrix2 →L[ℂ] ↥ComplexMatrix2.traceless :=
  LinearMap.toContinuousLinearMap tracelessProjLinear
theorem tracelessProj_coe_of_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    (tracelessProj X : ComplexMatrix2) = X := by
  have h : ComplexMatrix2.fullTrace X = 0 := hX
  change X - ((1 / 2 : ℂ) * ComplexMatrix2.fullTrace X) • (1 : ComplexMatrix2) = X
  simp [h]
theorem contDiffAt_logSeries_one (hEL : ComplexMatrix2.ExpLogEstimates) :
    ContDiffAt ℂ 1 ComplexMatrix2.logSeries (1 : ComplexMatrix2) := by
  have hexp : ContDiffAt ℂ 1 (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2) 0 :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (0 : ComplexMatrix2)).contDiffAt
  have hstrict : HasStrictFDerivAt (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2)
      (1 : ComplexMatrix2 →L[ℂ] ComplexMatrix2) 0 :=
    hasStrictFDerivAt_exp_zero
  have hd : HasFDerivAt (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2)
      ((ContinuousLinearEquiv.refl ℂ ComplexMatrix2 : ComplexMatrix2 ≃L[ℂ] ComplexMatrix2) :
        ComplexMatrix2 →L[ℂ] ComplexMatrix2) 0 :=
    hstrict.hasFDerivAt
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hs := hexp.hasStrictFDerivAt' hd hn
  let Ψ := hexp.localInverse hd hn
  have hΨ : ContDiffAt ℂ 1 Ψ (NormedSpace.exp (0 : ComplexMatrix2)) := hexp.to_localInverse hd hn
  have hΨ0 : Ψ (NormedSpace.exp (0 : ComplexMatrix2)) = 0 := hexp.localInverse_apply_image hd hn
  have hright : ∀ᶠ X in 𝓝 (NormedSpace.exp (0 : ComplexMatrix2)), NormedSpace.exp (Ψ X) = X :=
    hs.eventually_right_inverse
  have hsmall : ∀ᶠ X in 𝓝 (NormedSpace.exp (0 : ComplexMatrix2)),
      ComplexMatrix2.operatorNorm (Ψ X) < Real.log 2 := by
    have hc : ContinuousAt Ψ (NormedSpace.exp (0 : ComplexMatrix2)) := hΨ.continuousAt
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have := hc.tendsto.norm
    rw [hΨ0, norm_zero] at this
    exact this.eventually (gt_mem_nhds h2)
  have hlogexp := hEL.2.2.2.2.1
  have hEq : ComplexMatrix2.logSeries =ᶠ[𝓝 (NormedSpace.exp (0 : ComplexMatrix2))] Ψ := by
    filter_upwards [hright, hsmall] with X h1 h2
    have := (hlogexp (Ψ X) h2).2
    rw [show ComplexMatrix2.matExp (Ψ X) = X from h1] at this
    exact this
  have := hΨ.congr_of_eventuallyEq hEq
  rwa [NormedSpace.exp_zero] at this
section Forms
variable {L m : ℕ} {j j' : ℤ}
theorem extendForm_smul {Γ : Set (Bond L m j)} (t : ℂ) (B : SupportBond j' Γ → ComplexMatrix2) :
    extendForm (t • B) = t • extendForm B := by
  funext b
  simp only [extendForm, Pi.smul_apply]
  split_ifs <;> simp
theorem extendForm_zero {Γ : Set (Bond L m j)} :
    extendForm (0 : SupportBond j' Γ → ComplexMatrix2) = 0 := by
  funext b
  simp only [extendForm, Pi.zero_apply]
  split_ifs <;> simp
theorem extendForm_isBondForm
    (hx : ∀ b : Bond L m j', Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {Γ : Set (Bond L m j)} {B : SupportBond j' Γ → ComplexMatrix2}
    (hB : ∀ i, B i ∈ ComplexMatrix2.traceless) :
    IsBondForm complexLieAlgebra (extendForm B) := by
  have hnp : ∀ b : Bond L m j', b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented :=
    fun b hb hr => by
      rcases hx b with h | h
      · exact h.2 hr
      · exact h.2 hb
  have hpn : ∀ b : Bond L m j', ¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented :=
    fun b hb => by
      rcases hx b with h | h
      · exact absurd h.1 hb
      · exact h.1
  constructor
  · intro b hb
    unfold extendForm
    split_ifs with h h'
    · exact hB _
    · exact absurd h'.2 (hnp b hb)
    · exact ComplexMatrix2.traceless.zero_mem
  · intro b
    by_cases hb : b.IsPositivelyOriented
    · have h1 : ¬ (b.opposite ∈ doubleBlockSupport j' Γ ∧ b.opposite.IsPositivelyOriented) :=
        fun h => hnp b hb h.2
      by_cases hin : b ∈ doubleBlockSupport j' Γ
      · have h2 : b.opposite.opposite ∈ doubleBlockSupport j' Γ ∧
            b.opposite.opposite.IsPositivelyOriented := ⟨hin, hb⟩
        have h3 : b ∈ doubleBlockSupport j' Γ ∧ b.IsPositivelyOriented := ⟨hin, hb⟩
        simp only [extendForm, dif_neg h1, dif_pos h2, dif_pos h3]
        rfl
      · have h2 : ¬ (b.opposite.opposite ∈ doubleBlockSupport j' Γ ∧
            b.opposite.opposite.IsPositivelyOriented) := fun h => hin h.1
        have h3 : ¬ (b ∈ doubleBlockSupport j' Γ ∧ b.IsPositivelyOriented) := fun h => hin h.1
        simp only [extendForm, dif_neg h1, dif_neg h2, dif_neg h3, neg_zero]
    · have hr := hpn b hb
      have h3 : ¬ (b ∈ doubleBlockSupport j' Γ ∧ b.IsPositivelyOriented) := fun h => hb h.2
      by_cases hin : b.opposite ∈ doubleBlockSupport j' Γ
      · have h1 : b.opposite ∈ doubleBlockSupport j' Γ ∧ b.opposite.IsPositivelyOriented :=
          ⟨hin, hr⟩
        simp only [extendForm, dif_pos h1, dif_neg h3, neg_neg]
      · have h1 : ¬ (b.opposite ∈ doubleBlockSupport j' Γ ∧ b.opposite.IsPositivelyOriented) :=
          fun h => hin h.1
        have h2 : ¬ (b.opposite.opposite ∈ doubleBlockSupport j' Γ ∧
            b.opposite.opposite.IsPositivelyOriented) := fun h => hb h.2
        simp only [extendForm, dif_neg h1, dif_neg h2, dif_neg h3, neg_zero]
end Forms
section ConstraintMap
variable {L m K k : ℕ}
abbrev extendTraceless {Γ : Set (BondAtLevel L m K (k + 1))}
    (x : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless) :
    BondAtLevel L m K k → ComplexMatrix2 :=
  extendForm fun i => (x i : ComplexMatrix2)
theorem constraintMap_regular_near_zero
    (hSch : AveragingSchemeProperties)
    (hRead : ComplexAverageIsLocal)
    (hLog : LogSeriesInComplexGroupStatement)
    (hBlock : UnitBlockPathsAndLogarithm)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    (hx : ∀ b : BondAtLevel L m K k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {Γ : Set (BondAtLevel L m K (k + 1))} [Fintype (SupportBond (levelDepth K k) Γ)]
    (V : BondAtLevel L m K k → ComplexMatrix2) {c : BondAtLevel L m K (k + 1)} (hcΓ : c ∈ Γ)
    (hc : c.IsPositivelyOriented)
    (hV : V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2))) :
    ContDiffAt ℂ 1 (fun x : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless =>
        constraintMap V (extendTraceless x) c) 0 ∧
      (∀ᶠ x : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless in 𝓝 0,
        ConstraintMapDefined V (extendTraceless x) c ∧
          constraintMap V (extendTraceless x) c ∈ ComplexMatrix2.traceless) ∧
      constraintMap V
        (extendTraceless (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless)) c = 0 := by
  classical
  have hpn : ∀ b : BondAtLevel L m K k, ¬ b.IsPositivelyOriented →
      b.opposite.IsPositivelyOriented := fun b hb => by
    rcases hx b with h | h
    · exact absurd h.1 hb
    · exact h.1
  set ℬ : Set (BondAtLevel L m K k) := bondsInDoubleBlock c with hℬ
  obtain ⟨-, hdom, hmean, -⟩ := (hSch L hL m K k hm hk .centred).2.1 c hc
  obtain ⟨inst, hopen, -, hF⟩ := hdom.average_holomorphic.1
  have hclosed : ∀ b ∈ ℬ, b.opposite ∈ ℬ := fun b hb => ⟨hb.2, hb.1⟩
  have hsub : ∀ b ∈ ℬ, b ∈ doubleBlockSupport (levelDepth K k) Γ := fun b hb =>
    Set.mem_biUnion hcΓ hb
  rw [hmean.domain_eq] at hopen hF
  obtain ⟨O, hOopen, hDO⟩ := hopen
  set D : Set (PositiveBondOf ℬ → ComplexMatrix2) :=
    restrictToPositive ℬ ''
      (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) with hD
  let v : (SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless) →
      PositiveBondOf ℬ → ComplexMatrix2 := fun x p =>
    ComplexMatrix2.matExp (Complex.I • (x ⟨p.1, hsub _ p.2.1, p.2.2⟩ : ComplexMatrix2)) * V p.1
  have hv0 : v 0 = restrictToPositive ℬ V := by
    funext p
    simp [v, restrictToPositive]
  have hvc : ContDiff ℂ 1 v := by
    rw [contDiff_pi]
    intro p
    have h1 : ContDiff ℂ 1 fun x : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless =>
        Complex.I • (x ⟨p.1, hsub _ p.2.1, p.2.2⟩ : ComplexMatrix2) :=
      ContDiff.const_smul _ (ComplexMatrix2.traceless.subtypeL.comp (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : SupportBond (levelDepth K k) Γ => ↥ComplexMatrix2.traceless)
        (⟨p.1, hsub _ p.2.1, p.2.2⟩ : SupportBond (levelDepth K k) Γ))).contDiff
    have h2 : ContDiff ℂ 1 (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2) :=
      contDiff_iff_contDiffAt.mpr fun X => (NormedSpace.exp_analytic (𝕂 := ℂ) X).contDiffAt
    exact (h2.comp h1).mul contDiff_const
  have hVD : restrictToPositive ℬ V ∈ D := ⟨V, hV, rfl⟩
  obtain ⟨F, hFan, hFeq⟩ := hF _ hVD
  have hVconf : IsGaugeField complexGaugeGroup ℬ V := hV.1.1
  have hexpmem := hBlock.2.1.matExp_mem_complex
  have hvP : ∀ x, v x ∈ ComplexMatrix2.complexifiedProduct
      fun _ : PositiveBondOf ℬ => ComplexMatrix2.FactorKind.group := by
    intro x p
    have h1 : ComplexMatrix2.matExp (Complex.I • (x ⟨p.1, hsub _ p.2.1, p.2.2⟩ : ComplexMatrix2)) ∈
        complexGaugeGroup :=
      hexpmem _ (x ⟨p.1, hsub _ p.2.1, p.2.2⟩).2
    have h2 : V p.1 ∈ complexGaugeGroup := hVconf.1 _ p.2.1
    have h1' : (ComplexMatrix2.matExp
        (Complex.I • (x ⟨p.1, hsub _ p.2.1, p.2.2⟩ : ComplexMatrix2))).det = 1 := h1
    have h2' : (V p.1).det = 1 := h2
    change (ComplexMatrix2.matExp
      (Complex.I • (x ⟨p.1, hsub _ p.2.1, p.2.2⟩ : ComplexMatrix2)) * V p.1).det = 1
    rw [Matrix.det_mul, h1', h2', one_mul]
  have hv0O : v 0 ∈ O := by
    rw [hv0]
    have : restrictToPositive ℬ V ∈ O ∩ _ := hDO ▸ hVD
    exact this.1
  have hvO : ∀ᶠ x in 𝓝 (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless), v x ∈ O :=
    hvc.continuous.continuousAt.eventually (hOopen.mem_nhds hv0O)
  have hvD : ∀ᶠ x in 𝓝 (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless), v x ∈ D := by
    filter_upwards [hvO] with x hx'
    rw [hDO]
    exact ⟨hx', hvP x⟩
  have htend : Tendsto v (𝓝 0) (𝓝[D] (restrictToPositive ℬ V)) := by
    rw [tendsto_nhdsWithin_iff, ← hv0]
    exact ⟨hvc.continuous.continuousAt.tendsto, hvD⟩
  have hvF := htend.eventually hFeq
  have hkey : ∀ x, v x ∈ D →
      expTwist (extendTraceless x) V ∈
          (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
        complexBlockAverageOnPositive (expTwist (extendTraceless x) V) c =
          schemeBlockAverage .centred (extendFromPositive ℬ (v x)) c := by
    intro x hxD
    obtain ⟨W, hW, hWv⟩ := hxD
    have hWconf : IsGaugeField complexGaugeGroup ℬ W := hW.1.1
    have hWpos : ∀ p : PositiveBondOf ℬ, W p.1 = v x p := fun p => congrFun hWv p
    have hval : ∀ p : PositiveBondOf ℬ, extendTraceless x p.1 =
        (x ⟨p.1, hsub _ p.2.1, p.2.2⟩ : ComplexMatrix2) := by
      intro p
      have h : p.1 ∈ doubleBlockSupport (levelDepth K k) Γ ∧ p.1.IsPositivelyOriented :=
        ⟨hsub _ p.2.1, p.2.2⟩
      simp only [extendTraceless, extendForm, dif_pos h]
    have hU : ∀ b ∈ ℬ, W b = expTwist (extendTraceless x) V b := by
      intro b hb
      by_cases hp : b.IsPositivelyOriented
      · rw [hWpos ⟨b, hb, hp⟩]
        simp only [expTwist, if_pos hp]
        rw [hval ⟨b, hb, hp⟩]
      · have hr := hpn b hp
        have hrb := hclosed b hb
        have h1 : W b = (W b.opposite)⁻¹ := hWconf.2 _ hrb
        rw [h1, hWpos ⟨b.opposite, hrb, hr⟩]
        simp only [expTwist, if_neg hp]
        rw [hval ⟨b.opposite, hrb, hr⟩]
    have hC : ∀ b ∈ ℬ, W b = extendFromPositive ℬ (v x) b := by
      intro b hb
      by_cases hp : b.IsPositivelyOriented
      · have h : b ∈ ℬ ∧ b.IsPositivelyOriented := ⟨hb, hp⟩
        rw [hWpos ⟨b, hb, hp⟩]
        simp only [extendFromPositive, dif_pos h]
      · have hr := hpn b hp
        have hrb := hclosed b hb
        have h1 : W b = (W b.opposite)⁻¹ := hWconf.2 _ hrb
        have h2 : ¬ (b ∈ ℬ ∧ b.IsPositivelyOriented) := fun h => hp h.2
        have h3 : b.opposite ∈ ℬ ∧ b.opposite.IsPositivelyOriented := ⟨hrb, hr⟩
        rw [h1, hWpos ⟨b.opposite, hrb, hr⟩]
        simp only [extendFromPositive, dif_neg h2, dif_pos h3]
    have hrd := hRead L m K k hL.1 hL.2 hm hk c hc
    have hUin := (hrd.mem_domain_iff W _ hU).mp hW
    have hCin := (hrd.mem_domain_iff W _ hC).mp hW
    refine ⟨hUin, ?_⟩
    rw [← hrd.average_eq W _ hU, hrd.average_eq W _ hC,
      hmean.average_eq _ (by rw [hmean.domain_eq]; exact hCin)]
    simp only [complexBlockAverage, if_pos hc]
  have hrd := hRead L m K k hL.1 hL.2 hm hk c hc
  have hMgrp : complexBlockAverage V c ∈ complexGaugeGroup := (hLog.2 L hL m K k hm hk c hc).1 V hV
  have hMdet : (complexBlockAverage V c).det = 1 := hMgrp
  have hMinv : complexBlockAverage V c * (complexBlockAverage V c)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hMdet]; exact isUnit_one)
  have hFc : ContDiffAt ℂ 1 F (v 0) := by
    rw [hv0]
    exact hFan.contDiffAt
  have hFx : ContDiffAt ℂ 1 (fun x => F (v x) ())
      (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless) :=
    (contDiffAt_pi.mp (hFc.comp 0 hvc.contDiffAt)) ()
  have hev : ∀ᶠ x in 𝓝 (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless),
      expTwist (extendTraceless x) V ∈
          (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) ∧
        complexBlockAverage (expTwist (extendTraceless x) V) c = F (v x) () := by
    filter_upwards [hvD, hvF] with x h1 h2
    obtain ⟨a, b⟩ := hkey x h1
    refine ⟨a, ?_⟩
    simp only [complexBlockAverage, if_pos hc]
    exact b.trans (congrFun h2 ())
  have hform0 : extendTraceless (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless) = 0 := by
    have : (fun i => (((0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless) i :
        ↥ComplexMatrix2.traceless) : ComplexMatrix2)) = 0 := by
      funext i
      rfl
    simp only [extendTraceless, this, extendForm_zero]
  have hagree0 : ∀ b ∈ ℬ, V b = expTwist (0 : BondAtLevel L m K k → ComplexMatrix2) V b := by
    intro b hb
    by_cases hp : b.IsPositivelyOriented
    · simp [expTwist, if_pos hp]
    · have h1 : V b = (V b.opposite)⁻¹ := hVconf.2 _ (hclosed b hb)
      simp only [expTwist, if_neg hp]
      simp [h1]
  have h00 : F (v 0) () = complexBlockAverage V c := by
    have h1 := hev.self_of_nhds.2
    rw [hform0] at h1
    rw [← h1]
    simp only [complexBlockAverage, if_pos hc]
    exact (hrd.average_eq _ _ hagree0).symm
  have hRc : ContDiffAt ℂ 1 (fun x => F (v x) () * (complexBlockAverage V c)⁻¹)
      (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless) := hFx.mul contDiffAt_const
  have hR0 : F (v 0) () * (complexBlockAverage V c)⁻¹ = 1 := by rw [h00, hMinv]
  have hlog1 : ContDiffAt ℂ 1 ComplexMatrix2.logSeries
      (F (v 0) () * (complexBlockAverage V c)⁻¹) := by
    rw [hR0]
    exact contDiffAt_logSeries_one hEL
  have hlogc : ContDiffAt ℂ 1 (fun x => Complex.I⁻¹ •
      ComplexMatrix2.logSeries (F (v x) () * (complexBlockAverage V c)⁻¹))
      (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless) :=
    ContDiffAt.const_smul _ (ContDiffAt.comp (g := ComplexMatrix2.logSeries)
      (f := fun x => F (v x) () * (complexBlockAverage V c)⁻¹)
      (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless) hlog1 hRc)
  have hRnear : ∀ᶠ x in 𝓝 (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless),
      F (v x) () * (complexBlockAverage V c)⁻¹ ∈ ComplexMatrix2.logBall := by
    have h1 : Metric.ball (F (v 0) () * (complexBlockAverage V c)⁻¹) 1 ∈
        𝓝 (F (v 0) () * (complexBlockAverage V c)⁻¹) := Metric.ball_mem_nhds _ one_pos
    filter_upwards [hRc.continuousAt.eventually h1] with x hx'
    rw [hR0, dist_eq_norm] at hx'
    exact hx'
  refine ⟨hlogc.congr_of_eventuallyEq ?_, ?_, ?_⟩
  · filter_upwards [hev] with x hx'
    simp only [constraintMap, hx'.2]
  · filter_upwards [hev, hRnear] with x h1 h2
    have hX : complexBlockAverage (expTwist (extendTraceless x) V) c *
        (complexBlockAverage V c)⁻¹ ∈ ComplexMatrix2.logBall := by
      rw [h1.2]
      exact h2
    refine ⟨⟨h1.1, hX⟩, ?_⟩
    have hg1 : (complexBlockAverage (expTwist (extendTraceless x) V) c).det = 1 :=
      (hLog.2 L hL m K k hm hk c hc).1 _ h1.1
    have hgrp : complexBlockAverage (expTwist (extendTraceless x) V) c *
        (complexBlockAverage V c)⁻¹ ∈ complexGaugeGroup := by
      change (_ * _ : ComplexMatrix2).det = 1
      rw [Matrix.det_mul, hg1, Matrix.det_nonsing_inv, hMdet]
      simp
    exact (hBlock.2.1.logSeries_mem _ hgrp hX).1
  · have hlogone : ComplexMatrix2.logSeries (1 : ComplexMatrix2) = 0 := by
      simp [ComplexMatrix2.logSeries]
    simp only [constraintMap]
    rw [hev.self_of_nhds.2, hR0, hlogone, smul_zero]
end ConstraintMap
section Tuples
open Matrices.GroupLieProduct
variable {σ τ : Type}
def piTracelessProj (σ : Type) [Fintype σ] :
    (σ → ComplexMatrix2) →L[ℂ] (σ → ↥ComplexMatrix2.traceless) :=
  ContinuousLinearMap.pi fun i => tracelessProj.comp (ContinuousLinearMap.proj i)
def piTracelessIncl (σ : Type) [Fintype σ] :
    (σ → ↥ComplexMatrix2.traceless) →L[ℂ] (σ → ComplexMatrix2) :=
  ContinuousLinearMap.pi fun i => ComplexMatrix2.traceless.subtypeL.comp (ContinuousLinearMap.proj i)
theorem piTracelessIncl_apply [Fintype σ] (x : σ → ↥ComplexMatrix2.traceless) (i : σ) :
    piTracelessIncl σ x i = (x i : ComplexMatrix2) := rfl
theorem piTracelessIncl_mem [Fintype σ] (x : σ → ↥ComplexMatrix2.traceless) :
    piTracelessIncl σ x ∈ tracelessPi σ := fun i => (x i).2
theorem piTracelessIncl_proj [Fintype σ] {A : σ → ComplexMatrix2} (hA : A ∈ tracelessPi σ) :
    piTracelessIncl σ (piTracelessProj σ A) = A := by
  funext i
  exact tracelessProj_coe_of_mem (hA i)
def tupleOfCoordsLinear [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    ComplexCoordinates (Fintype.card σ * 3) →ₗ[ℂ] (σ → ComplexMatrix2) where
  toFun := tupleOfCoords b ν
  map_add' w w' := by
    funext i
    simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, add_smul, Finset.sum_add_distrib]
  map_smul' z w := by
    funext i
    simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, Finset.smul_sum, mul_smul]
theorem tupleOfCoords_mem [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (w : ComplexCoordinates (Fintype.card σ * 3)) :
    tupleOfCoords b ν w ∈ tracelessPi σ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.tupleOfCoords_mem <;> assumption
def coordsOfTuple [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    (σ → ↥ComplexMatrix2.traceless) →ₗ[ℂ] ComplexCoordinates (Fintype.card σ * 3) where
  toFun x k := b.repr (x (ν.symm (finProdFinEquiv.symm k).1)) (finProdFinEquiv.symm k).2
  map_add' x y := by
    funext k
    simp
  map_smul' z x := by
    funext k
    simp
theorem tupleOfCoords_coordsOfTuple [Fintype σ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (x : σ → ↥ComplexMatrix2.traceless) :
    tupleOfCoords b ν (coordsOfTuple b ν x) = piTracelessIncl σ x := by
  funext i
  have h := b.sum_repr (x i)
  have h2 : ∑ c, b.repr (x i) c • ((b c : ↥ComplexMatrix2.traceless) : ComplexMatrix2) = x i := by
    have h3 := congrArg ComplexMatrix2.traceless.subtype h
    rw [map_sum] at h3
    simpa only [map_smul, Submodule.subtype_apply] using h3
  simpa only [tupleOfCoords, ComplexCoordinates.tracelessTuple, coordsOfTuple, LinearMap.coe_mk,
    AddHom.coe_mk, Equiv.symm_apply_apply, piTracelessIncl_apply, Equiv.apply_symm_apply,
    Prod.fst, Prod.snd] using h2
def matrixPiLinearEquiv {k : ℕ} (ν : τ ≃ Fin k) :
    (τ → ComplexMatrix2) ≃ₗ[ℂ] ComplexCoordinates
      (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) where
  toEquiv := matrixPiEquiv ν
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem isHolomorphicOnTraceless_of_differentiableOn [Fintype σ] [Fintype τ]
    (hTop : ExpChartHolomorphy.TracelessTopologiesAgree σ)
    (d : (σ → ↥ComplexMatrix2.traceless) → τ → ↥ComplexMatrix2.traceless)
    {N : Set (σ → ↥ComplexMatrix2.traceless)} (hN : IsOpen N)
    (hd : DifferentiableOn ℂ d N) (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {k : ℕ}
    (ν : τ ≃ Fin k) :
    IsHolomorphicOnTraceless b (matrixPiEquiv ν)
      {A | A ∈ tracelessPi σ ∧ piTracelessProj σ A ∈ N}
      (fun A => piTracelessIncl τ (d (piTracelessProj σ A))) := by
  have hsub : {A | A ∈ tracelessPi σ ∧ piTracelessProj σ A ∈ N} ⊆ tracelessPi σ :=
    fun A hA => hA.1
  refine ⟨((hTop _ hsub).1).mpr ⟨piTracelessProj σ ⁻¹' N,
    hN.preimage (piTracelessProj σ).continuous, ?_⟩, ?_⟩
  · ext A
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  intro ν'
  let tc : ComplexCoordinates (Fintype.card σ * 3) →L[ℂ] (σ → ComplexMatrix2) :=
    LinearMap.toContinuousLinearMap (tupleOfCoordsLinear b ν')
  let mp : (τ → ComplexMatrix2) →L[ℂ] _ :=
    LinearMap.toContinuousLinearMap (matrixPiLinearEquiv ν).toLinearMap
  let lin : ComplexCoordinates (Fintype.card σ * 3) →L[ℂ] (σ → ↥ComplexMatrix2.traceless) :=
    (piTracelessProj σ).comp tc
  let out : (τ → ↥ComplexMatrix2.traceless) →L[ℂ] _ := mp.comp (piTracelessIncl τ)
  have hset : tupleOfCoords b ν' ⁻¹' {A | A ∈ tracelessPi σ ∧ piTracelessProj σ A ∈ N} =
      lin ⁻¹' N := by
    ext w
    exact ⟨fun h => h.2, fun h => ⟨tupleOfCoords_mem b ν' w, h⟩⟩
  have hS : IsOpen (lin ⁻¹' N) := hN.preimage lin.continuous
  have hf : DifferentiableOn ℂ (fun w => out (d (lin w))) (lin ⁻¹' N) :=
    out.differentiable.comp_differentiableOn
      (hd.comp lin.differentiable.differentiableOn fun _ h => h)
  rw [ComplexCoordinates.IsHolomorphicIn, hset]
  refine ⟨hS, hf.continuousOn, ?_⟩
  intro a ha j
  have hline : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • ComplexCoordinates.stdBasisVector j ∈ lin ⁻¹' N :=
    hline.continuousAt.eventually (hS.mem_nhds (by simpa using ha))
  filter_upwards [hev] with ζ hζ
  have h1 : DifferentiableAt ℂ (fun w => out (d (lin w)))
      (a + ζ • ComplexCoordinates.stdBasisVector j) :=
    (hf _ hζ).differentiableAt (hS.mem_nhds hζ)
  have h2 : DifferentiableAt ℂ (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  have h3 := DifferentiableAt.comp (g := fun w => out (d (lin w))) ζ h1 h2
  exact h3
theorem tendsto_zero_of_isHolomorphicOnTraceless [Fintype σ] [Fintype τ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {k : ℕ} {ν : τ ≃ Fin k}
    {N : Set (σ → ComplexMatrix2)} {D : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (hD : IsHolomorphicOnTraceless b (matrixPiEquiv ν) N D)
    (h0 : (0 : σ → ComplexMatrix2) ∈ N) (hD0 : D 0 = 0) :
    Tendsto (fun x : σ → ↥ComplexMatrix2.traceless => piTracelessProj τ (D (piTracelessIncl σ x)))
      (𝓝 0) (𝓝 0) := by
  let ν' := Fintype.equivFin σ
  obtain ⟨hopen, hcont, -⟩ := hD.2 ν'
  have hz : tupleOfCoords b ν' 0 = 0 := (tupleOfCoordsLinear b ν').map_zero
  have h0S : (0 : ComplexCoordinates (Fintype.card σ * 3)) ∈ tupleOfCoords b ν' ⁻¹' N := by
    change tupleOfCoords b ν' 0 ∈ N
    rw [hz]
    exact h0
  have hc0 := hcont.continuousAt (hopen.mem_nhds h0S)
  let ρ : (σ → ↥ComplexMatrix2.traceless) →L[ℂ] ComplexCoordinates (Fintype.card σ * 3) :=
    LinearMap.toContinuousLinearMap (coordsOfTuple b ν')
  let mpe := (matrixPiLinearEquiv ν).toContinuousLinearEquiv
  have hρ0 : ContinuousAt ρ 0 := ρ.continuous.continuousAt
  have hρz : ρ 0 = 0 := map_zero ρ
  have hcomp : ContinuousAt (fun x : σ → ↥ComplexMatrix2.traceless =>
      matrixPiEquiv ν (D (tupleOfCoords b ν' (ρ x)))) 0 := by
    have h1 : ContinuousAt (matrixPiEquiv ν ∘ D ∘ tupleOfCoords b ν') (ρ 0) := by
      rw [hρz]
      exact hc0
    exact ContinuousAt.comp (f := ρ) h1 hρ0
  have hfin : ContinuousAt (fun x : σ → ↥ComplexMatrix2.traceless =>
      piTracelessProj τ (mpe.symm (matrixPiEquiv ν
        (D (tupleOfCoords b ν' (ρ x)))))) 0 :=
    (piTracelessProj τ).continuous.continuousAt.comp
      (mpe.symm.continuous.continuousAt.comp hcomp)
  have heq : (fun x : σ → ↥ComplexMatrix2.traceless =>
      piTracelessProj τ (D (piTracelessIncl σ x))) =
      fun x => piTracelessProj τ (mpe.symm (matrixPiEquiv ν
        (D (tupleOfCoords b ν' (ρ x))))) := by
    funext x
    have h1 : mpe.symm (matrixPiEquiv ν (D (tupleOfCoords b ν' (ρ x)))) =
        D (tupleOfCoords b ν' (ρ x)) := mpe.symm_apply_apply _
    rw [h1]
    have h2 : tupleOfCoords b ν' (ρ x) = piTracelessIncl σ x :=
      tupleOfCoords_coordsOfTuple b ν' x
    rw [h2]
  rw [heq]
  have := hfin.tendsto
  have hval : piTracelessProj τ (mpe.symm (matrixPiEquiv ν
      (D (tupleOfCoords b ν' (ρ 0))))) = 0 := by
    have h1 : mpe.symm (matrixPiEquiv ν (D (tupleOfCoords b ν' (ρ 0)))) =
        D (tupleOfCoords b ν' (ρ 0)) := mpe.symm_apply_apply _
    rw [h1, hρz, hz, hD0, map_zero]
  rwa [hval] at this
end Tuples
section Pivots
variable {L m : ℕ} {j j' : ℤ}
theorem singleBondForm_isBondForm
    (hx : ∀ b : Bond L m j', Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (b : Bond L m j') {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    IsBondForm complexLieAlgebra (singleBondForm b X) := by
  classical
  have hne : b.opposite ≠ b := by
    intro h
    rcases hx b with h1 | h1
    · exact h1.2 (h ▸ h1.1)
    · exact h1.2 (h ▸ h1.1)
  have hrev : ∀ a a' : Bond L m j', a.opposite = a'.opposite → a = a' := fun a a' h =>
    congrArg Bond.opposite h
  constructor
  · intro b' _
    unfold singleBondForm
    split_ifs
    · exact hX
    · exact ComplexMatrix2.traceless.neg_mem hX
    · exact ComplexMatrix2.traceless.zero_mem
  · intro b'
    by_cases h1 : b' = b
    · subst h1
      simp [singleBondForm, hne]
    · by_cases h2 : b' = b.opposite
      · subst h2
        have h3 : b.opposite.opposite = b := rfl
        simp [singleBondForm, hne, h3]
      · have h3 : b'.opposite ≠ b := fun h => h2 (hrev b' b.opposite h)
        have h4 : b'.opposite ≠ b.opposite := fun h => h1 (hrev _ _ h)
        simp [singleBondForm, h1, h2, h3, h4]
theorem isBondForm_add {A A' : Bond L m j' → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A) (hA' : IsBondForm complexLieAlgebra A') :
    IsBondForm complexLieAlgebra (A + A') := by
  refine ⟨fun b hb => ComplexMatrix2.traceless.add_mem (hA.1 b hb) (hA'.1 b hb), fun b => ?_⟩
  simp only [Pi.add_apply, hA.2 b, hA'.2 b, neg_add]
theorem isBondForm_zero : IsBondForm complexLieAlgebra (0 : Bond L m j' → ComplexMatrix2) :=
  ⟨fun _ _ => ComplexMatrix2.traceless.zero_mem, fun _ => by simp⟩
theorem extendForm_eq_sum_singleBondForm
    (hx : ∀ b : Bond L m j', Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {Γ : Set (Bond L m j)} [Fintype ↥Γ] (pv : ↥Γ → Bond L m j')
    (hpp : ∀ c, (pv c).IsPositivelyOriented)
    (hpm : ∀ c, pv c ∈ doubleBlockSupport j' Γ) (hinj : Function.Injective pv)
    (B : SupportBond j' Γ → ComplexMatrix2) (X : ↥Γ → ComplexMatrix2)
    (hB : ∀ c, B ⟨pv c, hpm c, hpp c⟩ = X c)
    (hB0 : ∀ i : SupportBond j' Γ, (∀ c, i.1 ≠ pv c) → B i = 0) :
    extendForm B = ∑ c, singleBondForm (pv c) (X c) := by
  classical
  have hnp : ∀ b : Bond L m j', b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented :=
    fun b hb hr => by
      rcases hx b with h | h
      · exact h.2 hr
      · exact h.2 hb
  have hrev : ∀ a a' : Bond L m j', a.opposite = a'.opposite → a = a' := fun a a' h =>
    congrArg Bond.opposite h
  funext b
  rw [Finset.sum_apply]
  by_cases h1 : ∃ c, b = pv c
  · obtain ⟨c, rfl⟩ := h1
    rw [Finset.sum_eq_single c]
    · have h : pv c ∈ doubleBlockSupport j' Γ ∧ (pv c).IsPositivelyOriented := ⟨hpm c, hpp c⟩
      simp only [extendForm, dif_pos h, singleBondForm, if_true, hB c]
    · intro c' _ hne
      have h2 : pv c ≠ pv c' := fun h => hne (hinj h).symm
      have h3 : pv c ≠ (pv c').opposite := fun h => hnp _ (hpp c') (h ▸ hpp c)
      simp only [singleBondForm, if_neg h2, if_neg h3]
    · simp
  · by_cases h2 : ∃ c, b = (pv c).opposite
    · obtain ⟨c, rfl⟩ := h2
      rw [Finset.sum_eq_single c]
      · have h3 : ¬ ((pv c).opposite ∈ doubleBlockSupport j' Γ ∧
            (pv c).opposite.IsPositivelyOriented) :=
          fun h => hnp _ (hpp c) h.2
        have h4 : (pv c).opposite.opposite ∈ doubleBlockSupport j' Γ ∧
            (pv c).opposite.opposite.IsPositivelyOriented := ⟨hpm c, hpp c⟩
        have h5 : (pv c).opposite ≠ pv c := fun h => hnp _ (hpp c) (h.symm ▸ hpp c)
        simp only [extendForm, dif_neg h3, dif_pos h4, singleBondForm, if_neg h5, if_true]
        rw [← hB c]
        rfl
      · intro c' _ hne
        have h3 : (pv c).opposite ≠ pv c' := fun h => hnp _ (hpp c) (h.symm ▸ hpp c')
        have h4 : (pv c).opposite ≠ (pv c').opposite := fun h => hne (hinj (hrev _ _ h)).symm
        simp only [singleBondForm, if_neg h3, if_neg h4]
      · simp
    · have hz : ∀ c, singleBondForm (pv c) (X c) b = 0 := by
        intro c
        have h3 : b ≠ pv c := fun h => h1 ⟨c, h⟩
        have h4 : b ≠ (pv c).opposite := fun h => h2 ⟨c, h⟩
        simp only [singleBondForm, if_neg h3, if_neg h4]
      rw [Finset.sum_eq_zero fun c _ => hz c]
      unfold extendForm
      split_ifs with h3 h4
      · exact hB0 _ fun c h => h1 ⟨c, h⟩
      · have : B ⟨b.opposite, h4⟩ = 0 := hB0 _ fun c h => h2 ⟨c, congrArg Bond.opposite h⟩
        rw [this, neg_zero]
      · rfl
end Pivots
section Main
theorem pivotCoeffInv_eq_symm {L m : ℕ} {j j' : ℤ} {V : Bond L m j' → ComplexMatrix2}
    {c : Bond L m j} {T : ↥ComplexMatrix2.traceless ≃ₗ[ℂ] ↥ComplexMatrix2.traceless}
    (hT : ∀ X : ↥ComplexMatrix2.traceless, (T X : ComplexMatrix2) = pivotCoeff V c X)
    (X : ↥ComplexMatrix2.traceless) : pivotCoeffInv V c X = (T.symm X : ComplexMatrix2) := by
  have hb : (X : ComplexMatrix2) ∈ pivotCoeff V c '' (ComplexMatrix2.traceless : Set ComplexMatrix2) :=
    ⟨T.symm X, (T.symm X).2, by rw [← hT]; simp⟩
  have h1 : pivotCoeffInv V c X ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2) :=
    Function.invFunOn_mem hb
  have h2 : pivotCoeff V c (pivotCoeffInv V c X) = X := Function.invFunOn_eq hb
  have h3 : T ⟨pivotCoeffInv V c X, h1⟩ = X := Subtype.ext (by rw [hT]; exact h2)
  have h4 : (⟨pivotCoeffInv V c X, h1⟩ : ↥ComplexMatrix2.traceless) = T.symm X := by
    apply T.injective
    rw [h3]
    simp
  exact congrArg Subtype.val h4
def tracelessEntryEquiv : ↥ComplexMatrix2.traceless ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun X := ![(X : ComplexMatrix2) 0 0, (X : ComplexMatrix2) 0 1, (X : ComplexMatrix2) 1 0]
  invFun z := ⟨!![z 0, z 1; z 2, -z 0], by
    change ComplexMatrix2.fullTrace _ = 0
    simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]⟩
  map_add' X Y := by
    ext i
    fin_cases i <;> simp
  map_smul' c X := by
    ext i
    fin_cases i <;> simp
  left_inv X := by
    apply Subtype.ext
    have hX : (X : ComplexMatrix2) 0 0 + (X : ComplexMatrix2) 1 1 = 0 := by
      have h : ComplexMatrix2.fullTrace (X : ComplexMatrix2) = 0 := X.2
      simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using h
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    linear_combination -hX
  right_inv z := by
    ext i
    fin_cases i <;> simp
theorem exists_traceless_ne_zero : ∃ X : ↥ComplexMatrix2.traceless, (X : ComplexMatrix2) ≠ 0 := by
  refine ⟨⟨!![1, 0; 0, -1], ?_⟩, ?_⟩
  · change ComplexMatrix2.fullTrace _ = 0
    simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this
theorem linearizingCorrection_exists_unique
    (hQ : LinearizedConstraintAtBond.Statement)
    (hElim : UniqueEliminationClaim)
    (hSch : AveragingSchemeProperties)
    (hRead : ComplexAverageIsLocal)
    (hLog : LogSeriesInComplexGroupStatement)
    (hBlock : UnitBlockPathsAndLogarithm)
    (hPivot : PivotOfEveryBond)
    (hFin : BondEndpointsAndFiniteness)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hCh : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) :
    LinearizingCorrectionExistsAndIsLocallyUnique := by
  intro L m K k hL hm hk V Γ hpos hform hinv
  classical
  have hKpos : 0 < K := by omega
  have hfinB : Finite (BondAtLevel L m K k) :=
    ((hFin ⟨L, hL, ⟨K, hKpos⟩, ⟨m, hm⟩⟩).1 (levelDepth K k) (by
      change -((m : ℕ) : ℤ) ≤ (K : ℤ) - (k : ℤ)
      omega)).2.2.2
  have hfinC : Finite (BondAtLevel L m K (k + 1)) :=
    ((hFin ⟨L, hL, ⟨K, hKpos⟩, ⟨m, hm⟩⟩).1 (levelDepth K (k + 1)) (by
      change -((m : ℕ) : ℤ) ≤ (K : ℤ) - ((k + 1 : ℕ) : ℤ)
      push_cast
      omega)).2.2.2
  obtain ⟨instF⟩ := nonempty_fintype (SupportBond (levelDepth K k) Γ)
  obtain ⟨instΓ⟩ := nonempty_fintype ↥Γ
  have hx : ∀ b : BondAtLevel L m K k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    (hBlock.1 L hL m K k hm hk 0).xor_oriented
  choose Tc hTc using fun c : ↥Γ => hinv c.1 c.2
  have hQc : ∀ c : ↥Γ, LinearizedConstraintProperties V c.1 := fun c =>
    hQ L m K k hL hm hk V c.1 (hpos _ c.2) (hform _ c.2)
  have helim := (hElim L m K k hL hm hk V Γ hpos hform hinv).1
  have near := fun c : ↥Γ => constraintMap_regular_near_zero hSch hRead hLog hBlock hEL hL hm hk hx
    (Γ := Γ) V c.2 (hpos _ c.2) (hform _ c.2)
  let g : (SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless) →
      ↥Γ → ↥ComplexMatrix2.traceless := fun x c =>
    tracelessProj (constraintMap V (extendTraceless x) c.1)
  have hgc : ContDiffAt ℂ 1 g 0 := contDiffAt_pi.mpr fun c =>
    ContDiffAt.comp (g := tracelessProj) 0 tracelessProj.contDiff.contDiffAt (near c).1
  have hg0 : g 0 = 0 := by
    funext c
    simp only [g, (near c).2.2, map_zero]
    rfl
  have hLne : (L : ℂ) ≠ 0 := by
    have : L ≠ 0 := by have := hL.2; omega
    exact_mod_cast this
  have hformSmul : ∀ (t : ℂ) (x : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless),
      extendTraceless (t • x) = t • extendTraceless x := by
    intro t x
    have : (fun i => (((t • x) i : ↥ComplexMatrix2.traceless) : ComplexMatrix2)) =
        t • fun i => (x i : ComplexMatrix2) := by
      funext i
      rfl
    simp only [extendTraceless, this, extendForm_smul]
  have hOne : ∀ x : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless,
      IsBondForm complexLieAlgebra (extendTraceless x) := fun x =>
    extendForm_isBondForm hx fun i => (x i).2
  have hT : ∀ (x : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless) (c : ↥Γ),
      ((fderiv ℂ g 0 x c : ↥ComplexMatrix2.traceless) : ComplexMatrix2) =
        (L : ℂ) • linearizedConstraint V (extendTraceless x) c.1 := by
    intro x c
    have h1 := (hQc c).hasDerivAt_constraintMap _ (hOne x)
    have h2 : HasDerivAt (fun t : ℂ => g (t • x) c)
        (tracelessProj ((L : ℂ) • linearizedConstraint V (extendTraceless x) c.1)) 0 := by
      have h3 := tracelessProj.hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
      have h4 : (fun t : ℂ => g (t • x) c) =
          (tracelessProj ∘ fun t : ℂ => constraintMap V (t • extendTraceless x) c.1) := by
        funext t
        simp only [g, Function.comp, hformSmul]
      rw [h4]
      exact h3
    have hgd : HasFDerivAt g (fderiv ℂ g 0) ((0 : ℂ) • x) := by
      rw [zero_smul]
      exact (hgc.differentiableAt (by norm_num)).hasFDerivAt
    have hline : HasDerivAt (fun t : ℂ => t • x) x 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const x
    have h5 := hgd.comp_hasDerivAt (0 : ℂ) hline
    have h6 := (hasDerivAt_pi.mp h5) c
    have h7 := h6.unique h2
    rw [h7]
    exact tracelessProj_coe_of_mem
      (ComplexMatrix2.traceless.smul_mem _ ((hQc c).mem_complexLieAlgebra _ (hOne x)))
  have hQ0 : ∀ c : ↥Γ, linearizedConstraint V 0 c.1 = 0 := by
    intro c
    have h1 := (hQc c).map_smul 0 0 isBondForm_zero
    simpa using h1
  have hcoef : ∀ c : ↥Γ, ∃ X : ↥ComplexMatrix2.traceless, pivotCoeff V c.1 X ≠ 0 := by
    intro c
    obtain ⟨X₀, hX₀⟩ := exists_traceless_ne_zero
    refine ⟨(Tc c).symm X₀, ?_⟩
    rw [← hTc c]
    simpa using hX₀
  let pv : ↥Γ → BondAtLevel L m K k := fun c => pivot c.1
  have hpp : ∀ c : ↥Γ, (pv c).IsPositivelyOriented := fun c =>
    (hPivot ⟨L, hL, ⟨K, hKpos⟩, ⟨m, hm⟩⟩ k hk c.1).isPositivelyOriented_iff.mpr (hpos _ c.2)
  have hpm0 : ∀ c : ↥Γ, pv c ∈ (bondsInDoubleBlock c.1 : Set (BondAtLevel L m K k)) := by
    intro c
    by_contra hnot
    obtain ⟨X, hX⟩ := hcoef c
    apply hX
    have hread := (hQc c).eq_of_eqOn_doubleBlock (singleBondForm (pv c) (X : ComplexMatrix2)) 0
      (singleBondForm_isBondForm hx _ X.2) isBondForm_zero (by
        intro b hb
        have h1 : b ≠ pv c := fun h => hnot (h ▸ hb)
        have h2 : b ≠ (pv c).opposite := fun h => hnot (by
          have h3 : b.opposite ∈ (bondsInDoubleBlock c.1 : Set (BondAtLevel L m K k)) :=
            ⟨hb.2, hb.1⟩
          rw [h] at h3
          exact h3)
        simp [singleBondForm, h1, h2])
    rw [hQ0 c] at hread
    exact hread
  have hpm : ∀ c : ↥Γ, pv c ∈ doubleBlockSupport (levelDepth K k) Γ := fun c =>
    Set.mem_biUnion c.2 (hpm0 c)
  have hinj : Function.Injective pv := by
    intro c c' hcc
    by_contra hne
    obtain ⟨X, hX⟩ := hcoef c
    apply hX
    have h1 := helim c.1 c.2 c'.1 c'.2 (fun h => hne (Subtype.ext h).symm) X X.2
    have h2 : pv c' = pv c := hcc.symm
    have h3 : pivotCoeff V c.1 X =
        linearizedConstraint V (singleBondForm (pv c) (X : ComplexMatrix2)) c.1 := rfl
    rw [h3, ← h2]
    exact h1
  let Xv : (↥Γ → ↥ComplexMatrix2.traceless) → ↥Γ → ↥ComplexMatrix2.traceless := fun y c =>
    ((L : ℂ)⁻¹) • (Tc c).symm (y c)
  let P₀ : (↥Γ → ↥ComplexMatrix2.traceless) →
      SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless := fun y b =>
    if h : ∃ c : ↥Γ, (b : BondAtLevel L m K k) = pivot (c : BondAtLevel L m K (k + 1)) then
      Xv y h.choose else 0
  let Plin : (↥Γ → ↥ComplexMatrix2.traceless) →ₗ[ℂ]
      SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless :=
    { toFun := P₀
      map_add' := by
        intro y y'
        funext b
        by_cases h : ∃ c : ↥Γ, (b : BondAtLevel L m K k) = pivot (c : BondAtLevel L m K (k + 1))
        · have e : ∀ y, P₀ y b = Xv y h.choose := fun y => dif_pos h
          rw [Pi.add_apply, e, e, e]
          simp only [Xv, Pi.add_apply, map_add, smul_add]
        · have e : ∀ y, P₀ y b = 0 := fun y => dif_neg h
          rw [Pi.add_apply, e, e, e, add_zero]
      map_smul' := by
        intro z y
        funext b
        by_cases h : ∃ c : ↥Γ, (b : BondAtLevel L m K k) = pivot (c : BondAtLevel L m K (k + 1))
        · have e : ∀ y, P₀ y b = Xv y h.choose := fun y => dif_pos h
          rw [RingHom.id_apply, Pi.smul_apply, e, e]
          simp only [Xv, Pi.smul_apply, map_smul]
          exact smul_comm _ _ _
        · have e : ∀ y, P₀ y b = 0 := fun y => dif_neg h
          rw [RingHom.id_apply, Pi.smul_apply, e, e, smul_zero] }
  let P : (↥Γ → ↥ComplexMatrix2.traceless) →L[ℂ]
      SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless :=
    LinearMap.toContinuousLinearMap Plin
  have hPapply : ∀ y, P y = P₀ y := fun y => rfl
  have hPcoe : ∀ y i, ((P y i : ↥ComplexMatrix2.traceless) : ComplexMatrix2) =
      pivotCorrectionLift V Γ (fun c => (y c : ComplexMatrix2)) i := by
    intro y i
    rw [hPapply]
    by_cases h : ∃ c : ↥Γ, (i : BondAtLevel L m K k) = pivot (c : BondAtLevel L m K (k + 1))
    · simp only [P₀, pivotCorrectionLift, dif_pos h, Xv]
      rw [pivotCoeffInv_eq_symm (hTc h.choose) (y h.choose)]
      rfl
    · simp only [P₀, pivotCorrectionLift, dif_neg h]
      rfl
  have hPval : ∀ y c, P y ⟨pv c, hpm c, hpp c⟩ = Xv y c := by
    intro y c
    rw [hPapply]
    have h : ∃ c' : ↥Γ, ((⟨pv c, hpm c, hpp c⟩ : SupportBond (levelDepth K k) Γ) :
        BondAtLevel L m K k) = pivot (c' : BondAtLevel L m K (k + 1)) := ⟨c, rfl⟩
    have h2 : h.choose = c := hinj h.choose_spec.symm
    simp only [P₀, dif_pos h, h2]
  have hP0 : ∀ y (i : SupportBond (levelDepth K k) Γ), (∀ c, i.1 ≠ pv c) → P y i = 0 := by
    intro y i hi
    rw [hPapply]
    have h : ¬ ∃ c : ↥Γ, (i : BondAtLevel L m K k) = pivot (c : BondAtLevel L m K (k + 1)) :=
      fun ⟨c, hc⟩ => hi c hc
    simp only [P₀, dif_neg h]
  have hQsum : ∀ (c : ↥Γ) (Y : ↥Γ → ↥ComplexMatrix2.traceless) (S : Finset ↥Γ),
      IsBondForm complexLieAlgebra (∑ c' ∈ S, singleBondForm (pv c') (Y c' : ComplexMatrix2)) ∧
        linearizedConstraint V (∑ c' ∈ S, singleBondForm (pv c') (Y c' : ComplexMatrix2)) c.1 =
          if c ∈ S then pivotCoeff V c.1 (Y c) else 0 := by
    intro c Y S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨by simpa using isBondForm_zero, ?_⟩
      simpa using hQ0 c
    | insert a S ha ih =>
      have hA := singleBondForm_isBondForm hx (pv a) (Y a).2
      rw [Finset.sum_insert ha]
      refine ⟨isBondForm_add hA ih.1, ?_⟩
      rw [(hQc c).map_add _ _ hA ih.1, ih.2]
      by_cases hac : a = c
      · subst hac
        simp only [Finset.mem_insert, true_or, if_true, if_neg ha, add_zero]
        rfl
      · have h1 : linearizedConstraint V (singleBondForm (pv a) (Y a : ComplexMatrix2)) c.1 = 0 :=
          helim c.1 c.2 a.1 a.2 (fun h => hac (Subtype.ext h)) _ (Y a).2
        have h2 : (c ∈ insert a S) ↔ c ∈ S := by
          simp [Finset.mem_insert, Ne.symm hac]
        simp only [h1, zero_add, h2]
  have hTP : ∀ y, fderiv ℂ g 0 (P y) = y := by
    intro y
    funext c
    apply Subtype.ext
    rw [hT]
    have hsum : extendTraceless (P y) = ∑ c', singleBondForm (pv c') (Xv y c' : ComplexMatrix2) :=
      extendForm_eq_sum_singleBondForm hx pv hpp hpm hinj _ _
        (fun c' => by rw [hPval]) (fun i hi => by rw [hP0 y i hi]; rfl)
    rw [hsum, (hQsum c (Xv y) Finset.univ).2, if_pos (Finset.mem_univ c), ← hTc c]
    simp only [Xv, map_smul, LinearEquiv.apply_symm_apply, Submodule.coe_smul, smul_smul,
      mul_inv_cancel₀ hLne, one_smul]
  have hS : {x : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless | ∀ c : ↥Γ,
      ConstraintMapDefined V (extendTraceless x) c.1 ∧
        constraintMap V (extendTraceless x) c.1 ∈ ComplexMatrix2.traceless} ∈ 𝓝 0 :=
    eventually_all.mpr fun c => (near c).2.1
  obtain ⟨hex, huniq⟩ := implicit_solution_of_rightInverse g hgc hg0 P hTP _ hS
  have hBridge : ∀ (x : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless)
      (dd : ↥Γ → ↥ComplexMatrix2.traceless),
      piTracelessIncl _ x - pivotCorrectionLift V Γ (piTracelessIncl _ dd) =
        piTracelessIncl _ (x - P dd) := by
    intro x dd
    funext i
    change (x i : ComplexMatrix2) - pivotCorrectionLift V Γ (fun c => (dd c : ComplexMatrix2)) i =
      ((x i - P dd i : ↥ComplexMatrix2.traceless) : ComplexMatrix2)
    rw [← hPcoe]
    rfl
  have hTopF := (hCh.2.1 (SupportBond (levelDepth K k) Γ)).1
  refine ⟨?_, ?_⟩
  · obtain ⟨d, N', hN'o, h0N', hd0, hdd, hdN⟩ := hex
    refine ⟨{A | A ∈ Matrices.GroupLieProduct.tracelessPi _ ∧ piTracelessProj _ A ∈ N'},
      fun A => piTracelessIncl ↥Γ (d (piTracelessProj _ A)), ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun _ => ComplexMatrix2.traceless.zero_mem, ?_⟩
      rw [map_zero]
      exact h0N'
    · exact ⟨instF, instΓ, fun b ν =>
        isHolomorphicOnTraceless_of_differentiableOn hTopF d hN'o hdd b ν⟩
    · exact fun B _ => piTracelessIncl_mem _
    · change piTracelessIncl ↥Γ (d (piTracelessProj _ 0)) = 0
      rw [map_zero, hd0, map_zero]
    · intro B hB c
      obtain ⟨x, hxdef⟩ : ∃ x, x = piTracelessProj _ B := ⟨_, rfl⟩
      have hBx : piTracelessIncl _ x = B := by
        rw [hxdef]
        exact piTracelessIncl_proj hB.1
      have hxN : x ∈ N' := by
        rw [hxdef]
        exact hB.2
      obtain ⟨hinS, hgeq⟩ := hdN x hxN
      have harg := hBridge x (d x)
      rw [hBx] at harg
      simp only [← hxdef]
      have hfo : extendForm (B - pivotCorrectionLift V Γ (piTracelessIncl ↥Γ (d x))) =
          extendTraceless (x - P (d x)) := by
        rw [harg]
        rfl
      rw [hfo]
      refine ⟨(hinS c).1, ?_⟩
      have h1 : ((g (x - P (d x)) c : ↥ComplexMatrix2.traceless) : ComplexMatrix2) =
          constraintMap V (extendTraceless (x - P (d x))) c.1 := tracelessProj_coe_of_mem (hinS c).2
      rw [← h1, hgeq, hT x c, ← hBx]
      rfl
  · intro N₁ D₁ N₂ D₂ h₁ h₂
    have key : ∀ N D, IsLinearizingCorrection V Γ N D →
        Tendsto (fun x => piTracelessProj ↥Γ (D (piTracelessIncl _ x))) (𝓝 0) (𝓝 0) ∧
        (∀ᶠ x in 𝓝 (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless),
          g (x - P (piTracelessProj ↥Γ (D (piTracelessIncl _ x)))) = fderiv ℂ g 0 x) ∧
        ∀ᶠ B in 𝓝[(supportForms (levelDepth K k) Γ :
            Set (SupportBond (levelDepth K k) Γ → ComplexMatrix2))] 0,
          B ∈ N ∧ D B ∈ Matrices.GroupLieProduct.tracelessPi ↥Γ := by
      rintro N D ⟨h0, ⟨i1, i2, hol⟩, halg, hD0, heq⟩
      obtain rfl : i1 = instF := Subsingleton.elim _ _
      obtain rfl : i2 = instΓ := Subsingleton.elim _ _
      have hh := hol (Module.Basis.ofEquivFun tracelessEntryEquiv) (Fintype.equivFin _)
      obtain ⟨O, hOo, hNO⟩ := ((hTopF N hh.1.1).1).mp hh.1
      have h0O : (0 : SupportBond (levelDepth K k) Γ → ComplexMatrix2) ∈ O := by
        rw [hNO] at h0
        exact h0.1
      have hinN : ∀ A ∈ Matrices.GroupLieProduct.tracelessPi (SupportBond (levelDepth K k) Γ),
          A ∈ O → A ∈ N := by
        intro A hA h
        rw [hNO]
        exact ⟨h, hA⟩
      have hnearO : ∀ᶠ x in 𝓝 (0 : SupportBond (levelDepth K k) Γ → ↥ComplexMatrix2.traceless),
          piTracelessIncl _ x ∈ O :=
        (piTracelessIncl _).continuous.continuousAt.eventually
          (hOo.mem_nhds (by rwa [map_zero]))
      refine ⟨tendsto_zero_of_isHolomorphicOnTraceless hh h0 hD0, ?_, ?_⟩
      · filter_upwards [hnearO] with x hxO
        have hB := hinN _ (piTracelessIncl_mem x) hxO
        obtain ⟨dd, hdd⟩ : ∃ dd, dd = piTracelessProj ↥Γ (D (piTracelessIncl _ x)) := ⟨_, rfl⟩
        have hDB : piTracelessIncl _ dd = D (piTracelessIncl _ x) := by
          rw [hdd]
          exact piTracelessIncl_proj (halg _ hB)
        rw [← hdd]
        funext c
        have he := (heq _ hB c).2
        have harg := hBridge x dd
        rw [hDB] at harg
        rw [harg] at he
        apply Subtype.ext
        rw [hT x c]
        have h1 : g (x - P dd) c = tracelessProj
            ((L : ℂ) • linearizedConstraint V (extendTraceless x) c.1) := by
          change tracelessProj (constraintMap V (extendTraceless (x - P dd)) c.1) = _
          exact congrArg tracelessProj he
        rw [h1]
        exact tracelessProj_coe_of_mem
          (ComplexMatrix2.traceless.smul_mem _ ((hQc c).mem_complexLieAlgebra _ (hOne x)))
      · have hO : ∀ᶠ B in 𝓝[(supportForms (levelDepth K k) Γ :
            Set (SupportBond (levelDepth K k) Γ → ComplexMatrix2))] 0, B ∈ O :=
          nhdsWithin_le_nhds (hOo.mem_nhds h0O)
        filter_upwards [hO, self_mem_nhdsWithin] with B h1 h2
        have hBa : B ∈ Matrices.GroupLieProduct.tracelessPi (SupportBond (levelDepth K k) Γ) :=
          fun i => (Submodule.mem_pi.mp h2) i (Set.mem_univ i)
        exact ⟨hinN B hBa h1, halg _ (hinN B hBa h1)⟩
    obtain ⟨t₁, e₁, f₁⟩ := key _ _ h₁
    obtain ⟨t₂, e₂, f₂⟩ := key _ _ h₂
    have hev := huniq _ _ t₁ t₂ e₁ e₂
    have htend : Tendsto (piTracelessProj (SupportBond (levelDepth K k) Γ))
        (𝓝[(supportForms (levelDepth K k) Γ :
          Set (SupportBond (levelDepth K k) Γ → ComplexMatrix2))] 0) (𝓝 0) :=
      ((piTracelessProj _).continuous.tendsto' 0 0 (map_zero _)).mono_left nhdsWithin_le_nhds
    filter_upwards [htend.eventually hev, f₁, f₂, self_mem_nhdsWithin] with B hB g₁ g₂ hf
    have hBa : B ∈ Matrices.GroupLieProduct.tracelessPi (SupportBond (levelDepth K k) Γ) :=
      fun i => (Submodule.mem_pi.mp hf) i (Set.mem_univ i)
    rw [piTracelessIncl_proj hBa] at hB
    have h3 := congrArg (piTracelessIncl ↥Γ) hB
    rwa [piTracelessIncl_proj g₁.2, piTracelessIncl_proj g₂.2] at h3
end Main
end PeriodicLattice.LinearizingCorrection
end YangMills.Construction
