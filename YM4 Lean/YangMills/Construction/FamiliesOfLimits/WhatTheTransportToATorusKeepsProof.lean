import YangMills.Construction.FamiliesOfLimits.WhatTheTransportToATorusKeeps
import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorusProof
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
open YangMills.Construction.TestFunctions YangMills.Construction.AmbientPoints
open YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.FundamentalDomain (fundBox openBox IntegrableOnFundBox torusIntegral)
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.FamiliesOfLimits.TorusPeriodization
section Euclidean
variable {ℓ : ℝ}
private theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
private theorem norm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
private theorem latticeTranslate_zero (ℓ : ℝ) : latticeTranslate ℓ 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.latticeTranslate_zero <;> assumption
private theorem le_euclidNormVec_latticeTranslate (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ euclidNormVec (latticeTranslate ℓ k) := by apply _root_.YangMills.Construction.TestPairs.le_euclidNormVec_latticeTranslate <;> assumption
private theorem eq_of_translates_mem_of_diam (hℓ : 0 < ℓ) {A : Set (Fin 4 → ℝ)}
    (hA : HasDiameterLE A (ℓ / 2)) {x : Fin 4 → ℝ} {k k' : Fin 4 → ℤ}
    (hx : x + latticeTranslate ℓ k ∈ A) (hx' : x + latticeTranslate ℓ k' ∈ A) : k = k' := by
  by_contra hne
  have hdiff : (x + latticeTranslate ℓ k) - (x + latticeTranslate ℓ k') =
      latticeTranslate ℓ (k - k') := by
    funext μ
    simp [latticeTranslate]
    ring
  have hdiam := hA _ hx _ hx'
  rw [hdiff] at hdiam
  have hlow := le_euclidNormVec_latticeTranslate hℓ (sub_ne_zero.mpr hne)
  linarith
variable {A : Set (Fin 4 → ℝ)} {g : (Fin 4 → ℝ) → ℝ}
private theorem periodicSum_eq_single_term (hℓ : 0 < ℓ) (hA : HasDiameterLE A (ℓ / 2))
    (hg : Function.support g ⊆ A) {x : Fin 4 → ℝ} {k : Fin 4 → ℤ}
    (hk : g (x + latticeTranslate ℓ k) ≠ 0) :
    periodicSum ℓ g x = g (x + latticeTranslate ℓ k) := by
  refine tsum_eq_single k fun k' hk' => ?_
  by_contra hne
  exact hk' (eq_of_translates_mem_of_diam hℓ hA (hg hne) (hg hk))
private theorem periodize_torusProj_of_ne (hℓ : 0 < ℓ) (hA : HasDiameterLE A (ℓ / 2))
    (hg : Function.support g ⊆ A) {x : Fin 4 → ℝ} (hx : g x ≠ 0) :
    periodize ℓ g (torusProj ℓ x) = g x := by
  have h0 : g (x + latticeTranslate ℓ 0) ≠ 0 := by simpa [latticeTranslate_zero] using hx
  rw [periodize_torusProj, periodicSum_eq_single_term hℓ hA hg h0, latticeTranslate_zero,
    add_zero]
private theorem exists_lift_of_periodize_ne (hℓ : 0 < ℓ) (hA : HasDiameterLE A (ℓ / 2))
    (hg : Function.support g ⊆ A) {u : Torus4 ℓ} (hu : periodize ℓ g u ≠ 0) :
    ∃ x, torusProj ℓ x = u ∧ g x ≠ 0 ∧ periodize ℓ g u = g x := by
  obtain ⟨v, rfl⟩ := torusProj_surjective ℓ u
  by_cases hex : ∃ k, g (v + latticeTranslate ℓ k) ≠ 0
  · obtain ⟨k, hk⟩ := hex
    exact ⟨v + latticeTranslate ℓ k, torusProj_add_latticeTranslate ℓ v k, hk, by
      rw [periodize_torusProj, periodicSum_eq_single_term hℓ hA hg hk]⟩
  · push Not at hex
    exact absurd (by simp [periodize_torusProj, periodicSum, hex]) hu
private theorem support_periodize (hℓ : 0 < ℓ) (hA : HasDiameterLE A (ℓ / 2))
    (hg : Function.support g ⊆ A) :
    Function.support (periodize ℓ g) = torusProj ℓ '' Function.support g := by
  ext u
  constructor
  · intro hu
    obtain ⟨x, rfl, hx, -⟩ := exists_lift_of_periodize_ne hℓ hA hg hu
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [Function.mem_support, periodize_torusProj_of_ne hℓ hA hg hx]
    exact hx
private theorem summable_translates_of_diam (hℓ : 0 < ℓ) (hA : HasDiameterLE A (ℓ / 2))
    (hg : Function.support g ⊆ A) (x : Fin 4 → ℝ) :
    Summable fun k : Fin 4 → ℤ => g (x + latticeTranslate ℓ k) := by
  refine summable_of_hasFiniteSupport (Set.Subsingleton.finite ?_)
  intro k hk k' hk'
  exact eq_of_translates_mem_of_diam hℓ hA (hg hk) (hg hk')
private theorem periodize_linear (hℓ : 0 < ℓ) (hA : HasDiameterLE A (ℓ / 2))
    {h : (Fin 4 → ℝ) → ℝ} (hg : Function.support g ⊆ A) (hh : Function.support h ⊆ A)
    (a b : ℝ) : periodize ℓ (a • g + b • h) = a • periodize ℓ g + b • periodize ℓ h := by
  funext u
  obtain ⟨v, rfl⟩ := torusProj_surjective _ u
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, periodize_torusProj]
  unfold periodicSum
  have hsg := (summable_translates_of_diam hℓ hA hg v).mul_left a
  have hsh := (summable_translates_of_diam hℓ hA hh v).mul_left b
  rw [← tsum_mul_left, ← tsum_mul_left, ← hsg.tsum_add hsh]
  rfl
private theorem periodize_norm_le (hℓ : 0 < ℓ) (hA : HasDiameterLE A (ℓ / 2))
    (hg : Function.support g ⊆ A) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (u : Torus4 ℓ) :
    ‖periodize ℓ g u‖ ≤ C := by
  by_cases hu : periodize ℓ g u = 0
  · rw [hu, norm_zero]
    exact (norm_nonneg _).trans (hC 0)
  · obtain ⟨x, -, -, hx⟩ := exists_lift_of_periodize_ne hℓ hA hg hu
    rw [hx]
    exact hC x
private theorem periodize_bounded_and_uniformNorm (hℓ : 0 < ℓ) (hA : HasDiameterLE A (ℓ / 2))
    (hg : Function.support g ⊆ A) (hb : IsBoundedFun g) :
    IsBoundedFun (periodize ℓ g) ∧ uniformNorm (periodize ℓ g) = uniformNorm g := by
  obtain ⟨C, hC⟩ := hb
  have hbdd : BddAbove (range fun x => ‖g x‖) := ⟨C, by
    rintro _ ⟨x, rfl⟩
    exact hC x⟩
  have hle : ∀ x, ‖g x‖ ≤ uniformNorm g := fun x => le_ciSup hbdd x
  have hnn : 0 ≤ uniformNorm g := Real.iSup_nonneg fun _ => norm_nonneg _
  have hper : ∀ u, ‖periodize ℓ g u‖ ≤ uniformNorm g := fun u =>
    periodize_norm_le hℓ hA hg hle u
  have hbddp : BddAbove (range fun u => ‖periodize ℓ g u‖) := ⟨uniformNorm g, by
    rintro _ ⟨u, rfl⟩
    exact hper u⟩
  have hnnp : 0 ≤ uniformNorm (periodize ℓ g) := Real.iSup_nonneg fun _ => norm_nonneg _
  refine ⟨⟨_, hper⟩, le_antisymm (Real.iSup_le hper hnn) (Real.iSup_le (fun x => ?_) hnnp)⟩
  by_cases hx : g x = 0
  · rw [hx, norm_zero]
    exact hnnp
  · have hsup := le_ciSup hbddp (torusProj ℓ x)
    simp only [periodize_torusProj_of_ne hℓ hA hg hx] at hsup
    exact hsup
private theorem finite_translates_meeting (hℓ : 0 < ℓ) {W K : Set (Fin 4 → ℝ)}
    (hW : Bornology.IsBounded W) (hK : Bornology.IsBounded K) :
    {k : Fin 4 → ℤ | ∃ y ∈ W, y + latticeTranslate ℓ k ∈ K}.Finite := by
  obtain ⟨r, hr⟩ := hW.exists_norm_le
  obtain ⟨r', hr'⟩ := hK.exists_norm_le
  set N : ℤ := ⌈(r + r') / ℓ⌉
  refine (Set.Finite.pi (t := fun _ : Fin 4 => Set.Icc (-N) N) fun _ =>
    Set.finite_Icc _ _).subset ?_
  rintro k ⟨y, hy, hyk⟩
  intro μ _
  have hnorm : ‖latticeTranslate ℓ k‖ ≤ r + r' := by
    have hsplit : latticeTranslate ℓ k = (y + latticeTranslate ℓ k) - y := by abel
    rw [hsplit]
    exact (norm_sub_le _ _).trans (by linarith [hr y hy, hr' _ hyk])
  have hcoord : |ℓ * (k μ : ℝ)| ≤ r + r' := by
    have hpi := norm_le_pi_norm (latticeTranslate ℓ k) μ
    rw [Real.norm_eq_abs] at hpi
    exact hpi.trans hnorm
  have hdiv : |(k μ : ℝ)| ≤ (r + r') / ℓ := by
    rw [le_div_iff₀ hℓ, mul_comm]
    rwa [abs_mul, abs_of_pos hℓ] at hcoord
  have hceil : |(k μ : ℝ)| ≤ (N : ℝ) := hdiv.trans (Int.le_ceil _)
  have habs := abs_le.mp hceil
  exact ⟨by exact_mod_cast habs.1, by exact_mod_cast habs.2⟩
private theorem isBounded_fundBox (ℓ : ℝ) : Bornology.IsBounded (fundBox ℓ) := by
  have hsub : fundBox ℓ ⊆ Set.Icc (fun _ => -ℓ / 2) (fun _ => ℓ / 2) := fun y hy =>
    ⟨fun μ => (FundamentalDomain.mem_fundBox.1 hy μ).1,
      fun μ => (FundamentalDomain.mem_fundBox.1 hy μ).2.le⟩
  exact (Metric.isBounded_Icc _ _).subset hsub
private theorem measurableSet_fundBox (ℓ : ℝ) : MeasurableSet (fundBox ℓ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico
private def shiftedBox (ℓ : ℝ) (k : Fin 4 → ℤ) : Set (Fin 4 → ℝ) :=
  (fun x => x - latticeTranslate ℓ k) ⁻¹' fundBox ℓ
private theorem measurableSet_shiftedBox (ℓ : ℝ) (k : Fin 4 → ℤ) :
    MeasurableSet (shiftedBox ℓ k) :=
  (measurable_id.sub_const _) (measurableSet_fundBox ℓ)
private theorem iUnion_shiftedBox (hℓ : 0 < ℓ) : ⋃ k, shiftedBox ℓ k = univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have hcoord : ∀ μ, ∃ m : ℤ, x μ - ℓ * (m : ℝ) ∈ Set.Ico (-ℓ / 2) (ℓ / 2) := fun μ => by
    obtain ⟨m, hm, -⟩ := existsUnique_add_zsmul_mem_Ico hℓ (x μ) (-ℓ / 2)
    refine ⟨-m, ?_⟩
    have heq : x μ - ℓ * ((-m : ℤ) : ℝ) = x μ + m • ℓ := by
      simp only [zsmul_eq_mul]
      push_cast
      ring
    have hup : -ℓ / 2 + ℓ = ℓ / 2 := by ring
    rw [heq, ← hup]
    exact hm
  choose k hk using hcoord
  exact Set.mem_iUnion.2 ⟨k, FundamentalDomain.mem_fundBox.2 hk⟩
private theorem pairwise_disjoint_shiftedBox (hℓ : 0 < ℓ) :
    Pairwise (Function.onFun Disjoint (shiftedBox ℓ)) := by
  intro k k' hne
  refine Set.disjoint_left.2 fun x hx hx' => hne ?_
  funext μ
  by_contra hμ
  have hm := FundamentalDomain.mem_fundBox.1 hx μ
  have hm' := FundamentalDomain.mem_fundBox.1 hx' μ
  simp only [Pi.sub_apply, latticeTranslate, Set.mem_Ico] at hm hm'
  have hone : (1 : ℝ) ≤ |(k μ : ℝ) - (k' μ : ℝ)| := by
    have hint : 1 ≤ |k μ - k' μ| := Int.one_le_abs (sub_ne_zero.mpr hμ)
    exact_mod_cast hint
  have hlow : ℓ ≤ |ℓ * ((k μ : ℝ) - (k' μ : ℝ))| := by
    rw [abs_mul, abs_of_pos hℓ]
    nlinarith
  have hhigh : |ℓ * ((k μ : ℝ) - (k' μ : ℝ))| < ℓ := by
    rw [abs_lt]
    constructor <;> nlinarith [hm.1, hm.2, hm'.1, hm'.2]
  linarith
private theorem integral_fundBox_shift (k : Fin 4 → ℤ) :
    ∫ y in fundBox ℓ, g (y + latticeTranslate ℓ k) = ∫ x in shiftedBox ℓ k, g x := by
  have hpre : (fun y : Fin 4 → ℝ => y + latticeTranslate ℓ k) ⁻¹' shiftedBox ℓ k =
      fundBox ℓ := by
    ext y
    simp [shiftedBox]
  have hmp := (measurePreserving_add_right (volume : Measure (Fin 4 → ℝ))
    (latticeTranslate ℓ k)).setIntegral_preimage_emb
    (MeasurableEquiv.addRight (latticeTranslate ℓ k)).measurableEmbedding g (shiftedBox ℓ k)
  rw [hpre] at hmp
  exact hmp
private theorem integral_periodize (hℓ : 0 < ℓ) (hcont : Continuous g)
    (hc : HasCompactSupport g) :
    IntegrableOn (fun y => periodize ℓ g (torusProj ℓ y)) (fundBox ℓ) ∧ Integrable g ∧
      ∫ y in fundBox ℓ, periodize ℓ g (torusProj ℓ y) = ∫ x, g x := by
  have hint : Integrable g := hcont.integrable_of_hasCompactSupport hc
  have hfin := finite_translates_meeting hℓ (isBounded_fundBox ℓ) hc.isCompact.isBounded
  set F := hfin.toFinset
  have hF : ∀ k, k ∉ F → ∀ y ∈ fundBox ℓ, g (y + latticeTranslate ℓ k) = 0 := fun k hk y hy => by
    by_contra hne
    exact hk (hfin.mem_toFinset.2 ⟨y, hy, subset_tsupport g hne⟩)
  have hform : ∀ y ∈ fundBox ℓ,
      periodize ℓ g (torusProj ℓ y) = ∑ k ∈ F, g (y + latticeTranslate ℓ k) := fun y hy => by
    rw [periodize_torusProj]
    exact tsum_eq_sum fun k hk => hF k hk y hy
  have hk : ∀ k, Integrable fun y => g (y + latticeTranslate ℓ k) := fun k =>
    hint.comp_add_right (latticeTranslate ℓ k)
  have hsum : Integrable fun y => ∑ k ∈ F, g (y + latticeTranslate ℓ k) :=
    integrable_finsetSum F fun k _ => hk k
  refine ⟨?_, hint, ?_⟩
  · exact hsum.integrableOn.congr_fun (fun y hy => (hform y hy).symm) (measurableSet_fundBox ℓ)
  · rw [setIntegral_congr_fun (measurableSet_fundBox ℓ) hform,
      integral_finsetSum F fun k _ => (hk k).integrableOn]
    have hun := hasSum_integral_iUnion (measurableSet_shiftedBox ℓ)
      (pairwise_disjoint_shiftedBox hℓ) (f := g) (μ := volume) hint.integrableOn
    rw [iUnion_shiftedBox hℓ, setIntegral_univ] at hun
    rw [← hun.tsum_eq, tsum_eq_sum (s := F)]
    · exact Finset.sum_congr rfl fun k _ => integral_fundBox_shift k
    · intro k hk'
      rw [← integral_fundBox_shift k]
      exact setIntegral_eq_zero_of_forall_eq_zero fun y hy => hF k hk' y hy
private theorem contDiff_periodize_lift (hℓ : 0 < ℓ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) : ContDiff ℝ 1 fun y => periodize ℓ g (torusProj ℓ y) := by
  refine contDiff_iff_contDiffAt.2 fun y₀ => ?_
  have hfin := finite_translates_meeting hℓ (Metric.isBounded_ball (x := y₀) (r := 1))
    hc.isCompact.isBounded
  have hsum : ContDiff ℝ 1 fun y => ∑ k ∈ hfin.toFinset, g (y + latticeTranslate ℓ k) :=
    ContDiff.sum fun k _ => hg.comp (contDiff_id.add contDiff_const)
  refine hsum.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
  rw [periodize_torusProj]
  refine tsum_eq_sum fun k hk => ?_
  by_contra hne
  exact hk (hfin.mem_toFinset.2 ⟨y, hy, subset_tsupport g hne⟩)
end Euclidean
section Torus
variable (s : Conventions.StandingParameters)
private theorem torusSide_pos : 0 < PeriodicLattice.torusSide s.L s.m := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.torusSide_pos <;> assumption
private def plainToPt : (Fin 4 → ℝ) ≃ₜ Pt s .euclidean where
  toEquiv := Equiv.refl _
  continuous_toFun := by
    refine (LipschitzWith.of_dist_le_mul (K := 2) fun (x y : Fin 4 → ℝ) => ?_).continuous
    rw [NNReal.coe_ofNat, dist_eq_norm]
    exact euclidNormVec_le_two_mul_norm (x - y)
  continuous_invFun := by
    have hlip : @LipschitzWith (Pt s .euclidean) (Fin 4 → ℝ) _ _ 1 fun x => x := by
      refine LipschitzWith.of_dist_le_mul fun (x y : Fin 4 → ℝ) => ?_
      rw [NNReal.coe_one, one_mul]
      change dist x y ≤ euclidNormVec (x - y)
      rw [dist_eq_norm]
      exact norm_le_euclidNormVec (x - y)
    exact hlip.continuous
private theorem tsupport_plain_eq (f : Pt s .euclidean → ℝ) :
    tsupport (fun x : Fin 4 → ℝ => f x) = (tsupport f : Set (Pt s .euclidean)) := by
  have hcl := (plainToPt s).symm.image_closure (Function.support f)
  have hid : ∀ T : Set (Pt s .euclidean), (plainToPt s).symm '' T = T := fun T => Set.image_id T
  rw [hid, hid] at hcl
  exact hcl.symm
private theorem hasCompactSupport_plain {f : Pt s .euclidean → ℝ}
    (hc : IsCompact (tsupport f)) : HasCompactSupport (fun x : Fin 4 → ℝ => f x) := by
  have himg := hc.image (plainToPt s).symm.continuous
  have heq : (plainToPt s).symm '' tsupport f = tsupport (fun x : Fin 4 → ℝ => f x) :=
    (Set.image_id _).trans (tsupport_plain_eq s f).symm
  rw [heq] at himg
  exact himg
private theorem pointDist_proj_le (x y : Fin 4 → ℝ) :
    pointDist s .torus (proj s .torus x) (proj s .torus y) ≤ euclidNormVec (x - y) := by
  have hleast := (isLeast_pointDist_proj s x y).2 ⟨0, rfl⟩
  simpa [latticeTranslate_zero] using hleast
private theorem continuous_proj_torus : Continuous (proj s .torus) := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun (x y : Fin 4 → ℝ) => ?_).continuous
  have hd : dist x y = ‖x - y‖ := dist_eq_norm x y
  rw [NNReal.coe_ofNat, hd]
  exact (pointDist_proj_le s x y).trans (euclidNormVec_le_two_mul_norm _)
private theorem iInf_image_image {β γ : Type*} (φ : β → γ) (A' A'' : Set β)
    (G : γ → γ → ℝ≥0∞) :
    ⨅ a ∈ φ '' A', ⨅ b ∈ φ '' A'', G a b = ⨅ a ∈ A', ⨅ b ∈ A'', G (φ a) (φ b) := by
  rw [iInf_image]
  simp only [iInf_image]
variable {s}
variable {A : Set (Pt s .euclidean)} {f : Pt s .euclidean → ℝ}
private theorem pointDist_proj_eq (hA : HasDiameterLE A (s.side / 2)) {x y : Fin 4 → ℝ}
    (hx : x ∈ A) (hy : y ∈ A) :
    pointDist s .torus (proj s .torus x) (proj s .torus y) = pointDist s .euclidean x y := by
  have hℓ := torusSide_pos s
  have hxy : euclidNormVec (x - y) ≤ PeriodicLattice.torusSide s.L s.m / 2 := hA x hx y hy
  obtain ⟨⟨k, hk⟩, -⟩ := isLeast_pointDist_proj s x y
  apply le_antisymm (pointDist_proj_le s x y)
  change euclidNormVec (x - y) ≤ _
  rw [← hk]
  by_cases k0 : k = 0
  · subst k0
    simp [latticeTranslate_zero]
  · have hlow := le_euclidNormVec_latticeTranslate hℓ k0
    have htri := euclidNormVec_sub_le (latticeTranslate (PeriodicLattice.torusSide s.L s.m) k)
      (x - y) 0
    rw [sub_zero, sub_zero, euclidNormVec_sub_comm _ (x - y)] at htri
    change _ ≤ euclidNormVec (x - y - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k)
    linarith
private theorem setDist_proj_eq (hA : HasDiameterLE A (s.side / 2))
    {A' A'' : Set (Pt s .euclidean)} (h' : A' ⊆ A) (h'' : A'' ⊆ A) :
    setDist s .torus (proj s .torus '' A') (proj s .torus '' A'') =
      setDist s .euclidean A' A'' := by
  refine (iInf_image_image (proj s .torus) A' A''
    fun a b => ENNReal.ofReal (pointDist s .torus a b)).trans ?_
  refine iInf_congr fun x => iInf_congr fun hx => iInf_congr fun y => iInf_congr fun hy => ?_
  exact congrArg ENNReal.ofReal (pointDist_proj_eq hA (h' hx) (h'' hy))
private theorem support_subset_of_supported (hf : IsSupportedIn s A f) :
    Function.support f ⊆ A :=
  (subset_tsupport f).trans hf.2
private theorem periodizeEqTsumTranslates_of_diam (hA : HasDiameterLE A (s.side / 2))
    (hf : IsSupportedIn s A f) : PeriodizeEqTsumTranslates s A f := by
  have hℓ := torusSide_pos s
  have hsup := support_subset_of_supported hf
  refine ⟨?_, ?_, ?_⟩
  · funext x
    exact periodize_torusProj _ f x
  · intro x k hk k' hk'
    exact eq_of_translates_mem_of_diam hℓ hA (hsup hk) (hsup hk')
  · intro hcube y hy k hk0
    by_contra hne
    have hmem := hcube (hsup hne)
    obtain ⟨μ, hμ⟩ := Function.ne_iff.mp hk0
    have hbox := FundamentalDomain.mem_fundBox.1 hy μ
    have hopen := FundamentalDomain.mem_openBox.1 hmem μ
    have hμ' : k μ ≠ 0 := hμ
    have hside : 0 < s.side := hℓ
    simp only [Pi.add_apply, latticeTranslate, mem_Ioo, mem_Ico] at hbox hopen
    have hcases : k μ ≤ -1 ∨ 1 ≤ k μ := by omega
    rcases hcases with hneg | hpos
    · have hcast : (k μ : ℝ) ≤ -1 := by exact_mod_cast hneg
      have hmul := mul_le_mul_of_nonneg_left hcast hside.le
      linarith [hbox.2, hopen.1]
    · have hcast : (1 : ℝ) ≤ k μ := by exact_mod_cast hpos
      have hmul := mul_le_mul_of_nonneg_left hcast hside.le
      linarith [hbox.1, hopen.2]
private theorem projPreservesDist_of_diam (hA : HasDiameterLE A (s.side / 2)) :
    ProjPreservesDist s A :=
  ⟨fun _ hx _ hy => pointDist_proj_eq hA hx hy,
    fun _ _ h' h'' => setDist_proj_eq hA h' h''⟩
private theorem periodizeLinearOn_of_diam (hA : HasDiameterLE A (s.side / 2)) :
    PeriodizeLinearOn s A := by
  intro f h hf hh a b
  have hℓ := torusSide_pos s
  constructor
  · have hsub : tsupport (a • f + b • h) ⊆ tsupport f ∪ tsupport h := by
      refine closure_minimal ?_ ((isClosed_tsupport f).union (isClosed_tsupport h))
      intro x hx
      by_contra hno
      simp only [mem_union, not_or] at hno
      have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport hno.1
      have hh0 : h x = 0 := image_eq_zero_of_notMem_tsupport hno.2
      exact hx (by simp [hf0, hh0])
    exact ⟨(hf.1.union hh.1).of_isClosed_subset (isClosed_tsupport _) hsub,
      hsub.trans (union_subset hf.2 hh.2)⟩
  · exact periodize_linear hℓ hA (support_subset_of_supported hf)
      (support_subset_of_supported hh) a b
private theorem tsupport_periodizeOnTorus (hA : HasDiameterLE A (s.side / 2))
    (hf : IsSupportedIn s A f) :
    tsupport (periodizeOnTorus s f) = proj s .torus '' tsupport f := by
  have hℓ := torusSide_pos s
  have hs : Function.support (periodizeOnTorus s f) =
      proj s .torus '' Function.support f :=
    support_periodize hℓ hA (support_subset_of_supported hf)
  have hc := hasCompactSupport_plain s hf.1
  apply Subset.antisymm
  · refine closure_minimal ?_ (hc.image (continuous_proj_torus s)).isClosed
    rw [hs]
    exact image_mono (subset_tsupport fun x : Fin 4 → ℝ => f x)
  · unfold tsupport
    rw [hs]
    exact image_closure_subset_closure_image (continuous_proj_torus s)
private theorem periodize_lipschitz_of_ne (hA : HasDiameterLE A (s.side / 2))
    (hf : IsSupportedIn s A f) {C : ℝ}
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y) (u v : Pt s .torus)
    (hu : periodizeOnTorus s f u ≠ 0) :
    ‖periodizeOnTorus s f u - periodizeOnTorus s f v‖ ≤ C * pointDist s .torus u v := by
  have hℓ := torusSide_pos s
  have hsup := support_subset_of_supported hf
  obtain ⟨x, rfl, hx, hTx⟩ := exists_lift_of_periodize_ne hℓ hA hsup hu
  obtain ⟨y, rfl⟩ := torusProj_surjective _ v
  by_cases hv : periodizeOnTorus s f (torusProj _ y) = 0
  · obtain ⟨⟨k, hk⟩, -⟩ := isLeast_pointDist_proj s x y
    have hw : f (y + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) = 0 := by
      by_contra hne
      have hval := periodize_torusProj_of_ne hℓ hA hsup hne
      rw [torusProj_add_latticeTranslate] at hval
      exact hne (hval.symm.trans hv)
    have hbound := hC x (y + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k)
    rw [hw, sub_zero] at hbound
    have hdist : euclidDistR4 x (y + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) =
        pointDist s .torus (proj s .torus x) (proj s .torus y) := by
      rw [← hk]
      simp only [euclidDistR4]
      congr 1
      abel
    rw [hdist] at hbound
    rw [hv, sub_zero]
    change ‖periodize _ f (torusProj _ x)‖ ≤ _
    rw [hTx]
    exact hbound
  · obtain ⟨y', hy', hy'ne, hTy⟩ := exists_lift_of_periodize_ne hℓ hA hsup hv
    change ‖periodize _ f (torusProj _ x) - periodize _ f (torusProj _ y)‖ ≤ _
    rw [hTx, hTy, ← hy']
    have hdist := pointDist_proj_eq hA (hsup hx) (hsup hy'ne)
    have hbound := hC x y'
    change _ ≤ C * pointDist s .torus (proj s .torus x) (proj s .torus y')
    rw [hdist]
    exact hbound
private theorem periodize_lipschitz (hA : HasDiameterLE A (s.side / 2))
    (hf : IsSupportedIn s A f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y) (u v : Pt s .torus) :
    ‖periodizeOnTorus s f u - periodizeOnTorus s f v‖ ≤ C * pointDist s .torus u v := by
  by_cases hu : periodizeOnTorus s f u = 0
  · by_cases hv : periodizeOnTorus s f v = 0
    · rw [hu, hv, sub_self, norm_zero]
      exact mul_nonneg hC0 (dist_nonneg : (0 : ℝ) ≤ dist u v)
    · rw [norm_sub_rev, pointDist_comm]
      exact periodize_lipschitz_of_ne hA hf hC v u hv
  · exact periodize_lipschitz_of_ne hA hf hC u v hu
private theorem isBoundedFun_of_lipschitz (hf : IsCompact (tsupport f))
    (hL : IsLipschitzFor (pointDist s .euclidean) f) : IsBoundedFun f := by
  obtain ⟨C, hC0, hC⟩ := hL
  have hcont : Continuous f := by
    refine (LipschitzWith.of_dist_le_mul (K := C.toNNReal) fun x y => ?_).continuous
    rw [Real.coe_toNNReal C hC0, dist_eq_norm]
    exact hC x y
  obtain ⟨B, hB⟩ := hf.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact (hB x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _
private theorem lipschitz_bounds {M : ℝ} (hM : 1 ≤ M) (hA : HasDiameterLE A (s.side / 2))
    (hf : IsSupportedIn s A f) (hL : IsLipschitzFor (pointDist s .euclidean) f) :
    IsLipschitzFor (pointDist s .torus) (periodizeOnTorus s f) ∧
      lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (periodizeOnTorus s f) ≤
        lipConstR4 f ∧
      sharpNormTorus (ℓ := PeriodicLattice.torusSide s.L s.m) M (periodizeOnTorus s f) ≤
        sharpNormR4 M f := by
  have hbound := isBoundedFun_of_lipschitz hf.1 hL
  obtain ⟨C, hC0, hC⟩ := hL
  have hlip : lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (periodizeOnTorus s f) ≤
      lipConstR4 f := by
    refine csInf_le_csInf ⟨0, fun c hc => hc.1⟩ ⟨C, hC0, hC⟩ ?_
    exact fun c hc => ⟨hc.1, periodize_lipschitz hA hf hc.1 hc.2⟩
  refine ⟨⟨C, hC0, periodize_lipschitz hA hf hC0 hC⟩, hlip, ?_⟩
  exact max_le_max
    (periodize_bounded_and_uniformNorm (torusSide_pos s) hA (support_subset_of_supported hf)
      hbound).2.le
    (mul_le_mul_of_nonneg_left hlip (by linarith))
private theorem periodizePreservesFun_of_diam {M : ℝ} (hM : 1 ≤ M)
    (hA : HasDiameterLE A (s.side / 2)) (hf : IsSupportedIn s A f) :
    PeriodizePreservesFun s M f := by
  have hℓ := torusSide_pos s
  have hc := hasCompactSupport_plain s hf.1
  refine ⟨tsupport_periodizeOnTorus hA hf,
    periodize_bounded_and_uniformNorm hℓ hA (support_subset_of_supported hf), fun hcont => ?_,
    lipschitz_bounds hM hA hf, fun h1 => ?_⟩
  · exact integral_periodize hℓ (hcont.comp (plainToPt s).continuous) hc
  · exact contDiff_periodize_lift hℓ h1 hc
private theorem projImageClosedBall_holds : ProjImageClosedBall s := by
  intro (c : Fin 4 → ℝ) R _ _
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (pointDist_proj_le s x c).trans hx
  · intro hu
    obtain ⟨y, rfl⟩ := torusProj_surjective _ u
    obtain ⟨⟨k, hk⟩, -⟩ := isLeast_pointDist_proj s y c
    have hproj : torusProj (PeriodicLattice.torusSide s.L s.m)
        (y - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) = torusProj _ y := by
      have hadd := torusProj_add_latticeTranslate (PeriodicLattice.torusSide s.L s.m)
        (y - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) k
      rw [sub_add_cancel] at hadd
      exact hadd.symm
    refine ⟨y - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k, ?_, hproj⟩
    exact show euclidNormVec (y - latticeTranslate (PeriodicLattice.torusSide s.L s.m) k - c) ≤
        R from by
      rw [sub_right_comm]
      exact (show _ = _ from hk).trans_le hu
private theorem periodizeBasicProps_of_diam {M : ℝ} (hM : 1 ≤ M)
    (hA : HasDiameterLE A (s.side / 2)) (hf : IsSupportedIn s A f) :
    PeriodizeBasicProps s M A f :=
  ⟨periodizeEqTsumTranslates_of_diam hA hf, projPreservesDist_of_diam hA,
    periodizeLinearOn_of_diam hA, periodizePreservesFun_of_diam hM hA hf,
    projImageClosedBall_holds⟩
variable {n : ℕ} {X : Fin n → Pt s .euclidean → ℝ}
private theorem exists_originBall_radius (hX : X ∈ separatedTuples s .euclidean n) :
    ∃ ρ : ℝ, 0 < ρ ∧ SupportsInOriginBall s ρ X := by
  have hcomp : IsCompact (⋃ i, tsupport (X i)) := isCompact_iUnion fun i => (hX.1 i).2
  obtain ⟨r, hr, hsub⟩ := hcomp.isBounded.subset_ball_lt 0 ((0 : Fin 4 → ℝ) : Pt s .euclidean)
  exact ⟨r, hr, fun i => (subset_iUnion (fun i => tsupport (X i)) i).trans hsub⟩
private theorem originBall_diam_le {ρ D : ℝ} (hD : 2 * ρ ≤ D) :
    HasDiameterLE (originBall s ρ) D := by
  intro x hx y hy
  have hxρ : euclidNormVec (x - 0) < ρ := hx
  have hyρ : euclidNormVec (y - 0) < ρ := hy
  have htri := euclidNormVec_sub_le x 0 y
  rw [euclidNormVec_sub_comm 0 y] at htri
  linarith
private theorem originBall_subset_openBox {ρ : ℝ} (h4 : 4 * ρ ≤ s.side) (hρ : 0 < ρ) :
    originBall s ρ ⊆ openBox s.side := by
  intro (x : Fin 4 → ℝ) hx
  have hxρ : euclidNormVec (x - 0) < ρ := hx
  rw [sub_zero] at hxρ
  refine FundamentalDomain.mem_openBox.2 fun μ => ?_
  have hcoord := abs_lt.mp ((abs_apply_le_euclidNormVec x μ).trans_lt hxρ)
  exact ⟨by linarith [hcoord.1], by linarith [hcoord.2]⟩
private theorem isLipschitzFor_of_isC1Fn {g : Pt s .euclidean → ℝ} (h1 : IsC1Fn g)
    (hc : IsCompact (tsupport g)) : IsLipschitzFor (pointDist s .euclidean) g := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_plain s hc) ((isC1Fn_euclidean_iff g).1 h1) one_ne_zero
  refine ⟨C, C.coe_nonneg, fun (x y : Fin 4 → ℝ) => ?_⟩
  have hle := hC.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left (norm_le_euclidNormVec _) C.coe_nonneg)
private theorem originBallAdmits_and_preserves {M ρ : ℝ} (hM : 1 ≤ M)
    (hX : X ∈ separatedTuples s .euclidean n) (hρ : 0 < ρ) (hs : SupportsInOriginBall s ρ X)
    (h4 : 4 * ρ ≤ s.side) : OriginBallAdmits s M ρ X ∧ PeriodizePreservesTuple s M X := by
  have hD : HasDiameterLE (originBall s ρ) (s.side / 2) :=
    originBall_diam_le (by linarith)
  have hsup : ∀ i, IsSupportedIn s (originBall s ρ) (X i) := fun i =>
    ⟨(hX.1 i).2, hs i⟩
  have hts : ∀ i, tsupport (periodizedTuple s X i) =
      proj s .torus '' (tsupport (X i) : Set (Pt s .euclidean)) := fun i =>
    (tsupport_periodizeOnTorus hD (hsup i)).trans (congrArg _ (tsupport_plain_eq s (X i)))
  have hfun := fun i => periodizePreservesFun_of_diam hM hD (hsup i)
  have hlip := fun i => isLipschitzFor_of_isC1Fn (hX.1 i).1 (hX.1 i).2
  refine ⟨⟨hD, originBall_subset_openBox h4 hρ,
      fun i => ⟨hsup i, periodizeBasicProps_of_diam hM hD (hsup i)⟩⟩,
    ⟨fun i => ⟨(hfun i).2.2.2.2 (hX.1 i).1, ?_⟩, fun i j hij => ?_⟩, fun i => ?_,
    fun i k _ => ?_, fun i c R hR hR' hsub => ?_⟩
  · rw [hts i, ← tsupport_plain_eq s (X i)]
    exact (hasCompactSupport_plain s (hX.1 i).2).image (continuous_proj_torus s)
  · show Disjoint (tsupport (periodizedTuple s X i)) (tsupport (periodizedTuple s X j))
    rw [hts i, hts j]
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hdist := pointDist_proj_eq hD ((hsup j).2 hy) ((hsup i).2 hx)
    rw [hxy, pointDist_self] at hdist
    have hyx : y = x := eq_of_pointDist_eq_zero .euclidean hdist.symm
    subst hyx
    exact Set.disjoint_left.1 (hX.2 hij) hx hy
  · have hl := (hfun i).2.2.2.1 (hlip i)
    exact ⟨hl.1, hl.2.2⟩
  · rw [hts i, hts k]
    exact setDist_proj_eq hD (hsup i).2 (hsup k).2
  · rw [hts i, ← projImageClosedBall_holds c R hR hR']
    exact image_mono hsub
private theorem eventuallyConnectedSchwingerDefined_of_sep
    (hX : X ∈ separatedTuples s .euclidean n) : EventuallyConnectedSchwingerDefined s X := by
  intro t _ ht
  obtain ⟨ρ, hρ, hs⟩ := exists_originBall_radius hX
  filter_upwards [ht.eventually_ge_atTop (4 * ρ)] with j hj
  have hD : HasDiameterLE (originBall s ρ) ((t j).side / 2) :=
    originBall_diam_le (by linarith)
  refine ⟨⟨originBall s ρ, ?_, hs⟩, fun i => ?_⟩
  · exact iSup₂_le fun x hx => iSup₂_le fun y hy => ENNReal.ofReal_le_ofReal (hD x hx y hy)
  · obtain ⟨C, hC⟩ := (hasCompactSupport_plain s (hX.1 i).2).exists_bound_of_continuous
      ((isC1Fn_euclidean_iff (X i)).1 (hX.1 i).1).continuous
    have hsub : Function.support (X i) ⊆ originBall s ρ :=
      (subset_tsupport (X i)).trans (hs i)
    exact ⟨C, periodize_norm_le (torusSide_pos (t j)) hD hsub hC⟩
end Torus
theorem periodizationProperties_holds : PeriodizationProperties := fun _ _ hM =>
  ⟨fun _ hA _ hf => periodizeBasicProps_of_diam hM hA hf,
    fun _ _ _ hX => ⟨exists_originBall_radius hX,
      fun _ hρ hs h4 => originBallAdmits_and_preserves hM hX hρ hs h4,
      fun _ => eventuallyConnectedSchwingerDefined_of_sep hX⟩⟩
end YangMills.Construction.FamiliesOfLimits.TorusPeriodization
end
