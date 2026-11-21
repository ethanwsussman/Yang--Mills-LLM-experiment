import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.PassageToTheLimit.LatticeFunctionalsAreBoundedForms
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflections
import YangMills.Construction.PassageToTheLimit.SpacesOfTestFunctionsProductsAndSeparatedTuples
import YangMills.Construction.PassageToTheLimit.TransportedLatticeFunctionalsAreBoundedForms
import Mathlib
set_option autoImplicit false
open Set Topology
noncomputable section
namespace YangMills.Construction
open TorusMetric (euclidNormVec torusProj Torus4)
open TestFunctions (periodize periodicSum latticeTranslate HasDiameterLE liftPoint)
namespace LimitSpaces
namespace PeriodizeOnSmallSets
variable {ℓ : ℝ} {B : Set (Fin 4 → ℝ)} {f g : (Fin 4 → ℝ) → ℝ}
theorem latticeTranslate_zero : latticeTranslate ℓ 0 = 0 := by
  funext μ
  simp [latticeTranslate]
theorem le_euclidNormVec_latticeTranslate {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ euclidNormVec (latticeTranslate ℓ k) := by
  obtain ⟨μ, hμ⟩ := Function.ne_iff.mp hk
  have hμ' : k μ ≠ 0 := hμ
  have h1 : (1 : ℝ) ≤ (k μ : ℝ) ^ 2 := by
    have h2 : 0 < (k μ) ^ 2 := by positivity
    have h3 : (1 : ℤ) ≤ (k μ) ^ 2 := by omega
    exact_mod_cast h3
  refine Real.le_sqrt_of_sq_le ?_
  calc ℓ ^ 2 ≤ ℓ ^ 2 * (k μ : ℝ) ^ 2 := le_mul_of_one_le_right (sq_nonneg _) h1
    _ = (latticeTranslate ℓ k μ) ^ 2 := by simp [latticeTranslate, mul_pow]
    _ ≤ ∑ ν, (latticeTranslate ℓ k ν) ^ 2 :=
      Finset.single_le_sum (f := fun ν => (latticeTranslate ℓ k ν) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
theorem eq_zero_of_eq_add_latticeTranslate (hℓ : 0 < ℓ) (hB : HasDiameterLE B (ℓ / 2))
    {x y : Fin 4 → ℝ} (hx : x ∈ B) (hy : y ∈ B) {k : Fin 4 → ℤ}
    (h : x = y + latticeTranslate ℓ k) : k = 0 := by
  by_contra hk
  have h1 := le_euclidNormVec_latticeTranslate (ℓ := ℓ) hk
  have h2 := hB x hx y hy
  have h3 : x - y = latticeTranslate ℓ k := by rw [h]; abel
  rw [h3] at h2
  linarith
theorem torusProj_injOn (hℓ : 0 < ℓ) (hB : HasDiameterLE B (ℓ / 2)) : InjOn (torusProj ℓ) B := by
  intro x hx y hy h
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq h
  have h0 := eq_zero_of_eq_add_latticeTranslate hℓ hB hx hy hk
  rw [hk, h0, latticeTranslate_zero, add_zero]
theorem periodize_torusProj_of_mem (hℓ : 0 < ℓ) (hB : HasDiameterLE B (ℓ / 2))
    (hf : ∀ x, x ∉ B → f x = 0) {x : Fin 4 → ℝ} (hx : x ∈ B) :
    periodize ℓ f (torusProj ℓ x) = f x := by
  rw [TestFunctions.periodize_torusProj]
  unfold periodicSum
  rw [tsum_eq_single 0]
  · rw [latticeTranslate_zero, add_zero]
  · intro k hk
    refine hf _ fun hm => hk ?_
    exact eq_zero_of_eq_add_latticeTranslate hℓ hB hm hx rfl
theorem periodize_eq_zero_of_not_mem (hf : ∀ x, x ∉ B → f x = 0) {w : Torus4 ℓ}
    (hw : w ∉ torusProj ℓ '' B) : periodize ℓ f w = 0 := by
  have h : ∀ k, f (liftPoint w + latticeTranslate ℓ k) = 0 := fun k =>
    hf _ fun hm => hw ⟨_, hm, by
      rw [TestFunctions.torusProj_add_latticeTranslate, TestFunctions.torusProj_liftPoint]⟩
  simp only [periodize, periodicSum, h, tsum_zero]
theorem periodize_linear_comb (hℓ : 0 < ℓ) (hB : HasDiameterLE B (ℓ / 2))
    (hf : ∀ x, x ∉ B → f x = 0) (hg : ∀ x, x ∉ B → g x = 0) (a b : ℝ) :
    periodize ℓ (a • f + b • g) = a • periodize ℓ f + b • periodize ℓ g := by
  have hc : ∀ x, x ∉ B → (a • f + b • g) x = 0 := fun x hx => by simp [hf x hx, hg x hx]
  funext w
  by_cases hw : w ∈ torusProj ℓ '' B
  · obtain ⟨x, hx, rfl⟩ := hw
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [periodize_torusProj_of_mem hℓ hB hc hx, periodize_torusProj_of_mem hℓ hB hf hx,
      periodize_torusProj_of_mem hℓ hB hg hx]
    simp
  · simp only [Pi.add_apply, Pi.smul_apply]
    rw [periodize_eq_zero_of_not_mem hc hw, periodize_eq_zero_of_not_mem hf hw,
      periodize_eq_zero_of_not_mem hg hw]
    simp
theorem uniformNorm_periodize (hℓ : 0 < ℓ) (hB : HasDiameterLE B (ℓ / 2))
    (hf : ∀ x, x ∉ B → f x = 0) (hb : TestFunctions.IsBoundedFun f) :
    TestFunctions.uniformNorm (periodize ℓ f) = TestFunctions.uniformNorm f := by
  obtain ⟨C, hC⟩ := hb
  have bddf : BddAbove (range fun x => ‖f x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have h0 : 0 ≤ TestFunctions.uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
  have hle : ∀ w, ‖periodize ℓ f w‖ ≤ TestFunctions.uniformNorm f := by
    intro w
    by_cases hw : w ∈ torusProj ℓ '' B
    · obtain ⟨x, hx, rfl⟩ := hw
      rw [periodize_torusProj_of_mem hℓ hB hf hx]
      exact le_ciSup bddf x
    · rw [periodize_eq_zero_of_not_mem hf hw, norm_zero]
      exact h0
  have bddT : BddAbove (range fun w => ‖periodize ℓ f w‖) :=
    ⟨_, by rintro _ ⟨w, rfl⟩; exact hle w⟩
  have h0' : 0 ≤ TestFunctions.uniformNorm (periodize ℓ f) :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  refine le_antisymm (Real.iSup_le hle h0) (Real.iSup_le (fun x => ?_) h0')
  by_cases hx : x ∈ B
  · rw [← periodize_torusProj_of_mem hℓ hB hf hx]
    exact le_ciSup bddT (torusProj ℓ x)
  · rw [hf x hx, norm_zero]
    exact h0'
theorem periodize_isLipschitzFor (hℓ : 0 < ℓ) (hB : HasDiameterLE B (ℓ / 2))
    {d : Torus4 ℓ → Torus4 ℓ → ℝ} (hnn : ∀ a b, 0 ≤ d a b) (hsymm : ∀ a b, d a b = d b a)
    (hd : ∀ x ∈ B, ∀ y ∈ B, d (torusProj ℓ x) (torusProj ℓ y) = euclidNormVec (x - y))
    (hlift : ∀ (x : Fin 4 → ℝ) (w : Torus4 ℓ),
      ∃ u, torusProj ℓ u = w ∧ euclidNormVec (x - u) = d (torusProj ℓ x) w)
    (hf : ∀ x, x ∉ B → f x = 0)
    (hL : TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f) :
    TestFunctions.IsLipschitzFor d (periodize ℓ f) := by
  obtain ⟨C, hC0, hC⟩ := hL
  have hlift' : ∀ w, periodize ℓ f w ≠ 0 → ∃ x ∈ B, torusProj ℓ x = w := by
    intro w hw
    by_contra hn
    exact hw (periodize_eq_zero_of_not_mem hf fun ⟨x, hx, e⟩ => hn ⟨x, hx, e⟩)
  have key : ∀ w w', periodize ℓ f w ≠ 0 → periodize ℓ f w' = 0 →
      ‖periodize ℓ f w - periodize ℓ f w'‖ ≤ C * d w w' := by
    intro w w' hw hw'
    obtain ⟨x, hx, rfl⟩ := hlift' w hw
    obtain ⟨u, rfl, hu⟩ := hlift x w'
    have hzero : f u = 0 := by
      by_cases hm : u ∈ B
      · rw [← periodize_torusProj_of_mem hℓ hB hf hm]
        exact hw'
      · exact hf u hm
    rw [hw', periodize_torusProj_of_mem hℓ hB hf hx, ← hu]
    have := hC x u
    rw [hzero] at this
    exact this
  refine ⟨C, hC0, fun w w' => ?_⟩
  by_cases hw : periodize ℓ f w = 0
  · by_cases hw' : periodize ℓ f w' = 0
    · rw [hw, hw', sub_zero, norm_zero]
      exact mul_nonneg hC0 (hnn _ _)
    · rw [norm_sub_rev, hsymm]
      exact key w' w hw' hw
  · by_cases hw' : periodize ℓ f w' = 0
    · exact key w w' hw hw'
    · obtain ⟨x, hx, rfl⟩ := hlift' w hw
      obtain ⟨y, hy, rfl⟩ := hlift' w' hw'
      rw [periodize_torusProj_of_mem hℓ hB hf hx, periodize_torusProj_of_mem hℓ hB hf hy,
        hd x hx y hy]
      exact hC x y
theorem abs_apply_le_euclidNormVec (u : Fin 4 → ℝ) (μ : Fin 4) : |u μ| ≤ euclidNormVec u := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem finite_latticeTranslates_near (hℓ : 0 < ℓ) (hB : HasDiameterLE B (ℓ / 2))
    (htri : ∀ a b c : Fin 4 → ℝ,
      euclidNormVec (a - c) ≤ euclidNormVec (a - b) + euclidNormVec (b - c))
    (hsym : ∀ a b : Fin 4 → ℝ, euclidNormVec (a - b) = euclidNormVec (b - a))
    (v : Fin 4 → ℝ) :
    {k : Fin 4 → ℤ | ∃ y, euclidNormVec (y - v) < 1 ∧ y + latticeTranslate ℓ k ∈ B}.Finite := by
  by_cases hne : {k : Fin 4 → ℤ | ∃ y, euclidNormVec (y - v) < 1 ∧
      y + latticeTranslate ℓ k ∈ B}.Nonempty
  · obtain ⟨k₀, y₀, hy₀, hz₀⟩ := hne
    let N : ℤ := ⌈1 / 2 + 2 / ℓ⌉
    refine (Set.finite_Icc (k₀ - fun _ => N) (k₀ + fun _ => N)).subset ?_
    rintro k ⟨y, hy, hz⟩
    have hμ : ∀ μ, |(k μ : ℝ) - (k₀ μ : ℝ)| ≤ 1 / 2 + 2 / ℓ := by
      intro μ
      have h1 := hB _ hz _ hz₀
      have h2 := htri (y + latticeTranslate ℓ k) (y₀ + latticeTranslate ℓ k₀)
        (y₀ + latticeTranslate ℓ k₀ + (y - y₀))
      have h3 : (y₀ + latticeTranslate ℓ k₀) - (y₀ + latticeTranslate ℓ k₀ + (y - y₀)) =
          y₀ - y := by
        abel
      have h4 := htri y₀ v y
      have h5 := hsym v y
      rw [h3] at h2
      have h6 := abs_apply_le_euclidNormVec
        ((y + latticeTranslate ℓ k) - (y₀ + latticeTranslate ℓ k₀ + (y - y₀))) μ
      have h7 : ((y + latticeTranslate ℓ k) - (y₀ + latticeTranslate ℓ k₀ + (y - y₀))) μ =
          ℓ * ((k μ : ℝ) - (k₀ μ : ℝ)) := by
        simp [latticeTranslate]
        ring
      rw [h7, abs_mul, abs_of_pos hℓ] at h6
      have h8 : ℓ * |(k μ : ℝ) - (k₀ μ : ℝ)| ≤ ℓ * (1 / 2 + 2 / ℓ) := by
        have : ℓ * (1 / 2 + 2 / ℓ) = ℓ / 2 + 2 := by
          field_simp
        rw [this]
        linarith
      exact le_of_mul_le_mul_left h8 hℓ
    have hN : 1 / 2 + 2 / ℓ ≤ (N : ℝ) := Int.le_ceil _
    constructor
    · intro μ
      have := (abs_le.mp (hμ μ)).1
      have h' : (k₀ μ : ℝ) - N ≤ k μ := by linarith
      simp only [Pi.sub_apply]
      exact_mod_cast h'
    · intro μ
      have := (abs_le.mp (hμ μ)).2
      have h' : (k μ : ℝ) ≤ k₀ μ + N := by linarith
      simp only [Pi.add_apply]
      exact_mod_cast h'
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty
theorem contDiff_periodicSum (hℓ : 0 < ℓ) (hB : HasDiameterLE B (ℓ / 2))
    (htri : ∀ a b c : Fin 4 → ℝ,
      euclidNormVec (a - c) ≤ euclidNormVec (a - b) + euclidNormVec (b - c))
    (hsym : ∀ a b : Fin 4 → ℝ, euclidNormVec (a - b) = euclidNormVec (b - a))
    (hf : ∀ x, x ∉ B → f x = 0) (hc : ContDiff ℝ 1 f) : ContDiff ℝ 1 (periodicSum ℓ f) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  have hfin := finite_latticeTranslates_near hℓ hB htri hsym v
  have hsum : ContDiff ℝ 1 fun u => ∑ k ∈ hfin.toFinset, f (u + latticeTranslate ℓ k) :=
    ContDiff.sum fun k _ => hc.comp (contDiff_id.add contDiff_const)
  refine hsum.contDiffAt.congr_of_eventuallyEq ?_
  have hcont : Continuous fun u : Fin 4 → ℝ => euclidNormVec (u - v) := by
    unfold euclidNormVec
    fun_prop
  have hv : euclidNormVec (v - v) < 1 := by
    simp [euclidNormVec]
  have hnear : ∀ᶠ u in 𝓝 v, euclidNormVec (u - v) < 1 :=
    hcont.continuousAt.eventually (gt_mem_nhds hv)
  filter_upwards [hnear] with u hu
  unfold periodicSum
  refine tsum_eq_sum fun k hk => hf _ fun hm => hk ?_
  exact hfin.mem_toFinset.mpr ⟨u, hu, hm⟩
theorem isCompactWrt_image {X Y : Type*} {d : X → X → ℝ} {d' : Y → Y → ℝ} {φ : X → Y}
    (hφ : MetricNotions.IsContinuousWrt d d' φ) {Z : Set X}
    (hZ : MetricNotions.IsCompactWrt d Z) : MetricNotions.IsCompactWrt d' (φ '' Z) := by
  classical
  intro 𝒰 hU hcov
  have hopen : ∀ U ∈ 𝒰, MetricNotions.IsOpenWrt d (φ ⁻¹' U) := by
    intro U hm x hx
    obtain ⟨r, hr, h⟩ := hU U hm (φ x) hx
    obtain ⟨δ, hδ, h'⟩ := hφ x r hr
    exact ⟨δ, hδ, fun y hy => h _ (h' y hy)⟩
  obtain ⟨𝒱, h𝒱, hfin, hcov'⟩ := hZ ((fun U => φ ⁻¹' U) '' 𝒰)
    (by rintro _ ⟨U, hm, rfl⟩; exact hopen U hm)
    (by
      intro x hx
      obtain ⟨U, hm, hxU⟩ := hcov ⟨x, hx, rfl⟩
      exact ⟨_, ⟨U, hm, rfl⟩, hxU⟩)
  choose! G hG using fun V (hV : V ∈ 𝒱) => h𝒱 hV
  refine ⟨G '' 𝒱, ?_, hfin.image G, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact (hG V hV).1
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨V, hV, hxV⟩ := hcov' hx
    refine ⟨G V, ⟨V, hV, rfl⟩, ?_⟩
    have e := (hG V hV).2
    rw [← e] at hxV
    exact hxV
theorem isCompactWrt_singleton {X : Type*} {d : X → X → ℝ} (w : X) :
    MetricNotions.IsCompactWrt d {w} := by
  intro 𝒰 _ hc
  obtain ⟨U, hU, hw⟩ := hc (mem_singleton w)
  exact ⟨{U}, singleton_subset_iff.mpr hU, finite_singleton U,
    singleton_subset_iff.mpr ⟨U, mem_singleton U, hw⟩⟩
open ReflectionPositivity.CutoffMirrors Ambient
theorem torusSide_pos (D : MirrorData) : 0 < PeriodicLattice.torusSide D.L D.m := by
  have h := D.isAdmissible.2
  unfold PeriodicLattice.torusSide
  positivity
theorem torusProj_zero : torusProj ℓ 0 = 0 := by
  funext μ
  simp [torusProj]
section MetricFacts
variable (hS : AmbientMetric.Claim)
include hS
theorem euclidNormVec_sub_triangle (s : Conventions.StandingParameters) (a b c : Fin 4 → ℝ) :
    euclidNormVec (a - c) ≤ euclidNormVec (a - b) + euclidNormVec (b - c) :=
  (hS s .euclidean).1.2.1.triangle a b c
theorem euclidNormVec_sub_comm (s : Conventions.StandingParameters) (a b : Fin 4 → ℝ) :
    euclidNormVec (a - b) = euclidNormVec (b - a) :=
  (hS s .euclidean).1.2.1.symm a b
theorem torusDist_torusProj (D : MirrorData)
    (hB : HasDiameterLE B (PeriodicLattice.torusSide D.L D.m / 2))
    {x y : Fin 4 → ℝ} (hx : x ∈ B) (hy : y ∈ B) :
    D.torusDist (torusProj (PeriodicLattice.torusSide D.L D.m) x)
        (torusProj (PeriodicLattice.torusSide D.L D.m) y) =
      euclidNormVec (x - y) := by
  have hl := (hS D.toStandingParameters .periodic).1.1 x y
  have hmin : IsLeast ((fun γ => euclidNormVec (x - y - γ)) ''
      (Ambient.periodic.periodGroup D.toStandingParameters : Set (Fin 4 → ℝ)))
      (D.torusDist (torusProj (PeriodicLattice.torusSide D.L D.m) x)
        (torusProj (PeriodicLattice.torusSide D.L D.m) y)) := hl.1
  have hle : D.torusDist (torusProj (PeriodicLattice.torusSide D.L D.m) x)
      (torusProj (PeriodicLattice.torusSide D.L D.m) y) ≤ euclidNormVec (x - y) := hl.2
  obtain ⟨⟨γ, hγ, e⟩, -⟩ := hmin
  have h0 : torusProj (PeriodicLattice.torusSide D.L D.m) γ =
      torusProj (PeriodicLattice.torusSide D.L D.m) 0 := by
    rw [torusProj_zero]
    exact (Ambient.periodic.mem_periodGroup_iff D.toStandingParameters γ).mp hγ
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq h0
  rw [zero_add] at hk
  refine le_antisymm hle ?_
  rw [← e]
  by_cases hk0 : k = 0
  · simp [hk, hk0, latticeTranslate_zero]
  · have h1 := le_euclidNormVec_latticeTranslate (ℓ := PeriodicLattice.torusSide D.L D.m) hk0
    have h2 := hB x hx y hy
    have h3 := euclidNormVec_sub_triangle hS D.toStandingParameters
      (latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) (x - y) 0
    have h4 := euclidNormVec_sub_comm hS D.toStandingParameters
      (latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) (x - y)
    rw [sub_zero, sub_zero] at h3
    show euclidNormVec (x - y) ≤ euclidNormVec (x - y - γ)
    rw [hk]
    linarith
theorem exists_lift_realizing (D : MirrorData) (x : Fin 4 → ℝ)
    (w : Torus4 (PeriodicLattice.torusSide D.L D.m)) :
    ∃ u, torusProj (PeriodicLattice.torusSide D.L D.m) u = w ∧
      euclidNormVec (x - u) = D.torusDist (torusProj (PeriodicLattice.torusSide D.L D.m) x) w :=
  (hS D.toStandingParameters .periodic).1.2.2.2.1
    (torusProj (PeriodicLattice.torusSide D.L D.m) x) w x rfl
theorem eq_zero_of_not_mem_of_support_subset (s : Conventions.StandingParameters)
    {A : Set (Fin 4 → ℝ)}
    (hA : Ambient.euclidean.closedSupport s f ⊆ A) : ∀ x, x ∉ A → f x = 0 := by
  intro x hx
  by_contra h
  have hx' : x ∈ MetricNotions.closureWrt (Ambient.euclidean.pointDist s) {y | f y ≠ 0} :=
    fun r hr => ⟨x, h, by
      rw [((hS s .euclidean).1.2.1.eq_zero_iff x x).mpr rfl]
      exact hr⟩
  exact hx (hA hx')
theorem supp_periodize (s : Conventions.StandingParameters) (D : MirrorData)
    (hB : HasDiameterLE B (PeriodicLattice.torusSide D.L D.m / 2))
    (hcomp : Ambient.euclidean.IsCompactSubset s (Ambient.euclidean.closedSupport s f))
    (hsub : Ambient.euclidean.closedSupport s f ⊆ B) :
    D.supp (periodize (PeriodicLattice.torusSide D.L D.m) f) =
      torusProj (PeriodicLattice.torusSide D.L D.m) '' Ambient.euclidean.closedSupport s f := by
  have hℓ := torusSide_pos D
  have hB' : HasDiameterLE (Ambient.euclidean.closedSupport s f)
      (PeriodicLattice.torusSide D.L D.m / 2) :=
    fun x hx y hy => hB x (hsub hx) y (hsub hy)
  have hoff := eq_zero_of_not_mem_of_support_subset hS (f := f) s (subset_refl _)
  have htop := hS D.toStandingParameters .periodic
  have hcont : MetricNotions.IsContinuousWrt (Ambient.euclidean.pointDist s)
      (Ambient.periodic.pointDist D.toStandingParameters)
      (torusProj (PeriodicLattice.torusSide D.L D.m)) :=
    htop.1.2.2.2.2
  apply Subset.antisymm
  · intro w hw
    by_contra hn
    have hw' : ∀ r : ℝ, 0 < r → ∃ y, periodize (PeriodicLattice.torusSide D.L D.m) f y ≠ 0 ∧
        D.torusDist w y < r := hw
    have hpos := htop.2.1.1
      (torusProj (PeriodicLattice.torusSide D.L D.m) '' Ambient.euclidean.closedSupport s f) {w}
      (isCompactWrt_image hcont hcomp) (isCompactWrt_singleton w)
      (Set.disjoint_singleton_right.mpr hn)
    obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
    have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
    obtain ⟨y, hy, hwy⟩ := hw' r hr0'
    have hyS : y ∈ torusProj (PeriodicLattice.torusSide D.L D.m) ''
        Ambient.euclidean.closedSupport s f := by
      by_contra hny
      exact hy (periodize_eq_zero_of_not_mem hoff hny)
    have hle : Ambient.periodic.infSetDist D.toStandingParameters
        (torusProj (PeriodicLattice.torusSide D.L D.m) '' Ambient.euclidean.closedSupport s f)
          {w} ≤
        ENNReal.ofReal (Ambient.periodic.pointDist D.toStandingParameters y w) :=
      iInf₂_le_of_le y hyS (iInf₂_le_of_le w rfl le_rfl)
    have hsymm : Ambient.periodic.pointDist D.toStandingParameters y w = D.torusDist w y :=
      htop.1.2.1.symm y w
    rw [hsymm] at hle
    have h2 : ENNReal.ofReal (D.torusDist w y) ≤ r :=
      (ENNReal.ofReal_le_ofReal hwy.le).trans_eq ENNReal.ofReal_coe_nnreal
    exact lt_irrefl _ (hr.trans_le (hle.trans h2))
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : ∀ r : ℝ, 0 < r → ∃ y, f y ≠ 0 ∧ Ambient.euclidean.pointDist s x y < r := hx
    intro r hr
    obtain ⟨y, hy, hxy⟩ := hx' r hr
    have hyS : y ∈ Ambient.euclidean.closedSupport s f := by
      by_contra hny
      exact hy (hoff y hny)
    refine ⟨torusProj (PeriodicLattice.torusSide D.L D.m) y, ?_, ?_⟩
    · show periodize (PeriodicLattice.torusSide D.L D.m) f
          (torusProj (PeriodicLattice.torusSide D.L D.m) y) ≠ 0
      rw [periodize_torusProj_of_mem hℓ hB' hoff hyS]
      exact hy
    · exact lt_of_le_of_lt ((htop.1.1 x y).2) hxy
end MetricFacts
end PeriodizeOnSmallSets
open PeriodizeOnSmallSets Ambient ReflectionPositivity.CutoffMirrors
theorem periodizedFormsBounded_holds
    (hLat : torusFormsBounded)
    (hS : AmbientMetric.Claim)
    (hP : Ambient.testSpacesAndSepTuples) :
    periodizedFormsBounded := by
  intro q hq s D W _ hWc hWd hlarge
  have hℓ := torusSide_pos D
  have hB : HasDiameterLE (⋃ l, W l) (PeriodicLattice.torusSide D.L D.m / 2) := hlarge
  have hBl : ∀ l, HasDiameterLE (W l) (PeriodicLattice.torusSide D.L D.m / 2) :=
    fun l x hx y hy => hB x (mem_iUnion.mpr ⟨l, hx⟩) y (mem_iUnion.mpr ⟨l, hy⟩)
  have htop := hS D.toStandingParameters .periodic
  have hcont : MetricNotions.IsContinuousWrt (Ambient.euclidean.pointDist s)
      (Ambient.periodic.pointDist D.toStandingParameters)
      (torusProj (PeriodicLattice.torusSide D.L D.m)) :=
    htop.1.2.2.2.2
  have hlipT : ∀ f ∈ Ambient.euclidean.lipWithin s (⋃ l, W l),
      TestFunctions.IsLipschitzFor D.torusDist
          (periodize (PeriodicLattice.torusSide D.L D.m) f) ∧
        TestFunctions.uniformNorm (periodize (PeriodicLattice.torusSide D.L D.m) f) =
          TestFunctions.uniformNorm f := by
    intro f hf
    have hoff := eq_zero_of_not_mem_of_support_subset hS (f := f) s hf.2.2
    have hbd := ((hP s .euclidean ⟨1, Set.mem_Ici.mpr le_rfl⟩ (⋃ l, W l) univ 1 le_rfl).1.2.1
      f hf).2
    exact ⟨periodize_isLipschitzFor hℓ hB (d := D.torusDist) htop.1.2.1.nonneg htop.1.2.1.symm
      (fun x hx y hy => torusDist_torusProj hS D hB hx hy) (exists_lift_realizing hS D) hoff
      hf.1,
      uniformNorm_periodize hℓ hB hoff hbd⟩
  have hc1 : ∀ l, ∀ f ∈ Ambient.euclidean.c1Within s (W l),
      periodize (PeriodicLattice.torusSide D.L D.m) f ∈
        Ambient.periodic.c1Within D.toStandingParameters
          (torusProj (PeriodicLattice.torusSide D.L D.m) '' W l) := by
    intro l f hf
    have hsupp := supp_periodize hS s D (hBl l) hf.2.1 hf.2.2
    have hoff := eq_zero_of_not_mem_of_support_subset hS (f := f) s hf.2.2
    have hsupp' : Ambient.periodic.closedSupport D.toStandingParameters
        (periodize (PeriodicLattice.torusSide D.L D.m) f) =
        torusProj (PeriodicLattice.torusSide D.L D.m) '' Ambient.euclidean.closedSupport s f :=
      hsupp
    have hcomp : Ambient.periodic.IsCompactSubset D.toStandingParameters
        (Ambient.periodic.closedSupport D.toStandingParameters
          (periodize (PeriodicLattice.torusSide D.L D.m) f)) := by
      rw [hsupp']
      exact isCompactWrt_image hcont hf.2.1
    have hC1 : Ambient.periodic.IsC1 D.toStandingParameters
        (periodize (PeriodicLattice.torusSide D.L D.m) f) := by
      have e : periodize (PeriodicLattice.torusSide D.L D.m) f ∘
            torusProj (PeriodicLattice.torusSide D.L D.m) =
          periodicSum (PeriodicLattice.torusSide D.L D.m) f :=
        funext (TestFunctions.periodize_torusProj _ f)
      have hcd : ContDiff ℝ 1
          (periodize (PeriodicLattice.torusSide D.L D.m) f ∘
            torusProj (PeriodicLattice.torusSide D.L D.m)) := by
        rw [e]
        exact contDiff_periodicSum hℓ (hBl l) (euclidNormVec_sub_triangle hS s)
          (euclidNormVec_sub_comm hS s) hoff hf.1.1
      exact hcd
    refine ⟨⟨hC1, hcomp⟩, hcomp, ?_⟩
    rw [hsupp']
    exact image_mono hf.2.2
  have hdis : ∀ h : Ambient.euclidean.C1ProductSpace s W, MirrorData.PairwiseDisjointSupp (D := D)
      fun l => periodize (PeriodicLattice.torusSide D.L D.m) (h l).1 := by
    intro h l l' hll
    show D.supp (periodize (PeriodicLattice.torusSide D.L D.m) (h l).1) ∩
      D.supp (periodize (PeriodicLattice.torusSide D.L D.m) (h l').1) = ∅
    rw [supp_periodize hS s D (hBl l) (h l).2.2.1 (h l).2.2.2,
      supp_periodize hS s D (hBl l') (h l').2.2.1 (h l').2.2.2]
    apply eq_empty_of_forall_notMem
    rintro w ⟨⟨x, hx, rfl⟩, ⟨y, hy, e⟩⟩
    have hxW := (h l).2.2.2 hx
    have hyW := (h l').2.2.2 hy
    have hxy : y = x :=
      torusProj_injOn hℓ hB (mem_iUnion.mpr ⟨l', hyW⟩) (mem_iUnion.mpr ⟨l, hxW⟩) e
    subst hxy
    exact Set.disjoint_left.mp (show Disjoint (W l) (W l') from hWd hll) hxW hyW
  have hmemL : ∀ (h : Ambient.euclidean.C1ProductSpace s W) (l : Fin q),
      (h l).1 ∈ Ambient.euclidean.lipWithin s (⋃ l, W l) := by
    intro h l
    have hl := (hP s .euclidean ⟨1, Set.mem_Ici.mpr le_rfl⟩ (W l) univ 1 le_rfl).1.2.2.2.1
      (h l).2
    exact ⟨hl.1, hl.2.1, hl.2.2.trans (subset_iUnion W l)⟩
  have hoffP : ∀ (h : Ambient.euclidean.C1ProductSpace s W) (l : Fin q) (x : Fin 4 → ℝ),
      x ∉ W l → (h l).1 x = 0 :=
    fun h l => eq_zero_of_not_mem_of_support_subset hS s (h l).2.2.2
  refine ⟨fun f hf => hlipT f hf, ?_, hdis, ?_⟩
  · intro f hf f' hf' a b
    exact periodize_linear_comb hℓ hB (eq_zero_of_not_mem_of_support_subset hS s hf.2.2)
      (eq_zero_of_not_mem_of_support_subset hS s hf'.2.2) a b
  · let W' : Fin q → Set (Ambient.periodic.Carrier D.toStandingParameters) :=
      fun l => torusProj (PeriodicLattice.torusSide D.L D.m) '' W l
    have hW'c : ∀ l, Ambient.periodic.IsCompactSubset D.toStandingParameters (W' l) :=
      fun l => isCompactWrt_image hcont (hWc l)
    have hW'd : Pairwise (Function.onFun Disjoint W') := by
      intro l l' hll
      refine Set.disjoint_left.mpr ?_
      rintro w ⟨x, hx, rfl⟩ ⟨y, hy, e⟩
      have hxy : y = x :=
        torusProj_injOn hℓ hB (mem_iUnion.mpr ⟨l', hy⟩) (mem_iUnion.mpr ⟨l, hx⟩) e
      subst hxy
      exact Set.disjoint_left.mp (show Disjoint (W l) (W l') from hWd hll) hx hy
    have R := (hLat q hq).2 D W' hW'c hW'd
    let tp : Ambient.euclidean.C1ProductSpace s W →
        Ambient.periodic.C1ProductSpace D.toStandingParameters W' :=
      fun h l => ⟨periodize (PeriodicLattice.torusSide D.L D.m) (h l).1, hc1 l _ (h l).2⟩
    have et : ∀ h, periodizedForm D h = torusForm D (tp h) := fun _ => rfl
    refine ⟨fun h => ?_, ?_, fun h => ?_⟩
    · rw [et]
      exact R.1 (tp h)
    · intro i a b X Y Z hY hZ hi
      show (periodizedForm D Z).re =
        a * (periodizedForm D X).re + b * (periodizedForm D Y).re
      rw [et, et, et]
      refine R.2.1 i a b (tp X) (tp Y) (tp Z)
        (fun l hl => congrArg (periodize (PeriodicLattice.torusSide D.L D.m)) (hY l hl))
        (fun l hl => congrArg (periodize (PeriodicLattice.torusSide D.L D.m)) (hZ l hl)) ?_
      show periodize (PeriodicLattice.torusSide D.L D.m) (Z i).1 =
        a • periodize (PeriodicLattice.torusSide D.L D.m) (X i).1 +
          b • periodize (PeriodicLattice.torusSide D.L D.m) (Y i).1
      rw [hi]
      exact periodize_linear_comb hℓ (hBl i) (hoffP X i) (hoffP Y i) a b
    · have hb := ((hLat q hq).1 D
        (fun l => periodize (PeriodicLattice.torusSide D.L D.m) (h l).1)
        ⟨fun l => (hlipT _ (hmemL h l)).1, hdis h⟩).1
      refine hb.trans (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun l _ => ?_) (fun l _ => ?_)) (by positivity))
      · exact Real.iSup_nonneg fun _ => norm_nonneg _
      · rw [(hlipT _ (hmemL h l)).2]
        exact le_max_left _ _
end LimitSpaces
end YangMills.Construction
end
