import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Towers.IntegralOfTheThirdPowersOfTheFreeSymbolsProof
import YangMills.Construction.FormsOnATorus.KernelOfTheLatticeSymbolProof
import YangMills.Construction.ResponseInTheExpansion.SumOverMomentaOfTheCurlCurl
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Filter Topology
namespace YangMills.Construction.ResponseInTheExpansion
namespace LowSymbolKernel
private abbrev Mom := Fin 4 → ℝ
section Calculus
variable {ι : Type*} {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
private structure RegDomain (U : ι → Set Mom) : Prop where
  isOpen : ∀ i, IsOpen (U i)
  norm_pos : ∀ i, ∀ p ∈ U i, 0 < ‖p‖
  norm_le : ∀ i, ∀ p ∈ U i, ‖p‖ ≤ 4
private def DerivBound (U : ι → Set Mom) (a : ℤ) (f : ι → Mom → F) (r : ℕ) : Prop :=
  ∃ K : ℝ, ∀ i, ∀ p ∈ U i, ‖iteratedFDeriv ℝ r (f i) p‖ ≤ K * ‖p‖ ^ (a - r)
private structure HasOrder (U : ι → Set Mom) (a : ℤ) (f : ι → Mom → F) : Prop where
  smooth : ∀ i, ContDiffOn ℝ ∞ (f i) (U i)
  bound : ∀ r, DerivBound U a f r
private lemma DerivBound.bilinear {U : ι → Set Mom} (hU : RegDomain U) (B : F →L[ℝ] G →L[ℝ] H) {f : ι → Mom → F} {g : ι → Mom → G}
    {a a' : ℤ} {r : ℕ} (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i)) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (bf : ∀ s ≤ r, DerivBound U a f s) (bg : ∀ s ≤ r, DerivBound U a' g s) :
    DerivBound U (a + a') (fun i p => B (f i p) (g i p)) r := by
  have bf' : ∀ s, ∃ K : ℝ, s ≤ r → ∀ i, ∀ p ∈ U i, ‖iteratedFDeriv ℝ s (f i) p‖ ≤ K * ‖p‖ ^ (a - s) := by
    intro s
    by_cases h : s ≤ r
    · obtain ⟨K, hK⟩ := bf s h
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  have bg' : ∀ s, ∃ K : ℝ, s ≤ r → ∀ i, ∀ p ∈ U i, ‖iteratedFDeriv ℝ s (g i) p‖ ≤ K * ‖p‖ ^ (a' - s) := by
    intro s
    by_cases h : s ≤ r
    · obtain ⟨K, hK⟩ := bg s h
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Kf hKf using bf'
  choose Kg hKg using bg'
  refine ⟨‖B‖ * ∑ s ∈ Finset.range (r + 1), (r.choose s : ℝ) * Kf s * Kg (r - s), fun i p hp => ?_⟩
  have key := B.norm_iteratedFDerivWithin_le_of_bilinear (hf i) (hg i) (hU.isOpen i).uniqueDiffOn hp
    (n := r) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen r (hU.isOpen i) hp] at key
  refine key.trans ?_
  have hw : ‖p‖ ≠ 0 := (hU.norm_pos i p hp).ne'
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s hs => ?_) (ContinuousLinearMap.opNorm_nonneg B)
  have hs' : s ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [iteratedFDerivWithin_of_isOpen s (hU.isOpen i) hp, iteratedFDerivWithin_of_isOpen (r - s) (hU.isOpen i) hp]
  have h1 := hKf s hs' i p hp
  have h2 := hKg (r - s) (Nat.sub_le _ _) i p hp
  have h3 : ‖p‖ ^ (a + a' - r) = ‖p‖ ^ (a - s) * ‖p‖ ^ (a' - ((r - s : ℕ) : ℤ)) := by
    rw [← zpow_add₀ hw]
    congr 1
    push_cast [Nat.cast_sub hs']
    ring
  rw [h3]
  calc (r.choose s : ℝ) * ‖iteratedFDeriv ℝ s (f i) p‖ * ‖iteratedFDeriv ℝ (r - s) (g i) p‖
      ≤ (r.choose s : ℝ) * (Kf s * ‖p‖ ^ (a - s)) * (Kg (r - s) * ‖p‖ ^ (a' - ((r - s : ℕ) : ℤ))) := by
        have h0 : 0 ≤ Kf s * ‖p‖ ^ (a - s) := (norm_nonneg _).trans h1
        gcongr
    _ = _ := by ring
private lemma HasOrder.bilinear {U : ι → Set Mom} (hU : RegDomain U) (B : F →L[ℝ] G →L[ℝ] H) {f : ι → Mom → F} {g : ι → Mom → G}
    {a a' : ℤ} (hf : HasOrder U a f) (hg : HasOrder U a' g) : HasOrder U (a + a') (fun i p => B (f i p) (g i p)) :=
  ⟨fun i => (B.isBoundedBilinearMap.contDiff (n := ∞)).comp_contDiffOn ((hf.smooth i).prodMk (hg.smooth i)),
    fun _ => DerivBound.bilinear hU B hf.smooth hg.smooth (fun s _ => hf.bound s) (fun s _ => hg.bound s)⟩
private lemma HasOrder.add {U : ι → Set Mom} (hU : RegDomain U) {f g : ι → Mom → F} {a : ℤ} (hf : HasOrder U a f) (hg : HasOrder U a g) :
    HasOrder U a (fun i p => f i p + g i p) := by
  refine ⟨fun i => (hf.smooth i).add (hg.smooth i), fun r => ?_⟩
  obtain ⟨K, hK⟩ := hf.bound r
  obtain ⟨K', hK'⟩ := hg.bound r
  refine ⟨K + K', fun i p hp => ?_⟩
  have h1 : ContDiffAt ℝ r (f i) p :=
    ((hf.smooth i).contDiffAt ((hU.isOpen i).mem_nhds hp)).of_le (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℝ r (g i) p :=
    ((hg.smooth i).contDiffAt ((hU.isOpen i).mem_nhds hp)).of_le (by exact_mod_cast le_top)
  have : iteratedFDeriv ℝ r (fun p => f i p + g i p) p =
      iteratedFDeriv ℝ r (f i) p + iteratedFDeriv ℝ r (g i) p := by
    have := iteratedFDeriv_add_apply (x := p) h1 h2
    exact this
  rw [this, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hK i p hp) (hK' i p hp))
private lemma HasOrder.const (U : ι → Set Mom) (hU : RegDomain U) (c : F) : HasOrder U 0 (fun _ _ => c) := by
  refine ⟨fun i => contDiffOn_const, fun r => ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨‖c‖, fun i p hp => by simp⟩
  · refine ⟨0, fun i p hp => ?_⟩
    simp [iteratedFDeriv_const_of_ne hr.ne']
private lemma HasOrder.clm_comp {U : ι → Set Mom} (hU : RegDomain U) (L : F →L[ℝ] G) {f : ι → Mom → F} {a : ℤ} (hf : HasOrder U a f) :
    HasOrder U a (fun i p => L (f i p)) := by
  refine ⟨fun i => L.contDiff.comp_contDiffOn (hf.smooth i), fun r => ?_⟩
  obtain ⟨K, hK⟩ := hf.bound r
  refine ⟨‖L‖ * K, fun i p hp => ?_⟩
  have h1 : ContDiffAt ℝ r (f i) p :=
    ((hf.smooth i).contDiffAt ((hU.isOpen i).mem_nhds hp)).of_le (by exact_mod_cast le_top)
  have : iteratedFDeriv ℝ r (fun p => L (f i p)) p =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ r (f i) p) := L.iteratedFDeriv_comp_left h1 (le_refl _)
  rw [this, mul_assoc]
  refine (L.norm_compContinuousMultilinearMap_le _).trans ?_
  exact mul_le_mul_of_nonneg_left (hK i p hp) (norm_nonneg _)
private lemma HasOrder.neg {U : ι → Set Mom} (hU : RegDomain U) {f : ι → Mom → F} {a : ℤ} (hf : HasOrder U a f) :
    HasOrder U a (fun i p => - f i p) :=
  by simpa using hf.clm_comp hU (-(ContinuousLinearMap.id ℝ F))
private lemma HasOrder.sub {U : ι → Set Mom} (hU : RegDomain U) {f g : ι → Mom → F} {a : ℤ} (hf : HasOrder U a f) (hg : HasOrder U a g) :
    HasOrder U a (fun i p => f i p - g i p) := by
  simpa [sub_eq_add_neg] using hf.add hU (hg.neg hU)
private lemma HasOrder.of_le {U : ι → Set Mom} (hU : RegDomain U) {f : ι → Mom → F} {a a' : ℤ} (h : a' ≤ a) (hf : HasOrder U a f) :
    HasOrder U a' f := by
  refine ⟨hf.smooth, fun r => ?_⟩
  obtain ⟨K, hK⟩ := hf.bound r
  refine ⟨|K| * 4 ^ (a - a'), fun i p hp => ?_⟩
  have hw := hU.norm_pos i p hp
  refine (hK i p hp).trans ?_
  have e : ‖p‖ ^ (a - r) = ‖p‖ ^ (a' - r) * ‖p‖ ^ (a - a') := by
    rw [← zpow_add₀ hw.ne']; congr 1; ring
  have h2 : ‖p‖ ^ (a - a') ≤ (4 : ℝ) ^ (a - a') :=
    zpow_le_zpow_left₀ (by omega) hw.le (hU.norm_le i p hp)
  have h3 : 0 ≤ ‖p‖ ^ (a' - r) := by positivity
  rw [e]
  calc K * (‖p‖ ^ (a' - r) * ‖p‖ ^ (a - a')) ≤ |K| * (‖p‖ ^ (a' - r) * (4 : ℝ) ^ (a - a')) := by
        refine mul_le_mul (le_abs_self K) ?_ (by positivity) (abs_nonneg K)
        exact mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by ring
private lemma HasOrder.finsetSum {U : ι → Set Mom} (hU : RegDomain U) {J : Type*} (s : Finset J) {f : J → ι → Mom → F} {a : ℤ}
    (hf : ∀ j ∈ s, HasOrder U a (f j)) : HasOrder U a (fun i p => ∑ j ∈ s, f j i p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun i => by simpa using contDiffOn_const, fun r => ⟨0, fun i p hp => ?_⟩⟩
    have : (fun p : Mom => ∑ j ∈ (∅ : Finset J), f j i p) = fun _ => (0 : F) := by simp
    show ‖iteratedFDeriv ℝ r (fun p : Mom => ∑ j ∈ (∅ : Finset J), f j i p) p‖ ≤ _
    rw [this]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · simp [iteratedFDeriv_const_of_ne hr.ne']
  | insert j s hj ih =>
    have h1 := hf j (Finset.mem_insert_self _ _)
    have h2 := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa [Finset.sum_insert hj] using h1.add hU h2
private lemma HasOrder.deriv_family {U : ι → Set Mom} (hU : RegDomain U) {f : ι → Mom → F} {a : ℤ} (hf : HasOrder U a f) :
    HasOrder U (a - 1) (fun i => fderiv ℝ (f i)) := by
  refine ⟨fun i => ?_, fun r => ?_⟩
  · have := (hf.smooth i).fderiv_of_isOpen (m := ∞) (hU.isOpen i) (by simp)
    exact this
  · obtain ⟨K, hK⟩ := hf.bound (r + 1)
    refine ⟨K, fun i p hp => ?_⟩
    rw [norm_iteratedFDeriv_fderiv]
    refine (hK i p hp).trans_eq ?_
    congr 2
    push_cast; ring
private lemma HasOrder.ringInverse {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {U : ι → Set Mom} (hU : RegDomain U)
    {f : ι → Mom → A} {a : ℤ} (hf : HasOrder U a f) (hu : ∀ i, ∀ p ∈ U i, IsUnit (f i p)) {K : ℝ}
    (hK : ∀ i, ∀ p ∈ U i, ‖Ring.inverse (f i p)‖ ≤ K * ‖p‖ ^ (-a)) :
    HasOrder U (-a) (fun i p => Ring.inverse (f i p)) := by
  set g : ι → Mom → A := fun i p => Ring.inverse (f i p) with hg
  have hsm : ∀ i, ContDiffOn ℝ ∞ (g i) (U i) := by
    intro i p hp
    obtain ⟨u, hu'⟩ := hu i p hp
    have h1 : ContDiffAt ℝ ∞ (f i) p := (hf.smooth i).contDiffAt ((hU.isOpen i).mem_nhds hp)
    have h2 : ContDiffAt ℝ ∞ Ring.inverse (f i p) := by
      rw [← hu']; exact contDiffAt_ringInverse ℝ u
    exact (h2.comp p h1).contDiffWithinAt
  let B₁ : A →L[ℝ] (Mom →L[ℝ] A) →L[ℝ] (Mom →L[ℝ] A) :=
    -((ContinuousLinearMap.compL ℝ Mom A A).comp (ContinuousLinearMap.mul ℝ A))
  let B₂ : (Mom →L[ℝ] A) →L[ℝ] A →L[ℝ] (Mom →L[ℝ] A) :=
    ((ContinuousLinearMap.compL ℝ Mom A A).comp (ContinuousLinearMap.mul ℝ A).flip).flip
  have hd : ∀ i, ∀ p ∈ U i, fderiv ℝ (g i) p = B₁ (g i p) (B₂ (fderiv ℝ (f i) p) (g i p)) := by
    intro i p hp
    obtain ⟨u, hu'⟩ := hu i p hp
    have h1 : HasFDerivAt (f i) (fderiv ℝ (f i) p) p :=
      (((hf.smooth i).contDiffAt ((hU.isOpen i).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
    have h2 : HasFDerivAt Ring.inverse (-((ContinuousLinearMap.mulLeftRight ℝ A) ↑u⁻¹) ↑u⁻¹) (f i p) := by
      rw [← hu']; exact hasFDerivAt_ringInverse u
    have h3 := (h2.comp p h1).fderiv
    have h4 : g i p = ↑u⁻¹ := by
      simp only [hg]; rw [← hu']; exact Ring.inverse_unit u
    have h5 : g i = Ring.inverse ∘ f i := rfl
    rw [h5, h3, ← h5, h4]
    ext1 v
    simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.mulLeftRight_apply]
    simp [B₁, B₂, mul_assoc]
    try rfl
  have main : ∀ n : ℕ, ∀ r ≤ n, DerivBound U (-a) g r := by
    intro n
    induction n with
    | zero =>
      intro r hr
      obtain rfl : r = 0 := by omega
      exact ⟨K, fun i p hp => by simpa using hK i p hp⟩
    | succ n ih =>
      intro r hr
      rcases Nat.lt_or_ge r (n + 1) with h | h
      · exact ih r (by omega)
      obtain rfl : r = n + 1 := by omega
      have hDf := hf.deriv_family hU
      have hmid_s : ∀ i, ContDiffOn ℝ ∞ (fun p => B₂ (fderiv ℝ (f i) p) (g i p)) (U i) := fun i =>
        (B₂.isBoundedBilinearMap.contDiff (n := ∞)).comp_contDiffOn ((hDf.smooth i).prodMk (hsm i))
      have hmid : ∀ s ≤ n, DerivBound U (a - 1 + -a) (fun i p => B₂ (fderiv ℝ (f i) p) (g i p)) s := fun s hs =>
        DerivBound.bilinear hU B₂ hDf.smooth hsm (fun s' _ => hDf.bound s') (fun s' hs' => ih s' (by omega))
      obtain ⟨K', hK'⟩ := DerivBound.bilinear hU B₁ hsm hmid_s ih hmid
      refine ⟨K', fun i p hp => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv]
      have hev : _root_.fderiv ℝ (g i) =ᶠ[nhds p] fun p => B₁ (g i p) (B₂ (fderiv ℝ (f i) p) (g i p)) :=
        Filter.eventually_of_mem ((hU.isOpen i).mem_nhds hp) (hd i)
      rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
      refine (hK' i p hp).trans_eq ?_
      congr 2
      push_cast; ring
  exact ⟨hsm, fun r => main r r le_rfl⟩
private lemma HasOrder.of_bounded {U : ι → Set Mom} (hU : RegDomain U) {f : ι → Mom → F} (hs : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hb : ∀ r : ℕ, ∃ K : ℝ, ∀ i, ∀ p ∈ U i, ‖iteratedFDeriv ℝ r (f i) p‖ ≤ K) {a : ℤ}
    (hl : ∀ r : ℕ, (r : ℤ) < a → DerivBound U a f r) : HasOrder U a f := by
  refine ⟨hs, fun r => ?_⟩
  by_cases h : (r : ℤ) < a
  · exact hl r h
  obtain ⟨K, hK⟩ := hb r
  refine ⟨|K| * 4 ^ ((r : ℤ) - a), fun i p hp => ?_⟩
  have hw := hU.norm_pos i p hp
  have h1 : ‖p‖ ^ ((r : ℤ) - a) ≤ (4 : ℝ) ^ ((r : ℤ) - a) :=
    zpow_le_zpow_left₀ (by omega) hw.le (hU.norm_le i p hp)
  have h2 : (1 : ℝ) ≤ (4 : ℝ) ^ ((r : ℤ) - a) * ‖p‖ ^ (a - r) := by
    have h3 : ‖p‖ ^ (a - r) * ‖p‖ ^ ((r : ℤ) - a) = 1 := by
      rw [← zpow_add₀ hw.ne']; simp
    have h4 : 0 ≤ ‖p‖ ^ (a - r) := by positivity
    calc (1 : ℝ) = ‖p‖ ^ (a - r) * ‖p‖ ^ ((r : ℤ) - a) := h3.symm
      _ ≤ ‖p‖ ^ (a - r) * (4 : ℝ) ^ ((r : ℤ) - a) := mul_le_mul_of_nonneg_left h1 h4
      _ = _ := by ring
  calc ‖iteratedFDeriv ℝ r (f i) p‖ ≤ |K| * 1 := by
        rw [mul_one]; exact (hK i p hp).trans (le_abs_self K)
    _ ≤ |K| * ((4 : ℝ) ^ ((r : ℤ) - a) * ‖p‖ ^ (a - r)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    _ = _ := by ring
end Calculus
section Landau
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
private lemma norm_fderiv_le_of_bounds (h : Mom → F) (hh : ContDiff ℝ 2 h) (p : Mom) {t A Hh : ℝ} (ht : 0 < t)
    (hA : ∀ q, ‖q - p‖ ≤ t → ‖h q‖ ≤ A) (hH : ∀ q, ‖q - p‖ ≤ t → ‖fderiv ℝ (fderiv ℝ h) q‖ ≤ Hh) :
    ‖fderiv ℝ h p‖ ≤ 2 * A / t + Hh * t := by
  have hd1 : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hpp : ‖p - p‖ ≤ t := by simpa using ht.le
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA p hpp)
  have hH0 : 0 ≤ Hh := (norm_nonneg (fderiv ℝ (fderiv ℝ h) p)).trans (hH p hpp)
  have hconv : Convex ℝ (Metric.closedBall p t) := convex_closedBall p t
  have hmem : ∀ {q}, q ∈ Metric.closedBall p t ↔ ‖q - p‖ ≤ t := by
    intro q; simp [dist_eq_norm]
  have hpmem : p ∈ Metric.closedBall p t := hmem.mpr hpp
  have s1 : ∀ x ∈ Metric.closedBall p t, ‖fderiv ℝ h x - fderiv ℝ h p‖ ≤ Hh * t := by
    intro x hx
    have := hconv.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ h) (C := Hh)
      (fun y _ => hd2 y) (fun y hy => hH y (hmem.mp hy)) hpmem hx
    exact this.trans (mul_le_mul_of_nonneg_left (hmem.mp hx) hH0)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  set u : Mom := (t / ‖v‖) • v with hu
  have hun : ‖u‖ = t := by
    rw [hu, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hq : p + u ∈ Metric.closedBall p t := hmem.mpr (by simp [hun])
  have s2 := hconv.norm_image_sub_le_of_norm_fderiv_le' (f := h) (φ := fderiv ℝ h p) (C := Hh * t)
    (fun y _ => hd1 y) s1 hpmem hq
  have e1 : p + u - p = u := by abel
  rw [e1, hun] at s2
  have s3 : ‖fderiv ℝ h p u‖ ≤ 2 * A + Hh * t * t := by
    have a1 := hA (p + u) (hmem.mp hq)
    have a2 := hA p hpp
    have e2 : fderiv ℝ h p u = (h (p + u) - h p) - (h (p + u) - h p - fderiv ℝ h p u) := by abel
    rw [e2]
    refine (norm_sub_le _ _).trans (add_le_add ?_ s2)
    refine (norm_sub_le _ _).trans ?_
    linarith
  have e3 : fderiv ℝ h p u = (t / ‖v‖) • fderiv ℝ h p v := by
    rw [hu, map_smul]
  rw [e3, norm_smul, Real.norm_of_nonneg (by positivity)] at s3
  have : ‖fderiv ℝ h p v‖ = (‖v‖ / t) * ((t / ‖v‖) * ‖fderiv ℝ h p v‖) := by
    field_simp
  rw [this]
  calc ‖v‖ / t * (t / ‖v‖ * ‖fderiv ℝ h p v‖) ≤ ‖v‖ / t * (2 * A + Hh * t * t) :=
        mul_le_mul_of_nonneg_left s3 (by positivity)
    _ = (2 * A / t + Hh * t) * ‖v‖ := by field_simp
private lemma norm_iteratedFDeriv_two_eq (E : Mom → F) (x : Mom) : ‖iteratedFDeriv ℝ 2 E x‖ = ‖fderiv ℝ (fderiv ℝ E) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
private lemma fderiv_le_of_quartic {E : Mom → F} (hE : ContDiff ℝ ∞ E) {K Hh ν : ℝ} (hK0 : 0 ≤ K)
    (hν : 0 ≤ ν) (hK : ∀ q, ‖E q‖ ≤ K * (‖q‖ ^ 4 + ν ^ 4))
    (hH : ∀ q, ‖q‖ ≤ 1 → ‖iteratedFDeriv ℝ 2 E q‖ ≤ Hh) {q : Mom} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ ≤ 1 / 4)
    (hνq : ν ≤ 2 * ‖q‖) : ‖fderiv ℝ E q‖ ≤ (64 * K + Hh) * ‖q‖ ^ 2 := by
  set s := ‖q‖ with hs
  have ht : 0 < s ^ 2 := by positivity
  have hss : s ^ 2 ≤ s := by nlinarith
  have hE2 : ContDiff ℝ 2 E := by simpa using contDiff_infty.1 hE 2
  have hb : ∀ x, ‖x - q‖ ≤ s ^ 2 → ‖x‖ ≤ 2 * s := by
    intro x hx
    have : ‖x‖ ≤ ‖x - q‖ + ‖q‖ := by simpa using norm_add_le (x - q) q
    linarith
  have := norm_fderiv_le_of_bounds E hE2 q (A := 32 * K * s ^ 4) (Hh := Hh) ht
    (fun x hx => by
      refine (hK x).trans ?_
      have h1 := hb x hx
      have h2 : ‖x‖ ^ 4 ≤ (2 * s) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1 4
      have h3 : ν ^ 4 ≤ (2 * s) ^ 4 := pow_le_pow_left₀ hν hνq 4
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add h2 h3) hK0])
    (fun x hx => by
      rw [← norm_iteratedFDeriv_two_eq]
      refine hH x ((hb x hx).trans ?_)
      linarith)
  refine this.trans_eq ?_
  field_simp
  ring
private lemma fderiv_fderiv_le_of_quartic {E : Mom → F} (hE : ContDiff ℝ ∞ E) {K Hh ν : ℝ} (hK0 : 0 ≤ K)
    (hν : 0 ≤ ν) (hK : ∀ q, ‖E q‖ ≤ K * (‖q‖ ^ 4 + ν ^ 4))
    (hH : ∀ q, ‖q‖ ≤ 1 → ‖iteratedFDeriv ℝ 2 E q‖ ≤ Hh)
    (hH3 : ∀ q, ‖q‖ ≤ 1 → ‖iteratedFDeriv ℝ 3 E q‖ ≤ Hh) {p : Mom} (hp0 : 0 < ‖p‖) (hp1 : ‖p‖ ≤ 1 / 8)
    (hνp : ν ≤ ‖p‖) : ‖fderiv ℝ (fderiv ℝ E) p‖ ≤ (12 * (64 * K + Hh) + Hh) * ‖p‖ := by
  set w := ‖p‖ with hw
  have hH0 : 0 ≤ Hh := (norm_nonneg _).trans (hH 0 (by simp))
  have hK1 : 0 ≤ 64 * K + Hh := by positivity
  have hd : ContDiff ℝ 2 (fderiv ℝ E) := by
    simpa using contDiff_infty.1 (hE.fderiv_right (m := ∞) (by simp)) 2
  have hbx : ∀ x, ‖x - p‖ ≤ w / 2 → w / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3 * w / 2 := by
    intro x hx
    have h1 : ‖x‖ ≤ ‖x - p‖ + ‖p‖ := by simpa using norm_add_le (x - p) p
    have h2 : ‖p‖ ≤ ‖p - x‖ + ‖x‖ := by simpa using norm_add_le (p - x) x
    rw [norm_sub_rev] at h2
    constructor <;> linarith
  have := norm_fderiv_le_of_bounds (fderiv ℝ E) hd p (A := (64 * K + Hh) * (3 * w ^ 2)) (Hh := Hh) (by positivity : 0 < w / 2)
    (fun x hx => by
      obtain ⟨h1, h2⟩ := hbx x hx
      have h0 : 0 < ‖x‖ := by linarith
      refine (fderiv_le_of_quartic hE hK0 hν hK hH h0 (by linarith) (by linarith)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK1
      nlinarith)
    (fun x hx => by
      obtain ⟨h1, h2⟩ := hbx x hx
      rw [← norm_iteratedFDeriv_two_eq, norm_iteratedFDeriv_fderiv]
      exact hH3 x (by linarith))
  refine this.trans ?_
  have : 2 * ((64 * K + Hh) * (3 * w ^ 2)) / (w / 2) = 12 * (64 * K + Hh) * w := by
    field_simp; ring
  rw [this]
  nlinarith
end Landau
section Periodize
private def wrapAngle (x : ℝ) : ℝ := x - 2 * Real.pi * round (x / (2 * Real.pi))
private def periodize (σ : Fin 4 → ℂ) (Θ : Mom → ℂ) (p : Mom) : ℂ :=
  (∏ i, σ i ^ round (p i / (2 * Real.pi))) * Θ (fun i => wrapAngle (p i))
private lemma round_eq_of_abs_lt {x : ℝ} {n : ℤ} (h : |x - n| < 1 / 2) : round x = n := by
  rw [round_eq, Int.floor_eq_iff]
  have := abs_lt.mp h
  constructor <;> linarith [this.1, this.2]
private lemma twoPi_pos : 0 < 2 * Real.pi := by positivity
private lemma wrapAngle_add_two_pi (x : ℝ) : wrapAngle (x + 2 * Real.pi) = wrapAngle x := by
  have : (x + 2 * Real.pi) / (2 * Real.pi) = x / (2 * Real.pi) + 1 := by
    field_simp
  simp only [wrapAngle, this, round_add_one]
  push_cast; ring
private lemma periodize_add_single (σ : Fin 4 → ℂ) (hσ : ∀ i, σ i ≠ 0) (Θ : Mom → ℂ) (p : Mom) (i : Fin 4) :
    periodize σ Θ (p + Pi.single i (2 * Real.pi)) = σ i * periodize σ Θ p := by
  have e1 : (fun j => wrapAngle ((p + Pi.single i (2 * Real.pi) : Mom) j)) = fun j => wrapAngle (p j) := by
    funext j
    by_cases h : j = i
    · subst h; simp [wrapAngle_add_two_pi]
    · simp [h]
  have e2 : ∀ j, σ j ^ round ((p + Pi.single i (2 * Real.pi) : Mom) j / (2 * Real.pi)) =
      σ j ^ round (p j / (2 * Real.pi)) * (if j = i then σ j else 1) := by
    intro j
    by_cases h : j = i
    · subst h
      have : (p j + 2 * Real.pi) / (2 * Real.pi) = p j / (2 * Real.pi) + 1 := by field_simp
      simp [this, round_add_one, zpow_add₀ (hσ j)]
    · simp [h]
  unfold periodize
  rw [e1, Finset.prod_congr rfl fun j _ => e2 j, Finset.prod_mul_distrib]
  simp [Finset.prod_ite_eq']
  ring
private lemma half_le_abs_sub_two_pi_mul {x : ℝ} (h1 : Real.pi ≤ |x|) (h2 : |x| < 7 / 2) (n : ℤ) :
    1 / 2 ≤ |x - 2 * Real.pi * n| := by
  have hpi := Real.pi_gt_d2
  rcases eq_or_ne n 0 with rfl | hn
  · simp; linarith
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have h3 : |2 * Real.pi * n| ≤ |x - 2 * Real.pi * n| + |x| := by
    have := abs_sub_le (2 * Real.pi * (n : ℝ)) x 0
    simpa [abs_sub_comm] using this
  have h4 : |2 * Real.pi * (n : ℝ)| = 2 * Real.pi * |(n : ℝ)| := by
    rw [abs_mul, abs_of_pos twoPi_pos]
  rw [h4] at h3
  nlinarith
private lemma periodize_eq_self (σ : Fin 4 → ℂ) {Θ : Mom → ℂ} (hΘ : ∀ p, 1 / 2 ≤ ‖p‖ → Θ p = 0) {p : Mom} (hp : ‖p‖ < 7 / 2) :
    periodize σ Θ p = Θ p := by
  have hpi := Real.pi_gt_d2
  by_cases h : ∀ i, |p i| < Real.pi
  · have e : ∀ i, round (p i / (2 * Real.pi)) = 0 := by
      intro i
      apply round_eq_of_abs_lt
      simp only [Int.cast_zero, sub_zero, abs_div, abs_of_pos twoPi_pos]
      rw [div_lt_iff₀ twoPi_pos]
      linarith [h i]
    unfold periodize
    simp only [wrapAngle, e]
    simp
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hi2 : |p i| < 7 / 2 := by
      have := norm_le_pi_norm p i
      rw [Real.norm_eq_abs] at this
      linarith
    have h1 : Θ p = 0 := by
      apply hΘ
      have := norm_le_pi_norm p i
      rw [Real.norm_eq_abs] at this
      linarith
    have h2 : Θ (fun j => wrapAngle (p j)) = 0 := by
      apply hΘ
      have := norm_le_pi_norm (fun j => wrapAngle (p j)) i
      rw [Real.norm_eq_abs] at this
      exact (half_le_abs_sub_two_pi_mul hi hi2 _).trans this
    simp [periodize, h1, h2]
private lemma periodize_contDiff (σ : Fin 4 → ℂ) {Θ : Mom → ℂ} (hs : ContDiff ℝ ∞ Θ) (hΘ : ∀ p, 1 / 2 ≤ ‖p‖ → Θ p = 0) :
    ContDiff ℝ ∞ (periodize σ Θ) := by
  have hpi := Real.pi_gt_d2
  have hpi4 := Real.pi_lt_d2
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases h : ∀ i, |wrapAngle (p i)| < 3
  · set n : Fin 4 → ℤ := fun i => round (p i / (2 * Real.pi)) with hn
    have hev : ∀ᶠ q : Mom in nhds p, ∀ i, |q i - 2 * Real.pi * n i| < 3 := by
      rw [Filter.eventually_all]
      intro i
      have hc : Continuous fun q : Mom => |q i - 2 * Real.pi * n i| := by fun_prop
      exact hc.continuousAt.eventually (gt_mem_nhds (h i))
    have hsm : ContDiff ℝ ∞ (fun q : Mom => (∏ i, σ i ^ n i) * Θ (fun i => q i - 2 * Real.pi * n i)) := by
      refine contDiff_const.mul (hs.comp ?_)
      rw [contDiff_pi]
      intro i
      exact (contDiff_apply ℝ ℝ i).sub contDiff_const
    refine hsm.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    have e : ∀ i, round (q i / (2 * Real.pi)) = n i := by
      intro i
      apply round_eq_of_abs_lt
      have : q i / (2 * Real.pi) - n i = (q i - 2 * Real.pi * n i) / (2 * Real.pi) := by field_simp
      rw [this, abs_div, abs_of_pos twoPi_pos, div_lt_iff₀ twoPi_pos]
      linarith [hq i]
    simp only [periodize, wrapAngle, e]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hev : ∀ᶠ q : Mom in nhds p, |q i - p i| < 1 / 4 := by
      have hc : Continuous fun q : Mom => |q i - p i| := by fun_prop
      have h0 : |p i - p i| < 1 / 4 := by simp
      exact hc.continuousAt.eventually (gt_mem_nhds h0)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    have hz : Θ (fun j => wrapAngle (q j)) = 0 := by
      apply hΘ
      have h0 := norm_le_pi_norm (fun j => wrapAngle (q j)) i
      rw [Real.norm_eq_abs] at h0
      refine le_trans ?_ h0
      set m := round (q i / (2 * Real.pi)) with hm
      have h1 : |p i / (2 * Real.pi) - round (p i / (2 * Real.pi))| ≤ |p i / (2 * Real.pi) - m| :=
        round_le _ _
      have h2 : |wrapAngle (p i)| ≤ |p i - 2 * Real.pi * m| := by
        have e1 : ∀ k : ℤ, p i - 2 * Real.pi * k = (2 * Real.pi) * (p i / (2 * Real.pi) - k) := by
          intro k; field_simp
        simp only [wrapAngle]
        rw [e1 (round (p i / (2 * Real.pi))), e1 m, abs_mul (2 * Real.pi) _, abs_mul (2 * Real.pi) _]
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      have h3 : |p i - 2 * Real.pi * m| ≤ |q i - 2 * Real.pi * m| + |q i - p i| := by
        have := abs_sub_le (p i) (q i) (2 * Real.pi * m)
        rwa [abs_sub_comm (p i) (q i), add_comm] at this
      have h4 : wrapAngle (q i) = q i - 2 * Real.pi * m := rfl
      simp only [h4]
      linarith
    simp [periodize, hz]
end Periodize
private lemma abs_sin_sub_self_le (x : ℝ) : |Real.sin x - x| ≤ 2 * |x| ^ 3 := by apply _root_.YangMills.SharedProofs.p58168 <;> assumption
private lemma abs_sin_le_abs (x : ℝ) : |Real.sin x| ≤ |x| := by
  have key : ∀ y : ℝ, 0 ≤ y → |Real.sin y| ≤ y := by
    intro y hy
    rcases le_or_gt 1 y with h1 | h1
    · exact (Real.abs_sin_le_one y).trans h1
    rcases hy.eq_or_lt with rfl | hy0
    · simp
    · rw [abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hy0 (by linarith [Real.pi_gt_three]))]
      exact (Real.sin_lt hy0).le
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; exact key x h
  · have := key (-x) (by linarith)
    rw [Real.sin_neg, abs_neg] at this
    rw [abs_of_nonpos h]
    exact this
private def chord (t : ℝ) : ℝ := 2 * Real.sin (t / 2)
private lemma abs_chord_sub_le (t : ℝ) : |chord t - t| ≤ |t| ^ 3 := by
  have h := abs_sin_sub_self_le (t / 2)
  have e : chord t - t = 2 * (Real.sin (t / 2) - t / 2) := by unfold chord; ring
  rw [e, abs_mul, abs_two]
  have e2 : |t / 2| = |t| / 2 := by rw [abs_div, abs_two]
  rw [e2] at h
  have : 0 ≤ |t| ^ 3 := by positivity
  nlinarith
private lemma abs_chord_le (t : ℝ) : |chord t| ≤ |t| := by
  have h := abs_sin_le_abs (t / 2)
  unfold chord
  rw [abs_mul, abs_two]
  rw [abs_div, abs_two] at h
  linarith
private lemma half_abs_le_abs_chord {t : ℝ} (h : |t| < 7 / 2) : |t| / 2 ≤ |chord t| := by
  have key : ∀ u : ℝ, 0 ≤ u → u < 7 / 4 → u / 2 ≤ Real.sin u := by
    intro u h0 h1
    have hpi := Real.pi_gt_d2
    have hpi2 := Real.pi_lt_d2
    rcases le_or_gt u (Real.pi / 2) with h2 | h2
    · have := Real.mul_le_sin h0 h2
      have h3 : u / 2 ≤ 2 / Real.pi * u := by
        have : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          linarith
        nlinarith
      linarith
    · have h3 := Real.mul_le_sin (x := Real.pi - u) (by linarith) (by linarith)
      rw [Real.sin_pi_sub] at h3
      have h4 : (7 : ℝ) / 8 ≤ 2 / Real.pi * (Real.pi - u) := by
        have e : 2 / Real.pi * (Real.pi - u) = 2 - 2 * u / Real.pi := by field_simp
        rw [e]
        have : 2 * u / Real.pi ≤ 9 / 8 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        linarith
      linarith
  have habs : |chord t| = 2 * |Real.sin (t / 2)| := by unfold chord; rw [abs_mul, abs_two]
  rw [habs]
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    have := key (t / 2) (by linarith) (by linarith)
    have h2 := le_abs_self (Real.sin (t / 2))
    linarith
  · rw [abs_of_nonpos h0] at h ⊢
    have := key (-t / 2) (by linarith) (by linarith)
    have e : Real.sin (-t / 2) = -Real.sin (t / 2) := by
      rw [show -t / 2 = -(t / 2) by ring, Real.sin_neg]
    rw [e] at this
    have h2 := neg_le_abs (Real.sin (t / 2))
    linarith
private lemma abs_chord_mul_sub_le (a b x : ℝ) (ha : |a| ≤ x) (hb : |b| ≤ x) (hy : 0 ≤ x) :
    |chord a * chord b - a * b| ≤ 2 * x ^ 4 := by
  have h1 : |chord a - a| ≤ x ^ 3 := (abs_chord_sub_le a).trans (pow_le_pow_left₀ (abs_nonneg _) ha 3)
  have h2 : |chord b - b| ≤ x ^ 3 := (abs_chord_sub_le b).trans (pow_le_pow_left₀ (abs_nonneg _) hb 3)
  have h3 : |chord b| ≤ x := (abs_chord_le b).trans hb
  have e : chord a * chord b - a * b = (chord a - a) * chord b + a * (chord b - b) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have t1 : |chord a - a| * |chord b| ≤ x ^ 3 * x := mul_le_mul h1 h3 (abs_nonneg _) (by positivity)
  have t2 : |a| * |chord b - b| ≤ x * x ^ 3 := mul_le_mul ha h2 (abs_nonneg _) hy
  nlinarith
private lemma sqNorm_nonneg (p : Mom) : 0 ≤ LinearResponse.sqNorm p := Finset.sum_nonneg fun i _ => sq_nonneg _
private lemma norm_sq_le_sqNorm (p : Mom) : ‖p‖ ^ 2 ≤ LinearResponse.sqNorm p := by apply _root_.YangMills.Construction.Tower.FreeResolvents.CubicSumIntegral.sq_norm_le_sum_sq <;> assumption
private lemma sqNorm_le_four_mul_norm_sq (p : Mom) : LinearResponse.sqNorm p ≤ 4 * ‖p‖ ^ 2 := by
  have : LinearResponse.sqNorm p ≤ ∑ _i : Fin 4, ‖p‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h := norm_le_pi_norm p i
    rw [Real.norm_eq_abs] at h
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa using this
private lemma norm_sq_le_four_mul_sqNorm_lattice {p : Mom} (h : ‖p‖ < 7 / 2) :
    ‖p‖ ^ 2 ≤ 4 * LinearResponse.sqNorm (latticeMomentum p) := by
  have hh : ‖p‖ ≤ Real.sqrt (4 * LinearResponse.sqNorm (latticeMomentum p)) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    apply Real.le_sqrt_of_sq_le
    have h1 := norm_le_pi_norm p i
    rw [Real.norm_eq_abs] at h1
    have h2 := half_abs_le_abs_chord (t := p i) (by linarith)
    have h3 : (|p i| / 2) ^ 2 ≤ |chord (p i)| ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    rw [sq_abs] at h3
    have h4 : |p i| ^ 2 = p i ^ 2 := sq_abs _
    have h5 : chord (p i) ^ 2 ≤ LinearResponse.sqNorm (latticeMomentum p) :=
      Finset.single_le_sum (f := fun i => latticeMomentum p i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [div_pow, h4] at h3
    nlinarith
  calc ‖p‖ ^ 2 ≤ Real.sqrt (4 * LinearResponse.sqNorm (latticeMomentum p)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ = _ := Real.sq_sqrt (by have := sqNorm_nonneg (latticeMomentum p); linarith)
section Annulus
variable {ι : Type*} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
private def annulus (ν : ι → ℝ) (i : ι) : Set Mom := {p | ν i < ‖p‖ ∧ ‖p‖ < 7 / 2}
private lemma regDomain_annulus {ν : ι → ℝ} (hν : ∀ i, 0 < ν i) : RegDomain (annulus ν) where
  isOpen i := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  norm_pos i p hp := (hν i).trans hp.1
  norm_le i p hp := by have := hp.2; linarith
private lemma hasOrder_three {ν : ι → ℝ} (hν : ∀ i, 0 < ν i) {f : ι → Mom → F} (hs : ∀ i, ContDiff ℝ ∞ (f i)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ i q, ‖f i q‖ ≤ K * (‖q‖ ^ 4 + ν i ^ 4))
    (hb : ∀ r : ℕ, ∃ Kb : ℝ, ∀ i q, ‖q‖ ≤ 4 → ‖iteratedFDeriv ℝ r (f i) q‖ ≤ Kb) :
    HasOrder (annulus ν) 3 f := by
  have hU := regDomain_annulus hν
  refine HasOrder.of_bounded hU (fun i => (hs i).contDiffOn) (fun r => ?_) (fun r hr => ?_)
  · obtain ⟨Kb, h⟩ := hb r
    exact ⟨Kb, fun i p hp => h i p (hU.norm_le i p hp)⟩
  obtain ⟨K1, h1⟩ := hb 1
  obtain ⟨K2, h2⟩ := hb 2
  obtain ⟨K3, h3⟩ := hb 3
  set Hh := |K2| + |K3| with hHh
  have hH2 : ∀ i q, ‖q‖ ≤ 1 → ‖iteratedFDeriv ℝ 2 (f i) q‖ ≤ Hh := fun i q hq =>
    (h2 i q (by linarith)).trans ((le_abs_self _).trans (by simp [hHh]))
  have hH3 : ∀ i q, ‖q‖ ≤ 1 → ‖iteratedFDeriv ℝ 3 (f i) q‖ ≤ Hh := fun i q hq =>
    (h3 i q (by linarith)).trans ((le_abs_self _).trans (by simp [hHh]))
  have hr3 : r < 3 := by omega
  interval_cases r
  · refine ⟨K * 8, fun i p hp => ?_⟩
    have hw : 0 < ‖p‖ := hU.norm_pos i p hp
    have h4 : ‖p‖ ≤ 4 := hU.norm_le i p hp
    have hn : ν i ≤ ‖p‖ := hp.1.le
    rw [norm_iteratedFDeriv_zero]
    refine (hK i p).trans ?_
    have e : ‖p‖ ^ ((3 : ℤ) - ((0 : ℕ) : ℤ)) = ‖p‖ ^ 3 := by norm_num
    rw [e]
    have h5 : ν i ^ 4 ≤ ‖p‖ ^ 4 := pow_le_pow_left₀ (hν i).le hn 4
    have h6 : ‖p‖ ^ 4 ≤ 4 * ‖p‖ ^ 3 := by
      have : ‖p‖ ^ 4 = ‖p‖ * ‖p‖ ^ 3 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h4 (by positivity)
    have h7 : K * (‖p‖ ^ 4 + ν i ^ 4) ≤ K * (2 * (4 * ‖p‖ ^ 3)) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    exact h7.trans_eq (by ring)
  · refine ⟨(64 * K + Hh) + 64 * |K1|, fun i p hp => ?_⟩
    have hw : 0 < ‖p‖ := hU.norm_pos i p hp
    have hn : ν i ≤ ‖p‖ := hp.1.le
    have e : ‖p‖ ^ ((3 : ℤ) - ((1 : ℕ) : ℤ)) = ‖p‖ ^ 2 := by norm_num
    rw [e, norm_iteratedFDeriv_one]
    rcases le_or_gt ‖p‖ (1 / 8) with h8 | h8
    · have := fderiv_le_of_quartic (hs i) hK0 (hν i).le (hK i) (hH2 i) hw (by linarith) (by linarith)
      refine this.trans ?_
      have : 0 ≤ |K1| * ‖p‖ ^ 2 := by positivity
      nlinarith
    · have := h1 i p (hU.norm_le i p hp)
      rw [norm_iteratedFDeriv_one] at this
      have h5 : K1 ≤ |K1| := le_abs_self _
      have h6 : (1 : ℝ) ≤ 64 * ‖p‖ ^ 2 := by nlinarith
      have h7 : 0 ≤ (64 * K + Hh) * ‖p‖ ^ 2 := by positivity
      nlinarith [abs_nonneg K1]
  · refine ⟨(12 * (64 * K + Hh) + Hh) + 8 * |K2|, fun i p hp => ?_⟩
    have hw : 0 < ‖p‖ := hU.norm_pos i p hp
    have hn : ν i ≤ ‖p‖ := hp.1.le
    have e : ‖p‖ ^ ((3 : ℤ) - ((2 : ℕ) : ℤ)) = ‖p‖ := by norm_num
    rw [e]
    rcases le_or_gt ‖p‖ (1 / 8) with h8 | h8
    · have := fderiv_fderiv_le_of_quartic (hs i) hK0 (hν i).le (hK i) (hH2 i) (hH3 i) hw h8 hn
      rw [norm_iteratedFDeriv_two_eq]
      refine this.trans ?_
      have : 0 ≤ |K2| * ‖p‖ := by positivity
      nlinarith
    · have := h2 i p (hU.norm_le i p hp)
      have h5 : K2 ≤ |K2| := le_abs_self _
      have h6 : (0 : ℝ) ≤ (12 * (64 * K + Hh) + Hh) * ‖p‖ := by positivity
      nlinarith [abs_nonneg K2]
private lemma bound_on_ball {J : Type*} [Finite J] (g : J → Mom → F) (hg : ∀ j, ContDiff ℝ ∞ (g j)) (R : ℝ) (r : ℕ) :
    ∃ K : ℝ, ∀ j q, ‖q‖ ≤ R → ‖iteratedFDeriv ℝ r (g j) q‖ ≤ K := by
  classical
  have := Fintype.ofFinite J
  have h : ∀ j, ∃ K : ℝ, ∀ q, ‖q‖ ≤ R → ‖iteratedFDeriv ℝ r (g j) q‖ ≤ K := by
    intro j
    have hc : Continuous (iteratedFDeriv ℝ r (g j)) :=
      (hg j).continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Mom) R).exists_bound_of_continuousOn hc.continuousOn
    exact ⟨K, fun q hq => hK q (by simpa [dist_eq_norm] using hq)⟩
  choose K hK using h
  refine ⟨∑ j, |K j|, fun j q hq => (hK j q hq).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun j => |K j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
end Annulus
private abbrev Fiber := EuclideanSpace ℂ (Fin 4)
private abbrev Ops := Fiber →L[ℂ] Fiber
private def matOp (A : Matrix (Fin 4) (Fin 4) ℂ) : Ops := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℂ) A
private lemma matOp_mul (A B : Matrix (Fin 4) (Fin 4) ℂ) : matOp (A * B) = matOp A * matOp B := map_mul _ _ _
private lemma matOp_one : matOp 1 = 1 := map_one _
private lemma matOp_apply (A : Matrix (Fin 4) (Fin 4) ℂ) (x : Fiber) (m : Fin 4) :
    (matOp A x) m = ∑ m', A m m' * x m' := by
  have := congrFun (Matrix.ofLp_toEuclideanCLM (n := Fin 4) (𝕜 := ℂ) A x) m
  simpa [matOp, Matrix.mulVec, dotProduct] using this
private lemma inner_matOp (A : Matrix (Fin 4) (Fin 4) ℂ) (x : Fiber) :
    inner ℂ x (matOp A x) = ∑ m, ∑ m', (starRingEnd ℂ) (x m) * A m m' * x m' := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [matOp_apply, RCLike.inner_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m' _ => ?_
  ring
private lemma inverse_of_coercive {M : Matrix (Fin 4) (Fin 4) ℂ} {l : ℝ} (hl : 0 < l)
    (h : ∀ v : Fin 4 → ℂ, l * ∑ m, ‖v m‖ ^ 2 ≤
      (∑ m, ∑ m', (starRingEnd ℂ) (v m) * M m m' * v m').re) :
    IsUnit (matOp M) ∧ Ring.inverse (matOp M) = matOp M⁻¹ ∧ ‖matOp M⁻¹‖ ≤ l⁻¹ := by
  have hb : ∀ x : Fiber, l * ‖x‖ ≤ ‖matOp M x‖ := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 := h x.ofLp
    have h2 : ‖x‖ ^ 2 = ∑ m, ‖x m‖ ^ 2 := EuclideanSpace.norm_sq_eq x
    have h3 : (inner ℂ x (matOp M x)).re ≤ ‖x‖ * ‖matOp M x‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    rw [inner_matOp] at h3
    have h4 : l * ‖x‖ ^ 2 ≤ ‖x‖ * ‖matOp M x‖ := by
      rw [h2]
      exact h1.trans h3
    have h5 : ‖x‖ * (l * ‖x‖) ≤ ‖x‖ * ‖matOp M x‖ := by nlinarith
    exact le_of_mul_le_mul_left h5 hx0
  have hu : IsUnit M := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro a b hab
    have : matOp M (WithLp.toLp 2 (a - b)) = 0 := by
      ext m
      have h0 : (M.mulVec (a - b)) m = 0 := by
        rw [Matrix.mulVec_sub, hab]; simp
      rw [matOp_apply]
      simpa [Matrix.mulVec, dotProduct] using h0
    have h1 := hb (WithLp.toLp 2 (a - b))
    rw [this, norm_zero] at h1
    have h2 : ‖(WithLp.toLp 2 (a - b) : Fiber)‖ = 0 := by
      have := norm_nonneg (WithLp.toLp 2 (a - b) : Fiber)
      nlinarith
    have h3 : (WithLp.toLp 2 (a - b) : Fiber) = 0 := norm_eq_zero.mp h2
    have h4 : a - b = 0 := by
      have := congrArg WithLp.ofLp h3
      simpa using this
    exact sub_eq_zero.mp h4
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hu
  have e1 : matOp M * matOp M⁻¹ = 1 := by rw [← matOp_mul, Matrix.mul_nonsing_inv M hdet, matOp_one]
  have e2 : matOp M⁻¹ * matOp M = 1 := by rw [← matOp_mul, Matrix.nonsing_inv_mul M hdet, matOp_one]
  let u : Opsˣ := ⟨matOp M, matOp M⁻¹, e1, e2⟩
  have hinv : Ring.inverse (matOp M) = matOp M⁻¹ := Ring.inverse_unit u
  refine ⟨u.isUnit, hinv, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have h1 := hb (matOp M⁻¹ y)
  have e3 : matOp M (matOp M⁻¹ y) = y := by
    have := congrArg (fun A : Ops => A y) e1
    simpa using this
  rw [e3] at h1
  rw [inv_mul_eq_div, le_div_iff₀ hl]
  linarith
private lemma HasOrder.congr_on {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ι → Set Mom} (hU : RegDomain U)
    {f g : ι → Mom → F} {a : ℤ} (hf : HasOrder U a f) (h : ∀ i, ∀ p ∈ U i, g i p = f i p) : HasOrder U a g := by
  refine ⟨fun i => (hf.smooth i).congr (h i), fun r => ?_⟩
  obtain ⟨K, hK⟩ := hf.bound r
  refine ⟨K, fun i p hp => ?_⟩
  have hev : g i =ᶠ[𝓝 p] f i := Filter.eventually_of_mem ((hU.isOpen i).mem_nhds hp) (h i)
  rw [(hev.iteratedFDeriv ℝ r).eq_of_nhds]
  exact hK i p hp
private lemma hasOrder_one {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ν : ι → ℝ} (hν : ∀ i, 0 < ν i)
    {J : Type*} [Finite J] (g : J → Mom → F) (hg : ∀ j, ContDiff ℝ ∞ (g j)) (π : ι → J) {K : ℝ}
    (hK : ∀ j q, ‖g j q‖ ≤ K * ‖q‖) : HasOrder (annulus ν) 1 (fun i => g (π i)) := by
  have hU := regDomain_annulus hν
  refine HasOrder.of_bounded hU (fun i => (hg _).contDiffOn) (fun r => ?_) (fun r hr => ?_)
  · obtain ⟨Kb, h⟩ := bound_on_ball g hg 4 r
    exact ⟨Kb, fun i p hp => h _ p (hU.norm_le i p hp)⟩
  · obtain rfl : r = 0 := by omega
    refine ⟨K, fun i p hp => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    simpa using hK (π i) p
private lemma latticeMomentum_contDiff (a : Fin 4) : ContDiff ℝ ∞ (fun p : Mom => latticeMomentum p a) := by
  unfold latticeMomentum
  fun_prop
private lemma sqNorm_contDiff : ContDiff ℝ ∞ (fun p : Mom => LinearResponse.sqNorm p) := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.contDiff_sumSq <;> assumption
private lemma ofReal_comp_contDiff {f : Mom → ℝ} (h : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun p => (f p : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp h
private lemma exp_neg_le_bounds {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 24 / x ^ 4 ∧ Real.exp (-x) ≤ 6 / x ^ 3 := by
  have h4 := Real.pow_div_factorial_le_exp x hx.le 4
  have h3 := Real.pow_div_factorial_le_exp x hx.le 3
  have e4 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  have e3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [e4] at h4
  rw [e3] at h3
  rw [Real.exp_neg]
  have hp := Real.exp_pos x
  constructor
  · rw [inv_eq_one_div, div_le_div_iff₀ hp (by positivity)]
    nlinarith
  · rw [inv_eq_one_div, div_le_div_iff₀ hp (by positivity)]
    nlinarith
private structure KernelData (Bb : ℕ → ℝ) (C c c' N₁ : ℝ) where
  N : ℕ
  N_ge : N₁ ≤ N
  two_le_N : 2 ≤ N
  ε : ℝ
  ε_nonneg : 0 ≤ ε
  ε_le : ε ≤ Real.exp (-(c' * (N : ℝ)))
  S : Mom → Fin 4 → Fin 4 → ℂ
  hasLow : IsLowMomentumSymbol Bb C c ε S
  μ : Fin 4
  ν : Fin 4
  ρ : Fin 4
  τ : Fin 4
private def latticeDefect (a b : Fin 4) (p : Mom) : ℂ :=
  ((latticeMomentum p a * latticeMomentum p b : ℝ) : ℂ) - (if a = b then (LinearResponse.sqNorm p : ℂ) else 0)
private lemma latticeDefect_contDiff (j : Fin 4 × Fin 4) : ContDiff ℝ ∞ (latticeDefect j.1 j.2) := by
  unfold latticeDefect
  refine (ofReal_comp_contDiff ((latticeMomentum_contDiff _).mul (latticeMomentum_contDiff _))).sub ?_
  split_ifs
  · exact ofReal_comp_contDiff sqNorm_contDiff
  · exact contDiff_const
variable {Bb : ℕ → ℝ} {C c c' N₁ : ℝ}
namespace KernelData
variable (i : KernelData Bb C c c' N₁)
private def cutScale : ℝ := 1 / (4 * (i.N : ℝ))
private lemma size_pos : (0 : ℝ) < i.N := by
  have := i.two_le_N
  have h : (2 : ℝ) ≤ i.N := by exact_mod_cast this
  linarith
private lemma cutScale_pos : 0 < i.cutScale := by
  have := i.size_pos
  unfold cutScale
  positivity
private def defect (a b : Fin 4) (p : Mom) : ℂ := i.S p a b + latticeDefect a b p
private lemma symbol_contDiff (a b : Fin 4) : ContDiff ℝ ∞ (fun p => i.S p a b) :=
  contDiff_infty.2 fun r => i.hasLow.smooth r a b
private lemma defect_contDiff (a b : Fin 4) : ContDiff ℝ ∞ (i.defect a b) :=
  (i.symbol_contDiff a b).add (latticeDefect_contDiff (a, b))
private lemma symbolWithGradient_eq (p : Mom) (a b : Fin 4) :
    symbolWithGradient i.S p a b = i.defect a b p + (if a = b then (LinearResponse.sqNorm p : ℂ) else 0) := by
  simp only [symbolWithGradient, defect, latticeDefect]
  push_cast
  ring
private lemma ε_le_cutScale (hc' : 0 < c') : i.ε ≤ (24 * 256 / c' ^ 4) * i.cutScale ^ 4 := by
  have hN := i.size_pos
  have := (exp_neg_le_bounds (mul_pos hc' hN)).1
  refine i.ε_le.trans (this.trans_eq ?_)
  unfold cutScale
  field_simp
  norm_num
end KernelData
private def defectConst (C c' : ℝ) : ℝ := 16 * |C| + 2 + |C| * (24 * 256 / c' ^ 4)
private lemma defectConst_nonneg (hc' : 0 < c') : 0 ≤ defectConst C c' := by unfold defectConst; positivity
private lemma defect_bound (hc' : 0 < c') (i : KernelData Bb C c c' N₁) (a b : Fin 4) (q : Mom) :
    ‖i.defect a b q‖ ≤ defectConst C c' * (‖q‖ ^ 4 + i.cutScale ^ 4) := by
  have h1 := i.hasLow.near_transverse q a b
  have e : i.defect a b q = (i.S q a b - ((LinearResponse.sqNorm q * (if a = b then 1 else 0) - q a * q b : ℝ) : ℂ)) +
      ((latticeMomentum q a * latticeMomentum q b - q a * q b : ℝ) : ℂ) := by
    simp only [KernelData.defect, latticeDefect]
    split_ifs <;> push_cast <;> ring
  have h2 : |latticeMomentum q a * latticeMomentum q b - q a * q b| ≤ 2 * ‖q‖ ^ 4 := by
    have ha := norm_le_pi_norm q a
    have hb := norm_le_pi_norm q b
    rw [Real.norm_eq_abs] at ha hb
    exact abs_chord_mul_sub_le (q a) (q b) ‖q‖ ha hb (norm_nonneg _)
  have h3 : LinearResponse.sqNorm q ^ 2 ≤ 16 * ‖q‖ ^ 4 := by
    have := sqNorm_le_four_mul_norm_sq q
    have h0 := sqNorm_nonneg q
    calc LinearResponse.sqNorm q ^ 2 ≤ (4 * ‖q‖ ^ 2) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = _ := by ring
  have h4 := i.ε_le_cutScale hc'
  have hn4 : 0 ≤ i.cutScale ^ 4 := by have := i.cutScale_pos; positivity
  have hq4 : 0 ≤ ‖q‖ ^ 4 := by positivity
  have h5 : C * (LinearResponse.sqNorm q ^ 2 + i.ε) ≤ |C| * (16 * ‖q‖ ^ 4 + (24 * 256 / c' ^ 4) * i.cutScale ^ 4) := by
    have h0 := i.ε_nonneg
    have h00 : 0 ≤ LinearResponse.sqNorm q ^ 2 + i.ε := by positivity
    calc C * (LinearResponse.sqNorm q ^ 2 + i.ε) ≤ |C| * (LinearResponse.sqNorm q ^ 2 + i.ε) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) h00
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h6 : ‖((latticeMomentum q a * latticeMomentum q b - q a * q b : ℝ) : ℂ)‖ ≤ 2 * ‖q‖ ^ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact h2
  have h7 : 0 ≤ |C| * (24 * 256 / c' ^ 4) := by positivity
  have h8 := abs_nonneg C
  unfold defectConst
  have t1 := mul_nonneg h7 hq4
  have t2 := mul_nonneg h8 hn4
  nlinarith [h1, h5, h6, mul_nonneg (by positivity : (0 : ℝ) ≤ 16 * |C| + 2) hn4]
section Family
variable (hc' : 0 < c') (hc : 0 < c)
private abbrev domain (Bb : ℕ → ℝ) (C c c' N₁ : ℝ) : KernelData Bb C c c' N₁ → Set Mom := annulus KernelData.cutScale
private lemma regDomain_domain : RegDomain (domain Bb C c c' N₁) := regDomain_annulus KernelData.cutScale_pos
include hc' in
private lemma hasOrder_defect (a b : Fin 4) : HasOrder (domain Bb C c c' N₁) 3 (fun i => i.defect a b) := by
  refine hasOrder_three KernelData.cutScale_pos (fun i => i.defect_contDiff a b) (defectConst_nonneg hc') (fun i q => defect_bound hc' i a b q) fun r => ?_
  obtain ⟨Kg, hKg⟩ := bound_on_ball (fun j : Fin 4 × Fin 4 => latticeDefect j.1 j.2) latticeDefect_contDiff 4 r
  refine ⟨Bb r + Kg, fun i q hq => ?_⟩
  have h1 : ContDiffAt ℝ r (fun p => i.S p a b) q :=
    ((i.symbol_contDiff a b).of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : ContDiffAt ℝ r (latticeDefect a b) q :=
    ((latticeDefect_contDiff (a, b)).of_le (by exact_mod_cast le_top)).contDiffAt
  have e : iteratedFDeriv ℝ r (i.defect a b) q =
      iteratedFDeriv ℝ r (fun p => i.S p a b) q + iteratedFDeriv ℝ r (latticeDefect a b) q :=
    iteratedFDeriv_add_apply (x := q) h1 h2
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (i.hasLow.deriv_le r a b q) (hKg (a, b) q hq))
private def unitOp (a b : Fin 4) : Ops := matOp (Matrix.single a b 1)
private def defectOp (i : KernelData Bb C c c' N₁) (p : Mom) : Ops := ∑ a, ∑ b, (i.defect a b p) • unitOp a b
private def fullOp (i : KernelData Bb C c c' N₁) (p : Mom) : Ops := (LinearResponse.sqNorm p : ℂ) • (1 : Ops) + defectOp i p
private lemma fullOp_eq (i : KernelData Bb C c c' N₁) (p : Mom) : fullOp i p = matOp (symbolWithGradient i.S p) := by
  have h : symbolWithGradient i.S p = (LinearResponse.sqNorm p : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
      ∑ a, ∑ b, (i.defect a b p) • Matrix.single a b (1 : ℂ) := by
    have hX : (∑ a, ∑ b, (i.defect a b p) • Matrix.single a b (1 : ℂ)) = Matrix.of (fun a b => i.defect a b p) := by
      conv_rhs => rw [Matrix.matrix_eq_sum_single (Matrix.of fun a b => i.defect a b p)]
      simp [Matrix.smul_single]
    ext a b
    rw [i.symbolWithGradient_eq, hX]
    simp [Matrix.one_apply, add_comm]
  rw [h]
  simp only [fullOp, defectOp, unitOp, matOp, map_add, map_smul, map_one, map_sum]
include hc' in
private lemma hasOrder_defectOp : HasOrder (domain Bb C c c' N₁) 3 (defectOp (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  refine HasOrder.finsetSum hU Finset.univ fun a _ => HasOrder.finsetSum hU Finset.univ fun b _ => ?_
  have := HasOrder.bilinear hU (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Ops →L[ℝ] Ops) (hasOrder_defect hc' a b)
    (HasOrder.const _ hU (unitOp a b))
  simpa using this
private lemma hasOrder_coord (a : Fin 4) : HasOrder (domain Bb C c c' N₁) 1 (fun _ p => ((p a : ℝ) : ℂ)) := by
  have := hasOrder_one (ι := KernelData Bb C c c' N₁) KernelData.cutScale_pos (J := Unit) (fun _ p => ((p a : ℝ) : ℂ))
    (fun _ => ofReal_comp_contDiff (contDiff_apply ℝ ℝ a)) (fun _ => ()) (K := 1) (fun _ q => by
      rw [Complex.norm_real, one_mul]
      exact norm_le_pi_norm q a)
  exact this
private lemma hasOrder_sqNorm : HasOrder (domain Bb C c c' N₁) 2 (fun _ p => (LinearResponse.sqNorm p : ℂ)) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  have h : HasOrder (domain Bb C c c' N₁) 2 (fun _ p => ∑ a, ((p a : ℝ) : ℂ) * ((p a : ℝ) : ℂ)) := by
    refine HasOrder.finsetSum hU Finset.univ fun a _ => ?_
    exact HasOrder.bilinear hU (ContinuousLinearMap.mul ℝ ℂ) (hasOrder_coord a) (hasOrder_coord a)
  refine h.congr_on hU fun i p _ => ?_
  simp [LinearResponse.sqNorm, pow_two]
private lemma sqNorm_pos {p : Mom} (h : 0 < ‖p‖) : 0 < LinearResponse.sqNorm p :=
  lt_of_lt_of_le (by positivity) (norm_sq_le_sqNorm p)
private lemma hasOrder_inv_sqNorm : HasOrder (domain Bb C c c' N₁) (-2) (fun _ p => Ring.inverse (LinearResponse.sqNorm p : ℂ)) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  refine HasOrder.ringInverse hU hasOrder_sqNorm (fun i p hp => ?_) (K := 1) (fun i p hp => ?_)
  · have := sqNorm_pos (hU.norm_pos i p hp)
    exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast this.ne'))
  · have hw := hU.norm_pos i p hp
    have h1 := sqNorm_pos hw
    rw [Ring.inverse_eq_inv', norm_inv, Complex.norm_real, Real.norm_of_nonneg h1.le, one_mul]
    have : ‖p‖ ^ (-2 : ℤ) = (‖p‖ ^ 2)⁻¹ := by
      rw [zpow_neg]; norm_cast
    rw [this]
    exact inv_anti₀ (by positivity) (norm_sq_le_sqNorm p)
private def coercivity (i : KernelData Bb C c c' N₁) (p : Mom) : ℝ := c * LinearResponse.sqNorm (latticeMomentum p) - |C| * i.ε
private lemma coercivity_lower (i : KernelData Bb C c c' N₁) (p : Mom) (v : Fin 4 → ℂ) :
    coercivity i p * ∑ m, ‖v m‖ ^ 2 ≤
      (∑ m, ∑ m', (starRingEnd ℂ) (v m) * symbolWithGradient i.S p m m' * v m').re := by
  have h := i.hasLow.coercive p v
  have h0 : 0 ≤ ∑ m, ‖v m‖ ^ 2 := by positivity
  have h1 : C * i.ε ≤ |C| * i.ε := mul_le_mul_of_nonneg_right (le_abs_self C) i.ε_nonneg
  have h2 := mul_le_mul_of_nonneg_right h1 h0
  unfold coercivity
  nlinarith
variable (hN1 : 768 * |C| / (c' ^ 3 * c) ≤ N₁)
include hc hc' hN1 in
private lemma coercivity_ge (i : KernelData Bb C c c' N₁) {p : Mom} (h1 : i.cutScale ≤ ‖p‖) (h2 : ‖p‖ < 7 / 2) :
    c / 8 * ‖p‖ ^ 2 ≤ coercivity i p := by
  have hN := i.size_pos
  have hs := norm_sq_le_four_mul_sqNorm_lattice h2
  have he := (exp_neg_le_bounds (mul_pos hc' hN)).2
  have hn := i.cutScale_pos
  have hN' : 768 * |C| ≤ c * c' ^ 3 * i.N := by
    have := hN1.trans i.N_ge
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  have h3 : |C| * i.ε ≤ c / 8 * i.cutScale ^ 2 := by
    have h4 : i.ε ≤ 6 / (c' * i.N) ^ 3 := i.ε_le.trans he
    have h5 : |C| * i.ε ≤ |C| * (6 / (c' * i.N) ^ 3) := mul_le_mul_of_nonneg_left h4 (abs_nonneg C)
    refine h5.trans ?_
    have e : c / 8 * i.cutScale ^ 2 = (c * c' ^ 3 * i.N / 128 / 6 * 6) / (c' * i.N) ^ 3 := by
      unfold KernelData.cutScale
      field_simp
      ring
    rw [e, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [abs_nonneg C]
  have h4 : i.cutScale ^ 2 ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ hn.le h1 2
  have h5 : c / 8 * i.cutScale ^ 2 ≤ c / 8 * ‖p‖ ^ 2 := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : c * ‖p‖ ^ 2 ≤ c * (4 * LinearResponse.sqNorm (latticeMomentum p)) := mul_le_mul_of_nonneg_left hs hc.le
  unfold coercivity
  nlinarith
private lemma fullOp_inverse (i : KernelData Bb C c c' N₁) {p : Mom} (h : 0 < coercivity i p) :
    IsUnit (fullOp i p) ∧ Ring.inverse (fullOp i p) = matOp (symbolWithGradient i.S p)⁻¹ ∧
      ‖Ring.inverse (fullOp i p)‖ ≤ (coercivity i p)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := inverse_of_coercive h (coercivity_lower i p)
  rw [fullOp_eq]
  exact ⟨h1, h2, by rw [h2]; exact h3⟩
private lemma hasOrder_fullOp (hc' : 0 < c') : HasOrder (domain Bb C c c' N₁) 2 (fullOp (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  have h1 := HasOrder.bilinear hU (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Ops →L[ℝ] Ops) hasOrder_sqNorm
    (HasOrder.const _ hU (1 : Ops))
  have h2 := (hasOrder_defectOp hc').of_le hU (a' := 2) (by norm_num)
  have h3 := HasOrder.add hU (a := 2) (by simpa using h1) h2
  exact h3
include hc hc' hN1 in
private lemma hasOrder_inverse : HasOrder (domain Bb C c c' N₁) (-2) (fun i p => Ring.inverse (fullOp i p)) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  have hlam : ∀ i, ∀ p ∈ domain Bb C c c' N₁ i, c / 8 * ‖p‖ ^ 2 ≤ coercivity i p ∧ 0 < coercivity i p := by
    intro i p hp
    have h0 := coercivity_ge hc' hc hN1 i hp.1.le hp.2
    have hw := hU.norm_pos i p hp
    exact ⟨h0, lt_of_lt_of_le (by positivity) h0⟩
  refine HasOrder.ringInverse hU (hasOrder_fullOp hc') (fun i p hp => (fullOp_inverse i (hlam i p hp).2).1) (K := 8 / c) fun i p hp => ?_
  obtain ⟨h1, h2⟩ := hlam i p hp
  have hw := hU.norm_pos i p hp
  refine (fullOp_inverse i h2).2.2.trans ?_
  have e : ‖p‖ ^ (-(2 : ℤ)) = (‖p‖ ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
  rw [e]
  calc (coercivity i p)⁻¹ ≤ (c / 8 * ‖p‖ ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
    _ = _ := by field_simp
private def remainderOp (i : KernelData Bb C c c' N₁) (p : Mom) : Ops :=
  -((Ring.inverse (LinearResponse.sqNorm p : ℂ)) • (Ring.inverse (fullOp i p) * defectOp i p))
include hc hc' hN1 in
private lemma hasOrder_remainderOp : HasOrder (domain Bb C c c' N₁) (-1) (remainderOp (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  have h1 := HasOrder.bilinear hU (ContinuousLinearMap.mul ℝ Ops) (hasOrder_inverse hc' hc hN1) (hasOrder_defectOp hc')
  have h2 := HasOrder.bilinear hU (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Ops →L[ℝ] Ops) hasOrder_inv_sqNorm h1
  have h3 := h2.neg hU
  exact h3
private lemma inverse_eq (i : KernelData Bb C c c' N₁) {p : Mom} (hs : 0 < LinearResponse.sqNorm p) (hu : IsUnit (fullOp i p)) :
    Ring.inverse (fullOp i p) = Ring.inverse (LinearResponse.sqNorm p : ℂ) • (1 : Ops) + remainderOp i p := by
  have hG : Ring.inverse (fullOp i p) * fullOp i p = 1 := Ring.inverse_mul_cancel _ hu
  have hsq : (LinearResponse.sqNorm p : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set G := Ring.inverse (fullOp i p) with hGd
  set s := Ring.inverse (LinearResponse.sqNorm p : ℂ) with hsd
  have hss : s * (LinearResponse.sqNorm p : ℂ) = 1 := by
    rw [hsd, Ring.inverse_eq_inv']; exact inv_mul_cancel₀ hsq
  have e1 : (LinearResponse.sqNorm p : ℂ) • G + G * defectOp i p = 1 := by
    have : G * fullOp i p = (LinearResponse.sqNorm p : ℂ) • G + G * defectOp i p := by
      simp only [fullOp, mul_add, mul_smul_comm, mul_one]
    rw [← this, hG]
  have e2 : G + s • (G * defectOp i p) = s • (1 : Ops) := by
    rw [← e1, smul_add, smul_smul, hss, one_smul]
  simp only [remainderOp, ← hsd, ← hGd]
  rw [← e2]
  abel
private def entry (a b : Fin 4) : Ops →L[ℝ] ℂ :=
  (((EuclideanSpace.proj a : Fiber →L[ℂ] ℂ).comp
    (ContinuousLinearMap.apply ℂ Fiber (EuclideanSpace.single b (1 : ℂ)))) : Ops →L[ℂ] ℂ).restrictScalars ℝ
private lemma entry_apply (a b : Fin 4) (A : Ops) : entry a b A = (A (EuclideanSpace.single b (1 : ℂ))) a := rfl
private lemma entry_matOp (a b : Fin 4) (M : Matrix (Fin 4) (Fin 4) ℂ) : entry a b (matOp M) = M a b := by
  rw [entry_apply, matOp_apply]
  simp [EuclideanSpace.single_apply]
private lemma entry_one (a b : Fin 4) : entry a b (1 : Ops) = if a = b then 1 else 0 := by
  rw [entry_apply]
  simp [EuclideanSpace.single_apply]
private lemma entry_smul (a b : Fin 4) (s : ℂ) (A : Ops) : entry a b (s • A) = s * entry a b A := by
  simp [entry_apply]
private def latticeCurlPair (a b e f : Fin 4) (p : Mom) : ℂ :=
  ∑ m, (starRingEnd ℂ) (curlSymbol p a b m) * curlSymbol p e f m
private def planeCurlPair (a b e f : Fin 4) (p : Mom) : ℂ :=
  ∑ m, (starRingEnd ℂ) (planeCurl p a b m) * planeCurl p e f m
private def kernelSymbol (i : KernelData Bb C c c' N₁) (p : Mom) : ℂ :=
  ∑ m, ∑ m', (starRingEnd ℂ) (curlSymbol p i.μ i.ν m) * (symbolWithGradient i.S p)⁻¹ m m' *
    curlSymbol p i.ρ i.τ m'
private def kernelError (i : KernelData Bb C c c' N₁) (p : Mom) : ℂ :=
  Ring.inverse (LinearResponse.sqNorm p : ℂ) * (latticeCurlPair i.μ i.ν i.ρ i.τ p - planeCurlPair i.μ i.ν i.ρ i.τ p) +
    ∑ m, ∑ m', (starRingEnd ℂ) (curlSymbol p i.μ i.ν m) * entry m m' (remainderOp i p) * curlSymbol p i.ρ i.τ m'
private lemma kernelSymbol_sub (i : KernelData Bb C c c' N₁) {p : Mom} (hs : 0 < LinearResponse.sqNorm p) (hl : 0 < coercivity i p) :
    kernelSymbol i p - doubleCurlSymbol i.μ i.ν i.ρ i.τ p = kernelError i p := by
  obtain ⟨hu, h2, -⟩ := fullOp_inverse i hl
  have hG := inverse_eq i hs hu
  have hM : ∀ m m', (symbolWithGradient i.S p)⁻¹ m m' =
      Ring.inverse (LinearResponse.sqNorm p : ℂ) * (if m = m' then 1 else 0) + entry m m' (remainderOp i p) := by
    intro m m'
    refine (entry_matOp m m' (symbolWithGradient i.S p)⁻¹).symm.trans ?_
    rw [← h2, hG, map_add, entry_smul, entry_one]
  unfold kernelSymbol kernelError doubleCurlSymbol
  simp only [hM, mul_add, add_mul, Finset.sum_add_distrib]
  have e1 : (∑ m, ∑ m', (starRingEnd ℂ) (curlSymbol p i.μ i.ν m) *
      (Ring.inverse (LinearResponse.sqNorm p : ℂ) * if m = m' then 1 else 0) * curlSymbol p i.ρ i.τ m') =
      Ring.inverse (LinearResponse.sqNorm p : ℂ) * latticeCurlPair i.μ i.ν i.ρ i.τ p := by
    unfold latticeCurlPair
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  rw [e1]
  have e2 : (∑ m, (starRingEnd ℂ) (planeCurl p i.μ i.ν m) * planeCurl p i.ρ i.τ m) /
      (LinearResponse.sqNorm p : ℂ) = Ring.inverse (LinearResponse.sqNorm p : ℂ) * planeCurlPair i.μ i.ν i.ρ i.τ p := by
    rw [Ring.inverse_eq_inv', div_eq_inv_mul]; rfl
  rw [e2]
  ring
private lemma curlSymbol_contDiff (a b m : Fin 4) : ContDiff ℝ ∞ (fun p : Mom => curlSymbol p a b m) := by
  unfold curlSymbol
  refine contDiff_const.mul (ofReal_comp_contDiff (ContDiff.sub ?_ ?_))
  · split_ifs
    · exact latticeMomentum_contDiff _
    · exact contDiff_const
  · split_ifs
    · exact latticeMomentum_contDiff _
    · exact contDiff_const
private lemma planeCurl_contDiff (a b m : Fin 4) : ContDiff ℝ ∞ (fun p : Mom => planeCurl p a b m) := by
  unfold planeCurl
  refine contDiff_const.mul (ofReal_comp_contDiff (ContDiff.sub ?_ ?_))
  · split_ifs
    · exact contDiff_apply ℝ ℝ _
    · exact contDiff_const
  · split_ifs
    · exact contDiff_apply ℝ ℝ _
    · exact contDiff_const
private lemma conj_comp_contDiff {f : Mom → ℂ} (h : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun p => (starRingEnd ℂ) (f p)) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp h
private lemma abs_ite_le {P : Prop} [Decidable P] {x y : ℝ} (h : |x| ≤ y) (hy : 0 ≤ y) : |if P then x else 0| ≤ y := by
  split_ifs
  · exact h
  · simpa using hy
private lemma norm_curlSymbol_le (a b m : Fin 4) (q : Mom) : ‖curlSymbol q a b m‖ ≤ 2 * ‖q‖ := by
  have h : ∀ e, |latticeMomentum q e| ≤ ‖q‖ := fun e =>
    (abs_chord_le (q e)).trans (by simpa using norm_le_pi_norm q e)
  unfold curlSymbol
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_sub _ _).trans ?_
  have h1 := abs_ite_le (P := m = b) (h a) (norm_nonneg q)
  have h2 := abs_ite_le (P := m = a) (h b) (norm_nonneg q)
  linarith
private lemma norm_planeCurl_le (a b m : Fin 4) (q : Mom) : ‖planeCurl q a b m‖ ≤ 2 * ‖q‖ := by
  have h : ∀ e, |q e| ≤ ‖q‖ := fun e => by simpa using norm_le_pi_norm q e
  unfold planeCurl
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_sub _ _).trans ?_
  have h1 := abs_ite_le (P := m = b) (h a) (norm_nonneg q)
  have h2 := abs_ite_le (P := m = a) (h b) (norm_nonneg q)
  linarith
private lemma hasOrder_curl (m : Fin 4) (π : KernelData Bb C c c' N₁ → Fin 4 × Fin 4) :
    HasOrder (domain Bb C c c' N₁) 1 (fun i p => curlSymbol p (π i).1 (π i).2 m) :=
  hasOrder_one KernelData.cutScale_pos (fun (j : Fin 4 × Fin 4) p => curlSymbol p j.1 j.2 m)
    (fun j => curlSymbol_contDiff _ _ _) π (K := 2) (fun j q => norm_curlSymbol_le _ _ _ q)
private lemma hasOrder_conj_curl (m : Fin 4) (π : KernelData Bb C c c' N₁ → Fin 4 × Fin 4) :
    HasOrder (domain Bb C c c' N₁) 1 (fun i p => (starRingEnd ℂ) (curlSymbol p (π i).1 (π i).2 m)) :=
  hasOrder_one KernelData.cutScale_pos (fun (j : Fin 4 × Fin 4) p => (starRingEnd ℂ) (curlSymbol p j.1 j.2 m))
    (fun j => conj_comp_contDiff (curlSymbol_contDiff _ _ _)) π (K := 2)
    (fun j q => by rw [Complex.norm_conj]; exact norm_curlSymbol_le _ _ _ q)
private lemma hasOrder_planeCurl (m : Fin 4) (π : KernelData Bb C c c' N₁ → Fin 4 × Fin 4) :
    HasOrder (domain Bb C c c' N₁) 1 (fun i p => planeCurl p (π i).1 (π i).2 m) :=
  hasOrder_one KernelData.cutScale_pos (fun (j : Fin 4 × Fin 4) p => planeCurl p j.1 j.2 m)
    (fun j => planeCurl_contDiff _ _ _) π (K := 2) (fun j q => norm_planeCurl_le _ _ _ q)
private lemma hasOrder_conj_planeCurl (m : Fin 4) (π : KernelData Bb C c c' N₁ → Fin 4 × Fin 4) :
    HasOrder (domain Bb C c c' N₁) 1 (fun i p => (starRingEnd ℂ) (planeCurl p (π i).1 (π i).2 m)) :=
  hasOrder_one KernelData.cutScale_pos (fun (j : Fin 4 × Fin 4) p => (starRingEnd ℂ) (planeCurl p j.1 j.2 m))
    (fun j => conj_comp_contDiff (planeCurl_contDiff _ _ _)) π (K := 2)
    (fun j q => by rw [Complex.norm_conj]; exact norm_planeCurl_le _ _ _ q)
private lemma hasOrder_planeCurlPair : HasOrder (domain Bb C c c' N₁) 2 (fun i p => planeCurlPair i.μ i.ν i.ρ i.τ p) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  refine HasOrder.finsetSum hU Finset.univ fun m _ => ?_
  exact HasOrder.bilinear hU (ContinuousLinearMap.mul ℝ ℂ) (hasOrder_conj_planeCurl m fun i => (i.μ, i.ν))
    (hasOrder_planeCurl m fun i => (i.ρ, i.τ))
private lemma conj_I_mul_I_mul (x y : ℝ) : (starRingEnd ℂ) (Complex.I * (x : ℂ)) * (Complex.I * (y : ℂ)) = ((x * y : ℝ) : ℂ) := by
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  have := Complex.I_mul_I
  linear_combination (-(x : ℂ) * y) * this
private lemma abs_ite_prod_sub_le {P1 P2 P3 P4 : Prop} [Decidable P1] [Decidable P2] [Decidable P3] [Decidable P4]
    {x1 x2 x3 x4 y1 y2 y3 y4 κ : ℝ} (hκ : 0 ≤ κ) (h13 : |x1 * x3 - y1 * y3| ≤ κ) (h14 : |x1 * x4 - y1 * y4| ≤ κ)
    (h23 : |x2 * x3 - y2 * y3| ≤ κ) (h24 : |x2 * x4 - y2 * y4| ≤ κ) :
    |((if P1 then x1 else 0) - (if P2 then x2 else 0)) * ((if P3 then x3 else 0) - (if P4 then x4 else 0)) -
      ((if P1 then y1 else 0) - (if P2 then y2 else 0)) * ((if P3 then y3 else 0) - (if P4 then y4 else 0))| ≤ 4 * κ := by
  obtain ⟨a1, a2⟩ := abs_le.mp h13
  obtain ⟨b1, b2⟩ := abs_le.mp h14
  obtain ⟨c1, c2⟩ := abs_le.mp h23
  obtain ⟨d1, d2⟩ := abs_le.mp h24
  rw [abs_le]
  split_ifs <;> constructor <;> nlinarith
private lemma curlPair_sub_bound (a b e f : Fin 4) (q : Mom) : ‖latticeCurlPair a b e f q - planeCurlPair a b e f q‖ ≤ 32 * ‖q‖ ^ 4 := by
  unfold latticeCurlPair planeCurlPair
  rw [← Finset.sum_sub_distrib]
  have h : ∀ m ∈ (Finset.univ : Finset (Fin 4)),
      ‖(starRingEnd ℂ) (curlSymbol q a b m) * curlSymbol q e f m -
        (starRingEnd ℂ) (planeCurl q a b m) * planeCurl q e f m‖ ≤ 8 * ‖q‖ ^ 4 := by
    intro m _
    unfold curlSymbol planeCurl
    rw [conj_I_mul_I_mul, conj_I_mul_I_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hh : ∀ u v : Fin 4, |latticeMomentum q u * latticeMomentum q v - q u * q v| ≤ 2 * ‖q‖ ^ 4 := by
      intro u v
      have hu := norm_le_pi_norm q u
      have hv := norm_le_pi_norm q v
      rw [Real.norm_eq_abs] at hu hv
      exact abs_chord_mul_sub_le (q u) (q v) ‖q‖ hu hv (norm_nonneg _)
    have := abs_ite_prod_sub_le (P1 := m = b) (P2 := m = a) (P3 := m = f) (P4 := m = e)
      (by positivity : 0 ≤ 2 * ‖q‖ ^ 4) (hh a e) (hh a f) (hh b e) (hh b f)
    linarith
  refine (norm_sum_le_of_le _ h).trans ?_
  simp
  linarith
private lemma latticeCurlPair_contDiff (a b e f : Fin 4) : ContDiff ℝ ∞ (latticeCurlPair a b e f) := by
  unfold latticeCurlPair
  exact ContDiff.sum fun m _ => (conj_comp_contDiff (curlSymbol_contDiff _ _ _)).mul (curlSymbol_contDiff _ _ _)
private lemma planeCurlPair_contDiff (a b e f : Fin 4) : ContDiff ℝ ∞ (planeCurlPair a b e f) := by
  unfold planeCurlPair
  exact ContDiff.sum fun m _ => (conj_comp_contDiff (planeCurl_contDiff _ _ _)).mul (planeCurl_contDiff _ _ _)
private lemma hasOrder_curlPair_sub : HasOrder (domain Bb C c c' N₁) 3
    (fun i p => latticeCurlPair i.μ i.ν i.ρ i.τ p - planeCurlPair i.μ i.ν i.ρ i.τ p) := by
  refine hasOrder_three KernelData.cutScale_pos (f := fun i p => latticeCurlPair i.μ i.ν i.ρ i.τ p - planeCurlPair i.μ i.ν i.ρ i.τ p)
    (fun i => (latticeCurlPair_contDiff _ _ _ _).sub (planeCurlPair_contDiff _ _ _ _)) (K := 32) (by norm_num) (fun i q => ?_) fun r => ?_
  · refine (curlPair_sub_bound _ _ _ _ q).trans ?_
    have := i.cutScale_pos
    have h : 0 ≤ i.cutScale ^ 4 := by positivity
    linarith
  · obtain ⟨K, hK⟩ := bound_on_ball
      (fun j : Fin 4 × Fin 4 × Fin 4 × Fin 4 => fun p => latticeCurlPair j.1 j.2.1 j.2.2.1 j.2.2.2 p - planeCurlPair j.1 j.2.1 j.2.2.1 j.2.2.2 p)
      (fun j => (latticeCurlPair_contDiff _ _ _ _).sub (planeCurlPair_contDiff _ _ _ _)) 4 r
    exact ⟨K, fun i q hq => hK (i.μ, i.ν, i.ρ, i.τ) q hq⟩
include hc hc' hN1 in
private lemma hasOrder_kernelError : HasOrder (domain Bb C c c' N₁) 1 (kernelError (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  have h1 := HasOrder.bilinear hU (ContinuousLinearMap.mul ℝ ℂ) hasOrder_inv_sqNorm hasOrder_curlPair_sub
  have h2 : HasOrder (domain Bb C c c' N₁) 1 (fun i p => ∑ m, ∑ m', (starRingEnd ℂ) (curlSymbol p i.μ i.ν m) *
      entry m m' (remainderOp i p) * curlSymbol p i.ρ i.τ m') := by
    refine HasOrder.finsetSum hU Finset.univ fun m _ => HasOrder.finsetSum hU Finset.univ fun m' _ => ?_
    have a1 := HasOrder.bilinear hU (ContinuousLinearMap.mul ℝ ℂ) (hasOrder_conj_curl m fun i => (i.μ, i.ν))
      ((hasOrder_remainderOp hc' hc hN1).clm_comp hU (entry m m'))
    have a2 := HasOrder.bilinear hU (ContinuousLinearMap.mul ℝ ℂ) a1 (hasOrder_curl m' fun i => (i.ρ, i.τ))
    exact a2
  have h3 := HasOrder.add hU (a := 1) h1 h2
  exact h3
private def innerBump : ContDiffBump (0 : Mom) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
private def outerBump : ContDiffBump (0 : Mom) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
private def innerCut (p : Mom) : ℂ := ((innerBump p : ℝ) : ℂ)
private lemma innerBump_eq_one {p : Mom} (h : ‖p‖ ≤ 1 / 4) : innerBump p = 1 :=
  innerBump.one_of_mem_closedBall (by simpa [innerBump, dist_eq_norm] using h)
private lemma innerBump_eq_zero {p : Mom} (h : 1 / 2 ≤ ‖p‖) : innerBump p = 0 :=
  innerBump.zero_of_le_dist (by simpa [innerBump, dist_eq_norm] using h)
private lemma outerBump_eq_one {p : Mom} (h : ‖p‖ ≤ 1 / 2) : outerBump p = 1 :=
  outerBump.one_of_mem_closedBall (by simpa [outerBump, dist_eq_norm] using h)
private lemma outerBump_eq_zero {p : Mom} (h : 1 ≤ ‖p‖) : outerBump p = 0 :=
  outerBump.zero_of_le_dist (by simpa [outerBump, dist_eq_norm] using h)
private lemma innerCut_contDiff : ContDiff ℝ ∞ innerCut := ofReal_comp_contDiff innerBump.contDiff
private lemma hasOrder_one_sub_innerCut : HasOrder (domain Bb C c c' N₁) 1 (fun _ p => 1 - innerCut p) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  have hs : ContDiff ℝ ∞ (fun p => 1 - innerCut p) := contDiff_const.sub innerCut_contDiff
  refine HasOrder.of_bounded hU (fun i => hs.contDiffOn) (fun r => ?_) (fun r hr => ?_)
  · obtain ⟨Kb, h⟩ := bound_on_ball (J := Unit) (fun _ p => 1 - innerCut p) (fun _ => hs) 4 r
    exact ⟨Kb, fun i p hp => h () p (hU.norm_le i p hp)⟩
  · obtain rfl : r = 0 := by omega
    refine ⟨8, fun i p hp => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    have e : ‖p‖ ^ ((1 : ℤ) - ((0 : ℕ) : ℤ)) = ‖p‖ := by norm_num
    rw [e]
    rcases le_or_gt ‖p‖ (1 / 4) with h | h
    · simp [innerCut, innerBump_eq_one h]
    · have h0 := innerBump.nonneg (x := p)
      have h1 := innerBump.le_one (x := p)
      have e2 : 1 - innerCut p = ((1 - innerBump p : ℝ) : ℂ) := by simp [innerCut]
      show ‖1 - innerCut p‖ ≤ _
      rw [e2, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
private lemma hasOrder_doubleCurl : HasOrder (domain Bb C c c' N₁) 0 (fun i p => doubleCurlSymbol i.μ i.ν i.ρ i.τ p) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  have h := HasOrder.bilinear hU (ContinuousLinearMap.mul ℝ ℂ) hasOrder_inv_sqNorm hasOrder_planeCurlPair
  refine HasOrder.congr_on hU (a := 0) h fun i p _ => ?_
  simp only [ContinuousLinearMap.mul_apply']
  unfold doubleCurlSymbol
  rw [Ring.inverse_eq_inv', div_eq_inv_mul]
  rfl
private def scaledCut (N : ℕ) (p : Mom) : ℂ := ((outerBump ((N : ℝ) • p) : ℝ) : ℂ)
private lemma hasOrder_scaledCut : HasOrder (domain Bb C c c' N₁) 0 (fun i => scaledCut i.N) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  let ψc : Mom → ℂ := fun x => ((outerBump x : ℝ) : ℂ)
  have hψ : ContDiff ℝ ∞ ψc := ofReal_comp_contDiff outerBump.contDiff
  let L : ℕ → Mom →L[ℝ] Mom := fun N => (N : ℝ) • ContinuousLinearMap.id ℝ Mom
  have hcomp : ∀ N : ℕ, scaledCut N = ψc ∘ L N := fun N => rfl
  have hLn : ∀ N : ℕ, ‖L N‖ ≤ N := by
    intro N
    show ‖(N : ℝ) • ContinuousLinearMap.id ℝ Mom‖ ≤ _
    refine (norm_smul_le (N : ℝ) (ContinuousLinearMap.id ℝ Mom)).trans ?_
    have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Mom)
    simp only [Real.norm_natCast]
    have h0 : (0 : ℝ) ≤ N := by positivity
    nlinarith
  refine ⟨fun i => ((hψ.comp (L i.N).contDiff)).contDiffOn, fun r => ?_⟩
  obtain ⟨Kc, hKc⟩ := bound_on_ball (J := Unit) (fun _ => ψc) (fun _ => hψ) 1 r
  refine ⟨|Kc|, fun i p hp => ?_⟩
  have hw := hU.norm_pos i p hp
  have hN : (0 : ℝ) < i.N := i.size_pos
  show ‖iteratedFDeriv ℝ r (scaledCut i.N) p‖ ≤ _
  rw [hcomp]
  have hle : (r : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  rw [(L i.N).iteratedFDeriv_comp_right hψ p hle]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : (∏ _j : Fin r, ‖L i.N‖) ≤ (i.N : ℝ) ^ r := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) (hLn i.N) r
  have hzp : ‖p‖ ^ ((0 : ℤ) - (r : ℤ)) = (‖p‖ ^ r)⁻¹ := by
    rw [zero_sub, zpow_neg, zpow_natCast]
  rw [hzp]
  have hLp : ‖L i.N p‖ = i.N * ‖p‖ := by
    simp [L, norm_smul]
  rcases le_or_gt ‖L i.N p‖ 1 with h | h
  · have h1 := hKc () (L i.N p) h
    have h2 : (i.N : ℝ) ^ r ≤ (‖p‖ ^ r)⁻¹ := by
      rw [← inv_pow]
      refine pow_le_pow_left₀ hN.le ?_ r
      rw [hLp] at h
      rw [le_inv_comm₀ hN hw, inv_eq_one_div, le_div_iff₀ hN]
      linarith
    exact mul_le_mul (h1.trans (le_abs_self _)) (hprod.trans h2) (Finset.prod_nonneg fun _ _ => norm_nonneg _) (abs_nonneg _)
  · have hev : ψc =ᶠ[𝓝 (L i.N p)] fun _ => (0 : ℂ) := by
      have : ∀ᶠ y : Mom in 𝓝 (L i.N p), 1 < ‖y‖ := continuous_norm.continuousAt.eventually (lt_mem_nhds h)
      filter_upwards [this] with y hy
      simp [ψc, outerBump_eq_zero hy.le]
    rw [(hev.iteratedFDeriv ℝ r).eq_of_nhds]
    have h0 : iteratedFDeriv ℝ r (fun _ : Mom => (0 : ℂ)) (L i.N p) = 0 := by
      rw [iteratedFDeriv_zero_fun]
      rfl
    rw [h0]
    simp only [norm_zero, zero_mul]
    positivity
private def localPart (i : KernelData Bb C c c' N₁) (p : Mom) : ℂ :=
  (1 - scaledCut i.N p) * (kernelError i p + (1 - innerCut p) * doubleCurlSymbol i.μ i.ν i.ρ i.τ p)
include hc hc' hN1 in
private lemma hasOrder_localPart : HasOrder (domain Bb C c c' N₁) 1 (localPart (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)) := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  have h1 := HasOrder.bilinear hU (ContinuousLinearMap.mul ℝ ℂ) hasOrder_one_sub_innerCut hasOrder_doubleCurl
  have h2 := HasOrder.add hU (a := 1) (hasOrder_kernelError hc' hc hN1) h1
  have h3 := (HasOrder.const _ hU (1 : ℂ)).sub hU hasOrder_scaledCut
  have h4 := HasOrder.bilinear hU (ContinuousLinearMap.mul ℝ ℂ) h3 h2
  exact h4
end Family
private def flipSign (k m : Fin 4) : ℂ := if m = k then -1 else 1
private lemma flipSign_mul_self (k m : Fin 4) : flipSign k m * flipSign k m = 1 := by
  unfold flipSign; split_ifs <;> simp
private lemma conj_flipSign (k m : Fin 4) : (starRingEnd ℂ) (flipSign k m) = flipSign k m := by
  unfold flipSign; split_ifs <;> simp
private def shiftSign (i : KernelData Bb C c c' N₁) (k : Fin 4) : ℂ := flipSign k i.μ * flipSign k i.ν * flipSign k i.ρ * flipSign k i.τ
private lemma shiftSign_mul_self (i : KernelData Bb C c c' N₁) (k : Fin 4) : shiftSign i k * shiftSign i k = 1 := by
  unfold shiftSign
  have h1 := flipSign_mul_self k i.μ
  have h2 := flipSign_mul_self k i.ν
  have h3 := flipSign_mul_self k i.ρ
  have h4 := flipSign_mul_self k i.τ
  calc _ = (flipSign k i.μ * flipSign k i.μ) * (flipSign k i.ν * flipSign k i.ν) * (flipSign k i.ρ * flipSign k i.ρ) *
        (flipSign k i.τ * flipSign k i.τ) := by ring
    _ = 1 := by rw [h1, h2, h3, h4]; ring
private lemma shiftSign_ne_zero (i : KernelData Bb C c c' N₁) (k : Fin 4) : shiftSign i k ≠ 0 := fun h => by
  have := shiftSign_mul_self i k
  rw [h] at this
  simp at this
private def realFlip (k m : Fin 4) : ℝ := if m = k then -1 else 1
private lemma realFlip_mul_self (k m : Fin 4) : realFlip k m * realFlip k m = 1 := by
  unfold realFlip; split_ifs <;> simp
private lemma flipSign_eq (k m : Fin 4) : flipSign k m = (realFlip k m : ℂ) := by
  unfold flipSign realFlip; split_ifs <;> simp
private lemma latticeMomentum_add_single (p : Mom) (k m : Fin 4) :
    latticeMomentum (p + Pi.single k (2 * Real.pi)) m = realFlip k m * latticeMomentum p m := by
  unfold latticeMomentum realFlip
  by_cases h : m = k
  · subst h
    have : (p m + 2 * Real.pi) / 2 = p m / 2 + Real.pi := by ring
    simp [this, Real.sin_add_pi]
  · simp [h]
private lemma curlSymbol_add_single (p : Mom) (k a b m : Fin 4) :
    curlSymbol (p + Pi.single k (2 * Real.pi)) a b m = flipSign k a * flipSign k b * flipSign k m * curlSymbol p a b m := by
  have hσ := realFlip_mul_self k
  have hr : ((if m = b then latticeMomentum (p + Pi.single k (2 * Real.pi)) a else 0) -
      (if m = a then latticeMomentum (p + Pi.single k (2 * Real.pi)) b else 0) : ℝ) =
      realFlip k a * realFlip k b * realFlip k m * ((if m = b then latticeMomentum p a else 0) -
        (if m = a then latticeMomentum p b else 0)) := by
    rw [latticeMomentum_add_single, latticeMomentum_add_single]
    by_cases h1 : m = b <;> by_cases h2 : m = a
    · subst h1; subst h2; simp
    · subst h1
      simp only [if_true, if_neg h2, sub_zero]
      linear_combination (-(realFlip k a) * latticeMomentum p a) * hσ m
    · subst h2
      simp only [if_true, if_neg h1, zero_sub]
      linear_combination (realFlip k b * latticeMomentum p b) * hσ m
    · simp [h1, h2]
  unfold curlSymbol
  rw [hr, flipSign_eq, flipSign_eq, flipSign_eq]
  push_cast
  ring
private def flipMatrix (k : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal (flipSign k)
private lemma flipMatrix_inv (k : Fin 4) : (flipMatrix k)⁻¹ = flipMatrix k := by
  apply Matrix.inv_eq_right_inv
  rw [flipMatrix, Matrix.diagonal_mul_diagonal]
  simp [flipSign_mul_self, Matrix.diagonal_one]
private lemma periodShiftSign_eq (k a b : Fin 4) : periodShiftSign k a b = flipSign k a * flipSign k b := by
  unfold periodShiftSign flipSign
  simp only [@eq_comm _ k a, @eq_comm _ k b]
  by_cases h1 : a = k <;> by_cases h2 : b = k <;> simp [h1, h2] <;> norm_num
private lemma symbolWithGradient_add_single (i : KernelData Bb C c c' N₁) (p : Mom) (k : Fin 4) :
    symbolWithGradient i.S (p + Pi.single k (2 * Real.pi)) = flipMatrix k * symbolWithGradient i.S p * flipMatrix k := by
  ext a b
  rw [flipMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [symbolWithGradient]
  rw [i.hasLow.periodic_shift p k a b, periodShiftSign_eq, latticeMomentum_add_single, latticeMomentum_add_single, flipSign_eq, flipSign_eq]
  push_cast
  ring
private lemma kernelSymbol_add_single (i : KernelData Bb C c c' N₁) (p : Mom) (k : Fin 4) :
    kernelSymbol i (p + Pi.single k (2 * Real.pi)) = shiftSign i k * kernelSymbol i p := by
  have hinv : (symbolWithGradient i.S (p + Pi.single k (2 * Real.pi)))⁻¹ =
      flipMatrix k * ((symbolWithGradient i.S p)⁻¹ * flipMatrix k) := by
    rw [symbolWithGradient_add_single, Matrix.mul_inv_rev, Matrix.mul_inv_rev, flipMatrix_inv]
  have hent : ∀ m m', (symbolWithGradient i.S (p + Pi.single k (2 * Real.pi)))⁻¹ m m' =
      flipSign k m * (symbolWithGradient i.S p)⁻¹ m m' * flipSign k m' := by
    intro m m'
    rw [hinv, flipMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  unfold kernelSymbol shiftSign
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [hent, curlSymbol_add_single, curlSymbol_add_single, map_mul, map_mul, map_mul, conj_flipSign, conj_flipSign, conj_flipSign]
  have hu := flipSign_mul_self k m
  have hv := flipSign_mul_self k m'
  generalize (starRingEnd ℂ) (curlSymbol p i.μ i.ν m) = X
  generalize (symbolWithGradient i.S p)⁻¹ m m' = G
  generalize curlSymbol p i.ρ i.τ m' = W
  calc _ = flipSign k i.μ * flipSign k i.ν * flipSign k i.ρ * flipSign k i.τ * (X * G * W) *
        (flipSign k m * flipSign k m) * (flipSign k m' * flipSign k m') := by ring
    _ = _ := by rw [hu, hv]; ring
private lemma exp_two_pi_half_int {z : ℝ} {w n : ℤ} (hz : z = w + (n : ℝ) / 2) :
    Complex.exp (Complex.I * ((2 * Real.pi * z : ℝ) : ℂ)) = (-1 : ℂ) ^ n := by
  have e : Complex.I * ((2 * Real.pi * z : ℝ) : ℂ) = ((2 * w + n : ℤ) : ℂ) * (Real.pi * Complex.I) := by
    rw [hz]
    push_cast
    ring
  rw [e, Complex.exp_int_mul, Complex.exp_pi_mul_I, zpow_add₀ (by norm_num), zpow_mul]
  simp
private lemma neg_one_zpow_ite {P1 P2 P3 P4 : Prop} [Decidable P1] [Decidable P2] [Decidable P3] [Decidable P4] :
    (-1 : ℂ) ^ ((if P1 then 1 else 0) + (if P2 then 1 else 0) - (if P3 then 1 else 0) - (if P4 then 1 else 0) : ℤ) =
      (if P3 then -1 else 1) * (if P4 then -1 else 1) * (if P1 then -1 else 1) * (if P2 then -1 else 1) := by
  split_ifs <;> norm_num
private lemma abs_wrapAngle_le (x : ℝ) : |wrapAngle x| ≤ Real.pi := by
  have h := abs_sub_round (x / (2 * Real.pi))
  have e : wrapAngle x = (2 * Real.pi) * (x / (2 * Real.pi) - round (x / (2 * Real.pi))) := by
    unfold wrapAngle; field_simp
  rw [e, abs_mul, abs_of_pos twoPi_pos]
  nlinarith [Real.pi_pos]
private lemma chord_sq (t : ℝ) : chord t ^ 2 = 2 - 2 * Real.cos t := by
  unfold chord
  rw [mul_pow, Real.sin_sq_eq_half_sub]
  have : 2 * (t / 2) = t := by ring
  rw [this]
  ring
private lemma chord_wrapAngle_sq (x : ℝ) : chord (wrapAngle x) ^ 2 = chord x ^ 2 := by
  rw [chord_sq, chord_sq]
  have : wrapAngle x = x - round (x / (2 * Real.pi)) * (2 * Real.pi) := by unfold wrapAngle; ring
  rw [this, Real.cos_sub_int_mul_two_pi]
private def wrapVec (p : Mom) : Mom := fun i => wrapAngle (p i)
private lemma norm_wrapVec_le (p : Mom) : ‖wrapVec p‖ ≤ Real.pi := by
  rw [pi_norm_le_iff_of_nonneg Real.pi_pos.le]
  intro i
  exact abs_wrapAngle_le (p i)
private lemma coercivity_wrapVec (i : KernelData Bb C c c' N₁) (p : Mom) : coercivity i (wrapVec p) = coercivity i p := by
  unfold coercivity
  congr 2
  unfold LinearResponse.sqNorm
  refine Finset.sum_congr rfl fun j _ => ?_
  exact chord_wrapAngle_sq (p j)
private lemma wrapAngle_eventually {p : Mom} (h : ∀ i, |wrapAngle (p i)| < 3) :
    ∀ᶠ q : Mom in 𝓝 p, ∀ i, wrapAngle (q i) = q i - 2 * Real.pi * round (p i / (2 * Real.pi)) := by
  have hpi := Real.pi_gt_d2
  rw [Filter.eventually_all]
  intro i
  have hc : Continuous fun q : Mom => |q i - 2 * Real.pi * round (p i / (2 * Real.pi))| := by fun_prop
  have hev := hc.continuousAt.eventually (gt_mem_nhds (h i))
  filter_upwards [hev] with q hq
  have : round (q i / (2 * Real.pi)) = round (p i / (2 * Real.pi)) := by
    apply round_eq_of_abs_lt
    have e : q i / (2 * Real.pi) - (round (p i / (2 * Real.pi)) : ℝ) =
        (q i - 2 * Real.pi * round (p i / (2 * Real.pi))) / (2 * Real.pi) := by field_simp
    rw [e, abs_div, abs_of_pos twoPi_pos, div_lt_iff₀ twoPi_pos]
    linarith
  simp only [wrapAngle, this]
private lemma periodize_eventually_one {Θ : Mom → ℂ} {p : Mom} {δ : ℝ} (hδ : δ ≤ 1) (h : ‖wrapVec p‖ < δ)
    (hΘ : ∀ x, ‖x‖ < δ → Θ x = 1) : ∀ᶠ q : Mom in 𝓝 p, periodize (fun _ => 1) Θ q = 1 := by
  have h3 : ∀ i, |wrapAngle (p i)| < 3 := fun i => by
    have := norm_le_pi_norm (wrapVec p) i
    rw [Real.norm_eq_abs] at this
    have h4 : |wrapAngle (p i)| = |wrapVec p i| := rfl
    linarith
  have hn := wrapAngle_eventually h3
  set g : Mom → Mom := fun q i => q i - 2 * Real.pi * round (p i / (2 * Real.pi)) with hg
  have hgc : Continuous g := by
    rw [hg]; fun_prop
  have hgp : g p = wrapVec p := rfl
  have hev : ∀ᶠ q : Mom in 𝓝 p, ‖g q‖ < δ :=
    (continuous_norm.comp hgc).continuousAt.eventually (gt_mem_nhds (by simpa [hgp] using h))
  filter_upwards [hn, hev] with q h1 h2
  have e : (fun i => wrapAngle (q i)) = g q := funext h1
  simp [periodize, e, hΘ _ h2]
private lemma sqNorm_latticeMomentum_continuous : Continuous (fun p : Mom => LinearResponse.sqNorm (latticeMomentum p)) := by
  unfold LinearResponse.sqNorm
  exact continuous_finset_sum _ fun i _ => ((latticeMomentum_contDiff i).continuous).pow 2
private lemma fullOp_contDiff (i : KernelData Bb C c c' N₁) : ContDiff ℝ ∞ (fullOp i) := by
  unfold fullOp
  refine ((ofReal_comp_contDiff sqNorm_contDiff).smul contDiff_const).add ?_
  unfold defectOp
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ => (i.defect_contDiff a b).smul contDiff_const
private lemma kernelSymbol_contDiffAt (i : KernelData Bb C c c' N₁) {p : Mom} (h : 0 < coercivity i p) : ContDiffAt ℝ ∞ (kernelSymbol i) p := by
  have hW : IsOpen {q | 0 < coercivity i q} := by
    apply isOpen_lt continuous_const
    unfold coercivity
    exact (continuous_const.mul sqNorm_latticeMomentum_continuous).sub continuous_const
  have hev : kernelSymbol i =ᶠ[𝓝 p] fun q => ∑ m, ∑ m', (starRingEnd ℂ) (curlSymbol q i.μ i.ν m) *
      entry m m' (Ring.inverse (fullOp i q)) * curlSymbol q i.ρ i.τ m' := by
    filter_upwards [hW.mem_nhds h] with q hq
    unfold kernelSymbol
    obtain ⟨-, h2, -⟩ := fullOp_inverse i hq
    simp only [h2, entry_matOp]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨u, hu⟩ := (fullOp_inverse i h).1
  have hinv : ContDiffAt ℝ ∞ (fun q => Ring.inverse (fullOp i q)) p := by
    have h2 : ContDiffAt ℝ ∞ Ring.inverse (fullOp i p) := by
      rw [← hu]; exact contDiffAt_ringInverse ℝ u
    exact h2.comp p (fullOp_contDiff i).contDiffAt
  refine ContDiffAt.sum fun m _ => ContDiffAt.sum fun m' _ => ?_
  refine ((conj_comp_contDiff (curlSymbol_contDiff _ _ _)).contDiffAt.mul ?_).mul (curlSymbol_contDiff _ _ _).contDiffAt
  exact (entry m m').contDiff.contDiffAt.comp p hinv
private lemma scaledCut_contDiff (N : ℕ) : ContDiff ℝ ∞ (scaledCut N) :=
  ofReal_comp_contDiff (outerBump.contDiff.comp (by fun_prop : ContDiff ℝ ∞ (fun p : Mom => (N : ℝ) • p)))
private lemma scaledCut_eq_zero {N : ℕ} {p : Mom} (h : 1 ≤ (N : ℝ) * ‖p‖) : scaledCut N p = 0 := by
  have : outerBump ((N : ℝ) • p) = 0 := outerBump_eq_zero (by
    rw [norm_smul, Real.norm_natCast]; exact h)
  simp [scaledCut, this]
private lemma scaledCut_eq_one {N : ℕ} {p : Mom} (h : (N : ℝ) * ‖p‖ ≤ 1 / 2) : scaledCut N p = 1 := by
  have : outerBump ((N : ℝ) • p) = 1 := outerBump_eq_one (by
    rw [norm_smul, Real.norm_natCast]; exact h)
  simp [scaledCut, this]
private def cutDoubleCurl (i : KernelData Bb C c c' N₁) (p : Mom) : ℂ :=
  (1 - scaledCut i.N p) * innerCut p * doubleCurlSymbol i.μ i.ν i.ρ i.τ p
private lemma doubleCurl_contDiffAt (a b e f : Fin 4) {p : Mom} (h : 0 < ‖p‖) : ContDiffAt ℝ ∞ (doubleCurlSymbol a b e f) p := by
  have hs := sqNorm_pos h
  have h2 : ContDiffAt ℝ ∞ (fun p => (LinearResponse.sqNorm p : ℂ)) p := (ofReal_comp_contDiff sqNorm_contDiff).contDiffAt
  have hcc : doubleCurlSymbol a b e f = fun p => planeCurlPair a b e f p * ((LinearResponse.sqNorm p : ℂ))⁻¹ := by
    funext q
    exact div_eq_mul_inv _ _
  rw [hcc]
  exact (planeCurlPair_contDiff a b e f).contDiffAt.mul (h2.inv (by exact_mod_cast hs.ne'))
private lemma one_le_size_mul_norm (i : KernelData Bb C c c' N₁) {p : Mom} (h : 1 / 2 ≤ ‖p‖) : 1 ≤ (i.N : ℝ) * ‖p‖ := by
  have : (2 : ℝ) ≤ i.N := by exact_mod_cast i.two_le_N
  nlinarith
private lemma cutDoubleCurl_eq_zero (i : KernelData Bb C c c' N₁) {p : Mom} (h : 1 / 2 ≤ ‖p‖) : cutDoubleCurl i p = 0 := by
  simp [cutDoubleCurl, innerCut, innerBump_eq_zero h]
private lemma cutDoubleCurl_contDiff (i : KernelData Bb C c c' N₁) : ContDiff ℝ ∞ (cutDoubleCurl i) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases h : (i.N : ℝ) * ‖p‖ < 1 / 2
  · have hc : Continuous fun q : Mom => (i.N : ℝ) * ‖q‖ := by fun_prop
    have hev := hc.continuousAt.eventually (gt_mem_nhds h)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    simp [cutDoubleCurl, scaledCut_eq_one hq.le]
  · have hp : 0 < ‖p‖ := by
      by_contra h0
      have : ‖p‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
      rw [this] at h
      norm_num at h
    exact ((contDiff_const.sub (scaledCut_contDiff i.N)).contDiffAt.mul innerCut_contDiff.contDiffAt).mul
      (doubleCurl_contDiffAt _ _ _ _ hp)
private def periodicPart (i : KernelData Bb C c c' N₁) (p : Mom) : ℂ :=
  (1 - periodize (fun _ => 1) (scaledCut i.N) p) * kernelSymbol i p - periodize (shiftSign i) (cutDoubleCurl i) p
private lemma periodicPart_eq_near (i : KernelData Bb C c c' N₁) {p : Mom} (hp : ‖p‖ < 7 / 2) :
    periodicPart i p = (1 - scaledCut i.N p) * kernelSymbol i p - cutDoubleCurl i p := by
  unfold periodicPart
  rw [periodize_eq_self _ (fun x hx => scaledCut_eq_zero (one_le_size_mul_norm i hx)) hp, periodize_eq_self _ (fun x hx => cutDoubleCurl_eq_zero i hx) hp]
section Final
variable (hc' : 0 < c') (hc : 0 < c) (hN1 : 768 * |C| / (c' ^ 3 * c) ≤ N₁)
include hc hc' hN1 in
private lemma cutKernel_contDiff (i : KernelData Bb C c c' N₁) :
    ContDiff ℝ ∞ (fun p => (1 - periodize (fun _ => 1) (scaledCut i.N) p) * kernelSymbol i p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hN := i.size_pos
  have hN2 : (2 : ℝ) ≤ i.N := by exact_mod_cast i.two_le_N
  have hps : ContDiff ℝ ∞ (periodize (fun _ => 1) (scaledCut i.N)) :=
    periodize_contDiff _ (scaledCut_contDiff _) (fun x hx => scaledCut_eq_zero (one_le_size_mul_norm i hx))
  set δ : ℝ := 1 / (2 * (i.N : ℝ)) with hδ
  by_cases h : ‖wrapVec p‖ < δ
  · have h1 : δ ≤ 1 := by
      rw [hδ, div_le_one (by positivity)]
      linarith
    have hev := periodize_eventually_one (Θ := scaledCut i.N) h1 h (fun x hx => scaledCut_eq_one (by
      rw [hδ, lt_div_iff₀ (by positivity)] at hx
      nlinarith))
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    simp [hq]
  · have hn : i.cutScale ≤ ‖wrapVec p‖ := by
      have : i.cutScale ≤ δ := by
        unfold KernelData.cutScale
        rw [hδ]
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      linarith [not_lt.mp h]
    have hpi := Real.pi_lt_d2
    have hl := coercivity_ge hc' hc hN1 i hn (by linarith [norm_wrapVec_le p])
    have hw : 0 < ‖wrapVec p‖ := lt_of_lt_of_le i.cutScale_pos hn
    have hlp : 0 < coercivity i p := by
      rw [← coercivity_wrapVec]
      exact lt_of_lt_of_le (by positivity) hl
    exact (contDiff_const.sub hps).contDiffAt.mul (kernelSymbol_contDiffAt i hlp)
include hc hc' hN1 in
private lemma periodicPart_contDiff (i : KernelData Bb C c c' N₁) : ContDiff ℝ ∞ (periodicPart i) :=
  (cutKernel_contDiff hc' hc hN1 i).sub (periodize_contDiff _ (cutDoubleCurl_contDiff i) (fun x hx => cutDoubleCurl_eq_zero i hx))
private lemma periodicPart_add_single (i : KernelData Bb C c c' N₁) (p : Mom) (k : Fin 4) :
    periodicPart i (p + Pi.single k (2 * Real.pi)) * shiftSign i k = periodicPart i p := by
  unfold periodicPart
  rw [periodize_add_single _ (fun _ => one_ne_zero), periodize_add_single _ (shiftSign_ne_zero i), kernelSymbol_add_single]
  have := shiftSign_mul_self i k
  linear_combination ((1 - 1 * periodize (fun _ => 1) (scaledCut i.N) p) * kernelSymbol i p - periodize (shiftSign i) (cutDoubleCurl i) p) * this +
    0 * this
include hc hc' hN1 in
private lemma periodicPart_eq_localPart (i : KernelData Bb C c c' N₁) {p : Mom} (hp : p ∈ domain Bb C c c' N₁ i) : periodicPart i p = localPart i p := by
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  have hw := hU.norm_pos i p hp
  have hs := sqNorm_pos hw
  have hl : 0 < coercivity i p := lt_of_lt_of_le (by positivity) (coercivity_ge hc' hc hN1 i hp.1.le hp.2)
  have hT := kernelSymbol_sub i hs hl
  rw [periodicPart_eq_near i hp.2]
  have e : kernelSymbol i p = kernelError i p + doubleCurlSymbol i.μ i.ν i.ρ i.τ p := by rw [← hT]; ring
  unfold cutDoubleCurl localPart
  rw [e]
  ring
private lemma periodicPart_eq_zero_low (i : KernelData Bb C c c' N₁) {q : Mom} (h : (i.N : ℝ) * ‖q‖ ≤ 1 / 2) : periodicPart i q = 0 := by
  have hN2 : (2 : ℝ) ≤ i.N := by exact_mod_cast i.two_le_N
  rw [periodicPart_eq_near i (by nlinarith [norm_nonneg q])]
  simp [cutDoubleCurl, scaledCut_eq_one h]
end Final
private lemma norm_zpow_le_sqNorm_rpow {p : Mom} (h : 0 < ‖p‖) (r : ℕ) :
    ‖p‖ ^ ((1 : ℤ) - r) ≤ 2 ^ r * LinearResponse.sqNorm p ^ ((1 - (r : ℝ)) / 2) := by
  have hs := sqNorm_pos h
  set y := Real.sqrt (LinearResponse.sqNorm p) with hy
  have hy0 : 0 < y := Real.sqrt_pos.mpr hs
  have hy2 : LinearResponse.sqNorm p = y ^ 2 := (Real.sq_sqrt hs.le).symm
  have h1 : ‖p‖ ≤ y := Real.le_sqrt_of_sq_le (norm_sq_le_sqNorm p)
  have h2 : y ≤ 2 * ‖p‖ := by
    have : y ^ 2 ≤ (2 * ‖p‖) ^ 2 := by
      rw [← hy2]
      have := sqNorm_le_four_mul_norm_sq p
      nlinarith
    exact (pow_le_pow_iff_left₀ hy0.le (by positivity) two_ne_zero).mp this
  have e : LinearResponse.sqNorm p ^ ((1 - (r : ℝ)) / 2) = y ^ (1 - (r : ℝ)) := by
    rw [hy2, ← Real.rpow_natCast y 2, ← Real.rpow_mul hy0.le]
    congr 1
    push_cast
    ring
  rw [e]
  cases r with
  | zero =>
    simpa using h1
  | succ n =>
    have e1 : ((1 : ℤ) - ((n + 1 : ℕ) : ℤ)) = -(n : ℤ) := by push_cast; ring
    have e2 : (1 - ((n + 1 : ℕ) : ℝ)) = -(n : ℝ) := by push_cast; ring
    rw [e1, e2, zpow_neg, zpow_natCast, Real.rpow_neg hy0.le, Real.rpow_natCast]
    have h3 : y ^ n ≤ 2 ^ n * ‖p‖ ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hy0.le h2 n
    have h5 : 0 < ‖p‖ ^ n := by positivity
    have h6 : (‖p‖ ^ n)⁻¹ ≤ 2 ^ n * (y ^ n)⁻¹ := by
      rw [inv_le_comm₀ h5 (by positivity), mul_inv, inv_inv]
      rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      linarith
    have h7 : (0 : ℝ) ≤ (y ^ n)⁻¹ := by positivity
    calc (‖p‖ ^ n)⁻¹ ≤ 2 ^ n * (y ^ n)⁻¹ := h6
      _ ≤ 2 ^ (n + 1) * (y ^ n)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ h7
        exact pow_le_pow_right₀ (by norm_num) (by omega)
private lemma dualMomentum_bounds {N : ℕ} [NeZero N] {j : TorusFields.TorusSite N} (hN : 2 ≤ N) (hj : j ≠ 0) :
    (∀ i, |dualMomentum j i| ≤ Real.pi) ∧ 1 ≤ (N : ℝ) * ‖dualMomentum j‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have e : ∀ i, dualMomentum j i = 2 * Real.pi * ((j i).valMinAbs : ℝ) / N := fun i => rfl
  constructor
  · intro i
    have h := ZMod.valMinAbs_mem_Ioc (j i)
    have h1 : -(N : ℤ) < (j i).valMinAbs * 2 := h.1
    have h2 : (j i).valMinAbs * 2 ≤ N := h.2
    have h3 : |(((j i).valMinAbs : ℤ) : ℝ)| * 2 ≤ N := by
      have : |(j i).valMinAbs| * 2 ≤ (N : ℤ) := by
        rcases abs_cases (j i).valMinAbs with ⟨h4, _⟩ | ⟨h4, _⟩ <;> rw [h4] <;> omega
      exact_mod_cast this
    rw [e, abs_div, abs_mul, abs_of_pos twoPi_pos, abs_of_pos hN0, div_le_iff₀ hN0]
    nlinarith [Real.pi_pos]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hj
    have h1 : (j i).valMinAbs ≠ 0 := fun h => hi ((ZMod.valMinAbs_eq_zero _).mp h)
    have h2 : (1 : ℝ) ≤ |(((j i).valMinAbs : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |(j i).valMinAbs| := Int.one_le_abs h1
      exact_mod_cast this
    have h3 := norm_le_pi_norm (dualMomentum j) i
    rw [Real.norm_eq_abs, e, abs_div, abs_mul, abs_of_pos twoPi_pos, abs_of_pos hN0, div_le_iff₀ hN0] at h3
    have := Real.pi_gt_three
    nlinarith
private lemma flipSign_eq_ite (k m : Fin 4) : flipSign k m = if k = m then -1 else 1 := by
  simp only [flipSign, eq_comm]
end LowSymbolKernel
open LowSymbolKernel in
theorem lowSymbolKernelStatement_holds (h₁ : orderOneMomentumSumStatement)
    (h₂ : curlCurlMomentumSumStatement) : lowSymbolKernelStatement := by
  intro Bb C c c' hc hc'
  set N₁ : ℝ := 768 * |C| / (c' ^ 3 * c) with hN₁
  have hN1 : 768 * |C| / (c' ^ 3 * c) ≤ N₁ := le_rfl
  have ho := hasOrder_localPart (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁) hc' hc hN1
  have hbd := ho.bound
  choose Kb hKb using hbd
  set B' : ℕ → ℝ := fun r => 2 ^ r * |Kb r| with hB'
  obtain ⟨C₁, N₀₁, m1⟩ := h₁ B'
  obtain ⟨C₂, N₀₂, m2⟩ := h₂ (fun p => innerBump p) innerBump.contDiff
    (by filter_upwards [innerBump.eventuallyEq_one] with p hp; simpa using hp)
    (fun p hp => innerBump_eq_zero (by
      have := sqNorm_le_four_mul_norm_sq p
      nlinarith [norm_nonneg p]))
  refine ⟨C₁ + C₂, max (max N₀₁ N₀₂) (max N₁ 2), ?_⟩
  intro N _ ε S μ ν ρ τ z hN hε0 hε hS hμν hρτ hz hz1 hz2
  have g1 : N₀₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have g2 : N₀₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have g3 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have g4 : (2 : ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have g4' : 2 ≤ N := by exact_mod_cast g4
  let i : KernelData Bb C c c' N₁ := ⟨N, g3, g4', ε, hε0, hε, S, hS, μ, ν, ρ, τ⟩
  have hU := regDomain_domain (Bb := Bb) (C := C) (c := c) (c' := c') (N₁ := N₁)
  have hpi := Real.pi_lt_d2
  have hord : IsSymbolOfOrder B' 1 (periodicPart i) := by
    refine ⟨fun r => ?_, fun r p hp0 hcube => ?_⟩
    · exact ((contDiff_infty.1 (periodicPart_contDiff hc' hc hN1 i)) r).contDiffOn
    · have hw : 0 < ‖p‖ := norm_pos_iff.mpr hp0
      have hpn : ‖p‖ ≤ Real.pi := (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 fun j => hcube j
      have hs : 0 ≤ LinearResponse.sqNorm p ^ ((1 - (r : ℝ)) / 2) := Real.rpow_nonneg (sqNorm_nonneg p) _
      have hB0 : 0 ≤ B' r := by simp only [hB']; positivity
      by_cases hh : (N : ℝ) * ‖p‖ < 1 / 2
      · have hc1 : Continuous fun q : Mom => (N : ℝ) * ‖q‖ := by fun_prop
        have hev : periodicPart i =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
          filter_upwards [hc1.continuousAt.eventually (gt_mem_nhds hh)] with q hq
          exact periodicPart_eq_zero_low i hq.le
        rw [(hev.iteratedFDeriv ℝ r).eq_of_nhds, iteratedFDeriv_zero_fun]
        have : ((0 : Mom → Mom [×r]→L[ℝ] ℂ) p) = 0 := rfl
        rw [this, norm_zero]
        positivity
      · have hmem : p ∈ domain Bb C c c' N₁ i := by
          refine ⟨?_, by linarith⟩
          show 1 / (4 * (N : ℝ)) < ‖p‖
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        have hev : periodicPart i =ᶠ[𝓝 p] localPart i :=
          Filter.eventually_of_mem ((hU.isOpen i).mem_nhds hmem) fun q hq => periodicPart_eq_localPart hc' hc hN1 i hq
        rw [(hev.iteratedFDeriv ℝ r).eq_of_nhds]
        refine (hKb r i p hmem).trans ?_
        have h3 := norm_zpow_le_sqNorm_rpow hw r
        have h4 : 0 ≤ ‖p‖ ^ ((1 : ℤ) - r) := by positivity
        calc Kb r * ‖p‖ ^ ((1 : ℤ) - r) ≤ |Kb r| * (2 ^ r * LinearResponse.sqNorm p ^ ((1 - (r : ℝ)) / 2)) :=
              mul_le_mul (le_abs_self _) h3 h4 (abs_nonneg _)
          _ = _ := by simp only [hB']; ring
  have hper : ∀ (p : Fin 4 → ℝ) (k : Fin 4), (∀ w : Fin 4 → ℤ, p ≠ fun l => 2 * Real.pi * (w l : ℝ)) →
      periodicPart i (p + Pi.single k (2 * Real.pi)) * Complex.exp (Complex.I * (2 * Real.pi * z k : ℝ)) = periodicPart i p := by
    intro p k _
    obtain ⟨w, hw⟩ := hz k
    have hn : z k = w + (((if k = ρ then 1 else 0) + (if k = τ then 1 else 0) - (if k = μ then 1 else 0) -
        (if k = ν then 1 else 0) : ℤ) : ℝ) / 2 := by
      rw [hw]
      split_ifs <;> norm_num
    rw [exp_two_pi_half_int hn, neg_one_zpow_ite]
    have : (if k = μ then (-1 : ℂ) else 1) * (if k = ν then -1 else 1) * (if k = ρ then -1 else 1) *
        (if k = τ then -1 else 1) = shiftSign i k := by
      simp only [shiftSign, flipSign_eq_ite]
      rfl
    rw [this]
    exact periodicPart_add_single i p k
  have w1 := m1 N (periodicPart i) z g1 hord hper hz1 hz2
  have w2 := m2 N μ ν ρ τ z g2 hμν hρτ hz1 hz2
  have key : inverseSymbolFourierSum N S μ ν ρ τ z = nonzeroMomentumWave N (periodicPart i) z +
      nonzeroMomentumWave N (fun p => ((innerBump p : ℝ) : ℂ) * doubleCurlSymbol μ ν ρ τ p) z := by
    unfold inverseSymbolFourierSum nonzeroMomentumWave
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← add_mul]
    congr 1
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    obtain ⟨q1, q2⟩ := dualMomentum_bounds g4' hj0
    have hn : ‖dualMomentum j‖ < 7 / 2 := by
      have : ‖dualMomentum j‖ ≤ Real.pi := (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 fun l => q1 l
      linarith
    rw [periodicPart_eq_near i hn]
    have hz0 : scaledCut i.N (dualMomentum j) = 0 := scaledCut_eq_zero q2
    simp only [cutDoubleCurl, hz0, sub_zero, one_mul, innerCut]
    exact (sub_add_cancel _ _).symm
  rw [key]
  have e : nonzeroMomentumWave N (periodicPart i) z + nonzeroMomentumWave N (fun p => ((innerBump p : ℝ) : ℂ) * doubleCurlSymbol μ ν ρ τ p) z -
      (LinearResponse.continuumCurvatureKernel z μ ν ρ τ : ℂ) = nonzeroMomentumWave N (periodicPart i) z +
      (nonzeroMomentumWave N (fun p => ((innerBump p : ℝ) : ℂ) * doubleCurlSymbol μ ν ρ τ p) z - (LinearResponse.continuumCurvatureKernel z μ ν ρ τ : ℂ)) := by
    ring
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (add_le_add w1 w2)
end YangMills.Construction.ResponseInTheExpansion
end
