import YangMills.Construction.ToriAtArbitraryCouplings.TheEuclideanDistanceAndTheCoveringMapProof
import YangMills.Construction.ToriAtArbitraryCouplings.TheTransportToATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set MetricNotions TestFunctions
open TorusMetric (euclidNormVec)
namespace ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace TransportToTorus
open DistanceAndProjection
section MetricFacts
variable {X Y : Type*} {d : X → X → ℝ} {d' : Y → Y → ℝ}
theorem exists_pos_lowerBound_of_finite {α : Type*} (D : α → ℝ) {T : Set (Set α)} (hT : T.Finite)
    (h : ∀ U ∈ T, ∃ r : ℝ, 0 < r ∧ ∀ w ∈ U, r ≤ D w) :
    ∃ r : ℝ, 0 < r ∧ ∀ U ∈ T, ∀ w ∈ U, r ≤ D w := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert U T _ _ ih =>
    obtain ⟨r, hr, hU⟩ := h U (mem_insert _ _)
    obtain ⟨r', hr', hT'⟩ := ih fun V hV => h V (mem_insert_of_mem _ hV)
    refine ⟨min r r', lt_min hr hr', fun V hV w hw => ?_⟩
    rcases hV with rfl | hV
    · exact (min_le_left _ _).trans (hU w hw)
    · exact (min_le_right _ _).trans (hT' V hV w hw)
theorem closureWrt_image_subset_image_of_isCompactWrt (hself : ∀ x, d x x = 0)
    (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hnonneg' : ∀ x y, 0 ≤ d' x y) (hzero' : ∀ x y, d' x y = 0 → x = y)
    (hsymm' : ∀ x y, d' x y = d' y x) (htri' : ∀ x y z, d' x z ≤ d' x y + d' y z)
    {p : X → Y} (hp : ∀ u v, d' (p u) (p v) ≤ d u v) {K A : Set X}
    (hK : IsCompactWrt d K) (hA : A ⊆ K) : closureWrt d' (p '' A) ⊆ p '' K := by
  intro x hx
  by_contra hxK
  have hcover : K ⊆ ⋃₀ {U : Set X | IsOpenWrt d U ∧
      ∃ r : ℝ, 0 < r ∧ ∀ w ∈ U, r ≤ d' x (p w)} := by
    intro u hu
    have hpos : 0 < d' x (p u) := lt_of_le_of_ne (hnonneg' _ _) fun h =>
      hxK ⟨u, hu, (hzero' _ _ h.symm).symm⟩
    refine ⟨{w | d u w < d' x (p u) / 2}, ⟨?_, d' x (p u) / 2, half_pos hpos, ?_⟩, ?_⟩
    · intro y hy
      refine ⟨d' x (p u) / 2 - d u y, sub_pos.2 hy, fun z hz => ?_⟩
      have := htri u y z
      change d u z < d' x (p u) / 2
      linarith
    · intro w hw
      have h1 := htri' x (p w) (p u)
      have h2 := hp w u
      have h3 := hsymm w u
      change d u w < d' x (p u) / 2 at hw
      linarith
    · change d u u < d' x (p u) / 2
      rw [hself]
      exact half_pos hpos
  obtain ⟨T, hT, hfin, hKT⟩ := hK _ (fun U hU => hU.1) hcover
  obtain ⟨r, hr, hlow⟩ := exists_pos_lowerBound_of_finite (fun w => d' x (p w)) hfin
    fun U hU => (hT hU).2
  obtain ⟨y, ⟨w, hw, rfl⟩, hxy⟩ := hx r hr
  obtain ⟨U, hU, hwU⟩ := hKT (hA hw)
  exact absurd (hlow U hU w hwU) (not_le.2 hxy)
end MetricFacts
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem latticeTranslate_zero (ℓ : ℝ) : latticeTranslate ℓ 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.latticeTranslate_zero <;> assumption
variable (s : TorusSide)
theorem length_pos : 0 < s.length := by apply _root_.YangMills.Construction.ToriAtArbitraryCouplings.DistanceAndProjection.length_pos <;> assumption
theorem torusTransport_proj (f : (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ) :
    s.torusTransport f (s.proj v) = periodicSum s.length f v :=
  TestFunctions.periodize_torusProj s.length f v
theorem proj_add_latticeTranslate (v : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    s.proj (v + latticeTranslate s.length k) = s.proj v :=
  torusProj_add_latticeTranslate s.length v k
theorem proj_surjective : Function.Surjective s.proj := torusProj_surjective s.length
section SmallSupport
variable {s} {S : Set (Fin 4 → ℝ)} (hd : IsometricOnSmallSets s)
  (hS : HasDiameterLE S (s.length / 2)) {f : (Fin 4 → ℝ) → ℝ} (hf : ∀ v, f v ≠ 0 → v ∈ S)
include hd hS
theorem add_latticeTranslate_not_mem {u : Fin 4 → ℝ} (hu : u ∈ S) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    u + latticeTranslate s.length k ∉ S := by
  intro h
  have hempty := (hd S hS).2.2.1 k hk
  have hmem : u + latticeTranslate s.length k ∈
      S ∩ (fun v => v + latticeTranslate s.length k) '' S := ⟨h, u, hu, rfl⟩
  rw [hempty] at hmem
  exact hmem
include hf
theorem eq_of_term_ne_zero (v : Fin 4 → ℝ) (k k' : Fin 4 → ℤ)
    (hk : f (v + latticeTranslate s.length k) ≠ 0)
    (hk' : f (v + latticeTranslate s.length k') ≠ 0) : k = k' := by
  by_contra hne
  have e : v + latticeTranslate s.length k' =
      (v + latticeTranslate s.length k) + latticeTranslate s.length (k' - k) := by
    rw [add_assoc, ← latticeTranslate_add]
    simp
  have hmem := hf _ hk'
  rw [e] at hmem
  exact add_latticeTranslate_not_mem hd hS (hf _ hk) (sub_ne_zero.2 (Ne.symm hne)) hmem
theorem periodicSum_eq_term {v : Fin 4 → ℝ} {k : Fin 4 → ℤ}
    (hk : f (v + latticeTranslate s.length k) ≠ 0) :
    periodicSum s.length f v = f (v + latticeTranslate s.length k) := by
  refine tsum_eq_single k fun k' hk' => ?_
  by_contra h
  exact hk' (eq_of_term_ne_zero hd hS hf v k' k h hk)
theorem periodicSum_eq_self_of_ne_zero {u : Fin 4 → ℝ} (hu : f u ≠ 0) :
    periodicSum s.length f u = f u := by
  have h0 : f (u + latticeTranslate s.length 0) ≠ 0 := by simpa [_root_.YangMills.Construction.ToriAtArbitraryCouplings.TransportToTorus.latticeTranslate_zero] using hu
  rw [periodicSum_eq_term hd hS hf h0]
  simp [_root_.YangMills.Construction.ToriAtArbitraryCouplings.TransportToTorus.latticeTranslate_zero]
theorem exists_lift_of_torusTransport_ne_zero {x : s.Point .torus} (h : s.torusTransport f x ≠ 0) :
    ∃ u, s.proj u = x ∧ f u ≠ 0 ∧ s.torusTransport f x = f u := by
  obtain ⟨v, rfl⟩ := proj_surjective s x
  rw [torusTransport_proj] at h ⊢
  have hex : ∃ k, f (v + latticeTranslate s.length k) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact h (by simp [periodicSum, hno])
  obtain ⟨k, hk⟩ := hex
  exact ⟨_, proj_add_latticeTranslate s v k, hk, periodicSum_eq_term hd hS hf hk⟩
theorem eq_zero_of_torusTransport_eq_zero {v : Fin 4 → ℝ}
    (h : s.torusTransport f (s.proj v) = 0) : f v = 0 := by
  by_contra hne
  rw [torusTransport_proj, periodicSum_eq_self_of_ne_zero hd hS hf hne] at h
  exact hne h
theorem setOf_torusTransport_ne_zero :
    {x | s.torusTransport f x ≠ 0} = s.proj '' {u | f u ≠ 0} := by
  ext x
  constructor
  · intro h
    obtain ⟨u, hu, hfu, -⟩ := exists_lift_of_torusTransport_ne_zero hd hS hf h
    exact ⟨u, hfu, hu⟩
  · rintro ⟨u, hu, rfl⟩
    have hu' : f u ≠ 0 := hu
    change s.torusTransport f (s.proj u) ≠ 0
    rwa [torusTransport_proj, periodicSum_eq_self_of_ne_zero hd hS hf hu']
theorem isBoundedFun_and_uniformNorm_torusTransport (hb : IsBoundedFun f) :
    IsBoundedFun (s.torusTransport f) ∧ uniformNorm (s.torusTransport f) = uniformNorm f := by
  obtain ⟨C, hC⟩ := hb
  have hval : ∀ x, ∃ u, ‖s.torusTransport f x‖ ≤ ‖f u‖ := fun x => by
    by_cases h : s.torusTransport f x = 0
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨u, -, -, hu⟩ := exists_lift_of_torusTransport_ne_zero hd hS hf h
      exact ⟨u, by rw [hu]⟩
  have hbf : BddAbove (range fun u => ‖f u‖) := ⟨C, by rintro _ ⟨u, rfl⟩; exact hC u⟩
  have hbg : ∀ x, ‖s.torusTransport f x‖ ≤ C := fun x => by
    obtain ⟨u, hu⟩ := hval x
    exact hu.trans (hC u)
  have hbg' : BddAbove (range fun x => ‖s.torusTransport f x‖) :=
    ⟨C, by rintro _ ⟨x, rfl⟩; exact hbg x⟩
  have : Nonempty (s.Point .torus) := ⟨s.proj 0⟩
  refine ⟨⟨C, hbg⟩, le_antisymm (ciSup_le fun x => ?_) (ciSup_le fun u => ?_)⟩
  · obtain ⟨u, hu⟩ := hval x
    exact hu.trans (le_ciSup hbf u)
  · by_cases hu : f u = 0
    · rw [hu, norm_zero]
      exact (norm_nonneg _).trans (le_ciSup hbg' (s.proj 0))
    · have : ‖f u‖ = ‖s.torusTransport f (s.proj u)‖ := by
        rw [torusTransport_proj, periodicSum_eq_self_of_ne_zero hd hS hf hu]
      rw [this]
      exact le_ciSup hbg' _
omit hd in
theorem isBoundedFun_of_isLipschitzFor (hl : IsLipschitzFor euclidDistR4 f) : IsBoundedFun f := by
  obtain ⟨C, hC0, hC⟩ := hl
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hside : 0 ≤ s.length / 2 := (_root_.YangMills.Construction.ToriAtArbitraryCouplings.TransportToTorus.euclidNormVec_nonneg _).trans (hS p hp p hp)
    refine ⟨‖f p‖ + C * (s.length / 2), fun x => ?_⟩
    by_cases hx : f x = 0
    · rw [hx, norm_zero]
      positivity
    · have h1 : ‖f x - f p‖ ≤ C * euclidDistR4 x p := hC x p
      have h2 : C * euclidDistR4 x p ≤ C * (s.length / 2) :=
        mul_le_mul_of_nonneg_left (hS x (hf x hx) p hp) hC0
      have h3 : ‖f x‖ ≤ ‖f p‖ + ‖f x - f p‖ := by
        simpa using norm_add_le (f p) (f x - f p)
      linarith
  · refine ⟨0, fun x => ?_⟩
    have hx : f x = 0 := by
      by_contra h
      exact hne ⟨x, hf x h⟩
    simp [hx]
theorem torusTransport_lipschitz (ha : DistanceIsLeastAndLiftsExist s) (hb : IsMetric s) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y) (x y : s.Point .torus) :
    ‖s.torusTransport f x - s.torusTransport f y‖ ≤ C * s.pointDist .torus x y := by
  have aux : ∀ x y : s.Point .torus, s.torusTransport f x ≠ 0 →
      ‖s.torusTransport f x - s.torusTransport f y‖ ≤ C * s.pointDist .torus x y := by
    intro x y hx
    obtain ⟨u, hux, hfu, hgx⟩ := exists_lift_of_torusTransport_ne_zero hd hS hf hx
    by_cases hy : s.torusTransport f y = 0
    · obtain ⟨v, hvy, hdist⟩ := ha.2.2 .torus x y u hux
      have hvy' : s.proj v = y := hvy
      have hfv : f v = 0 := eq_zero_of_torusTransport_eq_zero hd hS hf (by rw [hvy']; exact hy)
      have h := hC u v
      rw [hgx, hy, ← hfv, ← hdist]
      exact h
    · obtain ⟨v, hvy, hfv, hgy⟩ := exists_lift_of_torusTransport_ne_zero hd hS hf hy
      have hdist := (hd S hS).1 u (hf u hfu) v (hf v hfv)
      rw [hux, hvy] at hdist
      have h := hC u v
      rw [hgx, hgy, hdist]
      exact h
  by_cases hx : s.torusTransport f x = 0
  · by_cases hy : s.torusTransport f y = 0
    · rw [hx, hy, sub_zero, norm_zero]
      obtain ⟨u, hu⟩ := proj_surjective s x
      obtain ⟨v, -, hdist⟩ := ha.2.2 .torus x y u hu
      rw [← hdist]
      exact mul_nonneg hC0 (_root_.YangMills.Construction.ToriAtArbitraryCouplings.TransportToTorus.euclidNormVec_nonneg _)
    · rw [norm_sub_rev, (hb .torus x y x).1]
      exact aux y x hy
  · exact aux x y hx
omit hf hd in
theorem contDiff_periodicSum (hf : ∀ v, f v ≠ 0 → v ∈ S) (hc : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (periodicSum s.length f) := by
  have hℓ := _root_.YangMills.Construction.ToriAtArbitraryCouplings.TransportToTorus.length_pos s
  obtain ⟨p, hp⟩ : ∃ p : Fin 4 → ℝ, ∀ w ∈ S, euclidNormVec (w - p) ≤ s.length / 2 := by
    by_cases hne : S.Nonempty
    · obtain ⟨p, hp⟩ := hne
      exact ⟨p, fun w hw => hS w hw p hp⟩
    · exact ⟨0, fun w hw => (hne ⟨w, hw⟩).elim⟩
  rw [contDiff_iff_contDiffAt]
  intro u₀
  obtain ⟨N, hN⟩ := exists_int_gt ((s.length / 2 + 1 + ‖u₀ - p‖) / s.length)
  let F : Finset (Fin 4 → ℤ) := Finset.Icc (fun _ => -N) (fun _ => N)
  have hoff : ∀ u ∈ Metric.ball u₀ 1, ∀ k ∉ F, f (u + latticeTranslate s.length k) = 0 := by
    intro u hu k hk
    by_contra hne
    apply hk
    have hbound : ∀ μ, |(k μ : ℝ)| < N := by
      intro μ
      have h1 := (_root_.YangMills.Construction.ToriAtArbitraryCouplings.TransportToTorus.abs_apply_le_euclidNormVec _ μ).trans (hp _ (hf _ hne))
      have h2 : |u μ - u₀ μ| < 1 := by
        have := (norm_le_pi_norm (u - u₀) μ).trans_lt (mem_ball_iff_norm.1 hu)
        simpa using this
      have h3 : |u₀ μ - p μ| ≤ ‖u₀ - p‖ := by
        simpa using norm_le_pi_norm (u₀ - p) μ
      have e : s.length * (k μ : ℝ) =
          (u + latticeTranslate s.length k - p) μ - (u μ - u₀ μ) - (u₀ μ - p μ) := by
        simp [latticeTranslate]
        ring
      have h4 : s.length * |(k μ : ℝ)| ≤ s.length / 2 + 1 + ‖u₀ - p‖ := by
        rw [← abs_of_pos hℓ, ← abs_mul, abs_of_pos hℓ, e]
        have t1 := abs_sub (((u + latticeTranslate s.length k - p) μ) - (u μ - u₀ μ)) (u₀ μ - p μ)
        have t2 := abs_sub ((u + latticeTranslate s.length k - p) μ) (u μ - u₀ μ)
        linarith
      have h5 : |(k μ : ℝ)| ≤ (s.length / 2 + 1 + ‖u₀ - p‖) / s.length := by
        rw [le_div_iff₀ hℓ]
        linarith
      exact h5.trans_lt hN
    have hbound' : ∀ μ, |k μ| < N := fun μ => by
      have := hbound μ
      rw [← Int.cast_abs] at this
      exact_mod_cast this
    refine Finset.mem_Icc.2 ⟨fun μ => ?_, fun μ => ?_⟩
    · exact (neg_lt_of_abs_lt (hbound' μ)).le
    · exact (lt_of_abs_lt (hbound' μ)).le
  have hsum : ContDiff ℝ 1 fun u => ∑ k ∈ F, f (u + latticeTranslate s.length k) :=
    ContDiff.sum fun k _ => hc.comp (contDiff_id.add contDiff_const)
  refine hsum.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds u₀ one_pos] with u hu
  exact tsum_eq_sum (hoff u hu)
end SmallSupport
theorem summable_translates {S : Set (Fin 4 → ℝ)} (hd : IsometricOnSmallSets s)
    (hS : HasDiameterLE S (s.length / 2)) {f : (Fin 4 → ℝ) → ℝ} (hf : ∀ v, f v ≠ 0 → v ∈ S)
    (v : Fin 4 → ℝ) : Summable fun k => f (v + latticeTranslate s.length k) := by
  refine summable_of_hasFiniteSupport (Set.Subsingleton.finite ?_)
  intro k hk k' hk'
  exact eq_of_term_ne_zero hd hS hf v k k' hk hk'
theorem pointDist_euclidean_self (u : Fin 4 → ℝ) : s.pointDist .euclidean u u = 0 := by
  show euclidNormVec (u - u) = 0
  simp [euclidNormVec]
theorem ne_zero_subset_closedSupport (f : (Fin 4 → ℝ) → ℝ) :
    {u | f u ≠ 0} ⊆ s.closedSupport .euclidean f :=
  fun u hu _ hr => ⟨u, hu, lt_of_eq_of_lt (pointDist_euclidean_self s u) hr⟩
theorem closedSupport_torusTransport {S : Set (Fin 4 → ℝ)} (ha : DistanceIsLeastAndLiftsExist s)
    (hb : IsMetric s) (hd : IsometricOnSmallSets s) (hS : HasDiameterLE S (s.length / 2))
    {f : (Fin 4 → ℝ) → ℝ} (hf : s.HasCompactSupportWithin S f) :
    s.closedSupport .torus (s.torusTransport f) = s.proj '' s.closedSupport .euclidean f := by
  have hoff : ∀ v, f v ≠ 0 → v ∈ S := fun v hv => hf.2 (ne_zero_subset_closedSupport s f hv)
  have hp : ∀ u v, s.pointDist .torus (s.proj u) (s.proj v) ≤
      s.pointDist .euclidean u v := fun u v => ha.2.1 .torus u v
  have hset := setOf_torusTransport_ne_zero hd hS hoff
  have hnonneg : ∀ x y : s.Point .torus, 0 ≤ s.pointDist .torus x y := fun x y => by
    obtain ⟨u, hu⟩ := proj_surjective s x
    obtain ⟨v, -, hdist⟩ := ha.2.2 .torus x y u hu
    rw [← hdist]
    exact _root_.YangMills.Construction.ToriAtArbitraryCouplings.TransportToTorus.euclidNormVec_nonneg _
  apply subset_antisymm
  · change closureWrt (s.pointDist .torus) {x | s.torusTransport f x ≠ 0} ⊆ _
    rw [hset]
    exact closureWrt_image_subset_image_of_isCompactWrt (pointDist_euclidean_self s)
      (fun x y => (hb .euclidean x y x).1) (fun x y z => (hb .euclidean x y z).2.2)
      hnonneg (fun x y => (hb .torus x y x).2.1) (fun x y => (hb .torus x y x).1)
      (fun x y z => (hb .torus x y z).2.2) hp hf.1 (ne_zero_subset_closedSupport s f)
  · rintro _ ⟨u, hu, rfl⟩ r hr
    obtain ⟨y, hy, huy⟩ := hu r hr
    refine ⟨s.proj y, ?_, (hp u y).trans_lt huy⟩
    have : s.proj y ∈ {x | s.torusTransport f x ≠ 0} := by
      rw [hset]
      exact ⟨y, hy, rfl⟩
    exact this
theorem properties_of_fullStatement (hT : DistanceAndProjection.FullStatement) : Properties := by
  intro s S hS
  obtain ⟨ha, hb, -, hd, -⟩ := hT s
  refine ⟨fun f hf => ?_, fun f h hf hh => ?_⟩
  · have hoff : ∀ v, f v ≠ 0 → v ∈ S := fun v hv => hf.2 (ne_zero_subset_closedSupport s f hv)
    have hcomp : s.torusTransport f ∘ s.proj = periodicSum s.length f :=
      funext fun v => torusTransport_proj s f v
    refine ⟨fun v k k' hk hk' => eq_of_term_ne_zero hd hS hoff v k k' hk hk', hcomp,
      ⟨s.torusTransport f, hcomp, fun g hg => ?_⟩,
      isBoundedFun_and_uniformNorm_torusTransport hd hS hoff,
      closedSupport_torusTransport s ha hb hd hS hf, fun hc => ?_, fun hl => ?_⟩
    · funext x
      obtain ⟨v, rfl⟩ := proj_surjective s x
      exact (congrFun hg v).trans (congrFun hcomp v).symm
    · have : ContDiff ℝ 1 (s.torusTransport f ∘ s.proj) := by
        rw [hcomp]
        exact contDiff_periodicSum hS hoff hc
      exact this
    · have hbdd : IsBoundedFun f := isBoundedFun_of_isLipschitzFor hS hoff hl
      have hsup := (isBoundedFun_and_uniformNorm_torusTransport hd hS hoff hbdd).2
      obtain ⟨C, hC0, hC⟩ := hl
      have hlip : ∀ C : ℝ, 0 ≤ C → (∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y) →
          ∀ x y : s.Point .torus,
            ‖s.torusTransport f x - s.torusTransport f y‖ ≤ C * euclidDistTorus x y :=
        fun C h0 h x y => torusTransport_lipschitz hd hS hoff ha hb h0 h x y
      have hle : s.lipConst .torus (s.torusTransport f) ≤ s.lipConst .euclidean f := by
        refine csInf_le_csInf ⟨0, fun c hc => hc.1⟩ ⟨C, hC0, hC⟩ ?_
        exact fun c hc => ⟨hc.1, hlip c hc.1 hc.2⟩
      refine ⟨⟨C, hC0, hlip C hC0 hC⟩, hle, fun m' => ?_⟩
      have e1 := s.sharpNormAt_eq m' .torus (s.torusTransport f)
      have e2 := s.sharpNormAt_eq m' .euclidean f
      refine e1.le.trans (le_trans ?_ e2.ge)
      refine max_le_max hsup.le (mul_le_mul_of_nonneg_left hle ?_)
      positivity
  · have hoff : ∀ v, f v ≠ 0 → v ∈ S := fun v hv => hf.2 (ne_zero_subset_closedSupport s f hv)
    have hoff' : ∀ v, h v ≠ 0 → v ∈ S := fun v hv => hh.2 (ne_zero_subset_closedSupport s h hv)
    refine ⟨fun α α' => ?_, ?_⟩
    · funext x
      obtain ⟨v, rfl⟩ := proj_surjective s x
      change s.torusTransport (α • f + α' • h) (s.proj v) =
        α * s.torusTransport f (s.proj v) + α' * s.torusTransport h (s.proj v)
      rw [torusTransport_proj, torusTransport_proj, torusTransport_proj]
      simp only [periodicSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Summable.tsum_add ((summable_translates s hd hS hoff v).mul_left α)
        ((summable_translates s hd hS hoff' v).mul_left α'), tsum_mul_left, tsum_mul_left]
    · rw [closedSupport_torusTransport s ha hb hd hS hf, closedSupport_torusTransport s ha hb hd hS hh]
      exact (hd S hS).2.2.2 _ _ hf.2 hh.2
end TransportToTorus
end ToriAtArbitraryCouplings
end YangMills.Construction
end
