import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.InfiniteLattice.TransportOfLipschitzFunctionsAtAPositiveMargin
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric TestFunctions
noncomputable section
namespace LipschitzPeriodization
open InfiniteLattice.MarginPeriodization
section Norms
private theorem euclidNormVec_nonneg (u : Fin 4 → ℝ) : 0 ≤ euclidNormVec u := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_nonneg <;> assumption
private theorem euclidNormVec_zero : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
private theorem euclidNormVec_neg (u : Fin 4 → ℝ) : euclidNormVec (-u) = euclidNormVec u := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
private theorem euclidNormVec_sub_comm (x y : Fin 4 → ℝ) :
    euclidNormVec (x - y) = euclidNormVec (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
private theorem euclidNormVec_smul (s : ℝ) (u : Fin 4 → ℝ) :
    euclidNormVec (s • u) = |s| * euclidNormVec u := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
private theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
private theorem le_euclidNormVec_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ}
    (hk : k ≠ 0) : ℓ ≤ euclidNormVec (latticeTranslate ℓ k) := by apply _root_.YangMills.Construction.TestPairs.le_euclidNormVec_latticeTranslate <;> assumption
private theorem latticeTranslate_zero (ℓ : ℝ) : latticeTranslate ℓ 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.latticeTranslate_zero <;> assumption
private theorem intCombination_eq_latticeTranslate (ℓ : ℝ) (m : Fin 4 → ℤ) :
    ReflectionPositivity.AxisMirror.intCombination ℓ m = latticeTranslate ℓ m := by
  funext μ
  simp [ReflectionPositivity.AxisMirror.intCombination, PeriodicLattice.coordVec, Finset.sum_apply,
    Pi.single_apply, latticeTranslate]
private theorem continuous_torusProj (ℓ : ℝ) : Continuous (torusProj ℓ) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
end Norms
section Ball
variable {ℓ r : ℝ}
private theorem lt_euclidNormVec_add_latticeTranslate (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    {x y : Fin 4 → ℝ} (hx : x ∈ SourcesAndGluing.ballR4 r)
    (hy : y ∈ SourcesAndGluing.ballR4 r) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    euclidNormVec (x - y) < euclidNormVec (x - y + latticeTranslate ℓ k) := by
  have hxy := hasDiameterLE_ballR4 r x hx y hy
  have hk' := le_euclidNormVec_latticeTranslate hℓ hk
  have htri := Periodization.euclidNormVec_triangle (x - y + latticeTranslate ℓ k) (-(x - y))
  rw [euclidNormVec_neg, add_neg_cancel_comm] at htri
  linarith
private theorem torusEuclidNorm_proj_sub_proj
    (H1 : ∀ y y' : Fin 4 → ℝ,
      IsLeast (range fun m : Fin 4 → ℤ => euclidNormVec (y - y' + latticeTranslate ℓ m))
        (torusEuclidNorm (torusProj ℓ y - torusProj ℓ y')))
    (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2) {x y : Fin 4 → ℝ}
    (hx : x ∈ SourcesAndGluing.ballR4 r)
    (hy : y ∈ SourcesAndGluing.ballR4 r) :
    torusEuclidNorm (torusProj ℓ x - torusProj ℓ y) = euclidNormVec (x - y) := by
  obtain ⟨⟨m, hm⟩, hlow⟩ := H1 x y
  have h0 : torusEuclidNorm (torusProj ℓ x - torusProj ℓ y) ≤ euclidNormVec (x - y) := by
    have h := hlow ⟨0, rfl⟩
    simpa [latticeTranslate_zero] using h
  by_cases hm0 : m = 0
  · subst hm0
    simpa [latticeTranslate_zero] using hm.symm
  · have h := lt_euclidNormVec_add_latticeTranslate hℓ hr hx hy hm0
    linarith
private theorem torusProj_injOn (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2) :
    InjOn (torusProj ℓ) (SourcesAndGluing.ballR4 r) := by
  intro x hx y hy hxy
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq hxy.symm
  by_cases hk0 : k = 0
  · subst hk0
    simpa [latticeTranslate_zero] using hk.symm
  · exfalso
    have h := lt_euclidNormVec_add_latticeTranslate hℓ hr hx hy hk0
    rw [hk] at h
    have hz : x - (x + latticeTranslate ℓ k) + latticeTranslate ℓ k = 0 := by abel
    rw [hz, euclidNormVec_zero] at h
    exact absurd (euclidNormVec_nonneg _) (not_le.mpr h)
end Ball
section Periodize
variable {ℓ r : ℝ} {f : (Fin 4 → ℝ) → ℝ}
private theorem mem_ball_of_ne_zero (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r)
    {x : Fin 4 → ℝ} (hx : f x ≠ 0) : x ∈ SourcesAndGluing.ballR4 r :=
  hs (subset_tsupport f hx)
private theorem eq_zero_of_notMem_ball (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r)
    {x : Fin 4 → ℝ} (hx : x ∉ SourcesAndGluing.ballR4 r) : f x = 0 := by
  by_contra h
  exact hx (mem_ball_of_ne_zero hs h)
private theorem shift_eq_of_ne_zero (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) {x y : Fin 4 → ℝ}
    (hxy : euclidNormVec (x - y) < ℓ / 2) {k k' : Fin 4 → ℤ}
    (hk : f (x + latticeTranslate ℓ k) ≠ 0) (hk' : f (y + latticeTranslate ℓ k') ≠ 0) :
    k = k' := by
  by_contra hne
  have hsub : k - k' ≠ 0 := sub_ne_zero.mpr hne
  have h1 := le_euclidNormVec_latticeTranslate hℓ hsub
  have h2 := hasDiameterLE_ballR4 r _ (mem_ball_of_ne_zero hs hk) _
    (mem_ball_of_ne_zero hs hk')
  have hper : latticeTranslate ℓ (k - k') =
      (x + latticeTranslate ℓ k - (y + latticeTranslate ℓ k')) + -(x - y) := by
    have : latticeTranslate ℓ k = latticeTranslate ℓ (k - k') + latticeTranslate ℓ k' := by
      rw [← latticeTranslate_add, sub_add_cancel]
    rw [this]
    abel
  have h3 := Periodization.euclidNormVec_triangle
    (x + latticeTranslate ℓ k - (y + latticeTranslate ℓ k')) (-(x - y))
  rw [← hper, euclidNormVec_neg] at h3
  linarith
private theorem nonzero_shift_subsingleton (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) (x : Fin 4 → ℝ) :
    {k : Fin 4 → ℤ | f (x + latticeTranslate ℓ k) ≠ 0}.Subsingleton := by
  intro k hk k' hk'
  refine shift_eq_of_ne_zero hℓ hr hs (x := x) (y := x) ?_ hk hk'
  rw [sub_self, euclidNormVec_zero]
  linarith [(by linarith : (0 : ℝ) < ℓ / 2)]
private theorem periodize_torusProj_eq_shift (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) {x : Fin 4 → ℝ} {k : Fin 4 → ℤ}
    (hk : f (x + latticeTranslate ℓ k) ≠ 0) :
    periodize ℓ f (torusProj ℓ x) = f (x + latticeTranslate ℓ k) := by
  rw [periodize_torusProj]
  refine tsum_eq_single k fun k' hk' => ?_
  by_contra h
  exact hk' (nonzero_shift_subsingleton hℓ hr hs x h hk)
private theorem periodize_torusProj_eq_zero {x : Fin 4 → ℝ}
    (h : ∀ k, f (x + latticeTranslate ℓ k) = 0) : periodize ℓ f (torusProj ℓ x) = 0 := by
  rw [periodize_torusProj]
  simp [periodicSum, h]
private theorem periodize_torusProj_of_mem_ball (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) {x : Fin 4 → ℝ}
    (hx : x ∈ SourcesAndGluing.ballR4 r) : periodize ℓ f (torusProj ℓ x) = f x := by
  rw [periodize_torusProj]
  have h : periodicSum ℓ f x = f (x + latticeTranslate ℓ 0) := by
    refine tsum_eq_single 0 fun k hk => eq_zero_of_notMem_ball hs fun hxk => ?_
    have h := lt_euclidNormVec_add_latticeTranslate hℓ hr hx hxk hk
    have hz : x - (x + latticeTranslate ℓ k) + latticeTranslate ℓ k = 0 := by abel
    rw [hz, euclidNormVec_zero] at h
    exact absurd (euclidNormVec_nonneg _) (not_le.mpr h)
  rw [h, latticeTranslate_zero, add_zero]
private theorem exists_lift_of_periodize_ne_zero (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) {u : Torus4 ℓ}
    (hu : periodize ℓ f u ≠ 0) : ∃ x, torusProj ℓ x = u ∧ f x = periodize ℓ f u := by
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective ℓ u
  by_cases h : ∀ k, f (x + latticeTranslate ℓ k) = 0
  · exact absurd (periodize_torusProj_eq_zero h) hu
  · push Not at h
    obtain ⟨k, hk⟩ := h
    exact ⟨x + latticeTranslate ℓ k, torusProj_add_latticeTranslate ℓ x k,
      (periodize_torusProj_eq_shift hℓ hr hs hk).symm⟩
private theorem support_periodize (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) :
    Function.support (periodize ℓ f) = torusProj ℓ '' Function.support f := by
  ext u
  constructor
  · intro hu
    obtain ⟨x, rfl, hx⟩ := exists_lift_of_periodize_ne_zero hℓ hr hs hu
    refine ⟨x, ?_, rfl⟩
    rw [Function.mem_support, hx]
    exact hu
  · rintro ⟨x, hx, rfl⟩
    rw [Function.mem_support,
      periodize_torusProj_of_mem_ball hℓ hr hs (mem_ball_of_ne_zero hs hx)]
    exact hx
private theorem summable_shifts (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) (x : Fin 4 → ℝ) :
    Summable fun k : Fin 4 → ℤ => f (x + latticeTranslate ℓ k) :=
  summable_of_hasFiniteSupport (nonzero_shift_subsingleton hℓ hr hs x).finite
private theorem periodize_lipschitz_of_ne_zero
    (H1 : ∀ y y' : Fin 4 → ℝ,
      IsLeast (range fun m : Fin 4 → ℤ => euclidNormVec (y - y' + latticeTranslate ℓ m))
        (torusEuclidNorm (torusProj ℓ y - torusProj ℓ y')))
    (H3 : ∀ (y : Fin 4 → ℝ) (x' : Torus4 ℓ), ∃ y'', torusProj ℓ y'' = x' ∧
      euclidNormVec (y - y'') = torusEuclidNorm (torusProj ℓ y - x'))
    (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) {C : ℝ}
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y) {u u' : Torus4 ℓ}
    (hu : periodize ℓ f u ≠ 0) :
    ‖periodize ℓ f u - periodize ℓ f u'‖ ≤ C * euclidDistTorus u u' := by
  obtain ⟨x, rfl, hx⟩ := exists_lift_of_periodize_ne_zero hℓ hr hs hu
  have hxB : x ∈ SourcesAndGluing.ballR4 r :=
    mem_ball_of_ne_zero hs (by rw [hx]; exact hu)
  by_cases hu' : periodize ℓ f u' = 0
  · obtain ⟨y, rfl, hy⟩ := H3 x u'
    have hfy : f y = 0 := by
      by_contra hne
      have hne' : f (y + latticeTranslate ℓ 0) ≠ 0 := by
        rwa [latticeTranslate_zero, add_zero]
      have h := periodize_torusProj_eq_shift hℓ hr hs hne'
      rw [latticeTranslate_zero, add_zero, hu'] at h
      exact hne h.symm
    have h := hC x y
    rw [hx, hfy] at h
    rw [hu']
    simpa [euclidDistR4, euclidDistTorus, hy] using h
  · obtain ⟨y, rfl, hy⟩ := exists_lift_of_periodize_ne_zero hℓ hr hs hu'
    have hyB : y ∈ SourcesAndGluing.ballR4 r :=
      mem_ball_of_ne_zero hs (by rw [hy]; exact hu')
    have h := hC x y
    rw [hx, hy] at h
    have hd : euclidDistTorus (torusProj ℓ x) (torusProj ℓ y) = euclidDistR4 x y :=
      torusEuclidNorm_proj_sub_proj H1 hℓ hr hxB hyB
    rw [hd]
    exact h
private theorem periodize_lipschitz
    (H1 : ∀ y y' : Fin 4 → ℝ,
      IsLeast (range fun m : Fin 4 → ℤ => euclidNormVec (y - y' + latticeTranslate ℓ m))
        (torusEuclidNorm (torusProj ℓ y - torusProj ℓ y')))
    (H3 : ∀ (y : Fin 4 → ℝ) (x' : Torus4 ℓ), ∃ y'', torusProj ℓ y'' = x' ∧
      euclidNormVec (y - y'') = torusEuclidNorm (torusProj ℓ y - x'))
    (H4 : ∀ x x' : Torus4 ℓ, torusEuclidNorm (x - x') = torusEuclidNorm (x' - x))
    (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y) (u u' : Torus4 ℓ) :
    ‖periodize ℓ f u - periodize ℓ f u'‖ ≤ C * euclidDistTorus u u' := by
  by_cases hu : periodize ℓ f u = 0
  · by_cases hu' : periodize ℓ f u' = 0
    · rw [hu, hu', sub_zero, norm_zero]
      have hnn : 0 ≤ euclidDistTorus u u' :=
        Real.sInf_nonneg (by rintro _ ⟨v, -, rfl⟩; exact euclidNormVec_nonneg v)
      exact mul_nonneg hC0 hnn
    · have h := periodize_lipschitz_of_ne_zero H1 H3 hℓ hr hs hC (u' := u) hu'
      have hd : euclidDistTorus u' u = euclidDistTorus u u' := H4 u' u
      rw [hd, norm_sub_rev] at h
      exact h
  · exact periodize_lipschitz_of_ne_zero H1 H3 hℓ hr hs hC hu
private theorem lipschitz_across_boundary
    (hf : Continuous f) (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hin : ∀ x ∈ SourcesAndGluing.ballR4 r,
      ∀ y ∈ SourcesAndGluing.ballR4 r, ‖f x - f y‖ ≤ C * euclidNormVec (x - y))
    {x y : Fin 4 → ℝ} (hx : x ∈ SourcesAndGluing.ballR4 r)
    (hy : y ∉ SourcesAndGluing.ballR4 r) :
    ‖f x - f y‖ ≤ C * euclidNormVec (x - y) := by
  rw [eq_zero_of_notMem_ball hs hy, sub_zero]
  by_cases hfx : f x = 0
  · rw [hfx, norm_zero]
    exact mul_nonneg hC0 (euclidNormVec_nonneg _)
  set γ : ℝ → Fin 4 → ℝ := fun t => x + t • (y - x) with hγ
  have hγc : Continuous γ := by fun_prop
  have hγ0 : γ 0 = x := by simp [hγ]
  have hγ1 : γ 1 = y := by simp [hγ]
  set T : Set ℝ := Icc 0 1 ∩ γ ⁻¹' tsupport f with hT
  have hTc : IsCompact T :=
    isCompact_Icc.inter_right ((isClosed_tsupport f).preimage hγc)
  have h0T : (0 : ℝ) ∈ T := by
    refine ⟨left_mem_Icc.mpr zero_le_one, ?_⟩
    show γ 0 ∈ tsupport f
    rw [hγ0]
    exact subset_tsupport f hfx
  have hsT : sSup T ∈ T := hTc.sSup_mem ⟨0, h0T⟩
  set s := sSup T with hsdef
  have hs1 : s < 1 := by
    refine lt_of_le_of_ne hsT.1.2 fun h1 => hy ?_
    have hmem : γ s ∈ tsupport f := hsT.2
    rw [h1, hγ1] at hmem
    exact hs hmem
  have hzero : ∀ t ∈ Ioc s 1, f (γ t) = 0 := by
    intro t ht
    by_contra hne
    have htT : t ∈ T := ⟨⟨hsT.1.1.trans ht.1.le, ht.2⟩, subset_tsupport f hne⟩
    exact absurd (le_csSup hTc.bddAbove htT) (not_le.mpr ht.1)
  have hclosed : IsClosed {t : ℝ | f (γ t) = 0} :=
    isClosed_eq (hf.comp hγc) continuous_const
  have hfs : f (γ s) = 0 := by
    have hsub : closure (Ioc s 1) ⊆ {t : ℝ | f (γ t) = 0} :=
      closure_minimal hzero hclosed
    rw [closure_Ioc hs1.ne] at hsub
    exact hsub (left_mem_Icc.mpr hs1.le)
  have hγs : γ s ∈ SourcesAndGluing.ballR4 r := hs hsT.2
  have h := hin x hx (γ s) hγs
  rw [hfs, sub_zero] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0)
  have hvec : x - γ s = s • (x - y) := by
    simp only [hγ]
    rw [← neg_sub y x, smul_neg]
    abel
  rw [hvec, euclidNormVec_smul, abs_of_nonneg hsT.1.1]
  exact mul_le_of_le_one_left (euclidNormVec_nonneg _) hs1.le
private theorem lipschitz_of_periodize
    (H1 : ∀ y y' : Fin 4 → ℝ,
      IsLeast (range fun m : Fin 4 → ℤ => euclidNormVec (y - y' + latticeTranslate ℓ m))
        (torusEuclidNorm (torusProj ℓ y - torusProj ℓ y')))
    (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2) (hf : Continuous f)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u u' : Torus4 ℓ,
      ‖periodize ℓ f u - periodize ℓ f u'‖ ≤ C * euclidDistTorus u u') (x y : Fin 4 → ℝ) :
    ‖f x - f y‖ ≤ C * euclidDistR4 x y := by
  have hin : ∀ x ∈ SourcesAndGluing.ballR4 r,
      ∀ y ∈ SourcesAndGluing.ballR4 r, ‖f x - f y‖ ≤ C * euclidNormVec (x - y) := by
    intro x hx y hy
    have h := hC (torusProj ℓ x) (torusProj ℓ y)
    rw [periodize_torusProj_of_mem_ball hℓ hr hs hx,
      periodize_torusProj_of_mem_ball hℓ hr hs hy] at h
    have hd : euclidDistTorus (torusProj ℓ x) (torusProj ℓ y) = euclidNormVec (x - y) :=
      torusEuclidNorm_proj_sub_proj H1 hℓ hr hx hy
    rwa [hd] at h
  show ‖f x - f y‖ ≤ C * euclidNormVec (x - y)
  by_cases hx : x ∈ SourcesAndGluing.ballR4 r
  · by_cases hy : y ∈ SourcesAndGluing.ballR4 r
    · exact hin x hx y hy
    · exact lipschitz_across_boundary hf hs hC0 hin hx hy
  · by_cases hy : y ∈ SourcesAndGluing.ballR4 r
    · rw [norm_sub_rev, euclidNormVec_sub_comm]
      exact lipschitz_across_boundary hf hs hC0 hin hy hx
    · rw [eq_zero_of_notMem_ball hs hx, eq_zero_of_notMem_ball hs hy, sub_zero, norm_zero]
      exact mul_nonneg hC0 (euclidNormVec_nonneg _)
private theorem periodize_comp_proj_contDiff (hℓ : 0 < ℓ) (hr : 2 * r < ℓ / 2)
    (hs : tsupport f ⊆ SourcesAndGluing.ballR4 r) (hC1 : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (periodize ℓ f ∘ torusProj ℓ) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  set V : Set (Fin 4 → ℝ) := {x | euclidNormVec (x - x₀) < ℓ / 4} with hV
  have hVo : IsOpen V :=
    isOpen_lt (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
      continuous_const
  have hVn : V ∈ nhds x₀ := by
    refine hVo.mem_nhds ?_
    show euclidNormVec (x₀ - x₀) < ℓ / 4
    rw [sub_self, euclidNormVec_zero]
    linarith
  by_cases hk : ∃ x₁ ∈ V, ∃ k, f (x₁ + latticeTranslate ℓ k) ≠ 0
  · obtain ⟨x₁, hx₁, k₀, hk₀⟩ := hk
    have hterm : ContDiff ℝ 1 fun x => f (x + latticeTranslate ℓ k₀) :=
      hC1.comp (contDiff_id.add contDiff_const)
    refine hterm.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hVn] with x hx
    show periodize ℓ f (torusProj ℓ x) = f (x + latticeTranslate ℓ k₀)
    by_cases hne : f (x + latticeTranslate ℓ k₀) = 0
    · rw [hne]
      refine periodize_torusProj_eq_zero fun k => ?_
      by_contra hk
      have hnear : euclidNormVec (x - x₁) < ℓ / 2 := by
        have h := Periodization.euclidNormVec_triangle (x - x₀) (x₀ - x₁)
        rw [sub_add_sub_cancel, euclidNormVec_sub_comm x₀ x₁] at h
        have h1 : euclidNormVec (x - x₀) < ℓ / 4 := hx
        have h2 : euclidNormVec (x₁ - x₀) < ℓ / 4 := hx₁
        linarith
      have hkk := shift_eq_of_ne_zero hℓ hr hs hnear hk hk₀
      rw [hkk] at hk
      exact hk hne
    · exact periodize_torusProj_eq_shift hℓ hr hs hne
  · push Not at hk
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hVn] with x hx
    exact periodize_torusProj_eq_zero (hk x hx)
end Periodize
private theorem continuous_of_isLipschitzFor {f : (Fin 4 → ℝ) → ℝ}
    (hf : IsLipschitzFor euclidDistR4 f) : Continuous f := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_r4 <;> assumption
theorem statement_of_projectionFacts
    (hFacts : ReflectionPositivity.AxisMirror.ProjectionFacts) : Statement := by
  intro D c r f h hr hrl hLf hLh hf hh
  set ℓ : ℝ := D.side with hℓdef
  have hrad : c.radius ℓ < ℓ / 4 := margin_radius_lt_quarter c ℓ
  have hℓ : 0 < ℓ := by linarith
  have hr2 : 2 * r < ℓ / 2 := by linarith
  obtain ⟨H1', -, H3', H4', -, -⟩ := (hFacts ⟨D, 1, one_pos⟩).2.1
  have H1 : ∀ y y' : Fin 4 → ℝ,
      IsLeast (range fun m : Fin 4 → ℤ => euclidNormVec (y - y' + latticeTranslate ℓ m))
        (torusEuclidNorm (torusProj ℓ y - torusProj ℓ y')) := by
    intro y y'
    have h1 := H1' y y'
    simp only [intCombination_eq_latticeTranslate] at h1
    exact h1
  have H3 : ∀ (y : Fin 4 → ℝ) (x' : Torus4 ℓ), ∃ y'', torusProj ℓ y'' = x' ∧
      euclidNormVec (y - y'') = torusEuclidNorm (torusProj ℓ y - x') := H3'
  have H4 : ∀ x x' : Torus4 ℓ, torusEuclidNorm (x - x') = torusEuclidNorm (x' - x) := H4'
  have hcf := continuous_of_isLipschitzFor hLf
  obtain ⟨hfc, hfs⟩ := hf
  obtain ⟨hhc, hhs⟩ := hh
  refine ⟨⟨fun x hx y hy => torusEuclidNorm_proj_sub_proj H1 hℓ hr2 hx hy,
      torusProj_injOn hℓ hr2⟩,
    ⟨fun x => periodize_torusProj ℓ f x, nonzero_shift_subsingleton hℓ hr2 hfs,
      fun x hx => periodize_torusProj_of_mem_ball hℓ hr2 hfs hx⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t
    refine ⟨⟨hr, hrl, tsupport f ∪ tsupport h, hfc.union hhc, union_subset hfs hhs, ?_⟩, ?_⟩
    · intro x hx
      have h1 : f x = 0 := image_eq_zero_of_notMem_tsupport fun hm => hx (Or.inl hm)
      have h2 : h x = 0 := image_eq_zero_of_notMem_tsupport fun hm => hx (Or.inr hm)
      simp [h1, h2]
    · funext u
      obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective ℓ u
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, periodize_torusProj, periodicSum]
      rw [Summable.tsum_add ((summable_shifts hℓ hr2 hfs x).mul_left s)
        ((summable_shifts hℓ hr2 hhs x).mul_left t), tsum_mul_left, tsum_mul_left]
  · intro r' hr' hr'l hsub
    refine ⟨⟨hr', hr'l, tsupport f, hfc, hsub, fun x hx => image_eq_zero_of_notMem_tsupport hx⟩,
      fun g hg => ?_⟩
    funext u
    obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective ℓ u
    rw [hg x, periodize_torusProj]
    rfl
  · obtain ⟨B, hB⟩ := hcf.bounded_above_of_compact_support hfc
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    have hbdd : BddAbove (range fun x => ‖f x‖) := ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x⟩
    have hTB : ∀ u, ‖periodize ℓ f u‖ ≤ B := by
      intro u
      by_cases hu : periodize ℓ f u = 0
      · rw [hu, norm_zero]
        exact hB0
      · obtain ⟨x, -, hx⟩ := exists_lift_of_periodize_ne_zero hℓ hr2 hfs hu
        rw [← hx]
        exact hB x
    have hTbdd : BddAbove (range fun u => ‖periodize ℓ f u‖) :=
      ⟨B, by rintro _ ⟨u, rfl⟩; exact hTB u⟩
    have hsup : uniformNorm (periodize ℓ f) = uniformNorm f := by
      have hf0 : 0 ≤ uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
      have hT0 : 0 ≤ uniformNorm (periodize ℓ f) := Real.iSup_nonneg fun _ => norm_nonneg _
      apply le_antisymm
      · refine ciSup_le fun u => ?_
        by_cases hu : periodize ℓ f u = 0
        · rw [hu, norm_zero]
          exact hf0
        · obtain ⟨x, -, hx⟩ := exists_lift_of_periodize_ne_zero hℓ hr2 hfs hu
          rw [← hx]
          exact le_ciSup hbdd x
      · refine ciSup_le fun x => ?_
        by_cases hx : x ∈ SourcesAndGluing.ballR4 r
        · rw [← periodize_torusProj_of_mem_ball hℓ hr2 hfs hx]
          exact le_ciSup hTbdd (torusProj ℓ x)
        · rw [eq_zero_of_notMem_ball hfs hx, norm_zero]
          exact hT0
    have hlip : lipConstTorus (periodize ℓ f) = lipConstR4 f := by
      unfold lipConstTorus lipConstR4 bestLipschitzConstant
      congr 1
      ext C
      constructor
      · rintro ⟨hC0, hC⟩
        exact ⟨hC0, lipschitz_of_periodize H1 hℓ hr2 hcf hfs hC0 hC⟩
      · rintro ⟨hC0, hC⟩
        exact ⟨hC0, periodize_lipschitz H1 H3 H4 hℓ hr2 hfs hC0 hC⟩
    obtain ⟨C, hC0, hC⟩ := hLf
    refine ⟨⟨B, hTB⟩, hsup, ⟨C, hC0, periodize_lipschitz H1 H3 H4 hℓ hr2 hfs hC0 hC⟩, hlip,
      fun M => ?_⟩
    unfold sharpNormTorus sharpNormR4
    rw [hsup, hlip]
  · intro hC1
    exact periodize_comp_proj_contDiff hℓ hr2 hfs hC1
  · have hcov := continuous_torusProj ℓ
    have : Fact (0 < ℓ) := ⟨hℓ⟩
    have hsupp : ∀ g : (Fin 4 → ℝ) → ℝ, IsCompact (tsupport g) →
        tsupport g ⊆ SourcesAndGluing.ballR4 r →
        tsupport (periodize ℓ g) = torusProj ℓ '' tsupport g := by
      intro g hgc hgs
      refine Subset.antisymm ?_ ?_
      · refine closure_minimal ?_ (hgc.image hcov).isClosed
        rw [support_periodize hℓ hr2 hgs]
        exact image_mono (subset_tsupport g)
      · have h1 := image_closure_subset_closure_image (s := Function.support g) hcov
        rw [← support_periodize hℓ hr2 hgs] at h1
        exact h1
    refine ⟨hsupp f hfc hfs, ?_, ?_⟩
    · rw [hsupp f hfc hfs]
      exact hfc.image hcov
    · rw [hsupp f hfc hfs, hsupp h hhc hhs]
      unfold setEuclidDist setDistR4
      simp only [iInf_image]
      refine iInf_congr fun x => iInf_congr fun hx => iInf_congr fun y => iInf_congr fun hy => ?_
      rw [torusEuclidNorm_proj_sub_proj H1 hℓ hr2 (hfs hx) (hhs hy)]
  · intro ℓ' _ h'
    simp only [ExpandingTori.PeriodizationMargin.radius]
    linarith
end LipschitzPeriodization
end
end YangMills.Construction
