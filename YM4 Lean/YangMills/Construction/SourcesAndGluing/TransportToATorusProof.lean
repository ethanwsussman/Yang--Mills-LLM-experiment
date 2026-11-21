import YangMills.Construction.SourcesAndGluing.TransportToATorus
import YangMills.Construction.Torus.CollinearQuadruplesProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SourcesAndGluing.TorusPeriodizationOfBall
open Set TorusMetric TestFunctions
open AmbientPoints (euclidNormVec_eq_norm torusEuclidNorm_eq_sqrt torusEuclidNorm_torusProj_le
  exists_torusProj_eq_euclidNormVec_eq torusEuclidNorm_sub_comm eq_of_torusEuclidNorm_sub_eq_zero
  torusEuclidNorm_sub_self euclidNormVec_sub_comm euclidNormVec_sub_le
  eq_of_euclidNormVec_sub_eq_zero)
open scoped ContDiff Topology
noncomputable section
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_sub_le_add (x y : Fin 4 → ℝ) :
    euclidNormVec (x - y) ≤ euclidNormVec x + euclidNormVec y := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.euclidNormVec_sub_le <;> assumption
theorem euclidNormVec_sub_euclidNormVec_le (x y : Fin 4 → ℝ) :
    euclidNormVec x - euclidNormVec y ≤ euclidNormVec (x - y) := by
  have h := euclidNormVec_sub_le x y 0
  rw [sub_zero, sub_zero] at h
  linarith
theorem euclidNormVec_smul (t : ℝ) (v : Fin 4 → ℝ) :
    euclidNormVec (t • v) = |t| * euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem continuous_torusEuclidNorm {S : ℝ} : Continuous (torusEuclidNorm (S := S)) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusEuclidNorm <;> assumption
theorem torusEuclidNorm_nonneg {S : ℝ} (x : Torus4 S) : 0 ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
theorem latticeTranslate_zero (ℓ : ℝ) : latticeTranslate ℓ 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.latticeTranslate_zero <;> assumption
theorem latticeTranslate_injective {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    Function.Injective (latticeTranslate ℓ) := by
  intro k k' h
  funext μ
  have h' := congrFun h μ
  simp only [latticeTranslate] at h'
  exact_mod_cast mul_left_cancel₀ hℓ h'
theorem le_euclidNormVec_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ euclidNormVec (latticeTranslate ℓ k) := by apply _root_.YangMills.Construction.TestPairs.le_euclidNormVec_latticeTranslate <;> assumption
variable {D : GluingSetup} {m' : ℕ+} {ρ : ℝ}
theorem torusSideAt_eq (D : GluingSetup) (m' : ℕ+) :
    D.torusSideAt m' = 2 * (D.L : ℝ) ^ (m' : ℕ) := rfl
theorem projAt_add_latticeTranslate (x : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    D.projAt m' (x + latticeTranslate (D.torusSideAt m') k) = D.projAt m' x :=
  torusProj_add_latticeTranslate _ x k
theorem exists_latticeTranslate_of_projAt_eq {x y : Fin 4 → ℝ}
    (h : D.projAt m' x = D.projAt m' y) :
    ∃ k, x = y + latticeTranslate (D.torusSideAt m') k :=
  exists_latticeTranslate_of_torusProj_eq h
theorem projAt_surjective : Function.Surjective (D.projAt m') := torusProj_surjective _
theorem continuous_projAt : Continuous (D.projAt m') := by
  show Continuous (torusProj (D.torusSideAt m'))
  exact continuous_pi fun μ => (AddCircle.continuous_mk' _).comp (continuous_apply μ)
theorem torusEuclidNorm_projAt_sub_le (x y : Fin 4 → ℝ) :
    torusEuclidNorm (S := D.torusSideAt m') (D.projAt m' x - D.projAt m' y) ≤
      euclidNormVec (x - y) := by
  rw [← map_sub]
  exact torusEuclidNorm_torusProj_le _
theorem euclidNormVec_sub_lt_sub_latticeTranslate (hρ : 0 < ρ)
    (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    {x y : Fin 4 → ℝ} (hx : x ∈ ballR4 ρ) (hy : y ∈ ballR4 ρ)
    {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    euclidNormVec (x - y) < euclidNormVec (x - y - latticeTranslate (D.torusSideAt m') k) := by
  have hℓ : 4 * ρ + 4 ≤ D.torusSideAt m' := by
    rw [torusSideAt_eq]
    linarith
  have h1 := le_euclidNormVec_latticeTranslate (by linarith : 0 < D.torusSideAt m') hk
  have h2 := euclidNormVec_sub_le_add x y
  have h3 := euclidNormVec_sub_euclidNormVec_le (latticeTranslate (D.torusSideAt m') k) (x - y)
  rw [euclidNormVec_sub_comm (latticeTranslate _ k) (x - y)] at h3
  have hx' : euclidNormVec x < ρ := hx
  have hy' : euclidNormVec y < ρ := hy
  linarith
theorem torusEuclidNorm_projAt_sub (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    {x y : Fin 4 → ℝ} (hx : x ∈ ballR4 ρ) (hy : y ∈ ballR4 ρ) :
    torusEuclidNorm (S := D.torusSideAt m') (D.projAt m' x - D.projAt m' y) =
      euclidNormVec (x - y) := by
  refine le_antisymm (torusEuclidNorm_projAt_sub_le x y) ?_
  obtain ⟨b, hb, hb'⟩ :=
    exists_torusProj_eq_euclidNormVec_eq (S := D.torusSideAt m') (D.projAt m' x - D.projAt m' y)
  have hcov : D.projAt m' (x - y) = D.projAt m' b := by
    rw [map_sub]
    exact hb.symm
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_projAt_eq hcov
  have hb2 : b = x - y - latticeTranslate (D.torusSideAt m') k := by
    rw [hk, add_sub_cancel_right]
  rw [← hb', hb2]
  by_cases hk0 : k = 0
  · rw [hk0, latticeTranslate_zero, sub_zero]
  · exact (euclidNormVec_sub_lt_sub_latticeTranslate hρ hL hx hy hk0).le
theorem injOn_projAt (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ)) :
    InjOn (D.projAt m') (ballR4 ρ) := by
  intro x hx y hy h
  have h1 := torusEuclidNorm_projAt_sub hρ hL hx hy
  have h0 : torusEuclidNorm (S := D.torusSideAt m') (D.projAt m' y - D.projAt m' y) = 0 :=
    torusEuclidNorm_sub_self _
  rw [h, h0] at h1
  exact eq_of_euclidNormVec_sub_eq_zero x y h1.symm
theorem eq_of_add_latticeTranslate_mem (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    {x : Fin 4 → ℝ} {k k' : Fin 4 → ℤ}
    (h : x + latticeTranslate (D.torusSideAt m') k ∈ ballR4 ρ)
    (h' : x + latticeTranslate (D.torusSideAt m') k' ∈ ballR4 ρ) : k = k' := by
  have hℓ : D.torusSideAt m' ≠ 0 := by
    rw [torusSideAt_eq]
    intro h0
    linarith
  have hq := injOn_projAt hρ hL h h'
    (by rw [projAt_add_latticeTranslate, projAt_add_latticeTranslate])
  exact latticeTranslate_injective hℓ (add_left_cancel hq)
theorem projIsometricOnBall_holds (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ)) :
    ProjIsometricOnBall D m' ρ := by
  refine ⟨fun x hx y hy k hk => euclidNormVec_sub_lt_sub_latticeTranslate hρ hL hx hy hk,
    fun x hx y hy => ?_, injOn_projAt hρ hL, fun k k' hkk => ?_⟩
  · rw [D.torusDist_eq_torusEuclidNorm]
    exact torusEuclidNorm_projAt_sub hρ hL hx hy
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hq : D.projAt m' y = D.projAt m' x := by
      have h := congrArg (D.projAt m') hxy
      simpa only [projAt_add_latticeTranslate] using h
    have hyx := injOn_projAt hρ hL hy hx hq
    subst hyx
    have hℓ : D.torusSideAt m' ≠ 0 := by
      rw [torusSideAt_eq]
      intro h0
      linarith
    exact hkk (latticeTranslate_injective hℓ (add_left_cancel hxy).symm)
section Functions
variable {𝕜 : Type} [RCLike 𝕜] {f : (Fin 4 → ℝ) → 𝕜}
theorem apply_eq_zero_of_notMem (hf : HasCompactSupportIn f (ballR4 ρ)) {x : Fin 4 → ℝ}
    (hx : x ∉ ballR4 ρ) : f x = 0 := by
  by_contra h
  exact hx (hf.2 (subset_closure (show x ∈ {x | f x ≠ 0} from h)))
theorem mem_ballR4_of_ne_zero (hf : HasCompactSupportIn f (ballR4 ρ)) {x : Fin 4 → ℝ}
    (hx : f x ≠ 0) : x ∈ ballR4 ρ := by
  by_contra h
  exact hx (apply_eq_zero_of_notMem hf h)
theorem ballPeriodize_projAt (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (f : (Fin 4 → ℝ) → 𝕜) {x : Fin 4 → ℝ} (hx : x ∈ ballR4 ρ) :
    D.ballPeriodize m' ρ f (D.projAt m' x) = f x :=
  (D.isBallPeriodization_ballPeriodize f (injOn_projAt hρ hL)).1 x hx
theorem ballPeriodize_of_notMem_image (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (f : (Fin 4 → ℝ) → 𝕜) {u : D.torusAt m'} (hu : u ∉ D.projAt m' '' ballR4 ρ) :
    D.ballPeriodize m' ρ f u = 0 :=
  (D.isBallPeriodization_ballPeriodize f (injOn_projAt hρ hL)).2 u hu
theorem exists_of_ballPeriodize_ne_zero (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    {u : D.torusAt m'} (h : D.ballPeriodize m' ρ f u ≠ 0) :
    ∃ x ∈ ballR4 ρ, D.projAt m' x = u ∧ f x = D.ballPeriodize m' ρ f u := by
  by_cases hu : u ∈ D.projAt m' '' ballR4 ρ
  · obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨x, hx, rfl, (ballPeriodize_projAt hρ hL f hx).symm⟩
  · exact absurd (ballPeriodize_of_notMem_image hρ hL f hu) h
theorem ballPeriodize_projAt_eq_tsum (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (hf : HasCompactSupportIn f (ballR4 ρ)) (x : Fin 4 → ℝ) :
    D.ballPeriodize m' ρ f (D.projAt m' x) =
      ∑' k : Fin 4 → ℤ, f (x + latticeTranslate (D.torusSideAt m') k) := by
  by_cases h : ∃ k, x + latticeTranslate (D.torusSideAt m') k ∈ ballR4 ρ
  · obtain ⟨k₀, hk₀⟩ := h
    rw [tsum_eq_single k₀ fun k hk => apply_eq_zero_of_notMem hf fun hb =>
      hk (eq_of_add_latticeTranslate_mem hρ hL hb hk₀)]
    rw [← projAt_add_latticeTranslate (D := D) (m' := m') x k₀]
    exact ballPeriodize_projAt hρ hL f hk₀
  · have hall : ∀ k, f (x + latticeTranslate (D.torusSideAt m') k) = 0 := fun k =>
      apply_eq_zero_of_notMem hf fun hb => h ⟨k, hb⟩
    simp only [hall, tsum_zero]
    refine ballPeriodize_of_notMem_image hρ hL f ?_
    rintro ⟨y, hy, hxy⟩
    obtain ⟨k, rfl⟩ := exists_latticeTranslate_of_projAt_eq hxy
    exact h ⟨k, hy⟩
theorem suppTorus_ballPeriodize (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (hf : HasCompactSupportIn f (ballR4 ρ)) :
    (D.withCutoffAndSide D.K m').suppTorus (D.ballPeriodize m' ρ f) =
      D.projAt m' '' GluingSetup.suppR4 f := by
  ext u
  constructor
  · intro hu
    have hu' : ∀ r : ℝ, 0 < r → ∃ v : D.torusAt m', D.ballPeriodize m' ρ f v ≠ 0 ∧
        torusEuclidNorm (S := D.torusSideAt m') (u - v) < r := fun r hr => by
      obtain ⟨v, hv, hd⟩ := hu r hr
      exact ⟨v, hv, hd⟩
    have hnear : ∀ r : ℝ, 0 < r → ∃ x ∈ GluingSetup.suppR4 f,
        torusEuclidNorm (S := D.torusSideAt m') (u - D.projAt m' x) < r := fun r hr => by
      obtain ⟨v, hv, hd⟩ := hu' r hr
      obtain ⟨x, -, rfl, hfx⟩ := exists_of_ballPeriodize_ne_zero hρ hL hv
      exact ⟨x, subset_closure (show x ∈ {x | f x ≠ 0} by
        show f x ≠ 0
        rw [hfx]
        exact hv), hd⟩
    obtain ⟨x₁, hx₁, -⟩ := hnear 1 one_pos
    have hcont : Continuous fun x : Fin 4 → ℝ =>
        torusEuclidNorm (S := D.torusSideAt m') (u - D.projAt m' x) :=
      continuous_torusEuclidNorm.comp (continuous_const.sub continuous_projAt)
    obtain ⟨x₀, hx₀, hmin⟩ := hf.1.exists_isMinOn ⟨x₁, hx₁⟩ hcont.continuousOn
    have hzero : torusEuclidNorm (S := D.torusSideAt m') (u - D.projAt m' x₀) = 0 := by
      refine le_antisymm (le_of_forall_pos_lt_add fun r hr => ?_) (torusEuclidNorm_nonneg _)
      obtain ⟨x, hx, hd⟩ := hnear r hr
      have := hmin hx
      simp only [mem_ofPred_eq] at this
      linarith
    exact ⟨x₀, hx₀, (eq_of_torusEuclidNorm_sub_eq_zero _ _ hzero).symm⟩
  · rintro ⟨y, hy, rfl⟩ r hr
    have hopen : IsOpen {x : Fin 4 → ℝ | euclidNormVec (y - x) < r} :=
      isOpen_lt (continuous_euclidNormVec.comp (continuous_const.sub continuous_id))
        continuous_const
    have hmem : y ∈ {x : Fin 4 → ℝ | euclidNormVec (y - x) < r} := by
      show euclidNormVec (y - y) < r
      rw [sub_self]
      simpa [euclidNormVec] using hr
    obtain ⟨x, hxr, hx⟩ := mem_closure_iff.1 hy _ hopen hmem
    have hx' : f x ≠ 0 := hx
    refine ⟨D.projAt m' x, ?_, lt_of_le_of_lt (torusEuclidNorm_projAt_sub_le y x) hxr⟩
    show D.ballPeriodize m' ρ f (D.projAt m' x) ≠ 0
    rw [ballPeriodize_projAt hρ hL f (mem_ballR4_of_ne_zero hf hx')]
    exact hx'
theorem ballPeriodizeValues_holds (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ)) :
    BallPeriodizeValues D m' ρ 𝕜 := by
  intro f hf
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, ballPeriodize_projAt_eq_tsum hρ hL hf, ?_, ?_,
    suppTorus_ballPeriodize hρ hL hf⟩
  · funext u
    by_cases hu : u ∈ D.projAt m' '' ballR4 ρ
    · obtain ⟨x, hx, rfl⟩ := hu
      rw [hg.1 x hx, ballPeriodize_projAt hρ hL f hx]
    · rw [hg.2 u hu, ballPeriodize_of_notMem_image hρ hL f hu]
  · rintro rfl
    exact D.isBallPeriodization_ballPeriodize f (injOn_projAt hρ hL)
  · intro x k k' h h'
    exact eq_of_add_latticeTranslate_mem hρ hL (mem_ballR4_of_ne_zero hf h)
      (mem_ballR4_of_ne_zero hf h')
  · intro ρ' hρ' hL' hf'
    funext u
    obtain ⟨x, rfl⟩ := projAt_surjective u
    rw [ballPeriodize_projAt_eq_tsum hρ' hL' hf', ballPeriodize_projAt_eq_tsum hρ hL hf]
theorem ballPeriodizeLinear_holds (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ)) :
    BallPeriodizeLinear D m' ρ 𝕜 := by
  intro f g a b hf hg
  have hsub : GluingSetup.suppR4 (a • f + b • g) ⊆
      GluingSetup.suppR4 f ∪ GluingSetup.suppR4 g := by
    refine (closure_mono ?_).trans closure_union.subset
    intro x hx
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hc
    exact hx (by simp [hc.1, hc.2])
  refine ⟨⟨(hf.1.union hg.1).of_isClosed_subset isClosed_closure hsub,
    hsub.trans (union_subset hf.2 hg.2)⟩, ?_⟩
  funext u
  by_cases hu : u ∈ D.projAt m' '' ballR4 ρ
  · obtain ⟨x, hx, rfl⟩ := hu
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [ballPeriodize_projAt hρ hL _ hx, ballPeriodize_projAt hρ hL _ hx,
      ballPeriodize_projAt hρ hL _ hx]
    simp
  · simp only [Pi.add_apply, Pi.smul_apply]
    rw [ballPeriodize_of_notMem_image hρ hL _ hu, ballPeriodize_of_notMem_image hρ hL _ hu,
      ballPeriodize_of_notMem_image hρ hL _ hu]
    simp
theorem ballPeriodize_projAt_of_nearest (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (hf : HasCompactSupportIn f (ballR4 ρ)) {x y : Fin 4 → ℝ}
    (hx : x ∈ ballR4 ρ)
    (hxy : euclidNormVec (x - y) =
      torusEuclidNorm (S := D.torusSideAt m') (D.projAt m' x - D.projAt m' y)) :
    D.ballPeriodize m' ρ f (D.projAt m' y) = f y := by
  by_cases hy : y ∈ ballR4 ρ
  · exact ballPeriodize_projAt hρ hL f hy
  · rw [apply_eq_zero_of_notMem hf hy]
    refine ballPeriodize_of_notMem_image hρ hL f ?_
    rintro ⟨y', hy', hq⟩
    obtain ⟨k, hk⟩ := exists_latticeTranslate_of_projAt_eq hq.symm
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [latticeTranslate_zero, add_zero] at hk
      exact hy (hk ▸ hy')
    have h1 := euclidNormVec_sub_lt_sub_latticeTranslate hρ hL hx hy' hk0
    have h2 : x - y' - latticeTranslate (D.torusSideAt m') k = x - y := by
      rw [hk]
      abel
    rw [h2, hxy, ← hq, torusEuclidNorm_projAt_sub hρ hL hx hy'] at h1
    exact lt_irrefl _ h1
theorem lipschitz_ballPeriodize_iff (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (hf : HasCompactSupportIn f (ballR4 ρ)) {C : ℝ} (hC : 0 ≤ C) :
    (∀ u v : D.torusAt m', ‖D.ballPeriodize m' ρ f u - D.ballPeriodize m' ρ f v‖ ≤
        C * euclidDistTorus (ℓ := D.torusSideAt m') u v) ↔
      ∀ x y : Fin 4 → ℝ, ‖f x - f y‖ ≤ C * euclidDistR4 x y := by
  constructor
  · intro h
    have key : ∀ x y : Fin 4 → ℝ, f x ≠ 0 → ‖f x - f y‖ ≤ C * euclidDistR4 x y := by
      intro x y hfx
      have hxB := mem_ballR4_of_ne_zero hf hfx
      by_cases hy : y ∈ ballR4 ρ
      · have h1 := h (D.projAt m' x) (D.projAt m' y)
        rw [ballPeriodize_projAt hρ hL f hxB, ballPeriodize_projAt hρ hL f hy] at h1
        have h2 : euclidDistTorus (ℓ := D.torusSideAt m') (D.projAt m' x) (D.projAt m' y) =
            euclidDistR4 x y := torusEuclidNorm_projAt_sub hρ hL hxB hy
        rwa [h2] at h1
      · obtain ⟨z₀, hz₀, hmax⟩ := hf.1.exists_isMaxOn
          ⟨x, subset_closure (show x ∈ {x | f x ≠ 0} from hfx)⟩
          continuous_euclidNormVec.continuousOn
        have hr : euclidNormVec z₀ < ρ := hf.2 hz₀
        have hxr : euclidNormVec x ≤ euclidNormVec z₀ :=
          hmax (subset_closure (show x ∈ {x | f x ≠ 0} from hfx))
        have hyρ : ρ ≤ euclidNormVec y := not_lt.1 hy
        set r' := (euclidNormVec z₀ + ρ) / 2 with hr'
        have hcont : Continuous fun t : ℝ => euclidNormVec (x + t • (y - x)) :=
          continuous_euclidNormVec.comp (by fun_prop)
        have hmem : r' ∈ Set.Icc (euclidNormVec (x + (0 : ℝ) • (y - x)))
            (euclidNormVec (x + (1 : ℝ) • (y - x))) := by
          simp only [zero_smul, add_zero, one_smul, add_sub_cancel]
          constructor <;> linarith
        obtain ⟨t, ht, htr⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn hmem
        have htr' : euclidNormVec (x + t • (y - x)) = r' := htr
        have hy'B : x + t • (y - x) ∈ ballR4 ρ := by
          show euclidNormVec (x + t • (y - x)) < ρ
          rw [htr']
          linarith
        have hfy' : f (x + t • (y - x)) = 0 := by
          by_contra hne
          have h3 : euclidNormVec (x + t • (y - x)) ≤ euclidNormVec z₀ :=
            hmax (subset_closure (show x + t • (y - x) ∈ {x | f x ≠ 0} from hne))
          linarith
        have h1 := h (D.projAt m' x) (D.projAt m' (x + t • (y - x)))
        rw [ballPeriodize_projAt hρ hL f hxB, ballPeriodize_projAt hρ hL f hy'B, hfy'] at h1
        have h2 : euclidDistTorus (ℓ := D.torusSideAt m') (D.projAt m' x)
            (D.projAt m' (x + t • (y - x))) = euclidNormVec (x - (x + t • (y - x))) :=
          torusEuclidNorm_projAt_sub hρ hL hxB hy'B
        have h4 : euclidNormVec (x - (x + t • (y - x))) ≤ euclidNormVec (x - y) := by
          have h5 : x - (x + t • (y - x)) = t • (x - y) := by
            funext μ
            simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            ring
          rw [h5, euclidNormVec_smul, abs_of_nonneg ht.1]
          exact mul_le_of_le_one_left (euclidNormVec_nonneg _) ht.2
        rw [h2] at h1
        rw [apply_eq_zero_of_notMem hf hy]
        exact h1.trans (mul_le_mul_of_nonneg_left h4 hC)
    intro x y
    by_cases hx : f x = 0
    · by_cases hy : f y = 0
      · rw [hx, hy, sub_zero, norm_zero]
        exact mul_nonneg hC (euclidNormVec_nonneg _)
      · have h1 := key y x hy
        rw [norm_sub_rev]
        have h2 : euclidDistR4 y x = euclidDistR4 x y := euclidNormVec_sub_comm y x
        rwa [h2] at h1
    · exact key x y hx
  · intro h
    have key : ∀ u v : D.torusAt m', D.ballPeriodize m' ρ f u ≠ 0 →
        ‖D.ballPeriodize m' ρ f u - D.ballPeriodize m' ρ f v‖ ≤
          C * euclidDistTorus (ℓ := D.torusSideAt m') u v := by
      intro u v hu
      obtain ⟨x, hx, rfl, hfx⟩ := exists_of_ballPeriodize_ne_zero hρ hL hu
      obtain ⟨b, hb, hb'⟩ :=
        exists_torusProj_eq_euclidNormVec_eq (S := D.torusSideAt m') (D.projAt m' x - v)
      have hqb : D.projAt m' b = D.projAt m' x - v := hb
      have hy : D.projAt m' (x - b) = v := by
        rw [map_sub, hqb, sub_sub_cancel]
      have hxy : euclidNormVec (x - (x - b)) =
          torusEuclidNorm (S := D.torusSideAt m') (D.projAt m' x - D.projAt m' (x - b)) := by
        rw [sub_sub_cancel, hy, hb']
      have ht := ballPeriodize_projAt_of_nearest hρ hL hf hx hxy
      rw [hy] at ht
      rw [ht, ← hfx]
      have h1 := h x (x - b)
      have h2 : euclidDistR4 x (x - b) =
          euclidDistTorus (ℓ := D.torusSideAt m') (D.projAt m' x) v := by
        show euclidNormVec (x - (x - b)) =
          torusEuclidNorm (S := D.torusSideAt m') (D.projAt m' x - v)
        rw [sub_sub_cancel, hb']
      rwa [h2] at h1
    intro u v
    by_cases hu : D.ballPeriodize m' ρ f u = 0
    · by_cases hv : D.ballPeriodize m' ρ f v = 0
      · rw [hu, hv, sub_zero, norm_zero]
        exact mul_nonneg hC (torusEuclidNorm_nonneg _)
      · have h1 := key v u hv
        rw [norm_sub_rev]
        have h2 : euclidDistTorus (ℓ := D.torusSideAt m') v u =
            euclidDistTorus (ℓ := D.torusSideAt m') u v :=
          torusEuclidNorm_sub_comm v u
        rwa [h2] at h1
    · exact key u v hu
theorem lipConstTorus_ballPeriodize (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (hf : HasCompactSupportIn f (ballR4 ρ)) :
    lipConstTorus (ℓ := D.torusSideAt m') (D.ballPeriodize m' ρ f) = lipConstR4 f := by
  unfold lipConstTorus lipConstR4 bestLipschitzConstant
  congr 1
  ext C
  constructor
  · rintro ⟨hC, h⟩
    exact ⟨hC, (lipschitz_ballPeriodize_iff hρ hL hf hC).1 h⟩
  · rintro ⟨hC, h⟩
    exact ⟨hC, (lipschitz_ballPeriodize_iff hρ hL hf hC).2 h⟩
theorem bddAbove_norm_of_lipschitz (hρ : 0 < ρ) (hf : HasCompactSupportIn f (ballR4 ρ))
    (hlip : IsLipschitzFor euclidDistR4 f) : BddAbove (range fun x => ‖f x‖) := by
  obtain ⟨C, hC, h⟩ := hlip
  set y₀ : Fin 4 → ℝ := fun _ => ρ with hy₀
  have hy : y₀ ∉ ballR4 ρ := by
    intro hb
    have h1 : euclidNormVec y₀ < ρ := hb
    have h2 := abs_apply_le_euclidNormVec y₀ 0
    simp only [hy₀, abs_of_pos hρ] at h2
    linarith
  refine ⟨C * (ρ + euclidNormVec y₀), ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ ballR4 ρ
  · have h1 := h x y₀
    rw [apply_eq_zero_of_notMem hf hy, sub_zero] at h1
    have h2 : euclidDistR4 x y₀ ≤ ρ + euclidNormVec y₀ := by
      have h3 := euclidNormVec_sub_le_add x y₀
      have h4 : euclidNormVec x < ρ := hx
      have h5 : euclidDistR4 x y₀ = euclidNormVec (x - y₀) := rfl
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC)
  · show ‖f x‖ ≤ _
    rw [apply_eq_zero_of_notMem hf hx, norm_zero]
    exact mul_nonneg hC (add_nonneg hρ.le (euclidNormVec_nonneg _))
theorem uniformNorm_ballPeriodize (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (hf : HasCompactSupportIn f (ballR4 ρ)) (hlip : IsLipschitzFor euclidDistR4 f) :
    uniformNorm (D.ballPeriodize m' ρ f) = uniformNorm f := by
  have hb := bddAbove_norm_of_lipschitz hρ hf hlip
  have hnn : 0 ≤ uniformNorm f := (norm_nonneg (f 0)).trans (le_ciSup hb 0)
  have hbT : BddAbove (range fun u => ‖D.ballPeriodize m' ρ f u‖) := by
    refine ⟨uniformNorm f, ?_⟩
    rintro _ ⟨u, rfl⟩
    by_cases hu : D.ballPeriodize m' ρ f u = 0
    · show ‖D.ballPeriodize m' ρ f u‖ ≤ _
      rw [hu, norm_zero]
      exact hnn
    · obtain ⟨x, -, -, hfx⟩ := exists_of_ballPeriodize_ne_zero hρ hL hu
      show ‖D.ballPeriodize m' ρ f u‖ ≤ _
      rw [← hfx]
      exact le_ciSup hb x
  refine le_antisymm (ciSup_le fun u => ?_) (ciSup_le fun x => ?_)
  · by_cases hu : D.ballPeriodize m' ρ f u = 0
    · rw [hu, norm_zero]
      exact hnn
    · obtain ⟨x, -, -, hfx⟩ := exists_of_ballPeriodize_ne_zero hρ hL hu
      rw [← hfx]
      exact le_ciSup hb x
  · by_cases hx : x ∈ ballR4 ρ
    · rw [← ballPeriodize_projAt hρ hL f hx]
      exact le_ciSup hbT (D.projAt m' x)
    · rw [apply_eq_zero_of_notMem hf hx, norm_zero]
      exact (norm_nonneg (D.ballPeriodize m' ρ f 0)).trans (le_ciSup hbT 0)
theorem contDiff_ballPeriodize_comp_projAt (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (hf : HasCompactSupportIn f (ballR4 ρ)) {n : WithTop ℕ∞} (hc : ContDiff ℝ n f) :
    ContDiff ℝ n (D.ballPeriodize m' ρ f ∘ D.projAt m') := by
  have hℓ : 4 * ρ + 4 ≤ D.torusSideAt m' := by
    rw [torusSideAt_eq]
    linarith
  refine contDiff_iff_contDiffAt.2 fun x₀ => ?_
  have hU : {x : Fin 4 → ℝ | euclidNormVec (x - x₀) < 1 / 2} ∈ 𝓝 x₀ := by
    refine IsOpen.mem_nhds (isOpen_lt
      (continuous_euclidNormVec.comp (continuous_id.sub continuous_const)) continuous_const) ?_
    show euclidNormVec (x₀ - x₀) < 1 / 2
    rw [sub_self]
    simp [euclidNormVec]
  by_cases h : ∃ x, euclidNormVec (x - x₀) < 1 / 2 ∧
      ∃ k, x + latticeTranslate (D.torusSideAt m') k ∈ ballR4 ρ
  · obtain ⟨x₁, hx₁, k₀, hk₀⟩ := h
    have hc' : ContDiffAt ℝ n (fun x => f (x + latticeTranslate (D.torusSideAt m') k₀)) x₀ :=
      (hc.comp (contDiff_id.add contDiff_const)).contDiffAt
    refine hc'.congr_of_eventuallyEq (Filter.mem_of_superset hU fun x hx => ?_)
    have hx' : euclidNormVec (x - x₀) < 1 / 2 := hx
    show D.ballPeriodize m' ρ f (D.projAt m' x) = f (x + latticeTranslate (D.torusSideAt m') k₀)
    rw [← projAt_add_latticeTranslate (D := D) (m' := m') x k₀]
    by_cases hb : x + latticeTranslate (D.torusSideAt m') k₀ ∈ ballR4 ρ
    · exact ballPeriodize_projAt hρ hL f hb
    · rw [apply_eq_zero_of_notMem hf hb]
      refine ballPeriodize_of_notMem_image hρ hL f ?_
      rintro ⟨y, hy, hq⟩
      obtain ⟨k, hk⟩ := exists_latticeTranslate_of_projAt_eq hq
      have hkk : k = 0 := by
        by_contra hk0
        have h1 := le_euclidNormVec_latticeTranslate (by linarith : 0 < D.torusSideAt m') hk0
        have h2 : latticeTranslate (D.torusSideAt m') k =
            (y - (x₁ + latticeTranslate (D.torusSideAt m') k₀)) - (x - x₁) := by
          rw [hk]
          abel
        have h3 := euclidNormVec_sub_le x x₀ x₁
        rw [euclidNormVec_sub_comm x₀ x₁] at h3
        have h4 := euclidNormVec_sub_le_add (y - (x₁ + latticeTranslate (D.torusSideAt m') k₀))
          (x - x₁)
        have h5 := euclidNormVec_sub_le_add y (x₁ + latticeTranslate (D.torusSideAt m') k₀)
        have h6 : euclidNormVec y < ρ := hy
        have h7 : euclidNormVec (x₁ + latticeTranslate (D.torusSideAt m') k₀) < ρ := hk₀
        rw [← h2] at h4
        linarith
      rw [hkk, latticeTranslate_zero, add_zero] at hk
      exact hb (hk ▸ hy)
  · refine (contDiffAt_const (c := (0 : 𝕜))).congr_of_eventuallyEq
      (Filter.mem_of_superset hU fun x hx => ?_)
    show D.ballPeriodize m' ρ f (D.projAt m' x) = 0
    refine ballPeriodize_of_notMem_image hρ hL f ?_
    rintro ⟨y, hy, hq⟩
    obtain ⟨k, hk⟩ := exists_latticeTranslate_of_projAt_eq hq
    exact h ⟨x, hx, k, hk ▸ hy⟩
theorem ballPeriodizeNormsAndRegularity_holds (hρ : 0 < ρ)
    (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ)) :
    BallPeriodizeNormsAndRegularity D m' ρ 𝕜 := by
  intro f hf
  refine ⟨fun hlip => ?_, fun hc => contDiff_ballPeriodize_comp_projAt hρ hL hf hc,
    fun hc => contDiff_ballPeriodize_comp_projAt hρ hL hf hc⟩
  have hsup := uniformNorm_ballPeriodize hρ hL hf hlip
  have hLip := lipConstTorus_ballPeriodize hρ hL hf
  refine ⟨?_, hsup, hLip, ?_⟩
  · obtain ⟨C, hC, h⟩ := hlip
    exact ⟨C, hC, (lipschitz_ballPeriodize_iff hρ hL hf hC).2 h⟩
  · show max (uniformNorm (D.ballPeriodize m' ρ f))
        (40 * D.M * lipConstTorus (ℓ := D.torusSideAt m') (D.ballPeriodize m' ρ f)) =
      max (uniformNorm f) (40 * D.M * lipConstR4 f)
    rw [hsup, hLip]
theorem ballPeriodizeSuppNear_holds (hρ : 0 < ρ)
    (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ)) :
    BallPeriodizeSuppNear D m' ρ 𝕜 := by
  intro f hf x R _ hsub u hu
  rw [suppTorus_ballPeriodize hρ hL hf] at hu
  obtain ⟨y, hy, rfl⟩ := hu
  rw [D.torusDist_eq_torusEuclidNorm]
  exact (torusEuclidNorm_projAt_sub_le y x).trans (hsub hy)
theorem ballPeriodizeComp_holds (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ)) :
    BallPeriodizeComp D m' ρ 𝕜 := by
  intro f s hf hfs
  have hs : ∀ x, D.inducedMotion m' s (D.projAt m' x) =
      D.projAt m' ((s : Equiv.Perm (Fin 4 → ℝ)) x) :=
    fun x => congrFun (D.inducedMotion_descends m' s) x
  funext u
  obtain ⟨x, rfl⟩ := projAt_surjective u
  show D.ballPeriodize m' ρ (f ∘ (s : Equiv.Perm (Fin 4 → ℝ))) (D.projAt m' x) =
    D.ballPeriodize m' ρ f (D.inducedMotion m' s (D.projAt m' x))
  by_cases h : D.ballPeriodize m' ρ (f ∘ (s : Equiv.Perm (Fin 4 → ℝ))) (D.projAt m' x) = 0
  · rw [h]
    by_contra hne
    obtain ⟨y, -, hq, hfy⟩ := exists_of_ballPeriodize_ne_zero hρ hL (Ne.symm hne)
    have hfy0 : f y ≠ 0 := by
      rw [hfy]
      exact Ne.symm hne
    set x' := (s : Equiv.Perm (Fin 4 → ℝ)).symm y with hx'
    have hsx : (s : Equiv.Perm (Fin 4 → ℝ)) x' = y := Equiv.apply_symm_apply _ y
    have hne' : (f ∘ (s : Equiv.Perm (Fin 4 → ℝ))) x' ≠ 0 := by
      simpa only [Function.comp_apply, hsx] using hfy0
    have hx'B := mem_ballR4_of_ne_zero hfs hne'
    have hqx : D.projAt m' x' = D.projAt m' x := by
      apply (D.inducedMotion m' s).injective
      rw [hs, hsx, hq]
    rw [← hqx, ballPeriodize_projAt hρ hL _ hx'B] at h
    exact hne' h
  · obtain ⟨x', -, hq, hfx⟩ := exists_of_ballPeriodize_ne_zero hρ hL h
    have hne : (f ∘ (s : Equiv.Perm (Fin 4 → ℝ))) x' ≠ 0 := by
      rw [hfx]
      exact h
    have hB : (s : Equiv.Perm (Fin 4 → ℝ)) x' ∈ ballR4 ρ :=
      mem_ballR4_of_ne_zero hf hne
    rw [← hfx, ← hq, hs, ballPeriodize_projAt hρ hL f hB]
    rfl
theorem ballPeriodizeSuppDist_holds (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (𝕜' : Type) [RCLike 𝕜'] : BallPeriodizeSuppDist D m' ρ 𝕜 𝕜' := by
  intro f g hf hg
  rw [suppTorus_ballPeriodize hρ hL hf, suppTorus_ballPeriodize hρ hL hg]
  unfold setEuclidDist setDistR4
  simp only [iInf_image]
  refine iInf_congr fun a => iInf_congr fun ha => iInf_congr fun b => iInf_congr fun hb => ?_
  exact congrArg ENNReal.ofReal (torusEuclidNorm_projAt_sub hρ hL (hf.2 ha) (hg.2 hb))
end Functions
open Ambient
theorem hasCompactSupportIn_of_suppR4_subset {g : (Fin 4 → ℝ) → ℝ}
    (hg : GluingSetup.suppR4 g ⊆ ballR4 ρ) :
    HasCompactSupportIn g (ballR4 ρ) := by
  refine ⟨Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_, hg⟩
  refine (Metric.isBounded_closedBall (x := (0 : Fin 4 → ℝ)) (r := ρ)).subset fun x hx => ?_
  have h1 : euclidNormVec x < ρ := hg hx
  rw [mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg ((euclidNormVec_nonneg x).trans h1.le)).2 fun μ =>
    (abs_apply_le_euclidNormVec x μ).trans h1.le
theorem ballPeriodizeTuples_holds (hρ : 0 < ρ) (hL : 2 * ρ + 2 ≤ (D.L : ℝ) ^ (m' : ℕ))
    (n : ℕ+) : BallPeriodizeTuples D m' ρ n := by
  have hN := ballPeriodizeNormsAndRegularity_holds (D := D) (m' := m') (𝕜 := ℝ) hρ hL
  have hsupp : ∀ f ∈ sepLipBall D ρ n, ∀ i,
      HasCompactSupportIn (f i) (ballR4 ρ) := fun f hf i => ⟨hf.1.2.1 i, hf.2 i⟩
  have hdisj : ∀ f : euclidean.FunTuple D n, euclidean.CompactDisjointSupp f →
      euclidean.SuppSubset f (ballR4 ρ) →
      (torus m').CompactDisjointSupp (S := D) (D.ballPeriodizeTuple m' ρ f) := by
    intro f hf hB
    have hs : ∀ i, (torus m').supp D (D.ballPeriodizeTuple m' ρ f i) =
        D.projAt m' '' GluingSetup.suppR4 (f i) := fun i =>
      suppTorus_ballPeriodize hρ hL ⟨hf.1 i, hB i⟩
    refine ⟨fun i => ?_, fun i k hik => ?_⟩
    · rw [hs]
      exact (hf.1 i).image continuous_projAt
    · rw [hs, hs]
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have hba := injOn_projAt hρ hL (hB k hb) (hB i ha) hab
      subst hba
      exact Set.disjoint_left.mp (hf.2 i k hik) ha hb
  refine ⟨fun f hf => ⟨fun i => ((hN (f i) (hsupp f hf i)).1 (hf.1.1 i)).1,
      hdisj f hf.1.2 hf.2⟩, ?_, fun f hf i => ((hN (f i) (hsupp f hf i)).1 (hf.1.1 i)).2.2.2,
    fun _ f hf => ?_, fun f _ J hJ => rfl, fun f hf => ?_, ?_⟩
  · intro i a b f hf f' hf' f'' hf'' hk hi
    refine ⟨fun k hki => ⟨?_, ?_⟩, ?_⟩
    · show D.ballPeriodize m' ρ (f k) = D.ballPeriodize m' ρ (f' k)
      rw [(hk k hki).1]
    · show D.ballPeriodize m' ρ (f k) = D.ballPeriodize m' ρ (f'' k)
      rw [(hk k hki).2]
    · show D.ballPeriodize m' ρ (f'' i) = _
      rw [hi]
      exact (ballPeriodizeLinear_holds hρ hL (f i) (f' i) a b (hsupp f hf i)
        (hsupp f' hf' i)).2
  · refine iInf_congr fun i => iInf_congr fun k => iInf_congr fun _ => ?_
    exact ballPeriodizeSuppDist_holds hρ hL ℝ (f i) (f k) (hsupp f hf i) (hsupp f hf k)
  · have hsep : ∀ i, HasCompactSupportIn (f i) (ballR4 ρ) := fun i =>
      ⟨hf.1.2.1 i, hf.2 i⟩
    exact ⟨fun i => (hN (f i) (hsep i)).2.1 (hf.1.1 i), hdisj f hf.1.2 hf.2⟩
  · intro d R _ _ _ f hf hB
    have hsep : ∀ i, HasCompactSupportIn (f i) (ballR4 ρ) := fun i =>
      hasCompactSupportIn_of_suppR4_subset (hB i)
    refine ⟨fun i => ((hN (f i) (hsep i)).1 (hf.1 i)).1, fun i => ?_, fun i k hik => ?_⟩
    · obtain ⟨x, hx⟩ := hf.2.1 i
      refine ⟨D.projAt m' x, fun u hu => ?_⟩
      have h1 := ballPeriodizeSuppNear_holds (D := D) (m' := m') (𝕜 := ℝ) hρ hL (f i) (hsep i)
        x R ‹_› hx u hu
      rwa [D.torusDist_eq_torusEuclidNorm] at h1
    · have h1 := ballPeriodizeSuppDist_holds (D := D) (m' := m') hρ hL ℝ (f i) (f k)
        (hsep i) (hsep k)
      exact (hf.2.2 i k hik).trans_eq h1.symm
theorem torusPeriodizationOfBall : Statement := by
  intro D m' ρ hρ hL
  exact ⟨projIsometricOnBall_holds hρ hL,
    fun 𝕜 _ => ⟨ballPeriodizeValues_holds hρ hL, ballPeriodizeLinear_holds hρ hL,
      ballPeriodizeNormsAndRegularity_holds hρ hL, ballPeriodizeSuppNear_holds hρ hL,
      ballPeriodizeComp_holds hρ hL⟩,
    fun 𝕜 𝕜' _ _ => ballPeriodizeSuppDist_holds hρ hL 𝕜',
    fun n => ballPeriodizeTuples_holds hρ hL n⟩
end
end YangMills.Construction.SourcesAndGluing.TorusPeriodizationOfBall
