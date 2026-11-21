import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.PassageToTheLimit.TransportedLatticeFunctionalsAreBoundedFormsProof
import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPair
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice TestFunctions
namespace TestPairs
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem euclidNormVec_sub_comm (u v : Fin 4 → ℝ) :
    euclidNormVec (u - v) = euclidNormVec (v - u) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNormVec_smul (a : ℝ) (v : Fin 4 → ℝ) :
    euclidNormVec (a • v) = |a| * euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem euclidNormVec_zero : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [euclidNormVec]
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem isClosed_closedBallR4 (c : Fin 4 → ℝ) (R : ℝ) : IsClosed (closedBallR4 c R) :=
  isClosed_le (continuous_euclidNormVec.comp (continuous_id.sub continuous_const)) continuous_const
theorem isCompact_closedBallR4 (c : Fin 4 → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (closedBallR4 c R) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_closedBallR4 c R)
    ((Metric.isBounded_closedBall (x := c) (r := R)).subset ?_)
  intro t ht
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro μ
  rw [Real.dist_eq]
  exact (abs_apply_le_euclidNormVec (t - c) μ).trans ht
theorem euclidNormVec_sub_le_two_mul_of_mem {c t t' : Fin 4 → ℝ} {R : ℝ}
    (ht : t ∈ closedBallR4 c R) (ht' : t' ∈ closedBallR4 c R) :
    euclidNormVec (t - t') ≤ 2 * R := by
  have h : t - t' = (t - c) + (c - t') := by abel
  have ht1 : euclidNormVec (t - c) ≤ R := ht
  have ht2 : euclidNormVec (t' - c) ≤ R := ht'
  rw [h]
  have := euclidNormVec_add_le (t - c) (c - t')
  rw [euclidNormVec_sub_comm c t'] at this
  linarith
theorem le_euclidNormVec_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ euclidNormVec (latticeTranslate ℓ k) := by
  obtain ⟨μ, hμ⟩ := Function.ne_iff.mp hk
  refine le_trans ?_ (abs_apply_le_euclidNormVec _ μ)
  have h1 : (1 : ℝ) ≤ |(k μ : ℝ)| := by
    have : (1 : ℤ) ≤ |k μ| := Int.one_le_abs hμ
    exact_mod_cast this
  simp only [latticeTranslate, abs_mul, abs_of_pos hℓ]
  nlinarith
section MinimalLift
variable {ℓ : ℝ}
theorem torusProj_map_add (t t' : Fin 4 → ℝ) :
    torusProj ℓ (t + t') = torusProj ℓ t + torusProj ℓ t' := by
  funext μ
  simp [torusProj]
theorem torusProj_map_sub (t t' : Fin 4 → ℝ) :
    torusProj ℓ (t - t') = torusProj ℓ t - torusProj ℓ t' := by
  funext μ
  simp [torusProj]
theorem torusProj_map_zero : torusProj ℓ (0 : Fin 4 → ℝ) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.torusProj_zero <;> assumption
theorem continuous_torusProj : Continuous (torusProj ℓ) :=
  continuous_pi fun μ => (AddCircle.continuous_mk' _).comp (continuous_apply μ)
theorem exists_minimal_lift (u : Torus4 ℓ) :
    ∃ τ, torusProj ℓ τ = u ∧ euclidNormVec τ = torusEuclidNorm u ∧
      torusEuclidNorm u = Real.sqrt (∑ μ, ‖u μ‖ ^ 2) := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (u μ)
  have hcov : torusProj ℓ b = u := funext hb
  have hval : euclidNormVec b = Real.sqrt (∑ μ, ‖u μ‖ ^ 2) := by
    unfold euclidNormVec
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← hb' μ, sq_abs]
  have hleast : IsLeast (euclidNormVec '' (torusProj ℓ ⁻¹' {u})) (euclidNormVec b) := by
    refine ⟨⟨b, hcov, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have hv' : torusProj ℓ v = u := hv
    rw [hval]
    unfold euclidNormVec
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
    rw [← hv', ← sq_abs (v μ)]
    exact pow_le_pow_left₀ (norm_nonneg _) (addCircle_norm_coe_le_abs _) 2
  have hnum : torusEuclidNorm u = euclidNormVec b := hleast.csInf_eq
  exact ⟨b, hcov, hnum.symm, hnum.trans hval⟩
theorem torusEuclidNorm_nonneg (u : Torus4 ℓ) : 0 ≤ torusEuclidNorm u := by
  obtain ⟨τ, -, h, -⟩ := exists_minimal_lift u
  rw [← h]
  exact euclidNormVec_nonneg _
theorem torusEuclidNorm_torusProj_le (t : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj ℓ t) ≤ euclidNormVec t := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
theorem torusEuclidNorm_neg (u : Torus4 ℓ) : torusEuclidNorm (-u) = torusEuclidNorm u := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.torusEuclidNorm_neg <;> assumption
theorem torusEuclidNorm_add_le (u v : Torus4 ℓ) :
    torusEuclidNorm (u + v) ≤ torusEuclidNorm u + torusEuclidNorm v := by
  obtain ⟨τ, hτ, h, -⟩ := exists_minimal_lift u
  obtain ⟨σ, hσ, h', -⟩ := exists_minimal_lift v
  rw [← h, ← h', ← hτ, ← hσ, ← torusProj_map_add]
  exact (torusEuclidNorm_torusProj_le _).trans (euclidNormVec_add_le _ _)
theorem continuous_torusEuclidNorm : Continuous (torusEuclidNorm : Torus4 ℓ → ℝ) := by
  have h : (torusEuclidNorm : Torus4 ℓ → ℝ) = fun u => Real.sqrt (∑ μ, ‖u μ‖ ^ 2) :=
    funext fun u => (exists_minimal_lift u).choose_spec.2.2
  rw [h]
  fun_prop
theorem torusEuclidNorm_zero : torusEuclidNorm (0 : Torus4 ℓ) = 0 := by
  have h := torusEuclidNorm_torusProj_le (ℓ := ℓ) 0
  rw [torusProj_map_zero, euclidNormVec_zero] at h
  exact le_antisymm h (torusEuclidNorm_nonneg _)
theorem torusEuclidNorm_torusProj_of_le_half (hℓ : 0 < ℓ) {t : Fin 4 → ℝ}
    (ht : euclidNormVec t ≤ ℓ / 2) : torusEuclidNorm (torusProj ℓ t) = euclidNormVec t := by
  refine le_antisymm (torusEuclidNorm_torusProj_le t) ?_
  obtain ⟨τ, hτ, hn, -⟩ := exists_minimal_lift (torusProj ℓ t)
  rw [← hn]
  obtain ⟨k, rfl⟩ := exists_latticeTranslate_of_torusProj_eq hτ
  by_cases hk : k = 0
  · subst hk
    have : latticeTranslate ℓ (0 : Fin 4 → ℤ) = 0 := by
      funext μ
      simp [latticeTranslate]
    rw [this, add_zero]
  · have h1 := le_euclidNormVec_latticeTranslate hℓ hk
    have h2 := euclidNormVec_add_le (t + latticeTranslate ℓ k) (-t)
    rw [euclidNormVec_neg, add_comm t, add_neg_cancel_right, add_comm _ t] at h2
    linarith
theorem torusProj_image_closedBallR4 (c : Fin 4 → ℝ) (R : ℝ) :
    torusProj ℓ '' closedBallR4 c R = closedBallTorus (torusProj ℓ c) R := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    show torusEuclidNorm (torusProj ℓ t - torusProj ℓ c) ≤ R
    rw [← torusProj_map_sub]
    exact (torusEuclidNorm_torusProj_le _).trans ht
  · intro hu
    obtain ⟨τ, hτ, hn, -⟩ := exists_minimal_lift (u - torusProj ℓ c)
    refine ⟨c + τ, ?_, ?_⟩
    · show euclidNormVec (c + τ - c) ≤ R
      rw [add_sub_cancel_left, hn]
      exact hu
    · rw [torusProj_map_add, hτ]
      abel
theorem euclidDistTorus_torusProj_of_mem (hℓ : 0 < ℓ) {c t t' : Fin 4 → ℝ} {R : ℝ}
    (hR : R ≤ ℓ / 4) (ht : t ∈ closedBallR4 c R) (ht' : t' ∈ closedBallR4 c R) :
    euclidDistTorus (torusProj ℓ t) (torusProj ℓ t') = euclidDistR4 t t' := by
  show torusEuclidNorm (torusProj ℓ t - torusProj ℓ t') = euclidNormVec (t - t')
  rw [← torusProj_map_sub]
  apply torusEuclidNorm_torusProj_of_le_half hℓ
  have := euclidNormVec_sub_le_two_mul_of_mem ht ht'
  linarith
theorem closedBallR4_subset_centredIcoCube (hℓ : 0 < ℓ) {c : Fin 4 → ℝ} {R : ℝ}
    (hR : R ≤ ℓ / 4) : closedBallR4 c R ⊆ centredIcoCube ℓ c := by
  intro t ht μ _
  have h := abs_le.mp ((abs_apply_le_euclidNormVec (t - c) μ).trans ht)
  simp only [Pi.sub_apply] at h
  constructor <;> linarith [h.1, h.2]
theorem injOn_torusProj_closedBallR4 (hℓ : 0 < ℓ) {c : Fin 4 → ℝ} {R : ℝ} (hR : R ≤ ℓ / 4) :
    InjOn (torusProj ℓ) (closedBallR4 c R) :=
  (bijOn_torusProj_centredIcoCube hℓ c).injOn.mono (closedBallR4_subset_centredIcoCube hℓ hR)
end MinimalLift
section BallCompatible
variable {ℓ : ℝ} {c : Fin 4 → ℝ} {r : ℝ}
def BallCompatible (ℓ : ℝ) (c : Fin 4 → ℝ) (r : ℝ) (ψ : (Fin 4 → ℝ) → ℝ) (φ : Torus4 ℓ → ℝ) :
    Prop :=
  (∀ t, t ∉ closedBallR4 c r → ψ t = 0) ∧ (∀ t ∈ closedBallR4 c r, φ (torusProj ℓ t) = ψ t) ∧
    ∀ u, u ∉ closedBallTorus (torusProj ℓ c) r → φ u = 0
theorem ballCompatible_liftToBall {φ : Torus4 ℓ → ℝ}
    (h0 : ∀ u, u ∉ closedBallTorus (torusProj ℓ c) r → φ u = 0) :
    BallCompatible ℓ c r (liftToBall ℓ c r φ) φ := by
  refine ⟨fun t ht => indicator_of_notMem ht _, fun t ht => ?_, h0⟩
  rw [liftToBall, indicator_of_mem ht]
  rfl
variable {ψ : (Fin 4 → ℝ) → ℝ} {φ : Torus4 ℓ → ℝ}
theorem liftToBall_eq_of_ballCompatible (h : BallCompatible ℓ c r ψ φ) :
    liftToBall ℓ c r φ = ψ := by
  funext t
  by_cases ht : t ∈ closedBallR4 c r
  · rw [liftToBall, indicator_of_mem ht, ← h.2.1 t ht]
    rfl
  · rw [liftToBall, indicator_of_notMem ht, h.1 t ht]
theorem mem_closedBallR4_of_ne_zero (h : BallCompatible ℓ c r ψ φ) {t : Fin 4 → ℝ}
    (ht : ψ t ≠ 0) : t ∈ closedBallR4 c r := by
  by_contra hn
  exact ht (h.1 t hn)
theorem exists_mem_torusProj_eq_of_ne_zero (h : BallCompatible ℓ c r ψ φ) {u : Torus4 ℓ}
    (hu : φ u ≠ 0) : ∃ t ∈ closedBallR4 c r, torusProj ℓ t = u := by
  have hm : u ∈ closedBallTorus (torusProj ℓ c) r := by
    by_contra hn
    exact hu (h.2.2 u hn)
  rw [← torusProj_image_closedBallR4] at hm
  exact hm
theorem ballCompatible_periodize (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4)
    (h0 : ∀ t, t ∉ closedBallR4 c r → ψ t = 0) : BallCompatible ℓ c r ψ (periodize ℓ ψ) := by
  have hper0 : latticeTranslate ℓ (0 : Fin 4 → ℤ) = 0 := by
    funext μ
    simp [latticeTranslate]
  refine ⟨h0, fun t ht => ?_, fun u hu => ?_⟩
  · rw [periodize_torusProj, periodicSum, tsum_eq_single (0 : Fin 4 → ℤ)]
    · rw [hper0, add_zero]
    · intro k hk
      apply h0
      intro hm
      have he := injOn_torusProj_closedBallR4 hℓ hr hm ht (torusProj_add_latticeTranslate ℓ t k)
      have hz : latticeTranslate ℓ k = 0 := by simpa using he
      have h1 := le_euclidNormVec_latticeTranslate hℓ hk
      rw [hz, euclidNormVec_zero] at h1
      linarith
  · obtain ⟨t, rfl⟩ := torusProj_surjective ℓ u
    rw [periodize_torusProj, periodicSum]
    have hall : ∀ k : Fin 4 → ℤ, ψ (t + latticeTranslate ℓ k) = 0 := by
      intro k
      apply h0
      intro hm
      apply hu
      rw [← torusProj_image_closedBallR4]
      exact ⟨_, hm, torusProj_add_latticeTranslate ℓ t k⟩
    simp only [hall, tsum_zero]
theorem bddAbove_range_of_values {A B : Type*} [Nonempty B] {a : A → ℝ} {b : B → ℝ}
    (Hab : ∀ x, a x = 0 ∨ ∃ y, b y = a x) (hb : ∀ y, 0 ≤ b y) (hB : BddAbove (range b)) :
    BddAbove (range a) := by
  obtain ⟨M, hM⟩ := hB
  refine ⟨M, ?_⟩
  rintro _ ⟨x, rfl⟩
  rcases Hab x with h | ⟨y, hy⟩
  · rw [h]
    exact (hb (Classical.arbitrary B)).trans (hM ⟨_, rfl⟩)
  · rw [← hy]
    exact hM ⟨y, rfl⟩
theorem iSup_eq_of_nonzero_values {X Y : Type*} [Nonempty X] [Nonempty Y] {g : X → ℝ}
    {g' : Y → ℝ} (hg : ∀ x, 0 ≤ g x) (hg' : ∀ y, 0 ≤ g' y) (H : ∀ x, g x = 0 ∨ ∃ y, g' y = g x)
    (H' : ∀ y, g' y = 0 ∨ ∃ x, g x = g' y) : ⨆ x, g x = ⨆ y, g' y := by
  by_cases hb : BddAbove (range g)
  · have hb' : BddAbove (range g') := bddAbove_range_of_values H' hg hb
    apply le_antisymm
    · refine ciSup_le fun x => ?_
      rcases H x with h | ⟨y, hy⟩
      · rw [h]
        exact Real.iSup_nonneg hg'
      · rw [← hy]
        exact le_ciSup hb' y
    · refine ciSup_le fun y => ?_
      rcases H' y with h | ⟨x, hx⟩
      · rw [h]
        exact Real.iSup_nonneg hg
      · rw [← hx]
        exact le_ciSup hb x
  · have hb' : ¬ BddAbove (range g') := fun h => hb (bddAbove_range_of_values H hg' h)
    rw [Real.iSup_of_not_bddAbove hb, Real.iSup_of_not_bddAbove hb']
theorem uniformNorm_eq_of_ballCompatible (h : BallCompatible ℓ c r ψ φ) :
    uniformNorm ψ = uniformNorm φ := by
  refine iSup_eq_of_nonzero_values (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) ?_ ?_
  · intro t
    by_cases ht : ψ t = 0
    · left
      simp [ht]
    · right
      exact ⟨torusProj ℓ t, by rw [h.2.1 t (mem_closedBallR4_of_ne_zero h ht)]⟩
  · intro u
    by_cases hu : φ u = 0
    · left
      simp [hu]
    · right
      obtain ⟨t, ht, rfl⟩ := exists_mem_torusProj_eq_of_ne_zero h hu
      exact ⟨t, by rw [h.2.1 t ht]⟩
theorem euclidDistTorus_comm (u w : Torus4 ℓ) : euclidDistTorus u w = euclidDistTorus w u := by
  show torusEuclidNorm (u - w) = torusEuclidNorm (w - u)
  rw [← neg_sub, torusEuclidNorm_neg]
theorem lipschitz_bound_descends (h : BallCompatible ℓ c r ψ φ) {C : ℝ}
    (H : ∀ t t', ‖ψ t - ψ t'‖ ≤ C * euclidDistR4 t t') {u w : Torus4 ℓ}
    (hu : φ u ≠ 0) (hw : φ w = 0) : ‖φ u - φ w‖ ≤ C * euclidDistTorus w u := by
  obtain ⟨t, ht, rfl⟩ := exists_mem_torusProj_eq_of_ne_zero h hu
  obtain ⟨τ, hτ, hn, -⟩ := exists_minimal_lift (w - torusProj ℓ t)
  have hcov : torusProj ℓ (t + τ) = w := by
    rw [torusProj_map_add, hτ]
    abel
  have hz : ψ (t + τ) = 0 := by
    by_cases hm : t + τ ∈ closedBallR4 c r
    · rw [← h.2.1 _ hm, hcov, hw]
    · exact h.1 _ hm
  have h1 := H t (t + τ)
  rw [hz, ← h.2.1 t ht] at h1
  rw [hw]
  have hd : euclidDistR4 t (t + τ) = euclidDistTorus w (torusProj ℓ t) := by
    show euclidNormVec (t - (t + τ)) = torusEuclidNorm (w - torusProj ℓ t)
    rw [← hn, sub_add_cancel_left, euclidNormVec_neg]
  rwa [hd] at h1
theorem lipschitz_bound_ascends (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h : BallCompatible ℓ c r ψ φ) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ u w : Torus4 ℓ, ‖φ u - φ w‖ ≤ C * euclidDistTorus u w)
    {t t' : Fin 4 → ℝ} (ht : t ∈ closedBallR4 c r) (ht' : t' ∉ closedBallR4 c r) :
    ‖ψ t - ψ t'‖ ≤ C * euclidDistR4 t t' := by
  set ρ : ℝ → ℝ := fun θ => euclidNormVec (t + θ • (t' - t) - c) with hρ
  have hcont : Continuous ρ := continuous_euclidNormVec.comp (by fun_prop)
  have h0 : ρ 0 ≤ r := by
    have ht0 : euclidNormVec (t - c) ≤ r := ht
    simpa [hρ] using ht0
  have h1 : r < ρ 1 := by
    have : ¬ euclidNormVec (t' - c) ≤ r := ht'
    simpa [hρ] using not_le.mp this
  have hr' : r < min (ρ 1) (ℓ / 2) := by
    refine lt_min h1 ?_
    linarith
  have hmem : min (ρ 1) (ℓ / 2) ∈ Icc (ρ 0) (ρ 1) := ⟨h0.trans hr'.le, min_le_left _ _⟩
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hθ⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn hmem
  have hfar : euclidNormVec (t + θ • (t' - t) - c) ≤ ℓ / 2 := by
    have : ρ θ ≤ ℓ / 2 := by
      rw [hθ]
      exact min_le_right _ _
    exact this
  have hoff : torusProj ℓ (t + θ • (t' - t)) ∉ closedBallTorus (torusProj ℓ c) r := by
    intro hm
    have hm' : torusEuclidNorm (torusProj ℓ (t + θ • (t' - t)) - torusProj ℓ c) ≤ r := hm
    rw [← torusProj_map_sub, torusEuclidNorm_torusProj_of_le_half hℓ hfar] at hm'
    have : ρ θ ≤ r := hm'
    rw [hθ] at this
    exact absurd this (not_le.mpr hr')
  have hz := h.2.2 _ hoff
  have h2 := H (torusProj ℓ t) (torusProj ℓ (t + θ • (t' - t)))
  rw [hz, h.2.1 t ht] at h2
  rw [h.1 t' ht']
  have hd : euclidDistTorus (torusProj ℓ t) (torusProj ℓ (t + θ • (t' - t))) ≤
      euclidDistR4 t t' := by
    show torusEuclidNorm (torusProj ℓ t - torusProj ℓ (t + θ • (t' - t))) ≤ euclidNormVec (t - t')
    rw [← torusProj_map_sub]
    refine (torusEuclidNorm_torusProj_le _).trans ?_
    have he : t - (t + θ • (t' - t)) = θ • (t - t') := by
      rw [sub_add_cancel_left, ← smul_neg, neg_sub]
    rw [he, euclidNormVec_smul, abs_of_nonneg hθ0]
    have := euclidNormVec_nonneg (t - t')
    nlinarith
  exact h2.trans (mul_le_mul_of_nonneg_left hd hC)
theorem lipschitz_bound_iff (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h : BallCompatible ℓ c r ψ φ) {C : ℝ} (hC : 0 ≤ C) :
    (∀ u w : Torus4 ℓ, ‖φ u - φ w‖ ≤ C * euclidDistTorus u w) ↔
      ∀ t t', ‖ψ t - ψ t'‖ ≤ C * euclidDistR4 t t' := by
  constructor
  · intro H t t'
    by_cases ht : t ∈ closedBallR4 c r <;> by_cases ht' : t' ∈ closedBallR4 c r
    · rw [← h.2.1 t ht, ← h.2.1 t' ht', ← euclidDistTorus_torusProj_of_mem hℓ hr ht ht']
      exact H _ _
    · exact lipschitz_bound_ascends hℓ hr hr0 h hC H ht ht'
    · have := lipschitz_bound_ascends hℓ hr hr0 h hC H ht' ht
      rw [norm_sub_rev]
      have hd : euclidDistR4 t t' = euclidDistR4 t' t := euclidNormVec_sub_comm t t'
      rwa [hd]
    · rw [h.1 t ht, h.1 t' ht', sub_self, norm_zero]
      exact mul_nonneg hC (euclidNormVec_nonneg _)
  · intro H u w
    by_cases hu : φ u = 0 <;> by_cases hw : φ w = 0
    · rw [hu, hw, sub_self, norm_zero]
      exact mul_nonneg hC (torusEuclidNorm_nonneg _)
    · have := lipschitz_bound_descends h H hw hu
      rwa [norm_sub_rev]
    · have := lipschitz_bound_descends h H hu hw
      rwa [euclidDistTorus_comm] at this
    · obtain ⟨t, ht, rfl⟩ := exists_mem_torusProj_eq_of_ne_zero h hu
      obtain ⟨t', ht', rfl⟩ := exists_mem_torusProj_eq_of_ne_zero h hw
      rw [h.2.1 t ht, h.2.1 t' ht', euclidDistTorus_torusProj_of_mem hℓ hr ht ht']
      exact H t t'
theorem isLipschitzFor_iff_of_ballCompatible (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h : BallCompatible ℓ c r ψ φ) :
    IsLipschitzFor euclidDistTorus φ ↔ IsLipschitzFor euclidDistR4 ψ := by
  constructor
  · rintro ⟨C, hC, H⟩
    exact ⟨C, hC, (lipschitz_bound_iff hℓ hr hr0 h hC).1 H⟩
  · rintro ⟨C, hC, H⟩
    exact ⟨C, hC, (lipschitz_bound_iff hℓ hr hr0 h hC).2 H⟩
theorem lipConst_eq_of_ballCompatible (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h : BallCompatible ℓ c r ψ φ) : lipConstR4 ψ = lipConstTorus φ := by
  unfold lipConstTorus lipConstR4 bestLipschitzConstant
  congr 1
  ext C
  constructor
  · rintro ⟨hC, H⟩
    exact ⟨hC, (lipschitz_bound_iff hℓ hr hr0 h hC).2 H⟩
  · rintro ⟨hC, H⟩
    exact ⟨hC, (lipschitz_bound_iff hℓ hr hr0 h hC).1 H⟩
theorem tsupport_subset_closedBallR4 (h : BallCompatible ℓ c r ψ φ) :
    tsupport ψ ⊆ closedBallR4 c r :=
  closure_minimal (fun _ ht => mem_closedBallR4_of_ne_zero h ht) (isClosed_closedBallR4 c r)
theorem tsupport_eq_torusProj_image (hℓ : 0 < ℓ) (hr0 : 0 < r) (h : BallCompatible ℓ c r ψ φ) :
    tsupport φ = torusProj ℓ '' tsupport ψ := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  have hcl := tsupport_subset_closedBallR4 h
  have hcpt : IsCompact (tsupport ψ) :=
    (isCompact_closedBallR4 c hr0.le).of_isClosed_subset (isClosed_tsupport ψ) hcl
  have hclosedImage : IsClosed (torusProj ℓ '' tsupport ψ) :=
    (hcpt.image continuous_torusProj).isClosed
  have himage : Function.support φ = torusProj ℓ '' Function.support ψ := by
    ext u
    constructor
    · intro hu
      obtain ⟨t, ht, rfl⟩ := exists_mem_torusProj_eq_of_ne_zero h hu
      refine ⟨t, ?_, rfl⟩
      have hne : φ (torusProj ℓ t) ≠ 0 := hu
      rw [h.2.1 t ht] at hne
      exact hne
    · rintro ⟨t, ht, rfl⟩
      have hne : ψ t ≠ 0 := ht
      show φ (torusProj ℓ t) ≠ 0
      rwa [h.2.1 t (mem_closedBallR4_of_ne_zero h ht)]
  show closure (Function.support φ) = torusProj ℓ '' closure (Function.support ψ)
  rw [himage]
  apply Subset.antisymm
  · exact closure_minimal (image_mono subset_closure) hclosedImage
  · exact image_closure_subset_closure_image continuous_torusProj
theorem setDist_eq_of_ballCompatible (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    {ψ₁ ψ₂ : (Fin 4 → ℝ) → ℝ} {φ₁ φ₂ : Torus4 ℓ → ℝ} (h₁ : BallCompatible ℓ c r ψ₁ φ₁)
    (h₂ : BallCompatible ℓ c r ψ₂ φ₂) :
    setDistR4 (tsupport ψ₁) (tsupport ψ₂) = setEuclidDist (tsupport φ₁) (tsupport φ₂) := by
  rw [tsupport_eq_torusProj_image hℓ hr0 h₁, tsupport_eq_torusProj_image hℓ hr0 h₂]
  unfold setDistR4 setEuclidDist
  simp only [iInf_image]
  refine iInf_congr fun U => iInf_congr fun hU => iInf_congr fun V => iInf_congr fun hV => ?_
  have := euclidDistTorus_torusProj_of_mem hℓ hr (tsupport_subset_closedBallR4 h₁ hU)
    (tsupport_subset_closedBallR4 h₂ hV)
  have h' : torusEuclidNorm (torusProj ℓ U - torusProj ℓ V) = euclidNormVec (U - V) := this
  rw [h']
theorem continuous_of_isLipschitzFor_torus (hφ : IsLipschitzFor euclidDistTorus φ) :
    Continuous φ := by
  obtain ⟨C, -, H⟩ := hφ
  refine continuous_iff_continuousAt.2 fun x => ?_
  show Filter.Tendsto φ (nhds x) (nhds (φ x))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun y : Torus4 ℓ => C * torusEuclidNorm (y - x) :=
    continuous_const.mul (continuous_torusEuclidNorm.comp (continuous_id.sub continuous_const))
  have hl := hc.tendsto x
  simp only [sub_self, torusEuclidNorm_zero, mul_zero] at hl
  exact squeeze_zero (fun _ => norm_nonneg _) (fun y => H y x) hl
theorem continuous_of_isLipschitzFor_r4 (hψ : IsLipschitzFor euclidDistR4 ψ) : Continuous ψ := by
  obtain ⟨C, -, H⟩ := hψ
  refine continuous_iff_continuousAt.2 fun x => ?_
  show Filter.Tendsto ψ (nhds x) (nhds (ψ x))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun y : Fin 4 → ℝ => C * euclidNormVec (y - x) :=
    continuous_const.mul (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
  have hl := hc.tendsto x
  simp only [sub_self, euclidNormVec_zero, mul_zero] at hl
  exact squeeze_zero (fun _ => norm_nonneg _) (fun y => H y x) hl
theorem eq_comp_torusProj_on_cube (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (h : BallCompatible ℓ c r ψ φ)
    {t : Fin 4 → ℝ} (ht : t ∈ centredIcoCube ℓ c) : ψ t = φ (torusProj ℓ t) := by
  by_cases hb : t ∈ closedBallR4 c r
  · exact (h.2.1 t hb).symm
  · rw [h.1 t hb]
    by_contra hne
    obtain ⟨t', ht', he⟩ := exists_mem_torusProj_eq_of_ne_zero h (Ne.symm hne)
    have := (bijOn_torusProj_centredIcoCube hℓ c).injOn
      (closedBallR4_subset_centredIcoCube hℓ hr ht') ht he
    exact hb (this ▸ ht')
theorem measurableSet_centredIcoCube (C : Fin 4 → ℝ) : MeasurableSet (centredIcoCube ℓ C) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico
theorem integral_eq_integralTorusLebesgue (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4)
    (h : BallCompatible ℓ c r ψ φ) (hφ : Measurable φ) :
    (∫ t, ψ t) = integralTorusLebesgue ℓ φ := by
  have hτ : torusLebesgue ℓ = cubePushforward ℓ c := cubePushforward_indep hℓ _ _
  rw [integralTorusLebesgue, hτ, cubePushforward,
    integral_map (measurable_torusProj ℓ).aemeasurable hφ.aestronglyMeasurable,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := centredIcoCube ℓ c) (fun t ht =>
      h.1 t fun hb => ht (closedBallR4_subset_centredIcoCube hℓ hr hb))]
  exact setIntegral_congr_fun (measurableSet_centredIcoCube c) fun t ht =>
    eq_comp_torusProj_on_cube hℓ hr h ht
def kernelIntegrandTorus (φ₁ φ₂ : Torus4 ℓ → ℝ) (z : Torus4 ℓ × Torus4 ℓ) : ℝ :=
  φ₁ z.1 * φ₂ z.2 * torusEuclidNorm (z.1 - z.2) ^ (-8 : ℤ)
theorem measurable_inv_pow_eight : Measurable fun x : ℝ => x ^ (-8 : ℤ) := by
  have : (fun x : ℝ => x ^ (-8 : ℤ)) = fun x => (x ^ 8)⁻¹ := by
    funext x
    rw [zpow_neg]
    norm_cast
  rw [this]
  fun_prop
theorem measurable_kernelIntegrandTorus (hℓ : 0 < ℓ) {φ₁ φ₂ : Torus4 ℓ → ℝ}
    (m₁ : Measurable φ₁) (m₂ : Measurable φ₂) : Measurable (kernelIntegrandTorus φ₁ φ₂) := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  have hc : Continuous fun z : Torus4 ℓ × Torus4 ℓ => torusEuclidNorm (z.1 - z.2) :=
    continuous_torusEuclidNorm.comp (continuous_fst.sub continuous_snd)
  exact ((m₁.comp measurable_fst).mul (m₂.comp measurable_snd)).mul
    (measurable_inv_pow_eight.comp hc.measurable)
theorem inverseEighthKernel_eq_integral_prod_torus (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4)
    {ψ₁ ψ₂ : (Fin 4 → ℝ) → ℝ} {φ₁ φ₂ : Torus4 ℓ → ℝ} (h₁ : BallCompatible ℓ c r ψ₁ φ₁)
    (h₂ : BallCompatible ℓ c r ψ₂ φ₂) (m₁ : Measurable φ₁) (m₂ : Measurable φ₂) :
    inverseEighthKernel ψ₁ ψ₂ = ∫ z, kernelIntegrandTorus φ₁ φ₂ z ∂(torusLebesgue ℓ).prod
      (torusLebesgue ℓ) := by
  have hτ : torusLebesgue ℓ = cubePushforward ℓ c := cubePushforward_indep hℓ _ _
  have hQ := measurableSet_centredIcoCube (ℓ := ℓ) c
  have hmap : (torusLebesgue ℓ).prod (torusLebesgue ℓ) =
      (((volume : Measure (Fin 4 → ℝ)).restrict (centredIcoCube ℓ c)).prod
        ((volume : Measure (Fin 4 → ℝ)).restrict (centredIcoCube ℓ c))).map
        (Prod.map (torusProj ℓ) (torusProj ℓ)) := by
    rw [hτ, cubePushforward]
    exact Measure.map_prod_map _ _ (measurable_torusProj ℓ) (measurable_torusProj ℓ)
  have hmm : Measurable (Prod.map (torusProj ℓ) (torusProj ℓ)) :=
    (measurable_torusProj ℓ).prodMap (measurable_torusProj ℓ)
  rw [hmap, integral_map hmm.aemeasurable
    (measurable_kernelIntegrandTorus hℓ m₁ m₂).aestronglyMeasurable, Measure.prod_restrict,
    inverseEighthKernel, Measure.volume_eq_prod,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := centredIcoCube ℓ c ×ˢ centredIcoCube ℓ c)]
  · refine setIntegral_congr_fun (hQ.prod hQ) ?_
    rintro ⟨U, V⟩ ⟨hU, hV⟩
    have e₁ := eq_comp_torusProj_on_cube hℓ hr h₁ hU
    have e₂ := eq_comp_torusProj_on_cube hℓ hr h₂ hV
    simp only [kernelIntegrandTorus, Prod.map_apply, RCLike.ofReal_real_eq_id, id_eq]
    rw [← e₁, ← e₂]
    by_cases hz : ψ₁ U = 0 ∨ ψ₂ V = 0
    · rcases hz with hz | hz <;> simp [hz]
    · rw [not_or] at hz
      have hd := euclidDistTorus_torusProj_of_mem hℓ hr
        (mem_closedBallR4_of_ne_zero h₁ hz.1) (mem_closedBallR4_of_ne_zero h₂ hz.2)
      have hd' : torusEuclidNorm (torusProj ℓ U - torusProj ℓ V) = euclidNormVec (U - V) := hd
      rw [hd']
  · rintro ⟨U, V⟩ hz
    by_cases hU : U ∈ centredIcoCube ℓ c
    · have hV : V ∉ centredIcoCube ℓ c := fun hV => hz ⟨hU, hV⟩
      have : ψ₂ V = 0 := h₂.1 V fun hb => hV (closedBallR4_subset_centredIcoCube hℓ hr hb)
      simp [this]
    · have : ψ₁ U = 0 := h₁.1 U fun hb => hU (closedBallR4_subset_centredIcoCube hℓ hr hb)
      simp [this]
end BallCompatible
section Separation
variable {G : Type*} [AddCommGroup G] {n : G → ℝ}
theorem le_of_infDist_ge {A B : Set G} {d : ℝ} (hd : 0 < d)
    (h : ENNReal.ofReal d ≤ ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (n (a - b))) {a b : G} (ha : a ∈ A)
    (hb : b ∈ B) : d ≤ n (a - b) := by
  have h1 : ENNReal.ofReal d ≤ ENNReal.ofReal (n (a - b)) :=
    h.trans ((iInf₂_le a ha).trans (iInf₂_le b hb))
  rcases ENNReal.ofReal_le_ofReal_iff'.mp h1 with h2 | h2
  · exact h2
  · exact absurd hd (not_lt.mpr h2)
theorem centres_dist_le_eight (hneg : ∀ x, n (-x) = n x) (hadd : ∀ x y, n (x + y) ≤ n x + n y)
    {A B : Set G} {x₁ x₂ : G} {d : ℝ} (hd : 0 < d) (hA : ∀ a ∈ A, n (a - x₁) ≤ d)
    (hB : ∀ b ∈ B, n (b - x₂) ≤ d)
    (h6 : (⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (n (a - b))) ≤ ENNReal.ofReal (6 * d)) :
    n (x₁ - x₂) ≤ 8 * d := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hex : ∃ a ∈ A, ∃ b ∈ B, n (a - b) < 6 * d + ε := by
    by_contra hno
    have hall : ∀ a ∈ A, ∀ b ∈ B, 6 * d + ε ≤ n (a - b) := by
      intro a ha b hb
      by_contra hlt
      exact hno ⟨a, ha, b, hb, not_le.mp hlt⟩
    have h1 : ENNReal.ofReal (6 * d + ε) ≤ ENNReal.ofReal (6 * d) :=
      (le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal (hall a ha b hb)).trans h6
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    linarith
  obtain ⟨a, ha, b, hb, hab⟩ := hex
  have e : x₁ - x₂ = -(a - x₁) + ((a - b) + (b - x₂)) := by abel
  have h1 := hadd (-(a - x₁)) ((a - b) + (b - x₂))
  have h2 := hadd (a - b) (b - x₂)
  rw [hneg] at h1
  rw [e]
  linarith [hA a ha, hB b hb]
theorem points_dist_le_ten (hneg : ∀ x, n (-x) = n x) (hadd : ∀ x y, n (x + y) ≤ n x + n y)
    {x₁ x₂ u v : G} {d : ℝ} (hu : n (u - x₁) ≤ d) (hv : n (v - x₂) ≤ d)
    (hx : n (x₁ - x₂) ≤ 8 * d) : n (u - v) ≤ 10 * d := by
  have e : u - v = (u - x₁) + ((x₁ - x₂) + -(v - x₂)) := by abel
  have h1 := hadd (u - x₁) ((x₁ - x₂) + -(v - x₂))
  have h2 := hadd (x₁ - x₂) (-(v - x₂))
  rw [hneg] at h2
  rw [e]
  linarith
end Separation
theorem closedBallR4_left_subset_midpoint {X₁ X₂ : Fin 4 → ℝ} {d : ℝ}
    (hX : euclidNormVec (X₁ - X₂) ≤ 8 * d) :
    closedBallR4 X₁ d ⊆ closedBallR4 (midpointR4 X₁ X₂) (5 * d) := by
  intro y hy
  have hy' : euclidNormVec (y - X₁) ≤ d := hy
  have e : y - midpointR4 X₁ X₂ = (y - X₁) + (1 / 2 : ℝ) • (X₁ - X₂) := by
    funext μ
    simp [midpointR4]
    ring
  show euclidNormVec (y - midpointR4 X₁ X₂) ≤ 5 * d
  rw [e]
  refine (euclidNormVec_add_le _ _).trans ?_
  rw [euclidNormVec_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith
theorem closedBallR4_right_subset_midpoint {X₁ X₂ : Fin 4 → ℝ} {d : ℝ}
    (hX : euclidNormVec (X₁ - X₂) ≤ 8 * d) :
    closedBallR4 X₂ d ⊆ closedBallR4 (midpointR4 X₁ X₂) (5 * d) := by
  intro y hy
  have hy' : euclidNormVec (y - X₂) ≤ d := hy
  have e : y - midpointR4 X₁ X₂ = (y - X₂) + (1 / 2 : ℝ) • (X₂ - X₁) := by
    funext μ
    simp [midpointR4]
    ring
  show euclidNormVec (y - midpointR4 X₁ X₂) ≤ 5 * d
  rw [e]
  refine (euclidNormVec_add_le _ _).trans ?_
  rw [euclidNormVec_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    euclidNormVec_sub_comm X₂ X₁]
  linarith
theorem volume_closedBallR4 (x : Fin 4 → ℝ) {d : ℝ} (hd : 0 ≤ d) :
    volume (closedBallR4 x d) = ENNReal.ofReal (Real.pi ^ 2 / 2 * d ^ 4) := by
  have hset : closedBallR4 x d = (fun y => y + -x) ⁻¹'
      {y : Fin 4 → ℝ | (∑ i, |y i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ d} := by
    ext y
    simp only [closedBallR4, euclidNormVec, mem_ofPred_eq, mem_preimage, Real.sqrt_eq_rpow,
      Real.rpow_two, sq_abs, sub_eq_add_neg]
  rw [hset, measure_preimage_add_right, volume_sum_rpow_le (ι := Fin 4) (p := 2) (by norm_num) d]
  have hG1 : Real.Gamma (1 / 2 + 1) = Real.sqrt Real.pi / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hG2 : Real.Gamma ((4 : ℝ) / 2 + 1) = 2 := by
    have h : (4 : ℝ) / 2 + 1 = ((2 : ℕ) : ℝ) + 1 := by norm_num
    rw [h, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  rw [hG1, hG2]
  have hsq : (2 * (Real.sqrt Real.pi / 2)) ^ 4 / 2 = Real.pi ^ 2 / 2 := by
    have h : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    calc (2 * (Real.sqrt Real.pi / 2)) ^ 4 / 2 = (Real.sqrt Real.pi ^ 2) ^ 2 / 2 := by ring
      _ = Real.pi ^ 2 / 2 := by rw [h]
  rw [hsq, ← ENNReal.ofReal_pow hd, ← ENNReal.ofReal_mul (by positivity), mul_comm]
section KernelR4
variable {f f₁ f₂ : (Fin 4 → ℝ) → ℝ} {x x₁ x₂ : Fin 4 → ℝ} {d ϑ : ℝ}
theorem hasCompactSupport_of_tsupport_subset (hd : 0 < d) (hs : tsupport f ⊆ closedBallR4 x d) :
    HasCompactSupport f :=
  (isCompact_closedBallR4 x hd.le).of_isClosed_subset (isClosed_tsupport f) hs
theorem norm_le_uniformNorm (hb : IsBoundedFun f) (y : Fin 4 → ℝ) : ‖f y‖ ≤ uniformNorm f := by
  obtain ⟨C, hC⟩ := hb
  exact le_ciSup (f := fun y => ‖f y‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ y
theorem uniformNorm_nonneg {X : Type*} (g : X → ℝ) : 0 ≤ uniformNorm g :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem integral_le_uniformNorm_mul_volume (hd : 0 < d) (hc : Continuous f)
    (hs : tsupport f ⊆ closedBallR4 x d) :
    (∫ y, f y) ≤ uniformNorm f * (Real.pi ^ 2 / 2 * d ^ 4) := by
  have hcs := hasCompactSupport_of_tsupport_subset hd hs
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  have hb : IsBoundedFun f := ⟨C, hC⟩
  have hvol := volume_closedBallR4 x hd.le
  have hfin : volume (closedBallR4 x d) < ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_lt_top
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBallR4 x d)
    (fun y hy => image_eq_zero_of_notMem_tsupport fun hm => hy (hs hm))]
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := closedBallR4 x d) (f := f)
    (C := uniformNorm f) hfin (fun y _ => norm_le_uniformNorm hb y)
  have h2 : (volume : Measure (Fin 4 → ℝ)).real (closedBallR4 x d) = Real.pi ^ 2 / 2 * d ^ 4 := by
    rw [Measure.real, hvol, ENNReal.toReal_ofReal (by positivity)]
  rw [h2] at h1
  exact (le_abs_self _).trans h1
theorem kernel_bounds_r4 (hd : 0 < d) (hϑ : 0 < ϑ) (c₁ : Continuous f₁) (c₂ : Continuous f₂)
    (n₁ : ∀ y, 0 ≤ f₁ y) (n₂ : ∀ y, 0 ≤ f₂ y) (s₁ : tsupport f₁ ⊆ closedBallR4 x₁ d)
    (s₂ : tsupport f₂ ⊆ closedBallR4 x₂ d) (sep : SupportsSeparated euclidDistR4 d f₁ f₂)
    (i₁ : ϑ * uniformNorm f₁ * d ^ 4 ≤ ∫ y, f₁ y) (i₂ : ϑ * uniformNorm f₂ * d ^ 4 ≤ ∫ y, f₂ y) :
    IsKernelPairR4 f₁ f₂ ∧ KernelBoundChain d ϑ (uniformNorm f₁) (uniformNorm f₂) (∫ y, f₁ y)
      (∫ y, f₂ y) (inverseEighthKernel f₁ f₂) := by
  have k₁ := hasCompactSupport_of_tsupport_subset hd s₁
  have k₂ := hasCompactSupport_of_tsupport_subset hd s₂
  have hpos : 0 < setDistR4 (tsupport f₁) (tsupport f₂) := by
    refine lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd) ?_
    exact le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal (sep a ha b hb).1
  refine ⟨⟨k₁.exists_bound_of_continuous c₁, k₂.exists_bound_of_continuous c₂, c₁.measurable,
    c₂.measurable, k₁, k₂, hpos⟩, ?_⟩
  have I₁ : Integrable f₁ := c₁.integrable_of_hasCompactSupport k₁
  have I₂ : Integrable f₂ := c₂.integrable_of_hasCompactSupport k₂
  set A : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℝ := fun z => f₁ z.1 * f₂ z.2 with hA
  have IA : Integrable A (volume.prod volume) := I₁.mul_prod I₂
  have hAint : ∫ z, A z ∂(volume.prod volume) = (∫ y, f₁ y) * ∫ y, f₂ y := integral_prod_mul f₁ f₂
  set K : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℝ :=
    fun z => f₁ z.1 * f₂ z.2 * euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) with hK
  have hDpos : 0 < d ^ (-8 : ℤ) := zpow_pos hd _
  have hEpos : 0 < (10 * d) ^ (-8 : ℤ) := zpow_pos (by positivity) _
  have hbounds : ∀ z, (10 * d) ^ (-8 : ℤ) * A z ≤ K z ∧ K z ≤ d ^ (-8 : ℤ) * A z := by
    intro z
    by_cases hz : A z = 0
    · have hK0 : K z = 0 := by simp only [hK]; rw [show f₁ z.1 * f₂ z.2 = A z from rfl, hz, zero_mul]
      simp [hz, hK0]
    · have h1 : f₁ z.1 ≠ 0 := fun h => hz (by simp [hA, h])
      have h2 : f₂ z.2 ≠ 0 := fun h => hz (by simp [hA, h])
      obtain ⟨hlo, hhi⟩ := sep z.1 (subset_tsupport _ h1) z.2 (subset_tsupport _ h2)
      have hlo' : d ≤ euclidNormVec (z.1 - z.2) := hlo
      have hhi' : euclidNormVec (z.1 - z.2) ≤ 10 * d := hhi
      have hA0 : 0 ≤ A z := mul_nonneg (n₁ _) (n₂ _)
      have hvpos : 0 < euclidNormVec (z.1 - z.2) := lt_of_lt_of_le hd hlo'
      have hanti : ∀ {a b : ℝ}, 0 < a → a ≤ b → b ^ (-8 : ℤ) ≤ a ^ (-8 : ℤ) := by
        intro a b ha hab
        rw [zpow_neg, zpow_neg]
        exact inv_anti₀ (zpow_pos ha _) (zpow_le_zpow_left₀ (by norm_num) ha.le hab)
      have e : K z = euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) * A z := by
        simp only [hK, hA]
        ring
      rw [e]
      exact ⟨mul_le_mul_of_nonneg_right (hanti hvpos hhi') hA0,
        mul_le_mul_of_nonneg_right (hanti hd hlo') hA0⟩
  have hmK : Measurable K :=
    ((c₁.measurable.comp measurable_fst).mul (c₂.measurable.comp measurable_snd)).mul
      (measurable_inv_pow_eight.comp
        (continuous_euclidNormVec.comp (continuous_fst.sub continuous_snd)).measurable)
  have hK0 : ∀ z, 0 ≤ K z := fun z =>
    le_trans (mul_nonneg hEpos.le (mul_nonneg (n₁ _) (n₂ _))) (hbounds z).1
  have IK : Integrable K (volume.prod volume) := by
    refine Integrable.mono' (IA.const_mul (d ^ (-8 : ℤ))) hmK.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (hK0 z)]
    exact (hbounds z).2
  have hker : inverseEighthKernel f₁ f₂ = ∫ z, K z ∂(volume.prod volume) := by
    rw [inverseEighthKernel, Measure.volume_eq_prod]
    rfl
  have hlow : (10 * d) ^ (-8 : ℤ) * (∫ y, f₁ y) * (∫ y, f₂ y) ≤ inverseEighthKernel f₁ f₂ := by
    rw [hker, mul_assoc, ← hAint, ← integral_const_mul]
    exact integral_mono (IA.const_mul _) IK fun z => (hbounds z).1
  have hupp : inverseEighthKernel f₁ f₂ ≤ d ^ (-8 : ℤ) * (∫ y, f₁ y) * (∫ y, f₂ y) := by
    rw [hker, mul_assoc, ← hAint, ← integral_const_mul]
    exact integral_mono IK (IA.const_mul _) fun z => (hbounds z).2
  set s₁' := uniformNorm f₁ with hs₁
  set s₂' := uniformNorm f₂ with hs₂
  have hs₁0 : 0 ≤ s₁' := uniformNorm_nonneg f₁
  have hs₂0 : 0 ≤ s₂' := uniformNorm_nonneg f₂
  set a₁ := ∫ y, f₁ y
  set a₂ := ∫ y, f₂ y
  have hDd : d ^ (-8 : ℤ) * d ^ 8 = 1 := by
    rw [zpow_neg]
    norm_cast
    exact inv_mul_cancel₀ (pow_ne_zero _ hd.ne')
  have hE : (10 * d) ^ (-8 : ℤ) = kernelLowerConst * d ^ (-8 : ℤ) := by
    rw [mul_zpow]
    rfl
  have hb₁ : 0 ≤ ϑ * s₁' * d ^ 4 := by positivity
  have hb₂ : 0 ≤ ϑ * s₂' * d ^ 4 := by positivity
  have hprod : (ϑ * s₁' * d ^ 4) * (ϑ * s₂' * d ^ 4) ≤ a₁ * a₂ :=
    mul_le_mul i₁ i₂ hb₂ (hb₁.trans i₁)
  have hfirst : kernelLowerConst * ϑ ^ 2 * s₁' * s₂' ≤ (10 * d) ^ (-8 : ℤ) * a₁ * a₂ := by
    have hF : 0 ≤ kernelLowerConst := by unfold kernelLowerConst; positivity
    have h1 := mul_le_mul_of_nonneg_left hprod (mul_nonneg hF hDpos.le)
    have e : kernelLowerConst * d ^ (-8 : ℤ) * ((ϑ * s₁' * d ^ 4) * (ϑ * s₂' * d ^ 4)) =
        kernelLowerConst * ϑ ^ 2 * s₁' * s₂' * (d ^ (-8 : ℤ) * d ^ 8) := by ring
    rw [e, hDd, mul_one] at h1
    rw [hE, mul_assoc (kernelLowerConst * d ^ (-8 : ℤ))]
    exact h1
  have hu₁ := integral_le_uniformNorm_mul_volume hd c₁ s₁
  have hu₂ := integral_le_uniformNorm_mul_volume hd c₂ s₂
  have ha₂ : 0 ≤ a₂ := hb₂.trans i₂
  have hlast : d ^ (-8 : ℤ) * a₁ * a₂ ≤ kernelUpperConst * s₁' * s₂' := by
    have hm : a₁ * a₂ ≤ (s₁' * (Real.pi ^ 2 / 2 * d ^ 4)) * (s₂' * (Real.pi ^ 2 / 2 * d ^ 4)) :=
      mul_le_mul hu₁ hu₂ ha₂ (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hm hDpos.le
    have e : d ^ (-8 : ℤ) * ((s₁' * (Real.pi ^ 2 / 2 * d ^ 4)) * (s₂' * (Real.pi ^ 2 / 2 * d ^ 4))) =
        kernelUpperConst * s₁' * s₂' * (d ^ (-8 : ℤ) * d ^ 8) := by
      unfold kernelUpperConst
      ring
    rw [e, hDd, mul_one] at h1
    rw [mul_assoc]
    exact h1
  exact ⟨hfirst, hlow, hupp, hlast⟩
end KernelR4
section TwoPairs
variable {ℓ : ℝ} {c : Fin 4 → ℝ} {r d ϑ : ℝ} {ψ ψ₁ ψ₂ : (Fin 4 → ℝ) → ℝ}
  {φ φ₁ φ₂ : Torus4 ℓ → ℝ}
theorem measurable_of_ballCompatible (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h : BallCompatible ℓ c r ψ φ) (hL : IsLipschitzFor euclidDistR4 ψ) : Measurable φ := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  exact (continuous_of_isLipschitzFor_torus
    ((isLipschitzFor_iff_of_ballCompatible hℓ hr hr0 h).2 hL)).measurable
theorem tsupport_subset_closedBallTorus (hℓ : 0 < ℓ) (hr0 : 0 < r)
    (h : BallCompatible ℓ c r ψ φ) : tsupport φ ⊆ closedBallTorus (torusProj ℓ c) r := by
  rw [tsupport_eq_torusProj_image hℓ hr0 h, ← torusProj_image_closedBallR4]
  exact image_mono (tsupport_subset_closedBallR4 h)
theorem isKernelBallTorus_of_ballCompatible (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h₁ : BallCompatible ℓ c r ψ₁ φ₁) (h₂ : BallCompatible ℓ c r ψ₂ φ₂)
    (hpos : 0 < setDistR4 (tsupport ψ₁) (tsupport ψ₂)) : IsKernelBallTorus φ₁ φ₂ c r := by
  refine ⟨?_, hr0, hr, tsupport_subset_closedBallTorus hℓ hr0 h₁,
    tsupport_subset_closedBallTorus hℓ hr0 h₂⟩
  rwa [← setDist_eq_of_ballCompatible hℓ hr hr0 h₁ h₂]
theorem inverseEighthKernel_eq_torus (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h₁ : BallCompatible ℓ c r ψ₁ φ₁) (h₂ : BallCompatible ℓ c r ψ₂ φ₂) (m₁ : Measurable φ₁)
    (m₂ : Measurable φ₂) (hpos : 0 < setDistR4 (tsupport ψ₁) (tsupport ψ₂)) :
    inverseEighthKernel ψ₁ ψ₂ = inverseEighthKernelTorus φ₁ φ₂ := by
  have H : ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus φ₁ φ₂ q.1 q.2 :=
    ⟨(c, r), isKernelBallTorus_of_ballCompatible hℓ hr hr0 h₁ h₂ hpos⟩
  rw [inverseEighthKernelTorus, dif_pos H]
  obtain ⟨-, -, hq, s₁, s₂⟩ := H.choose_spec
  have b₁ : BallCompatible ℓ H.choose.1 H.choose.2 (liftToBall ℓ H.choose.1 H.choose.2 φ₁) φ₁ :=
    ballCompatible_liftToBall fun u hu => image_eq_zero_of_notMem_tsupport fun hm => hu (s₁ hm)
  have b₂ : BallCompatible ℓ H.choose.1 H.choose.2 (liftToBall ℓ H.choose.1 H.choose.2 φ₂) φ₂ :=
    ballCompatible_liftToBall fun u hu => image_eq_zero_of_notMem_tsupport fun hm => hu (s₂ hm)
  rw [inverseEighthKernel_eq_integral_prod_torus hℓ hr h₁ h₂ m₁ m₂,
    inverseEighthKernel_eq_integral_prod_torus hℓ hq b₁ b₂ m₁ m₂]
theorem preservesInvariants_of_ballCompatible (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h₁ : BallCompatible ℓ c r ψ₁ φ₁) (h₂ : BallCompatible ℓ c r ψ₂ φ₂)
    (L₁ : IsLipschitzFor euclidDistR4 ψ₁) (L₂ : IsLipschitzFor euclidDistR4 ψ₂)
    (hpos : 0 < setDistR4 (tsupport ψ₁) (tsupport ψ₂)) : PreservesInvariants φ₁ φ₂ ψ₁ ψ₂ := by
  have m₁ := measurable_of_ballCompatible hℓ hr hr0 h₁ L₁
  have m₂ := measurable_of_ballCompatible hℓ hr hr0 h₂ L₂
  exact ⟨uniformNorm_eq_of_ballCompatible h₁, uniformNorm_eq_of_ballCompatible h₂,
    integral_eq_integralTorusLebesgue hℓ hr h₁ m₁, integral_eq_integralTorusLebesgue hℓ hr h₂ m₂,
    lipConst_eq_of_ballCompatible hℓ hr hr0 h₁, lipConst_eq_of_ballCompatible hℓ hr hr0 h₂,
    setDist_eq_of_ballCompatible hℓ hr hr0 h₁ h₂,
    inverseEighthKernel_eq_torus hℓ hr hr0 h₁ h₂ m₁ m₂ hpos⟩
theorem tsupport_subset_closedBall_iff (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h : BallCompatible ℓ c r ψ φ) {X : Fin 4 → ℝ} (hsub : closedBallR4 X d ⊆ closedBallR4 c r) :
    tsupport φ ⊆ closedBallTorus (torusProj ℓ X) d ↔ tsupport ψ ⊆ closedBallR4 X d := by
  rw [tsupport_eq_torusProj_image hℓ hr0 h, ← torusProj_image_closedBallR4]
  constructor
  · intro hs t ht
    obtain ⟨t', ht', he⟩ := hs ⟨t, ht, rfl⟩
    have := injOn_torusProj_closedBallR4 hℓ hr (hsub ht') (tsupport_subset_closedBallR4 h ht) he
    exact this ▸ ht'
  · exact fun hs => image_mono hs
theorem admissible_iff_of_ballCompatible (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h : BallCompatible ℓ c r ψ φ) :
    (IsLipschitzFor euclidDistTorus φ ∧ (∀ u, 0 ≤ φ u) ∧ ∃ u, φ u ≠ 0) ↔
      (IsLipschitzFor euclidDistR4 ψ ∧ (∀ t, 0 ≤ ψ t) ∧ ∃ t, ψ t ≠ 0) := by
  rw [isLipschitzFor_iff_of_ballCompatible hℓ hr hr0 h]
  refine and_congr_right fun _ => and_congr ⟨fun hn t => ?_, fun hn u => ?_⟩ ⟨?_, ?_⟩
  · by_cases ht : t ∈ closedBallR4 c r
    · rw [← h.2.1 t ht]
      exact hn _
    · rw [h.1 t ht]
  · by_cases hu : φ u = 0
    · rw [hu]
    · obtain ⟨t, ht, rfl⟩ := exists_mem_torusProj_eq_of_ne_zero h hu
      rw [h.2.1 t ht]
      exact hn t
  · rintro ⟨u, hu⟩
    obtain ⟨t, ht, rfl⟩ := exists_mem_torusProj_eq_of_ne_zero h hu
    exact ⟨t, by rwa [h.2.1 t ht] at hu⟩
  · rintro ⟨t, ht⟩
    exact ⟨torusProj ℓ t, by rwa [h.2.1 t (mem_closedBallR4_of_ne_zero h ht)]⟩
theorem isCentrePair_iff_of_ballCompatible (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) (hr0 : 0 < r)
    (h₁ : BallCompatible ℓ c r ψ₁ φ₁) (h₂ : BallCompatible ℓ c r ψ₂ φ₂)
    (L₁ : IsLipschitzFor euclidDistR4 ψ₁) (L₂ : IsLipschitzFor euclidDistR4 ψ₂)
    {X₁ X₂ : Fin 4 → ℝ} (s₁ : closedBallR4 X₁ d ⊆ closedBallR4 c r)
    (s₂ : closedBallR4 X₂ d ⊆ closedBallR4 c r) :
    IsCentrePairTorus ℓ d ϑ (torusProj ℓ X₁) (torusProj ℓ X₂) (φ₁, φ₂) ↔
      IsCentrePairR4 d ϑ X₁ X₂ (ψ₁, ψ₂) := by
  have m₁ := measurable_of_ballCompatible hℓ hr hr0 h₁ L₁
  have m₂ := measurable_of_ballCompatible hℓ hr hr0 h₂ L₂
  have i₁ : torusVolumeIntegral ℓ φ₁ = ∫ t, ψ₁ t :=
    (torusVolumeIntegral_eq_integralTorusLebesgue hℓ φ₁ m₁.aestronglyMeasurable).trans
      (integral_eq_integralTorusLebesgue hℓ hr h₁ m₁).symm
  have i₂ : torusVolumeIntegral ℓ φ₂ = ∫ t, ψ₂ t :=
    (torusVolumeIntegral_eq_integralTorusLebesgue hℓ φ₂ m₂.aestronglyMeasurable).trans
      (integral_eq_integralTorusLebesgue hℓ hr h₂ m₂).symm
  have l₁ : bestLipschitzConstant euclidDistTorus φ₁ = bestLipschitzConstant euclidDistR4 ψ₁ :=
    (lipConst_eq_of_ballCompatible hℓ hr hr0 h₁).symm
  have l₂ : bestLipschitzConstant euclidDistTorus φ₂ = bestLipschitzConstant euclidDistR4 ψ₂ :=
    (lipConst_eq_of_ballCompatible hℓ hr hr0 h₂).symm
  simp only [IsCentrePairTorus, IsCentrePairR4, IsCentrePair]
  rw [tsupport_subset_closedBall_iff hℓ hr hr0 h₁ s₁, tsupport_subset_closedBall_iff hℓ hr hr0 h₂ s₂,
    i₁, i₂, l₁, l₂, ← uniformNorm_eq_of_ballCompatible h₁, ← uniformNorm_eq_of_ballCompatible h₂,
    ← setDist_eq_of_ballCompatible hℓ hr hr0 h₁ h₂]
end TwoPairs
section Requirements
variable {ℓ d ϑ : ℝ}
theorem closedBallTorus_mono {c X : Fin 4 → ℝ} {r : ℝ} (hs : closedBallR4 X d ⊆ closedBallR4 c r) :
    closedBallTorus (torusProj ℓ X) d ⊆ closedBallTorus (torusProj ℓ c) r := by
  rw [← torusProj_image_closedBallR4, ← torusProj_image_closedBallR4]
  exact image_mono hs
theorem pairBoundsR4 (hd : 0 < d) (hϑ : 0 < ϑ) {x₁ x₂ : Fin 4 → ℝ} {f₁ f₂ : (Fin 4 → ℝ) → ℝ}
    (hc : (f₁, f₂) ∈ separatedPairsR4 d ϑ) (hz : IsCentrePairR4 d ϑ x₁ x₂ (f₁, f₂)) :
    PairBoundsR4 d ϑ x₁ x₂ f₁ f₂ := by
  obtain ⟨⟨l₁, g₁, -⟩, ⟨l₂, g₂, -⟩, -⟩ :=
    (mem_separatedPairs_iff euclidDistR4 closedBallR4 setDistR4 (fun f => ∫ x, f x) d ϑ
      (f₁, f₂)).1 hc
  obtain ⟨⟨t₁, i₁, -⟩, ⟨t₂, i₂, -⟩, sep, sep6⟩ := hz
  have hx : euclidNormVec (x₁ - x₂) ≤ 8 * d :=
    centres_dist_le_eight (n := euclidNormVec) euclidNormVec_neg euclidNormVec_add_le hd
      (A := tsupport f₁) (B := tsupport f₂) (fun _ ha => t₁ ha) (fun _ hb => t₂ hb) sep6
  have u₁ := closedBallR4_left_subset_midpoint hx
  have u₂ := closedBallR4_right_subset_midpoint hx
  have lie : SupportsSeparated euclidDistR4 d f₁ f₂ := fun u hu v hv =>
    ⟨le_of_infDist_ge (n := euclidNormVec) hd sep hu hv,
      points_dist_le_ten (n := euclidNormVec) euclidNormVec_neg euclidNormVec_add_le (t₁ hu)
        (t₂ hv) hx⟩
  obtain ⟨k₁, k₂⟩ := kernel_bounds_r4 hd hϑ (continuous_of_isLipschitzFor_r4 l₁)
    (continuous_of_isLipschitzFor_r4 l₂) g₁ g₂ t₁ t₂ lie i₁ i₂
  exact ⟨hx, ⟨union_subset u₁ u₂, union_subset (t₁.trans u₁) (t₂.trans u₂)⟩, lie, k₁, k₂⟩
theorem liftProperties (hd : 0 < d) (h40 : 40 * d ≤ ℓ) {X₁ X₂ : Fin 4 → ℝ}
    {f₁ f₂ : Torus4 ℓ → ℝ} (hX : euclidNormVec (X₁ - X₂) ≤ 8 * d)
    (hc : (f₁, f₂) ∈ separatedPairsTorus ℓ d ϑ)
    (hz : IsCentrePairTorus ℓ d ϑ (torusProj ℓ X₁) (torusProj ℓ X₂) (f₁, f₂)) :
    LiftProperties ℓ d ϑ (torusProj ℓ X₁) (torusProj ℓ X₂) X₁ X₂ f₁ f₂ ∧
      IsKernelBallTorus f₁ f₂ (midpointR4 X₁ X₂) (5 * d) := by
  have hℓ : 0 < ℓ := by linarith
  have hr : 5 * d ≤ ℓ / 4 := by linarith
  have hr0 : 0 < 5 * d := by linarith
  obtain ⟨m₁, m₂, -⟩ :=
    (mem_separatedPairs_iff euclidDistTorus closedBallTorus setEuclidDist (torusVolumeIntegral ℓ)
      d ϑ (f₁, f₂)).1 hc
  have hz' := hz
  obtain ⟨⟨t₁, -, -⟩, ⟨t₂, -, -⟩, sep, -⟩ := hz'
  have u₁ := closedBallR4_left_subset_midpoint hX
  have u₂ := closedBallR4_right_subset_midpoint hX
  have v₁ : ∀ u, u ∉ closedBallTorus (torusProj ℓ (midpointR4 X₁ X₂)) (5 * d) → f₁ u = 0 :=
    fun u hu => image_eq_zero_of_notMem_tsupport fun hm => hu (closedBallTorus_mono u₁ (t₁ hm))
  have v₂ : ∀ u, u ∉ closedBallTorus (torusProj ℓ (midpointR4 X₁ X₂)) (5 * d) → f₂ u = 0 :=
    fun u hu => image_eq_zero_of_notMem_tsupport fun hm => hu (closedBallTorus_mono u₂ (t₂ hm))
  have B₁ := ballCompatible_liftToBall v₁
  have B₂ := ballCompatible_liftToBall v₂
  have n₁ := (admissible_iff_of_ballCompatible hℓ hr hr0 B₁).1 m₁
  have n₂ := (admissible_iff_of_ballCompatible hℓ hr hr0 B₂).1 m₂
  have hpos : 0 < setDistR4 (tsupport (liftToBall ℓ (midpointR4 X₁ X₂) (5 * d) f₁))
      (tsupport (liftToBall ℓ (midpointR4 X₁ X₂) (5 * d) f₂)) := by
    rw [setDist_eq_of_ballCompatible hℓ hr hr0 B₁ B₂]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd) sep
  have hcent := (isCentrePair_iff_of_ballCompatible hℓ hr hr0 B₁ B₂ n₁.1 n₂.1 u₁ u₂).1 hz
  have hlift : ∀ x, x ∉ torusProj ℓ '' closedBallR4 (midpointR4 X₁ X₂) (5 * d) →
      x ∉ closedBallTorus (torusProj ℓ (midpointR4 X₁ X₂)) (5 * d) := fun x hx => by
    rwa [← torusProj_image_closedBallR4]
  refine ⟨⟨by linarith, ⟨torusProj ℓ (midpointR4 X₁ X₂), ⟨torusProj_image_closedBallR4 _ _,
      fun U hU V hV => euclidDistTorus_torusProj_of_mem hℓ hr hU hV⟩,
      union_subset (closedBallTorus_mono u₁) (closedBallTorus_mono u₂),
      union_subset (tsupport_subset_closedBallTorus hℓ hr0 B₁)
        (tsupport_subset_closedBallTorus hℓ hr0 B₂)⟩,
      ⟨hr0, hr, fun x hx => v₁ x (hlift x hx)⟩, ⟨hr0, hr, fun x hx => v₂ x (hlift x hx)⟩,
      (mem_separatedPairs_iff euclidDistR4 closedBallR4 setDistR4 (fun f => ∫ x, f x) d ϑ _).2
        ⟨n₁, n₂, X₁, X₂, hcent⟩, hcent,
      preservesInvariants_of_ballCompatible hℓ hr hr0 B₁ B₂ n₁.1 n₂.1 hpos⟩,
    isKernelBallTorus_of_ballCompatible hℓ hr hr0 B₁ B₂ hpos⟩
theorem pairBoundsTorus (hd : 0 < d) (hϑ : 0 < ϑ) (h40 : 40 * d ≤ ℓ) {x₁ x₂ : Torus4 ℓ}
    {f₁ f₂ : Torus4 ℓ → ℝ} (hc : (f₁, f₂) ∈ separatedPairsTorus ℓ d ϑ)
    (hz : IsCentrePairTorus ℓ d ϑ x₁ x₂ (f₁, f₂)) :
    PairBoundsTorus d ϑ x₁ x₂ f₁ f₂ ∧ ∀ X₁ X₂ : Fin 4 → ℝ, torusProj ℓ X₁ = x₁ →
      torusProj ℓ X₂ = x₂ → euclidDistR4 X₁ X₂ = euclidDistTorus x₁ x₂ →
        LiftProperties ℓ d ϑ x₁ x₂ X₁ X₂ f₁ f₂ := by
  have hz' := hz
  obtain ⟨⟨t₁, -, -⟩, ⟨t₂, -, -⟩, sep, sep6⟩ := hz'
  have hx : torusEuclidNorm (x₁ - x₂) ≤ 8 * d :=
    centres_dist_le_eight (n := torusEuclidNorm) torusEuclidNorm_neg torusEuclidNorm_add_le hd
      (A := tsupport f₁) (B := tsupport f₂) (fun _ ha => t₁ ha) (fun _ hb => t₂ hb) sep6
  refine ⟨?_, ?_⟩
  · obtain ⟨X₁, rfl⟩ := torusProj_surjective ℓ x₁
    obtain ⟨τ, hτ, hn, -⟩ := exists_minimal_lift (x₂ - torusProj ℓ X₁)
    have hcov : torusProj ℓ (X₁ + τ) = x₂ := by
      rw [torusProj_map_add, hτ]
      abel
    subst hcov
    have hX : euclidNormVec (X₁ - (X₁ + τ)) ≤ 8 * d := by
      rw [sub_add_cancel_left, euclidNormVec_neg, hn, ← neg_sub, torusEuclidNorm_neg]
      exact hx
    obtain ⟨⟨-, ⟨y, -, hold⟩, -, -, cls, cent, ks₁, ks₂, ki₁, ki₂, -, -, -, kk⟩, hball⟩ :=
      liftProperties hd h40 hX hc hz
    obtain ⟨-, -, -, -, chain⟩ := pairBoundsR4 hd hϑ cls cent
    rw [ks₁, ks₂, ki₁, ki₂, kk] at chain
    exact ⟨hx, ⟨y, hold⟩, fun u hu v hv => ⟨le_of_infDist_ge (n := torusEuclidNorm) hd sep hu hv,
      points_dist_le_ten (n := torusEuclidNorm) torusEuclidNorm_neg torusEuclidNorm_add_le (t₁ hu)
        (t₂ hv) hx⟩, ⟨(_, _), hball⟩, chain⟩
  · rintro X₁ X₂ rfl rfl e
    have hX : euclidNormVec (X₁ - X₂) ≤ 8 * d := by
      have e' : euclidNormVec (X₁ - X₂) = torusEuclidNorm (torusProj ℓ X₁ - torusProj ℓ X₂) := e
      rw [e']
      exact hx
    exact (liftProperties hd h40 hX hc hz).1
theorem periodizationProperties (hd : 0 < d) (hϑ : 0 < ϑ) (h40 : 40 * d ≤ ℓ)
    {x₁ x₂ : Fin 4 → ℝ} {f₁ f₂ : (Fin 4 → ℝ) → ℝ} (hc : (f₁, f₂) ∈ separatedPairsR4 d ϑ)
    (hz : IsCentrePairR4 d ϑ x₁ x₂ (f₁, f₂)) : PeriodizationProperties ℓ d ϑ x₁ x₂ f₁ f₂ := by
  have hℓ : 0 < ℓ := by linarith
  have hr : 5 * d ≤ ℓ / 4 := by linarith
  have hr0 : 0 < 5 * d := by linarith
  obtain ⟨m₁, m₂, -⟩ :=
    (mem_separatedPairs_iff euclidDistR4 closedBallR4 setDistR4 (fun f => ∫ x, f x) d ϑ
      (f₁, f₂)).1 hc
  have hz' := hz
  obtain ⟨⟨t₁, -, -⟩, ⟨t₂, -, -⟩, sep, -⟩ := hz'
  obtain ⟨hx, -⟩ := pairBoundsR4 hd hϑ hc hz
  have hX : euclidNormVec (x₁ - x₂) ≤ 8 * d := hx
  have u₁ := closedBallR4_left_subset_midpoint hX
  have u₂ := closedBallR4_right_subset_midpoint hX
  have v₁ : ∀ t, t ∉ closedBallR4 (midpointR4 x₁ x₂) (5 * d) → f₁ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hm => ht (u₁ (t₁ hm))
  have v₂ : ∀ t, t ∉ closedBallR4 (midpointR4 x₁ x₂) (5 * d) → f₂ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hm => ht (u₂ (t₂ hm))
  have B₁ : BallCompatible ℓ _ _ f₁ (periodize ℓ f₁) := ballCompatible_periodize hℓ hr v₁
  have B₂ : BallCompatible ℓ _ _ f₂ (periodize ℓ f₂) := ballCompatible_periodize hℓ hr v₂
  have n₁ := (admissible_iff_of_ballCompatible hℓ hr hr0 B₁).2 m₁
  have n₂ := (admissible_iff_of_ballCompatible hℓ hr hr0 B₂).2 m₂
  have hpos : 0 < setDistR4 (tsupport f₁) (tsupport f₂) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd) sep
  have hcent := (isCentrePair_iff_of_ballCompatible hℓ hr hr0 B₁ B₂ m₁.1 m₂.1 (ϑ := ϑ) u₁ u₂).2 hz
  have hdiam : HasDiameterLE (closedBallR4 (midpointR4 x₁ x₂) (5 * d)) (ℓ / 2) :=
    fun x hx y hy => by
      have := euclidNormVec_sub_le_two_mul_of_mem hx hy
      linarith
  have hlift : ∀ x, x ∉ torusProj ℓ '' closedBallR4 (midpointR4 x₁ x₂) (5 * d) →
      x ∉ closedBallTorus (torusProj ℓ (midpointR4 x₁ x₂)) (5 * d) := fun x hx => by
    rwa [← torusProj_image_closedBallR4]
  exact ⟨⟨hdiam, fun t ht => mem_closedBallR4_of_ne_zero B₁ ht⟩,
    ⟨hdiam, fun t ht => mem_closedBallR4_of_ne_zero B₂ ht⟩,
    (mem_separatedPairs_iff euclidDistTorus closedBallTorus setEuclidDist (torusVolumeIntegral ℓ)
      d ϑ _).2 ⟨n₁, n₂, _, _, hcent⟩, hcent,
    ⟨hr0, hr, fun x hx => B₁.2.2 x (hlift x hx)⟩, ⟨hr0, hr, fun x hx => B₂.2.2 x (hlift x hx)⟩,
    liftToBall_eq_of_ballCompatible B₁, liftToBall_eq_of_ballCompatible B₂,
    preservesInvariants_of_ballCompatible hℓ hr hr0 B₁ B₂ m₁.1 m₂.1 hpos⟩
end Requirements
theorem geometryAndKernelBounds : GeometryAndKernelBounds := by
  refine ⟨fun d ϑ hs x₁ x₂ f₁ f₂ hc hz => ⟨pairBoundsR4 hs.1 hs.2.1 hc hz,
    fun L ℓ' hside => periodizationProperties hs.1 hs.2.1 hside.2 hc hz⟩,
    fun L ℓ d ϑ hs hside x₁ x₂ f₁ f₂ hc hz => pairBoundsTorus hs.1 hs.2.1 hside.2 hc hz⟩
end TestPairs
end YangMills.Construction
