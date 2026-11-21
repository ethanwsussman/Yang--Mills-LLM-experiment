import YangMills.Construction.ReflectionPositivity.OneTorusAllCutoffsPointsAndTheClassC1
import YangMills.Construction.Torus.BallOfTheTorusAndTheBallOverIt
import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorus
import YangMills.Construction.Torus.CoveringMapIntegralAndVolumeOnTheTorus
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions YangMills.Construction.PlaquetteSupports
noncomputable section
namespace YangMills.Construction.TorusMeasure.BallProjection
theorem normVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem normVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem normVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem normVec_sub_comm (u v : Fin 4 → ℝ) : euclidNormVec (u - v) = euclidNormVec (v - u) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem normVec_smul (a : ℝ) (v : Fin 4 → ℝ) :
    euclidNormVec (a • v) = |a| * euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem abs_apply_le_normVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem eq_zero_of_normVec_nonpos {v : Fin 4 → ℝ} (hv : euclidNormVec v ≤ 0) : v = 0 := by
  funext μ
  have := (abs_apply_le_normVec v μ).trans hv
  simpa using abs_nonpos_iff.mp this
theorem continuous_normVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem le_normVec_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ euclidNormVec (latticeTranslate ℓ k) := by apply _root_.YangMills.Construction.TestPairs.le_euclidNormVec_latticeTranslate <;> assumption
theorem latticeTranslate_inj_of_pos {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Function.Injective (latticeTranslate ℓ) := by
  intro k k' hkk
  funext μ
  have := congrFun hkk μ
  simp only [latticeTranslate] at this
  exact_mod_cast mul_left_cancel₀ hℓ.ne' this
theorem closedBallR4_isClosed (c : Fin 4 → ℝ) (R : ℝ) : IsClosed (closedBallR4 c R) := by apply _root_.YangMills.Construction.TestPairs.isClosed_closedBallR4 <;> assumption
theorem closedBallR4_isCompact (c : Fin 4 → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (closedBallR4 c R) := by apply _root_.YangMills.Construction.TestPairs.isCompact_closedBallR4 <;> assumption
theorem normVec_sub_le_of_mem_closedBallR4 {c x y : Fin 4 → ℝ} {R : ℝ}
    (hx : x ∈ closedBallR4 c R) (hy : y ∈ closedBallR4 c R) : euclidNormVec (x - y) ≤ 2 * R := by apply _root_.YangMills.Construction.TestPairs.euclidNormVec_sub_le_two_mul_of_mem <;> assumption
variable {s : Conventions.StandingParameters}
theorem proj_map_add (x y : Fin 4 → ℝ) :
    proj s (x + y) = proj s x + proj s y := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusCutoffs.proj_add <;> assumption
theorem proj_map_sub (x y : Fin 4 → ℝ) :
    proj s (x - y) = proj s x - proj s y := by
  funext μ
  simp [proj, torusProj]
theorem proj_translate_invariant (x : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    proj s (x + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) = proj s x :=
  torusProj_add_latticeTranslate _ _ _
theorem proj_continuous : Continuous (proj s) :=
  continuous_pi fun μ => (AddCircle.continuous_mk' _).comp (continuous_apply μ)
theorem exists_lift_normVec_eq_pointNorm (hF : TorusCovering.ProjectionProperties s)
    (u : s.Torus) : ∃ τ, proj s τ = u ∧ euclidNormVec τ = pointNorm u := by
  obtain ⟨-, -, -, hlift, -, -, -, -, -, hleast⟩ := hF
  obtain ⟨⟨τ, hτ, hn⟩, -⟩ := hleast u
  exact ⟨τ, (hlift u τ).1 hτ, hn⟩
theorem shortVectorNormPreserved_holds (hF : TorusCovering.ProjectionProperties s)
    (hle : ∀ x, pointNorm (proj s x) ≤ euclidNormVec x)
    (hℓ : 0 < PeriodicLattice.torusSide s.L s.m) : ShortVectorNormPreserved s := by
  intro x hx
  refine le_antisymm (hle x) ?_
  obtain ⟨τ, hτ, hn⟩ := exists_lift_normVec_eq_pointNorm hF (proj s x)
  rw [← hn]
  obtain ⟨k, rfl⟩ := exists_latticeTranslate_of_torusProj_eq (ℓ := PeriodicLattice.torusSide s.L s.m) hτ
  by_cases hk : k = 0
  · subst hk
    have : latticeTranslate (PeriodicLattice.torusSide s.L s.m) (0 : Fin 4 → ℤ) = 0 := by
      funext μ
      simp [latticeTranslate]
    rw [this, add_zero]
  · have h1 := le_normVec_latticeTranslate hℓ hk
    have h2 := normVec_add_le (x + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) (-x)
    rw [normVec_neg, add_comm x, add_neg_cancel_right, add_comm _ x] at h2
    linarith
section Ball
variable {c : Fin 4 → ℝ} {R : ℝ}
theorem proj_mem_torusBallOver (hle : ∀ x, pointNorm (proj s x) ≤ euclidNormVec x)
    {x : Fin 4 → ℝ} (hx : x ∈ closedBallR4 c R) : proj s x ∈ torusBallOver s c R := by
  show pointNorm (proj s x - proj s c) ≤ R
  rw [← proj_map_sub]
  exact (hle _).trans hx
theorem exists_preimage_in_ball (hF : TorusCovering.ProjectionProperties s)
    {u : s.Torus} (hu : u ∈ torusBallOver s c R) : ∃ x ∈ closedBallR4 c R, proj s x = u := by
  obtain ⟨τ, hτ, hn⟩ := exists_lift_normVec_eq_pointNorm hF (u - proj s c)
  refine ⟨c + τ, ?_, ?_⟩
  · show euclidNormVec (c + τ - c) ≤ R
    rw [add_sub_cancel_left, hn]
    exact hu
  · rw [proj_map_add, hτ]
    abel
theorem pointDist_proj_eq_of_mem (hA : ShortVectorNormPreserved s)
    (hR : R ≤ PeriodicLattice.torusSide s.L s.m / 4) {x y : Fin 4 → ℝ}
    (hx : x ∈ closedBallR4 c R) (hy : y ∈ closedBallR4 c R) :
    pointDist (proj s x) (proj s y) = euclidDistR4 x y := by
  show pointNorm (proj s x - proj s y) = euclidNormVec (x - y)
  rw [← proj_map_sub]
  apply hA
  have := normVec_sub_le_of_mem_closedBallR4 hx hy
  linarith
theorem proj_injOn_ball (hA : ShortVectorNormPreserved s)
    (hR : R ≤ PeriodicLattice.torusSide s.L s.m / 4)
    (hℓ : 0 < PeriodicLattice.torusSide s.L s.m) : InjOn (proj s) (closedBallR4 c R) := by
  intro x hx y hy hxy
  have h1 := pointDist_proj_eq_of_mem hA hR hx hy
  have h0 : pointNorm (proj s (0 : Fin 4 → ℝ)) = euclidNormVec 0 :=
    hA 0 (by
      have : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [euclidNormVec]
      rw [this]
      linarith)
  have h2 : proj s (0 : Fin 4 → ℝ) = proj s x - proj s y := by
    rw [hxy, sub_self]
    funext μ
    simp [proj, torusProj]
  have h3 : euclidNormVec (x - y) = euclidNormVec (0 : Fin 4 → ℝ) := by
    rw [← h0, h2]
    exact h1.symm
  have h4 : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [euclidNormVec]
  exact sub_eq_zero.mp (eq_zero_of_normVec_nonpos (by rw [h3, h4]))
theorem ballMapsIsometricallyOnto_holds (hF : TorusCovering.ProjectionProperties s)
    (hle : ∀ x, pointNorm (proj s x) ≤ euclidNormVec x)
    (hA : ShortVectorNormPreserved s) (hR : R ≤ PeriodicLattice.torusSide s.L s.m / 4)
    (hℓ : 0 < PeriodicLattice.torusSide s.L s.m) : BallMapsIsometricallyOnto s c R := by
  refine ⟨⟨fun x hx => proj_mem_torusBallOver hle hx, proj_injOn_ball hA hR hℓ, ?_⟩,
    fun x hx y hy => pointDist_proj_eq_of_mem hA hR hx hy⟩
  intro u hu
  obtain ⟨x, hx, rfl⟩ := exists_preimage_in_ball hF hu
  exact ⟨x, hx, rfl⟩
theorem pushdownBijective_holds (hB : BallMapsIsometricallyOnto s c R) :
    PushdownBijective s c R := by
  classical
  have hbij := hB.1
  constructor
  · intro f hf
    let φ : s.Torus → ℝ := fun u =>
      if hu : u ∈ torusBallOver s c R then f (hbij.surjOn hu).choose else 0
    have hφ : IsPushdown s c R f φ := by
      refine ⟨hf, ?_, ?_⟩
      · intro x hx
        have hu := hbij.mapsTo hx
        have hspec := (hbij.surjOn hu).choose_spec
        have : (hbij.surjOn hu).choose = x := hbij.injOn hspec.1 hx hspec.2
        simp only [φ, dif_pos hu, this]
      · intro u hu
        simp only [φ, dif_neg hu]
    refine ⟨φ, hφ, ?_⟩
    intro ψ hψ
    funext u
    by_cases hu : u ∈ torusBallOver s c R
    · obtain ⟨x, hx, rfl⟩ := hbij.surjOn hu
      rw [hψ.2.1 x hx, hφ.2.1 x hx]
    · rw [hψ.2.2 u hu, hφ.2.2 u hu]
  · intro φ hφ
    have hex : IsPushdown s c R ((closedBallR4 c R).indicator (φ ∘ proj s)) φ := by
      refine ⟨fun x hx => indicator_of_notMem hx _, fun x hx => ?_, hφ⟩
      rw [indicator_of_mem hx]
      rfl
    refine ⟨⟨_, hex, ?_⟩, hex⟩
    intro f hf
    funext x
    by_cases hx : x ∈ closedBallR4 c R
    · rw [indicator_of_mem hx, ← hf.2.1 x hx]
      rfl
    · rw [indicator_of_notMem hx, hf.1 x hx]
variable {g : (Fin 4 → ℝ) → ℝ} {h : s.Torus → ℝ}
theorem mem_ball_of_apply_ne_zero (hgh : IsPushdown s c R g h) {x : Fin 4 → ℝ}
    (hx : g x ≠ 0) : x ∈ closedBallR4 c R := by
  by_contra hn
  exact hx (hgh.1 x hn)
theorem mem_torusBallOver_of_apply_ne_zero (hgh : IsPushdown s c R g h) {u : s.Torus}
    (hu : h u ≠ 0) : u ∈ torusBallOver s c R := by
  by_contra hn
  exact hu (hgh.2.2 u hn)
theorem isPeriodizationOf_holds (hB : BallMapsIsometricallyOnto s c R)
    (hR : R ≤ PeriodicLattice.torusSide s.L s.m / 4) (hℓ : 0 < PeriodicLattice.torusSide s.L s.m)
    (hgh : IsPushdown s c R g h) : IsPeriodizationOf s c R g h := by
  have hbij := hB.1
  have hone : ∀ (x : Fin 4 → ℝ) (k k' : Fin 4 → ℤ),
      x + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k ∈ closedBallR4 c R →
      x + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k' ∈ closedBallR4 c R → k = k' := by
    intro x k k' hk hk'
    have h1 := hbij.injOn hk hk'
      (by rw [proj_translate_invariant, proj_translate_invariant])
    exact latticeTranslate_inj_of_pos hℓ (add_left_cancel h1)
  have hformula : ∀ x, h (proj s x) =
      ∑' k : Fin 4 → ℤ, g (x + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) := by
    intro x
    by_cases hk : ∃ k₀, x + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k₀ ∈ closedBallR4 c R
    · obtain ⟨k₀, hk₀⟩ := hk
      rw [tsum_eq_single k₀, ← hgh.2.1 _ hk₀, proj_translate_invariant]
      intro k hne
      by_contra hz
      exact hne (hone x k k₀ (mem_ball_of_apply_ne_zero hgh hz) hk₀)
    · have hall : ∀ k : Fin 4 → ℤ, g (x + latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) = 0 :=
        fun k => hgh.1 _ fun hm => hk ⟨k, hm⟩
      simp only [hall, tsum_zero]
      by_contra hz
      obtain ⟨x₁, hx₁, he⟩ := hbij.surjOn (mem_torusBallOver_of_apply_ne_zero hgh hz)
      obtain ⟨k, rfl⟩ := exists_latticeTranslate_of_torusProj_eq (ℓ := PeriodicLattice.torusSide s.L s.m) he
      exact hk ⟨k, hx₁⟩
  refine ⟨hformula, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro x k k' hk hk'
    exact hone x k k' (mem_ball_of_apply_ne_zero hgh hk) (mem_ball_of_apply_ne_zero hgh hk')
  · intro x hx y hy
    have := normVec_sub_le_of_mem_closedBallR4 hx hy
    linarith
  · intro x hx
    exact mem_ball_of_apply_ne_zero hgh hx
  · funext u
    obtain ⟨x, rfl⟩ := torusProj_surjective (PeriodicLattice.torusSide s.L s.m) u
    have h1 := hformula x
    have h2 := periodize_torusProj (PeriodicLattice.torusSide s.L s.m) g x
    exact h1.trans h2.symm
theorem sameValues_holds (hB : BallMapsIsometricallyOnto s c R)
    (hgh : IsPushdown s c R g h) : SameValues s c R g h := by
  have hbij := hB.1
  refine ⟨?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hbij.surjOn hu
      exact ⟨x, hx, (hgh.2.1 x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, hbij.mapsTo hx, hgh.2.1 x hx⟩
  · unfold torusESup
    apply le_antisymm
    · refine iSup_le fun u => ?_
      by_cases hu : u ∈ torusBallOver s c R
      · obtain ⟨x, hx, rfl⟩ := hbij.surjOn hu
        simp only [hgh.2.1 x hx]
        exact le_iSup (fun x => ((|g x| : ℝ) : EReal)) x
      · simp only [hgh.2.2 u hu, abs_zero]
        refine le_trans ?_ (le_iSup (fun x => ((|g x| : ℝ) : EReal)) 0)
        exact_mod_cast abs_nonneg (g 0)
    · refine iSup_le fun x => ?_
      by_cases hx : x ∈ closedBallR4 c R
      · rw [← hgh.2.1 x hx]
        exact le_iSup (fun u => ((|h u| : ℝ) : EReal)) (proj s x)
      · simp only [hgh.1 x hx, abs_zero]
        refine le_trans ?_ (le_iSup (fun u => ((|h u| : ℝ) : EReal)) (proj s 0))
        exact_mod_cast abs_nonneg (h (proj s 0))
  · constructor
    · intro hn x
      by_cases hx : x ∈ closedBallR4 c R
      · rw [← hgh.2.1 x hx]
        exact hn _
      · rw [hgh.1 x hx]
    · intro hn u
      by_cases hu : u ∈ torusBallOver s c R
      · obtain ⟨x, hx, rfl⟩ := hbij.surjOn hu
        rw [hgh.2.1 x hx]
        exact hn x
      · rw [hgh.2.2 u hu]
theorem lipschitz_descend (hF : TorusCovering.ProjectionProperties s)
    (hB : BallMapsIsometricallyOnto s c R) (hgh : IsPushdown s c R g h) {C : ℝ}
    (H : ∀ x y, ‖g x - g y‖ ≤ C * euclidDistR4 x y) {u w : s.Torus}
    (hu : h u ≠ 0) (hw : h w = 0) : ‖h u - h w‖ ≤ C * pointDist w u := by
  obtain ⟨x, hx, rfl⟩ := hB.1.surjOn (mem_torusBallOver_of_apply_ne_zero hgh hu)
  obtain ⟨τ, hτ, hn⟩ := exists_lift_normVec_eq_pointNorm hF (w - proj s x)
  have hcov : proj s (x + τ) = w := by
    rw [proj_map_add, hτ]
    abel
  have hz : g (x + τ) = 0 := by
    by_cases hm : x + τ ∈ closedBallR4 c R
    · rw [← hgh.2.1 _ hm, hcov, hw]
    · exact hgh.1 _ hm
  have h1 := H x (x + τ)
  rw [hz, ← hgh.2.1 x hx] at h1
  rw [hw]
  have hd : euclidDistR4 x (x + τ) = pointDist w (proj s x) := by
    show euclidNormVec (x - (x + τ)) = pointNorm (w - proj s x)
    rw [← hn, sub_add_cancel_left, normVec_neg]
  rwa [hd] at h1
theorem lipschitz_ascend (hA : ShortVectorNormPreserved s)
    (hle : ∀ x, pointNorm (proj s x) ≤ euclidNormVec x)
    (hR : R ≤ PeriodicLattice.torusSide s.L s.m / 4) (hℓ : 0 < PeriodicLattice.torusSide s.L s.m)
    (hgh : IsPushdown s c R g h) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ u w : s.Torus, ‖h u - h w‖ ≤ C * pointDist u w) {x y : Fin 4 → ℝ}
    (hx : x ∈ closedBallR4 c R) (hy : y ∉ closedBallR4 c R) :
    ‖g x - g y‖ ≤ C * euclidDistR4 x y := by
  set ρ : ℝ → ℝ := fun θ => euclidNormVec (x + θ • (y - x) - c) with hρ
  have hcont : Continuous ρ := continuous_normVec.comp (by fun_prop)
  have h0 : ρ 0 ≤ R := by
    have hx0 : euclidNormVec (x - c) ≤ R := hx
    simpa [hρ] using hx0
  have h1 : R < ρ 1 := by
    have : ¬ euclidNormVec (y - c) ≤ R := hy
    simpa [hρ] using not_le.mp this
  have hR' : R < min (ρ 1) (PeriodicLattice.torusSide s.L s.m / 2) := by
    refine lt_min h1 ?_
    linarith
  have hmem : min (ρ 1) (PeriodicLattice.torusSide s.L s.m / 2) ∈ Icc (ρ 0) (ρ 1) :=
    ⟨h0.trans hR'.le, min_le_left _ _⟩
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hθ⟩ :=
    intermediate_value_Icc zero_le_one hcont.continuousOn hmem
  have hfar : euclidNormVec (x + θ • (y - x) - c) ≤ PeriodicLattice.torusSide s.L s.m / 2 := by
    have : ρ θ ≤ PeriodicLattice.torusSide s.L s.m / 2 := by
      rw [hθ]
      exact min_le_right _ _
    exact this
  have hoff : proj s (x + θ • (y - x)) ∉ torusBallOver s c R := by
    intro hm
    have hm' : pointNorm (proj s (x + θ • (y - x)) - proj s c) ≤ R := hm
    rw [← proj_map_sub, hA _ hfar] at hm'
    have : ρ θ ≤ R := hm'
    rw [hθ] at this
    exact absurd this (not_le.mpr hR')
  have hz := hgh.2.2 _ hoff
  have h2 := H (proj s x) (proj s (x + θ • (y - x)))
  rw [hz, hgh.2.1 x hx] at h2
  rw [hgh.1 y hy]
  have hd : pointDist (proj s x) (proj s (x + θ • (y - x))) ≤ euclidDistR4 x y := by
    show pointNorm (proj s x - proj s (x + θ • (y - x))) ≤ euclidNormVec (x - y)
    rw [← proj_map_sub]
    refine (hle _).trans ?_
    have he : x - (x + θ • (y - x)) = θ • (x - y) := by
      rw [sub_add_cancel_left, ← smul_neg, neg_sub]
    rw [he, normVec_smul, abs_of_nonneg hθ0]
    have := normVec_nonneg (x - y)
    nlinarith
  exact h2.trans (mul_le_mul_of_nonneg_left hd hC)
theorem lipschitz_bound_iff (hF : TorusCovering.ProjectionProperties s)
    (hsymm : ∀ u w : s.Torus, pointDist w u = pointDist u w)
    (hA : ShortVectorNormPreserved s)
    (hle : ∀ x, pointNorm (proj s x) ≤ euclidNormVec x)
    (hB : BallMapsIsometricallyOnto s c R)
    (hR : R ≤ PeriodicLattice.torusSide s.L s.m / 4) (hℓ : 0 < PeriodicLattice.torusSide s.L s.m)
    (hgh : IsPushdown s c R g h) {C : ℝ} (hC : 0 ≤ C) :
    (∀ u w : s.Torus, ‖h u - h w‖ ≤ C * pointDist u w) ↔
      ∀ x y, ‖g x - g y‖ ≤ C * euclidDistR4 x y := by
  constructor
  · intro H x y
    by_cases hx : x ∈ closedBallR4 c R <;> by_cases hy : y ∈ closedBallR4 c R
    · rw [← hgh.2.1 x hx, ← hgh.2.1 y hy, ← hB.2 x hx y hy]
      exact H _ _
    · exact lipschitz_ascend hA hle hR hℓ hgh hC H hx hy
    · have := lipschitz_ascend hA hle hR hℓ hgh hC H hy hx
      rw [norm_sub_rev]
      have hd : euclidDistR4 x y = euclidDistR4 y x := normVec_sub_comm x y
      rwa [hd]
    · rw [hgh.1 x hx, hgh.1 y hy, sub_self, norm_zero]
      exact mul_nonneg hC (normVec_nonneg _)
  · intro H u w
    by_cases hu : h u = 0 <;> by_cases hw : h w = 0
    · rw [hu, hw, sub_self, norm_zero]
      obtain ⟨τ, -, hn⟩ := exists_lift_normVec_eq_pointNorm hF (u - w)
      have : 0 ≤ pointDist u w := by
        show 0 ≤ pointNorm (u - w)
        rw [← hn]
        exact normVec_nonneg _
      exact mul_nonneg hC this
    · have := lipschitz_descend hF hB hgh H hw hu
      rw [norm_sub_rev]
      rwa [hsymm] at this ⊢
    · have := lipschitz_descend hF hB hgh H hu hw
      rwa [hsymm] at this
    · obtain ⟨x, hx, rfl⟩ := hB.1.surjOn (mem_torusBallOver_of_apply_ne_zero hgh hu)
      obtain ⟨y, hy, rfl⟩ := hB.1.surjOn (mem_torusBallOver_of_apply_ne_zero hgh hw)
      rw [hgh.2.1 x hx, hgh.2.1 y hy, hB.2 x hx y hy]
      exact H x y
theorem sameLipschitzConstant_holds (hF : TorusCovering.ProjectionProperties s)
    (hsymm : ∀ u w : s.Torus, pointDist w u = pointDist u w)
    (hA : ShortVectorNormPreserved s)
    (hle : ∀ x, pointNorm (proj s x) ≤ euclidNormVec x)
    (hB : BallMapsIsometricallyOnto s c R)
    (hR : R ≤ PeriodicLattice.torusSide s.L s.m / 4) (hℓ : 0 < PeriodicLattice.torusSide s.L s.m)
    (hgh : IsPushdown s c R g h) : SameLipschitzConstant s g h := by
  have key := fun (C : ℝ) (hC : 0 ≤ C) => lipschitz_bound_iff hF hsymm hA hle hB hR hℓ hgh hC
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨C, hC, H⟩
    exact ⟨C, hC, (key C hC).1 H⟩
  · rintro ⟨C, hC, H⟩
    exact ⟨C, hC, (key C hC).2 H⟩
  · intro _
    unfold lipConstTorus lipConstR4 bestLipschitzConstant
    congr 1
    ext C
    constructor
    · rintro ⟨hC, H⟩
      exact ⟨hC, (key C hC).1 H⟩
    · rintro ⟨hC, H⟩
      exact ⟨hC, (key C hC).2 H⟩
theorem supportsCorrespond_holds (hB : BallMapsIsometricallyOnto s c R) (hR0 : 0 < R)
    (hgh : IsPushdown s c R g h) : SupportsCorrespond s c R g h := by
  have hbij := hB.1
  have hsub : Function.support g ⊆ closedBallR4 c R := fun x hx => mem_ball_of_apply_ne_zero hgh hx
  have hcl : closure (Function.support g) ⊆ closedBallR4 c R :=
    closure_minimal hsub (closedBallR4_isClosed c R)
  have hcpt : IsCompact (closure (Function.support g)) :=
    (closedBallR4_isCompact c hR0.le).of_isClosed_subset isClosed_closure hcl
  have hclosedImage : IsClosed (proj s '' closure (Function.support g)) :=
    (hcpt.image proj_continuous).isClosed
  have hballClosed : IsClosed (torusBallOver s c R) := by
    rw [← hbij.image_eq]
    exact ((closedBallR4_isCompact c hR0.le).image proj_continuous).isClosed
  have himage : Function.support h = proj s '' Function.support g := by
    ext u
    constructor
    · intro hu
      obtain ⟨x, hx, rfl⟩ := hbij.surjOn (mem_torusBallOver_of_apply_ne_zero hgh hu)
      refine ⟨x, ?_, rfl⟩
      have hne : h (proj s x) ≠ 0 := hu
      rw [hgh.2.1 x hx] at hne
      exact hne
    · rintro ⟨x, hx, rfl⟩
      have hne : g x ≠ 0 := hx
      show h (proj s x) ≠ 0
      rwa [hgh.2.1 x (hsub hx)]
  refine ⟨hcl, ?_, ?_⟩
  · exact closure_minimal (fun u hu => mem_torusBallOver_of_apply_ne_zero hgh hu) hballClosed
  · show closure (Function.support h) = proj s '' closure (Function.support g)
    rw [himage]
    apply Subset.antisymm
    · exact closure_minimal (image_mono subset_closure) hclosedImage
    · exact image_closure_subset_closure_image proj_continuous
theorem sameIntegral_holds (hT : TorusCovering.PeriodizationProperties s)
    (hgh : IsPushdown s c R g h) (hc1 : IsPeriodizationOf s c R g h) :
    SameIntegral s g h := by
  intro hb hm
  obtain ⟨-, -, ⟨hdiam, -⟩, heq⟩ := hc1
  obtain ⟨-, ⟨hb', hm'⟩, hint⟩ := hT (closedBallR4 c R) g hdiam hb hm hgh.1
  rw [heq]
  exact ⟨hb', hm', hint⟩
end Ball
theorem ballProjectionStatement_holds (hCells : TranslatedLatticeCells.CellsAndBallsStatement)
    (hMeasure : TorusCovering.CoveringIntegralVolumeStatement) : BallProjectionStatement := by
  intro s R c hR0 hR
  obtain ⟨hD, -, -, -⟩ := hCells s
  obtain ⟨hF, -, -, hT⟩ := hMeasure s
  have hle := hD.2
  have hsymm : ∀ u w : s.Torus, pointDist w u = pointDist u w :=
    fun u w => (hD.1 u w 0).1
  have hℓ : 0 < PeriodicLattice.torusSide s.L s.m := by linarith
  have hA := shortVectorNormPreserved_holds hF hle hℓ
  have hB : BallMapsIsometricallyOnto s c R :=
    ballMapsIsometricallyOnto_holds hF hle hA hR hℓ
  refine ⟨hA, hB, pushdownBijective_holds hB, fun g h hgh => ?_⟩
  have hc1 := isPeriodizationOf_holds hB hR hℓ hgh
  exact ⟨hc1, sameValues_holds hB hgh, sameLipschitzConstant_holds hF hsymm hA hle hB hR hℓ hgh,
    supportsCorrespond_holds hB hR0 hgh, sameIntegral_holds hT hgh hc1⟩
end YangMills.Construction.TorusMeasure.BallProjection
end
