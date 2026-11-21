import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeProof
import YangMills.Construction.Torus.GeometryTransportLiftAndDilationOfTestPairs
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
open YangMills.Construction.TestPairs
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestFunctions.PairTransport
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_sub_comm (u v : Fin 4 → ℝ) :
    euclidNormVec (u - v) = euclidNormVec (v - u) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNormVec_smul (a : ℝ) (v : Fin 4 → ℝ) :
    euclidNormVec (a • v) = |a| * euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem euclidNormVec_sub_le_of_mem_closedBallR4 {c t t' : Fin 4 → ℝ} {R : ℝ}
    (ht : t ∈ closedBallR4 c R) (ht' : t' ∈ closedBallR4 c R) :
    euclidNormVec (t - t') ≤ 2 * R := by apply _root_.YangMills.Construction.TestPairs.euclidNormVec_sub_le_two_mul_of_mem <;> assumption
theorem le_euclidNormVec_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ euclidNormVec (latticeTranslate ℓ k) := by apply _root_.YangMills.Construction.TestPairs.le_euclidNormVec_latticeTranslate <;> assumption
def affineScale (a : ℝ) (v x : Fin 4 → ℝ) : Fin 4 → ℝ := a • x + v
section AffineScale
variable {a : ℝ} {v : Fin 4 → ℝ}
theorem euclidNormVec_affineScale_sub (ha : 0 < a) (x y : Fin 4 → ℝ) :
    euclidNormVec (affineScale a v x - affineScale a v y) = a * euclidNormVec (x - y) := by
  have h : affineScale a v x - affineScale a v y = a • (x - y) := by
    simp [affineScale, smul_sub]
  rw [h, euclidNormVec_smul, abs_of_pos ha]
theorem affineScale_affineScale_inv (ha : 0 < a) (x : Fin 4 → ℝ) :
    affineScale a v (affineScale a⁻¹ (-(a⁻¹ • v)) x) = x := by
  simp [affineScale, smul_add, smul_smul, mul_inv_cancel₀ ha.ne']
theorem affineScale_surjective (ha : 0 < a) : Function.Surjective (affineScale a v) :=
  fun x => ⟨_, affineScale_affineScale_inv ha x⟩
def affineScaleHomeomorph (ha : 0 < a) (v : Fin 4 → ℝ) : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) :=
  (Homeomorph.smulOfNeZero a ha.ne').trans (Homeomorph.addRight v)
theorem coe_affineScaleHomeomorph (ha : 0 < a) :
    (affineScaleHomeomorph ha v : (Fin 4 → ℝ) → Fin 4 → ℝ) = affineScale a v := by
  funext x
  simp [affineScaleHomeomorph, affineScale]
theorem tsupport_comp_affineScale (ha : 0 < a) (φ : (Fin 4 → ℝ) → ℝ) :
    tsupport (φ ∘ affineScale a v) = affineScale a v ⁻¹' tsupport φ := by
  rw [← coe_affineScaleHomeomorph ha, tsupport, tsupport, Function.support_comp_eq_preimage,
    Homeomorph.preimage_closure]
theorem uniformNorm_comp_affineScale (ha : 0 < a) (φ : (Fin 4 → ℝ) → ℝ) :
    uniformNorm (φ ∘ affineScale a v) = uniformNorm φ := by
  unfold uniformNorm
  exact (affineScale_surjective ha).iSup_comp fun y => ‖φ y‖
theorem integral_comp_affineScale (ha : 0 < a) (φ : (Fin 4 → ℝ) → ℝ) :
    ∫ x, (φ ∘ affineScale a v) x = (a ^ 4)⁻¹ * ∫ x, φ x := by
  have h1 : ∫ x, (φ ∘ affineScale a v) x = ∫ x, (fun y => φ (y + v)) (a • x) := rfl
  have h2 := Measure.integral_comp_smul (volume : Measure (Fin 4 → ℝ)) (fun y => φ (y + v)) a
  rw [h1, h2, integral_add_right_eq_self (fun y => φ y) v]
  have : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp
  rw [this, abs_of_pos (by positivity), smul_eq_mul]
theorem isLipschitzFor_comp_affineScale (ha : 0 < a) {φ : (Fin 4 → ℝ) → ℝ}
    (hφ : IsLipschitzFor euclidDistR4 φ) : IsLipschitzFor euclidDistR4 (φ ∘ affineScale a v) := by
  obtain ⟨C, hC, h⟩ := hφ
  refine ⟨C * a, by positivity, fun x y => ?_⟩
  have := h (affineScale a v x) (affineScale a v y)
  simp only [euclidDistR4, euclidNormVec_affineScale_sub ha] at this
  simp only [euclidDistR4, Function.comp]
  linarith
theorem bestLipschitzConstant_comp_affineScale_le (ha : 0 < a) {φ : (Fin 4 → ℝ) → ℝ}
    (hφ : IsLipschitzFor euclidDistR4 φ) :
    bestLipschitzConstant euclidDistR4 (φ ∘ affineScale a v) ≤
      a * bestLipschitzConstant euclidDistR4 φ := by
  have hstep : ∀ C ∈ {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖φ x - φ y‖ ≤ C * euclidDistR4 x y},
      a⁻¹ * bestLipschitzConstant euclidDistR4 (φ ∘ affineScale a v) ≤ C := by
    rintro C ⟨hC, h⟩
    have hle : bestLipschitzConstant euclidDistR4 (φ ∘ affineScale a v) ≤ a * C := by
      refine csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨by positivity, fun x y => ?_⟩
      have := h (affineScale a v x) (affineScale a v y)
      simp only [euclidDistR4, euclidNormVec_affineScale_sub ha] at this
      simp only [euclidDistR4, Function.comp]
      linarith
    calc a⁻¹ * bestLipschitzConstant euclidDistR4 (φ ∘ affineScale a v) ≤ a⁻¹ * (a * C) := by
          gcongr
      _ = C := by field_simp
  obtain ⟨C₀, hC₀, h₀⟩ := hφ
  have hinf : a⁻¹ * bestLipschitzConstant euclidDistR4 (φ ∘ affineScale a v) ≤
      bestLipschitzConstant euclidDistR4 φ := le_csInf ⟨C₀, hC₀, h₀⟩ hstep
  calc bestLipschitzConstant euclidDistR4 (φ ∘ affineScale a v)
      = a * (a⁻¹ * bestLipschitzConstant euclidDistR4 (φ ∘ affineScale a v)) := by field_simp
    _ ≤ _ := by gcongr
theorem bump_conditions_comp_affineScale (ha : 0 < a) {d ϑ : ℝ} (hd : 0 < d) (hϑ : 0 < ϑ)
    {φ : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (hL : IsLipschitzFor euclidDistR4 φ)
    (hs : tsupport φ ⊆ closedBallR4 x d) (hi : ϑ * uniformNorm φ * d ^ 4 ≤ ∫ y, φ y)
    (hl : bestLipschitzConstant euclidDistR4 φ ≤ uniformNorm φ / (ϑ * d)) :
    tsupport (φ ∘ affineScale a v) ⊆ closedBallR4 (affineScale a⁻¹ (-(a⁻¹ • v)) x) (d / a) ∧
      ϑ * uniformNorm (φ ∘ affineScale a v) * (d / a) ^ 4 ≤ ∫ y, (φ ∘ affineScale a v) y ∧
      bestLipschitzConstant euclidDistR4 (φ ∘ affineScale a v) ≤
        uniformNorm (φ ∘ affineScale a v) / (ϑ * (d / a)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tsupport_comp_affineScale ha]
    intro u hu
    have h1 : euclidNormVec (affineScale a v u - x) ≤ d := hs hu
    have h2 := euclidNormVec_affineScale_sub (v := v) ha u (affineScale a⁻¹ (-(a⁻¹ • v)) x)
    rw [affineScale_affineScale_inv ha] at h2
    show euclidNormVec (u - _) ≤ d / a
    rw [le_div_iff₀ ha]
    linarith
  · rw [uniformNorm_comp_affineScale ha, integral_comp_affineScale ha, div_pow]
    calc ϑ * uniformNorm φ * (d ^ 4 / a ^ 4) = (a ^ 4)⁻¹ * (ϑ * uniformNorm φ * d ^ 4) := by
          field_simp
      _ ≤ _ := by gcongr
  · rw [uniformNorm_comp_affineScale ha]
    refine (bestLipschitzConstant_comp_affineScale_le ha hL).trans ?_
    calc a * bestLipschitzConstant euclidDistR4 φ ≤ a * (uniformNorm φ / (ϑ * d)) := by gcongr
      _ = uniformNorm φ / (ϑ * (d / a)) := by field_simp
theorem setDistR4_le_mul_preimage {T : (Fin 4 → ℝ) → Fin 4 → ℝ} {c : ℝ} (hc : 0 < c)
    (hT : ∀ x y, euclidNormVec (T x - T y) = c * euclidNormVec (x - y)) (A B : Set (Fin 4 → ℝ)) :
    setDistR4 A B ≤ ENNReal.ofReal c * setDistR4 (T ⁻¹' A) (T ⁻¹' B) := by
  have h0 : ENNReal.ofReal c ≠ 0 := by simpa using hc
  have ht : ENNReal.ofReal c ≠ ∞ := ENNReal.ofReal_ne_top
  rw [← ENNReal.div_le_iff' h0 ht]
  refine le_iInf₂ fun a' ha' => le_iInf₂ fun b' hb' => ?_
  rw [ENNReal.div_le_iff' h0 ht, ← ENNReal.ofReal_mul hc.le, ← hT]
  exact iInf₂_le_of_le (T a') ha' (iInf₂_le (T b') hb')
theorem comp_affineScale_mem_separatedPairsR4 (ha : 0 < a) {d ϑ : ℝ} (hd : 0 < d) (hϑ : 0 < ϑ)
    {f h : (Fin 4 → ℝ) → ℝ} (hp : (f, h) ∈ separatedPairsR4 d ϑ) :
    (f ∘ affineScale a v, h ∘ affineScale a v) ∈ separatedPairsR4 (d / a) ϑ := by
  obtain ⟨⟨l₁, n₁, z₁⟩, ⟨l₂, n₂, z₂⟩, x₁, x₂, ⟨s₁, i₁, c₁⟩, ⟨s₂, i₂, c₂⟩, lo, hi⟩ :=
    (mem_separatedPairs_iff _ _ _ _ _ _ _).mp hp
  simp only at l₁ n₁ z₁ l₂ n₂ z₂ s₁ i₁ c₁ s₂ i₂ c₂ lo hi
  obtain ⟨b₁, b₂, b₃⟩ := bump_conditions_comp_affineScale (v := v) ha hd hϑ l₁ s₁ i₁ c₁
  obtain ⟨e₁, e₂, e₃⟩ := bump_conditions_comp_affineScale (v := v) ha hd hϑ l₂ s₂ i₂ c₂
  have hnz : ∀ {φ : (Fin 4 → ℝ) → ℝ}, (∃ y, φ y ≠ 0) → ∃ y, (φ ∘ affineScale a v) y ≠ 0 := by
    rintro φ ⟨y, hy⟩
    obtain ⟨y', rfl⟩ := affineScale_surjective (v := v) ha y
    exact ⟨y', hy⟩
  refine (mem_separatedPairs_iff _ _ _ _ _ _ _).mpr ⟨⟨isLipschitzFor_comp_affineScale ha l₁,
    fun y => n₁ _, hnz z₁⟩, ⟨isLipschitzFor_comp_affineScale ha l₂, fun y => n₂ _, hnz z₂⟩,
    _, _, ⟨b₁, b₂, b₃⟩, ⟨e₁, e₂, e₃⟩, ?_, ?_⟩
  · simp only [tsupport_comp_affineScale ha]
    have h1 := lo.trans (setDistR4_le_mul_preimage ha (euclidNormVec_affineScale_sub (v := v) ha)
      (tsupport f) (tsupport h))
    rw [ENNReal.ofReal_div_of_pos ha]
    exact (ENNReal.div_le_iff' (by simpa using ha) ENNReal.ofReal_ne_top).mpr h1
  · simp only [tsupport_comp_affineScale ha]
    have hinv : ∀ x y, euclidNormVec (affineScale a⁻¹ (-(a⁻¹ • v)) x -
        affineScale a⁻¹ (-(a⁻¹ • v)) y) = a⁻¹ * euclidNormVec (x - y) :=
      euclidNormVec_affineScale_sub (inv_pos.mpr ha)
    have h1 := setDistR4_le_mul_preimage (inv_pos.mpr ha) hinv (affineScale a v ⁻¹' tsupport f)
      (affineScale a v ⁻¹' tsupport h)
    have hpre : ∀ A : Set (Fin 4 → ℝ),
        affineScale a⁻¹ (-(a⁻¹ • v)) ⁻¹' (affineScale a v ⁻¹' A) = A := by
      intro A
      ext x
      simp [affineScale_affineScale_inv ha]
    rw [hpre, hpre] at h1
    refine h1.trans ?_
    calc ENNReal.ofReal a⁻¹ * setDistR4 (tsupport f) (tsupport h)
        ≤ ENNReal.ofReal a⁻¹ * ENNReal.ofReal (6 * d) := by gcongr
      _ = ENNReal.ofReal (6 * (d / a)) := by
          rw [← ENNReal.ofReal_mul (inv_pos.mpr ha).le]
          congr 1
          field_simp
theorem inverseEighthKernel_comp_affineScale (ha : 0 < a) (f h : (Fin 4 → ℝ) → ℝ) :
    inverseEighthKernel (f ∘ affineScale a v) (h ∘ affineScale a v) = inverseEighthKernel f h := by
  set G : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℝ :=
    fun w => f w.1 * h w.2 * ((euclidNormVec (w.1 - w.2) ^ (-8 : ℤ) : ℝ) : ℝ) with hG
  have hfree : inverseEighthKernel f h = ∫ w, G w := rfl
  have hkey : ∀ z : (Fin 4 → ℝ) × (Fin 4 → ℝ),
      (f ∘ affineScale a v) z.1 * (h ∘ affineScale a v) z.2 *
          ((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : ℝ) =
        a ^ 8 * (fun w => G (w + (v, v))) (a • z) := by
    intro z
    have hz : euclidNormVec ((a • z.1 + v) - (a • z.2 + v)) = a * euclidNormVec (z.1 - z.2) :=
      euclidNormVec_affineScale_sub ha z.1 z.2
    simp only [hG, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Function.comp,
      affineScale, hz, mul_zpow]
    have ha8 : a ^ 8 * a ^ (-8 : ℤ) = 1 := by
      rw [zpow_neg, show ((8 : ℤ)) = ((8 : ℕ) : ℤ) from rfl, zpow_natCast]
      field_simp
    linear_combination (-(f (a • z.1 + v) * h (a • z.2 + v)) *
      euclidNormVec (z.1 - z.2) ^ (-8 : ℤ)) * ha8
  have h1 : inverseEighthKernel (f ∘ affineScale a v) (h ∘ affineScale a v) =
      ∫ z : (Fin 4 → ℝ) × (Fin 4 → ℝ), a ^ 8 * (fun w => G (w + (v, v))) (a • z) :=
    integral_congr_ae (Filter.Eventually.of_forall hkey)
  have : ((volume : Measure (Fin 4 → ℝ)).prod (volume : Measure (Fin 4 → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have h2 := Measure.integral_comp_smul
    ((volume : Measure (Fin 4 → ℝ)).prod (volume : Measure (Fin 4 → ℝ)))
    (fun w => G (w + (v, v))) a
  rw [h1, hfree, integral_const_mul, Measure.volume_eq_prod, h2,
    integral_add_right_eq_self (fun w => G w) (v, v)]
  have : Module.finrank ℝ ((Fin 4 → ℝ) × (Fin 4 → ℝ)) = 8 := by simp
  rw [this, abs_of_pos (by positivity), smul_eq_mul]
  field_simp
end AffineScale
section TorusNorm
variable {ℓ : ℝ}
theorem torusProj_add (t t' : Fin 4 → ℝ) : torusProj ℓ (t + t') = torusProj ℓ t + torusProj ℓ t' := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem torusProj_sub (t t' : Fin 4 → ℝ) : torusProj ℓ (t - t') = torusProj ℓ t - torusProj ℓ t' := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem exists_torusProj_eq_euclidNormVec_eq (u : Torus4 ℓ) :
    ∃ τ, torusProj ℓ τ = u ∧ euclidNormVec τ = torusEuclidNorm u := by apply _root_.YangMills.Construction.AmbientPoints.exists_torusProj_eq_euclidNormVec_eq <;> assumption
theorem torusEuclidNorm_torusProj_le (t : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj ℓ t) ≤ euclidNormVec t := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
theorem torusEuclidNorm_neg (u : Torus4 ℓ) : torusEuclidNorm (-u) = torusEuclidNorm u := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.torusEuclidNorm_neg <;> assumption
theorem torusEuclidNorm_add_le (u v : Torus4 ℓ) :
    torusEuclidNorm (u + v) ≤ torusEuclidNorm u + torusEuclidNorm v := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
theorem exists_torusProj_eq_near (c : Fin 4 → ℝ) (u : Torus4 ℓ) :
    ∃ w, torusProj ℓ w = u ∧ euclidNormVec (w - c) = torusEuclidNorm (u - torusProj ℓ c) := by
  obtain ⟨τ, hτ, h⟩ := exists_torusProj_eq_euclidNormVec_eq (u - torusProj ℓ c)
  refine ⟨τ + c, ?_, ?_⟩
  · rw [torusProj_add, hτ, sub_add_cancel]
  · rw [add_sub_cancel_right, h]
theorem closedBallTorus_subset_image (c : Fin 4 → ℝ) (r : ℝ) :
    closedBallTorus (torusProj ℓ c) r ⊆ torusProj ℓ '' closedBallR4 c r := by
  intro u hu
  obtain ⟨w, hw, h⟩ := exists_torusProj_eq_near c u
  refine ⟨w, ?_, hw⟩
  show euclidNormVec (w - c) ≤ r
  rw [h]
  exact hu
theorem image_closedBallR4_subset (c : Fin 4 → ℝ) (r : ℝ) :
    torusProj ℓ '' closedBallR4 c r ⊆ closedBallTorus (torusProj ℓ c) r := by
  rintro _ ⟨w, hw, rfl⟩
  show torusEuclidNorm (torusProj ℓ w - torusProj ℓ c) ≤ r
  rw [← torusProj_sub]
  exact (torusEuclidNorm_torusProj_le _).trans hw
end TorusNorm
theorem isClosed_closedBallTorus {L m : ℕ} (z : FourTorus L m) (ρ : ℝ) :
    @IsClosed _ (metricTopology L m) (closedBallTorus z ρ) := by
  have ho : IsMetricOpen (closedBallTorus z ρ)ᶜ := by
    intro y hy
    have hy' : ρ < torusEuclidNorm (y - z) := not_le.mp hy
    refine ⟨torusEuclidNorm (y - z) - ρ, by linarith, fun y' hy₁ hin => ?_⟩
    have h1 : torusEuclidNorm (y' - y) < torusEuclidNorm (y - z) - ρ := hy₁
    have h2 : torusEuclidNorm (y' - z) ≤ ρ := hin
    have h3 := torusEuclidNorm_add_le (-(y' - y)) (y' - z)
    rw [torusEuclidNorm_neg] at h3
    have h4 : -(y' - y) + (y' - z) = y - z := by abel
    rw [h4] at h3
    linarith
  exact @IsClosed.mk _ (metricTopology L m) _ ho
theorem metricSupport_subset_closedBallTorus {L m : ℕ} {z : FourTorus L m} {ρ : ℝ}
    {f : FourTorus L m → ℝ} (h : ∀ y, f y ≠ 0 → y ∈ closedBallTorus z ρ) :
    PeriodicLattice.metricSupport f ⊆ closedBallTorus z ρ :=
  @closure_minimal _ (metricTopology L m) _ _ (show {y | f y ≠ 0} ⊆ closedBallTorus z ρ from h)
    (isClosed_closedBallTorus z ρ)
theorem mem_metricSupport_of_ne_zero {L m : ℕ} {f : FourTorus L m → ℝ} {y : FourTorus L m}
    (h : f y ≠ 0) : y ∈ PeriodicLattice.metricSupport f :=
  @subset_closure _ (metricTopology L m) {y | f y ≠ 0} y h
section Translates
variable {ℓ : ℝ}
theorem latticeTranslate_sub (k k' : Fin 4 → ℤ) :
    latticeTranslate ℓ (k - k') = latticeTranslate ℓ k - latticeTranslate ℓ k' := by apply _root_.YangMills.Construction.LatticeCovering.latticeTranslate_sub <;> assumption
theorem torusProj_sub_latticeTranslate (y : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    torusProj ℓ (y - latticeTranslate ℓ k) = torusProj ℓ y := by
  have := torusProj_add_latticeTranslate ℓ (y - latticeTranslate ℓ k) k
  rwa [sub_add_cancel, eq_comm] at this
theorem latticeTranslate_index_unique (hℓ : 0 < ℓ) {c c' u u₀ w w₀ : Fin 4 → ℝ} {r r' : ℝ}
    {k k₀ : Fin 4 → ℤ} (hsum : 2 * r + 2 * r' < ℓ) (hu : u ∈ closedBallR4 c r)
    (hu₀ : u₀ ∈ closedBallR4 c r) (hw : w ∈ closedBallR4 c' r') (hw₀ : w₀ ∈ closedBallR4 c' r')
    (h : w = u + latticeTranslate ℓ k) (h₀ : w₀ = u₀ + latticeTranslate ℓ k₀) : k = k₀ := by
  by_contra hne
  have h1 := le_euclidNormVec_latticeTranslate hℓ (sub_ne_zero.mpr hne)
  have h2 : latticeTranslate ℓ (k - k₀) = (w - w₀) + (u₀ - u) := by
    rw [latticeTranslate_sub, h, h₀]
    abel
  rw [h2] at h1
  have h3 := euclidNormVec_add_le (w - w₀) (u₀ - u)
  have h4 := euclidNormVec_sub_le_of_mem_closedBallR4 hw hw₀
  have h5 := euclidNormVec_sub_le_of_mem_closedBallR4 hu₀ hu
  linarith
theorem exists_latticeTranslate_between_balls (hℓ : 0 < ℓ) {c c' : Fin 4 → ℝ} {r r' : ℝ}
    (hsum : 2 * r + 2 * r' < ℓ) {P : Set (Torus4 ℓ)} (hne : P.Nonempty)
    (h₁ : P ⊆ torusProj ℓ '' closedBallR4 c r) (h₂ : P ⊆ torusProj ℓ '' closedBallR4 c' r') :
    ∃ k : Fin 4 → ℤ,
      (∀ u ∈ closedBallR4 c r, torusProj ℓ u ∈ P → u + latticeTranslate ℓ k ∈ closedBallR4 c' r') ∧
      ∀ w ∈ closedBallR4 c' r', torusProj ℓ w ∈ P → w - latticeTranslate ℓ k ∈ closedBallR4 c r := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨u₀, hu₀, e₁⟩ := h₁ hp
  obtain ⟨w₀, hw₀, e₂⟩ := h₂ hp
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq (e₂.trans e₁.symm)
  refine ⟨k, fun u hu hP => ?_, fun w hw hP => ?_⟩
  · obtain ⟨w, hw, e⟩ := h₂ hP
    obtain ⟨k', hk'⟩ := exists_latticeTranslate_of_torusProj_eq e
    have := latticeTranslate_index_unique hℓ hsum hu hu₀ hw hw₀ hk' hk
    rw [← this, ← hk']
    exact hw
  · obtain ⟨u, hu, e⟩ := h₁ hP
    obtain ⟨k', hk'⟩ := exists_latticeTranslate_of_torusProj_eq e.symm
    have := latticeTranslate_index_unique hℓ hsum hu hu₀ hw hw₀ hk' hk
    rw [← this, hk', add_sub_cancel_right]
    exact hu
theorem liftToBall_eq_shift {c c' : Fin 4 → ℝ} {r r' : ℝ} {P : Set (Torus4 ℓ)}
    {φ : Torus4 ℓ → ℝ} {k : Fin 4 → ℤ} (hφ : ∀ y, φ y ≠ 0 → y ∈ P)
    (hA : ∀ u ∈ closedBallR4 c r, torusProj ℓ u ∈ P → u + latticeTranslate ℓ k ∈ closedBallR4 c' r')
    (hB : ∀ w ∈ closedBallR4 c' r', torusProj ℓ w ∈ P → w - latticeTranslate ℓ k ∈ closedBallR4 c r) :
    liftToBall ℓ c' r' φ = fun y => liftToBall ℓ c r φ (y - latticeTranslate ℓ k) := by
  funext y
  have hcov := torusProj_sub_latticeTranslate (ℓ := ℓ) y k
  by_cases h1 : y ∈ closedBallR4 c' r' <;> by_cases h2 : y - latticeTranslate ℓ k ∈ closedBallR4 c r
  · simp [liftToBall, indicator, h1, h2, hcov]
  · have h0 : φ (torusProj ℓ y) = 0 := by
      by_contra hne
      exact h2 (hB y h1 (hφ _ hne))
    simp [liftToBall, indicator, h1, h2, h0]
  · have h0 : φ (torusProj ℓ y) = 0 := by
      by_contra hne
      have := hA _ h2 (by rw [hcov]; exact hφ _ hne)
      rw [sub_add_cancel] at this
      exact h1 this
    simp [liftToBall, indicator, h1, h2, hcov, h0]
  · simp [liftToBall, indicator, h1, h2]
theorem shift_eq_comp_affineScale (g : (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ) :
    (fun y => g (y - v)) = g ∘ affineScale 1 (-v) := by
  funext y
  simp [affineScale, sub_eq_add_neg]
theorem periodize_shift (g : (Fin 4 → ℝ) → ℝ) (k : Fin 4 → ℤ) :
    periodize ℓ (fun y => g (y - latticeTranslate ℓ k)) = periodize ℓ g := by
  funext x
  obtain ⟨v, rfl⟩ := torusProj_surjective ℓ x
  rw [periodize_torusProj, periodize_torusProj]
  have h1 : periodicSum ℓ (fun y => g (y - latticeTranslate ℓ k)) v =
      periodicSum ℓ g (v - latticeTranslate ℓ k) := by
    unfold periodicSum
    refine tsum_congr fun c => ?_
    show g (v + latticeTranslate ℓ c - latticeTranslate ℓ k) = _
    rw [show v + latticeTranslate ℓ c - latticeTranslate ℓ k =
      v - latticeTranslate ℓ k + latticeTranslate ℓ c by abel]
  rw [h1, ← periodicSum_add_latticeTranslate ℓ g (v - latticeTranslate ℓ k) k, sub_add_cancel]
theorem periodize_liftToBall (hℓ : 0 < ℓ) {c : Fin 4 → ℝ} {r : ℝ} (hr : r ≤ ℓ / 4)
    {φ : Torus4 ℓ → ℝ} (h0 : ∀ x, x ∉ torusProj ℓ '' closedBallR4 c r → φ x = 0) :
    periodize ℓ (liftToBall ℓ c r φ) = φ := by
  funext x
  obtain ⟨v, rfl⟩ := torusProj_surjective ℓ x
  rw [periodize_torusProj]
  unfold periodicSum
  by_cases hx : ∃ k, v + latticeTranslate ℓ k ∈ closedBallR4 c r
  · obtain ⟨k₀, hk₀⟩ := hx
    rw [tsum_eq_single k₀]
    · simp [liftToBall, indicator, hk₀, torusProj_add_latticeTranslate]
    · intro k hk
      have hout : v + latticeTranslate ℓ k ∉ closedBallR4 c r := by
        intro hin
        have h1 := le_euclidNormVec_latticeTranslate hℓ (sub_ne_zero.mpr hk)
        have h2 := euclidNormVec_sub_le_of_mem_closedBallR4 hin hk₀
        have h3 : latticeTranslate ℓ (k - k₀) =
            (v + latticeTranslate ℓ k) - (v + latticeTranslate ℓ k₀) := by
          rw [latticeTranslate_sub]
          abel
        rw [h3] at h1
        linarith
      simp [liftToBall, indicator, hout]
  · have hz : ∀ k, liftToBall ℓ c r φ (v + latticeTranslate ℓ k) = 0 := by
      intro k
      have : v + latticeTranslate ℓ k ∉ closedBallR4 c r := fun hin => hx ⟨k, hin⟩
      simp [liftToBall, indicator, this]
    simp only [hz, tsum_zero]
    refine (h0 _ ?_).symm
    rintro ⟨u, hu, e⟩
    obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq e
    exact hx ⟨k, hk ▸ hu⟩
end Translates
section BaseLift
theorem uniformNorm_pos {φ : (Fin 4 → ℝ) → ℝ} (hb : IsBoundedFun φ) (hz : ∃ y, φ y ≠ 0) :
    0 < uniformNorm φ := by
  obtain ⟨y, hy⟩ := hz
  obtain ⟨C, hC⟩ := hb
  have h1 : ‖φ y‖ ≤ uniformNorm φ :=
    le_ciSup (f := fun x => ‖φ x‖) ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩ y
  exact lt_of_lt_of_le (norm_pos_iff.mpr hy) h1
theorem kernelTwoSidedBound_of_chain {d ϑ s₁ s₂ i₁ i₂ K : ℝ}
    (h : KernelBoundChain d ϑ s₁ s₂ i₁ i₂ K) : KernelTwoSidedBound ϑ s₁ s₂ K := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨h₁.trans h₂, (h₃.trans h₄).trans_eq ?_⟩
  unfold kernelUpperConst
  ring
variable {ℓ d ϑ : ℝ}
def IsBaseLift (ℓ d ϑ : ℝ) (F H : Torus4 ℓ → ℝ) (c : Fin 4 → ℝ) : Prop :=
  (∃ y, F y ≠ 0) ∧ (∀ y, F y ≠ 0 → y ∈ torusProj ℓ '' closedBallR4 c (5 * d)) ∧
    (∀ y, H y ≠ 0 → y ∈ torusProj ℓ '' closedBallR4 c (5 * d)) ∧
    (liftToBall ℓ c (5 * d) F, liftToBall ℓ c (5 * d) H) ∈ separatedPairsR4 d ϑ ∧
    periodize ℓ (liftToBall ℓ c (5 * d) F) = F ∧ periodize ℓ (liftToBall ℓ c (5 * d) H) = H ∧
    PreservesInvariants F H (liftToBall ℓ c (5 * d) F) (liftToBall ℓ c (5 * d) H)
theorem exists_isBaseLift (hG : TestPairs.GeometryAndKernelBounds) {L : ℕ}
    (hs : IsSepShapePair d ϑ) (hside : IsAdmissibleSide L ℓ d) {F H : Torus4 ℓ → ℝ}
    (hp : (F, H) ∈ separatedPairsTorus ℓ d ϑ) : ∃ c, IsBaseLift ℓ d ϑ F H c := by
  have hd := hs.1
  have hℓ : 0 < ℓ := by linarith [hside.2]
  obtain ⟨⟨-, -, z₁⟩, -, x₁, x₂, hc⟩ := (mem_separatedPairs_iff _ _ _ _ _ _ _).mp hp
  obtain ⟨-, hLift⟩ := hG.2 L ℓ d ϑ hs hside x₁ x₂ F H hp hc
  obtain ⟨X₂, hX₂, hdist⟩ := exists_torusProj_eq_near (liftPoint x₁) x₂
  have hX₁ : torusProj ℓ (liftPoint x₁) = x₁ := torusProj_liftPoint x₁
  have hd' : euclidDistR4 (liftPoint x₁) X₂ = euclidDistTorus x₁ x₂ := by
    show euclidNormVec (liftPoint x₁ - X₂) = torusEuclidNorm (x₁ - x₂)
    rw [euclidNormVec_sub_comm, hdist, hX₁, ← neg_sub, torusEuclidNorm_neg]
  obtain ⟨h5, ⟨y, ⟨himg, -⟩, -, hsupp⟩, hb₁, hb₂, hclass, -, hkeep⟩ :=
    hLift _ _ hX₁ hX₂ hd'
  have hsub : ∀ {φ : Torus4 ℓ → ℝ}, tsupport φ ⊆ closedBallTorus y (5 * d) → ∀ u, φ u ≠ 0 →
      u ∈ torusProj ℓ '' closedBallR4 (midpointR4 (liftPoint x₁) X₂) (5 * d) := by
    intro φ hφ u hu
    rw [himg]
    exact hφ (subset_tsupport _ hu)
  have hr : 5 * d ≤ ℓ / 4 := by linarith
  exact ⟨_, z₁, hsub (subset_union_left.trans hsupp), hsub (subset_union_right.trans hsupp),
    hclass, periodize_liftToBall hℓ hr hb₁.2.2, periodize_liftToBall hℓ hr hb₂.2.2, hkeep⟩
theorem exists_shift_of_isBaseLift (hd : 0 < d) (h40 : 40 * d ≤ ℓ) {F H : Torus4 ℓ → ℝ}
    {c₀ c : Fin 4 → ℝ} {r : ℝ} (href : IsBaseLift ℓ d ϑ F H c₀) (hr : r ≤ ℓ / 4)
    (h₁ : ∀ y, F y ≠ 0 → y ∈ torusProj ℓ '' closedBallR4 c r)
    (h₂ : ∀ y, H y ≠ 0 → y ∈ torusProj ℓ '' closedBallR4 c r) :
    ∃ k : Fin 4 → ℤ,
      liftToBall ℓ c r F = (fun y => liftToBall ℓ c₀ (5 * d) F (y - latticeTranslate ℓ k)) ∧
      liftToBall ℓ c r H = fun y => liftToBall ℓ c₀ (5 * d) H (y - latticeTranslate ℓ k) := by
  obtain ⟨⟨y₀, hy₀⟩, hF, hH, -⟩ := href
  have hℓ : 0 < ℓ := by linarith
  have hsum : 2 * (5 * d) + 2 * r < ℓ := by linarith
  obtain ⟨k, hA, hB⟩ := exists_latticeTranslate_between_balls (P := {y | F y ≠ 0 ∨ H y ≠ 0}) hℓ
    hsum ⟨y₀, Or.inl hy₀⟩ (fun y hy => hy.elim (hF y) (hH y)) (fun y hy => hy.elim (h₁ y) (h₂ y))
  exact ⟨k, liftToBall_eq_shift (fun y hy => Or.inl hy) hA hB,
    liftToBall_eq_shift (fun y hy => Or.inr hy) hA hB⟩
theorem shift_mem_separatedPairsR4 (hs : IsSepShapePair d ϑ) {f h : (Fin 4 → ℝ) → ℝ}
    (hp : (f, h) ∈ separatedPairsR4 d ϑ) (v : Fin 4 → ℝ) :
    ((fun y => f (y - v)), (fun y => h (y - v))) ∈ separatedPairsR4 d ϑ := by
  have := comp_affineScale_mem_separatedPairsR4 (a := 1) (v := -v) one_pos hs.1 hs.2.1 hp
  rw [div_one] at this
  rwa [shift_eq_comp_affineScale f v, shift_eq_comp_affineScale h v]
theorem uniformNorm_shift (f : (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ) :
    uniformNorm (fun y => f (y - v)) = uniformNorm f := by
  rw [shift_eq_comp_affineScale]
  exact uniformNorm_comp_affineScale one_pos f
theorem inverseEighthKernel_shift (f h : (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ) :
    inverseEighthKernel (fun y => f (y - v)) (fun y => h (y - v)) = inverseEighthKernel f h := by
  rw [shift_eq_comp_affineScale f, shift_eq_comp_affineScale h]
  exact inverseEighthKernel_comp_affineScale one_pos f h
theorem isKernelPairR4_of_mem (hG : TestPairs.GeometryAndKernelBounds)
    (hs : IsSepShapePair d ϑ) {f h : (Fin 4 → ℝ) → ℝ}
    (hp : (f, h) ∈ separatedPairsR4 d ϑ) : IsKernelPairR4 f h := by
  obtain ⟨-, -, x₁, x₂, hc⟩ := (mem_separatedPairs_iff _ _ _ _ _ _ _).mp hp
  exact (hG.1 d ϑ hs x₁ x₂ f h hp hc).1.2.2.2.1
end BaseLift
section Requirements
variable {L m : ℕ} {d ϑ : ℝ}
theorem pairLiftProperties_of_ball {F H : FourTorus L m → ℝ} {c₀ c : Fin 4 → ℝ} {r : ℝ}
    (hs : IsSepShapePair d ϑ) (h40 : 40 * d ≤ torusSide L m)
    (href : IsBaseLift (torusSide L m) d ϑ F H c₀) (hr : r ≤ torusSide L m / 4)
    (h₁ : ∀ y, F y ≠ 0 → y ∈ torusProj (torusSide L m) '' closedBallR4 c r)
    (h₂ : ∀ y, H y ≠ 0 → y ∈ torusProj (torusSide L m) '' closedBallR4 c r) :
    PairLiftProperties d ϑ F H (liftToBall (torusSide L m) c r F)
      (liftToBall (torusSide L m) c r H) := by
  obtain ⟨k, e₁, e₂⟩ := exists_shift_of_isBaseLift hs.1 h40 href hr h₁ h₂
  obtain ⟨-, -, -, hcl, t₁, t₂, n₁, n₂, -, -, -, -, -, n₃⟩ := href
  rw [e₁, e₂]
  refine ⟨shift_mem_separatedPairsR4 hs hcl _, ?_, ?_, ?_, ?_, ?_⟩
  · exact (periodize_shift _ k).trans t₁
  · exact (periodize_shift _ k).trans t₂
  · rw [uniformNorm_shift]
    exact n₁
  · rw [uniformNorm_shift]
    exact n₂
  · rw [inverseEighthKernel_shift]
    exact n₃
theorem kernelTorusWellDefined_of_mem (hG : TestPairs.GeometryAndKernelBounds)
    (hs : IsSepShapePair d ϑ) (hside : IsAdmissibleSide L (torusSide L m) d)
    {F H : FourTorus L m → ℝ} (hp : (F, H) ∈ separatedPairsFourTorus L m d ϑ) :
    KernelTorusWellDefined F H := by
  obtain ⟨c₀, href⟩ := exists_isBaseLift hG hs hside hp
  obtain ⟨-, -, x₁, x₂, hc⟩ := (mem_separatedPairs_iff _ _ _ _ _ _ _).mp hp
  obtain ⟨⟨-, -, -, ⟨q, hq⟩, -⟩, -⟩ := hG.2 L (torusSide L m) d ϑ hs hside x₁ x₂ F H hp hc
  refine ⟨⟨q.1, q.2, hq⟩, fun c r hk => ?_⟩
  obtain ⟨-, -, hr, ht₁, ht₂⟩ := hk
  have hl := pairLiftProperties_of_ball hs hside.2 href hr
    (fun y hy => closedBallTorus_subset_image c r (ht₁ (subset_tsupport _ hy)))
    (fun y hy => closedBallTorus_subset_image c r (ht₂ (subset_tsupport _ hy)))
  exact ⟨isKernelPairR4_of_mem hG hs hl.1, hl.2.2.2.2.2⟩
theorem pairGeometryR4_of_mem (hG : TestPairs.GeometryAndKernelBounds)
    (hs : IsSepShapePair d ϑ) {f h : (Fin 4 → ℝ) → ℝ} {x₁ x₂ : Fin 4 → ℝ}
    (hp : (f, h) ∈ separatedPairsR4 d ϑ) (hc : IsCentrePairR4 d ϑ x₁ x₂ (f, h)) :
    PairGeometryR4 d ϑ x₁ x₂ f h := by
  obtain ⟨⟨-, -, z₁⟩, ⟨-, -, z₂⟩, -⟩ := (mem_separatedPairs_iff _ _ _ _ _ _ _).mp hp
  obtain ⟨⟨b₁, ⟨-, hsupp⟩, b₃, b₄, b₅⟩, -⟩ := hG.1 d ϑ hs x₁ x₂ f h hp hc
  exact ⟨uniformNorm_pos b₄.1 z₁, uniformNorm_pos b₄.2.1 z₂, b₁, subset_union_left.trans hsupp,
    subset_union_right.trans hsupp, b₃, kernelTwoSidedBound_of_chain b₅⟩
theorem periodizationOfPairR4_of_mem (hG : TestPairs.GeometryAndKernelBounds)
    (hs : IsSepShapePair d ϑ) (hside : IsAdmissibleSide L (torusSide L m) d)
    {f h : (Fin 4 → ℝ) → ℝ} (hp : (f, h) ∈ separatedPairsR4 d ϑ) :
    PeriodizationOfPairR4 L m d ϑ f h := by
  obtain ⟨-, -, x₁, x₂, hc⟩ := (mem_separatedPairs_iff _ _ _ _ _ _ _).mp hp
  have hd := hs.1
  have h40 := hside.2
  obtain ⟨-, hT⟩ := hG.1 d ϑ hs x₁ x₂ f h hp hc
  obtain ⟨-, -, hcl, -, hl₁, hl₂, e₁, e₂, n₁, n₂, -, -, -, -, -, n₃⟩ := hT L (torusSide L m) hside
  have hball : ∀ {φ : FourTorus L m → ℝ},
      LiftsToBall (torusSide L m) (midpointR4 x₁ x₂) (5 * d) φ →
      PeriodicLattice.metricSupport φ ⊆
        closedBallTorus (torusProj (torusSide L m) (midpointR4 x₁ x₂)) (5 * d) := by
    intro φ hφ
    refine metricSupport_subset_closedBallTorus fun y hy => image_closedBallR4_subset _ _ ?_
    by_contra hout
    exact hy (hφ.2.2 y hout)
  refine ⟨hcl, n₁.symm, n₂.symm, kernelTorusWellDefined_of_mem hG hs hside hcl, n₃.symm, hs.2.1,
    hs.2.2, hd, h40, hcl, torusProj (torusSide L m) (midpointR4 x₁ x₂), 5 * d,
    ⟨⟨by linarith, by linarith⟩, ?_⟩, midpointR4 x₁ x₂, rfl, ?_⟩
  · intro i
    fin_cases i
    · exact hball hl₁
    · exact hball hl₂
  · intro i
    fin_cases i
    · exact e₁.symm
    · exact e₂.symm
theorem exists_ball_of_isPairLift {F H : FourTorus L m → ℝ} {f h : (Fin 4 → ℝ) → ℝ}
    (hl : IsPairLift d ϑ F H f h) :
    ∃ (c : Fin 4 → ℝ) (r : ℝ), r ≤ torusSide L m / 4 ∧
      (∀ y, F y ≠ 0 → y ∈ torusProj (torusSide L m) '' closedBallR4 c r) ∧
      (∀ y, H y ≠ 0 → y ∈ torusProj (torusSide L m) '' closedBallR4 c r) ∧
      f = liftToBall (torusSide L m) c r F ∧ h = liftToBall (torusSide L m) c r H := by
  obtain ⟨-, -, -, -, -, z, ρ, ⟨⟨-, hρ⟩, hsup⟩, c, hc, hi⟩ := hl
  have hz : torusProj (torusSide L m) c = z := hc
  subst hz
  have h₀ : PeriodicLattice.metricSupport F ⊆ closedBallTorus (torusProj (torusSide L m) c) ρ :=
    hsup 0
  have h₁ : PeriodicLattice.metricSupport H ⊆ closedBallTorus (torusProj (torusSide L m) c) ρ :=
    hsup 1
  exact ⟨c, ρ, hρ.le,
    fun y hy => closedBallTorus_subset_image c ρ (h₀ (mem_metricSupport_of_ne_zero hy)),
    fun y hy => closedBallTorus_subset_image c ρ (h₁ (mem_metricSupport_of_ne_zero hy)), hi 0, hi 1⟩
theorem pairLiftProperties_of_isPairLift (hG : TestPairs.GeometryAndKernelBounds)
    (hs : IsSepShapePair d ϑ) (hside : IsAdmissibleSide L (torusSide L m) d)
    {F H : FourTorus L m → ℝ} (hp : (F, H) ∈ separatedPairsFourTorus L m d ϑ)
    {f h : (Fin 4 → ℝ) → ℝ} (hl : IsPairLift d ϑ F H f h) : PairLiftProperties d ϑ F H f h := by
  obtain ⟨c₀, href⟩ := exists_isBaseLift hG hs hside hp
  obtain ⟨c, r, hr, h₁, h₂, rfl, rfl⟩ := exists_ball_of_isPairLift hl
  exact pairLiftProperties_of_ball hs hside.2 href hr h₁ h₂
theorem exists_shift_of_isPairLift (hG : TestPairs.GeometryAndKernelBounds)
    (hs : IsSepShapePair d ϑ) (hside : IsAdmissibleSide L (torusSide L m) d)
    {F H : FourTorus L m → ℝ} (hp : (F, H) ∈ separatedPairsFourTorus L m d ϑ)
    {f₁ h₁ f₂ h₂ : (Fin 4 → ℝ) → ℝ}
    (hl₁ : IsPairLift d ϑ F H f₁ h₁) (hl₂ : IsPairLift d ϑ F H f₂ h₂) :
    ∃ k₀ : Fin 4 → ℤ, (f₂ = fun y => f₁ (y - latticeTranslate (torusSide L m) k₀)) ∧
      h₂ = fun y => h₁ (y - latticeTranslate (torusSide L m) k₀) := by
  obtain ⟨c₀, href⟩ := exists_isBaseLift hG hs hside hp
  obtain ⟨c, r, hr, a₁, a₂, rfl, rfl⟩ := exists_ball_of_isPairLift hl₁
  obtain ⟨c', r', hr', b₁, b₂, rfl, rfl⟩ := exists_ball_of_isPairLift hl₂
  obtain ⟨k, e₁, e₂⟩ := exists_shift_of_isBaseLift hs.1 hside.2 href hr a₁ a₂
  obtain ⟨k', e₁', e₂'⟩ := exists_shift_of_isBaseLift hs.1 hside.2 href hr' b₁ b₂
  have hv : ∀ y : Fin 4 → ℝ, y - latticeTranslate (torusSide L m) (k' - k) -
      latticeTranslate (torusSide L m) k = y - latticeTranslate (torusSide L m) k' := by
    intro y
    rw [latticeTranslate_sub]
    abel
  refine ⟨k' - k, ?_, ?_⟩
  · rw [e₁, e₁']
    funext y
    simp only [hv]
  · rw [e₂, e₂']
    funext y
    simp only [hv]
theorem pairTorusProperties_of_mem (hG : TestPairs.GeometryAndKernelBounds)
    (hs : IsSepShapePair d ϑ) (hside : IsAdmissibleSide L (torusSide L m) d)
    {F H : FourTorus L m → ℝ} (hp : (F, H) ∈ separatedPairsFourTorus L m d ϑ) :
    PairTorusProperties d ϑ F H := by
  have hd := hs.1
  have h40 := hside.2
  obtain ⟨-, -, x₁, x₂, hc⟩ := (mem_separatedPairs_iff _ _ _ _ _ _ _).mp hp
  obtain ⟨⟨b₁, -, -, -, b₅⟩, -⟩ := hG.2 L (torusSide L m) d ϑ hs hside x₁ x₂ F H hp hc
  obtain ⟨⟨s₁, -, -⟩, ⟨s₂, -, -⟩, -⟩ := hc
  have hsupp : SupportsInBall x₁ (9 * d) ![F, H] := by
    refine ⟨⟨by linarith, by linarith⟩, fun i => ?_⟩
    fin_cases i
    · refine metricSupport_subset_closedBallTorus fun y hy => ?_
      have h1 : torusEuclidNorm (y - x₁) ≤ d := s₁ (subset_tsupport _ hy)
      show torusEuclidNorm (y - x₁) ≤ 9 * d
      linarith
    · refine metricSupport_subset_closedBallTorus fun y hy => ?_
      have h1 : torusEuclidNorm (y - x₂) ≤ d := s₂ (subset_tsupport _ hy)
      have h2 : torusEuclidNorm (x₁ - x₂) ≤ 8 * d := b₁
      have h3 := torusEuclidNorm_add_le (y - x₂) (x₂ - x₁)
      rw [sub_add_sub_cancel, ← neg_sub x₁ x₂, torusEuclidNorm_neg] at h3
      show torusEuclidNorm (y - x₁) ≤ 9 * d
      linarith
  refine ⟨⟨x₁, hsupp⟩, ⟨ballIndicatorLift (liftPoint x₁) (9 * d) F,
    ballIndicatorLift (liftPoint x₁) (9 * d) H, hs.2.1, hs.2.2, hd, h40, hp, x₁, 9 * d, hsupp,
    liftPoint x₁, torusProj_liftPoint x₁, ?_⟩,
    fun f' h' hl => pairLiftProperties_of_isPairLift hG hs hside hp hl,
    kernelTwoSidedBound_of_chain b₅,
    fun f₁ h₁ f₂ h₂ hl₁ hl₂ => exists_shift_of_isPairLift hG hs hside hp hl₁ hl₂⟩
  intro i
  fin_cases i <;> rfl
theorem liftsPeriodizeConsistently_of_mem (hG : TestPairs.GeometryAndKernelBounds)
    (hs : IsSepShapePair d ϑ) (hL : 1 < L) (hside : IsAdmissibleSide L (torusSide L m) d)
    {m' : ℕ} (hside' : IsAdmissibleSide L (torusSide L m') d)
    (hle : torusSide L m' ≤ torusSide L m) {F H : FourTorus L m → ℝ}
    (hp : (F, H) ∈ separatedPairsFourTorus L m d ϑ) : LiftsPeriodizeConsistently m' d ϑ F H := by
  have hL' : (1 : ℝ) < L := by exact_mod_cast hL
  have hm : m' ≤ m := by
    have h1 : (L : ℝ) ^ m' ≤ (L : ℝ) ^ m := by
      have := hle
      simp only [torusSide] at this
      linarith
    exact (pow_le_pow_iff_right₀ hL').mp h1
  have hper : ∀ k : Fin 4 → ℤ, ∃ k' : Fin 4 → ℤ,
      latticeTranslate (torusSide L m) k = latticeTranslate (torusSide L m') k' := by
    intro k
    refine ⟨fun μ => (L : ℤ) ^ (m - m') * k μ, ?_⟩
    funext μ
    have h1 : (L : ℝ) ^ m = (L : ℝ) ^ m' * (L : ℝ) ^ (m - m') := by
      rw [← pow_add, Nat.add_sub_cancel' hm]
    simp only [latticeTranslate, torusSide, h1]
    push_cast
    ring
  refine ⟨fun f₁ h₁ f₂ h₂ hl₁ hl₂ => ?_, fun f' h' hl => ?_⟩
  · obtain ⟨k₀, e₁, e₂⟩ := exists_shift_of_isPairLift hG hs hside hp hl₁ hl₂
    obtain ⟨k', hk'⟩ := hper k₀
    rw [e₁, e₂, hk']
    exact ⟨(periodize_shift f₁ k').symm, (periodize_shift h₁ k').symm⟩
  · obtain ⟨hcl, -, -, n₁, n₂, n₃⟩ := pairLiftProperties_of_isPairLift hG hs hside hp hl
    obtain ⟨c₁, s₁, s₂, -, k₁, -⟩ := periodizationOfPairR4_of_mem hG hs hside' hcl
    exact ⟨c₁, s₁.trans n₁, s₂.trans n₂, k₁.trans n₃⟩
theorem meshSize_natCast_pos (hL : 0 < L) (b : ℕ) : 0 < meshSize L (b : ℤ) := by apply _root_.YangMills.Construction.SourcesAndGluing.meshSize_pos <;> assumption
theorem dilateR4_eq_comp_affineScale (b : ℕ) (f : (Fin 4 → ℝ) → ℝ) :
    dilateR4 L b f = f ∘ affineScale (meshSize L (b : ℤ)) 0 := by
  funext x
  simp [dilateR4, affineScale]
theorem div_meshSize_natCast (hL : 0 < L) (b : ℕ) (d : ℝ) :
    d / meshSize L (b : ℤ) = (L : ℝ) ^ b * d := by
  have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [meshSize, zpow_neg, zpow_natCast]
  field_simp
theorem dilationPairR4_of_mem (hs : IsSepShapePair d ϑ) (hL : 0 < L) (b : ℕ)
    {f h : (Fin 4 → ℝ) → ℝ} (hp : (f, h) ∈ separatedPairsR4 d ϑ) :
    DilationPairR4 L b d ϑ f h := by
  have ha := meshSize_natCast_pos hL b
  have hc := comp_affineScale_mem_separatedPairsR4 (v := 0) ha hs.1 hs.2.1 hp
  rw [div_meshSize_natCast hL] at hc
  rw [DilationPairR4, dilateR4_eq_comp_affineScale, dilateR4_eq_comp_affineScale]
  exact ⟨hc, uniformNorm_comp_affineScale ha f, uniformNorm_comp_affineScale ha h,
    inverseEighthKernel_comp_affineScale ha f h⟩
theorem dilateTorus_eq_periodize (hL : 0 < L) (b : ℕ) {F : FourTorus L m → ℝ}
    {f : (Fin 4 → ℝ) → ℝ} (ht : periodize (torusSide L m) f = F) :
    dilateTorus L m b F = periodize (torusSide L (m + b)) (dilateR4 L b f) := by
  have hside : meshSize L (b : ℤ) * torusSide L (m + b) = torusSide L m := by
    simp only [meshSize, torusSide, zpow_neg, zpow_natCast, pow_add]
    field_simp
  funext x
  obtain ⟨v, rfl⟩ := torusProj_surjective _ x
  rw [periodize_torusProj, dilateTorus, contractTorus_torusProj hL, ← ht, periodize_torusProj]
  unfold periodicSum
  refine tsum_congr fun k => ?_
  simp only [dilateR4]
  congr 1
  funext μ
  simp only [Pi.smul_apply, Pi.add_apply, latticeTranslate, smul_eq_mul, ← hside]
  ring
theorem dilationPairTorus_of_mem (hG : TestPairs.GeometryAndKernelBounds)
    (hs : IsSepShapePair d ϑ) (hL : 0 < L) (hm : 0 < m) (b : ℕ)
    (hside : IsAdmissibleSide L (torusSide L m) d) {F H : FourTorus L m → ℝ}
    (hp : (F, H) ∈ separatedPairsFourTorus L m d ϑ) : DilationPairTorus b d ϑ F H := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hsd : torusSide L (m + b) = (L : ℝ) ^ b * torusSide L m := by
    simp only [torusSide, pow_add]
    ring
  have hsides : (L : ℝ) ^ b * torusSide L m ∈ torusSides L := ⟨m + b, by omega, hsd.symm⟩
  have h40 : 40 * ((L : ℝ) ^ b * d) ≤ (L : ℝ) ^ b * torusSide L m := by
    have := mul_le_mul_of_nonneg_left hside.2 (pow_pos hL' b).le
    linarith
  obtain ⟨-, ⟨f', h', hl⟩, hall, -⟩ := pairTorusProperties_of_mem hG hs hside hp
  obtain ⟨hcl, t₁, t₂, n₁, n₂, n₃⟩ := hall f' h' hl
  obtain ⟨c, s₁, s₂, k⟩ := dilationPairR4_of_mem hs hL b hcl
  have hs' : IsSepShapePair ((L : ℝ) ^ b * d) ϑ := ⟨mul_pos (pow_pos hL' b) hs.1, hs.2⟩
  have hside' : IsAdmissibleSide L (torusSide L (m + b)) ((L : ℝ) ^ b * d) :=
    ⟨hsd ▸ hsides, hsd ▸ h40⟩
  obtain ⟨c₁, u₁, u₂, -, k₁, -⟩ := periodizationOfPairR4_of_mem hG hs' hside' c
  have e₁ := dilateTorus_eq_periodize hL b t₁
  have e₂ := dilateTorus_eq_periodize hL b t₂
  refine ⟨hsd, hsides, h40, ?_, ?_, ?_, ?_⟩
  · rw [e₁, e₂]
    exact c₁
  · rw [e₁]
    exact u₁.trans (s₁.trans n₁)
  · rw [e₂]
    exact u₂.trans (s₂.trans n₂)
  · rw [e₁, e₂]
    exact k₁.trans (k.trans n₃)
end Requirements
theorem pairTransportStatement_of_geometry (hG : TestPairs.GeometryAndKernelBounds) :
    PairTransportStatement := by
  intro s d ϑ hs
  have hL : 1 < s.L := by
    have := s.isAdmissible.2
    omega
  have hside : 40 * d ≤ s.side → IsAdmissibleSide s.L (torusSide s.L s.m) d :=
    fun h => ⟨⟨s.m, s.m.pos, rfl⟩, h⟩
  refine ⟨fun f h x₁ x₂ hp hc => pairGeometryR4_of_mem hG hs hp hc,
    fun h40 f h hp => periodizationOfPairR4_of_mem hG hs (hside h40) hp,
    fun h40 f h hp => pairTorusProperties_of_mem hG hs (hside h40) hp,
    fun m' hm' h40' hle f h hp =>
      liftsPeriodizeConsistently_of_mem hG hs hL (hside (h40'.trans hle)) ⟨hm', h40'⟩ hle hp,
    fun b => ⟨fun f h hp => dilationPairR4_of_mem hs (by omega) b hp,
      fun h40 f h hp => dilationPairTorus_of_mem hG hs (by omega) s.m.pos b (hside h40) hp⟩⟩
end YangMills.Construction.TestFunctions.PairTransport
end
