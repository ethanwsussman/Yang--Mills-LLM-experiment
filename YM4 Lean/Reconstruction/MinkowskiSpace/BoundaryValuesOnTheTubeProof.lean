import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.MotionsTensorProductsTranslationsAndTheReflection
import Reconstruction.MinkowskiSpace.AcrossTheSpacelikePointsProof
import Reconstruction.MinkowskiSpace.BoundaryValuesOnTheTube
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TubeBoundary
open MinkowskiSpace WightmanTheory
theorem taylor_integral_remainder_at_one (f : ℕ → ℝ → ℂ)
    (hf : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (f j) (f (j + 1) t) t) (m : ℕ) :
    f 0 0 = ∑ j ∈ Finset.range (m + 1), ((-1 : ℂ) ^ j / (j.factorial : ℂ)) * f j 1 +
      ((-1 : ℂ) ^ (m + 1) / (m.factorial : ℂ)) * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ m * f (m + 1) t := by
  have hI : ∀ j, ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (f j) (f (j + 1) t) t := by
    intro j t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hf j t ht
  have hc : ∀ j, ContinuousOn (f j) (Set.uIcc (0 : ℝ) 1) := fun j t ht =>
    (hI j t ht).continuousAt.continuousWithinAt
  have hii : ∀ j, IntervalIntegrable (f j) volume 0 1 := fun j => (hc j).intervalIntegrable
  induction m with
  | zero =>
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (hI 0) (hii 1)
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul, pow_one, neg_mul]
    simp only [zero_add] at h
    rw [h]
    ring
  | succ m ih =>
    have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
    have hU : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => (t : ℂ) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) ((t : ℂ) ^ m) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt.congr_deriv (by simp)
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (t : ℂ) ^ m) t := by
        simpa using h1.fun_pow (m + 1)
      exact (h2.div_const ((m + 1 : ℕ) : ℂ)).congr_deriv (mul_div_cancel_left₀ _ hm)
    have hUc : Continuous fun t : ℝ => (t : ℂ) ^ m := by fun_prop
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU (hI (m + 1))
      (hUc.intervalIntegrable 0 1) (hii (m + 2))
    have h0 : ((0 : ℝ) : ℂ) ^ (m + 1) = 0 := by simp
    simp only [h0, zero_div, zero_mul, Complex.ofReal_one, one_pow, sub_zero] at hparts
    have hdiv : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (m + 1) / ((m + 1 : ℕ) : ℂ) * f (m + 1 + 1) t =
        (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (m + 1) * f (m + 1 + 1) t) / ((m + 1 : ℕ) : ℂ) := by
      rw [← intervalIntegral.integral_div]
      exact intervalIntegral.integral_congr fun t _ => by ring
    rw [hdiv] at hparts
    rw [ih, Finset.sum_range_succ _ (m + 1)]
    have hpart2 : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ m * f (m + 1) t =
        1 / ((m + 1 : ℕ) : ℂ) * f (m + 1) 1 -
          (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (m + 1) * f (m + 1 + 1) t) / ((m + 1 : ℕ) : ℂ) := by
      linear_combination hparts
    rw [hpart2, Nat.factorial_succ]
    have hf0 : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    push_cast at hm ⊢
    field_simp
    ring
theorem hasDerivAt_along_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {g A₁ A₂ : E → ℂ} {v₁ v₂ : E}
    (hA₁ : ContinuousOn A₁ Ω) (hA₂ : ContinuousOn A₂ Ω)
    (h₁ : ∀ y ∈ Ω, HasDerivAt (fun s : ℝ => g (y + s • v₁)) (A₁ y) 0)
    (h₂ : ∀ y ∈ Ω, HasDerivAt (fun s : ℝ => g (y + s • v₂)) (A₂ y) 0) {y : E} (hy : y ∈ Ω) :
    HasDerivAt (fun s : ℝ => g (y + s • (v₁ + v₂))) (A₁ y + A₂ y) 0 := by
  let p : ℝ × ℝ → E := fun v => y + v.1 • v₁ + v.2 • v₂
  have hp : Continuous p := by fun_prop
  have hp0 : p ((0 : ℝ), (0 : ℝ)) = y := by simp [p]
  have hΩp : ∀ᶠ v in 𝓝 ((0 : ℝ), (0 : ℝ)), p v ∈ Ω :=
    hp.continuousAt.eventually (hΩ.mem_nhds (by rwa [hp0]))
  let f : ℝ → ℝ → ℂ := fun s r => g (p (s, r))
  let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun s r => (1 : ℝ →L[ℝ] ℝ).smulRight (A₁ (p (s, r)))
  let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun s r => (1 : ℝ →L[ℝ] ℝ).smulRight (A₂ (p (s, r)))
  have df₁ : ∀ᶠ v in 𝓝 ((0 : ℝ), (0 : ℝ)), HasFDerivAt (f · v.2) (Function.uncurry f₁ v) v.1 := by
    filter_upwards [hΩp] with v hv
    have h0 : HasDerivAt (fun s : ℝ => g (p v + s • v₁)) (A₁ (p v)) (v.1 - v.1) := by
      rw [sub_self]; exact h₁ _ hv
    have h1 := HasDerivAt.comp_sub_const v.1 v.1 h0
    have h2 : HasDerivAt (fun s => f s v.2) (A₁ (p v)) v.1 := by
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [f, p, sub_smul]
      congr 1
      abel
    exact h2.hasFDerivAt
  have df₂ : ∀ᶠ v in 𝓝 ((0 : ℝ), (0 : ℝ)), HasFDerivAt (f v.1 ·) (Function.uncurry f₂ v) v.2 := by
    filter_upwards [hΩp] with v hv
    have h0 : HasDerivAt (fun s : ℝ => g (p v + s • v₂)) (A₂ (p v)) (v.2 - v.2) := by
      rw [sub_self]; exact h₂ _ hv
    have h1 := HasDerivAt.comp_sub_const v.2 v.2 h0
    have h2 : HasDerivAt (fun s => f v.1 s) (A₂ (p v)) v.2 := by
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [f, p, sub_smul]
      congr 1
      abel
    exact h2.hasFDerivAt
  have cA : ∀ {A : E → ℂ}, ContinuousOn A Ω → ContinuousAt (fun v : ℝ × ℝ => A (p v)) (0, 0) := by
    intro A hA
    have h := (hA y hy).continuousAt (hΩ.mem_nhds hy)
    exact ContinuousAt.comp (f := p) (g := A) (by rwa [hp0]) hp.continuousAt
  have cf₁ : ContinuousAt (Function.uncurry f₁) ((0 : ℝ), (0 : ℝ)) := by
    have := (ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp (cA hA₁)
    exact this
  have cf₂ : ContinuousAt (Function.uncurry f₂) ((0 : ℝ), (0 : ℝ)) := by
    have := (ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp (cA hA₂)
    exact this
  have hs := (hasStrictFDerivAt_uncurry_coprod (f := f) (f₁ := f₁) (f₂ := f₂) (u := ((0 : ℝ), (0 : ℝ))) df₁ df₂ cf₁ cf₂).hasFDerivAt
  have hd : HasDerivAt (fun s : ℝ => (s, s)) ((1 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))
  have hc := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (f := fun s : ℝ => (s, s)) hs hd
  refine (hc.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  · change (1 : ℝ) • A₁ (p (0, 0)) + (1 : ℝ) • A₂ (p (0, 0)) = _
    simp [hp0]
  · change g (y + s • (v₁ + v₂)) = g (y + s • v₁ + s • v₂)
    rw [smul_add, add_assoc]
theorem hasDerivAt_along_finsetSum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {g : E → ℂ} {A : ι → E → ℂ} {v : ι → E} (S : Finset ι)
    (hA : ∀ k, ContinuousOn (A k) Ω)
    (h : ∀ k, ∀ y ∈ Ω, HasDerivAt (fun s : ℝ => g (y + s • v k)) (A k y) 0) :
    ∀ y ∈ Ω, HasDerivAt (fun s : ℝ => g (y + s • ∑ k ∈ S, v k)) (∑ k ∈ S, A k y) 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro y _
    simpa using hasDerivAt_const (0 : ℝ) (g y)
  | insert m S hm ih =>
    intro y hy
    have hc : ContinuousOn (fun y => ∑ k ∈ S, A k y) Ω :=
      continuousOn_finsetSum _ fun k _ => hA k
    have := hasDerivAt_along_add hΩ (hA m) hc (h m) ih hy
    simpa only [Finset.sum_insert hm] using this
section Points
variable {b : ℕ}
def diagTime (b : ℕ) : TestSpaces.PointTuple b := fun _ => timeUnit
def timeBasis (k : Fin b) : TestSpaces.PointTuple b := Pi.single k (Pi.single 0 1)
def complexTimeBasis (k : Fin b) : Fin b → ComplexVec4 := Pi.single k (Pi.single 0 1)
theorem timeUnit_eq_single : timeUnit = (Pi.single 0 1 : RealVec4) := by apply _root_.YangMills.Construction.MinkowskiSpace.ConeTubeLorentz.timeUnit_eq_single <;> assumption
theorem diagTime_eq_sum : diagTime b = ∑ k, timeBasis k := by
  have h := Finset.univ_sum_single (fun _ : Fin b => (Pi.single 0 1 : RealVec4))
  simp only [timeBasis]
  rw [h]
  funext k
  exact timeUnit_eq_single
theorem coneGap_add_smul_timeUnit (y : RealVec4) (t : ℝ) :
    coneGap (y + t • timeUnit) = coneGap y + t := by
  have h : spacePart (y + t • timeUnit) = spacePart y := by
    funext i
    simp [spacePart, timeUnit, mkTimeSpace]
  simp only [coneGap, h]
  simp [timeUnit, mkTimeSpace]
  ring
theorem coneGap_continuous : Continuous coneGap := by apply _root_.YangMills.Construction.WightmanTheory.continuous_coneGap <;> assumption
theorem isOpen_futureConeTuples : IsOpen (futureConeTuples b) := by
  refine isOpen_set_pi Set.finite_univ fun _ _ => ?_
  exact isOpen_lt continuous_const coneGap_continuous
theorem mem_futureConeTuples_of_gap {ε : ℝ} (hε : 0 < ε) {Y : TestSpaces.PointTuple b}
    (h : ∀ k, ε ≤ coneGap (Y k)) : Y ∈ futureConeTuples b :=
  fun k _ => lt_of_lt_of_le hε (h k)
theorem exists_uniform_gap {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b) :
    ∃ ε > 0, ∀ k, ε ≤ coneGap (Y k) := by
  rcases isEmpty_or_nonempty (Fin b) with h | h
  · exact ⟨1, one_pos, fun k => (h.false k).elim⟩
  · obtain ⟨k₀, hk₀⟩ := Finite.exists_min fun k => coneGap (Y k)
    exact ⟨_, hY k₀ trivial, hk₀⟩
theorem le_coneGap_add_diagTime {Y : TestSpaces.PointTuple b} {t : ℝ}
    (hY : Y ∈ closedFutureConeTuples b) (k : Fin b) : t ≤ coneGap ((Y + t • diagTime b) k) := by
  have : (Y + t • diagTime b) k = Y k + t • timeUnit := rfl
  rw [this, coneGap_add_smul_timeUnit]
  have h : coneGap (Y k) ≥ 0 := hY k trivial
  linarith
theorem half_le_coneGap_add_timeBasis {Y : TestSpaces.PointTuple b} {ε t : ℝ} (hε : 0 < ε)
    (h : ∀ j, ε ≤ coneGap (Y j)) (ht : |t| ≤ ε / 2) (k j : Fin b) :
    ε / 2 ≤ coneGap ((Y + t • timeBasis k) j) := by
  have ht' := abs_le.1 ht
  by_cases hjk : j = k
  · subst hjk
    have : (Y + t • timeBasis j) j = Y j + t • timeUnit := by
      simp [timeBasis, timeUnit_eq_single]
    rw [this, coneGap_add_smul_timeUnit]
    have := h j
    linarith
  · have : (Y + t • timeBasis k) j = Y j := by
      simp [timeBasis, Pi.single_eq_of_ne hjk]
    rw [this]
    have := h j
    linarith
theorem imPart_tubePoint (x Y : TestSpaces.PointTuple b) (k : Fin b) :
    MinkowskiSpace.imPart (tubePoint x Y k) = Y k := by
  funext μ
  simp [MinkowskiSpace.imPart, tubePoint, toComplex]
theorem tubePoint_mem_tubeTuples {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b)
    (x : TestSpaces.PointTuple b) : tubePoint x Y ∈ tubeTuples b := by
  intro k _
  change MinkowskiSpace.imPart (tubePoint x Y k) ∈ futureCone
  rw [imPart_tubePoint]
  exact hY k trivial
theorem tubeGap_tubePoint (x Y : TestSpaces.PointTuple b) (k : Fin b) :
    tubeGap (tubePoint x Y k) = coneGap (Y k) := by
  rw [tubeGap, imPart_tubePoint]
theorem tubePoint_continuous :
    Continuous fun p : TestSpaces.PointTuple b × TestSpaces.PointTuple b => tubePoint p.1 p.2 := by
  unfold tubePoint toComplex
  fun_prop
theorem tubePoint_add_smul_complexTimeBasis (x Y : TestSpaces.PointTuple b) (k : Fin b) (z : ℂ) :
    tubePoint x Y + z • complexTimeBasis k =
      tubePoint (x + z.re • timeBasis k) (Y + z.im • timeBasis k) := by
  funext j μ
  by_cases hjk : j = k
  · subst hjk
    by_cases hμ : μ = 0
    · subst hμ
      simp only [tubePoint, toComplex, complexTimeBasis, timeBasis, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_same, smul_eq_mul, mul_one, Complex.ofReal_add]
      apply Complex.ext <;> simp
    · simp [tubePoint, toComplex, complexTimeBasis, timeBasis, Pi.single_eq_of_ne hμ]
  · simp [tubePoint, toComplex, complexTimeBasis, timeBasis, Pi.single_eq_of_ne hjk]
def tupleToCoords (ζ : Fin b → ComplexVec4) : Coordinates.ComplexCoordinates (b * 4) :=
  fun j => ζ (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
theorem coordsToTuple_tupleToCoords (ζ : Fin b → ComplexVec4) :
    coordsToTuple (tupleToCoords ζ) = ζ := by apply _root_.YangMills.Construction.FieldForms.SpacelikeExtension.coordsToTuple_tupleCoords <;> assumption
theorem continuousOn_tubeTuples {u : (Fin b → ComplexVec4) → ℂ} (hu : IsHolomorphicOnTube u) :
    ContinuousOn u (tubeTuples b) := by apply _root_.YangMills.Construction.FieldForms.SpacelikeExtension.continuousOn_tubeTuples_of_holomorphic <;> assumption
theorem differentiableAt_time_line {u : (Fin b → ComplexVec4) → ℂ} (hu : IsHolomorphicOnTube u)
    {ζ : Fin b → ComplexVec4} (hζ : ζ ∈ tubeTuples b) (k : Fin b) :
    DifferentiableAt ℂ (fun z : ℂ => u (ζ + z • complexTimeBasis k)) 0 := by
  have hmem : tupleToCoords ζ ∈ coordsToTuple ⁻¹' tubeTuples b := by
    change coordsToTuple (tupleToCoords ζ) ∈ tubeTuples b
    rwa [coordsToTuple_tupleToCoords]
  have h := (hu.2.2 (tupleToCoords ζ) hmem (finProdFinEquiv (k, 0))).self_of_nhds
  have h0 := differentiableAt_pi.1 h 0
  have e : ∀ z : ℂ, coordsToTuple (tupleToCoords ζ + z • Coordinates.ComplexCoordinates.stdBasisVector
      (finProdFinEquiv (k, 0))) = ζ + z • complexTimeBasis k := by
    intro z
    funext i μ
    simp only [coordsToTuple, tupleToCoords, Coordinates.ComplexCoordinates.stdBasisVector,
      complexTimeBasis, Pi.add_apply, Pi.smul_apply, Equiv.symm_apply_apply, smul_eq_mul]
    congr 2
    by_cases hik : i = k
    · subst hik
      by_cases hμ : μ = 0
      · subst hμ
        simp
      · have : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (i, (0 : Fin 4)) := fun h =>
          hμ (by simpa using finProdFinEquiv.injective h)
        simp [Pi.single_eq_of_ne this, Pi.single_eq_of_ne hμ]
    · have : finProdFinEquiv (i, μ) ≠ finProdFinEquiv (k, (0 : Fin 4)) := fun h =>
        hik (by simpa using congrArg Prod.fst (finProdFinEquiv.injective h))
      simp [Pi.single_eq_of_ne this, Pi.single_eq_of_ne hik]
  simpa only [e] using h0
end Points
section Integrals
variable {b q : ℕ} {c : ℝ} {u : (Fin b → ComplexVec4) → ℂ}
def PolyGrowth (q : ℕ) (c : ℝ) (u : (Fin b → ComplexVec4) → ℂ) : Prop :=
  ∀ ζ ∈ tubeTuples b, ‖u ζ‖ ≤ c * ∏ k, (min 1 (tubeGap (ζ k)))⁻¹ ^ q
theorem norm_le_of_uniform_gap (hB : PolyGrowth q c u) (hc : 0 ≤ c) {ε : ℝ} (hε : 0 < ε)
    {Y : TestSpaces.PointTuple b} (hY : ∀ k, ε ≤ coneGap (Y k)) (x : TestSpaces.PointTuple b) :
    ‖u (tubePoint x Y)‖ ≤ c * ((min 1 ε)⁻¹) ^ (b * q) := by
  have hmem := tubePoint_mem_tubeTuples (mem_futureConeTuples_of_gap hε hY) x
  refine (hB _ hmem).trans (mul_le_mul_of_nonneg_left ?_ hc)
  have h1 : 0 < min 1 ε := lt_min one_pos hε
  have hle : ∀ k ∈ (Finset.univ : Finset (Fin b)),
      (min 1 (tubeGap (tubePoint x Y k)))⁻¹ ^ q ≤ (min 1 ε)⁻¹ ^ q := by
    intro k _
    rw [tubeGap_tubePoint]
    have h2 : min 1 ε ≤ min 1 (coneGap (Y k)) := min_le_min_left 1 (hY k)
    exact pow_le_pow_left₀ (inv_nonneg.2 (lt_of_lt_of_le h1 h2).le) ((inv_le_inv₀ (lt_of_lt_of_le h1 h2) h1).2 h2) q
  refine (Finset.prod_le_prod (fun k _ => ?_) hle).trans ?_
  · rw [tubeGap_tubePoint]
    have h2 : 0 < min 1 (coneGap (Y k)) := lt_min one_pos (lt_of_lt_of_le hε (hY k))
    positivity
  · simp [Finset.prod_const, mul_comm b q, pow_mul]
theorem continuous_comp_tubePoint (hu : IsHolomorphicOnTube u) {Y : TestSpaces.PointTuple b}
    (hY : Y ∈ futureConeTuples b) (a : TestSpaces.PointTuple b) :
    Continuous fun x : TestSpaces.PointTuple b => u (tubePoint (x + a) Y) := by
  have h : Continuous fun x : TestSpaces.PointTuple b => tubePoint (x + a) Y :=
    tubePoint_continuous.comp (f := fun x : TestSpaces.PointTuple b => (x + a, Y)) (by fun_prop)
  exact (continuousOn_tubeTuples hu).comp_continuous h fun x => tubePoint_mem_tubeTuples hY _
theorem integrable_shiftedIntegrand (hu : IsHolomorphicOnTube u) (hB : PolyGrowth q c u) (hc : 0 ≤ c)
    {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b) {ψ : TestSpaces.PointTuple b → ℂ}
    (hψ : Integrable ψ) : Integrable (shiftedIntegrand u Y ψ) := by
  obtain ⟨ε, hε, hm⟩ := exists_uniform_gap hY
  have hcont := continuous_comp_tubePoint hu hY 0
  simp only [add_zero] at hcont
  exact hψ.bdd_mul hcont.aestronglyMeasurable
    (ae_of_all _ fun x => norm_le_of_uniform_gap hB hc hε hm x)
theorem norm_pairing_le (hB : PolyGrowth q c u) (hc : 0 ≤ c) {ε : ℝ} (hε : 0 < ε)
    {Y : TestSpaces.PointTuple b} (hY : ∀ k, ε ≤ coneGap (Y k)) {ψ : TestSpaces.PointTuple b → ℂ}
    (hψ : Integrable ψ) :
    ‖pairing u Y ψ‖ ≤ c * ((min 1 ε)⁻¹) ^ (b * q) * WightmanReconstruction.lOneNorm ψ := by
  have h := norm_integral_le_of_norm_le (f := shiftedIntegrand u Y ψ)
    (hψ.norm.const_mul (c * ((min 1 ε)⁻¹) ^ (b * q)))
    (ae_of_all _ fun x => by
      simp only [shiftedIntegrand, norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_le_of_uniform_gap hB hc hε hY x) (norm_nonneg _))
  rwa [integral_const_mul] at h
theorem pairing_translateBy (Y a : TestSpaces.PointTuple b) (ψ : TestSpaces.PointTuple b → ℂ) :
    pairing u Y (translateBy a ψ) = ∫ x, u (tubePoint (x + a) Y) * ψ x := by
  rw [← integral_sub_right_eq_self (fun x => u (tubePoint (x + a) Y) * ψ x) a]
  simp [pairing, shiftedIntegrand, translateBy]
theorem continuousOn_shifted_pairing (hu : IsHolomorphicOnTube u) (hB : PolyGrowth q c u) (hc : 0 ≤ c)
    {ε : ℝ} (hε : 0 < ε) {ψ : TestSpaces.PointTuple b → ℂ} (hψ : Integrable ψ) :
    ContinuousOn
      (fun p : TestSpaces.PointTuple b × TestSpaces.PointTuple b =>
        ∫ x, u (tubePoint (x + p.2) p.1) * ψ x)
      ({Y | ∀ k, ε ≤ coneGap (Y k)} ×ˢ Set.univ) := by
  refine continuousOn_of_dominated (bound := fun x => c * ((min 1 ε)⁻¹) ^ (b * q) * ‖ψ x‖)
    ?_ ?_ (hψ.norm.const_mul _) (ae_of_all _ fun x => ?_)
  · rintro ⟨Y, a⟩ ⟨hY, -⟩
    exact (continuous_comp_tubePoint hu (mem_futureConeTuples_of_gap hε hY) a).aestronglyMeasurable.mul hψ.1
  · rintro ⟨Y, a⟩ ⟨hY, -⟩
    refine ae_of_all _ fun x => ?_
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_le_of_uniform_gap hB hc hε hY _) (norm_nonneg _)
  · refine ContinuousOn.mul ?_ continuousOn_const
    have hp : Continuous fun p : TestSpaces.PointTuple b × TestSpaces.PointTuple b =>
        tubePoint (x + p.2) p.1 :=
      tubePoint_continuous.comp
        (f := fun p : TestSpaces.PointTuple b × TestSpaces.PointTuple b => (x + p.2, p.1)) (by fun_prop)
    exact (continuousOn_tubeTuples hu).comp hp.continuousOn fun p hp' =>
      tubePoint_mem_tubeTuples (mem_futureConeTuples_of_gap hε hp'.1) _
theorem hasDerivAt_pairing_timeBasis (hu : IsHolomorphicOnTube u) (hB : PolyGrowth q c u) (hc : 0 ≤ c)
    {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b) (k : Fin b)
    {ψ : TestSpaces.PointTuple b → ℂ} (hψ : Integrable ψ)
    (hdψ : Integrable (TestSpaces.coordDeriv k 0 ψ)) (hd : Differentiable ℝ ψ) :
    HasDerivAt (fun s : ℝ => pairing u (Y + s • timeBasis k) ψ)
      (-Complex.I * pairing u Y (TestSpaces.coordDeriv k 0 ψ)) 0 := by
  obtain ⟨ε, hε, hm⟩ := exists_uniform_gap hY
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨r, hrdef⟩ : ∃ r, r = ε / 4 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; linarith
  let h : TestSpaces.PointTuple b → ℂ → ℂ := fun x z => u (tubePoint x Y + z • complexTimeBasis k)
  obtain ⟨C, hCdef⟩ : ∃ C, C = c * ((min 1 (ε / 2))⁻¹) ^ (b * q) := ⟨_, rfl⟩
  have hmarg : ∀ z : ℂ, ‖z‖ ≤ ε / 2 → ∀ j, ε / 2 ≤ coneGap ((Y + z.im • timeBasis k) j) :=
    fun z hz j => half_le_coneGap_add_timeBasis hε hm ((Complex.abs_im_le_norm z).trans hz) k j
  have hrep : ∀ x z, h x z =
      u (tubePoint (x + z.re • timeBasis k) (Y + z.im • timeBasis k)) := fun x z => by
    simp only [h, tubePoint_add_smul_complexTimeBasis]
  have hbd : ∀ x z, ‖z‖ ≤ ε / 2 → ‖h x z‖ ≤ C := fun x z hz => by
    rw [hrep, hCdef]
    exact norm_le_of_uniform_gap hB hc hε2 (hmarg z hz) _
  have hmem : ∀ x (z : ℂ), ‖z‖ ≤ ε / 2 →
      tubePoint x Y + z • complexTimeBasis k ∈ tubeTuples b := fun x z hz => by
    rw [tubePoint_add_smul_complexTimeBasis]
    exact tubePoint_mem_tubeTuples (mem_futureConeTuples_of_gap hε2 (hmarg z hz)) _
  have hdiff : ∀ x z, ‖z‖ ≤ ε / 2 → DifferentiableAt ℂ (h x) z := by
    intro x z hz
    have h0 := (differentiableAt_time_line hu (hmem x z hz) k).hasDerivAt
    rw [← sub_self z] at h0
    have h1 := HasDerivAt.comp_sub_const z z h0
    refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)).differentiableAt
    simp only [h, sub_smul]
    congr 1
    abel
  have hsmall : ∀ z w : ℂ, ‖z‖ ≤ r → ‖w - z‖ ≤ r → ‖w‖ ≤ ε / 2 := by
    intro z w hz hw
    have h1 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      simpa using norm_add_le z (w - z)
    rw [hrdef] at hz hw
    linarith
  have hcauchy : ∀ x z, ‖z‖ ≤ r → ‖deriv (h x) z‖ ≤ C / r := by
    intro x z hz
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ ?_
    · refine DifferentiableOn.diffContOnCl_ball (U := Metric.closedBall z r)
        (fun w hw => (hdiff x w (hsmall z w hz ?_)).differentiableWithinAt) subset_rfl
      simpa [dist_eq_norm] using hw
    · intro w hw
      refine hbd x w (hsmall z w hz ?_)
      simpa [dist_eq_norm] using hw.le
  have hcontx : ∀ z : ℂ, ‖z‖ ≤ ε / 2 → Continuous fun x => h x z := by
    intro z hz
    have hp : Continuous fun x : TestSpaces.PointTuple b =>
        tubePoint x Y + z • complexTimeBasis k :=
      (tubePoint_continuous.comp (f := fun x : TestSpaces.PointTuple b => (x, Y))
        (by fun_prop)).add continuous_const
    exact (continuousOn_tubeTuples hu).comp_continuous hp fun x => hmem x z hz
  have hr2 : r ≤ ε / 2 := by rw [hrdef]; linarith
  have hw : AEStronglyMeasurable (fun x => deriv (h x) 0) volume := by
    let t : ℕ → ℂ := fun n => ((r * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)
    have htpos : ∀ n : ℕ, 0 < r * (1 / ((n : ℝ) + 1)) := fun n => by positivity
    have htn : ∀ n, ‖t n‖ ≤ r := by
      intro n
      simp only [t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos n)]
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      nlinarith
    have ht0 : Tendsto t atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r
        have h2 := (Complex.continuous_ofReal.tendsto _).comp h1
        simpa [t, Function.comp_def] using h2
      · simp only [t, Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        exact (htpos n).ne'
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n x => (t n)⁻¹ • (h x (0 + t n) - h x 0)) (fun n => ?_) (ae_of_all _ fun x => ?_)
    · have h1 := hcontx (0 + t n) (by simpa using (htn n).trans hr2)
      have h2 := hcontx 0 (by simpa using hε2.le)
      exact ((h1.sub h2).const_smul (t n)⁻¹).aestronglyMeasurable
    · exact ((hdiff x 0 (by simpa using hε2.le)).hasDerivAt.tendsto_slope_zero).comp ht0
  have hbdw : ∀ x, ‖deriv (h x) 0‖ ≤ C / r := fun x => hcauchy x 0 (by simpa using hr.le)
  have hnorm : ∀ s : ℝ, s ∈ Metric.ball (0 : ℝ) r → ‖(s : ℂ) * Complex.I‖ ≤ r := by
    intro s hs
    have : |s| < r := by simpa [dist_eq_norm] using hs
    simpa using this.le
  let F : ℝ → TestSpaces.PointTuple b → ℂ := fun s x => h x ((s : ℂ) * Complex.I) * ψ x
  let F' : ℝ → TestSpaces.PointTuple b → ℂ :=
    fun s x => deriv (h x) ((s : ℂ) * Complex.I) * Complex.I * ψ x
  have hrepF : ∀ s : ℝ, pairing u (Y + s • timeBasis k) ψ = ∫ x, F s x := by
    intro s
    simp only [pairing, shiftedIntegrand, F, hrep]
    simp
  have h0 : ∀ x, h x 0 = u (tubePoint x Y) := fun x => by simp [h]
  have hfψ : Integrable fun x => u (tubePoint x Y) * ψ x :=
    integrable_shiftedIntegrand hu hB hc hY hψ
  have hfdψ : Integrable fun x => u (tubePoint x Y) * TestSpaces.coordDeriv k 0 ψ x :=
    integrable_shiftedIntegrand hu hB hc hY hdψ
  have hwψ : Integrable fun x => deriv (h x) 0 * ψ x :=
    hψ.bdd_mul hw (ae_of_all _ hbdw)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := (0 : ℝ)) (s := Metric.ball 0 r) (bound := fun x => C / r * ‖ψ x‖)
    (Metric.ball_mem_nhds _ hr)
    (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with s hs
      exact (hcontx _ ((hnorm s hs).trans hr2)).aestronglyMeasurable.mul hψ.1)
    (by
      have : F 0 = fun x => u (tubePoint x Y) * ψ x := by
        funext x
        simp [F, h0]
      rw [this]
      exact hfψ)
    (by
      have : F' 0 = fun x => deriv (h x) 0 * ψ x * Complex.I := by
        funext x
        simp only [F', Complex.ofReal_zero, zero_mul]
        ring
      rw [this]
      exact (hw.mul hψ.1).mul aestronglyMeasurable_const)
    (ae_of_all _ fun x s hs => by
      simp only [F', norm_mul, Complex.norm_I, mul_one]
      exact mul_le_mul_of_nonneg_right (hcauchy x _ (hnorm s hs)) (norm_nonneg _))
    (hψ.norm.const_mul _)
    (ae_of_all _ fun x s hs => by
      have h1 := (hdiff x _ ((hnorm s hs).trans hr2)).hasDerivAt
      have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I s :=
        (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).congr_deriv (by simp)
      have h2 := (h1.scomp s hlin).mul_const (ψ x)
      refine h2.congr_deriv ?_
      simp only [F', smul_eq_mul]
      ring)
  have ibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.mul ℝ ℂ) (f := fun x => u (tubePoint x Y))
    (f' := fun x => deriv (h x) 0) (g := ψ) (g' := TestSpaces.coordDeriv k 0 ψ)
    (v := timeBasis k) hwψ hfdψ hfψ
    (fun x _ => by
      have h1 := (hdiff x 0 (by simpa using hε2.le)).hasDerivAt
      have h1' : HasDerivAt (h x) (deriv (h x) 0) (((0 : ℝ) : ℂ)) := by simpa using h1
      have h2 := h1'.comp_ofReal
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [hrep]
      simp)
    (fun x _ => (hd x).lineDifferentiableAt.hasLineDerivAt)
  simp only [ContinuousLinearMap.mul_apply'] at ibp
  have hval : ∫ x, F' 0 x =
      -Complex.I * pairing u Y (TestSpaces.coordDeriv k 0 ψ) := by
    have e : (fun x => F' 0 x) = fun x => deriv (h x) 0 * ψ x * Complex.I := by
      funext x
      simp only [F', Complex.ofReal_zero, zero_mul]
      ring
    simp only [e, integral_mul_const, pairing, shiftedIntegrand]
    rw [ibp]
    ring
  rw [← hval]
  simpa only [hrepF] using key.2
end Integrals
section Schwartz
variable {b : ℕ}
open TestSpaces in
theorem multiDeriv_single (k : Fin b) (g : PointTuple b → ℂ) :
    multiDeriv (Pi.single k (Pi.single 0 1) : MultiIdx4 b) g =
      coordDeriv k 0 g := by
  let α : MultiIdx4 b := Pi.single k (Pi.single 0 1)
  have inner : ∀ (i : Fin b) (h : PointTuple b → ℂ),
      (List.finRange 4).foldr (fun μ h' => (coordDeriv i μ)^[α i μ] h') h =
        if i = k then coordDeriv k 0 h else h := by
    intro i h
    have e : List.finRange 4 = [0, 1, 2, 3] := by decide
    rw [e]
    by_cases hik : i = k
    · subst hik
      simp [α]
    · simp [α, hik]
  have outer : ∀ L : List (Fin b), L.Nodup →
      L.foldr (fun i h => (List.finRange 4).foldr
        (fun μ h' => (coordDeriv i μ)^[α i μ] h') h) g =
        if k ∈ L then coordDeriv k 0 g else g := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih =>
      intro hL
      have hL' := List.nodup_cons.1 hL
      rw [List.foldr_cons, ih hL'.2, inner]
      simp only [List.mem_cons]
      by_cases hik : i = k
      · subst hik
        simp [hL'.1]
      · have : k ≠ i := fun h => hik h.symm
        simp [hik, this]
  simpa [multiDeriv, List.mem_finRange] using outer _ (List.nodup_finRange b)
structure SchwartzClosure (b : ℕ) : Prop where
  coordDeriv_mem : ∀ ψ ∈ TestSpaces.schwartzSet b, ∀ k : Fin b,
    TestSpaces.coordDeriv k 0 ψ ∈ TestSpaces.schwartzSet b
  linComb_mem : ∀ φ ∈ TestSpaces.schwartzSet b, ∀ φ' ∈ TestSpaces.schwartzSet b,
    ∀ z z' : ℂ, TestSpaces.Elementary.linComb z φ z' φ' ∈ TestSpaces.schwartzSet b
  integrable : ∀ φ ∈ TestSpaces.schwartzSet b, Integrable φ
  translateBy_mem : ∀ φ ∈ TestSpaces.schwartzSet b, ∀ a : TestSpaces.PointTuple b,
    translateBy a φ ∈ TestSpaces.schwartzSet b
theorem schwartzClosure (h₁ : MotionsTranslations.Statement)
    (h₂ : WightmanReconstruction.SmoothToolkit.Toolkit)
    (h₃ : TestSpaces.Elementary.BasicProperties) (hb : 0 < b) : SchwartzClosure b where
  coordDeriv_mem ψ hψ k := by
    have h := (h₁.2.2.2.2 b hb ψ hψ (Pi.single k (Pi.single 0 1))).1
    rwa [multiDeriv_single] at h
  linComb_mem φ hφ φ' hφ' z z' := ((h₃ b hb).1.1 φ hφ φ' hφ' z z').1.1
  integrable φ hφ := (h₂.2.2.2.2.2.2.2 b hb φ hφ).1
  translateBy_mem φ hφ a := by
    have h := (h₁.2.2.2.1 b hb φ hφ 1 (-a) 1 isUnit_one ⟨le_rfl, fun i j => by
      rw [Matrix.one_apply]
      split_ifs <;> simp⟩).2.1
    have e : MotionsTranslations.affineComp 1 (-a) φ =
        translateBy a φ := by
      funext x
      simp only [MotionsTranslations.affineComp, translateBy]
      congr 1
      funext i μ
      simp [MotionsTranslations.affineApply, Matrix.one_apply,
        sub_eq_add_neg]
    rwa [e] at h
theorem SchwartzClosure.sum_coordDeriv_mem (F : SchwartzClosure b) {ψ : TestSpaces.PointTuple b → ℂ}
    (hψ : ψ ∈ TestSpaces.schwartzSet b) (S : Finset (Fin b)) :
    (fun x => ∑ k ∈ S, TestSpaces.coordDeriv k 0 ψ x) ∈
      TestSpaces.schwartzSet b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := F.linComb_mem ψ hψ ψ hψ 0 0
    have e : TestSpaces.Elementary.linComb 0 ψ 0 ψ = fun _ => 0 := by
      funext x
      simp [TestSpaces.Elementary.linComb]
    rw [e] at h
    simpa using h
  | insert m S hm ih =>
    have h := F.linComb_mem _ (F.coordDeriv_mem ψ hψ m) _ ih 1 1
    have e : TestSpaces.Elementary.linComb 1 (TestSpaces.coordDeriv m 0 ψ) 1
        (fun x => ∑ k ∈ S, TestSpaces.coordDeriv k 0 ψ x) =
        fun x => ∑ k ∈ insert m S, TestSpaces.coordDeriv k 0 ψ x := by
      funext x
      simp [TestSpaces.Elementary.linComb, Finset.sum_insert hm]
    rwa [e] at h
theorem SchwartzClosure.totalTimeDeriv_mem (F : SchwartzClosure b) {ψ : TestSpaces.PointTuple b → ℂ}
    (hψ : ψ ∈ TestSpaces.schwartzSet b) :
    totalTimeDeriv ψ ∈ TestSpaces.schwartzSet b :=
  F.sum_coordDeriv_mem hψ Finset.univ
theorem SchwartzClosure.iterate_totalTimeDeriv_mem (F : SchwartzClosure b)
    {ψ : TestSpaces.PointTuple b → ℂ} (hψ : ψ ∈ TestSpaces.schwartzSet b) (j : ℕ) :
    totalTimeDeriv^[j] ψ ∈ TestSpaces.schwartzSet b := by
  induction j with
  | zero => exact hψ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact F.totalTimeDeriv_mem ih
theorem differentiable_of_mem_schwartzSet {ψ : TestSpaces.PointTuple b → ℂ}
    (hψ : ψ ∈ TestSpaces.schwartzSet b) : Differentiable ℝ ψ :=
  hψ.1.differentiable (by simp)
theorem totalTimeDeriv_translateBy (a : TestSpaces.PointTuple b) (φ : TestSpaces.PointTuple b → ℂ) :
    totalTimeDeriv (translateBy a φ) = translateBy a (totalTimeDeriv φ) := by
  funext x
  simp only [totalTimeDeriv, translateBy, TestSpaces.coordDeriv, lineDeriv]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  funext t
  congr 1
  abel
theorem iterate_totalTimeDeriv_translateBy (a : TestSpaces.PointTuple b)
    (φ : TestSpaces.PointTuple b → ℂ) (j : ℕ) :
    totalTimeDeriv^[j] (translateBy a φ) = translateBy a (totalTimeDeriv^[j] φ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      totalTimeDeriv_translateBy]
theorem translateBy_zero (φ : TestSpaces.PointTuple b → ℂ) : translateBy 0 φ = φ := by
  funext x
  simp [translateBy]
theorem lOneNorm_translateBy (a : TestSpaces.PointTuple b) (φ : TestSpaces.PointTuple b → ℂ) :
    WightmanReconstruction.lOneNorm (translateBy a φ) = WightmanReconstruction.lOneNorm φ :=
  integral_sub_right_eq_self (fun x => ‖φ x‖) a
theorem integrable_translateBy {φ : TestSpaces.PointTuple b → ℂ} (hφ : Integrable φ)
    (a : TestSpaces.PointTuple b) : Integrable (translateBy a φ) :=
  hφ.comp_sub_right a
theorem coordDeriv_smul_add {φ φ' : TestSpaces.PointTuple b → ℂ} (hφ : Differentiable ℝ φ)
    (hφ' : Differentiable ℝ φ') (z z' : ℂ) (k : Fin b) :
    TestSpaces.coordDeriv k 0 (z • φ + z' • φ') =
      z • TestSpaces.coordDeriv k 0 φ + z' • TestSpaces.coordDeriv k 0 φ' := by
  funext x
  have h1 : HasLineDerivAt ℝ φ (TestSpaces.coordDeriv k 0 φ x) x
      (Pi.single k (Pi.single 0 1)) := (hφ x).lineDifferentiableAt.hasLineDerivAt
  have h2 : HasLineDerivAt ℝ φ' (TestSpaces.coordDeriv k 0 φ' x) x
      (Pi.single k (Pi.single 0 1)) := (hφ' x).lineDifferentiableAt.hasLineDerivAt
  exact ((h1.const_mul z).add (h2.const_mul z')).deriv
theorem totalTimeDeriv_smul_add {φ φ' : TestSpaces.PointTuple b → ℂ} (hφ : Differentiable ℝ φ)
    (hφ' : Differentiable ℝ φ') (z z' : ℂ) :
    totalTimeDeriv (z • φ + z' • φ') =
      z • totalTimeDeriv φ + z' • totalTimeDeriv φ' := by
  funext x
  simp only [totalTimeDeriv, coordDeriv_smul_add hφ hφ', Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
theorem SchwartzClosure.iterate_totalTimeDeriv_smul_add (F : SchwartzClosure b)
    {φ φ' : TestSpaces.PointTuple b → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet b)
    (hφ' : φ' ∈ TestSpaces.schwartzSet b) (z z' : ℂ) (j : ℕ) :
    totalTimeDeriv^[j] (z • φ + z' • φ') =
      z • totalTimeDeriv^[j] φ + z' • totalTimeDeriv^[j] φ' := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih,
      totalTimeDeriv_smul_add (differentiable_of_mem_schwartzSet (F.iterate_totalTimeDeriv_mem hφ j))
        (differentiable_of_mem_schwartzSet (F.iterate_totalTimeDeriv_mem hφ' j))]
end Schwartz
section Extension
variable {b q : ℕ} {c : ℝ} {u : (Fin b → ComplexVec4) → ℂ}
theorem continuousOn_pairing (hu : IsHolomorphicOnTube u) (hB : PolyGrowth q c u)
    (hc : 0 ≤ c) {ψ : TestSpaces.PointTuple b → ℂ} (hψ : Integrable ψ) :
    ContinuousOn (fun Y => pairing u Y ψ) (futureConeTuples b) := by
  intro Y hY
  obtain ⟨ε, hε, hm⟩ := exists_uniform_gap hY
  have hε2 : 0 < ε / 2 := half_pos hε
  have hnear : ∀ᶠ Y' in 𝓝 Y, ∀ k, ε / 2 ≤ coneGap (Y' k) := by
    refine Filter.eventually_all.2 fun k => ?_
    have h1 : Continuous fun Y' : TestSpaces.PointTuple b => coneGap (Y' k) :=
      coneGap_continuous.comp (continuous_apply k)
    have h2 : ε / 2 < coneGap (Y k) := by
      have := hm k
      linarith
    filter_upwards [h1.continuousAt.eventually (lt_mem_nhds h2)] with Y' hY'
    exact hY'.le
  have hS : {Y' : TestSpaces.PointTuple b | ∀ k, ε / 2 ≤ coneGap (Y' k)} ∈ 𝓝 Y := hnear
  have h1 := continuousOn_shifted_pairing hu hB hc hε2 hψ
  have h2 : ContinuousOn (fun Y' : TestSpaces.PointTuple b =>
      ∫ x, u (tubePoint (x + (0 : TestSpaces.PointTuple b)) Y') * ψ x)
      {Y' | ∀ k, ε / 2 ≤ coneGap (Y' k)} :=
    h1.comp (f := fun Y' : TestSpaces.PointTuple b => (Y', (0 : TestSpaces.PointTuple b)))
      (by fun_prop) fun Y' hY' => ⟨hY', trivial⟩
  have h3 := (h2.continuousAt hS).continuousWithinAt (s := futureConeTuples b)
  simpa [pairing, shiftedIntegrand] using h3
theorem pairing_finsetSum (hu : IsHolomorphicOnTube u) (hB : PolyGrowth q c u) (hc : 0 ≤ c)
    {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b) {ψ : Fin b → TestSpaces.PointTuple b → ℂ}
    (hψ : ∀ k, Integrable (ψ k)) :
    pairing u Y (fun x => ∑ k, ψ k x) = ∑ k, pairing u Y (ψ k) := by
  simp only [pairing, shiftedIntegrand, Finset.mul_sum]
  exact integral_finsetSum _ fun k _ => integrable_shiftedIntegrand hu hB hc hY (hψ k)
theorem hasDerivAt_pairing_diagTime (F : SchwartzClosure b) (hu : IsHolomorphicOnTube u)
    (hB : PolyGrowth q c u) (hc : 0 ≤ c) {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b)
    {ψ : TestSpaces.PointTuple b → ℂ} (hψ : ψ ∈ TestSpaces.schwartzSet b) :
    HasDerivAt (fun s : ℝ => pairing u (Y + s • diagTime b) ψ)
      (-Complex.I * pairing u Y (totalTimeDeriv ψ)) 0 := by
  have h := hasDerivAt_along_finsetSum isOpen_futureConeTuples
    (g := fun Y => pairing u Y ψ)
    (A := fun k Y => -Complex.I * pairing u Y (TestSpaces.coordDeriv k 0 ψ))
    (v := timeBasis) Finset.univ
    (fun k => continuousOn_const.mul
      (continuousOn_pairing hu hB hc (F.integrable _ (F.coordDeriv_mem ψ hψ k))))
    (fun k Y' hY' => hasDerivAt_pairing_timeBasis hu hB hc hY' k (F.integrable ψ hψ)
      (F.integrable _ (F.coordDeriv_mem ψ hψ k)) (differentiable_of_mem_schwartzSet hψ)) Y hY
  rw [← diagTime_eq_sum] at h
  refine h.congr_deriv ?_
  rw [← Finset.mul_sum]
  congr 1
  exact (pairing_finsetSum hu hB hc hY fun k =>
    F.integrable _ (F.coordDeriv_mem ψ hψ k)).symm
def taylorRemainderForm (u : (Fin b → ComplexVec4) → ℂ) (m : ℕ) (Y : TestSpaces.PointTuple b)
    (φ : TestSpaces.PointTuple b → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), (Complex.I ^ j / (j.factorial : ℂ)) *
      pairing u (Y + (1 : ℝ) • diagTime b) (totalTimeDeriv^[j] φ) +
    (Complex.I ^ (m + 1) / (m.factorial : ℂ)) * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ m *
      pairing u (Y + t • diagTime b) (totalTimeDeriv^[m + 1] φ)
theorem add_diagTime_mem_futureConeTuples {Y : TestSpaces.PointTuple b}
    (hY : Y ∈ closedFutureConeTuples b) {t : ℝ}
    (ht : 0 < t) : Y + t • diagTime b ∈ futureConeTuples b :=
  mem_futureConeTuples_of_gap ht fun k => le_coneGap_add_diagTime hY k
theorem mem_closed_of_mem_future {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b) :
    Y ∈ closedFutureConeTuples b :=
  fun k _ => show coneGap (Y k) ≥ 0 from le_of_lt (hY k trivial)
theorem add_nonneg_diagTime_mem {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b) {t : ℝ}
    (ht : 0 ≤ t) : Y + t • diagTime b ∈ futureConeTuples b := by
  refine fun k _ => ?_
  have e : (Y + t • diagTime b) k = Y k + t • timeUnit := rfl
  change coneGap _ > 0
  rw [e, coneGap_add_smul_timeUnit]
  have : coneGap (Y k) > 0 := hY k trivial
  linarith
theorem pairing_eq_taylorRemainderForm (F : SchwartzClosure b) (hu : IsHolomorphicOnTube u)
    (hB : PolyGrowth q c u) (hc : 0 ≤ c) {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b)
    {φ : TestSpaces.PointTuple b → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet b) (m : ℕ) :
    pairing u Y φ = taylorRemainderForm u m Y φ := by
  let f : ℕ → ℝ → ℂ := fun j t =>
    (-Complex.I) ^ j * pairing u (Y + t • diagTime b) (totalTimeDeriv^[j] φ)
  have hf : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (f j) (f (j + 1) t) t := by
    intro j t ht
    have h0 := hasDerivAt_pairing_diagTime F hu hB hc (add_nonneg_diagTime_mem hY ht.1)
      (F.iterate_totalTimeDeriv_mem hφ j)
    rw [← sub_self t] at h0
    have h1 := (HasDerivAt.comp_sub_const t t h0).const_mul ((-Complex.I) ^ j)
    refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp only [f]
      congr 2
      rw [sub_smul]
      abel
    · simp only [f, Function.iterate_succ_apply']
      ring
  have h := taylor_integral_remainder_at_one f hf m
  have e0 : f 0 0 = pairing u Y φ := by simp [f]
  rw [e0] at h
  rw [h, taylorRemainderForm]
  have hpow : ∀ j : ℕ, (-1 : ℂ) ^ j * (-Complex.I) ^ j = Complex.I ^ j := by
    intro j
    rw [← mul_pow]
    simp
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [f]
    linear_combination (pairing u (Y + (1 : ℝ) • diagTime b)
      (totalTimeDeriv^[j] φ) / (j.factorial : ℂ)) * hpow j
  · have e : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ m * f (m + 1) t = (-Complex.I) ^ (m + 1) *
        ∫ t in (0 : ℝ)..1, (t : ℂ) ^ m *
          pairing u (Y + t • diagTime b) (totalTimeDeriv^[m + 1] φ) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => by
        simp only [f]
        ring
    rw [e]
    linear_combination ((∫ t in (0 : ℝ)..1, (t : ℂ) ^ m *
      pairing u (Y + t • diagTime b) (totalTimeDeriv^[m + 1] φ)) /
        (m.factorial : ℂ)) * hpow (m + 1)
theorem continuousOn_pairing_translate (hu : IsHolomorphicOnTube u) (hB : PolyGrowth q c u) (hc : 0 ≤ c)
    {t : ℝ} (ht : 0 < t) {ψ : TestSpaces.PointTuple b → ℂ} (hψ : Integrable ψ) :
    ContinuousOn (fun p : TestSpaces.PointTuple b × TestSpaces.PointTuple b =>
        pairing u (p.1 + t • diagTime b) (translateBy p.2 ψ))
      (closedFutureConeTuples b ×ˢ Set.univ) := by
  have hmaps : Set.MapsTo
      (fun p : TestSpaces.PointTuple b × TestSpaces.PointTuple b => (p.1 + t • diagTime b, p.2))
      (closedFutureConeTuples b ×ˢ Set.univ)
      ({Y | ∀ k, t ≤ coneGap (Y k)} ×ˢ Set.univ) :=
    fun p hp => ⟨fun k => le_coneGap_add_diagTime hp.1 k, trivial⟩
  have h := (continuousOn_shifted_pairing hu hB hc ht hψ).comp
    (f := fun p : TestSpaces.PointTuple b × TestSpaces.PointTuple b => (p.1 + t • diagTime b, p.2))
    (by fun_prop) hmaps
  exact h.congr fun p _ => pairing_translateBy _ _ _
theorem norm_pow_mul_pairing_le (hB : PolyGrowth q c u) (hc : 0 ≤ c) {Y : TestSpaces.PointTuple b}
    (hY : Y ∈ closedFutureConeTuples b) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    {ψ : TestSpaces.PointTuple b → ℂ} (hψ : Integrable ψ) :
    ‖(t : ℂ) ^ (b * q) * pairing u (Y + t • diagTime b) ψ‖ ≤
      c * WightmanReconstruction.lOneNorm ψ := by
  have h := norm_pairing_le hB hc ht0 (fun k => le_coneGap_add_diagTime hY k) hψ
  rw [min_eq_right ht1] at h
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0.le]
  calc t ^ (b * q) * ‖pairing u (Y + t • diagTime b) ψ‖
      ≤ t ^ (b * q) * (c * t⁻¹ ^ (b * q) * WightmanReconstruction.lOneNorm ψ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = c * WightmanReconstruction.lOneNorm ψ := by
        rw [inv_pow]
        field_simp
theorem intervalIntegrable_pow_mul_pairing (hu : IsHolomorphicOnTube u) (hB : PolyGrowth q c u)
    (hc : 0 ≤ c) {Y : TestSpaces.PointTuple b} (hY : Y ∈ closedFutureConeTuples b)
    {ψ : TestSpaces.PointTuple b → ℂ} (hψ : Integrable ψ) :
    IntervalIntegrable
      (fun t : ℝ => (t : ℂ) ^ (b * q) * pairing u (Y + t • diagTime b) ψ) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hc1 : ContinuousOn (fun t : ℝ => pairing u (Y + t • diagTime b) ψ)
      (Set.Ioc 0 1) :=
    (continuousOn_pairing hu hB hc hψ).comp (f := fun t : ℝ => Y + t • diagTime b)
      (by fun_prop) fun t ht => add_diagTime_mem_futureConeTuples hY ht.1
  have hc2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (b * q)) (Set.Ioc 0 1) := by fun_prop
  refine Integrable.mono' (g := fun _ => c * WightmanReconstruction.lOneNorm ψ)
    (continuous_const.integrableOn_Ioc) ((hc2.mul hc1).aestronglyMeasurable measurableSet_Ioc) ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2
    (ae_of_all _ fun t ht => norm_pow_mul_pairing_le hB hc hY ht.1 ht.2 hψ)
theorem continuousOn_remainderIntegral (hu : IsHolomorphicOnTube u) (hB : PolyGrowth q c u)
    (hc : 0 ≤ c) {ψ : TestSpaces.PointTuple b → ℂ} (hψ : Integrable ψ) :
    ContinuousOn (fun p : TestSpaces.PointTuple b × TestSpaces.PointTuple b =>
        ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (b * q) *
          pairing u (p.1 + t • diagTime b) (translateBy p.2 ψ))
      (closedFutureConeTuples b ×ˢ Set.univ) := by
  intro p hp
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun _ => c * WightmanReconstruction.lOneNorm ψ) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with p' hp'
    rw [Set.uIoc_of_le zero_le_one]
    exact (intervalIntegrable_pow_mul_pairing hu hB hc hp'.1
      (integrable_translateBy hψ p'.2)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with p' hp'
    refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have h := norm_pow_mul_pairing_le hB hc hp'.1 ht.1 ht.2 (integrable_translateBy hψ p'.2)
    rwa [lOneNorm_translateBy] at h
  · refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact (continuousOn_const.mul (continuousOn_pairing_translate hu hB hc ht.1 hψ)) p hp
theorem continuousOn_taylorRemainderForm (F : SchwartzClosure b) (hu : IsHolomorphicOnTube u)
    (hB : PolyGrowth q c u) (hc : 0 ≤ c) {φ : TestSpaces.PointTuple b → ℂ}
    (hφ : φ ∈ TestSpaces.schwartzSet b) :
    ContinuousOn (fun p : TestSpaces.PointTuple b × TestSpaces.PointTuple b =>
        taylorRemainderForm u (b * q) p.1 (translateBy p.2 φ))
      (closedFutureConeTuples b ×ˢ Set.univ) := by
  have hI : ∀ j, Integrable (totalTimeDeriv^[j] φ) := fun j =>
    F.integrable _ (F.iterate_totalTimeDeriv_mem hφ j)
  simp only [taylorRemainderForm, iterate_totalTimeDeriv_translateBy]
  exact ContinuousOn.add
    (continuousOn_finsetSum _ fun j _ =>
      continuousOn_const.mul (continuousOn_pairing_translate hu hB hc one_pos (hI j)))
    (continuousOn_const.mul (continuousOn_remainderIntegral hu hB hc (hI _)))
theorem pairing_smul_add (hu : IsHolomorphicOnTube u) (hB : PolyGrowth q c u)
    (hc : 0 ≤ c) {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b)
    {ψ ψ' : TestSpaces.PointTuple b → ℂ} (hψ : Integrable ψ) (hψ' : Integrable ψ') (z z' : ℂ) :
    pairing u Y (z • ψ + z' • ψ') =
      z * pairing u Y ψ + z' * pairing u Y ψ' := by
  have h1 := integrable_shiftedIntegrand hu hB hc hY hψ
  have h2 := integrable_shiftedIntegrand hu hB hc hY hψ'
  have e : shiftedIntegrand u Y (z • ψ + z' • ψ') =
      fun x => z * shiftedIntegrand u Y ψ x + z' * shiftedIntegrand u Y ψ' x := by
    funext x
    simp only [shiftedIntegrand, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [pairing, e]
  rw [integral_add (h1.const_mul z) (h2.const_mul z'), integral_const_mul, integral_const_mul]
theorem taylorRemainderForm_smul_add (F : SchwartzClosure b) (hu : IsHolomorphicOnTube u)
    (hB : PolyGrowth q c u) (hc : 0 ≤ c) {Y : TestSpaces.PointTuple b}
    (hY : Y ∈ closedFutureConeTuples b)
    {φ φ' : TestSpaces.PointTuple b → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet b)
    (hφ' : φ' ∈ TestSpaces.schwartzSet b) (z z' : ℂ) :
    taylorRemainderForm u (b * q) Y (z • φ + z' • φ') =
      z * taylorRemainderForm u (b * q) Y φ + z' * taylorRemainderForm u (b * q) Y φ' := by
  have hI : ∀ j, Integrable (totalTimeDeriv^[j] φ) := fun j =>
    F.integrable _ (F.iterate_totalTimeDeriv_mem hφ j)
  have hI' : ∀ j, Integrable (totalTimeDeriv^[j] φ') := fun j =>
    F.integrable _ (F.iterate_totalTimeDeriv_mem hφ' j)
  have hterm : ∀ (j : ℕ) (t : ℝ), 0 < t →
      pairing u (Y + t • diagTime b) (totalTimeDeriv^[j] (z • φ + z' • φ')) =
        z * pairing u (Y + t • diagTime b) (totalTimeDeriv^[j] φ) +
          z' * pairing u (Y + t • diagTime b) (totalTimeDeriv^[j] φ') := by
    intro j t ht
    rw [F.iterate_totalTimeDeriv_smul_add hφ hφ']
    exact pairing_smul_add hu hB hc (add_diagTime_mem_futureConeTuples hY ht) (hI j) (hI' j) z z'
  have hterm1 : ∀ j : ℕ, _ := fun j => hterm j 1 one_pos
  have hint : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (b * q) * pairing u (Y + t • diagTime b)
        (totalTimeDeriv^[b * q + 1] (z • φ + z' • φ')) =
      z * (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (b * q) * pairing u (Y + t • diagTime b)
        (totalTimeDeriv^[b * q + 1] φ)) +
      z' * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (b * q) * pairing u (Y + t • diagTime b)
        (totalTimeDeriv^[b * q + 1] φ') := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        ((intervalIntegrable_pow_mul_pairing hu hB hc hY (hI _)).const_mul z)
        ((intervalIntegrable_pow_mul_pairing hu hB hc hY (hI' _)).const_mul z')]
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [hterm _ t ht.1]
    ring
  simp only [taylorRemainderForm, hint, hterm1]
  have hs : ∀ (A B : ℕ → ℂ) (d : ℕ → ℂ), ∑ j ∈ Finset.range (b * q + 1),
      d j * (z * A j + z' * B j) =
      z * ∑ j ∈ Finset.range (b * q + 1), d j * A j +
        z' * ∑ j ∈ Finset.range (b * q + 1), d j * B j := by
    intro A B d
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]
  ring
theorem norm_taylorRemainderForm_le (F : SchwartzClosure b) (hB : PolyGrowth q c u) (hc : 0 ≤ c)
    {Y : TestSpaces.PointTuple b} (hY : Y ∈ closedFutureConeTuples b) {φ : TestSpaces.PointTuple b → ℂ}
    (hφ : φ ∈ TestSpaces.schwartzSet b) :
    ‖taylorRemainderForm u (b * q) Y φ‖ ≤ 4 * c * maxTimeDerivNorm (b * q + 1) φ := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = maxTimeDerivNorm (b * q + 1) φ := ⟨_, rfl⟩
  rw [← hMdef]
  have hI : ∀ j, Integrable (totalTimeDeriv^[j] φ) := fun j =>
    F.integrable _ (F.iterate_totalTimeDeriv_mem hφ j)
  have hle : ∀ j ≤ b * q + 1, WightmanReconstruction.lOneNorm (totalTimeDeriv^[j] φ) ≤ M := by
    intro j hj
    rw [hMdef]
    exact Finset.le_sup' (fun j => WightmanReconstruction.lOneNorm (totalTimeDeriv^[j] φ))
      (Finset.mem_range.2 (by omega))
  have hL0 : ∀ ψ : TestSpaces.PointTuple b → ℂ, 0 ≤ WightmanReconstruction.lOneNorm ψ := fun ψ =>
    integral_nonneg fun _ => norm_nonneg _
  have hM0 : 0 ≤ M := (hL0 _).trans (hle 0 (by omega))
  have hcM : 0 ≤ c * M := mul_nonneg hc hM0
  have h1 : ∀ j ∈ Finset.range (b * q + 1),
      ‖(Complex.I ^ j / (j.factorial : ℂ)) *
        pairing u (Y + (1 : ℝ) • diagTime b) (totalTimeDeriv^[j] φ)‖ ≤
      (1 : ℝ) ^ j / (j.factorial : ℝ) * (c * M) := by
    intro j hj
    have hj' : j ≤ b * q + 1 := by
      have := Finset.mem_range.1 hj
      omega
    have h := norm_pairing_le hB hc one_pos
      (fun k => le_coneGap_add_diagTime (t := 1) hY k) (hI j)
    simp only [min_self, inv_one, one_pow, mul_one] at h
    rw [norm_mul, norm_div, norm_pow, Complex.norm_I, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left (hle j hj') hc
  have hexp : ∑ j ∈ Finset.range (b * q + 1), (1 : ℝ) ^ j / (j.factorial : ℝ) ≤ 3 :=
    (Real.sum_le_exp_of_nonneg zero_le_one _).trans
      (Real.exp_one_lt_d9.le.trans (by norm_num))
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum h1)
  rw [← Finset.sum_mul] at hsum
  have hsum3 := hsum.trans (mul_le_mul_of_nonneg_right hexp hcM)
  have hfac : ‖Complex.I ^ (b * q + 1) / ((b * q).factorial : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_pow, Complex.norm_I, one_pow, Complex.norm_natCast]
    have : (1 : ℝ) ≤ ((b * q).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    exact div_le_one_of_le₀ this (by positivity)
  have hbound : ‖∫ t in (0 : ℝ)..1, (t : ℂ) ^ (b * q) * pairing u (Y + t • diagTime b)
      (totalTimeDeriv^[b * q + 1] φ)‖ ≤ c * M * |(1 : ℝ) - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact (norm_pow_mul_pairing_le hB hc hY ht.1 ht.2 (hI _)).trans
      (mul_le_mul_of_nonneg_left (hle _ le_rfl) hc)
  have hbound' : ‖(Complex.I ^ (b * q + 1) / ((b * q).factorial : ℂ)) *
      ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (b * q) * pairing u (Y + t • diagTime b)
      (totalTimeDeriv^[b * q + 1] φ)‖ ≤ c * M := by
    rw [norm_mul]
    simp only [sub_zero, abs_one, mul_one] at hbound
    calc _ ≤ 1 * (c * M) := mul_le_mul hfac hbound (norm_nonneg _) zero_le_one
      _ = c * M := one_mul _
  refine (norm_add_le _ _).trans ?_
  linarith
end Extension
theorem boundaryValueBound_of_toolkit (h₁ : MotionsTranslations.Statement)
    (h₂ : WightmanReconstruction.SmoothToolkit.Toolkit)
    (h₃ : TestSpaces.Elementary.BasicProperties) : BoundaryValueBound := by
  intro b q c u hb hu hB'
  have hB : PolyGrowth q c u := hB'
  have F := schwartzClosure h₁ h₂ h₃ hb
  have hc : 0 ≤ c := by
    have h0 : (0 : TestSpaces.PointTuple b) ∈ closedFutureConeTuples b := fun k _ => by
      change coneGap 0 ≥ 0
      simp [coneGap, spaceNorm, spacePart]
    have hY := add_diagTime_mem_futureConeTuples h0 (t := 1) one_pos
    have hmem := tubePoint_mem_tubeTuples hY 0
    have h1 := hB _ hmem
    have hpos : 0 < ∏ k, (min 1 (tubeGap
        (tubePoint 0 (0 + (1 : ℝ) • diagTime b) k)))⁻¹ ^ q :=
      Finset.prod_pos fun k _ => pow_pos (inv_pos.2 (lt_min one_pos (hmem k trivial))) q
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) hpos
    linarith [norm_nonneg (u (tubePoint 0 (0 + (1 : ℝ) • diagTime b)))]
  have hE : IsBoundaryExtension u (taylorRemainderForm u (b * q)) := by
    refine ⟨fun Y hY φ hφ => (pairing_eq_taylorRemainderForm F hu hB hc hY hφ _).symm,
      fun φ hφ => continuousOn_taylorRemainderForm F hu hB hc hφ,
      fun Y hY φ hφ φ' hφ' z z' => taylorRemainderForm_smul_add F hu hB hc hY hφ hφ' z z'⟩
  have hspec : IsBoundaryExtension u (boundaryValue u) :=
    Classical.epsilon_spec (p := IsBoundaryExtension u) ⟨_, hE⟩
  refine ⟨fun Y hY φ hφ => integrable_shiftedIntegrand hu hB hc hY (F.integrable φ hφ),
    fun φ hφ j => F.integrable _ (F.iterate_totalTimeDeriv_mem hφ j),
    fun φ hφ a => F.translateBy_mem φ hφ a, hspec, ?_⟩
  intro Y hY φ hφ
  have hcont := hspec.2.1 φ hφ (Y, 0) ⟨hY, trivial⟩
  have hmap : Tendsto (fun s : ℝ => (Y + s • diagTime b, (0 : TestSpaces.PointTuple b))) (𝓝[>] 0)
      (𝓝[closedFutureConeTuples b ×ˢ Set.univ] (Y, 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : Continuous fun s : ℝ => (Y + s • diagTime b, (0 : TestSpaces.PointTuple b)) := by
        fun_prop
      have h2 := h1.tendsto 0
      simp only [zero_smul, add_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact ⟨mem_closed_of_mem_future (add_diagTime_mem_futureConeTuples hY hs), trivial⟩
  have hlim := hcont.tendsto.comp hmap
  simp only [translateBy_zero] at hlim
  refine le_of_tendsto hlim.norm ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hopen := add_diagTime_mem_futureConeTuples hY hs
  simp only [Function.comp, translateBy_zero]
  rw [hspec.1 _ hopen φ hφ, pairing_eq_taylorRemainderForm F hu hB hc hopen hφ (b * q)]
  exact norm_taylorRemainderForm_le F hB hc (mem_closed_of_mem_future hopen) hφ
end YangMills.Construction.TubeBoundary
