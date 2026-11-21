import YangMills.Construction.ClusterExpansionOfAStep.FormOfTheShares
import YangMills.Construction.FormsOnATorus.LimitFormIsASumOfShares
import YangMills.Construction.FormsOnATorus.SecondMomentAtLevelZero
import YangMills.Construction.FormsOnATorus.SecondMomentOfTheLimitForm
import YangMills.Construction.LawInAState.SumsOverTheBondsOfALattice
import YangMills.Construction.SummableBoundsOfTheFlow.OneNumberOfOneTotalProof
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped Quaternion
namespace YangMills.Construction.LimitForms
open TorusLumps BlockAverages
private def pairTerm (q : IntBond → IntBond → ℝ) (f g : IntBond → ℝ) (cc : IntBond × IntBond) : ℝ :=
  q cc.1 cc.2 * f cc.1 * g cc.2
private def axisIndicator (i : Fin 4) (c : IntBond) : ℝ := if c.2 = i then 1 else 0
private def axisCoord (i l : Fin 4) (c : IntBond) : ℝ := if c.2 = i then (c.1 l : ℝ) else 0
private def axisCoordSq (i l : Fin 4) (c : IntBond) : ℝ := if c.2 = i then (c.1 l : ℝ) ^ 2 else 0
private lemma hasSum_secondMoment_of_translateSum (q Q : IntBond → IntBond → ℝ) (i l : Fin 4)
    (hsum : ∀ b b' : IntBond, HasSum (fun u : Fin 4 → ℤ => q (b.1 + u, b.2) (b'.1 + u, b'.2)) (Q b b'))
    (h1 : HasSum (pairTerm q (axisIndicator i) (axisCoordSq i l)) 0)
    (h2 : HasSum (pairTerm q (axisCoordSq i l) (axisIndicator i)) 0)
    (h3 : HasSum (pairTerm q (axisCoord i l) (axisCoord i l)) 1) :
    HasSum (fun z : Fin 4 → ℤ => Q (0, i) (z, i) * (z l : ℝ) ^ 2) (-2) := by
  have hR := (h1.add h2).sub (h3.mul_left 2)
  let ι : (Fin 4 → ℤ) × (Fin 4 → ℤ) → IntBond × IntBond := fun x => ((x.1, i), (x.2, i))
  have hι : Function.Injective ι := by
    intro x y h
    have h1 := (Prod.ext_iff.1 (Prod.ext_iff.1 h).1).1
    have h2 := (Prod.ext_iff.1 (Prod.ext_iff.1 h).2).1
    exact Prod.ext h1 h2
  have hoff : ∀ cc ∉ Set.range ι, pairTerm q (axisIndicator i) (axisCoordSq i l) cc
      + pairTerm q (axisCoordSq i l) (axisIndicator i) cc -
      2 * pairTerm q (axisCoord i l) (axisCoord i l) cc = 0 := by
    rintro ⟨⟨u, a⟩, ⟨w, b⟩⟩ hcc
    have hab : ¬ (a = i ∧ b = i) := by
      rintro ⟨rfl, rfl⟩
      exact hcc ⟨(u, w), rfl⟩
    by_cases ha : a = i
    · have hb : b ≠ i := fun hb => hab ⟨ha, hb⟩
      simp [pairTerm, axisIndicator, axisCoord, axisCoordSq, hb]
    · simp [pairTerm, axisIndicator, axisCoord, axisCoordSq, ha]
  have hR2 := (hι.hasSum_iff hoff).2 hR
  let e : (Fin 4 → ℤ) × (Fin 4 → ℤ) ≃ (Fin 4 → ℤ) × (Fin 4 → ℤ) :=
    ⟨fun x => (x.2, x.1 + x.2), fun y => (y.2 - y.1, y.1), fun x => by simp, fun y => by simp⟩
  have hR3 := e.hasSum_iff.2 hR2
  have hfib : ∀ z : Fin 4 → ℤ, HasSum (fun u => ((fun cc => pairTerm q (axisIndicator i) (axisCoordSq i l) cc
      + pairTerm q (axisCoordSq i l) (axisIndicator i) cc -
      2 * pairTerm q (axisCoord i l) (axisCoord i l) cc) ∘ ι ∘ e) (z, u)) (Q (0, i) (z, i) * (z l : ℝ) ^ 2) := by
    intro z
    have h := (hsum (0, i) (z, i)).mul_right ((z l : ℝ) ^ 2)
    simp only [zero_add] at h
    refine (congrArg (fun f : (Fin 4 → ℤ) → ℝ => HasSum f _) ?_).mpr h
    funext u
    simp only [Function.comp, ι, e, Equiv.coe_fn_mk, pairTerm, axisIndicator, axisCoord, axisCoordSq, if_true,
      Pi.add_apply]
    push_cast
    ring
  have h4 := hR3.prod_fiberwise hfib
  have e4 : (0 : ℝ) + 0 - 2 * 1 = -2 := by norm_num
  rwa [e4] at h4
private lemma smul_quaternionI_sub (s t : ℝ) : s • quaternionI - t • quaternionI = (s - t) • quaternionI := by
  apply Subtype.ext
  show s • ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) - t • ((quaternionI : imaginaryQuaternions) : ℍ[ℝ])
    = (s - t) • ((quaternionI : imaginaryQuaternions) : ℍ[ℝ])
  rw [sub_smul]
private lemma neg_smul_quaternionI (s : ℝ) : -(s • quaternionI) = (-s) • quaternionI := by
  apply Subtype.ext
  show -(s • ((quaternionI : imaginaryQuaternions) : ℍ[ℝ])) = (-s) • ((quaternionI : imaginaryQuaternions) : ℍ[ℝ])
  rw [neg_smul]
private lemma norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
private lemma inner_smul_quaternionI (s t : ℝ) :
    inner ℝ (((s • quaternionI : imaginaryQuaternions)) : ℍ[ℝ])
      (((t • quaternionI : imaginaryQuaternions)) : ℍ[ℝ]) = s * t := by
  have h3 : ‖((quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by simpa using norm_quaternionI
  have h : inner ℝ ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
    rw [real_inner_self_eq_norm_sq, h3]; norm_num
  simp only [Submodule.coe_smul, real_inner_smul_left, real_inner_smul_right, h]
  ring
private lemma abs_coord_le_offsetSupNorm (z : Fin 4 → ℤ) (l : Fin 4) : |(z l : ℝ)| ≤ offsetSupNorm z := by apply _root_.YangMills.Construction.LatticeSums.abs_le_offsetSupNorm <;> assumption
private def planePotentialReal (i l : Fin 4) (c : IntBond) : ℝ :=
  (1 / 2) * (if c.2 = i then (c.1 l : ℝ) else if c.2 = l then -(c.1 i : ℝ) else 0)
private def halfProductGradient (i l : Fin 4) (c : IntBond) : ℝ :=
  (1 / 2) * (if c.2 = i then (c.1 l : ℝ) else if c.2 = l then (c.1 i : ℝ) else 0)
private def realGradient (f : (Fin 4 → ℤ) → ℝ) (c : IntBond) : ℝ := f (c.1 + Pi.single c.2 1) - f c.1
private lemma realGradient_coord (i : Fin 4) : realGradient (fun z => (z i : ℝ)) = axisIndicator i := by
  funext ⟨x, j⟩
  by_cases h : j = i
  · subst h; simp [realGradient, axisIndicator]
  · simp [realGradient, axisIndicator, h, Ne.symm h]
private lemma realGradient_halfProduct (i l : Fin 4) (hil : i ≠ l) :
    realGradient (fun z => 1 / 2 * ((z i : ℝ) * (z l : ℝ))) = halfProductGradient i l := by
  funext ⟨x, j⟩
  by_cases h : j = i
  · subst h
    simp [realGradient, halfProductGradient, Ne.symm hil, hil]
    ring
  · by_cases h2 : j = l
    · subst h2
      simp [realGradient, halfProductGradient, h, Ne.symm h]
      ring
    · simp [realGradient, halfProductGradient, h, h2, Ne.symm h, Ne.symm h2]
private lemma axisCoord_eq_add (i l : Fin 4) (hil : i ≠ l) (c : IntBond) :
    axisCoord i l c = planePotentialReal i l c + halfProductGradient i l c := by
  rcases c with ⟨x, j⟩
  by_cases h : j = i
  · subst h; simp [axisCoord, planePotentialReal, halfProductGradient]; ring
  · by_cases h2 : j = l
    · subst h2; simp [axisCoord, planePotentialReal, halfProductGradient, h]
    · simp [axisCoord, planePotentialReal, halfProductGradient, h, h2]
private lemma linearPotential_planeCurvature (i l : Fin 4) (hil : i ≠ l) (c : IntBond) :
    linearPotential (planeCurvature quaternionI l i) c = planePotentialReal i l c • quaternionI := by
  rcases c with ⟨x, j⟩
  have hA : ∀ ν, planeCurvature quaternionI l i ν j = if j = i then (if ν = l then quaternionI else 0)
      else if j = l then (if ν = i then -quaternionI else 0) else 0 := by
    intro ν
    unfold planeCurvature
    by_cases h1 : j = i
    · subst h1
      simp [hil]
    · by_cases h2 : j = l
      · subst h2
        simp [h1]
      · simp [h1, h2]
  unfold linearPotential planePotentialReal
  simp only [hA]
  by_cases h1 : j = i
  · subst h1
    simp [smul_smul]
  · by_cases h2 : j = l
    · subst h2
      simp [h1, smul_smul]
      exact neg_smul_quaternionI _
    · simp [h1, h2]
private lemma curvaturePairing_planeCurvature_self (i l : Fin 4) (hil : i ≠ l) :
    curvaturePairing (planeCurvature quaternionI l i) (planeCurvature quaternionI l i) = 1 := by
  have h3 : ‖((quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by simpa using norm_quaternionI
  have h : inner ℝ ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
    rw [real_inner_self_eq_norm_sq, h3]; norm_num
  unfold curvaturePairing planeCurvature
  fin_cases i <;> fin_cases l <;> first
    | exact absurd rfl hil
    | (simp [Fin.sum_univ_four]; exact Or.inl h3)
private lemma planeCurvature_antisymm (i l : Fin 4) (hil : i ≠ l) (μ ν : Fin 4) :
    planeCurvature quaternionI l i μ ν = - planeCurvature quaternionI l i ν μ := by
  unfold planeCurvature
  by_cases h1 : μ = l ∧ ν = i
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hil, Ne.symm hil]
  · by_cases h2 : μ = i ∧ ν = l
    · obtain ⟨rfl, rfl⟩ := h2
      simp [h1]
    · have h3 : ¬ (ν = l ∧ μ = i) := fun h => h2 ⟨h.2, h.1⟩
      have h4 : ¬ (ν = i ∧ μ = l) := fun h => h1 ⟨h.2, h.1⟩
      simp [h1, h2, h3, h4]
private lemma secondMoment_succ (hS : limitFormTranslateSumStatement)
    (hF : ShareFamilies.LevelSharesHaveUnitCurvatureForm)
    (hC : ShareFamilies.LevelSharesFormCurvatureFamily) (hO : TorusLumps.SecondOrderAtAbelianFields)
    (hH : FlatHessian.HessianAtTrivialFieldStatement) (T : RenormalizationStepParameters.ParameterAssignment) (hT : T.Admissible)
    (c C : ℝ) (t : ℕ)
    (Q : IntBond → IntBond → ℝ) (hc : 0 < c) (hQ : IsLimitForm T.coupling T.coercivity c C T.side (t + 1) Q)
    (i l : Fin 4) (hil : i ≠ l) :
    HasSum (fun z : Fin 4 → ℤ => Q (0, i) (z, i) * (z l : ℝ) ^ 2) (-2) := by
  obtain ⟨q, hq, hsum⟩ := hS T hT c C (t + 1) Q hc hQ
  set ℓ := T.stepParameters T.floorMin with hℓ
  have hfit : ℓ.Admissible := hT.fits _ le_rfl
  obtain ⟨hfam, -, -⟩ := hC T hT T.floorMin le_rfl t
  set h := ShareFamilies.levelShareFamily T.coupling T.side (t + 1) with hh
  obtain ⟨Slim, -, Ssym, -, -, Sgrad, -, -⟩ := hO ℓ hfit _ h hfam
  have hform : HasCurvatureForm h 1 := hF T hT t
  have hbil : ∀ (b b' : IntBond) (s u : ℝ),
      secondDerivLimit h b b' (s • quaternionI) (u • quaternionI) = s * u * q b b' := by
    intro b b' s u
    refine tendsto_nhds_unique (Slim b b' _ _) (((hq b b').const_mul (s * u)).congr' ?_)
    filter_upwards [eventually_ge_atTop (max 1 ℓ.n₀)] with n hn
    have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
    have hn2 : ℓ.n₀ ≤ n := (le_max_right _ _).trans hn
    haveI : NeZero n := ⟨by omega⟩
    have := (hH ℓ hfit _ h hfam n hn2 0 (bondFrom 0 b) (bondFrom 0 b')).1 (s • quaternionI) (u • quaternionI)
    rw [this, inner_smul_quaternionI]
    rfl
  have hsym : ∀ b b', q b b' = q b' b := by
    intro b b'
    have h1 := Ssym b b' quaternionI quaternionI
    have h2 := hbil b b' 1 1
    have h3 := hbil b' b 1 1
    rw [one_smul] at h2 h3
    rw [h2, h3] at h1
    simpa using h1
  have hgrad : ∀ (f : (Fin 4 → ℤ) → ℝ) (g : IntBond → ℝ),
      (∃ (K : ℝ) (p : ℕ), ∀ z, |f z| ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p) →
      (∃ (K : ℝ) (p : ℕ), ∀ c, |g c| ≤ K * (1 + (offsetSupNorm c.1 : ℝ)) ^ p) →
      HasSum (pairTerm q (realGradient f) g) 0 := by
    intro f g ⟨K, p, hf⟩ ⟨K', p', hg⟩
    have := Sgrad (fun z => f z • quaternionI) (fun c => g c • quaternionI)
      ⟨K, p, fun z => by rw [norm_smul, norm_quaternionI, mul_one]; exact hf z⟩
      ⟨K', p', fun c => by rw [norm_smul, norm_quaternionI, mul_one]; exact hg c⟩
    refine (congrArg (fun w : IntBond × IntBond → ℝ => HasSum w _) ?_).mpr this
    funext cc
    have e : discreteGradient (fun z => f z • quaternionI) cc.1 = realGradient f cc.1 • quaternionI := by
      unfold discreteGradient realGradient
      exact smul_quaternionI_sub _ _
    rw [e, hbil]
    simp only [pairTerm]
    ring
  have hswap : ∀ (f g : IntBond → ℝ) (v : ℝ), HasSum (pairTerm q f g) v → HasSum (pairTerm q g f) v := by
    intro f g v hv
    refine (congrArg (fun w : IntBond × IntBond → ℝ => HasSum w _) ?_).mpr
      ((Equiv.prodComm IntBond IntBond).hasSum_iff.2 hv)
    funext cc
    simp only [Function.comp, Equiv.prodComm_apply, Prod.swap, pairTerm]
    rw [hsym]
    ring
  have pz : ∃ (K : ℝ) (p : ℕ), ∀ z : Fin 4 → ℤ, |(z i : ℝ)| ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p :=
    ⟨1, 1, fun z => by have := abs_coord_le_offsetSupNorm z i; simp only [pow_one, one_mul]; linarith⟩
  have pzz : ∃ (K : ℝ) (p : ℕ), ∀ z : Fin 4 → ℤ,
      |1 / 2 * ((z i : ℝ) * (z l : ℝ))| ≤ K * (1 + (offsetSupNorm z : ℝ)) ^ p := by
    refine ⟨1, 2, fun z => ?_⟩
    have h1 := abs_coord_le_offsetSupNorm z i
    have h2 := abs_coord_le_offsetSupNorm z l
    have h0 : (0 : ℝ) ≤ offsetSupNorm z := by positivity
    rw [abs_mul, abs_mul]
    have h3 : |(z i : ℝ)| * |(z l : ℝ)| ≤ (offsetSupNorm z : ℝ) * offsetSupNorm z :=
      mul_le_mul h1 h2 (abs_nonneg _) h0
    have h4 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [h4]
    nlinarith [abs_nonneg (z i : ℝ), abs_nonneg (z l : ℝ), mul_nonneg (abs_nonneg (z i : ℝ)) (abs_nonneg (z l : ℝ))]
  have px2 : ∃ (K : ℝ) (p : ℕ), ∀ c : IntBond, |axisCoordSq i l c| ≤ K * (1 + (offsetSupNorm c.1 : ℝ)) ^ p := by
    refine ⟨1, 2, fun c => ?_⟩
    have h1 := abs_coord_le_offsetSupNorm c.1 l
    have h0 : (0 : ℝ) ≤ offsetSupNorm c.1 := by positivity
    unfold axisCoordSq
    split_ifs
    · rw [abs_pow]
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith
    · simp only [abs_zero, one_mul]; positivity
  have pfB : ∃ (K : ℝ) (p : ℕ), ∀ c : IntBond,
      |planePotentialReal i l c| ≤ K * (1 + (offsetSupNorm c.1 : ℝ)) ^ p := by
    refine ⟨1, 1, fun c => ?_⟩
    have h1 := abs_coord_le_offsetSupNorm c.1 l
    have h2 := abs_coord_le_offsetSupNorm c.1 i
    have h0 : (0 : ℝ) ≤ offsetSupNorm c.1 := by positivity
    unfold planePotentialReal
    rw [abs_mul]
    have h4 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [h4, pow_one, one_mul]
    split_ifs
    · linarith [abs_nonneg (c.1 l : ℝ)]
    · rw [abs_neg]; linarith [abs_nonneg (c.1 i : ℝ)]
    · simp; linarith
  have pfG : ∃ (K : ℝ) (p : ℕ), ∀ c : IntBond,
      |halfProductGradient i l c| ≤ K * (1 + (offsetSupNorm c.1 : ℝ)) ^ p := by
    refine ⟨1, 1, fun c => ?_⟩
    have h1 := abs_coord_le_offsetSupNorm c.1 l
    have h2 := abs_coord_le_offsetSupNorm c.1 i
    have h0 : (0 : ℝ) ≤ offsetSupNorm c.1 := by positivity
    unfold halfProductGradient
    rw [abs_mul]
    have h4 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [h4, pow_one, one_mul]
    split_ifs
    · linarith [abs_nonneg (c.1 l : ℝ)]
    · linarith [abs_nonneg (c.1 i : ℝ)]
    · simp; linarith
  have h1 : HasSum (pairTerm q (axisIndicator i) (axisCoordSq i l)) 0 := by
    have := hgrad (fun z => (z i : ℝ)) (axisCoordSq i l) pz px2
    rwa [realGradient_coord] at this
  have h2 := hswap _ _ _ h1
  have hBB : HasSum (pairTerm q (planePotentialReal i l) (planePotentialReal i l)) 1 := by
    have := hform.2 (planeCurvature quaternionI l i) (planeCurvature quaternionI l i)
      (planeCurvature_antisymm i l hil) (planeCurvature_antisymm i l hil)
    rw [curvaturePairing_planeCurvature_self i l hil, one_mul] at this
    refine (congrArg (fun w : IntBond × IntBond → ℝ => HasSum w _) ?_).mpr this
    funext cc
    simp only [limitFormTerm, linearPotential_planeCurvature i l hil, hbil, pairTerm]
    ring
  have hGB : HasSum (pairTerm q (halfProductGradient i l) (planePotentialReal i l)) 0 := by
    have := hgrad (fun z => 1 / 2 * ((z i : ℝ) * (z l : ℝ))) (planePotentialReal i l) pzz pfB
    rwa [realGradient_halfProduct i l hil] at this
  have hBG := hswap _ _ _ hGB
  have hGG : HasSum (pairTerm q (halfProductGradient i l) (halfProductGradient i l)) 0 := by
    have := hgrad (fun z => 1 / 2 * ((z i : ℝ) * (z l : ℝ))) (halfProductGradient i l) pzz pfG
    rwa [realGradient_halfProduct i l hil] at this
  have h3 : HasSum (pairTerm q (axisCoord i l) (axisCoord i l)) 1 := by
    have := ((hBB.add hGB).add hBG).add hGG
    simp only [add_zero] at this
    refine (congrArg (fun w : IntBond × IntBond → ℝ => HasSum w _) ?_).mpr this
    funext cc
    simp only [pairTerm, axisCoord_eq_add i l hil]
    ring
  exact hasSum_secondMoment_of_translateSum q Q i l hsum h1 h2 h3
theorem limitFormSecondMomentStatement_holds (hS : limitFormTranslateSumStatement)
    (h0 : wilsonLimitFormSecondMomentStatement)
    (hF : ShareFamilies.LevelSharesHaveUnitCurvatureForm) (hC : ShareFamilies.LevelSharesFormCurvatureFamily)
    (hO : TorusLumps.SecondOrderAtAbelianFields) (hH : FlatHessian.HessianAtTrivialFieldStatement) :
    limitFormSecondMomentStatement := by
  intro T hT c C k Q hc hQ i l hil
  cases k with
  | zero => exact h0 _ _ _ _ _ _ hc hQ i l hil
  | succ t => exact secondMoment_succ hS hF hC hO hH T hT c C t Q hc hQ i l hil
end YangMills.Construction.LimitForms
end
