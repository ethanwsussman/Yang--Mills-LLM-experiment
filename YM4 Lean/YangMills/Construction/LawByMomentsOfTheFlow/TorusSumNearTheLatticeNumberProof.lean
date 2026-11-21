import YangMills.Construction.LawByMomentsOfTheFlow.KernelOfTheCurvature
import YangMills.Construction.LawByMomentsOfTheFlow.TorusSumNearTheLatticeNumber
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses LevelTestFunctions CyclicFormula TestFunctions
section Translation
private def plaquetteTranslate (z : Fin 4 → ℤ) : IntPlaquette ≃ IntPlaquette where
  toFun p := (p.1 + z, p.2)
  invFun p := (p.1 - z, p.2)
  left_inv p := by simp
  right_inv p := by simp
private theorem plaquetteTranslate_apply (z : Fin 4 → ℤ) (p : IntPlaquette) :
    plaquetteTranslate z p = (p.1 + z, p.2) := rfl
private theorem memℓp_translate (z : Fin 4 → ℤ) (v : PlaquetteL2) :
    Memℓp (fun p => v (plaquetteTranslate z p)) 2 := by
  have h := (lp.memℓp v)
  rw [memℓp_gen_iff (by norm_num)] at h ⊢
  exact (plaquetteTranslate z).summable_iff.mpr h
private def translateL2 (z : Fin 4 → ℤ) : PlaquetteL2 →ₗ[ℝ] PlaquetteL2 where
  toFun v := ⟨fun p => v (plaquetteTranslate z p), memℓp_translate z v⟩
  map_add' u v := by ext p; rfl
  map_smul' c v := by ext p; rfl
private theorem translateL2_inner (z : Fin 4 → ℤ) (u v : PlaquetteL2) :
    inner ℝ (translateL2 z u) (translateL2 z v) = inner ℝ u v := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact (plaquetteTranslate z).tsum_eq fun p => inner ℝ (u p) (v p)
private def translateIsometry (z : Fin 4 → ℤ) : PlaquetteL2 →ₗᵢ[ℝ] PlaquetteL2 :=
  (translateL2 z).isometryOfInner (translateL2_inner z)
private theorem translateIsometry_apply (z : Fin 4 → ℤ) (v : PlaquetteL2) (p : IntPlaquette) :
    translateIsometry z v p = v (plaquetteTranslate z p) := rfl
private theorem translateIsometry_neg (z : Fin 4 → ℤ) (v : PlaquetteL2) :
    translateIsometry z (translateIsometry (-z) v) = v := by
  ext p
  simp [translateIsometry_apply, plaquetteTranslate_apply]
private def bondTranslate (z : Fin 4 → ℤ) : IntBond ≃ IntBond where
  toFun b := (b.1 - z, b.2)
  invFun b := (b.1 + z, b.2)
  left_inv b := by simp
  right_inv b := by simp
private theorem intCurl_translate (z : Fin 4 → ℤ) (A : IntBond →₀ ℝ) (p : IntPlaquette) :
    intCurl (A.equivMapDomain (bondTranslate z)) p = intCurl A (plaquetteTranslate z p) := by
  simp only [intCurl, Finsupp.equivMapDomain_apply, plaquetteTranslate_apply, bondTranslate]
  simp only [Equiv.coe_fn_symm_mk, add_right_comm]
private theorem map_span_curls_le (z : Fin 4 → ℤ) :
    (Submodule.span ℝ {v : PlaquetteL2 | ∃ A : IntBond →₀ ℝ, ∀ p, v p = intCurl A p}).map
        (translateIsometry z).toLinearMap ≤
      Submodule.span ℝ {v : PlaquetteL2 | ∃ A : IntBond →₀ ℝ, ∀ p, v p = intCurl A p} := by
  rw [Submodule.map_span_le]
  rintro v ⟨A, hA⟩
  refine Submodule.subset_span ⟨A.equivMapDomain (bondTranslate z), fun p => ?_⟩
  simp only [LinearIsometry.coe_toLinearMap]
  rw [translateIsometry_apply, hA, intCurl_translate]
private theorem translateIsometry_mem_intCurvatures (z : Fin 4 → ℤ) {v : PlaquetteL2}
    (hv : v ∈ intCurvatures) : translateIsometry z v ∈ intCurvatures := by
  have hc : Continuous (translateIsometry z) := (translateIsometry z).continuous
  have hv' : v ∈ closure (Submodule.span ℝ {v : PlaquetteL2 | ∃ A : IntBond →₀ ℝ, ∀ p, v p = intCurl A p} :
      Set PlaquetteL2) := hv
  exact map_mem_closure hc hv' (fun x hx => map_span_curls_le z ⟨x, hx, rfl⟩)
open Classical in
private theorem translateIsometry_single (z : Fin 4 → ℤ) (P : IntPlaquette) :
    translateIsometry z (lp.single 2 (plaquetteTranslate z P) (1 : ℝ) : PlaquetteL2) =
      (lp.single 2 P (1 : ℝ) : PlaquetteL2) := by
  ext p
  rw [translateIsometry_apply]
  by_cases h : p = P
  · subst h
    simp [lp.single_apply]
  · have h' : plaquetteTranslate z p ≠ plaquetteTranslate z P := fun e => h ((plaquetteTranslate z).injective e)
    rw [lp.single_apply_ne _ _ _ h, lp.single_apply_ne _ _ _ h']
private theorem intCurvatureProjection_translate (z : Fin 4 → ℤ) (P P' : IntPlaquette) :
    intCurvatureProjection (P.1 + z, P.2) (P'.1 + z, P'.2) = intCurvatureProjection P P' := by
  classical
  have hproj : ∀ x : PlaquetteL2, intCurvatures.starProjection (translateIsometry z x) =
      translateIsometry z (intCurvatures.starProjection x) := fun x => by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (translateIsometry_mem_intCurvatures z (Submodule.starProjection_apply_mem _ _)) fun w hw => ?_
    have hw' := translateIsometry_mem_intCurvatures (-z) hw
    have e : w = translateIsometry z (translateIsometry (-z) w) := (translateIsometry_neg z w).symm
    rw [e, ← map_sub, LinearIsometry.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero x _ hw'
  have e1 : intCurvatureProjection (P.1 + z, P.2) (P'.1 + z, P'.2) =
      inner ℝ (lp.single 2 (plaquetteTranslate z P) (1 : ℝ) : PlaquetteL2)
        (intCurvatures.starProjection (lp.single 2 (plaquetteTranslate z P') (1 : ℝ))) := rfl
  have e2 : intCurvatureProjection P P' = inner ℝ (lp.single 2 P (1 : ℝ) : PlaquetteL2)
      (intCurvatures.starProjection (lp.single 2 P' (1 : ℝ))) := rfl
  rw [e1, e2, ← (translateIsometry z).inner_map_map, ← hproj, translateIsometry_single, translateIsometry_single]
end Translation
section Lifting
variable {m : ℕ} [NeZero m]
private def liftCoord (z : Fin 4 → ℤ) (q : TorusPlaquette m) (a : Fin 4) : ℤ :=
  ((q.1 a).val : ℤ) - z a - (m : ℤ) * round ((barycenterCoord q a - z a) / (m : ℝ))
private def liftPlaquette (z : Fin 4 → ℤ) (p : OrientedPlaquette m) : IntPlaquette :=
  (liftCoord z p.1, ⟨p.1.2, p.2⟩)
private def projectPlaquette (z : Fin 4 → ℤ) (P : IntPlaquette) : OrientedPlaquette m :=
  ⟨(fun a => ((P.1 a + z a : ℤ) : ZMod m), P.2.1), P.2.2⟩
omit [NeZero m] in
private theorem intBarycenter_liftPlaquette (z : Fin 4 → ℤ) (p : OrientedPlaquette m) (a : Fin 4) :
    intBarycenter (liftPlaquette z p) a =
      barycenterCoord p.1 a - z a - m * round ((barycenterCoord p.1 a - z a) / (m : ℝ)) := by
  have key : ∀ v z' m' r o₁ o₂ : ℝ, v - z' - m' * r + o₁ + o₂ = v + o₁ + o₂ - z' - m' * r :=
    fun _ _ _ _ _ _ => by ring
  simp only [intBarycenter, barycenterCoord, liftPlaquette, liftCoord]
  push_cast
  exact key _ _ _ _ _ _
private theorem projectPlaquette_liftPlaquette (z : Fin 4 → ℤ) (p : OrientedPlaquette m) :
    projectPlaquette z (liftPlaquette z p) = p := by
  refine Subtype.ext (Prod.ext (funext fun a => ?_) rfl)
  simp only [projectPlaquette, liftPlaquette, liftCoord]
  simp
private theorem liftPlaquette_projectPlaquette (z : Fin 4 → ℤ) (P : IntPlaquette)
    (h : ∀ a, |intBarycenter P a| < (m : ℝ) / 2) :
    liftPlaquette z (projectPlaquette z P : OrientedPlaquette m) = P := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine Prod.ext (funext fun a => ?_) (Subtype.ext rfl)
  simp only [liftPlaquette, liftCoord, projectPlaquette]
  set val : ℤ := ((((P.1 a + z a : ℤ) : ZMod m)).val : ℤ) with hval
  have hv : val = (P.1 a + z a) - m * ((P.1 a + z a) / m) := by
    rw [hval, ZMod.val_intCast, Int.emod_def]
  set j : ℤ := (P.1 a + z a) / m with hj
  have hnat : (((((P.1 a + z a : ℤ) : ZMod m)).val : ℕ) : ℝ) = (P.1 a : ℝ) + z a - m * j := by
    have h1 : (val : ℝ) = (((((P.1 a + z a : ℤ) : ZMod m)).val : ℕ) : ℝ) := by simp [hval]
    rw [← h1, hv]
    push_cast
    ring
  have key : ∀ v z' m' j' o₁ o₂ : ℝ, v + z' - m' * j' + o₁ + o₂ - z' = v + o₁ + o₂ - m' * j' :=
    fun _ _ _ _ _ _ => by ring
  have hb : barycenterCoord (((fun a => ((P.1 a + z a : ℤ) : ZMod m)), P.2.1) : TorusPlaquette m) a - z a =
      intBarycenter P a - m * j := by
    simp only [barycenterCoord, intBarycenter]
    rw [hnat]
    exact key _ _ _ _ _ _
  have ht : (barycenterCoord (((fun a => ((P.1 a + z a : ℤ) : ZMod m)), P.2.1) : TorusPlaquette m) a - z a) /
      (m : ℝ) = intBarycenter P a / m - (j : ℝ) := by
    rw [hb]; field_simp
  have h0 : round (intBarycenter P a / (m : ℝ)) = 0 := by
    obtain ⟨l, u⟩ := abs_lt.mp (h a)
    refine round_eq_zero_iff.mpr ⟨?_, ?_⟩
    · rw [le_div_iff₀ hm]; linarith
    · rw [div_lt_iff₀ hm]; linarith
  rw [ht, round_sub_intCast, h0, hv]
  ring
end Lifting
private theorem abs_torusSum_sub_latticeSum_le {k m : ℕ} [NeZero k] [NeZero m]
    (f : Fin k → TorusPlaquette m → ℝ) (w : Fin k → IntPlaquette → ℝ) (z : Fin 4 → ℤ) (B : Finset IntPlaquette)
    (hfw : ∀ i (p : OrientedPlaquette m), f i p.1 = w i (liftPlaquette z p))
    (hbox : ∀ i Q, w i Q ≠ 0 → Q ∈ B)
    (hlift : ∀ i Q, w i Q ≠ 0 → liftPlaquette z (projectPlaquette z Q : OrientedPlaquette m) = Q)
    (hw1 : ∀ i Q, |w i Q| ≤ 1) (σ : Equiv.Perm (Fin k)) {X : ℝ} (hX : 0 ≤ X)
    (hterm : ∀ Q : Fin k → IntPlaquette, (∀ i, w i (Q i) ≠ 0) →
      |∏ c : Fin k, torusCurvatureProjection (projectPlaquette z (Q (σ c)) : OrientedPlaquette m)
          (projectPlaquette z (Q (σ (c + 1)))) -
        ∏ c : Fin k, intCurvatureProjection (Q (σ c)) (Q (σ (c + 1)))| ≤ X) :
    |∑ p : Fin k → OrientedPlaquette m, (∏ i, f i (p i).1) *
        ∏ c : Fin k, torusCurvatureProjection (p (σ c)) (p (σ (c + 1))) -
      ∑ Q ∈ Fintype.piFinset (fun _ : Fin k => B),
        (∏ i, w i (Q i)) * ∏ c : Fin k, intCurvatureProjection (Q (σ c)) (Q (σ (c + 1)))| ≤
      (B.card : ℝ) ^ k * X := by
  classical
  set S := Fintype.piFinset (fun i : Fin k => B.filter fun Q => w i Q ≠ 0) with hS
  have hmem : ∀ Q ∈ S, ∀ i, w i (Q i) ≠ 0 := fun Q hQ i =>
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hQ i)).2
  have h1 : ∑ Q ∈ Fintype.piFinset (fun _ : Fin k => B),
      (∏ i, w i (Q i)) * ∏ c : Fin k, intCurvatureProjection (Q (σ c)) (Q (σ (c + 1))) =
      ∑ Q ∈ S, (∏ i, w i (Q i)) * ∏ c : Fin k, intCurvatureProjection (Q (σ c)) (Q (σ (c + 1))) := by
    symm
    refine Finset.sum_subset (fun Q hQ => Fintype.mem_piFinset.mpr fun i =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hQ i)).1) fun Q hQ hn => ?_
    have : ∃ i, w i (Q i) = 0 := by
      by_contra hc
      push Not at hc
      exact hn (Fintype.mem_piFinset.mpr fun i => Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hQ i, hc i⟩)
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
  have h2 : ∑ Q ∈ S, (∏ i, f i (projectPlaquette z (Q i) : OrientedPlaquette m).1) *
      ∏ c : Fin k, torusCurvatureProjection (projectPlaquette z (Q (σ c)) : OrientedPlaquette m)
        (projectPlaquette z (Q (σ (c + 1)))) =
      ∑ p : Fin k → OrientedPlaquette m, (∏ i, f i (p i).1) *
        ∏ c : Fin k, torusCurvatureProjection (p (σ c)) (p (σ (c + 1))) := by
    refine Finset.sum_bij_ne_zero (fun Q _ _ i => projectPlaquette z (Q i)) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro Q hQ _ Q' hQ' _ he
      funext i
      have := congrFun he i
      rw [← hlift i _ (hmem Q hQ i), ← hlift i _ (hmem Q' hQ' i), this]
    · intro p _ hp
      have hne : ∀ i, f i (p i).1 ≠ 0 := fun i =>
        Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hp) i (Finset.mem_univ _)
      have hne' : ∀ i, w i (liftPlaquette z (p i)) ≠ 0 := fun i => by rw [← hfw]; exact hne i
      refine ⟨fun i => liftPlaquette z (p i), ?_, ?_, ?_⟩
      · exact Fintype.mem_piFinset.mpr fun i => Finset.mem_filter.mpr ⟨hbox i _ (hne' i), hne' i⟩
      · simpa only [projectPlaquette_liftPlaquette] using hp
      · funext i; exact projectPlaquette_liftPlaquette z (p i)
    · intro Q _ _; rfl
  rw [h1, ← h2, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h3 : ∀ Q ∈ S, |(∏ i, f i (projectPlaquette z (Q i) : OrientedPlaquette m).1) *
      (∏ c : Fin k, torusCurvatureProjection (projectPlaquette z (Q (σ c)) : OrientedPlaquette m)
        (projectPlaquette z (Q (σ (c + 1))))) -
      (∏ i, w i (Q i)) * ∏ c : Fin k, intCurvatureProjection (Q (σ c)) (Q (σ (c + 1)))| ≤ X := by
    intro Q hQ
    have hf : ∀ i, f i (projectPlaquette z (Q i) : OrientedPlaquette m).1 = w i (Q i) := fun i => by
      rw [hfw, hlift i _ (hmem Q hQ i)]
    simp only [hf]
    rw [← mul_sub, abs_mul]
    have h4 : |∏ i, w i (Q i)| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hw1 i _)
    calc _ ≤ 1 * X := mul_le_mul h4 (hterm Q (hmem Q hQ)) (abs_nonneg _) zero_le_one
      _ = X := one_mul _
  have hc : (S.card : ℝ) ≤ (B.card : ℝ) ^ k := by
    have h5 : S.card ≤ B.card ^ k := by
      rw [hS, Fintype.card_piFinset]
      calc ∏ i : Fin k, (B.filter fun Q => w i Q ≠ 0).card ≤ ∏ _i : Fin k, B.card :=
            Finset.prod_le_prod' fun i _ => Finset.card_filter_le _ _
        _ = B.card ^ k := by simp
    exact_mod_cast h5
  calc _ ≤ ∑ _Q ∈ S, X := Finset.sum_le_sum h3
    _ = (S.card : ℝ) * X := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hX
private theorem abs_inv_pow_mul_le {Kv e d w C : ℝ} (he : 0 < e) (hd : 0 < d) (hC : 0 ≤ C)
    (hsep : d ≤ e * w) (hone : |Kv| ≤ 1) (hfar : 2 ≤ w → |Kv| ≤ C * (w ^ 4)⁻¹) :
    |(e⁻¹) ^ 4 * Kv| ≤ (16 + C) * (d⁻¹) ^ 4 := by
  have hw0 : 0 < w := by
    by_contra h0
    have : w ≤ 0 := not_lt.mp h0
    nlinarith
  have hinv : e⁻¹ ≤ w * d⁻¹ := by
    rw [inv_le_comm₀ he (by positivity), mul_inv, inv_inv]
    calc w⁻¹ * d ≤ w⁻¹ * (e * w) := mul_le_mul_of_nonneg_left hsep (by positivity)
      _ = e := by field_simp
  have hp : (e⁻¹) ^ 4 ≤ (w * d⁻¹) ^ 4 := pow_le_pow_left₀ (by positivity) hinv 4
  have hd4 : 0 ≤ (d⁻¹) ^ 4 := by positivity
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e⁻¹) ^ 4)]
  by_cases h2 : 2 ≤ w
  · calc (e⁻¹) ^ 4 * |Kv| ≤ (w * d⁻¹) ^ 4 * (C * (w ^ 4)⁻¹) :=
          mul_le_mul hp (hfar h2) (abs_nonneg _) (by positivity)
      _ = C * (d⁻¹) ^ 4 := by field_simp
      _ ≤ (16 + C) * (d⁻¹) ^ 4 := mul_le_mul_of_nonneg_right (by linarith) hd4
  · have hw2 : w ≤ 2 := (not_le.mp h2).le
    calc (e⁻¹) ^ 4 * |Kv| ≤ (w * d⁻¹) ^ 4 * 1 := mul_le_mul hp hone (abs_nonneg _) (by positivity)
      _ ≤ (2 * d⁻¹) ^ 4 * 1 := by
          rw [mul_one, mul_one]
          exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hw2 (by positivity)) 4
      _ = 16 * (d⁻¹) ^ 4 := by ring
      _ ≤ (16 + C) * (d⁻¹) ^ 4 := mul_le_mul_of_nonneg_right (by linarith) hd4
private structure TorusProjectionBounds (m : ℕ) [NeZero m] (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  abs_le_one : ∀ p p' : OrientedPlaquette m, |torusCurvatureProjection p p'| ≤ 1
  approx : ∀ (p p' : OrientedPlaquette m) (P P' : IntPlaquette), IsLift P p → IsLift P' p' →
    (∀ a, |intBarycenter P a - intBarycenter P' a| ≤ (m : ℝ) / 4) →
    |torusCurvatureProjection p p' - intCurvatureProjection P P'| ≤ C * ((m : ℝ) ^ 4)⁻¹ ∧
    (2 ≤ ‖intBarycenter P - intBarycenter P'‖ →
      |torusCurvatureProjection p p'| ≤ C * (‖intBarycenter P - intBarycenter P'‖ ^ 4)⁻¹)
private theorem projection_link_bounds {m : ℕ} [NeZero m] {C e d : ℝ} (hK : TorusProjectionBounds m C)
    (he : 0 < e) (hd : 0 < d) (z : Fin 4 → ℤ) (P P' : IntPlaquette)
    (hsep : d ≤ e * ‖intBarycenter P - intBarycenter P'‖)
    (hsup : ∀ a, |intBarycenter P a - intBarycenter P' a| ≤ (m : ℝ) / 4) :
    |(e⁻¹) ^ 4 * torusCurvatureProjection (projectPlaquette z P : OrientedPlaquette m) (projectPlaquette z P')| ≤
      (16 + C) * (d⁻¹) ^ 4 ∧
    |(e⁻¹) ^ 4 * torusCurvatureProjection (projectPlaquette z P : OrientedPlaquette m) (projectPlaquette z P') -
        (e⁻¹) ^ 4 * intCurvatureProjection P P'| ≤
      C * ((e⁻¹) ^ 4 * ((m : ℝ) ^ 4)⁻¹) := by
  have hbq : ∀ (Q : IntPlaquette) (a : Fin 4), intBarycenter (Q.1 + z, Q.2) a = intBarycenter Q a + z a := by
    intro Q a
    simp only [intBarycenter, Pi.add_apply]
    push_cast
    ring
  have hvec : intBarycenter (P.1 + z, P.2) - intBarycenter (P'.1 + z, P'.2) =
      intBarycenter P - intBarycenter P' := by
    ext a
    simp only [PiLp.sub_apply, hbq]
    ring
  have h := hK.approx (projectPlaquette z P) (projectPlaquette z P') (P.1 + z, P.2) (P'.1 + z, P'.2)
    ⟨fun a => rfl, rfl⟩ ⟨fun a => rfl, rfl⟩
    (fun a => by
      have e1 : intBarycenter (P.1 + z, P.2) a - intBarycenter (P'.1 + z, P'.2) a =
          intBarycenter P a - intBarycenter P' a := by
        rw [hbq, hbq]; ring
      rw [e1]; exact hsup a)
  rw [hvec, intCurvatureProjection_translate] at h
  refine ⟨abs_inv_pow_mul_le he hd hK.nonneg hsep (hK.abs_le_one _ _) h.2, ?_⟩
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e⁻¹) ^ 4)]
  calc _ ≤ (e⁻¹) ^ 4 * (C * ((m : ℝ) ^ 4)⁻¹) := mul_le_mul_of_nonneg_left h.1 (by positivity)
    _ = _ := by ring
private theorem abs_prod_le_pow {ι : Type} (s : Finset ι) (a : ι → ℝ) {M : ℝ} (ha : ∀ i ∈ s, |a i| ≤ M) :
    |∏ i ∈ s, a i| ≤ M ^ s.card := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ s, |a i| ≤ ∏ _i ∈ s, M := Finset.prod_le_prod (fun i _ => abs_nonneg _) ha
    _ = M ^ s.card := by simp
private theorem abs_prod_sub_prod_le {ι : Type} (s : Finset ι) (a b : ι → ℝ) {M δ : ℝ} (hM : 1 ≤ M)
    (hδ : 0 ≤ δ) (ha : ∀ i ∈ s, |a i| ≤ M) (hb : ∀ i ∈ s, |b i| ≤ M) (hab : ∀ i ∈ s, |a i - b i| ≤ δ) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ s.card * M ^ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hM0 : 0 ≤ M := by linarith
    have h1 := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)) (fun j hj => hb j (Finset.mem_insert_of_mem hj))
      (fun j hj => hab j (Finset.mem_insert_of_mem hj))
    have hai := ha i (Finset.mem_insert_self _ _)
    have hbi := hab i (Finset.mem_insert_self _ _)
    have hB := abs_prod_le_pow s b (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    have e : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) + (a i - b i) * ∏ j ∈ s, b j := by ring
    rw [e]
    have t1 : |a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j)| ≤ M * (s.card * M ^ s.card * δ) := by
      rw [abs_mul]; exact mul_le_mul hai h1 (abs_nonneg _) hM0
    have t2 : |(a i - b i) * ∏ j ∈ s, b j| ≤ δ * M ^ s.card := by
      rw [abs_mul]; exact mul_le_mul hbi hB (abs_nonneg _) hδ
    have t3 := abs_add_le (a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j)) ((a i - b i) * ∏ j ∈ s, b j)
    have t5 : δ * M ^ s.card ≤ δ * M ^ (s.card + 1) := by
      refine mul_le_mul_of_nonneg_left ?_ hδ
      rw [pow_succ]; nlinarith [pow_nonneg hM0 s.card]
    push_cast
    have e2 : ((s.card : ℝ) + 1) * M ^ (s.card + 1) * δ =
        M * (s.card * M ^ s.card * δ) + δ * M ^ (s.card + 1) := by
      ring
    rw [e2]
    linarith
abbrev _root_.YangMills.SharedProofs.p14264 := @abs_prod_sub_prod_le
private theorem abs_prod_sub_prod_le_scaled {k : ℕ} {e : ℝ} (he : 0 < e) (a b : Fin k → ℝ) {M δ : ℝ}
    (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (ha : ∀ c, |(e⁻¹) ^ 4 * a c| ≤ M) (hb : ∀ c, |(e⁻¹) ^ 4 * b c| ≤ M)
    (hab : ∀ c, |(e⁻¹) ^ 4 * a c - (e⁻¹) ^ 4 * b c| ≤ δ) :
    |∏ c, a c - ∏ c, b c| ≤ e ^ (4 * k) * (k * M ^ k * δ) := by
  have hs : ∀ f : Fin k → ℝ, ∏ c, f c = e ^ (4 * k) * ∏ c, (e⁻¹) ^ 4 * f c := fun f => by
    have h1 : ∀ c, f c = e ^ 4 * ((e⁻¹) ^ 4 * f c) := fun c => by field_simp
    conv_lhs => rw [Finset.prod_congr rfl fun c _ => h1 c]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_mul]
  rw [hs a, hs b, ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < e ^ (4 * k))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := abs_prod_sub_prod_le Finset.univ (fun c => (e⁻¹) ^ 4 * a c) (fun c => (e⁻¹) ^ 4 * b c) hM hδ
    (fun c _ => ha c) (fun c _ => hb c) (fun c _ => hab c)
  simpa using this
private theorem fin_ne_add_one {k : ℕ} [NeZero k] (hk : 2 ≤ k) (c : Fin k) : c ≠ c + 1 := by
  intro h
  have h1 : (1 : Fin k) = 0 := by
    have : c + 1 = c + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have h2 := congrArg Fin.val h1
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h2
  simp at h2
abbrev _root_.YangMills.SharedProofs.p48899 := @fin_ne_add_one
private theorem abs_coord_le_norm (x : EuclideanFourSpace) (a : Fin 4) : |x a| ≤ ‖x‖ := by
  simpa using PiLp.norm_apply_le x a
private theorem supDist_le_norm_sub (x y : EuclideanFourSpace) : supDist x y ≤ ‖x - y‖ := by
  refine ciSup_le fun a => ?_
  simpa using abs_coord_le_norm (x - y) a
private theorem testWeight_eq_scaledWeight_lift {k : ℕ} {L : ℕ} [NeZero L] (P : LevelData k) (z : Fin 4 → ℤ)
    (hz : ∀ a, P.center a = (z a : ℝ) / (L : ℝ) ^ P.windowLevel) (i : Fin k)
    (p : OrientedPlaquette (fineSide L P.windowLevel (P.period L))) :
    P.testWeight L i _ p.1 = scaledWeight L P.scaleLevel (P.fn i) (liftPlaquette z p) := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have htop : ((P.period L : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hm : ((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) = (P.period L : ℝ) * (L : ℝ) ^ P.windowLevel := by
    rw [fineSide_eq]; push_cast; ring
  have hLK : (L : ℝ) ^ P.windowLevel ≠ 0 := pow_ne_zero _ hL
  have hLs : (L : ℝ) ^ P.scaleLevel ≠ 0 := pow_ne_zero _ hL
  simp only [LevelData.testWeight, scaledWeight]
  congr 1
  ext a
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [intBarycenter_liftPlaquette, hz a]
  simp only [circleRep]
  have e1 : (barycenterCoord p.1 a / (L : ℝ) ^ P.windowLevel - (z a : ℝ) / (L : ℝ) ^ P.windowLevel) /
      (P.period L : ℝ) =
      (barycenterCoord p.1 a - z a) / ((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) := by
    rw [hm]; field_simp
  rw [e1]
  generalize round ((barycenterCoord p.1 a - z a) / ((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ)) = r
  rw [hm]
  field_simp
private def linkBound (C d : ℝ) : ℝ := 1 + (16 + C) * (d⁻¹) ^ 4 + C
private theorem abs_orderSum_sub_le {k : ℕ} [NeZero k] {L : ℕ} [NeZero L] (P : LevelData k) {R d C : ℝ}
    (hk : 2 ≤ k) (hR : 0 ≤ R) (hd : 0 < d) (hP : P.SupAdmissible L R d)
    (hK : TorusProjectionBounds (fineSide L P.windowLevel (P.period L)) C) (σ : Equiv.Perm (Fin k)) :
    |∑ p : Fin k → OrientedPlaquette (fineSide L P.windowLevel (P.period L)),
        (∏ i, P.testWeight L i _ (p i).1) * ∏ c : Fin k, torusCurvatureProjection (p (σ c)) (p (σ (c + 1))) -
      ∑ Q ∈ Fintype.piFinset (fun _ : Fin k => plaquetteBox (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2)),
        (∏ i, scaledWeight L P.scaleLevel (P.fn i) (Q i)) *
          ∏ c : Fin k, intCurvatureProjection (Q (σ c)) (Q (σ (c + 1)))| ≤
      (6 * (2 * R + 7) ^ 4) ^ k * (k * linkBound C d ^ k *
        (C * (((L : ℝ) ^ P.scaleLevel) ^ 4 *
          (((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) ^ 4)⁻¹))) := by
  obtain ⟨z, hz⟩ := hP.center_mem_lattice
  have hC := hK.nonneg
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hT1 : (1 : ℝ) ≤ (L : ℝ) ^ P.scaleLevel := one_le_pow₀ hL1
  have hT0 : (0 : ℝ) < (L : ℝ) ^ P.scaleLevel := by linarith
  have hmcast : ((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) =
      (P.period L : ℝ) * (L : ℝ) ^ P.windowLevel := by
    rw [fineSide_eq]; push_cast; ring
  have htop1 : (1 : ℝ) ≤ (P.period L : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (P.period L))
  have hLK : (L : ℝ) ^ P.scaleLevel ≤ (L : ℝ) ^ P.windowLevel := pow_le_pow_right₀ hL1 hP.scaleLevel_le
  have hTm : (L : ℝ) ^ P.scaleLevel ≤ ((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) := by
    rw [hmcast]; nlinarith
  have hm0 : (0 : ℝ) < ((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) := by linarith
  have hsmall : 2 * (R * (L : ℝ) ^ P.scaleLevel) ≤ ((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) / 4 := by
    have := hP.support_small
    rw [hmcast]
    calc _ = 2 * R * (L : ℝ) ^ P.scaleLevel := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have hRT0 : 0 ≤ R * (L : ℝ) ^ P.scaleLevel := by positivity
  set e : ℝ := ((L : ℝ) ^ P.scaleLevel)⁻¹ with he
  have he0 : 0 < e := by positivity
  have heinv : e⁻¹ = (L : ℝ) ^ P.scaleLevel := inv_inv _
  have hwb : ∀ i Q, scaledWeight L P.scaleLevel (P.fn i) Q ≠ 0 →
      ∀ a, |intBarycenter Q a| ≤ R * (L : ℝ) ^ P.scaleLevel := by
    intro i Q hQ a
    have h1 := hP.isSupTestFamily.abs_coord_le i _ (subset_tsupport _ (Function.mem_support.mpr hQ)) a
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hT0] at h1
    rw [inv_mul_le_iff₀ hT0] at h1
    linarith [mul_comm R ((L : ℝ) ^ P.scaleLevel)]
  have hbox : ∀ i Q, scaledWeight L P.scaleLevel (P.fn i) Q ≠ 0 →
      Q ∈ plaquetteBox (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2) := by
    intro i Q hQ
    simp only [plaquetteBox, Finset.mem_product, Finset.mem_univ, and_true, Fintype.mem_piFinset, Finset.mem_Icc]
    intro a
    have h1 := hwb i Q hQ a
    obtain ⟨l, u⟩ := abs_le.mp h1
    have hb : R * (L : ℝ) ^ P.scaleLevel ≤ (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ : ℝ) := Nat.le_ceil _
    simp only [intBarycenter] at l u
    have o1 : (0 : ℝ) ≤ (if a = Q.2.1.1 then 1 / 2 else 0) := by split_ifs <;> norm_num
    have o2 : (if a = Q.2.1.1 then (1 : ℝ) / 2 else 0) ≤ 1 / 2 := by split_ifs <;> norm_num
    have o3 : (0 : ℝ) ≤ (if a = Q.2.1.2 then 1 / 2 else 0) := by split_ifs <;> norm_num
    have o4 : (if a = Q.2.1.2 then (1 : ℝ) / 2 else 0) ≤ 1 / 2 := by split_ifs <;> norm_num
    generalize (if a = Q.2.1.1 then (1 : ℝ) / 2 else 0) = u₁ at o1 o2 l u
    generalize (if a = Q.2.1.2 then (1 : ℝ) / 2 else 0) = u₂ at o3 o4 l u
    constructor
    · have : -(((⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2 : ℕ) : ℤ) : ℝ) ≤ (Q.1 a : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    · have : (Q.1 a : ℝ) ≤ (((⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2 : ℕ) : ℤ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
  have hlift : ∀ i Q, scaledWeight L P.scaleLevel (P.fn i) Q ≠ 0 →
      liftPlaquette z (projectPlaquette z Q : OrientedPlaquette (fineSide L P.windowLevel (P.period L))) = Q :=
    fun i Q hQ =>
    liftPlaquette_projectPlaquette z Q fun a => by
      have := hwb i Q hQ a
      linarith
  have hw1 : ∀ i Q, |scaledWeight L P.scaleLevel (P.fn i) Q| ≤ 1 := fun i Q => hP.isSupTestFamily.abs_le_one i _
  have hM1 : 1 ≤ linkBound C d := by
    have : 0 ≤ (16 + C) * (d⁻¹) ^ 4 := by positivity
    simp only [linkBound]; linarith
  set δ : ℝ := C * ((e⁻¹) ^ 4 * (((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) ^ 4)⁻¹) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδC : δ ≤ C := by
    have h1 : (e⁻¹) ^ 4 * (((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) ^ 4)⁻¹ ≤ 1 := by
      rw [heinv, ← div_eq_mul_inv]
      exact (div_le_one (by positivity)).mpr (pow_le_pow_left₀ hT0.le hTm 4)
    calc δ ≤ C * 1 := mul_le_mul_of_nonneg_left h1 hC
      _ = C := mul_one _
  have hterm : ∀ Q : Fin k → IntPlaquette, (∀ i, scaledWeight L P.scaleLevel (P.fn i) (Q i) ≠ 0) →
      |∏ c : Fin k, torusCurvatureProjection
          (projectPlaquette z (Q (σ c)) : OrientedPlaquette (fineSide L P.windowLevel (P.period L)))
          (projectPlaquette z (Q (σ (c + 1)))) -
        ∏ c : Fin k, intCurvatureProjection (Q (σ c)) (Q (σ (c + 1)))| ≤
        e ^ (4 * k) * (k * linkBound C d ^ k * δ) := by
    intro Q hQ
    have hlink : ∀ c : Fin k, _ := fun c : Fin k => by
      have hne : σ c ≠ σ (c + 1) := fun h => fin_ne_add_one hk c (σ.injective h)
      have hsep : d ≤ e * ‖intBarycenter (Q (σ c)) - intBarycenter (Q (σ (c + 1)))‖ := by
        have h1 := hP.isSupTestFamily.le_supDist _ _ hne _ (subset_tsupport _ (Function.mem_support.mpr (hQ (σ c))))
          _ (subset_tsupport _ (Function.mem_support.mpr (hQ (σ (c + 1)))))
        have h2 := supDist_le_norm_sub (((L : ℝ) ^ P.scaleLevel)⁻¹ • intBarycenter (Q (σ c)))
          (((L : ℝ) ^ P.scaleLevel)⁻¹ • intBarycenter (Q (σ (c + 1))))
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos he0] at h2
        exact h1.trans h2
      have hsup : ∀ a, |intBarycenter (Q (σ c)) a - intBarycenter (Q (σ (c + 1))) a| ≤
          ((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) / 4 := fun a => by
        obtain ⟨l₁, u₁⟩ := abs_le.mp (hwb _ _ (hQ (σ c)) a)
        obtain ⟨l₂, u₂⟩ := abs_le.mp (hwb _ _ (hQ (σ (c + 1))) a)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact projection_link_bounds hK he0 hd z _ _ hsep hsup
    have hbig : (16 + C) * (d⁻¹) ^ 4 ≤ linkBound C d := by
      simp only [linkBound]; linarith
    refine abs_prod_sub_prod_le_scaled he0 _ _ hM1 hδ0 (fun c => (hlink c).1.trans hbig) (fun c => ?_)
      (fun c => (hlink c).2)
    obtain ⟨h1, h2⟩ := hlink c
    obtain ⟨a1, a2⟩ := abs_le.mp h1
    obtain ⟨b1, b2⟩ := abs_le.mp h2
    refine abs_le.mpr ⟨?_, ?_⟩ <;> simp only [linkBound] <;> linarith
  have hX : 0 ≤ e ^ (4 * k) * (k * linkBound C d ^ k * δ) := by positivity
  have hcmp := abs_torusSum_sub_latticeSum_le
    (fun i => P.testWeight L i (fineSide L P.windowLevel (P.period L)))
    (fun i => scaledWeight L P.scaleLevel (P.fn i)) z
    (plaquetteBox (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2))
    (fun i p => testWeight_eq_scaledWeight_lift P z hz i p) hbox hlift hw1 σ hX hterm
  refine hcmp.trans ?_
  have hcard : ((plaquetteBox (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2)).card : ℝ) =
      (2 * ((⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ : ℝ) + 2) + 1) ^ 4 * 6 := by
    have h1 : (Finset.Icc (-(((⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2 : ℕ)) : ℤ))
        (((⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2 : ℕ)) : ℤ)).card =
        2 * (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2) + 1 := by
      simp only [Int.card_Icc]; omega
    have h2 : Fintype.card OrderedDirectionPair = 6 := by decide
    simp only [plaquetteBox, Finset.card_product, Fintype.card_piFinset, h1, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, h2]
    push_cast
    ring
  have hbase : e ^ 4 * ((plaquetteBox (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2)).card : ℝ) ≤ 6 * (2 * R + 7) ^ 4 := by
    rw [hcard]
    have h1 : ((⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ : ℕ) : ℝ) < R * (L : ℝ) ^ P.scaleLevel + 1 := Nat.ceil_lt_add_one hRT0
    have h2 : 2 * ((⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ : ℝ) + 2) + 1 ≤ (2 * R + 7) * (L : ℝ) ^ P.scaleLevel := by
      nlinarith
    have h3 : e * (2 * ((⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ : ℝ) + 2) + 1) ≤ 2 * R + 7 := by
      calc _ ≤ e * ((2 * R + 7) * (L : ℝ) ^ P.scaleLevel) := mul_le_mul_of_nonneg_left h2 he0.le
        _ = 2 * R + 7 := by rw [he]; field_simp
    have h4 : (e * (2 * ((⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ : ℝ) + 2) + 1)) ^ 4 ≤ (2 * R + 7) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h3 4
    calc _ = (e * (2 * ((⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ : ℝ) + 2) + 1)) ^ 4 * 6 := by ring
      _ ≤ (2 * R + 7) ^ 4 * 6 := mul_le_mul_of_nonneg_right h4 (by norm_num)
      _ = _ := by ring
  have hpow : ((plaquetteBox (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2)).card : ℝ) ^ k * e ^ (4 * k) ≤
      (6 * (2 * R + 7) ^ 4) ^ k := by
    rw [pow_mul, ← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (by positivity) hbase k
  have hY : 0 ≤ (k : ℝ) * linkBound C d ^ k * δ := by positivity
  calc _ = (((plaquetteBox (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2)).card : ℝ) ^ k * e ^ (4 * k)) *
        (k * linkBound C d ^ k * δ) := by ring
    _ ≤ (6 * (2 * R + 7) ^ 4) ^ k * (k * linkBound C d ^ k * δ) := mul_le_mul_of_nonneg_right hpow hY
    _ = _ := by rw [hδ, heinv]
theorem torusCycleSumNearLattice_of_curvatureKernelBounds (hK : curvatureKernelBoundsStatement) :
    torusCycleSumNearLatticeStatement := by
  intro k _ hk R d hR hd
  obtain ⟨C₀, hC₀⟩ := hK
  refine ⟨3 * ((unorientedCyclicOrders k).card : ℝ) *
    ((6 * (2 * R + 7) ^ 4) ^ k * (k * linkBound |C₀| d ^ k * |C₀|)), ?_⟩
  intro L _ P hP
  have hFacts : TorusProjectionBounds (fineSide L P.windowLevel (P.period L)) |C₀| := by
    obtain ⟨h1, -, h3, -⟩ := hC₀ (fineSide L P.windowLevel (P.period L))
    refine ⟨abs_nonneg _, h1, fun p p' Q Q' l l' hs => ?_⟩
    obtain ⟨a, b⟩ := h3 p p' Q Q' l l' hs
    exact ⟨a.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)), fun hf =>
      (b hf).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))⟩
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hLpos : (0 : ℝ) < L := by linarith
  have hmcast : ((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) =
      (P.period L : ℝ) * (L : ℝ) ^ P.windowLevel := by
    rw [fineSide_eq]; push_cast; ring
  have htop1 : (1 : ℝ) ≤ (P.period L : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (P.period L))
  have hrate : ((L : ℝ) ^ P.scaleLevel) ^ 4 * (((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) ^ 4)⁻¹ ≤
      (L : ℝ) ^ (-(4 * ((P.windowLevel : ℝ) - (P.scaleLevel : ℝ)))) := by
    have e1 : -(4 * ((P.windowLevel : ℝ) - (P.scaleLevel : ℝ))) =
        ((4 * P.scaleLevel : ℕ) : ℝ) - ((4 * P.windowLevel : ℕ) : ℝ) := by push_cast; ring
    rw [e1, Real.rpow_sub hLpos, Real.rpow_natCast, Real.rpow_natCast, hmcast, div_eq_mul_inv, ← pow_mul,
      mul_comm P.scaleLevel 4]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine inv_anti₀ (by positivity) ?_
    have h4 : (L : ℝ) ^ (4 * P.windowLevel) = ((L : ℝ) ^ P.windowLevel) ^ 4 := by rw [mul_comm, pow_mul]
    rw [h4]
    refine pow_le_pow_left₀ (by positivity) ?_ 4
    have : (0 : ℝ) < (L : ℝ) ^ P.windowLevel := by positivity
    nlinarith
  have hnum : latticeCycleSum L P.scaleLevel (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2) P.fn =
      3 * (if k = 2 then 1 / 2 else 1) *
      ∑ σ ∈ unorientedCyclicOrders k,
        ∑ Q ∈ Fintype.piFinset (fun _ : Fin k => plaquetteBox (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2)),
          (∏ i, scaledWeight L P.scaleLevel (P.fn i) (Q i)) *
            ∏ c : Fin k, intCurvatureProjection (Q (σ c)) (Q (σ (c + 1))) := rfl
  rw [hnum, ← mul_sub, abs_mul, ← Finset.sum_sub_distrib]
  have hcoef : |3 * (if k = 2 then (1 : ℝ) / 2 else 1)| ≤ 3 := by
    split_ifs <;> norm_num
  have hM0 : 0 ≤ linkBound |C₀| d := by
    have : 0 ≤ (16 + |C₀|) * (d⁻¹) ^ 4 := by positivity
    simp only [linkBound]; positivity
  have hone : ∀ σ : Equiv.Perm (Fin k), |∑ p : Fin k → OrientedPlaquette (fineSide L P.windowLevel (P.period L)),
        (∏ i, P.testWeight L i _ (p i).1) * ∏ c : Fin k, torusCurvatureProjection (p (σ c)) (p (σ (c + 1))) -
      ∑ Q ∈ Fintype.piFinset (fun _ : Fin k => plaquetteBox (⌈R * (L : ℝ) ^ P.scaleLevel⌉₊ + 2)),
        (∏ i, scaledWeight L P.scaleLevel (P.fn i) (Q i)) *
          ∏ c : Fin k, intCurvatureProjection (Q (σ c)) (Q (σ (c + 1)))| ≤
      ((6 * (2 * R + 7) ^ 4) ^ k * (k * linkBound |C₀| d ^ k * |C₀|)) *
        (L : ℝ) ^ (-(4 * ((P.windowLevel : ℝ) - (P.scaleLevel : ℝ)))) := by
    intro σ
    refine (abs_orderSum_sub_le P hk hR hd hP hFacts σ).trans ?_
    have hA : 0 ≤ (6 * (2 * R + 7) ^ 4) ^ k * (k * linkBound |C₀| d ^ k * |C₀|) := by positivity
    calc _ = ((6 * (2 * R + 7) ^ 4) ^ k * (k * linkBound |C₀| d ^ k * |C₀|)) *
          (((L : ℝ) ^ P.scaleLevel) ^ 4 * (((fineSide L P.windowLevel (P.period L) : ℕ) : ℝ) ^ 4)⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrate hA
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun σ (_ : σ ∈ unorientedCyclicOrders k) => hone σ)
  refine (mul_le_mul hcoef hsum (abs_nonneg _) (by norm_num)).trans (le_of_eq ?_)
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring
end YangMills.Construction.MomentLaw
end
