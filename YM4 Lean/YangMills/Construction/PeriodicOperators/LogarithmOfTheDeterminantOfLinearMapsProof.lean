import YangMills.Construction.PeriodicOperators.LogarithmOfTheDeterminantOfLinearMaps
import Mathlib
set_option autoImplicit false
open Filter Asymptotics Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LogDetOfMaps
open Coordinates.ComplexCoordinates.LogDetSecondDeriv
private theorem hasDerivAt_quadratic (c₀ a b : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => c₀ + (t : ℂ) * a + (1 / 2 : ℂ) * (t : ℂ) ^ 2 * b)
      (a + (t : ℂ) * b) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 := ((h1.mul_const a).const_add c₀).add (((h1.pow 2).const_mul (1 / 2 : ℂ)).mul_const b)
  exact (show HasDerivAt (fun t : ℝ => c₀ + (t : ℂ) * a + (1 / 2 : ℂ) * (t : ℂ) ^ 2 * b) _ t
    from h2).congr_deriv (by rw [show (2 - 1 : ℕ) = 1 from rfl]; push_cast; ring)
private theorem abs_pow_three_isLittleO_sq :
    (fun t : ℝ => |t| ^ 3) =o[𝓝 0] fun t : ℝ => ((t : ℂ)) ^ 2 := by
  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by simpa using ht
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  have h0 : 0 ≤ |t| ^ 2 := by positivity
  calc |t| ^ 3 = |t| * |t| ^ 2 := by ring
    _ ≤ ε * |t| ^ 2 := mul_le_mul_of_nonneg_right ht'.le h0
private theorem abs_pow_three_isLittleO_id :
    (fun t : ℝ => |t| ^ 3) =o[𝓝 0] fun t : ℝ => t := by
  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hε one_pos)] with t ht
  have ht' : |t| < min ε 1 := by simpa using ht
  have h1 : |t| < ε := lt_of_lt_of_le ht' (min_le_left _ _)
  have h2 : |t| < 1 := lt_of_lt_of_le ht' (min_le_right _ _)
  have h3 : |t| ^ 2 ≤ ε := by nlinarith [abs_nonneg t]
  simp only [Real.norm_eq_abs, abs_pow, abs_abs]
  calc |t| ^ 3 = |t| ^ 2 * |t| := by ring
    _ ≤ ε * |t| := mul_le_mul_of_nonneg_right h3 (abs_nonneg t)
private theorem derivs_eq_of_taylor {φ : ℝ → ℂ} {a b d c : ℂ}
    (hd : HasDerivAt φ d 0) (hev : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ φ t)
    (hc : HasDerivAt (deriv φ) c 0)
    (hexp : (fun t : ℝ => φ t - (φ 0 + (t : ℂ) * a + (1 / 2 : ℂ) * (t : ℂ) ^ 2 * b))
      =O[𝓝 0] fun t : ℝ => |t| ^ 3) :
    d = a ∧ c = b := by
  have hda : d = a := by
    have hE1 : HasDerivAt
        (fun t : ℝ => φ t - (φ 0 + (t : ℂ) * a + (1 / 2 : ℂ) * (t : ℂ) ^ 2 * b)) (d - a) 0 := by
      have h1 := hd.sub (hasDerivAt_quadratic (φ 0) a b 0)
      exact (show HasDerivAt
        (fun t : ℝ => φ t - (φ 0 + (t : ℂ) * a + (1 / 2 : ℂ) * (t : ℂ) ^ 2 * b)) _ 0
        from h1).congr_deriv (by simp)
    have hE2 : HasDerivAt
        (fun t : ℝ => φ t - (φ 0 + (t : ℂ) * a + (1 / 2 : ℂ) * (t : ℂ) ^ 2 * b)) 0 0 := by
      rw [hasDerivAt_iff_isLittleO_nhds_zero]
      simpa using hexp.trans_isLittleO abs_pow_three_isLittleO_id
    exact sub_eq_zero.1 (hE1.unique hE2)
  refine ⟨hda, ?_⟩
  have hd0 : deriv φ 0 = a := hd.deriv.trans hda
  set G : ℝ → ℂ := fun t => φ t - (φ 0 + (t : ℂ) * a + (1 / 2 : ℂ) * (t : ℂ) ^ 2 * c) with hG
  have hG0 : G 0 = 0 := by simp [hG]
  have hlin : (fun t : ℝ => deriv φ t - (a + (t : ℂ) * c)) =o[𝓝 0] fun t : ℝ => t := by
    have := hasDerivAt_iff_isLittleO_nhds_zero.1 hc
    simp only [zero_add, hd0] at this
    refine this.congr_left fun t => ?_
    simp only [Complex.real_smul]
    ring
  have hGo : G =o[𝓝 0] fun t : ℝ => ((t : ℂ)) ^ 2 := by
    rw [isLittleO_iff]
    intro ε hε
    have h1 := (isLittleO_iff.1 hlin hε).and hev
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 h1
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have hsub : Metric.closedBall (0 : ℝ) |t| ⊆ Metric.ball 0 δ := by
      intro s hs
      have hs' : |s| ≤ |t| := by simpa using hs
      have ht' : |t| < δ := by simpa using ht
      simpa using lt_of_le_of_lt hs' ht'
    have hder : ∀ s ∈ Metric.closedBall (0 : ℝ) |t|,
        HasDerivWithinAt G (deriv φ s - (a + (s : ℂ) * c)) (Metric.closedBall (0 : ℝ) |t|) s :=
      fun s hs => (((hball s (hsub hs)).2.hasDerivAt).sub
        (hasDerivAt_quadratic (φ 0) a c s)).hasDerivWithinAt
    have hbound : ∀ s ∈ Metric.closedBall (0 : ℝ) |t|,
        ‖deriv φ s - (a + (s : ℂ) * c)‖ ≤ ε * |t| := by
      intro s hs
      have hs' : |s| ≤ |t| := by simpa using hs
      have := (hball s (hsub hs)).1
      rw [Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_left hs' hε.le)
    have hmv := (convex_closedBall (0 : ℝ) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le
      hder hbound (x := 0) (y := t) (by simp) (by simp)
    simp only [hG0, sub_zero, Real.norm_eq_abs] at hmv
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc ‖G t‖ ≤ ε * |t| * |t| := hmv
      _ = ε * |t| ^ 2 := by ring
  have hsq : (fun t : ℝ => (t : ℂ) ^ 2 * ((1 / 2 : ℂ) * (c - b))) =o[𝓝 0]
      fun t : ℝ => ((t : ℂ)) ^ 2 := by
    refine ((hexp.trans_isLittleO abs_pow_three_isLittleO_sq).sub hGo).congr_left fun t => ?_
    simp only [hG]
    ring
  by_contra hne
  have hw : (1 / 2 : ℂ) * (c - b) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.2 hne)
  have hpos : 0 < ‖(1 / 2 : ℂ) * (c - b)‖ / 2 := half_pos (norm_pos_iff.2 hw)
  have hfil := ((isLittleO_iff.1 hsq hpos).filter_mono
    (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))).and self_mem_nhdsWithin
  obtain ⟨t, ht, ht0⟩ := hfil.exists
  have htpos : 0 < ‖((t : ℂ)) ^ 2‖ := by
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    exact norm_pos_iff.2 (pow_ne_zero 2 this)
  rw [norm_mul] at ht
  nlinarith [norm_pos_iff.2 hw]
variable {N : ℕ}
private theorem derivs_of_second_order_expansion
    (hZ : Coordinates.ComplexCoordinates.LogDetSecondDeriv.Claim)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (Coordinates.ComplexCoordinates N)} (hO : IsOpen O)
    (h0 : (0 : Coordinates.ComplexCoordinates N) ∈ O)
    {g : Coordinates.ComplexCoordinates N → ℂ} (hg : IsHolomorphicScalarIn O g)
    {a : Coordinates.ComplexCoordinates N → ℂ}
    {b : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N → ℂ}
    (ha : IsLinearMap ℂ a) (hb₁ : ∀ h, IsLinearMap ℂ fun k => b k h)
    (hb₂ : ∀ k, IsLinearMap ℂ (b k)) (hb : ∀ k h, b k h = b h k)
    (hexp : (fun z => g z - (g 0 + a z + (1 / 2 : ℂ) * b z z))
      =O[𝓝 0] fun z : Coordinates.ComplexCoordinates N => ‖z‖ ^ 3) :
    (∀ k, scalarDeriv g 0 k = a k) ∧ ∀ k h, scalarSecondDeriv g 0 k h = b k h := by
  have key : ∀ k, scalarDeriv g 0 k = a k ∧
      scalarSecondDeriv g 0 k k = b k k := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hZ.2 N O g hO h0 hg k k
    have hshift : ∀ t : ℝ, (fun t' : ℝ => g (t • k + t' • k)) =
        fun t' : ℝ => (fun s : ℝ => g (s • k)) (t + t') := by
      intro t
      funext t'
      simp only [add_smul]
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun s : ℝ => g (s • k)) t := by
      filter_upwards [h2] with t ht
      rw [hshift t] at ht
      have h' : DifferentiableAt ℝ (fun x : ℝ => (fun s : ℝ => g (s • k)) (t + x)) (-t + t) := by
        rw [neg_add_cancel]
        exact ht
      exact (differentiableAt_iff_comp_const_add (b := t)).2 h'
    have hder : (fun t : ℝ => deriv (fun t' : ℝ => g (t • k + t' • k)) 0) =
        deriv (fun s : ℝ => g (s • k)) := by
      funext t
      rw [hshift t]
      have h' := deriv_comp_const_add (f := fun s : ℝ => g (s • k)) (a := t) (x := 0)
      rw [add_zero] at h'
      exact h'
    rw [hder] at h3
    have hsmul : ∀ t : ℝ, t • k = (t : ℂ) • k := fun t => (Complex.coe_smul t k).symm
    have hline : Tendsto (fun t : ℝ => t • k) (𝓝 0) (𝓝 0) := by
      have : Continuous fun t : ℝ => t • k := by fun_prop
      simpa using this.tendsto 0
    have hE := hexp.comp_tendsto hline
    have hE' : (fun t : ℝ => g (t • k) - (g ((0 : ℝ) • k) + (t : ℂ) * a k +
        (1 / 2 : ℂ) * (t : ℂ) ^ 2 * b k k)) =O[𝓝 0] fun t : ℝ => |t| ^ 3 := by
      refine (hE.congr_left fun t => ?_).trans (IsBigO.of_bound (‖k‖ ^ 3) ?_)
      · simp only [Function.comp_apply, zero_smul]
        rw [hsmul t, ha.map_smul, (hb₁ _).map_smul, (hb₂ _).map_smul]
        simp only [smul_eq_mul]
        ring
      · refine Eventually.of_forall fun t => ?_
        simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs, abs_pow, abs_abs, mul_pow,
          abs_mul, abs_norm]
        exact (mul_comm _ _).le
    exact derivs_eq_of_taylor h1 hev h3 hE'
  refine ⟨fun k => (key k).1, fun k h => ?_⟩
  obtain ⟨-, ⟨B, hB⟩, hsym⟩ := (hD N 1 O (asLine g) hg).2 0 h0
  have hnum : ∀ k h, scalarSecondDeriv g 0 k h = B k h 0 := by
    intro k h
    rw [hB]
    rfl
  have hsymB : B h k 0 = B k h 0 := by
    rw [hB, hB, hsym]
  have e1 := (key (k + h)).2
  have e2 := (key k).2
  have e3 := (key h).2
  rw [hnum] at e1 e2 e3 ⊢
  have hbl : b (k + h) (k + h) = b k k + b k h + (b h k + b h h) := by
    rw [(hb₁ _).map_add, (hb₂ _).map_add, (hb₂ _).map_add]
  have hBl : B (k + h) (k + h) 0 = B k k 0 + B k h 0 + (B h k 0 + B h h 0) := by
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    ring
  rw [hbl, hBl, hsymB, hb h k, e2, e3] at e1
  have : (2 : ℂ) * B k h 0 = 2 * b k h := by linear_combination e1
  exact mul_left_cancel₀ two_ne_zero this
variable {C : Type}
private theorem isLinearMap_linearMapEntry {V : Type} [AddCommGroup V] [Module ℂ V]
    {F : V → Module.End ℂ (C → ℂ)} (hF : IsLinearMap ℂ F) (c' c : C) :
    IsLinearMap ℂ fun v => linearMapEntry (F v) c' c :=
  ⟨fun x y => by simp [linearMapEntry, hF.map_add], fun s x => by simp [linearMapEntry, hF.map_smul]⟩
theorem claim_of_matrix_formula (hZ : Coordinates.ComplexCoordinates.LogDetSecondDeriv.Claim)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim) : PeriodicOperators.LogDetOfMaps.Claim := by
  intro C _ N O M A₁ A₂ hO h0 hM hU hA₁ hA₂l hA₂r hA₂s hexp
  classical
  cases nonempty_fintype C
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let β : Module.Basis (Fin (Fintype.card C)) ℂ (C → ℂ) := (Pi.basisFun ℂ C).reindex e
  let T : Module.End ℂ (C → ℂ) → Matrix (Fin (Fintype.card C)) (Fin (Fintype.card C)) ℂ :=
    fun L => LinearMap.toMatrix β β L
  have hT : ∀ L i j, T L i j = linearMapEntry L (e.symm i) (e.symm j) := by
    intro L i j
    simp only [T, β, LinearMap.toMatrix_apply, linearMapEntry, Module.Basis.reindex_apply,
      Module.Basis.repr_reindex_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  have hTmul : ∀ L L', T (L * L') = T L * T L' := fun L L' => LinearMap.toMatrix_mul β L L'
  have hT1 : T 1 = 1 := LinearMap.toMatrix_one β
  have hright : T (M 0) * T (Ring.inverse (M 0)) = 1 := by
    rw [← hTmul, Ring.mul_inverse_cancel _ hU, hT1]
  have hinv : T (Ring.inverse (M 0)) = (T (M 0))⁻¹ := (Matrix.inv_eq_right_inv hright).symm
  have hUnit : IsUnit (T (M 0)) := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hright)
  have hdet : ∀ z, detRatio M z =
      detNormalized (fun z => T (M z)) z := by
    intro z
    simp only [detRatio, detNormalized]
    rw [← LinearMap.det_toMatrix β]
    change Matrix.det (T (Ring.inverse (M 0) * M z)) = _
    rw [hTmul, hinv]
  have hlog : logDetRatio M = logDetNormalized fun z => T (M z) := by
    funext z
    simp only [logDetRatio, logDetNormalized, hdet]
  have hentry : ∀ (L : Coordinates.ComplexCoordinates N → Module.End ℂ (C → ℂ)) i j,
      (fun z => T (L z) i j) = fun z => linearMapEntry (L z) (e.symm i) (e.symm j) :=
    fun L i j => funext fun z => hT _ i j
  have hhol : ∀ i j, IsHolomorphicScalarIn O fun z => T (M z) i j := by
    intro i j
    rw [hentry]
    exact hM _ _
  obtain ⟨⟨W, hWo, hW0, hWO, hWn, hWh⟩, hF⟩ := hZ.1 N _ O (fun z => T (M z)) hO h0 hhol hUnit
  refine ⟨⟨W, hWo, hW0, hWO, fun z hz => ?_, ?_⟩, fun k h => ?_⟩
  · rw [hdet]
    exact hWn z hz
  · rw [hlog]
    exact hWh
  · have hdiff : ∀ i j, _ := fun i j =>
      derivs_of_second_order_expansion hZ hD hO h0 (hM (e.symm i) (e.symm j))
        (isLinearMap_linearMapEntry hA₁ (e.symm i) (e.symm j))
        (fun h => isLinearMap_linearMapEntry (hA₂l h) (e.symm i) (e.symm j))
        (fun k => isLinearMap_linearMapEntry (hA₂r k) (e.symm i) (e.symm j))
        (fun k h => by rw [hA₂s k h]) (hexp (e.symm i) (e.symm j))
    have h1 : ∀ k, derivMatrix (fun z => T (M z)) k = T (A₁ k) := by
      intro k
      ext i j
      simp only [derivMatrix, Matrix.of_apply]
      rw [hentry, hT]
      exact (hdiff i j).1 k
    have h2 : secondDerivMatrix (fun z => T (M z)) k h = T (A₂ k h) := by
      ext i j
      simp only [secondDerivMatrix, Matrix.of_apply]
      rw [hentry, hT]
      exact (hdiff i j).2 k h
    rw [hlog, hF k h, h1, h1, h2, LinearMap.trace_eq_matrix_trace ℂ β,
      LinearMap.trace_eq_matrix_trace ℂ β]
    change _ = Matrix.trace (T (Ring.inverse (M 0) * A₂ k h)) -
      Matrix.trace (T (Ring.inverse (M 0) * A₁ k * Ring.inverse (M 0) * A₁ h))
    simp only [hTmul, hinv]
end YangMills.Construction.PeriodicOperators.LogDetOfMaps
end
