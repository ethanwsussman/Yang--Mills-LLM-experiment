import YangMills.Construction.Lattice.EndPointsAndOrientationOfABond
import YangMills.Construction.RunningCouplingSlope.PlainAverageAlongComplexCurvesProof
import YangMills.Construction.RunningCouplingSlope.PlainAverageNearOne
import YangMills.Construction.RunningCouplingSlope.PlainDifferentialIsLinear
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.HolDifferentialLinearProof
open Tower Matrices
section CurveDerivatives
variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private def HasCurveDeriv (V : ι → ComplexMatrix2) (f : (ι → ComplexMatrix2) → E)
    (T : (ι → ComplexMatrix2) →ₗ[ℂ] E) : Prop :=
  ∀ (g : ι → ComplexMatrix2) (γ : ℂ → ι → ComplexMatrix2), γ 0 = V →
    (∀ b, HasDerivAt (fun t => γ t b) (g b) 0) →
    HasDerivAt (fun t => f (γ t)) (T g) 0
variable {V : ι → ComplexMatrix2}
private theorem hasCurveDeriv_eval (b : ι) :
    HasCurveDeriv V (fun U => U b) (LinearMap.proj (R := ℂ) (φ := fun _ : ι => ComplexMatrix2) b) :=
  fun _ _ _ h => h b
private theorem hasCurveDeriv_one : HasCurveDeriv V (fun _ => (1 : ComplexMatrix2)) 0 :=
  fun _ _ _ _ => hasDerivAt_const _ _
private theorem hasCurveDeriv_mul {f₁ f₂ : (ι → ComplexMatrix2) → ComplexMatrix2}
    {T₁ T₂ : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2}
    (h₁ : HasCurveDeriv V f₁ T₁) (h₂ : HasCurveDeriv V f₂ T₂) :
    HasCurveDeriv V (fun U => f₁ U * f₂ U)
      ((LinearMap.mulRight ℂ (f₂ V)) ∘ₗ T₁ + (LinearMap.mulLeft ℂ (f₁ V)) ∘ₗ T₂) := by
  intro g γ h0 hγ
  have := (h₁ g γ h0 hγ).mul (h₂ g γ h0 hγ)
  rw [h0] at this
  exact this
private theorem hasCurveDeriv_sum {α : Type*} (s : Finset α) {f : α → (ι → ComplexMatrix2) → E}
    {T : α → (ι → ComplexMatrix2) →ₗ[ℂ] E} (h : ∀ a ∈ s, HasCurveDeriv V (f a) (T a)) :
    HasCurveDeriv V (fun U => ∑ a ∈ s, f a U) (∑ a ∈ s, T a) := by
  intro g γ h0 hγ
  have := HasDerivAt.fun_sum (u := s) fun a ha => h a ha g γ h0 hγ
  simpa [LinearMap.sum_apply] using this
private theorem hasCurveDeriv_const_smul {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {T : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2} (a : ℂ)
    (h : HasCurveDeriv V f T) : HasCurveDeriv V (fun U => a • f U) (a • T) :=
  fun g γ h0 hγ => (h g γ h0 hγ).const_smul a
private theorem hasCurveDeriv_inv (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {f : (ι → ComplexMatrix2) → ComplexMatrix2} {T : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2}
    (h : HasCurveDeriv V f T) (hu : IsUnit (Matrix.det (f V))) :
    HasCurveDeriv V (fun U => (f U)⁻¹)
      (-((LinearMap.mulRight ℂ (f V)⁻¹) ∘ₗ (LinearMap.mulLeft ℂ (f V)⁻¹) ∘ₗ T)) := by
  intro g γ h0 hγ
  have hF := h g γ h0 hγ
  set w := (f V)⁻¹ with hw
  have hfw : f V * w = 1 := Matrix.mul_nonsing_inv _ hu
  have hwf : w * f V = 1 := Matrix.nonsing_inv_mul _ hu
  have hdw : IsUnit (Matrix.det w) := by
    have h1 : Matrix.det w * Matrix.det (f V) = 1 := by rw [← Matrix.det_mul, hwf, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ h1
  have hX : HasDerivAt (fun t => f (γ t) * w) (T g * w) 0 := hF.mul_const w
  have hX0 : (fun t => f (γ t) * w) 0 = 1 := by simp only [h0, hfw]
  have hinv := ((hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hX hX hX).2.1 hX0).2.1
  have e : (fun t => (f (γ t))⁻¹) = fun t => w * (f (γ t) * w)⁻¹ := by
    funext t
    rw [Matrix.mul_inv_rev, ← mul_assoc, Matrix.mul_nonsing_inv _ hdw, one_mul]
  rw [e]
  have := hinv.const_mul w
  exact HasDerivAt.congr_deriv this (by simp [mul_assoc])
private theorem exists_hasCurveDeriv_listProd (l : List ι) :
    ∃ T, HasCurveDeriv V (fun U => (l.map U).prod) T := by
  induction l with
  | nil => exact ⟨0, by simpa using hasCurveDeriv_one (V := V)⟩
  | cons b l ih =>
    obtain ⟨T, hT⟩ := ih
    exact ⟨_, by simpa using hasCurveDeriv_mul (hasCurveDeriv_eval b) hT⟩
private theorem hasDerivAt_matrix_entry {W : ℂ → ComplexMatrix2} {D : ComplexMatrix2}
    (h : HasDerivAt W D 0) (a b : Fin 2) :
    HasDerivAt (fun t => W t a b) (D a b) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.hasDerivAt_matrix_entry <;> assumption
private theorem exists_hasCurveDeriv_det {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {T : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2}
    (h : HasCurveDeriv V f T) :
    ∃ T' : (ι → ComplexMatrix2) →ₗ[ℂ] ℂ, HasCurveDeriv V (fun U => Matrix.det (f U)) T' := by
  refine ⟨{ toFun := fun g => (T g 0 0 * f V 1 1 + f V 0 0 * T g 1 1) -
              (T g 0 1 * f V 1 0 + f V 0 1 * T g 1 0)
            map_add' := fun x y => by simp only [map_add, Matrix.add_apply]; ring
            map_smul' := fun a x => by
              simp only [map_smul, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]
              ring }, fun g γ h0 hγ => ?_⟩
  have hF := h g γ h0 hγ
  have e : (fun t => Matrix.det (f (γ t))) =
      fun t => f (γ t) 0 0 * f (γ t) 1 1 - f (γ t) 0 1 * f (γ t) 1 0 := by
    funext t
    exact Matrix.det_fin_two _
  rw [e]
  have := ((hasDerivAt_matrix_entry hF 0 0).mul (hasDerivAt_matrix_entry hF 1 1)).sub
    ((hasDerivAt_matrix_entry hF 0 1).mul (hasDerivAt_matrix_entry hF 1 0))
  simp only [h0] at this
  exact this
private theorem exists_hasCurveDeriv_sqrt {f : (ι → ComplexMatrix2) → ℂ}
    {T : (ι → ComplexMatrix2) →ₗ[ℂ] ℂ} (h : HasCurveDeriv V f T)
    (hs : f V ∈ Complex.slitPlane) :
    ∃ T' : (ι → ComplexMatrix2) →ₗ[ℂ] ℂ, HasCurveDeriv V (fun U => (f U) ^ (1 / 2 : ℂ)) T' := by
  have hr : HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (f V) ^ ((1 / 2 : ℂ) - 1) * 1) (f V) :=
    (hasDerivAt_id (f V)).cpow_const (c := (1 / 2 : ℂ)) hs
  refine ⟨((1 / 2 : ℂ) * (f V) ^ ((1 / 2 : ℂ) - 1) * 1) • T, fun g γ h0 hγ => ?_⟩
  have hF := h g γ h0 hγ
  have := HasDerivAt.comp (0 : ℂ) (h₂ := fun z : ℂ => z ^ (1 / 2 : ℂ))
    (by rw [h0]; exact hr) hF
  exact HasDerivAt.congr_deriv this (by simp [LinearMap.smul_apply])
private theorem exists_hasCurveDeriv_inv_smul {r : (ι → ComplexMatrix2) → ℂ}
    {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {R : (ι → ComplexMatrix2) →ₗ[ℂ] ℂ} {T : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2}
    (hr : HasCurveDeriv V r R) (hf : HasCurveDeriv V f T) (h0 : r V ≠ 0) :
    ∃ T' : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2,
      HasCurveDeriv V (fun U => (r U)⁻¹ • f U) T' := by
  refine ⟨(r V)⁻¹ • T + ((-((r V) ^ 2)⁻¹) • R).smulRight (f V), fun g γ hγ0 hγ => ?_⟩
  have h1 := hr g γ hγ0 hγ
  have h2 := hf g γ hγ0 hγ
  have h3 := h1.fun_inv (by rw [hγ0]; exact h0)
  have h4 := h3.fun_smul h2
  simp only [hγ0] at h4
  refine HasDerivAt.congr_deriv h4 ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul]
  congr 2
  field_simp
end CurveDerivatives
section Mean
variable {L n k j : ℕ}
private theorem det_listProd_eq_one (V : Edge L n k j → ComplexMatrix2)
    (hV : ∀ b, Matrix.det (V b) = 1) (l : List (Edge L n k j)) :
    Matrix.det ((l.map V).prod) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.det_list_prod_eq_one <;> assumption
private theorem cpow_half_sq (x : ℂ) : (x ^ (1 / 2 : ℂ)) ^ 2 = x := by
  have := Complex.cpow_nat_inv_pow x (n := 2) (by norm_num)
  simpa using this
private theorem sq_mem_slitPlane_of_near_one {r : ℂ} (h : ‖r - 1‖ < 1 / 2) :
    r ^ 2 ∈ Complex.slitPlane := by
  have hre : 1 / 2 < r.re := by
    have h1 := Complex.abs_re_le_norm (r - 1)
    have h2 := abs_lt.1 (lt_of_le_of_lt h1 h)
    simp at h2
    linarith [h2.1]
  rw [Complex.mem_slitPlane_iff]
  by_cases hy : r.im = 0
  · left
    simp [pow_two, Complex.mul_re, hy]
    nlinarith
  · right
    simp only [pow_two, Complex.mul_im]
    intro h0
    have : r.re * r.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact hy h1
private def expVelocity (V B : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  open Classical in
  fun b => if b.IsPositivelyOriented then (Complex.I • B b) * V b
    else -((V b.opposite)⁻¹ * ((Complex.I • B b.opposite) * V b.opposite) * (V b.opposite)⁻¹)
private theorem expVelocity_add_smul (V : Edge L n k j → ComplexMatrix2) (z : ℂ)
    (B B' : Edge L n k j → ComplexMatrix2) :
    expVelocity V (z • B + B') = z • expVelocity V B + expVelocity V B' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [expVelocity, if_pos hb, Pi.add_apply, Pi.smul_apply, smul_add, add_mul]
    rw [smul_comm, smul_mul_assoc]
  · simp only [expVelocity, if_neg hb, Pi.add_apply, Pi.smul_apply, smul_add, add_mul, mul_add,
      neg_add, smul_neg]
    rw [smul_comm Complex.I z (B b.opposite)]
    simp only [smul_mul_assoc, mul_smul_comm]
private theorem expTwist_curve (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {V : Edge L n k j → ComplexMatrix2} (hdet : ∀ b, Matrix.det (V b) = 1)
    (hrev : ∀ b, V b.opposite = (V b)⁻¹) (B : Edge L n k j → ComplexMatrix2) :
    (PeriodicLattice.expTwist ((0 : ℂ) • B) V = V) ∧
    ∀ b, HasDerivAt (fun t : ℂ => PeriodicLattice.expTwist (t • B) V b) (expVelocity V B b) 0 := by
  have hexp : ∀ b : Edge L n k j,
      HasDerivAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B) b))
      (Complex.I • B b) 0 := by
    intro b
    have hY : HasDerivAt (fun t : ℂ => Complex.I • t • B b) (Complex.I • B b) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).smul_const (B b)).const_smul Complex.I
      exact HasDerivAt.congr_deriv this (by simp)
    have hY0 : (fun t : ℂ => Complex.I • t • B b) 0 = 0 := by simp
    exact (hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hY hY hY).2.2 hY0
  have hexp0 : ∀ b : Edge L n k j, ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B) b) = 1 := by
    intro b
    simp [ComplexMatrix2.matExp]
  refine ⟨?_, fun b => ?_⟩
  · funext b
    unfold PeriodicLattice.expTwist
    by_cases hb : b.IsPositivelyOriented
    · simp only [if_pos hb, hexp0, one_mul]
    · simp only [if_neg hb, hexp0, one_mul]
      rw [hrev b]
      exact Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet b]; exact isUnit_one)
  · have hY : ∀ b : Edge L n k j,
        HasDerivAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b)
        ((Complex.I • B b) * V b) 0 := fun b => (hexp b).mul_const (V b)
    by_cases hb : b.IsPositivelyOriented
    · have e : (fun t : ℂ => PeriodicLattice.expTwist (t • B) V b) =
          fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b := by
        funext t
        simp only [PeriodicLattice.expTwist, if_pos hb]
      rw [e]
      have e' : expVelocity V B b = (Complex.I • B b) * V b := by
        simp only [expVelocity, if_pos hb]
      rw [e']
      exact hY b
    · have e : (fun t : ℂ => PeriodicLattice.expTwist (t • B) V b) =
          fun t : ℂ => (ComplexMatrix2.matExp (Complex.I • (t • B) b.opposite) * V b.opposite)⁻¹ := by
        funext t
        simp only [PeriodicLattice.expTwist, if_neg hb]
      rw [e]
      have e' : expVelocity V B b = -((V b.opposite)⁻¹ *
          ((Complex.I • B b.opposite) * V b.opposite) * (V b.opposite)⁻¹) := by
        simp only [expVelocity, if_neg hb]
      rw [e']
      have hu : IsUnit (Matrix.det (V b.opposite)) := by rw [hdet]; exact isUnit_one
      have h1 := hasCurveDeriv_inv (ι := Unit) (V := fun _ => V b.opposite) hd
        (f := fun U => U ())
        (T := LinearMap.proj (R := ℂ) (φ := fun _ : Unit => ComplexMatrix2) ())
        (hasCurveDeriv_eval ()) hu (fun _ => (Complex.I • B b.opposite) * V b.opposite)
        (fun t _ => ComplexMatrix2.matExp (Complex.I • (t • B) b.opposite) * V b.opposite)
        (by funext _; simp only [hexp0, one_mul]) (fun _ => hY b.opposite)
      exact HasDerivAt.congr_deriv h1 (by simp)
private theorem normalizedMean_curve (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    [Finite (Vertex L n k j)] {V : Edge L n k j → ComplexMatrix2} (hdet : ∀ b, Matrix.det (V b) = 1)
    (c : Edge L n k (j + 1)) (hr0 : meanRadius V c ≠ 0) (hr1 : ‖meanRadius V c - 1‖ < 1 / 2) :
    (∃ T, HasCurveDeriv V (fun U => meanRadius U c) T) ∧
      ∃ T, HasCurveDeriv V (fun U => normalizedMean U c) T := by
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  set S := hfin.toFinset with hSdef
  set w : ℂ := (1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L with hw
  have hmean : ∀ U : Edge L n k j → ComplexMatrix2, contourMean U c =
      w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy U c x π := by
    intro U
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hinvhol : ∀ l : List (Edge L n k j), PeriodicLattice.pathHolonomy V l =
      (l.map V).prod := fun _ => rfl
  have hhol : ∀ l : List (Edge L n k j), ∃ T,
      HasCurveDeriv V (fun U => PeriodicLattice.pathHolonomy U l) T :=
    fun l => exists_hasCurveDeriv_listProd l
  have hcvd : ∀ x π, ∃ T, HasCurveDeriv V (fun U => contourHolonomy U c x π) T := by
    intro x π
    obtain ⟨D₁, h₁⟩ := hhol (contourLeg c.source x π)
    obtain ⟨D₂, h₂⟩ := hhol (PeriodicLattice.crossingPath c x)
    obtain ⟨D₃, h₃⟩ := hhol (contourLeg c.target (PeriodicLattice.shiftAcross c x) π)
    have hu3 : IsUnit (Matrix.det (PeriodicLattice.pathHolonomy V
        (contourLeg c.target (PeriodicLattice.shiftAcross c x) π))) := by
      rw [hinvhol, det_listProd_eq_one V hdet]
      exact isUnit_one
    exact ⟨_, hasCurveDeriv_mul (hasCurveDeriv_mul h₁ h₂) (hasCurveDeriv_inv hd h₃ hu3)⟩
  choose Dc hDc using hcvd
  have hM : HasCurveDeriv V (fun U => contourMean U c)
      (w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), Dc x π) := by
    have h1 := hasCurveDeriv_const_smul w (hasCurveDeriv_sum S fun x _ =>
      hasCurveDeriv_sum Finset.univ fun π _ => hDc x π)
    intro g γ h0 hγ
    have h2 := h1 g γ h0 hγ
    have e : (fun t => contourMean (γ t) c) = fun t => w • ∑ x ∈ S,
        ∑ π : Equiv.Perm (Fin 4), contourHolonomy (γ t) c x π := by
      funext t
      exact hmean _
    rw [e]
    exact h2
  have hsq : meanRadius V c ^ 2 = Matrix.det (contourMean V c) := cpow_half_sq _
  have hslit : Matrix.det (contourMean V c) ∈ Complex.slitPlane :=
    hsq ▸ sq_mem_slitPlane_of_near_one hr1
  obtain ⟨Dd, hDd⟩ := exists_hasCurveDeriv_det hM
  obtain ⟨Dr, hDr⟩ := exists_hasCurveDeriv_sqrt hDd hslit
  obtain ⟨Du, hDu⟩ := exists_hasCurveDeriv_inv_smul hDr hM hr0
  exact ⟨⟨Dr, hDr⟩, ⟨Du, hDu⟩⟩
private theorem det_normalizedMean (U : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1))
    (h : meanRadius U c ≠ 0) : Matrix.det (normalizedMean U c) = 1 := by
  have hsq : meanRadius U c ^ 2 = Matrix.det (contourMean U c) := cpow_half_sq _
  rw [normalizedMean, Matrix.det_smul, Fintype.card_fin, inv_pow, hsq.symm, inv_mul_cancel₀]
  exact pow_ne_zero 2 h
private theorem logDeriv_normalizedMean
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    [Finite (Vertex L n k j)] {V : Edge L n k j → ComplexMatrix2} (hdet : ∀ b, Matrix.det (V b) = 1)
    (hrev : ∀ b, V b.opposite = (V b)⁻¹) (c : Edge L n k (j + 1))
    (hr0 : meanRadius V c ≠ 0) (hr1 : ‖meanRadius V c - 1‖ < 1 / 2) :
    ∃ T : (Edge L n k j → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2, ∀ B : Edge L n k j → ComplexMatrix2,
      logDirectionalDeriv ℂ (fun X => normalizedMean (PeriodicLattice.expTwist X V) c)
        (normalizedMean V c) B =
          Complex.I⁻¹ • (T (expVelocity V B) * (normalizedMean V c)⁻¹) ∧
      T (expVelocity V B) * (normalizedMean V c)⁻¹ ∈ ComplexMatrix2.traceless := by
  obtain ⟨⟨R, hR⟩, ⟨T, hT⟩⟩ := normalizedMean_curve hd hdet c hr0 hr1
  refine ⟨T, fun B => ?_⟩
  obtain ⟨h0, hγ⟩ := expTwist_curve hd hdet hrev B
  set W := normalizedMean V c with hW
  have hWdet : Matrix.det W = 1 := det_normalizedMean V c hr0
  have hWu : IsUnit (Matrix.det W) := by rw [hWdet]; exact isUnit_one
  have hu := hT (expVelocity V B) (fun t : ℂ => PeriodicLattice.expTwist (t • B) V) h0 hγ
  have hr := hR (expVelocity V B) (fun t : ℂ => PeriodicLattice.expTwist (t • B) V) h0 hγ
  have hX : HasDerivAt
      (fun t : ℂ => normalizedMean (PeriodicLattice.expTwist (t • B) V) c * W⁻¹)
      (T (expVelocity V B) * W⁻¹) 0 := hu.mul_const W⁻¹
  have hX0 : (fun t : ℂ => normalizedMean (PeriodicLattice.expTwist (t • B) V) c * W⁻¹) 0 = 1 := by
    show normalizedMean (PeriodicLattice.expTwist ((0 : ℂ) • B) V) c * W⁻¹ = 1
    rw [h0]
    exact Matrix.mul_nonsing_inv _ hWu
  have hne : {t : ℂ | meanRadius (PeriodicLattice.expTwist (t • B) V) c ≠ 0} ∈ nhds (0 : ℂ) := by
    have h1 := hr.continuousAt
    have h2 : meanRadius (PeriodicLattice.expTwist ((0 : ℂ) • B) V) c ≠ 0 := by rw [h0]; exact hr0
    exact h1.eventually_ne h2
  obtain ⟨-, -, hlog, hsl⟩ := (hd.2 _ _ _ _ _ _ _ hne hX hX hX).2.1 hX0
  have hdet1 : ∀ t ∈ {t : ℂ | meanRadius (PeriodicLattice.expTwist (t • B) V) c ≠ 0},
      Matrix.det (normalizedMean (PeriodicLattice.expTwist (t • B) V) c * W⁻¹) = 1 := by
    intro t ht
    rw [Matrix.det_mul, det_normalizedMean _ c ht, one_mul, Matrix.det_nonsing_inv, hWdet]
    simp
  refine ⟨?_, (hsl hdet1).2⟩
  unfold logDirectionalDeriv
  have e := hlog.deriv
  congr 1
private theorem finite_vertex (hf : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Finite (Vertex L n k j) := by
  have : Finite (Edge L n k j) := Set.finite_univ_iff.1 ((hf L hL k j hj).1 n hn).2.1
  exact Finite.of_injective
    (fun x : Vertex L n k j => PeriodicLattice.Bond.forwardFrom x 0) fun _ _ h =>
    congrArg PeriodicLattice.Bond.source h
end Mean
theorem holds (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hnear : NormalizedMeanNearOne) (hf : BondSetFields.ProductStructureHolds)
    (ho : PeriodicLattice.BondEndpointsOrientation.Statement) :
    HolDifferentialLinear := by
  intro L hL
  obtain ⟨ρ, hρ, hN⟩ := hnear L hL
  refine ⟨ρ, hρ, fun n k j hn hj V hV hVρ => ?_⟩
  have := finite_vertex (k := k) (j := j) hf hL hn hj.le
  have hdet : ∀ b, Matrix.det (V b) = 1 := fun b => hV.1 b (Set.mem_univ b)
  have hrev : ∀ b, V b.opposite = (V b)⁻¹ := fun b => hV.2 b (Set.mem_univ b)
  have hval : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      ∃ T : (Edge L n k j → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2,
      ∀ B : Edge L n k j → ComplexMatrix2,
      holLeftDifferential normalizedMean V B c =
        Complex.I⁻¹ • (T (expVelocity V B) * (normalizedMean V c)⁻¹) ∧
      T (expVelocity V B) * (normalizedMean V c)⁻¹ ∈ ComplexMatrix2.traceless := by
    intro c hc
    obtain ⟨hr0, hr1, -⟩ := hN n k j hn hj V hV hVρ c hc
    obtain ⟨T, hT⟩ := logDeriv_normalizedMean hd hdet hrev c hr0 hr1
    refine ⟨T, fun B => ⟨?_, (hT B).2⟩⟩
    have e : holLeftDifferential normalizedMean V B c =
        logDirectionalDeriv ℂ (fun X => normalizedMean (PeriodicLattice.expTwist X V) c)
          (normalizedMean V c) B := if_pos hc
    rw [e]
    exact (hT B).1
  have hlin : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      ∀ (z : ℂ) (B B' : Edge L n k j → ComplexMatrix2),
      holLeftDifferential normalizedMean V (z • B + B') c =
        z • holLeftDifferential normalizedMean V B c +
          holLeftDifferential normalizedMean V B' c := by
    intro c hc z B B'
    obtain ⟨T, hT⟩ := hval c hc
    rw [(hT _).1, (hT _).1, (hT _).1, expVelocity_add_smul, map_add, map_smul, add_mul,
      smul_mul_assoc, smul_add, smul_comm]
  refine ⟨fun B c hc => ?_, fun z B B' => ?_⟩
  · obtain ⟨T, hT⟩ := hval c hc
    rw [(hT B).1]
    exact ComplexMatrix2.traceless.smul_mem _ (hT B).2
  · funext b
    by_cases hb : b.IsPositivelyOriented
    · exact hlin b hb z B B'
    · have hx := ((ho ⟨L, hL, ⟨k, by omega⟩, ⟨n, hn⟩⟩ (j + 1) hj).2.2.2 b).2.2.2.2.2
      have hrb : b.opposite.IsPositivelyOriented := by
        rcases hx with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h hb
        · exact h
      have e : ∀ X : Edge L n k j → ComplexMatrix2, holLeftDifferential normalizedMean V X b =
          -holLeftDifferential normalizedMean V X b.opposite := by
        intro X
        have e₁ : holLeftDifferential normalizedMean V X b =
            -(logDirectionalDeriv ℂ
              (fun Y => normalizedMean (PeriodicLattice.expTwist Y V) b.opposite)
              (normalizedMean V b.opposite) X) := if_neg hb
        have e₂ : holLeftDifferential normalizedMean V X b.opposite =
            logDirectionalDeriv ℂ
              (fun Y => normalizedMean (PeriodicLattice.expTwist Y V) b.opposite)
              (normalizedMean V b.opposite) X := if_pos hrb
        rw [e₁, e₂]
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [e, e B, e B', hlin _ hrb z B B', neg_add, smul_neg]
end YangMills.Construction.RunningCouplingSlope.HolDifferentialLinearProof
end
