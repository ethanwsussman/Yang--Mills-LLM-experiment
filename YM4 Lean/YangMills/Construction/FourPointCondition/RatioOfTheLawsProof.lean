import YangMills.Construction.FourPointCondition.ConnectedFunctionsAreHomogeneous
import YangMills.Construction.FourPointCondition.ConnectedLawOfACollinearQuadruple
import YangMills.Construction.FourPointCondition.LevelReadByTheTwoPointFunction
import YangMills.Construction.FourPointCondition.RatioOfTheLaws
import YangMills.Construction.FourPointCondition.TuplesOfAQuadrupleOfTheClass
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
private theorem ratio_quotient_bounds {x al r Lw A σ e' Pc E : ℝ} (hx : 0 < x) (hal : al ∈ Icc (3 / 4 : ℝ) (5 / 4))
    (hA : 0 < A) (he : |e'| ≤ 1 / 4) (hσ : σ = (al / x) ^ 2 * A * (1 + e')) (hPc : 0 < Pc)
    (hlaw : |x ^ 4 * (Pc * r) - al ^ 4 * (Pc * Lw)| ≤ E) (hE : E ≤ Pc * (1 / 2 * (al ^ 4 * Lw)))
    (hL : 0 ≤ Lw) :
    8 / 25 * Lw ≤ r * A ^ 2 / σ ^ 2 ∧ r * A ^ 2 / σ ^ 2 ≤ 8 / 3 * Lw := by
  obtain ⟨he1, he2⟩ := abs_le.1 he
  have hal0 : 0 < al := by linarith [hal.1]
  have hM : 0 ≤ al ^ 4 * Lw := by positivity
  have hw0 : 0 < 1 + e' := by linarith
  set w : ℝ := (1 + e') ^ 2 with hw
  have hw1 : 9 / 16 ≤ w := by nlinarith
  have hw2 : w ≤ 25 / 16 := by nlinarith
  have hfac : x ^ 4 * (Pc * r) - al ^ 4 * (Pc * Lw) = Pc * (x ^ 4 * r - al ^ 4 * Lw) := by ring
  rw [hfac, abs_mul, abs_of_pos hPc] at hlaw
  have hb : |x ^ 4 * r - al ^ 4 * Lw| ≤ 1 / 2 * (al ^ 4 * Lw) := by
    have := hlaw.trans hE
    exact le_of_mul_le_mul_left this hPc
  obtain ⟨b1, b2⟩ := abs_le.1 hb
  have hval : r * A ^ 2 / σ ^ 2 = x ^ 4 * r / (al ^ 4 * w) := by
    rw [hσ, hw]
    have := hx.ne'
    have := hal0.ne'
    have := hA.ne'
    have := hw0.ne'
    field_simp
  have hden : 0 < al ^ 4 * w := by positivity
  rw [hval, le_div_iff₀ hden, div_le_iff₀ hden]
  constructor
  · have : 8 / 25 * Lw * (al ^ 4 * w) = 8 / 25 * w * (al ^ 4 * Lw) := by ring
    rw [this]
    nlinarith
  · have : 8 / 3 * Lw * (al ^ 4 * w) = 8 / 3 * w * (al ^ 4 * Lw) := by ring
    rw [this]
    nlinarith
private theorem exp_log_cube_le_volume {x σ S d a : ℝ} (hx : 16 ≤ x) (hxσ : x ≤ 1 / σ) (hd : 0 < d) (ha : 0 < a)
    (hsites : 1 ≤ d / a) (hvol : Real.exp (Real.log (1 / σ) ^ 3) ≤ S / d) :
    Real.exp (Real.log x ^ 3) ≤ S / a := by
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog : Real.log x ≤ Real.log (1 / σ) := Real.log_le_log hx0 hxσ
  have h3 : Real.log x ^ 3 ≤ Real.log (1 / σ) ^ 3 := pow_le_pow_left₀ hlog0 hlog 3
  have hS : 0 ≤ S / d := (Real.exp_pos _).le.trans hvol
  have e : S / a = S / d * (d / a) := by
    field_simp
  rw [e]
  calc Real.exp (Real.log x ^ 3) ≤ Real.exp (Real.log (1 / σ) ^ 3) := Real.exp_le_exp.2 h3
    _ ≤ S / d := hvol
    _ ≤ S / d * (d / a) := le_mul_of_one_le_right hS hsites
private theorem cumulantRatio_at_quadruple (hH : connectedFunctionsHomogeneousStatement)
    (hT : normalizedQuadrupleIsTestTuple) (hB : gaussianFourPointCollinear)
    {ℓ : TorusLumps.StepParameters} {vt C X : ℝ} {K : ℕ+} {β d : ℝ} {sides : Set ℝ} {φ ψ : (Fin 4 → ℝ) → ℝ} {k : ℕ}
    {σ al e : ℝ} (hv0 : 0 < vt) (hX : 16 ≤ X) (hβ : 0 < β)
    (R : LevelReadAtScale ℓ vt C X K β d sides φ ψ k σ al e) (s : Conventions.StandingParameters) (hsL : s.L = ℓ.side)
    (hsK : s.K = K) (hvol : Real.exp (Real.log (1 / σ) ^ 3) ≤ PeriodicLattice.torusSide s.L s.m / d)
    (f : Fin 4 → s.Torus → ℝ) (hf : f ∈ QuadrupleClasses.collinearQuadsTorus s d vt) :
    ∃ r : ℝ, PeriodicLattice.torusUrsellFunction s.L s.m s.K β f = r ∧
      8 / 25 * ResponseInTheExpansion.gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide s.L s.m) f ≤
        r * (9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernel φ ψ) ^ 2 / σ ^ 2 ∧
      r * (9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernel φ ψ) ^ 2 / σ ^ 2 ≤
        8 / 3 * ResponseInTheExpansion.gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide s.L s.m) f := by
  obtain ⟨L', hs, K', m'⟩ := s
  dsimp only at hsL hsK hvol ⊢
  subst hsL hsK
  have hB' := hB ⟨ℓ.side, hs, K', m'⟩ d vt f hf
  have hQ := hf.1
  obtain ⟨hsc, h40, hfL, -⟩ := id hQ
  have hd : 0 < d := hsc.1
  obtain ⟨hpos, htup, -⟩ := hT ℓ K' m' hs d vt f hQ
  set x : ℝ := (TorusLumps.couplingFlow ℓ β k).1 with hxdef
  have hx16 : 16 ≤ x := hX.trans (R.coupling_ge k le_rfl)
  have hx0 : 0 < x := by linarith
  have hLpos : 0 < (ℓ.side : ℝ) := by
    have := hs.2
    exact_mod_cast (by omega : 0 < ℓ.side)
  have ha : 0 < levelMesh ℓ.side K' k := by
    unfold levelMesh PeriodicLattice.meshSize
    exact zpow_pos hLpos _
  have hroom := exp_log_cube_le_volume hx16 R.coupling_le hd ha R.one_le_sites hvol
  have hlaw := R.laws m' hroom 3 (Or.inr rfl) (fun i x => (TestFunctions.uniformNorm (f i))⁻¹ * f i x) htup
  set c : Fin 4 → ℝ := fun i => (TestFunctions.uniformNorm (f i))⁻¹ with hc
  have hlip : ∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus (f i) := fun i => (hfL i).1
  obtain ⟨him, hscale⟩ := hH.1 ⟨ℓ.side, hs, K', m'⟩ β 4 f c hβ (by norm_num) hlip
  have hlawc : ResponseInTheExpansion.gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide ℓ.side m') (fun i x => c i * f i x) =
      (∏ i, c i) * ResponseInTheExpansion.gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide ℓ.side m') f := hH.2 _ 3 f c
  set P : ℝ := ∏ i, TestFunctions.uniformNorm (f i) with hP
  have hP0 : 0 < P := Finset.prod_pos fun i _ => hpos i
  have hPc : (∏ i, c i) = P⁻¹ := by
    rw [hP, Finset.prod_inv_distrib]
  set Lw : ℝ := ResponseInTheExpansion.gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide ℓ.side m') f with hLw
  set r : ℝ := (PeriodicLattice.torusUrsellFunction ℓ.side m' K' β f).re with hr
  have hSr : PeriodicLattice.torusUrsellFunction ℓ.side m' K' β f = (r : ℂ) := by
    apply Complex.ext
    · simp [hr]
    · simpa using him
  refine ⟨r, hSr, ?_⟩
  have hal := R.al_mem
  have hal0 : 0 < al := by linarith [hal.1]
  have hPinv : 0 < P⁻¹ := inv_pos.2 hP0
  set A4 : ℝ := 27 * Real.pi ^ (-8 : ℤ) * (25 / 4 : ℝ) ^ (-16 : ℤ) with hA4
  have hA40 : 0 < A4 := by
    rw [hA4]
    positivity
  have hLlow : A4 * vt ^ 4 * P ≤ Lw := hB'.2.1
  have hLw0 : 0 ≤ Lw := le_trans (by positivity) hLlow
  have hlawR : |x ^ 4 * (P⁻¹ * r) - al ^ 4 * (P⁻¹ * Lw)| ≤ C * (x ^ (-(1 / 100 : ℝ)) + e) := by
    have e1 : PeriodicLattice.torusUrsellFunction ℓ.side m' K' β (fun i x => c i * f i x) = ((P⁻¹ * r : ℝ) : ℂ) := by
      have : PeriodicLattice.torusUrsellFunction ℓ.side m' K' β (fun i x => c i * f i x) =
          ((∏ i, c i : ℝ) : ℂ) * PeriodicLattice.torusUrsellFunction ℓ.side m' K' β f := hscale
      rw [this, hSr, hPc]
      push_cast
      ring
    have e2 : (((x ^ (3 + 1) : ℝ)) : ℂ) * ((P⁻¹ * r : ℝ) : ℂ) -
        ((al ^ (3 + 1) * (P⁻¹ * Lw) : ℝ) : ℂ) =
        ((x ^ 4 * (P⁻¹ * r) - al ^ 4 * (P⁻¹ * Lw) : ℝ) : ℂ) := by
      push_cast
      ring
    have h := hlaw
    rw [e1, hlawc, hPc, e2, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hmargin : C * (x ^ (-(1 / 100 : ℝ)) + e) ≤ P⁻¹ * (1 / 2 * (al ^ 4 * Lw)) := by
    have h1 := R.margin_le
    have h2 : lawsMargin vt ≤ (2 : ℝ)⁻¹ ^ 4 * ((3 / 4 : ℝ) ^ 4 * (A4 * vt ^ 4)) := by
      unfold lawsMargin
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    have h3 : (3 / 4 : ℝ) ^ 4 ≤ al ^ 4 := pow_le_pow_left₀ (by norm_num) hal.1 4
    have h4 : A4 * vt ^ 4 ≤ P⁻¹ * Lw := by
      rw [inv_mul_eq_div, le_div_iff₀ hP0]
      exact hLlow
    have h5 : (3 / 4 : ℝ) ^ 4 * (A4 * vt ^ 4) ≤ al ^ 4 * (P⁻¹ * Lw) :=
      mul_le_mul h3 h4 (by positivity) (by positivity)
    have h6 : 0 ≤ al ^ 4 * (P⁻¹ * Lw) := by positivity
    have e3 : P⁻¹ * (1 / 2 * (al ^ 4 * Lw)) = 1 / 2 * (al ^ 4 * (P⁻¹ * Lw)) := by ring
    rw [e3]
    have e4 : (2 : ℝ)⁻¹ ^ 4 = 1 / 16 := by norm_num
    rw [e4] at h2
    linarith
  have hkernel : 0 < 9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernel φ ψ := by
    have h1 := R.kernel_mem.1
    have h2 : 0 < TestPairs.kernelLowerConst * vt ^ 2 := by
      unfold TestPairs.kernelLowerConst
      positivity
    have h3 : 0 < TestFunctions.inverseEighthKernel φ ψ := by linarith
    positivity
  obtain ⟨e', he', hσ⟩ := R.σ_eq
  exact ratio_quotient_bounds (r := r) (Lw := Lw) (Pc := P⁻¹) hx0 hal hkernel he' hσ hPinv hlawR hmargin hLw0
theorem cumulantRatio_holds (hLevel : levelReadByTwoPointStatement)
    (hH : connectedFunctionsHomogeneousStatement) (hT : normalizedQuadrupleIsTestTuple)
    (hB : gaussianFourPointCollinear) : cumulantRatioStatement := by
  intro a ha
  obtain ⟨L₁, r₁, c₁, p₁, h₁⟩ := hLevel a ha
  refine ⟨L₁, r₁, c₁, p₁, fun L hodd hL' T hTa hTL hD hC hHf hr hc => ?_⟩
  obtain ⟨y₁, g₁⟩ := h₁ L hodd hL' T hTa hTL hD hC hHf hr hc
  refine ⟨y₁, fun y hy hR hW => ?_⟩
  obtain ⟨-, G⟩ := g₁ y hy hR hW
  intro vt hv0 hv1
  obtain ⟨βv, nv, δv, C, X, hnv, hδ, -, hX, G'⟩ := G vt hv0 hv1
  refine ⟨max βv 1, nv, δv, hnv, hδ, fun K β d sides φ ψ hs hpair h1 h2 hβ hn hsm => ?_⟩
  obtain ⟨k, σ, al, e, R⟩ := G' K β d sides φ ψ hs hpair h1 h2 ((le_max_left _ _).trans hβ) hn hsm
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hβ)
  exact ⟨σ, R.σ_pos, R.twoPoint_eq, fun s hsL hsK hvol f hf =>
    cumulantRatio_at_quadruple hH hT hB hv0 hX hβ0 R s hsL hsK hvol f hf⟩
end YangMills.Construction.FourPointCondition
end
