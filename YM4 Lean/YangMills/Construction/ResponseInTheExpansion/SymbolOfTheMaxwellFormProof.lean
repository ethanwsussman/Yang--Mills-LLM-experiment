import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.RunningCouplingSlope.MomentOfASumOfFormsProof
import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficientProof
import YangMills.Construction.Towers.TheAbelianOperatorsAreLocalFamiliesProof
import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.ResponseInTheExpansion.GradientsUnderTheMaxwellForm
import YangMills.Construction.ResponseInTheExpansion.KernelOfTheMaxwellForm
import YangMills.Construction.ResponseInTheExpansion.SecondMomentOfTheMaxwellKernel
import YangMills.Construction.ResponseInTheExpansion.SymbolOfTheMaxwellForm
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace YangMills.Construction
noncomputable section
open TorusFields LinearResponse WeightedResponses RenormalizationStepParameters
namespace ResponseInTheExpansion
section
variable {N : ℕ} [NeZero N]
private def bondKernelSymbol (K : TorusBond N → TorusBond N → ℝ) (p : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ∑ x : TorusSite N, (K ((0 : TorusSite N), μ) (x, ν) : ℂ) * Complex.exp (Complex.I * (∑ i, p i *
    (torusDisplacement (0 : TorusSite N) x i + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) : ℝ))
private def dualCharacter (j x : TorusSite N) : ℂ := ∏ i, (ZMod.stdAddChar (j i * x i) : ℂ)
private theorem dualCharacter_add (j x y : TorusSite N) :
    dualCharacter j (x + y) = dualCharacter j x * dualCharacter j y := by
  simp only [dualCharacter, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]
private theorem dualCharacter_zero (j : TorusSite N) : dualCharacter j 0 = 1 := by
  simp [dualCharacter]
private theorem norm_dualCharacter (j x : TorusSite N) : ‖dualCharacter j x‖ = 1 := by
  simp [dualCharacter, norm_prod, AddChar.norm_apply]
private theorem dualCharacter_conj_mul (j x : TorusSite N) :
    (starRingEnd ℂ) (dualCharacter j x) * dualCharacter j x = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_dualCharacter]
  simp
private theorem dualCharacter_neg (j x : TorusSite N) :
    dualCharacter j (-x) = (starRingEnd ℂ) (dualCharacter j x) := by
  have h1 : dualCharacter j (-x) * dualCharacter j x = 1 := by
    rw [← dualCharacter_add]; simp [dualCharacter_zero]
  have h2 := dualCharacter_conj_mul j x
  have h3 : dualCharacter j x ≠ 0 := by
    intro h; have := norm_dualCharacter j x; simp [h] at this
  exact mul_right_cancel₀ h3 (h1.trans h2.symm)
private theorem sum_dualCharacter (x : TorusSite N) :
    ∑ j : TorusSite N, dualCharacter j x = if x = 0 then (N : ℂ) ^ 4 else 0 := by
  have h1 : ∑ j : TorusSite N, dualCharacter j x = ∏ i, ∑ a : ZMod N, (ZMod.stdAddChar (a * x i) : ℂ) := by
    rw [Finset.prod_univ_sum]
    simp [dualCharacter, Fintype.piFinset_univ]
  have h2 : ∀ i, ∑ a : ZMod N, (ZMod.stdAddChar (a * x i) : ℂ) = if x i = 0 then (N : ℂ) else 0 := by
    intro i
    have := AddChar.sum_mulShift (x i) (ZMod.isPrimitive_stdAddChar N)
    simpa [ZMod.card] using this
  rw [h1]
  simp only [h2]
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (funext hc)
    rw [if_neg hx]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
private theorem dualCharacter_siteOfInt (d e : Fin 4 → ℤ) :
    dualCharacter (siteOfInt d : TorusSite N) (siteOfInt e) =
    Complex.exp (Complex.I * (∑ i, (2 * Real.pi * (d i : ℝ) / (N : ℝ)) * (e i : ℝ) : ℝ)) := by
  have h : ∀ i, (ZMod.stdAddChar ((siteOfInt d : TorusSite N) i * (siteOfInt e : TorusSite N) i) : ℂ) =
      Complex.exp (Complex.I * (((2 * Real.pi * (d i : ℝ) / (N : ℝ)) * (e i : ℝ) : ℝ) : ℂ)) := by
    intro i
    have : (siteOfInt d : TorusSite N) i * (siteOfInt e : TorusSite N) i = ((d i * e i : ℤ) : ZMod N) := by
      simp [siteOfInt]
    rw [this, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  simp only [dualCharacter, h]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
end
section
variable {N : ℕ} [NeZero N]
private theorem exists_int_displacement (x y : TorusSite N) :
    ∃ d : Fin 4 → ℤ, (∀ i, torusDisplacement x y i = (d i : ℝ)) ∧ (siteOfInt d : TorusSite N) = y - x := by
  refine ⟨fun i => ((y i).val : ℤ) - ((x i).val : ℤ) -
    (N : ℤ) * round ((((y i).val : ℝ) - ((x i).val : ℝ)) / (N : ℝ)), ?_, ?_⟩
  · intro i
    simp [torusDisplacement, circleSub]
  · funext i
    simp [siteOfInt]
private def IsMomentumAt (j : TorusSite N) (q : Fin 4 → ℝ) : Prop :=
  ∃ d : Fin 4 → ℤ, (siteOfInt d : TorusSite N) = j ∧ ∀ i, q i = 2 * Real.pi * (d i : ℝ) / (N : ℝ)
private theorem isMomentumAt_dualMomentum (j : TorusSite N) : IsMomentumAt j (dualMomentum j) :=
  ⟨fun i => (j i).valMinAbs, by funext i; simp [siteOfInt], fun i => by simp [dualMomentum]⟩
private theorem dualCharacter_eq_exp {j : TorusSite N} {q : Fin 4 → ℝ} (hq : IsMomentumAt j q) (e : Fin 4 → ℤ) :
    dualCharacter j (siteOfInt e) = Complex.exp (Complex.I * (∑ i, q i * (e i : ℝ) : ℝ)) := by
  obtain ⟨d, rfl, hd⟩ := hq
  rw [dualCharacter_siteOfInt]
  simp only [hd]
private def halfPhase (q : Fin 4 → ℝ) (m : Fin 4) : ℂ := Complex.exp (Complex.I * ((q m / 2 : ℝ) : ℂ))
private theorem halfPhase_ne_zero (q : Fin 4 → ℝ) (m : Fin 4) : halfPhase q m ≠ 0 := Complex.exp_ne_zero _
private theorem norm_halfPhase (q : Fin 4 → ℝ) (m : Fin 4) : ‖halfPhase q m‖ = 1 := by
  rw [halfPhase, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _
private theorem conj_halfPhase (q : Fin 4 → ℝ) (m : Fin 4) :
    (starRingEnd ℂ) (halfPhase q m) = (halfPhase q m)⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, norm_halfPhase]
  simp
private theorem halfPhase_sub_inv (q : Fin 4 → ℝ) (m : Fin 4) :
    halfPhase q m - (halfPhase q m)⁻¹ = Complex.I * (latticeMomentum q m : ℂ) := by
  have h1 : (halfPhase q m)⁻¹ = Complex.exp (-(Complex.I * ((q m / 2 : ℝ) : ℂ))) := by
    rw [halfPhase, Complex.exp_neg]
  rw [h1, halfPhase, latticeMomentum]
  set t : ℂ := ((q m / 2 : ℝ) : ℂ) with ht
  have e1 : Complex.exp (Complex.I * t) = Complex.cos t + Complex.sin t * Complex.I := by
    rw [mul_comm]; exact Complex.exp_mul_I _
  have e2 : Complex.exp (-(Complex.I * t)) = Complex.cos t - Complex.sin t * Complex.I := by
    rw [show -(Complex.I * t) = (-t) * Complex.I by ring, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]
    ring
  rw [e1, e2, ht]
  push_cast
  ring
private theorem siteOfInt_single (m : Fin 4) : (siteOfInt (Pi.single m 1) : TorusSite N) = unitStep N m := by
  funext i
  by_cases h : i = m
  · subst h; simp [siteOfInt, unitStep]
  · simp [siteOfInt, unitStep, Pi.single_apply, h]
private theorem dualCharacter_unitStep {j : TorusSite N} {q : Fin 4 → ℝ} (hq : IsMomentumAt j q) (m : Fin 4) :
    dualCharacter j (unitStep N m) = halfPhase q m ^ 2 := by
  rw [← siteOfInt_single, dualCharacter_eq_exp hq, halfPhase, ← Complex.exp_nat_mul]
  congr 1
  have : (∑ i, q i * (((Pi.single m 1 : Fin 4 → ℤ) i : ℤ) : ℝ)) = q m := by
    simp [Pi.single_apply]
  rw [this]
  push_cast
  ring
private theorem bondPhase_eq {j : TorusSite N} {q : Fin 4 → ℝ} (hq : IsMomentumAt j q) (w : TorusSite N)
    (μ ν : Fin 4) :
    Complex.exp (Complex.I * (∑ i, q i *
      (torusDisplacement (0 : TorusSite N) w i + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) : ℝ)) =
      dualCharacter j w * halfPhase q ν * (halfPhase q μ)⁻¹ := by
  obtain ⟨d, hd, hw⟩ := exists_int_displacement (0 : TorusSite N) w
  rw [sub_zero] at hw
  have h1 : (∑ i, q i * (torusDisplacement (0 : TorusSite N) w i +
      ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2)) =
      (∑ i, q i * (d i : ℝ)) + q ν / 2 - q μ / 2 := by
    have : ∀ i, q i * (torusDisplacement (0 : TorusSite N) w i +
        ((if i = ν then (1 : ℝ) else 0) - (if i = μ then 1 else 0)) / 2) =
        q i * (d i : ℝ) + (if i = ν then q i / 2 else 0) - (if i = μ then q i / 2 else 0) := by
      intro i
      rw [hd i]
      split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [h1, ← hw, dualCharacter_eq_exp hq, halfPhase, halfPhase, ← Complex.exp_neg, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring
private structure IsGaugeKernel (K : TorusBond N → TorusBond N → ℝ) (c : ℝ) : Prop where
  symm : ∀ b b', K b b' = K b' b
  translate : ∀ (u : TorusSite N) (b b' : TorusBond N), K (b.1 + u, b.2) (b'.1 + u, b'.2) = K b b'
  reflect : ∀ b b' : TorusBond N,
    K (-(b.1 + unitStep N b.2), b.2) (-(b'.1 + unitStep N b'.2), b'.2) = K b b'
  gauge : ∀ (φ : TorusSite N → ℝ) (b : TorusBond N), ∑ b', K b b' * latticeGradient φ b' = 0
  coercive : ∀ A : TorusBond N → ℝ,
    c * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)), WeightedResponses.curl A p ^ 2 ≤
    ∑ b, ∑ b', A b * K b b' * A b'
variable {K : TorusBond N → TorusBond N → ℝ} {c : ℝ}
private theorem symbol_eq_sum {j : TorusSite N} {q : Fin 4 → ℝ} (hq : IsMomentumAt j q) (μ ν : Fin 4) :
    bondKernelSymbol K q μ ν =
      ∑ w : TorusSite N, (K ((0 : TorusSite N), μ) (w, ν) : ℂ) *
        (dualCharacter j w * halfPhase q ν * (halfPhase q μ)⁻¹) := by
  simp only [bondKernelSymbol, bondPhase_eq hq]
private theorem kernel_apply_wave
    (hS : ∀ (u : TorusSite N) (b b' : TorusBond N), K (b.1 + u, b.2) (b'.1 + u, b'.2) = K b b')
    {j : TorusSite N} {q : Fin 4 → ℝ} (hq : IsMomentumAt j q) (x : TorusSite N) (μ ν : Fin 4) :
    ∑ y : TorusSite N, (K (x, μ) (y, ν) : ℂ) * (dualCharacter j y * halfPhase q ν) =
      bondKernelSymbol K q μ ν * (dualCharacter j x * halfPhase q μ) := by
  rw [symbol_eq_sum hq, Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight x)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h := hS x ((0 : TorusSite N), μ) (w, ν)
  simp only [zero_add] at h
  simp only [Equiv.coe_addRight, h, dualCharacter_add]
  have := halfPhase_ne_zero q μ
  field_simp
private theorem symbol_ward (hK : IsGaugeKernel K c) {j : TorusSite N} {q : Fin 4 → ℝ} (hq : IsMomentumAt j q)
    (μ : Fin 4) : ∑ ν, bondKernelSymbol K q μ ν * (latticeMomentum q ν : ℂ) = 0 := by
  have hg : ∑ b' : TorusBond N, (K ((0 : TorusSite N), μ) b' : ℂ) *
      (dualCharacter j (b'.1 + unitStep N b'.2) - dualCharacter j b'.1) = 0 := by
    have h1 := hK.gauge (fun x => (dualCharacter j x).re) ((0 : TorusSite N), μ)
    have h2 := hK.gauge (fun x => (dualCharacter j x).im) ((0 : TorusSite N), μ)
    have : ∀ b' : TorusBond N, (K ((0 : TorusSite N), μ) b' : ℂ) *
        (dualCharacter j (b'.1 + unitStep N b'.2) - dualCharacter j b'.1) =
        ((K ((0 : TorusSite N), μ) b' * latticeGradient (fun x => (dualCharacter j x).re) b' : ℝ) : ℂ) +
        ((K ((0 : TorusSite N), μ) b' * latticeGradient (fun x => (dualCharacter j x).im) b' : ℝ) : ℂ) *
          Complex.I := by
      intro b'
      apply Complex.ext <;> simp [latticeGradient]
    simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, h1, h2]
    simp
  rw [Fintype.sum_prod_type, Finset.sum_comm] at hg
  have h3 : ∀ ν, ∑ y : TorusSite N, (K ((0 : TorusSite N), μ) (y, ν) : ℂ) *
      (dualCharacter j (y + unitStep N ν) - dualCharacter j y) =
      bondKernelSymbol K q μ ν * halfPhase q μ * (Complex.I * (latticeMomentum q ν : ℂ)) := by
    intro ν
    have h4 := kernel_apply_wave hK.translate hq (0 : TorusSite N) μ ν
    rw [dualCharacter_zero, one_mul] at h4
    rw [← h4, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [dualCharacter_add, dualCharacter_unitStep hq, ← halfPhase_sub_inv]
    have := halfPhase_ne_zero q ν
    field_simp
  simp only [h3] at hg
  have h5 : halfPhase q μ * Complex.I * ∑ ν, bondKernelSymbol K q μ ν * (latticeMomentum q ν : ℂ) = 0 := by
    rw [Finset.mul_sum, ← hg]
    refine Finset.sum_congr rfl fun ν _ => ?_
    ring
  have h6 : halfPhase q μ * Complex.I ≠ 0 := mul_ne_zero (halfPhase_ne_zero q μ) Complex.I_ne_zero
  exact (mul_eq_zero.mp h5).resolve_left h6
private def complexCurl (f : TorusBond N → ℂ) (p : TorusPlaquette N) : ℂ :=
  f (p.1, p.2.1) + f (p.1 + unitStep N p.2.1, p.2.2) - f (p.1 + unitStep N p.2.2, p.2.1) - f (p.1, p.2.2)
private theorem complexCurl_re (f : TorusBond N → ℂ) (p : TorusPlaquette N) :
    (complexCurl f p).re = WeightedResponses.curl (fun b => (f b).re) p := by
  simp [complexCurl, WeightedResponses.curl]
private theorem complexCurl_im (f : TorusBond N → ℂ) (p : TorusPlaquette N) :
    (complexCurl f p).im = WeightedResponses.curl (fun b => (f b).im) p := by
  simp [complexCurl, WeightedResponses.curl]
private def planeWave (j : TorusSite N) (q : Fin 4 → ℝ) (v : Fin 4 → ℂ) : TorusBond N → ℂ :=
  fun b => dualCharacter j b.1 * halfPhase q b.2 * v b.2
private theorem complexCurl_planeWave {j : TorusSite N} {q : Fin 4 → ℝ} (hq : IsMomentumAt j q)
    (v : Fin 4 → ℂ) (x : TorusSite N) (μ ν : Fin 4) :
    complexCurl (planeWave j q v) (x, μ, ν) = dualCharacter j x * halfPhase q μ * halfPhase q ν *
      (Complex.I * ((latticeMomentum q μ : ℂ) * v ν - (latticeMomentum q ν : ℂ) * v μ)) := by
  have e1 : Complex.I * (latticeMomentum q μ : ℂ) = halfPhase q μ - (halfPhase q μ)⁻¹ :=
    (halfPhase_sub_inv q μ).symm
  have e2 : Complex.I * (latticeMomentum q ν : ℂ) = halfPhase q ν - (halfPhase q ν)⁻¹ :=
    (halfPhase_sub_inv q ν).symm
  have a := halfPhase_ne_zero q μ
  have b := halfPhase_ne_zero q ν
  have : Complex.I * ((latticeMomentum q μ : ℂ) * v ν - (latticeMomentum q ν : ℂ) * v μ) =
      (halfPhase q μ - (halfPhase q μ)⁻¹) * v ν - (halfPhase q ν - (halfPhase q ν)⁻¹) * v μ := by
    rw [← e1, ← e2]; ring
  rw [this]
  simp only [complexCurl, planeWave, dualCharacter_add, dualCharacter_unitStep hq]
  field_simp
  ring
private theorem sum_plaquettes_axes (g : Fin 4 → Fin 4 → ℝ) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)), g p.2.1 p.2.2 =
      (N : ℝ) ^ 4 * ∑ μ, ∑ ν, if μ < ν then g μ ν else 0 := by
  have h1 : plaquettesIn (Finset.univ : Finset (TorusSite N)) =
      Finset.univ.filter fun p : TorusPlaquette N => p.2.1 < p.2.2 := by
    ext p
    simp [plaquettesIn]
  rw [h1, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [ZMod.card]
private theorem quadratic_planeWave
    (hS : ∀ (u : TorusSite N) (b b' : TorusBond N), K (b.1 + u, b.2) (b'.1 + u, b'.2) = K b b')
    {j : TorusSite N} {q : Fin 4 → ℝ} (hq : IsMomentumAt j q) (v : Fin 4 → ℂ) :
    ∑ b, ∑ b', (starRingEnd ℂ) (planeWave j q v b) * (K b b' : ℂ) * planeWave j q v b' =
      (N : ℂ) ^ 4 * ∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * bondKernelSymbol K q μ ν * v ν := by
  have h1 : ∀ (x : TorusSite N) (μ : Fin 4), ∑ b' : TorusBond N, (starRingEnd ℂ) (planeWave j q v (x, μ)) *
      (K (x, μ) b' : ℂ) * planeWave j q v b' =
      ∑ ν, (starRingEnd ℂ) (v μ) * bondKernelSymbol K q μ ν * v ν := by
    intro x μ
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have h2 := kernel_apply_wave hS hq x μ ν
    have h3 : ∑ y : TorusSite N, (starRingEnd ℂ) (planeWave j q v (x, μ)) * (K (x, μ) (y, ν) : ℂ) *
        planeWave j q v (y, ν) = (starRingEnd ℂ) (planeWave j q v (x, μ)) * v ν *
        ∑ y : TorusSite N, (K (x, μ) (y, ν) : ℂ) * (dualCharacter j y * halfPhase q ν) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [planeWave]
      ring
    rw [h3, h2]
    simp only [planeWave, map_mul, conj_halfPhase]
    have h4 := dualCharacter_conj_mul j x
    have h5 := halfPhase_ne_zero q μ
    calc _ = ((starRingEnd ℂ) (dualCharacter j x) * dualCharacter j x) * ((halfPhase q μ)⁻¹ * halfPhase q μ) *
          ((starRingEnd ℂ) (v μ) * bondKernelSymbol K q μ ν * v ν) := by ring
      _ = _ := by rw [h4, inv_mul_cancel₀ h5]; ring
  rw [Fintype.sum_prod_type]
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [ZMod.card]
private theorem re_hermitian_quadratic (f : TorusBond N → ℂ) :
    (∑ b, ∑ b', (starRingEnd ℂ) (f b) * (K b b' : ℂ) * f b').re =
      (∑ b, ∑ b', (f b).re * K b b' * (f b').re) + ∑ b, ∑ b', (f b).im * K b b' * (f b').im := by
  simp only [Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  simp
private theorem lagrange_identity_four (a : Fin 4 → ℝ) (v : Fin 4 → ℂ) :
    (∑ μ, ∑ ν, if μ < ν then ‖(a μ : ℂ) * v ν - (a ν : ℂ) * v μ‖ ^ 2 else 0) +
      ‖∑ μ, (a μ : ℂ) * v μ‖ ^ 2 = (∑ i, a i ^ 2) * ∑ m, ‖v m‖ ^ 2 := by
  have hn : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  simp only [hn, Fin.sum_univ_four]
  simp
  ring
private theorem re_rank_one_form (a : Fin 4 → ℝ) (v : Fin 4 → ℂ) :
    (∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * ((a μ * a ν : ℝ) : ℂ) * v ν).re = ‖∑ μ, (a μ : ℂ) * v μ‖ ^ 2 := by
  have hn : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  simp only [hn, Fin.sum_univ_four]
  simp
  ring
private theorem symbol_lower_curl (hK : IsGaugeKernel K c) (hc : 0 ≤ c) {j : TorusSite N} {q : Fin 4 → ℝ}
    (hq : IsMomentumAt j q) (v : Fin 4 → ℂ) :
    c * ∑ μ, ∑ ν, (if μ < ν then
        ‖(latticeMomentum q μ : ℂ) * v ν - (latticeMomentum q ν : ℂ) * v μ‖ ^ 2 else 0) ≤
      (∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * bondKernelSymbol K q μ ν * v ν).re := by
  set f := planeWave j q v with hf
  have h1 := re_hermitian_quadratic (K := K) f
  rw [quadratic_planeWave hK.translate hq v] at h1
  have hcurl : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)),
      WeightedResponses.curl (fun b => (f b).re) p ^ 2 + WeightedResponses.curl (fun b => (f b).im) p ^ 2 =
        ‖(latticeMomentum q p.2.1 : ℂ) * v p.2.2 - (latticeMomentum q p.2.2 : ℂ) * v p.2.1‖ ^ 2 := by
    rintro ⟨x, μ, ν⟩ -
    have hz : ∀ z : ℂ, z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := fun z => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [← complexCurl_re, ← complexCurl_im, hz, complexCurl_planeWave hq]
    simp [norm_dualCharacter, norm_halfPhase]
  have h2 := hK.coercive (fun b => (f b).re)
  have h3 := hK.coercive (fun b => (f b).im)
  have h4 : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)), WeightedResponses.curl (fun b => (f b).re) p ^ 2 +
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)), WeightedResponses.curl (fun b => (f b).im) p ^ 2 =
      (N : ℝ) ^ 4 * ∑ μ, ∑ ν, (if μ < ν then
        ‖(latticeMomentum q μ : ℂ) * v ν - (latticeMomentum q ν : ℂ) * v μ‖ ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hcurl]
    exact sum_plaquettes_axes fun μ ν => ‖(latticeMomentum q μ : ℂ) * v ν - (latticeMomentum q ν : ℂ) * v μ‖ ^ 2
  have h5 : ((N : ℂ) ^ 4 * ∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * bondKernelSymbol K q μ ν * v ν).re =
      (N : ℝ) ^ 4 * (∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * bondKernelSymbol K q μ ν * v ν).re := by
    rw [show ((N : ℂ) ^ 4) = (((N : ℝ) ^ 4 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  rw [h5] at h1
  have hN : (0 : ℝ) < (N : ℝ) ^ 4 := by
    have : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have h6 : (N : ℝ) ^ 4 * (c * ∑ μ, ∑ ν, (if μ < ν then
        ‖(latticeMomentum q μ : ℂ) * v ν - (latticeMomentum q ν : ℂ) * v μ‖ ^ 2 else 0)) ≤
      (N : ℝ) ^ 4 * (∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * bondKernelSymbol K q μ ν * v ν).re := by
    rw [h1]
    nlinarith [h2, h3, h4]
  exact le_of_mul_le_mul_left h6 hN
private theorem symbolWithGradient_lower (hK : IsGaugeKernel K c) (hc : 0 ≤ c) {j : TorusSite N}
    {q : Fin 4 → ℝ} (hq : IsMomentumAt j q) (v : Fin 4 → ℂ) :
    min c 1 * sqNorm (latticeMomentum q) * ∑ m, ‖v m‖ ^ 2 ≤
      (∑ m, ∑ m', (starRingEnd ℂ) (v m) * symbolWithGradient (bondKernelSymbol K) q m m' * v m').re := by
  have h1 := symbol_lower_curl hK hc hq v
  have h2 := re_rank_one_form (latticeMomentum q) v
  have h3 := lagrange_identity_four (latticeMomentum q) v
  have h4 : (∑ m, ∑ m', (starRingEnd ℂ) (v m) * symbolWithGradient (bondKernelSymbol K) q m m' * v m') =
      (∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * bondKernelSymbol K q μ ν * v ν) +
      ∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * ((latticeMomentum q μ * latticeMomentum q ν : ℝ) : ℂ) * v ν := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    simp only [symbolWithGradient]
    ring
  rw [h4, Complex.add_re, h2]
  set X := ∑ μ, ∑ ν, (if μ < ν then
        ‖(latticeMomentum q μ : ℂ) * v ν - (latticeMomentum q ν : ℂ) * v μ‖ ^ 2 else 0) with hX
  set Y := ‖∑ μ, (latticeMomentum q μ : ℂ) * v μ‖ ^ 2 with hY
  have hX0 : 0 ≤ X := by
    refine Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => ?_
    split_ifs <;> positivity
  have h5 : sqNorm (latticeMomentum q) * ∑ m, ‖v m‖ ^ 2 = X + Y := by
    rw [sqNorm]; exact h3.symm
  have h6 : min c 1 ≤ c := min_le_left _ _
  have h7 : min c 1 ≤ 1 := min_le_right _ _
  calc min c 1 * sqNorm (latticeMomentum q) * ∑ m, ‖v m‖ ^ 2
      = min c 1 * (X + Y) := by rw [mul_assoc, h5]
    _ ≤ c * X + Y := by nlinarith
    _ ≤ _ := by linarith
end
section
variable {N : ℕ} [NeZero N] {K : TorusBond N → TorusBond N → ℝ} {c : ℝ}
private theorem symbol_conj_eq (hK : IsGaugeKernel K c) {j : TorusSite N} {q : Fin 4 → ℝ} (hq : IsMomentumAt j q)
    (μ ν : Fin 4) : (starRingEnd ℂ) (bondKernelSymbol K q μ ν) = bondKernelSymbol K q μ ν := by
  have hinv : Function.Involutive fun w : TorusSite N => -(w + unitStep N ν) + unitStep N μ := by
    intro w
    simp only
    abel
  have hKw : ∀ w : TorusSite N, K ((0 : TorusSite N), μ) (w, ν) =
      K ((0 : TorusSite N), μ) (-(w + unitStep N ν) + unitStep N μ, ν) := by
    intro w
    have h1 := hK.reflect ((0 : TorusSite N), μ) (w, ν)
    have h2 := hK.translate (unitStep N μ) (-((0 : TorusSite N) + unitStep N μ), μ) (-(w + unitStep N ν), ν)
    simp only [zero_add, neg_add_cancel] at h1 h2
    rw [h2, h1]
  have h3 : bondKernelSymbol K q μ ν = ∑ w : TorusSite N, (K ((0 : TorusSite N), μ) (w, ν) : ℂ) *
      (dualCharacter j (-(w + unitStep N ν) + unitStep N μ) * halfPhase q ν * (halfPhase q μ)⁻¹) := by
    rw [symbol_eq_sum hq, ← Equiv.sum_comp hinv.toPerm]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Function.Involutive.coe_toPerm]
    rw [← hKw w]
  conv_rhs => rw [h3]
  conv_lhs => rw [symbol_eq_sum hq, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have ha := halfPhase_ne_zero q μ
  have hb := halfPhase_ne_zero q ν
  simp only [map_mul, Complex.conj_ofReal, map_inv₀, conj_halfPhase, dualCharacter_add, dualCharacter_neg,
    dualCharacter_unitStep hq, map_pow]
  field_simp
private theorem symbol_comm (hK : IsGaugeKernel K c) {j : TorusSite N} {q : Fin 4 → ℝ} (hq : IsMomentumAt j q)
    (μ ν : Fin 4) : bondKernelSymbol K q ν μ = bondKernelSymbol K q μ ν := by
  rw [← symbol_conj_eq hK hq μ ν, symbol_eq_sum hq, symbol_eq_sum hq, map_sum,
    ← Equiv.sum_comp (Equiv.neg (TorusSite N))]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hKw : K ((0 : TorusSite N), ν) (-w, μ) = K ((0 : TorusSite N), μ) (w, ν) := by
    have h2 := hK.translate w (-w, μ) ((0 : TorusSite N), ν)
    simp only [neg_add_cancel, zero_add] at h2
    rw [hK.symm, ← h2]
  simp only [Equiv.neg_apply, hKw, map_mul, Complex.conj_ofReal, map_inv₀, conj_halfPhase, dualCharacter_neg,
    inv_inv]
  ring
private theorem sqNorm_latticeMomentum_pos {j : TorusSite N} (hj : j ≠ 0) :
    0 < sqNorm (latticeMomentum (dualMomentum j)) := by
  obtain ⟨i, hi⟩ : ∃ i, j i ≠ 0 := by
    by_contra hc
    exact hj (funext fun i => by simpa using not_not.mp (fun h => hc ⟨i, h⟩))
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ha : (j i).valMinAbs ≠ 0 := by simpa using hi
  have hb : (((j i).valMinAbs).natAbs : ℝ) ≤ (N : ℝ) / 2 := by
    have := ZMod.natAbs_valMinAbs_le (j i)
    have h2 : (2 * ((j i).valMinAbs).natAbs) ≤ N := by omega
    have h3 : (2 * (((j i).valMinAbs).natAbs : ℝ)) ≤ N := by exact_mod_cast h2
    linarith
  set a : ℝ := ((j i).valMinAbs : ℝ) with ha'
  have hab : |a| ≤ (N : ℝ) / 2 := by
    rw [ha', ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact hb
  have hs : Real.sin (dualMomentum j i / 2) ≠ 0 := by
    have ht : dualMomentum j i / 2 = Real.pi * a / N := by
      simp only [dualMomentum, ha']
      ring
    have hlt : |Real.pi * a / N| < Real.pi := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hN, div_lt_iff₀ hN]
      nlinarith [Real.pi_pos]
    have := abs_lt.mp hlt
    rw [ht, Ne, Real.sin_eq_zero_iff_of_lt_of_lt this.1 this.2]
    have ha0 : a ≠ 0 := by rw [ha']; exact_mod_cast ha
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero ha0) hN.ne'
  have h1 : 0 < latticeMomentum (dualMomentum j) i ^ 2 := by
    have : latticeMomentum (dualMomentum j) i ≠ 0 := mul_ne_zero two_ne_zero hs
    positivity
  exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun i => latticeMomentum (dualMomentum j) i ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ i))
private abbrev gradientMatrix (K : TorusBond N → TorusBond N → ℝ) (j : TorusSite N) : Matrix (Fin 4) (Fin 4) ℂ :=
  symbolWithGradient (bondKernelSymbol K) (dualMomentum j)
private theorem gradientMatrix_symm (hK : IsGaugeKernel K c) (j : TorusSite N) (μ ν : Fin 4) :
    gradientMatrix K j μ ν = gradientMatrix K j ν μ := by
  simp only [gradientMatrix, symbolWithGradient]
  rw [symbol_comm hK (isMomentumAt_dualMomentum j) ν μ, mul_comm (latticeMomentum _ ν)]
private theorem gradientMatrix_det_isUnit (hK : IsGaugeKernel K c) (hc : 0 < c) {j : TorusSite N} (hj : j ≠ 0) :
    IsUnit (gradientMatrix K j).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := symbolWithGradient_lower hK hc.le (isMomentumAt_dualMomentum j) v
  have h2 : (∑ m, ∑ m', (starRingEnd ℂ) (v m) *
      symbolWithGradient (bondKernelSymbol K) (dualMomentum j) m m' * v m') = 0 := by
    refine Finset.sum_eq_zero fun m _ => ?_
    have h3 := congrFun hMv m
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h3
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h3, mul_zero]
  rw [h2] at h1
  have h4 := sqNorm_latticeMomentum_pos hj
  have h5 : 0 < ∑ m, ‖v m‖ ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hc'
      exact hv (funext fun i => by simpa using not_not.mp (fun h => hc' ⟨i, h⟩))
    have : 0 < ‖v i‖ ^ 2 := by positivity
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i))
  have : 0 < min c 1 * sqNorm (latticeMomentum (dualMomentum j)) * ∑ m, ‖v m‖ ^ 2 := by positivity
  simp at h1
  linarith
private theorem symbol_solves (hK : IsGaugeKernel K c) (hc : 0 < c) {j : TorusSite N} (hj : j ≠ 0)
    (u : Fin 4 → ℂ) (hu : ∑ m, (latticeMomentum (dualMomentum j) m : ℂ) * u m = 0) (m : Fin 4) :
    ∑ ν, bondKernelSymbol K (dualMomentum j) m ν * ((gradientMatrix K j)⁻¹.mulVec u) ν = u m := by
  set M := gradientMatrix K j with hM
  set g := M⁻¹.mulVec u with hg
  set a := latticeMomentum (dualMomentum j) with ha
  have hq := isMomentumAt_dualMomentum j
  have hMg : M.mulVec g = u := by
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (gradientMatrix_det_isUnit hK hc hj),
      Matrix.one_mulVec]
  have hMg' : ∀ m, ∑ ν, M m ν * g ν = u m := fun m => congrFun hMg m
  have hrow : ∀ ν, ∑ m, (a m : ℂ) * M m ν = (a ν : ℂ) * (sqNorm a : ℂ) := by
    intro ν
    have h1 : ∀ m, (a m : ℂ) * M m ν = bondKernelSymbol K (dualMomentum j) ν m * (a m : ℂ) +
        (a ν : ℂ) * ((a m ^ 2 : ℝ) : ℂ) := by
      intro m
      rw [hM, gradientMatrix_symm hK j m ν]
      simp only [gradientMatrix, symbolWithGradient]
      push_cast
      ring
    have hw : ∑ m, bondKernelSymbol K (dualMomentum j) ν m * (a m : ℂ) = 0 := symbol_ward hK hq ν
    simp only [h1, Finset.sum_add_distrib, hw, zero_add, ← Finset.mul_sum, sqNorm]
    push_cast
    rfl
  have hdot : (sqNorm a : ℂ) * ∑ ν, (a ν : ℂ) * g ν = 0 := by
    calc (sqNorm a : ℂ) * ∑ ν, (a ν : ℂ) * g ν
        = ∑ ν, (∑ m, (a m : ℂ) * M m ν) * g ν := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [hrow]; ring
      _ = ∑ m, (a m : ℂ) * ∑ ν, M m ν * g ν := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun ν _ => ?_
          ring
      _ = 0 := by simp only [hMg', hu]
  have hne : (sqNorm a : ℂ) ≠ 0 := by
    exact_mod_cast (sqNorm_latticeMomentum_pos hj).ne'
  have hdot0 := (mul_eq_zero.mp hdot).resolve_left hne
  have h2 : ∑ ν, bondKernelSymbol K (dualMomentum j) m ν * g ν =
      (∑ ν, M m ν * g ν) - (a m : ℂ) * ∑ ν, (a ν : ℂ) * g ν := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [hM, gradientMatrix, symbolWithGradient]
    push_cast
    ring
  rw [h2, hdot0, hMg']
  ring
private theorem curlSymbol_dot (p : Fin 4 → ℝ) (ρ τ : Fin 4) :
    ∑ m, (latticeMomentum p m : ℂ) * curlSymbol p ρ τ m = 0 := by
  simp only [curlSymbol]
  have : ∀ m, (latticeMomentum p m : ℂ) * (Complex.I * (((if m = τ then latticeMomentum p ρ else 0) -
      (if m = ρ then latticeMomentum p τ else 0) : ℝ) : ℂ)) =
      (if m = τ then (latticeMomentum p m : ℂ) * Complex.I * (latticeMomentum p ρ : ℂ) else 0) -
        (if m = ρ then (latticeMomentum p m : ℂ) * Complex.I * (latticeMomentum p τ : ℂ) else 0) := by
    intro m
    split_ifs <;> push_cast <;> ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
private def plaquettePhase (j : TorusSite N) (p : TorusPlaquette N) : ℂ :=
  dualCharacter j p.1 * halfPhase (dualMomentum j) p.2.1 * halfPhase (dualMomentum j) p.2.2
private def solutionVector (K : TorusBond N → TorusBond N → ℝ) (j : TorusSite N) (p : TorusPlaquette N) :
    Fin 4 → ℂ :=
  (gradientMatrix K j)⁻¹.mulVec (curlSymbol (dualMomentum j) p.2.1 p.2.2)
private def solutionForm (K : TorusBond N → TorusBond N → ℝ) (p : TorusPlaquette N) (b : TorusBond N) : ℂ :=
  ((N : ℂ) ^ 4)⁻¹ * ∑ j ∈ (Finset.univ : Finset (TorusSite N)).erase 0, plaquettePhase j p *
    (starRingEnd ℂ) (dualCharacter j b.1 * halfPhase (dualMomentum j) b.2) * solutionVector K j p b.2
private theorem kernel_apply_conjWave (hK : IsGaugeKernel K c) (j : TorusSite N) (x : TorusSite N)
    (μ ν : Fin 4) :
    ∑ y : TorusSite N, (K (x, μ) (y, ν) : ℂ) * (starRingEnd ℂ) (dualCharacter j y * halfPhase (dualMomentum j) ν) =
      bondKernelSymbol K (dualMomentum j) μ ν *
        (starRingEnd ℂ) (dualCharacter j x * halfPhase (dualMomentum j) μ) := by
  have hq := isMomentumAt_dualMomentum j
  have h := congrArg (starRingEnd ℂ) (kernel_apply_wave hK.translate hq x μ ν)
  rw [map_sum, map_mul, symbol_conj_eq hK hq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp
private theorem kernel_apply_solution (hK : IsGaugeKernel K c) (hc : 0 < c) (p : TorusPlaquette N)
    (x : TorusSite N) (m : Fin 4) :
    ∑ b' : TorusBond N, (K (x, m) b' : ℂ) * solutionForm K p b' = ((N : ℂ) ^ 4)⁻¹ * ∑ j : TorusSite N,
      (starRingEnd ℂ) (dualCharacter j x * halfPhase (dualMomentum j) m) *
        (plaquettePhase j p * curlSymbol (dualMomentum j) p.2.1 p.2.2 m) := by
  have h1 : ∀ j ∈ (Finset.univ : Finset (TorusSite N)).erase 0,
      ∑ b' : TorusBond N, (K (x, m) b' : ℂ) * (plaquettePhase j p *
        (starRingEnd ℂ) (dualCharacter j b'.1 * halfPhase (dualMomentum j) b'.2) * solutionVector K j p b'.2) =
      (starRingEnd ℂ) (dualCharacter j x * halfPhase (dualMomentum j) m) *
        (plaquettePhase j p * curlSymbol (dualMomentum j) p.2.1 p.2.2 m) := by
    intro j hj
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    have h2 := symbol_solves hK hc hj0 _ (curlSymbol_dot (dualMomentum j) p.2.1 p.2.2) m
    rw [← h2, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have h3 := kernel_apply_conjWave hK j x m ν
    calc _ = (∑ y : TorusSite N, (K (x, m) (y, ν) : ℂ) *
          (starRingEnd ℂ) (dualCharacter j y * halfPhase (dualMomentum j) ν)) *
          (plaquettePhase j p * solutionVector K j p ν) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = _ := by
          rw [h3]
          simp only [solutionVector]
          ring
  have h0 : curlSymbol (dualMomentum (0 : TorusSite N)) p.2.1 p.2.2 m = 0 := by
    simp [curlSymbol, dualMomentum, latticeMomentum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : TorusSite N)), h0]
  simp only [mul_zero, zero_add]
  rw [← Finset.sum_congr rfl h1, Finset.sum_comm]
  simp only [solutionForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end
section
variable {N : ℕ} [NeZero N] {K : TorusBond N → TorusBond N → ℝ} {c : ℝ}
private theorem fourier_inversion (x z : TorusSite N) (m n : Fin 4) :
    ((N : ℂ) ^ 4)⁻¹ * ∑ j : TorusSite N, (starRingEnd ℂ) (dualCharacter j x * halfPhase (dualMomentum j) m) *
      planeWave j (dualMomentum j) (Pi.single m 1) (z, n) = if (z, n) = (x, m) then 1 else 0 := by
  have hN : ((N : ℂ) ^ 4) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne N)
  by_cases hn : n = m
  · subst hn
    have h1 : ∀ j : TorusSite N, (starRingEnd ℂ) (dualCharacter j x * halfPhase (dualMomentum j) n) *
        planeWave j (dualMomentum j) (Pi.single n 1) (z, n) = dualCharacter j (z + -x) := by
      intro j
      have ha := halfPhase_ne_zero (dualMomentum j) n
      simp only [planeWave, map_mul, conj_halfPhase, dualCharacter_add, dualCharacter_neg, Pi.single_eq_same]
      field_simp
    simp only [h1, sum_dualCharacter]
    by_cases hz : z = x
    · subst hz
      simp [hN]
    · have : z + -x ≠ 0 := by
        intro h; exact hz (add_neg_eq_zero.mp h)
      simp [this, hz]
  · have h1 : ∀ j : TorusSite N, (starRingEnd ℂ) (dualCharacter j x * halfPhase (dualMomentum j) m) *
        planeWave j (dualMomentum j) (Pi.single m 1) (z, n) = 0 := by
      intro j
      simp [planeWave, Pi.single_apply, hn]
    rw [Finset.sum_eq_zero fun j _ => h1 j]
    simp [hn]
private theorem pairing_solution (hK : IsGaugeKernel K c) (hc : 0 < c) (p : TorusPlaquette N)
    (B : TorusBond N → ℝ) :
    ∑ b, ∑ b', (B b : ℂ) * (K b b' : ℂ) * solutionForm K p b' = (WeightedResponses.curl B p : ℂ) := by
  obtain ⟨y, ρ, τ⟩ := p
  have h1 : ∀ b : TorusBond N, ∑ b', (B b : ℂ) * (K b b' : ℂ) * solutionForm K (y, ρ, τ) b' =
      (B b : ℂ) * ((if (y, ρ) = b then 1 else 0) + (if (y + unitStep N ρ, τ) = b then 1 else 0) -
        (if (y + unitStep N τ, ρ) = b then 1 else 0) - (if (y, τ) = b then 1 else 0)) := by
    rintro ⟨x, m⟩
    simp only [mul_assoc]
    rw [← Finset.mul_sum, kernel_apply_solution hK hc]
    congr 1
    have hw : ∀ j : TorusSite N, plaquettePhase j (y, ρ, τ) * curlSymbol (dualMomentum j) ρ τ m =
        complexCurl (planeWave j (dualMomentum j) (Pi.single m 1)) (y, ρ, τ) := by
      intro j
      rw [complexCurl_planeWave (isMomentumAt_dualMomentum j)]
      simp only [plaquettePhase, curlSymbol]
      congr 1
      congr 1
      by_cases h1 : m = τ <;> by_cases h2 : m = ρ <;> simp [h1, h2, Pi.single_apply, eq_comm] <;>
        split_ifs <;> simp
    simp only [hw, complexCurl, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      fourier_inversion]
  simp only [h1]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [WeightedResponses.curl]
private def bilinearForm (K : TorusBond N → TorusBond N → ℝ) (A B : TorusBond N → ℝ) : ℝ :=
  ∑ b, ∑ b', A b * K b b' * B b'
private theorem pairing_solution_re (hK : IsGaugeKernel K c) (hc : 0 < c) (p : TorusPlaquette N)
    (B : TorusBond N → ℝ) :
    bilinearForm K B (fun b => (solutionForm K p b).re) = WeightedResponses.curl B p := by
  have h := congrArg Complex.re (pairing_solution hK hc p B)
  simp only [Complex.re_sum, Complex.ofReal_re] at h
  rw [← h]
  simp [bilinearForm, Complex.mul_re]
private theorem pairing_solution_im (hK : IsGaugeKernel K c) (hc : 0 < c) (p : TorusPlaquette N)
    (B : TorusBond N → ℝ) :
    bilinearForm K B (fun b => (solutionForm K p b).im) = 0 := by
  have h := congrArg Complex.im (pairing_solution hK hc p B)
  simp only [Complex.im_sum, Complex.ofReal_im] at h
  rw [← h]
  simp [bilinearForm, Complex.mul_im]
private theorem bilinearForm_comm (hK : IsGaugeKernel K c) (A B : TorusBond N → ℝ) :
    bilinearForm K A B = bilinearForm K B A := by
  simp only [bilinearForm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [hK.symm]
  ring
private theorem bilinearForm_self_nonneg (hK : IsGaugeKernel K c) (hc : 0 < c) (A : TorusBond N → ℝ) :
    0 ≤ bilinearForm K A A := by
  have h := hK.coercive A
  have h1 : 0 ≤ ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)), WeightedResponses.curl A p ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  exact le_trans (mul_nonneg hc.le h1) h
private theorem bilinearForm_sub_sub (hK : IsGaugeKernel K c) (A H : TorusBond N → ℝ) :
    bilinearForm K (fun b => A b - H b) (fun b => A b - H b) =
      bilinearForm K A A - 2 * bilinearForm K A H + bilinearForm K H H := by
  have h := bilinearForm_comm hK H A
  have : bilinearForm K (fun b => A b - H b) (fun b => A b - H b) =
      bilinearForm K A A - bilinearForm K A H - bilinearForm K H A + bilinearForm K H H := by
    simp only [bilinearForm, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [this, h]
  ring
private theorem entry_zero_of_quadratic_zero {ι : Type} [DecidableEq ι] (P : Finset ι) (D : ι → ι → ℝ)
    (hs : ∀ a b, D a b = D b a)
    (hq : ∀ h : ι → ℝ, ∑ a ∈ P, ∑ b ∈ P, h a * D a b * h b = 0) {a b : ι} (ha : a ∈ P) (hb : b ∈ P) :
    D a b = 0 := by
  have hd : ∀ x ∈ P, D x x = 0 := by
    intro x hx
    have := hq fun y => if y = x then 1 else 0
    simpa [hx, Finset.sum_ite_eq'] using this
  have h1 := hq fun y => (if y = a then 1 else 0) + (if y = b then 1 else 0)
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero,
    Finset.sum_ite_eq', ha, hb, if_true, Finset.sum_const_zero] at h1
  rw [hd a ha, hd b hb, hs b a] at h1
  linarith
private theorem sum_conj_curlSymbol (q : Fin 4 → ℝ) (μ ν : Fin 4) (g : Fin 4 → ℂ) :
    ∑ m, (starRingEnd ℂ) (curlSymbol q μ ν m) * g m =
      Complex.I * ((latticeMomentum q ν : ℂ) * g μ - (latticeMomentum q μ : ℂ) * g ν) := by
  have : ∀ m, (starRingEnd ℂ) (curlSymbol q μ ν m) * g m =
      (if m = μ then Complex.I * (latticeMomentum q ν : ℂ) * g m else 0) -
        (if m = ν then Complex.I * (latticeMomentum q μ : ℂ) * g m else 0) := by
    intro m
    simp only [curlSymbol, map_mul, Complex.conj_I, Complex.conj_ofReal]
    split_ifs <;> push_cast <;> ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
private theorem plaquettePhase_centre (j : TorusSite N) (p p' : TorusPlaquette N) :
    Complex.exp (Complex.I * (∑ i, dualMomentum j i * plaquetteCentreDisplacement p p' i : ℝ)) =
      plaquettePhase j p' * (starRingEnd ℂ) (plaquettePhase j p) := by
  have hq := isMomentumAt_dualMomentum j
  obtain ⟨d, hd, hw⟩ := exists_int_displacement p.1 p'.1
  set q := dualMomentum j with hqd
  have h1 : (∑ i, q i * plaquetteCentreDisplacement p p' i) =
      (∑ i, q i * (d i : ℝ)) + q p'.2.1 / 2 + q p'.2.2 / 2 - q p.2.1 / 2 - q p.2.2 / 2 := by
    have : ∀ i, q i * plaquetteCentreDisplacement p p' i = q i * (d i : ℝ) +
        (if i = p'.2.1 then q i / 2 else 0) +
        (if i = p'.2.2 then q i / 2 else 0) - (if i = p.2.1 then q i / 2 else 0) -
        (if i = p.2.2 then q i / 2 else 0) := by
      intro i
      simp only [plaquetteCentreDisplacement, hd i]
      split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have h2 : dualCharacter j (p'.1 + -p.1) = Complex.exp (Complex.I * (∑ i, q i * (d i : ℝ) : ℝ)) := by
    rw [← dualCharacter_eq_exp hq, hw, sub_eq_add_neg]
  have h3 : plaquettePhase j p' * (starRingEnd ℂ) (plaquettePhase j p) = dualCharacter j (p'.1 + -p.1) *
      halfPhase q p'.2.1 * halfPhase q p'.2.2 * (halfPhase q p.2.1)⁻¹ * (halfPhase q p.2.2)⁻¹ := by
    simp only [plaquettePhase, map_mul, conj_halfPhase, dualCharacter_add, dualCharacter_neg, ← hqd]
    ring
  rw [h3, h2, h1]
  simp only [halfPhase]
  rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring
private theorem complexCurl_solution (p p' : TorusPlaquette N) :
    complexCurl (solutionForm K p') p =
      inverseSymbolFourierSum N (bondKernelSymbol K) p.2.1 p.2.2 p'.2.1 p'.2.2
        (plaquetteCentreDisplacement p p') := by
  obtain ⟨x, μ, ν⟩ := p
  simp only [complexCurl, solutionForm, inverseSymbolFourierSum]
  rw [← mul_add, ← mul_sub, ← mul_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hq := isMomentumAt_dualMomentum j
  set q := dualMomentum j with hqd
  have h1 : ∑ m, ∑ m', (starRingEnd ℂ) (curlSymbol q μ ν m) * (symbolWithGradient (bondKernelSymbol K) q)⁻¹ m m' *
      curlSymbol q p'.2.1 p'.2.2 m' = Complex.I * ((latticeMomentum q ν : ℂ) * solutionVector K j p' μ -
        (latticeMomentum q μ : ℂ) * solutionVector K j p' ν) := by
    rw [← sum_conj_curlSymbol]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [solutionVector, Matrix.mulVec, dotProduct, gradientMatrix, ← hqd, Finset.mul_sum, mul_assoc]
  rw [h1, plaquettePhase_centre]
  have e1 : Complex.I * (latticeMomentum q μ : ℂ) = halfPhase q μ - (halfPhase q μ)⁻¹ :=
    (halfPhase_sub_inv q μ).symm
  have e2 : Complex.I * (latticeMomentum q ν : ℂ) = halfPhase q ν - (halfPhase q ν)⁻¹ :=
    (halfPhase_sub_inv q ν).symm
  have hI : Complex.I * ((latticeMomentum q ν : ℂ) * solutionVector K j p' μ -
      (latticeMomentum q μ : ℂ) * solutionVector K j p' ν) =
      (halfPhase q ν - (halfPhase q ν)⁻¹) * solutionVector K j p' μ -
        (halfPhase q μ - (halfPhase q μ)⁻¹) * solutionVector K j p' ν := by
    rw [← e1, ← e2]; ring
  rw [hI]
  have ha := halfPhase_ne_zero q μ
  have hb := halfPhase_ne_zero q ν
  simp only [plaquettePhase, map_mul, conj_halfPhase, dualCharacter_add, dualCharacter_unitStep hq, map_pow, ← hqd]
  field_simp
  ring
private theorem bilinearForm_sum_right (B : TorusBond N → ℝ) (P : Finset (TorusPlaquette N))
    (h : TorusPlaquette N → ℝ) (F : TorusPlaquette N → TorusBond N → ℝ) :
    bilinearForm K B (fun b => ∑ e ∈ P, h e * F e b) = ∑ e ∈ P, h e * bilinearForm K B (F e) := by
  simp only [bilinearForm, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun e _ => ?_
  ring
private theorem covariance_eq_fourierSum (hK : IsGaugeKernel K c) (hc : 0 < c)
    (Tt : TorusPlaquette N → TorusPlaquette N → ℝ)
    (hs : ∀ p p', Tt p p' = Tt p' p)
    (hl : ∀ h : TorusPlaquette N → ℝ, IsLUB (Set.range fun A : TorusBond N → ℝ =>
        2 * ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)), h p * WeightedResponses.curl A p -
          bilinearForm K A A)
      (∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)), h p * Tt p p' * h p'))
    {p p' : TorusPlaquette N} (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)))
    (hp' : p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite N))) :
    (Tt p p' : ℂ) = inverseSymbolFourierSum N (bondKernelSymbol K) p.2.1 p.2.2 p'.2.1 p'.2.2
      (plaquetteCentreDisplacement p p') := by
  set P := plaquettesIn (Finset.univ : Finset (TorusSite N)) with hP
  set F : TorusPlaquette N → TorusBond N → ℝ := fun p b => (solutionForm K p b).re with hF
  set G : TorusPlaquette N → TorusBond N → ℝ := fun p b => (solutionForm K p b).im with hG
  have hpair : ∀ a (B : TorusBond N → ℝ), bilinearForm K B (F a) = WeightedResponses.curl B a :=
    fun a B => pairing_solution_re hK hc a B
  have hcurl_lin : ∀ (h : TorusPlaquette N → ℝ) (a : TorusPlaquette N),
      WeightedResponses.curl (fun b => ∑ e ∈ P, h e * F e b) a =
      ∑ e ∈ P, h e * WeightedResponses.curl (F e) a := by
    intro h a
    simp only [WeightedResponses.curl, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have hD : ∀ h : TorusPlaquette N → ℝ,
      ∑ a ∈ P, ∑ b ∈ P, h a * (Tt a b - WeightedResponses.curl (F b) a) * h b = 0 := by
    intro h
    set H : TorusBond N → ℝ := fun b => ∑ e ∈ P, h e * F e b with hH
    have hHB : ∀ B : TorusBond N → ℝ, bilinearForm K B H = ∑ e ∈ P, h e * WeightedResponses.curl B e := by
      intro B
      rw [hH, bilinearForm_sum_right]
      simp only [hpair]
    have hLUB : IsLUB (Set.range fun A : TorusBond N → ℝ =>
        2 * ∑ e ∈ P, h e * WeightedResponses.curl A e - bilinearForm K A A)
        (bilinearForm K H H) := by
      refine IsGreatest.isLUB ⟨⟨H, ?_⟩, ?_⟩
      · simp only [← hHB]
        ring
      · rintro _ ⟨A, rfl⟩
        simp only [← hHB]
        have h1 := bilinearForm_self_nonneg hK hc (fun b => A b - H b)
        rw [bilinearForm_sub_sub hK] at h1
        linarith
    have h1 := (hl h).unique hLUB
    have h2 : bilinearForm K H H = ∑ a ∈ P, ∑ b ∈ P, h a * WeightedResponses.curl (F b) a * h b := by
      rw [hHB]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hH, hcurl_lin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [h2] at h1
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    linarith
  have hsymD : ∀ a b, Tt a b - WeightedResponses.curl (F b) a = Tt b a - WeightedResponses.curl (F a) b := by
    intro a b
    rw [← hpair a (F b), ← hpair b (F a), bilinearForm_comm hK, hs]
  have h3 := entry_zero_of_quadratic_zero P (fun a b => Tt a b - WeightedResponses.curl (F b) a) hsymD hD hp hp'
  have h4 : Tt p p' = WeightedResponses.curl (F p') p := by
    linarith
  have h5 : WeightedResponses.curl (G p') p = 0 := by
    have h6 := hK.coercive (G p')
    have h7 : ∑ b, ∑ b', G p' b * K b b' * G p' b' = 0 := pairing_solution_im hK hc p' (G p')
    rw [h7] at h6
    have h8 : ∑ e ∈ P, WeightedResponses.curl (G p') e ^ 2 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have := mul_pos hc hcon
      linarith
    have h9 := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg (WeightedResponses.curl (G p') e))).mp
      (le_antisymm h8 (Finset.sum_nonneg fun e _ => sq_nonneg _)) p hp
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h9
  rw [← complexCurl_solution]
  apply Complex.ext
  · rw [complexCurl_re, Complex.ofReal_re, h4]
  · rw [complexCurl_im, Complex.ofReal_im]
    exact h5.symm
end
section
private theorem summable_exp_neg_natAbs {s : ℝ} (hs : 0 < s) :
    Summable fun n : ℤ => Real.exp (-(s * (n.natAbs : ℝ))) := by apply _root_.YangMills.SharedProofs.p17292 <;> assumption
private def intGeomSum (s : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-(s * (n.natAbs : ℝ)))
private theorem sum_zmod_exp_le {N : ℕ} [NeZero N] {s : ℝ} (hs : 0 < s) :
    ∑ a : ZMod N, Real.exp (-(s * (a.valMinAbs.natAbs : ℝ))) ≤ intGeomSum s := by apply _root_.YangMills.DeltaSharedProofs.p501961 <;> assumption
variable {N : ℕ} [NeZero N]
private abbrev supNormSite (x : TorusSite N) : ℕ := supDist (0 : TorusSite N) x
private theorem natAbs_le_supNormSite (x : TorusSite N) (i : Fin 4) :
    (x i).valMinAbs.natAbs ≤ supNormSite x := by
  have h : ((0 - x i : ZMod N).valMinAbs).natAbs ≤ supDist (0 : TorusSite N) x :=
    Finset.le_sup (f := fun i => (((0 : TorusSite N) i - x i).valMinAbs).natAbs) (Finset.mem_univ i)
  simpa [ZMod.natAbs_valMinAbs_neg] using h
private theorem sum_exp_supNormSite_le {s : ℝ} (hs : 0 < s) :
    ∑ x : TorusSite N, Real.exp (-(s * (supNormSite x : ℝ))) ≤ intGeomSum (s / 4) ^ 4 := by
  have h1 : ∀ x : TorusSite N, Real.exp (-(s * (supNormSite x : ℝ))) ≤
      ∏ i, Real.exp (-(s / 4 * ((x i).valMinAbs.natAbs : ℝ))) := by
    intro x
    rw [← Real.exp_sum, Real.exp_le_exp]
    have h2 : ∑ i, ((x i).valMinAbs.natAbs : ℝ) ≤ 4 * (supNormSite x : ℝ) := by
      calc ∑ i, ((x i).valMinAbs.natAbs : ℝ) ≤ ∑ _i : Fin 4, (supNormSite x : ℝ) :=
            Finset.sum_le_sum fun i _ => by exact_mod_cast natAbs_le_supNormSite x i
        _ = _ := by simp
    have h3 : ∑ i, -(s / 4 * ((x i).valMinAbs.natAbs : ℝ)) =
        -(s / 4 * ∑ i, ((x i).valMinAbs.natAbs : ℝ)) := by
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    rw [h3]
    nlinarith
  calc ∑ x : TorusSite N, Real.exp (-(s * (supNormSite x : ℝ)))
      ≤ ∑ x : TorusSite N, ∏ i, Real.exp (-(s / 4 * ((x i).valMinAbs.natAbs : ℝ))) :=
        Finset.sum_le_sum fun x _ => h1 x
    _ = ∏ _i : Fin 4, ∑ a : ZMod N, Real.exp (-(s / 4 * (a.valMinAbs.natAbs : ℝ))) := by
        rw [Finset.prod_univ_sum]
        simp [Fintype.piFinset_univ]
    _ = (∑ a : ZMod N, Real.exp (-(s / 4 * (a.valMinAbs.natAbs : ℝ)))) ^ 4 := by simp
    _ ≤ intGeomSum (s / 4) ^ 4 := by
        refine pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
          (sum_zmod_exp_le (by positivity)) 4
private theorem two_abs_displacement_le (x : TorusSite N) (i : Fin 4) :
    2 * |torusDisplacement (0 : TorusSite N) x i| ≤ N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  simp only [torusDisplacement, circleSub]
  set t : ℝ := (((x i).val : ℝ) - (((0 : TorusSite N) i).val : ℝ)) / (N : ℝ) with ht
  have h1 : (((x i).val : ℝ) - (((0 : TorusSite N) i).val : ℝ)) = (N : ℝ) * t := by
    rw [ht]; field_simp
  rw [h1, ← mul_sub, abs_mul, abs_of_pos hN]
  have := abs_sub_round t
  nlinarith
private theorem displacement_eq_of_small (x : TorusSite N) (i : Fin 4) (d : ℤ) (hd : (d : ZMod N) = x i)
    (hlt : 2 * |(d : ℝ)| < N) : torusDisplacement (0 : TorusSite N) x i = d := by
  obtain ⟨e, he, hx⟩ := exists_int_displacement (0 : TorusSite N) x
  have h1 := two_abs_displacement_le x i
  rw [he i] at h1 ⊢
  have h2 : ((e i - d : ℤ) : ZMod N) = 0 := by
    have := congrFun hx i
    simp only [siteOfInt, sub_zero] at this
    push_cast
    rw [this, hd, sub_self]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h3 : |((e i - d : ℤ) : ℝ)| < N := by
    push_cast
    have := abs_sub (e i : ℝ) (d : ℝ)
    linarith
  rw [hk] at h3
  have hk0 : k = 0 := by
    by_contra hne
    have h4 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hne
      exact_mod_cast this
    push_cast at h3
    rw [abs_mul, abs_of_pos hN] at h3
    nlinarith
  rw [hk0] at hk
  have : e i = d := by linarith
  rw [this]
private theorem abs_displacement_le_supNormSite (x : TorusSite N) (i : Fin 4) :
    |torusDisplacement (0 : TorusSite N) x i| ≤ (supNormSite x : ℝ) := by
  have h0 := natAbs_le_supNormSite x i
  by_cases h2 : 2 * |(((x i).valMinAbs : ℤ) : ℝ)| < N
  · rw [displacement_eq_of_small x i _ (by simp) h2, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact_mod_cast h0
  · have h3 := two_abs_displacement_le x i
    have h4 : (N : ℝ) ≤ 2 * ((x i).valMinAbs.natAbs : ℝ) := by
      push Not at h2
      rwa [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] at h2
    have h5 : ((x i).valMinAbs.natAbs : ℝ) ≤ (supNormSite x : ℝ) := by exact_mod_cast h0
    linarith
end
section
private def linearPairing (ζ : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ := ∑ i, ζ i • ContinuousLinearMap.proj i
private theorem linearPairing_apply (ζ p : Fin 4 → ℝ) : linearPairing ζ p = ∑ i, p i * ζ i := by
  simp [linearPairing, mul_comm]
private theorem norm_linearPairing_le (ζ : Fin 4 → ℝ) : ‖linearPairing ζ‖ ≤ ∑ i, |ζ i| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun p => ?_
  rw [linearPairing_apply, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm p i) (abs_nonneg _)
private def unitPhase (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))
private theorem contDiff_unitPhase : ContDiff ℝ ⊤ unitPhase := by
  unfold unitPhase
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
private theorem iteratedDeriv_unitPhase (r : ℕ) :
    iteratedDeriv r unitPhase = fun t => Complex.I ^ r * unitPhase t := by apply _root_.YangMills.Construction.Tower.LocalFamilies.AbelianLocality.iteratedDeriv_expI <;> assumption
private theorem norm_iteratedFDeriv_unitPhase (r : ℕ) (t : ℝ) : ‖iteratedFDeriv ℝ r unitPhase t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_unitPhase]
  simp [unitPhase, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
private theorem contDiff_unitPhase_pairing (ζ : Fin 4 → ℝ) (r : ℕ) :
    ContDiff ℝ r fun p => unitPhase (linearPairing ζ p) :=
  (contDiff_unitPhase.of_le le_top).comp (linearPairing ζ).contDiff
private theorem norm_iteratedFDeriv_unitPhase_pairing_le (ζ : Fin 4 → ℝ) (r : ℕ) (p : Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ r (fun p => unitPhase (linearPairing ζ p)) p‖ ≤ (∑ i, |ζ i|) ^ r := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (linearPairing ζ) (contDiff_unitPhase.of_le le_top) p
    (le_refl (r : WithTop ℕ∞))
  have h1 : (fun p => unitPhase (linearPairing ζ p)) = unitPhase ∘ (linearPairing ζ) := rfl
  rw [h1, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_unitPhase, one_mul]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_linearPairing_le ζ) r
variable {N : ℕ} [NeZero N]
private def bondMidDisplacement (x : TorusSite N) (μ ν : Fin 4) : Fin 4 → ℝ := fun i =>
  torusDisplacement (0 : TorusSite N) x i + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2
private theorem bondKernelSymbol_eq_sum (K : TorusBond N → TorusBond N → ℝ) (μ ν : Fin 4) :
    (fun p => bondKernelSymbol K p μ ν) =
      fun p => ∑ x : TorusSite N, K ((0 : TorusSite N), μ) (x, ν) •
        unitPhase (linearPairing (bondMidDisplacement x μ ν) p) := by
  funext p
  simp only [bondKernelSymbol, unitPhase, linearPairing_apply, bondMidDisplacement, Complex.real_smul]
private theorem abs_bondMidDisplacement_le (x : TorusSite N) (μ ν i : Fin 4) :
    |bondMidDisplacement x μ ν i| ≤ (supNormSite x : ℝ) + 1 := by
  have h1 := abs_displacement_le_supNormSite x i
  have h2 : |(((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2 : ℝ)| ≤ 1 := by
    split_ifs <;> norm_num
  exact (abs_add_le _ _).trans (by linarith)
private theorem sum_abs_bondMidDisplacement_le (x : TorusSite N) (μ ν : Fin 4) :
    ∑ i, |bondMidDisplacement x μ ν i| ≤ 4 * ((supNormSite x : ℝ) + 1) := by
  calc ∑ i, |bondMidDisplacement x μ ν i| ≤ ∑ _i : Fin 4, ((supNormSite x : ℝ) + 1) :=
        Finset.sum_le_sum fun i _ => abs_bondMidDisplacement_le x μ ν i
    _ = _ := by simp; ring
private def kernelMomentBound (C c₀ : ℝ) (r : ℕ) : ℝ :=
  C * ((8 / c₀) ^ r * (r.factorial : ℝ) * Real.exp (c₀ / 2)) * intGeomSum (c₀ / 2 / 4) ^ 4
variable {K : TorusBond N → TorusBond N → ℝ} {C c₀ : ℝ}
private theorem kernel_moment_le (hC : 0 ≤ C) (hc : 0 < c₀)
    (hD : ∀ b b' : TorusBond N, |K b b'| ≤ C * Real.exp (-(c₀ * (supDist b.1 b'.1 : ℝ)))) (r : ℕ) (μ ν : Fin 4) :
    ∑ x : TorusSite N, |K ((0 : TorusSite N), μ) (x, ν)| * (∑ i, |bondMidDisplacement x μ ν i|) ^ r ≤
      kernelMomentBound C c₀ r := by
  have hA : 0 ≤ (8 / c₀) ^ r * (r.factorial : ℝ) * Real.exp (c₀ / 2) := by positivity
  have h1 : ∀ x : TorusSite N, |K ((0 : TorusSite N), μ) (x, ν)| * (∑ i, |bondMidDisplacement x μ ν i|) ^ r ≤
      C * ((8 / c₀) ^ r * (r.factorial : ℝ) * Real.exp (c₀ / 2)) *
        Real.exp (-(c₀ / 2 * (supNormSite x : ℝ))) := by
    intro x
    set t : ℝ := (supNormSite x : ℝ) with ht
    have ht0 : 0 ≤ t := Nat.cast_nonneg _
    have h2 := hD ((0 : TorusSite N), μ) (x, ν)
    have h3 : (∑ i, |bondMidDisplacement x μ ν i|) ^ r ≤ (4 * (t + 1)) ^ r :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (sum_abs_bondMidDisplacement_le x μ ν) r
    have h4 : (4 * (t + 1)) ^ r ≤ (8 / c₀) ^ r * (r.factorial : ℝ) * Real.exp (c₀ / 2 * (t + 1)) := by
      have h5 := Real.pow_div_factorial_le_exp (c₀ / 2 * (t + 1)) (by positivity) r
      have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
      rw [div_le_iff₀ hf] at h5
      calc (4 * (t + 1)) ^ r = (8 / c₀) ^ r * (c₀ / 2 * (t + 1)) ^ r := by
            rw [← mul_pow]; congr 1; field_simp; ring
        _ ≤ (8 / c₀) ^ r * (Real.exp (c₀ / 2 * (t + 1)) * (r.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = _ := by ring
    calc |K ((0 : TorusSite N), μ) (x, ν)| * (∑ i, |bondMidDisplacement x μ ν i|) ^ r
        ≤ (C * Real.exp (-(c₀ * t))) * ((8 / c₀) ^ r * (r.factorial : ℝ) * Real.exp (c₀ / 2 * (t + 1))) :=
          mul_le_mul h2 (h3.trans h4) (by positivity) (by positivity)
      _ = _ := by
          have : Real.exp (c₀ / 2 * (t + 1)) = Real.exp (c₀ / 2) * Real.exp (c₀ / 2 * t) := by
            rw [← Real.exp_add]; congr 1; ring
          have h6 : Real.exp (-(c₀ * t)) * Real.exp (c₀ / 2 * t) = Real.exp (-(c₀ / 2 * t)) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [this]
          calc _ = C * ((8 / c₀) ^ r * (r.factorial : ℝ) * Real.exp (c₀ / 2)) *
                (Real.exp (-(c₀ * t)) * Real.exp (c₀ / 2 * t)) := by ring
            _ = _ := by rw [h6]
  calc _ ≤ ∑ x : TorusSite N, C * ((8 / c₀) ^ r * (r.factorial : ℝ) * Real.exp (c₀ / 2)) *
        Real.exp (-(c₀ / 2 * (supNormSite x : ℝ))) := Finset.sum_le_sum fun x _ => h1 x
    _ = C * ((8 / c₀) ^ r * (r.factorial : ℝ) * Real.exp (c₀ / 2)) *
        ∑ x : TorusSite N, Real.exp (-(c₀ / 2 * (supNormSite x : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ _ := by
        rw [kernelMomentBound]
        exact mul_le_mul_of_nonneg_left (sum_exp_supNormSite_le (by positivity)) (mul_nonneg hC hA)
private theorem kernel_tail_le (hC : 0 ≤ C) (hc : 0 < c₀)
    (hD : ∀ b b' : TorusBond N, |K b b'| ≤ C * Real.exp (-(c₀ * (supDist b.1 b'.1 : ℝ)))) (μ ν : Fin 4)
    (W : Finset (TorusSite N)) (R : ℝ) (hW : ∀ x ∈ W, R ≤ (supNormSite x : ℝ)) :
    ∑ x ∈ W, |K ((0 : TorusSite N), μ) (x, ν)| ≤
      C * intGeomSum (c₀ / 2 / 4) ^ 4 * Real.exp (-(c₀ / 2 * R)) := by
  have h1 : ∀ x ∈ W, |K ((0 : TorusSite N), μ) (x, ν)| ≤
      C * Real.exp (-(c₀ / 2 * R)) * Real.exp (-(c₀ / 2 * (supNormSite x : ℝ))) := by
    intro x hx
    have h2 := hD ((0 : TorusSite N), μ) (x, ν)
    refine h2.trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
    have := hW x hx
    change -(c₀ * (supNormSite x : ℝ)) ≤ _
    nlinarith
  have h3 : ∑ x ∈ W, Real.exp (-(c₀ / 2 * (supNormSite x : ℝ))) ≤ intGeomSum (c₀ / 2 / 4) ^ 4 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W) fun _ _ _ => (Real.exp_pos _).le).trans
      (sum_exp_supNormSite_le (by positivity))
  calc _ ≤ ∑ x ∈ W, C * Real.exp (-(c₀ / 2 * R)) * Real.exp (-(c₀ / 2 * (supNormSite x : ℝ))) :=
        Finset.sum_le_sum h1
    _ = C * Real.exp (-(c₀ / 2 * R)) * ∑ x ∈ W, Real.exp (-(c₀ / 2 * (supNormSite x : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ C * Real.exp (-(c₀ / 2 * R)) * intGeomSum (c₀ / 2 / 4) ^ 4 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring
private theorem symbol_contDiff (r : ℕ) (μ ν : Fin 4) : ContDiff ℝ r fun p => bondKernelSymbol K p μ ν := by
  rw [bondKernelSymbol_eq_sum]
  exact ContDiff.sum fun x _ => (contDiff_unitPhase_pairing _ r).const_smul _
private theorem norm_iteratedFDeriv_symbol_le (hC : 0 ≤ C) (hc : 0 < c₀)
    (hD : ∀ b b' : TorusBond N, |K b b'| ≤ C * Real.exp (-(c₀ * (supDist b.1 b'.1 : ℝ)))) (r : ℕ) (μ ν : Fin 4)
    (p : Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ r (fun p => bondKernelSymbol K p μ ν) p‖ ≤ kernelMomentBound C c₀ r := by
  rw [bondKernelSymbol_eq_sum]
  have h1 : iteratedFDeriv ℝ r (fun p => ∑ x : TorusSite N,
      K ((0 : TorusSite N), μ) (x, ν) • unitPhase (linearPairing (bondMidDisplacement x μ ν) p)) p =
      ∑ x : TorusSite N, K ((0 : TorusSite N), μ) (x, ν) •
        iteratedFDeriv ℝ r (fun p => unitPhase (linearPairing (bondMidDisplacement x μ ν) p)) p := by
    rw [iteratedFDeriv_fun_sum_apply fun x _ => ((contDiff_unitPhase_pairing _ r).const_smul _).contDiffAt]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact iteratedFDeriv_const_smul_apply' (contDiff_unitPhase_pairing _ r).contDiffAt
  rw [h1]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => ?_).trans (kernel_moment_le hC hc hD r μ ν))
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_unitPhase_pairing_le _ r p) (abs_nonneg _)
private theorem exp_two_pi_half_int (d n : ℤ) :
    Complex.exp (Complex.I * ((2 * Real.pi * ((d : ℝ) + (n : ℝ) / 2) : ℝ) : ℂ)) = (-1 : ℂ) ^ n := by
  have h : Complex.I * ((2 * Real.pi * ((d : ℝ) + (n : ℝ) / 2) : ℝ) : ℂ) =
      (d : ℂ) * (2 * Real.pi * Complex.I) + (n : ℂ) * (Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_int_mul,
    Complex.exp_pi_mul_I]
private theorem periodShift_phase (d : ℤ) (i μ ν : Fin 4) :
    Complex.exp (Complex.I * ((2 * Real.pi * ((d : ℝ) + ((if i = ν then 1 else 0) -
      (if i = μ then 1 else 0)) / 2) : ℝ) : ℂ)) = periodShiftSign i μ ν := by
  unfold periodShiftSign
  by_cases a : i = ν <;> by_cases b : i = μ
  · simp only [if_pos a, if_pos b]
    rw [show (2 * Real.pi * ((d : ℝ) + (1 - 1) / 2)) = 2 * Real.pi * ((d : ℝ) + ((0 : ℤ) : ℝ) / 2) by
      norm_num, exp_two_pi_half_int]
    norm_num
  · simp only [if_pos a, if_neg b]
    rw [show (2 * Real.pi * ((d : ℝ) + (1 - 0) / 2)) = 2 * Real.pi * ((d : ℝ) + ((1 : ℤ) : ℝ) / 2) by
      norm_num, exp_two_pi_half_int]
    norm_num
  · simp only [if_neg a, if_pos b]
    rw [show (2 * Real.pi * ((d : ℝ) + (0 - 1) / 2)) = 2 * Real.pi * ((d : ℝ) + ((-1 : ℤ) : ℝ) / 2) by
      push_cast; ring, exp_two_pi_half_int]
    norm_num
  · simp only [if_neg a, if_neg b]
    rw [show (2 * Real.pi * ((d : ℝ) + (0 - 0) / 2)) = 2 * Real.pi * ((d : ℝ) + ((0 : ℤ) : ℝ) / 2) by
      norm_num, exp_two_pi_half_int]
    norm_num
private theorem symbol_periodShift (p : Fin 4 → ℝ) (i μ ν : Fin 4) :
    bondKernelSymbol K (p + Pi.single i (2 * Real.pi)) μ ν = periodShiftSign i μ ν * bondKernelSymbol K p μ ν := by
  simp only [bondKernelSymbol, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨d, hd, -⟩ := exists_int_displacement (0 : TorusSite N) x
  have h1 : (∑ k, (p + Pi.single i (2 * Real.pi) : Fin 4 → ℝ) k * (torusDisplacement (0 : TorusSite N) x k +
      ((if k = ν then 1 else 0) - (if k = μ then 1 else 0)) / 2)) =
      (∑ k, p k * (torusDisplacement (0 : TorusSite N) x k +
      ((if k = ν then 1 else 0) - (if k = μ then 1 else 0)) / 2)) +
      2 * Real.pi * ((d i : ℝ) + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp [hd i]
    · intro k _ hk; simp [hk]
    · simp
  rw [h1, Complex.ofReal_add, mul_add, Complex.exp_add, periodShift_phase]
  ring
end
section
variable {N : ℕ} [NeZero N] {K : TorusBond N → TorusBond N → ℝ} {C c₀ c : ℝ}
private def farSites (N : ℕ) [NeZero N] : Finset (TorusSite N) :=
  Finset.univ.filter fun x => (N : ℝ) ≤ 2 * ((supNormSite x : ℝ) + 1)
private theorem kernel_reflect_site (hK : IsGaugeKernel K c) (μ ν : Fin 4) (w : TorusSite N) :
    K ((0 : TorusSite N), μ) (-(w + unitStep N ν) + unitStep N μ, ν) = K ((0 : TorusSite N), μ) (w, ν) := by
  have h1 := hK.reflect ((0 : TorusSite N), μ) (w, ν)
  have h2 := hK.translate (unitStep N μ) (-((0 : TorusSite N) + unitStep N μ), μ) (-(w + unitStep N ν), ν)
  simp only [zero_add, neg_add_cancel] at h1 h2
  rw [h2, h1]
private theorem unitStep_apply (m i : Fin 4) : (unitStep N m) i = if i = m then 1 else 0 := by
  simp [unitStep, Pi.single_apply]
private theorem bondMidDisplacement_reflect (w : TorusSite N) (μ ν : Fin 4) (hw : w ∉ farSites N) :
    bondMidDisplacement (-(w + unitStep N ν) + unitStep N μ) μ ν = fun i => -bondMidDisplacement w μ ν i := by
  have hlt : 2 * ((supNormSite w : ℝ) + 1) < N := by
    simpa [farSites] using hw
  funext i
  obtain ⟨d, hd, hx⟩ := exists_int_displacement (0 : TorusSite N) w
  rw [sub_zero] at hx
  set e : ℤ := -d i - (if i = ν then 1 else 0) + (if i = μ then 1 else 0) with he
  have hde : (e : ZMod N) = (-(w + unitStep N ν) + unitStep N μ) i := by
    have := congrFun hx i
    simp only [siteOfInt] at this
    simp only [Pi.add_apply, Pi.neg_apply, unitStep_apply, ← this, he]
    push_cast
    split_ifs <;> ring
  have h1 := abs_displacement_le_supNormSite w i
  rw [hd i] at h1
  have he2 : 2 * |(e : ℝ)| < N := by
    have h2 : |(e : ℝ)| ≤ (supNormSite w : ℝ) + 1 := by
      have h3 := abs_le.mp h1
      rw [he]
      push_cast
      refine abs_le.mpr ?_
      split_ifs <;> constructor <;> linarith [h3.1, h3.2]
    linarith
  have h4 := displacement_eq_of_small _ i e hde he2
  simp only [bondMidDisplacement, h4, hd i, he]
  push_cast
  split_ifs <;> ring
private theorem symbol_re_im_eq (p : Fin 4 → ℝ) (μ ν : Fin 4) :
    (bondKernelSymbol K p μ ν).re = ∑ x : TorusSite N, K ((0 : TorusSite N), μ) (x, ν) *
      Real.cos (linearPairing (bondMidDisplacement x μ ν) p) ∧
    (bondKernelSymbol K p μ ν).im = ∑ x : TorusSite N, K ((0 : TorusSite N), μ) (x, ν) *
      Real.sin (linearPairing (bondMidDisplacement x μ ν) p) := by
  have h : bondKernelSymbol K p μ ν = ∑ x, _ := congrFun (bondKernelSymbol_eq_sum K μ ν) p
  have he : ∀ t : ℝ, unitPhase t = Complex.exp ((t : ℂ) * Complex.I) := fun t => by rw [unitPhase, mul_comm]
  rw [h]
  constructor
  · simp only [Complex.re_sum, Complex.smul_re, he, Complex.exp_ofReal_mul_I_re, smul_eq_mul]
  · simp only [Complex.im_sum, Complex.smul_im, he, Complex.exp_ofReal_mul_I_im, smul_eq_mul]
private theorem abs_symbol_im_le (hK : IsGaugeKernel K c) (p : Fin 4 → ℝ) (μ ν : Fin 4) :
    |(bondKernelSymbol K p μ ν).im| ≤ ∑ x ∈ farSites N, |K ((0 : TorusSite N), μ) (x, ν)| := by
  have hinv : Function.Involutive fun w : TorusSite N => -(w + unitStep N ν) + unitStep N μ := by
    intro w
    simp only
    abel
  rw [(symbol_re_im_eq p μ ν).2]
  set f : TorusSite N → ℝ := fun x => K ((0 : TorusSite N), μ) (x, ν) *
    Real.sin (linearPairing (bondMidDisplacement x μ ν) p) with hf
  have h1 : ∑ x, f x = ∑ x, f (-(x + unitStep N ν) + unitStep N μ) := (Equiv.sum_comp hinv.toPerm f).symm
  have h2 : 2 * ∑ x, f x = ∑ x, (f x + f (-(x + unitStep N ν) + unitStep N μ)) := by
    rw [Finset.sum_add_distrib, ← h1]; ring
  have h3 : ∀ x, x ∉ farSites N → f x + f (-(x + unitStep N ν) + unitStep N μ) = 0 := by
    intro x hx
    simp only [hf, kernel_reflect_site hK, bondMidDisplacement_reflect x μ ν hx]
    have : linearPairing (fun i => -bondMidDisplacement x μ ν i) p = -linearPairing (bondMidDisplacement x μ ν) p := by
      simp only [linearPairing_apply, mul_neg, Finset.sum_neg_distrib]
    rw [this, Real.sin_neg]
    ring
  have h4 : ∀ x, |f x + f (-(x + unitStep N ν) + unitStep N μ)| ≤
      if x ∈ farSites N then 2 * |K ((0 : TorusSite N), μ) (x, ν)| else 0 := by
    intro x
    split_ifs with hx
    · simp only [hf, kernel_reflect_site hK]
      have a1 := Real.abs_sin_le_one (linearPairing (bondMidDisplacement x μ ν) p)
      have a2 := Real.abs_sin_le_one
        (linearPairing (bondMidDisplacement (-(x + unitStep N ν) + unitStep N μ) μ ν) p)
      have a3 := abs_nonneg (K ((0 : TorusSite N), μ) (x, ν))
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      nlinarith
    · rw [h3 x hx, abs_zero]
  have h5 : 2 * |∑ x, f x| ≤ 2 * ∑ x ∈ farSites N, |K ((0 : TorusSite N), μ) (x, ν)| := by
    calc 2 * |∑ x, f x| = |2 * ∑ x, f x| := by rw [abs_mul]; norm_num
      _ ≤ ∑ x, |f x + f (-(x + unitStep N ν) + unitStep N μ)| := by
          rw [h2]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, (if x ∈ farSites N then 2 * |K ((0 : TorusSite N), μ) (x, ν)| else 0) :=
          Finset.sum_le_sum fun x _ => h4 x
      _ = _ := by
          rw [← Finset.sum_filter, Finset.mul_sum]
          congr 1
          ext x
          simp
  linarith
private theorem abs_zeroth_moment_le (hK : IsGaugeKernel K c) (μ ν : Fin 4) :
    |∑ x : TorusSite N, K ((0 : TorusSite N), μ) (x, ν)| ≤
      ((N : ℝ) + 2) * ∑ x ∈ farSites N, |K ((0 : TorusSite N), μ) (x, ν)| := by
  set φ : TorusSite N → ℝ := fun x => torusDisplacement (0 : TorusSite N) x ν with hφ
  have h := hK.gauge φ ((0 : TorusSite N), μ)
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single ν] at h
  · set g : TorusSite N → ℝ := fun x => φ (x + unitStep N ν) - φ x with hg
    have hg1 : ∀ x, x ∉ farSites N → g x = 1 := by
      intro x hx
      have hlt : 2 * ((supNormSite x : ℝ) + 1) < N := by simpa [farSites] using hx
      obtain ⟨d, hd, hxd⟩ := exists_int_displacement (0 : TorusSite N) x
      rw [sub_zero] at hxd
      have h1 := abs_displacement_le_supNormSite x ν
      rw [hd ν] at h1
      have h2 : ((d ν + 1 : ℤ) : ZMod N) = (x + unitStep N ν) ν := by
        have := congrFun hxd ν
        simp only [siteOfInt] at this
        simp [unitStep_apply, ← this]
      have h3 : 2 * |((d ν + 1 : ℤ) : ℝ)| < N := by
        have : |((d ν + 1 : ℤ) : ℝ)| ≤ (supNormSite x : ℝ) + 1 := by
          push_cast
          refine (abs_add_le _ _).trans ?_
          simpa using h1
        linarith
      have h4 := displacement_eq_of_small _ ν _ h2 h3
      simp only [hg, hφ, h4, hd ν]
      push_cast
      ring
    have hg2 : ∀ x, |1 - g x| ≤ (N : ℝ) + 2 := by
      intro x
      have h1 := two_abs_displacement_le (x + unitStep N ν) ν
      have h2 := two_abs_displacement_le x ν
      have h3 := abs_le.mp (show |φ (x + unitStep N ν)| ≤ (N : ℝ) / 2 by simp only [hφ]; linarith)
      have h4 := abs_le.mp (show |φ x| ≤ (N : ℝ) / 2 by simp only [hφ]; linarith)
      refine abs_le.mpr ⟨?_, ?_⟩ <;> simp only [hg] <;> linarith [h3.1, h3.2, h4.1, h4.2]
    have h5 : ∑ x : TorusSite N, K ((0 : TorusSite N), μ) (x, ν) =
        ∑ x : TorusSite N, K ((0 : TorusSite N), μ) (x, ν) * (1 - g x) := by
      have : ∑ x : TorusSite N, K ((0 : TorusSite N), μ) (x, ν) * g x = 0 := h
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, this, sub_zero]
    rw [h5]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h6 : ∀ x : TorusSite N, |K ((0 : TorusSite N), μ) (x, ν) * (1 - g x)| ≤
        if x ∈ farSites N then ((N : ℝ) + 2) * |K ((0 : TorusSite N), μ) (x, ν)| else 0 := by
      intro x
      split_ifs with hx
      · rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hg2 x) (abs_nonneg _)
      · rw [hg1 x hx]; simp
    refine (Finset.sum_le_sum fun x _ => h6 x).trans (le_of_eq ?_)
    rw [← Finset.sum_filter, Finset.mul_sum]
    congr 1
    ext x
    simp
  · intro m _ hm
    refine Finset.sum_eq_zero fun x _ => ?_
    have : latticeGradient φ (x, m) = 0 := by
      simp only [latticeGradient, hφ, torusDisplacement]
      simp [unitStep_apply, hm.symm]
    rw [this, mul_zero]
  · simp
private theorem cos_fourth_order (t : ℝ) : |Real.cos t - 1 + t ^ 2 / 2| ≤ 3 * t ^ 4 := by
  by_cases h : |t| ≤ 1
  · have h1 := Real.cos_bound h
    have h2 : Real.cos t - 1 + t ^ 2 / 2 = Real.cos t - (1 - t ^ 2 / 2) := by ring
    rw [h2]
    refine h1.trans ?_
    have h3 : |t| ^ 4 = t ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
    rw [h3]
    have : 0 ≤ t ^ 4 := by positivity
    nlinarith
  · push Not at h
    have h1 : 1 ≤ t ^ 2 := by
      rw [← sq_abs]; nlinarith
    have h2 := Real.cos_le_one t
    have h3 := Real.neg_one_le_cos t
    have h4 : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    rw [h4]
    refine abs_le.mpr ⟨by nlinarith, by nlinarith⟩
private theorem sq_linearPairing_le (ζ p : Fin 4 → ℝ) :
    linearPairing ζ p ^ 2 ≤ sqNorm p * (∑ i, |ζ i|) ^ 2 := by
  rw [linearPairing_apply, sqNorm]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  simp only [Fin.sum_univ_four, ← sq_abs (ζ _)]
  nlinarith [abs_nonneg (ζ 0), abs_nonneg (ζ 1), abs_nonneg (ζ 2), abs_nonneg (ζ 3),
    mul_nonneg (abs_nonneg (ζ 0)) (abs_nonneg (ζ 1)), mul_nonneg (abs_nonneg (ζ 0)) (abs_nonneg (ζ 2)),
    mul_nonneg (abs_nonneg (ζ 0)) (abs_nonneg (ζ 3)), mul_nonneg (abs_nonneg (ζ 1)) (abs_nonneg (ζ 2)),
    mul_nonneg (abs_nonneg (ζ 1)) (abs_nonneg (ζ 3)), mul_nonneg (abs_nonneg (ζ 2)) (abs_nonneg (ζ 3))]
private theorem symbol_re_taylor_le (hC : 0 ≤ C) (hc : 0 < c₀)
    (hD : ∀ b b' : TorusBond N, |K b b'| ≤ C * Real.exp (-(c₀ * (supDist b.1 b'.1 : ℝ))))
    (p : Fin 4 → ℝ) (μ ν : Fin 4) (T : ℝ) :
    |(bondKernelSymbol K p μ ν).re - T| ≤ |∑ x : TorusSite N, K ((0 : TorusSite N), μ) (x, ν)| +
      |(1 / 2 : ℝ) * (∑ x : TorusSite N, K ((0 : TorusSite N), μ) (x, ν) *
        (linearPairing (bondMidDisplacement x μ ν) p) ^ 2) + T| +
      3 * sqNorm p ^ 2 * kernelMomentBound C c₀ 4 := by
  rw [(symbol_re_im_eq p μ ν).1]
  set k : TorusSite N → ℝ := fun x => K ((0 : TorusSite N), μ) (x, ν) with hk
  set θ : TorusSite N → ℝ := fun x => linearPairing (bondMidDisplacement x μ ν) p with hθ
  have h1 : ∑ x, k x * Real.cos (θ x) - T = (∑ x, k x) -
      ((1 / 2 : ℝ) * (∑ x, k x * θ x ^ 2) + T) + ∑ x, k x * (Real.cos (θ x) - 1 + θ x ^ 2 / 2) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_one, Finset.mul_sum]
    have : ∀ x, k x * (θ x ^ 2 / 2) = 1 / 2 * (k x * θ x ^ 2) := fun x => by ring
    simp only [this]
    ring
  have h2 : |∑ x, k x * (Real.cos (θ x) - 1 + θ x ^ 2 / 2)| ≤ 3 * sqNorm p ^ 2 * kernelMomentBound C c₀ 4 := by
    calc _ ≤ ∑ x, |k x * (Real.cos (θ x) - 1 + θ x ^ 2 / 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, 3 * sqNorm p ^ 2 * (|k x| * (∑ i, |bondMidDisplacement x μ ν i|) ^ 4) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [abs_mul]
          have h3 := cos_fourth_order (θ x)
          have h4 := sq_linearPairing_le (bondMidDisplacement x μ ν) p
          have h5 : θ x ^ 4 ≤ sqNorm p ^ 2 * (∑ i, |bondMidDisplacement x μ ν i|) ^ 4 := by
            have h6 : θ x ^ 4 = (θ x ^ 2) ^ 2 := by ring
            have h7 : sqNorm p ^ 2 * (∑ i, |bondMidDisplacement x μ ν i|) ^ 4 =
                (sqNorm p * (∑ i, |bondMidDisplacement x μ ν i|) ^ 2) ^ 2 := by ring
            rw [h6, h7]
            exact pow_le_pow_left₀ (sq_nonneg _) h4 2
          have h8 := abs_nonneg (k x)
          calc _ ≤ |k x| * (3 * (sqNorm p ^ 2 * (∑ i, |bondMidDisplacement x μ ν i|) ^ 4)) :=
                mul_le_mul_of_nonneg_left (h3.trans (by linarith)) h8
            _ = _ := by ring
      _ = 3 * sqNorm p ^ 2 * ∑ x, |k x| * (∑ i, |bondMidDisplacement x μ ν i|) ^ 4 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (kernel_moment_le hC hc hD 4 μ ν) (by positivity)
  rw [h1]
  refine (abs_add_le _ _).trans ?_
  have h3 := abs_sub (∑ x, k x) ((1 / 2 : ℝ) * (∑ x, k x * θ x ^ 2) + T)
  linarith
end
section
private theorem norm_unitPhase (t : ℝ) : ‖unitPhase t‖ = 1 := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.norm_exp_I_mul_ofReal <;> assumption
private theorem norm_unitPhase_sub_le (a b : ℝ) : ‖unitPhase a - unitPhase b‖ ≤ |a - b| := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.norm_exp_I_sub_exp_I_le <;> assumption
private theorem abs_re_hermitian_le (X : Fin 4 → Fin 4 → ℂ) (e : ℝ) (h : ∀ μ ν, ‖X μ ν‖ ≤ e) (v : Fin 4 → ℂ) :
    |(∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * X μ ν * v ν).re| ≤ 4 * e * ∑ m, ‖v m‖ ^ 2 := by
  have he : 0 ≤ e := (norm_nonneg _).trans (h 0 0)
  refine (Complex.abs_re_le_norm _).trans ?_
  have h1 : ‖∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * X μ ν * v ν‖ ≤ e * (∑ m, ‖v m‖) ^ 2 := by
    calc _ ≤ ∑ μ, ∑ ν, ‖(starRingEnd ℂ) (v μ) * X μ ν * v ν‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => norm_sum_le _ _)
      _ ≤ ∑ μ, ∑ ν, e * (‖v μ‖ * ‖v ν‖) := by
          refine Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => ?_
          rw [norm_mul, norm_mul, RCLike.norm_conj]
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h μ ν) (norm_nonneg (v μ)))
            (norm_nonneg (v ν))
          linarith
      _ = _ := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          simp only [Finset.mul_sum]
  have h2 : (∑ m, ‖v m‖) ^ 2 ≤ 4 * ∑ m, ‖v m‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 4))) (f := fun m => ‖v m‖)
    simpa using this
  calc _ ≤ e * (∑ m, ‖v m‖) ^ 2 := h1
    _ ≤ e * (4 * ∑ m, ‖v m‖ ^ 2) := mul_le_mul_of_nonneg_left h2 he
    _ = _ := by ring
section Comparison
variable {N : ℕ} [NeZero N] {n : ℕ} [NeZero n]
private def centralBox (N : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-((N / 4 : ℕ) : ℤ)) ((N / 4 : ℕ) : ℤ)
private theorem mem_centralBox {w : Fin 4 → ℤ} (hw : w ∈ centralBox N) (i : Fin 4) :
    4 * |w i| ≤ (N : ℤ) := by
  have h := Fintype.mem_piFinset.mp hw i
  rw [Finset.mem_Icc] at h
  have h2 : |w i| ≤ ((N / 4 : ℕ) : ℤ) := abs_le.mpr h
  omega
private theorem card_centralBox_le : ((centralBox N).card : ℝ) ≤ ((N : ℝ) + 1) ^ 4 := by
  have h : (centralBox N).card = (2 * (N / 4) + 1) ^ 4 := by
    simp only [centralBox, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    omega
  rw [h]
  push_cast
  have h2 : ((2 * (N / 4) + 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
    have : 2 * (N / 4) + 1 ≤ N + 1 := by omega
    exact_mod_cast this
  push_cast at h2
  exact pow_le_pow_left₀ (by positivity) h2 4
private theorem siteOfInt_injOn_centralBox (hn : N ≤ n) {w w' : Fin 4 → ℤ} (hw : w ∈ centralBox N)
    (hw' : w' ∈ centralBox N) (h : (siteOfInt w : TorusSite n) = siteOfInt w') : w = w' := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  funext i
  have h1 := mem_centralBox hw i
  have h2 := mem_centralBox hw' i
  have h3 : ((w i : ℤ) : ZMod n) = w' i := congrFun h i
  have h4 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h3
  obtain ⟨k, hk⟩ := h4
  have a1 := abs_le.mp (show |w i| ≤ |w i| from le_rfl)
  have a2 := abs_le.mp (show |w' i| ≤ |w' i| from le_rfl)
  have hk0 : k = 0 := by
    by_contra hne
    have : 1 ≤ |k| := Int.one_le_abs hne
    have hnz : (0 : ℤ) < n := by exact_mod_cast hn0
    have h5 : |w' i - w i| < n := by
      refine abs_lt.mpr ⟨?_, ?_⟩ <;> omega
    rw [hk, abs_mul, abs_of_pos hnz] at h5
    nlinarith
  rw [hk0] at hk
  omega
private theorem bondMidDisplacement_siteOfInt (hn : N ≤ n) {w : Fin 4 → ℤ} (hw : w ∈ centralBox N)
    (μ ν : Fin 4) :
    bondMidDisplacement (siteOfInt w : TorusSite n) μ ν = fun i =>
      (w i : ℝ) + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2 := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  funext i
  have h1 := mem_centralBox hw i
  have h2 : 2 * |(w i : ℝ)| < n := by
    have h3 : 2 * |w i| < (n : ℤ) := by omega
    rw [← Int.cast_abs]
    exact_mod_cast h3
  have h4 := displacement_eq_of_small (siteOfInt w : TorusSite n) i (w i) (by simp [siteOfInt]) h2
  simp only [bondMidDisplacement, h4]
private theorem far_of_not_mem_image (hn : N ≤ n) (x : TorusSite n)
    (hx : x ∉ (centralBox N).image (siteOfInt : _ → TorusSite n)) :
    ((N : ℝ) / 4 - 1) ≤ (supNormSite x : ℝ) := by
  by_contra hc
  push Not at hc
  apply hx
  refine Finset.mem_image.mpr ⟨fun i => (x i).valMinAbs, ?_, by funext i; simp [siteOfInt]⟩
  refine Fintype.mem_piFinset.mpr fun i => ?_
  have h1 := natAbs_le_supNormSite x i
  have h3 : 4 * (supNormSite x + 1) < N := by
    have : (4 * ((supNormSite x : ℝ) + 1)) < N := by linarith
    exact_mod_cast this
  have h4 : (x i).valMinAbs.natAbs ≤ N / 4 := by omega
  rw [Finset.mem_Icc]
  omega
private theorem symbol_eq_box_add_tail (hn : N ≤ n) (K : TorusBond n → TorusBond n → ℝ) (p : Fin 4 → ℝ)
    (μ ν : Fin 4) :
    bondKernelSymbol K p μ ν = (∑ w ∈ centralBox N, K ((0 : TorusSite n), μ) (siteOfInt w, ν) •
        unitPhase (linearPairing
          (fun i => (w i : ℝ) + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) p)) +
      ∑ x ∈ Finset.univ \ (centralBox N).image (siteOfInt : _ → TorusSite n),
        K ((0 : TorusSite n), μ) (x, ν) • unitPhase (linearPairing (bondMidDisplacement x μ ν) p) := by
  have h : bondKernelSymbol K p μ ν = ∑ x, _ := congrFun (bondKernelSymbol_eq_sum K μ ν) p
  rw [h, ← Finset.sum_sdiff (Finset.subset_univ ((centralBox N).image (siteOfInt : _ → TorusSite n))),
    add_comm]
  congr 1
  rw [Finset.sum_image fun a ha b hb hab => siteOfInt_injOn_centralBox hn ha hb hab]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [bondMidDisplacement_siteOfInt hn hw]
private theorem norm_tail_le (hn : N ≤ n) {K : TorusBond n → TorusBond n → ℝ} {C c₀ : ℝ} (hC : 0 ≤ C)
    (hc : 0 < c₀)
    (hD : ∀ b b' : TorusBond n, |K b b'| ≤ C * Real.exp (-(c₀ * (supDist b.1 b'.1 : ℝ)))) (p : Fin 4 → ℝ)
    (μ ν : Fin 4) :
    ‖∑ x ∈ Finset.univ \ (centralBox N).image (siteOfInt : _ → TorusSite n),
        K ((0 : TorusSite n), μ) (x, ν) • unitPhase (linearPairing (bondMidDisplacement x μ ν) p)‖ ≤
      C * intGeomSum (c₀ / 2 / 4) ^ 4 * Real.exp (-(c₀ / 2 * ((N : ℝ) / 4 - 1))) := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ x, ‖K ((0 : TorusSite n), μ) (x, ν) • unitPhase (linearPairing (bondMidDisplacement x μ ν) p)‖ =
      |K ((0 : TorusSite n), μ) (x, ν)| := fun x => by
    rw [norm_smul, norm_unitPhase, mul_one, Real.norm_eq_abs]
  simp only [h1]
  refine kernel_tail_le hC hc hD μ ν _ _ fun x hx => ?_
  exact far_of_not_mem_image hn x (Finset.mem_sdiff.mp hx).2
private theorem norm_symbol_sub_le (hn : N ≤ n) {K : TorusBond N → TorusBond N → ℝ}
    {K' : TorusBond n → TorusBond n → ℝ} {C c₀ e : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c₀)
    (hD : ∀ b b' : TorusBond N, |K b b'| ≤ C * Real.exp (-(c₀ * (supDist b.1 b'.1 : ℝ))))
    (hD' : ∀ b b' : TorusBond n, |K' b b'| ≤ C * Real.exp (-(c₀ * (supDist b.1 b'.1 : ℝ))))
    (h : ∀ (μ ν : Fin 4) (w : Fin 4 → ℤ), (∀ i, 4 * |w i| ≤ (N : ℤ)) →
      |K ((0 : TorusSite N), μ) (siteOfInt w, ν) - K' ((0 : TorusSite n), μ) (siteOfInt w, ν)| ≤ e)
    (he : 0 ≤ e) (p : Fin 4 → ℝ) (μ ν : Fin 4) :
    ‖bondKernelSymbol K p μ ν - bondKernelSymbol K' p μ ν‖ ≤ ((N : ℝ) + 1) ^ 4 * e +
      2 * (C * intGeomSum (c₀ / 2 / 4) ^ 4 * Real.exp (-(c₀ / 2 * ((N : ℝ) / 4 - 1)))) := by
  rw [symbol_eq_box_add_tail (le_refl N) K p μ ν, symbol_eq_box_add_tail hn K' p μ ν]
  set A := ∑ w ∈ centralBox N, K ((0 : TorusSite N), μ) (siteOfInt w, ν) •
        unitPhase (linearPairing
          (fun i => (w i : ℝ) + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) p) with hA
  set A' := ∑ w ∈ centralBox N, K' ((0 : TorusSite n), μ) (siteOfInt w, ν) •
        unitPhase (linearPairing
          (fun i => (w i : ℝ) + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) p) with hA'
  set B := ∑ x ∈ Finset.univ \ (centralBox N).image (siteOfInt : _ → TorusSite N),
        K ((0 : TorusSite N), μ) (x, ν) • unitPhase (linearPairing (bondMidDisplacement x μ ν) p) with hB
  set B' := ∑ x ∈ Finset.univ \ (centralBox N).image (siteOfInt : _ → TorusSite n),
        K' ((0 : TorusSite n), μ) (x, ν) • unitPhase (linearPairing (bondMidDisplacement x μ ν) p) with hB'
  have h1 : ‖B‖ ≤ _ := norm_tail_le (le_refl N) hC hc hD p μ ν
  have h2 : ‖B'‖ ≤ _ := norm_tail_le hn hC hc hD' p μ ν
  have h3 : ‖A - A'‖ ≤ ((N : ℝ) + 1) ^ 4 * e := by
    rw [hA, hA', ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have h4 : ∀ w ∈ centralBox N, ‖K ((0 : TorusSite N), μ) (siteOfInt w, ν) •
        unitPhase (linearPairing
          (fun i => (w i : ℝ) + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) p) -
        K' ((0 : TorusSite n), μ) (siteOfInt w, ν) •
        unitPhase (linearPairing
          (fun i => (w i : ℝ) + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) p)‖ ≤ e := by
      intro w hw
      rw [← sub_smul, norm_smul, norm_unitPhase, mul_one, Real.norm_eq_abs]
      exact h μ ν w (mem_centralBox hw)
    refine (Finset.sum_le_card_nsmul _ _ _ h4).trans ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right card_centralBox_le he
  have h5 : A + B - (A' + B') = (A - A') + B - B' := by ring
  rw [h5]
  refine (norm_sub_le _ _).trans ?_
  have h6 := norm_add_le (A - A') B
  linarith
end Comparison
end
section
private theorem norm_symbol_sub_le_of_close {N : ℕ} [NeZero N] {K : TorusBond N → TorusBond N → ℝ} {C c₀ : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c₀)
    (hD : ∀ b b' : TorusBond N, |K b b'| ≤ C * Real.exp (-(c₀ * (supDist b.1 b'.1 : ℝ))))
    (p q : Fin 4 → ℝ) {e : ℝ} (he : ∀ i, |p i - q i| ≤ e) (μ ν : Fin 4) :
    ‖bondKernelSymbol K p μ ν - bondKernelSymbol K q μ ν‖ ≤ kernelMomentBound C c₀ 1 * e := by
  have h1 : bondKernelSymbol K p μ ν = ∑ x, _ := congrFun (bondKernelSymbol_eq_sum K μ ν) p
  have h2 : bondKernelSymbol K q μ ν = ∑ x, _ := congrFun (bondKernelSymbol_eq_sum K μ ν) q
  have he0 : 0 ≤ e := (abs_nonneg _).trans (he 0)
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have h3 : ∀ x : TorusSite N, ‖K ((0 : TorusSite N), μ) (x, ν) •
      unitPhase (linearPairing (bondMidDisplacement x μ ν) p) -
      K ((0 : TorusSite N), μ) (x, ν) • unitPhase (linearPairing (bondMidDisplacement x μ ν) q)‖ ≤
      |K ((0 : TorusSite N), μ) (x, ν)| * (∑ i, |bondMidDisplacement x μ ν i|) ^ 1 * e := by
    intro x
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc, pow_one]
    refine mul_le_mul_of_nonneg_left ((norm_unitPhase_sub_le _ _).trans ?_) (abs_nonneg _)
    simp only [linearPairing_apply, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← sub_mul, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
  refine (Finset.sum_le_sum fun x _ => h3 x).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (kernel_moment_le hC hc hD 1 μ ν) he0
private theorem abs_latticeMomentum_sub_le (p q : Fin 4 → ℝ) (i : Fin 4) :
    |latticeMomentum p i - latticeMomentum q i| ≤ |p i - q i| := by
  simp only [latticeMomentum]
  have h := Real.abs_sin_sub_sin_le (p i / 2) (q i / 2)
  rw [← mul_sub, abs_mul, abs_two]
  have h2 : |p i / 2 - q i / 2| = |p i - q i| / 2 := by
    rw [← sub_div, abs_div, abs_two]
  rw [h2] at h
  linarith
private theorem abs_latticeMomentum_le (p : Fin 4 → ℝ) (i : Fin 4) : |latticeMomentum p i| ≤ 2 := by
  simp only [latticeMomentum, abs_mul, abs_two]
  have := Real.abs_sin_le_one (p i / 2)
  linarith
private theorem symbolWithGradient_lower_everywhere {N : ℕ} [NeZero N]
    (Kf : ∀ (m : ℕ) [NeZero m], TorusBond m → TorusBond m → ℝ)
    {c C c₀ E : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hG : ∀ (m : ℕ) [NeZero m], N ≤ m → IsGaugeKernel (Kf m) c)
    (hD : ∀ (m : ℕ) [NeZero m], N ≤ m → ∀ b b' : TorusBond m,
      |Kf m b b'| ≤ C * Real.exp (-(c₀ * (supDist b.1 b'.1 : ℝ))))
    (hE : ∀ (m : ℕ) [NeZero m], N ≤ m → ∀ (p : Fin 4 → ℝ) (μ ν : Fin 4),
      ‖bondKernelSymbol (Kf N) p μ ν - bondKernelSymbol (Kf m) p μ ν‖ ≤ E)
    (p : Fin 4 → ℝ) (v : Fin 4 → ℂ) :
    min c 1 * sqNorm (latticeMomentum p) * ∑ m, ‖v m‖ ^ 2 - 4 * E * ∑ m, ‖v m‖ ^ 2 ≤
      (∑ m, ∑ m', (starRingEnd ℂ) (v m) * symbolWithGradient (bondKernelSymbol (Kf N)) p m m' * v m').re := by
  set V := ∑ m, ‖v m‖ ^ 2 with hV
  set M₁ := kernelMomentBound C c₀ 1 with hM
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set Λ := (4 * (M₁ + 4) + 16) * Real.pi * V with hΛ
  obtain ⟨m₁, hm₁⟩ := exists_nat_gt (Λ / ε)
  set m := max N (m₁ + 1) with hm
  have hNm : N ≤ m := le_max_left _ _
  have hmpos : 0 < m := lt_of_lt_of_le (Nat.succ_pos m₁) (le_max_right _ _)
  have : NeZero m := ⟨hmpos.ne'⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hΛm : Λ / m ≤ ε := by
    have h1 : (m₁ : ℝ) < m := by
      have : m₁ < m := lt_of_lt_of_le (Nat.lt_succ_self m₁) (le_max_right _ _)
      exact_mod_cast this
    rw [div_le_iff₀ hmR]
    have h2 := (div_lt_iff₀ hε).mp (hm₁.trans h1)
    linarith
  set d : Fin 4 → ℤ := fun i => round ((m : ℝ) * p i / (2 * Real.pi)) with hd
  set q : Fin 4 → ℝ := fun i => 2 * Real.pi * (d i : ℝ) / (m : ℝ) with hqd
  set e : ℝ := Real.pi / m with he
  have he0 : 0 ≤ e := by positivity
  have hpq : ∀ i, |p i - q i| ≤ e := by
    intro i
    have h1 := abs_sub_round ((m : ℝ) * p i / (2 * Real.pi))
    have h2 : p i - q i = (2 * Real.pi / m) * ((m : ℝ) * p i / (2 * Real.pi) - (d i : ℝ)) := by
      simp only [hqd]
      field_simp
    rw [h2, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / (m : ℝ))]
    calc _ ≤ 2 * Real.pi / (m : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = e := by rw [he]; ring
  have hq : IsMomentumAt (siteOfInt d : TorusSite m) q := ⟨d, rfl, fun i => rfl⟩
  have hL := symbolWithGradient_lower (hG m hNm) hc.le hq v
  set X : Fin 4 → Fin 4 → ℂ := fun μ ν => symbolWithGradient (bondKernelSymbol (Kf m)) q μ ν -
    symbolWithGradient (bondKernelSymbol (Kf N)) p μ ν with hX
  have hXb : ∀ μ ν, ‖X μ ν‖ ≤ M₁ * e + E + 4 * e := by
    intro μ ν
    have h1 := norm_symbol_sub_le_of_close hC hc₀ (hD m hNm) q p (e := e)
      (fun i => by rw [abs_sub_comm]; exact hpq i) μ ν
    have h2 := hE m hNm p μ ν
    have h3 : ‖((latticeMomentum q μ * latticeMomentum q ν - latticeMomentum p μ * latticeMomentum p ν : ℝ) : ℂ)‖ ≤
        4 * e := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have e1 : |latticeMomentum q μ - latticeMomentum p μ| ≤ e :=
        (abs_latticeMomentum_sub_le q p μ).trans (by rw [abs_sub_comm]; exact hpq μ)
      have e2 : |latticeMomentum q ν - latticeMomentum p ν| ≤ e :=
        (abs_latticeMomentum_sub_le q p ν).trans (by rw [abs_sub_comm]; exact hpq ν)
      have b1 := abs_latticeMomentum_le q μ
      have b2 := abs_latticeMomentum_le p ν
      have h4 : latticeMomentum q μ * latticeMomentum q ν - latticeMomentum p μ * latticeMomentum p ν =
          latticeMomentum q μ * (latticeMomentum q ν - latticeMomentum p ν) +
          (latticeMomentum q μ - latticeMomentum p μ) * latticeMomentum p ν := by ring
      rw [h4]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have t2 := abs_nonneg (latticeMomentum p ν)
      have t3 := abs_nonneg (latticeMomentum q ν - latticeMomentum p ν)
      have m1 := mul_le_mul b1 e2 t3 (by norm_num)
      have m2 := mul_le_mul e1 b2 t2 he0
      linarith
    have h5 : X μ ν = (bondKernelSymbol (Kf m) q μ ν - bondKernelSymbol (Kf m) p μ ν) -
        (bondKernelSymbol (Kf N) p μ ν - bondKernelSymbol (Kf m) p μ ν) +
        ((latticeMomentum q μ * latticeMomentum q ν - latticeMomentum p μ * latticeMomentum p ν : ℝ) : ℂ) := by
      simp only [hX, symbolWithGradient]
      push_cast
      ring
    rw [h5]
    refine (norm_add_le _ _).trans ?_
    have h6 := norm_sub_le (bondKernelSymbol (Kf m) q μ ν - bondKernelSymbol (Kf m) p μ ν)
      (bondKernelSymbol (Kf N) p μ ν - bondKernelSymbol (Kf m) p μ ν)
    linarith
  have hQ := abs_re_hermitian_le X _ hXb v
  have hsplit : (∑ a, ∑ b, (starRingEnd ℂ) (v a) * symbolWithGradient (bondKernelSymbol (Kf m)) q a b * v b) =
      (∑ a, ∑ b, (starRingEnd ℂ) (v a) * symbolWithGradient (bondKernelSymbol (Kf N)) p a b * v b) +
      ∑ μ, ∑ ν, (starRingEnd ℂ) (v μ) * X μ ν * v ν := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    simp only [hX]
    ring
  rw [hsplit, Complex.add_re] at hL
  have hsq : sqNorm (latticeMomentum p) ≤ sqNorm (latticeMomentum q) + 16 * e := by
    simp only [sqNorm]
    have : ∀ i, latticeMomentum p i ^ 2 ≤ latticeMomentum q i ^ 2 + 4 * e := by
      intro i
      have e1 := (abs_latticeMomentum_sub_le p q i).trans (hpq i)
      have b1 := abs_le.mp (abs_latticeMomentum_le p i)
      have b2 := abs_le.mp (abs_latticeMomentum_le q i)
      have e2 := abs_le.mp e1
      nlinarith
    calc _ ≤ ∑ i, (latticeMomentum q i ^ 2 + 4 * e) := Finset.sum_le_sum fun i _ => this i
      _ = _ := by rw [Finset.sum_add_distrib]; simp; ring
  have hκ1 : min c 1 ≤ 1 := min_le_right _ _
  have hQ2 := (abs_le.mp hQ).2
  have h7 : min c 1 * sqNorm (latticeMomentum p) * V ≤
      min c 1 * sqNorm (latticeMomentum q) * V + 16 * e * V := by
    calc min c 1 * sqNorm (latticeMomentum p) * V
        ≤ min c 1 * (sqNorm (latticeMomentum q) + 16 * e) * V := by gcongr
      _ = min c 1 * sqNorm (latticeMomentum q) * V + min c 1 * (16 * e) * V := by ring
      _ ≤ _ := by
          have : min c 1 * (16 * e) * V ≤ 1 * (16 * e) * V := by gcongr
          linarith
  have h8 : Λ / m = (4 * (M₁ + 4) + 16) * e * V := by
    rw [hΛ, he]; ring
  rw [h8] at hΛm
  nlinarith
end
section
private theorem holdsOnParameters_of_three {P Q R S : ParameterAssignment → ℝ → Prop}
    (h : ∀ T y, T.Admissible → P T y → Q T y → R T y → S T y)
    (hP : HoldsOnParameterFamilies P) (hQ : HoldsOnParameterFamilies Q) (hR : HoldsOnParameterFamilies R) :
    HoldsOnParameterFamilies S := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, h₁, H₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, h₂, H₂⟩ := hQ a ha
  obtain ⟨L₃, r₃, C₃, h₃, H₃⟩ := hR a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max C₁ (max C₂ C₃),
    fun c => lt_min (h₁ c) (lt_min (h₂ c) (h₃ c)), ?_⟩
  intro L hL hLL T hTa hTL hD hS hH hr hC
  obtain ⟨y₁, Y₁⟩ := H₁ L hL (le_trans (le_max_left _ _) hLL) T hTa hTL hD hS hH
    (hr.trans (min_le_left _ _)) ((le_max_left _ _).trans hC)
  obtain ⟨y₂, Y₂⟩ := H₂ L hL (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLL) T hTa hTL hD hS hH
    (hr.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (((le_max_left _ _).trans (le_max_right _ _)).trans hC)
  obtain ⟨y₃, Y₃⟩ := H₃ L hL (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLL) T hTa hTL hD hS hH
    (hr.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (((le_max_right _ _).trans (le_max_right _ _)).trans hC)
  refine ⟨max y₁ (max y₂ y₃), fun y hy hRet hRow => ?_⟩
  exact h T y hD (Y₁ y ((le_max_left _ _).trans hy) hRet hRow)
    (Y₂ y (((le_max_left _ _).trans (le_max_right _ _)).trans hy) hRet hRow)
    (Y₃ y (((le_max_right _ _).trans (le_max_right _ _)).trans hy) hRet hRow)
private theorem kernel_gauge_of_form {N : ℕ} [NeZero N] {K : TorusBond N → TorusBond N → ℝ}
    (hs : ∀ b b', K b b' = K b' b)
    (h : ∀ (φ : TorusSite N → ℝ) (A : TorusBond N → ℝ), ∑ b, ∑ b', latticeGradient φ b * K b b' * A b' = 0)
    (φ : TorusSite N → ℝ) (b : TorusBond N) : ∑ b', K b b' * latticeGradient φ b' = 0 := by
  have h1 := h φ fun c => if c = b then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hs, mul_comm]
private theorem add_two_le_exp {s : ℝ} (hs : 0 < s) (x : ℝ) (hx : 0 ≤ x) :
    x + 2 ≤ (1 / s + 2) * Real.exp (s * x) := by
  have h1 : s * x + 1 ≤ Real.exp (s * x) := Real.add_one_le_exp _
  have h2 : 1 ≤ Real.exp (s * x) := Real.one_le_exp (by positivity)
  have h3 : x ≤ 1 / s * Real.exp (s * x) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hs]
    linarith
  nlinarith
private theorem pow_four_le_exp {s : ℝ} (hs : 0 < s) (x : ℝ) (hx : 0 ≤ x) :
    x ^ 4 ≤ (1 / s) ^ 4 * 24 * Real.exp (s * x) := by
  have h := Real.pow_div_factorial_le_exp (s * x) (by positivity) 4
  have h4 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h4, div_le_iff₀ (by norm_num)] at h
  calc x ^ 4 = (1 / s) ^ 4 * (s * x) ^ 4 := by
        rw [← mul_pow]; congr 1; field_simp
    _ ≤ (1 / s) ^ 4 * (Real.exp (s * x) * 24) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring
private theorem exp_neg_mul_antitone {c c' : ℝ} (h : c ≤ c') {N : ℝ} (hN : 0 ≤ N) :
    Real.exp (-(c' * N)) ≤ Real.exp (-(c * N)) := by
  rw [Real.exp_le_exp]
  nlinarith
private theorem mul_le_sq_add {a e₂ e : ℝ} (ha : 0 ≤ a) (h2 : e₂ ≤ e) (h3 : 0 ≤ e₂) (h1 : e ≤ 1) :
    a * e₂ ≤ a ^ 2 + e := by
  by_cases h6 : a ≤ 1
  · nlinarith
  · push Not at h6
    nlinarith
private theorem constants_combine {A₁ A₂ D₂ M₄ A₄ Z e : ℝ} (h1 : 0 ≤ A₁) (h2 : 0 ≤ A₂) (h3 : 0 ≤ M₄)
    (h4 : 0 ≤ A₄) (hZ : 0 ≤ Z) (he : 0 ≤ e) :
    A₂ * e + D₂ * (Z + e) + 3 * Z * M₄ + A₁ * e ≤ (A₁ + A₂ + D₂ + 3 * M₄ + 4 * A₄) * (Z + e) := by
  have t1 := mul_nonneg h1 hZ
  have t2 := mul_nonneg h2 hZ
  have t3 := mul_nonneg h3 he
  have t4 := mul_nonneg h4 (add_nonneg hZ he)
  nlinarith
variable (Tb : ParameterAssignment) (y : ℝ)
private abbrev kernelAt (k : ℕ) {N : ℕ} [NeZero N] : TorusBond N → TorusBond N → ℝ :=
  maxwellKernel Tb.coupling (Tb.stepParameters y).side k
set_option maxHeartbeats 1000000 in
private theorem maxwellSymbolBounds_of (hDr : Tb.Admissible) (h0 : GradientMaxwellPropertiesAt Tb y)
    (h1 : maxwellKernelBoundsAt Tb y) (h2 : MaxwellKernelSecondMomentAt Tb y) :
    MaxwellSymbolBoundsAt Tb y := by
  obtain ⟨C₁, c₁, hc₁, H1⟩ := h1
  obtain ⟨C₂, c₂, hc₂, H2⟩ := h2
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = max C₁ 0 := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := hC₀ ▸ le_max_right _ _
  have hC₁₀ : C₁ ≤ C₀ := hC₀ ▸ le_max_left _ _
  obtain ⟨D₂, hD₂⟩ : ∃ D₂, D₂ = max C₂ 0 := ⟨_, rfl⟩
  have hD₂0 : 0 ≤ D₂ := hD₂ ▸ le_max_right _ _
  have hC₂₂ : C₂ ≤ D₂ := hD₂ ▸ le_max_left _ _
  have hcK : 0 < 2 * Tb.coercivity := by have := hDr.cK_pos; linarith
  have hgauge : ∀ (k N : ℕ) [NeZero N], Tb.n₀ ≤ N →
      IsGaugeKernel (kernelAt Tb y k : TorusBond N → TorusBond N → ℝ) (2 * Tb.coercivity) := by
    intro k N _ hN
    obtain ⟨s1, s2, s3, -, -⟩ := H1 k N hN
    obtain ⟨-, g2, g3⟩ := h0 k N hN
    exact ⟨s1, s2, s3, kernel_gauge_of_form s1 g2, g3⟩
  have hdecay : ∀ (k N : ℕ) [NeZero N], Tb.n₀ ≤ N → ∀ b b' : TorusBond N, |kernelAt Tb y k b b'| ≤
      C₀ * Real.exp (-(c₁ * (supDist b.1 b'.1 : ℝ))) := by
    intro k N _ hN b b'
    obtain ⟨-, -, -, s4, -⟩ := H1 k N hN
    exact (s4 b b').trans (mul_le_mul_of_nonneg_right hC₁₀ (Real.exp_pos _).le)
  obtain ⟨G₀, hG₀⟩ : ∃ G₀, G₀ = intGeomSum (c₁ / 2 / 4) ^ 4 := ⟨_, rfl⟩
  have hG₀0 : 0 ≤ G₀ := by rw [hG₀]; positivity
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = C₀ * G₀ * Real.exp (c₁ / 2) := ⟨_, rfl⟩
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hwrap : ∀ (k N : ℕ) [NeZero N], Tb.n₀ ≤ N → ∀ μ ν : Fin 4,
      ∑ x ∈ farSites N, |kernelAt Tb y k ((0 : TorusSite N), μ) (x, ν)| ≤
        A₁ * Real.exp (-(c₁ / 4 * (N : ℝ))) := by
    intro k N _ hN μ ν
    have h3 := kernel_tail_le hC₀0 hc₁ (hdecay k N hN) μ ν (farSites N) ((N : ℝ) / 2 - 1) (by
      intro x hx
      have := (Finset.mem_filter.mp hx).2
      linarith)
    refine h3.trans (le_of_eq ?_)
    rw [hA₁, hG₀, mul_assoc (C₀ * _), ← Real.exp_add]
    congr 2
    ring
  obtain ⟨s₈, hs₈⟩ : ∃ s₈, s₈ = c₁ / 8 := ⟨_, rfl⟩
  have hs₈0 : 0 < s₈ := by rw [hs₈]; positivity
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, A₂ = (1 / s₈ + 2) * A₁ := ⟨_, rfl⟩
  have hA₂0 : 0 ≤ A₂ := by rw [hA₂]; positivity
  obtain ⟨A₃, hA₃⟩ : ∃ A₃, A₃ = (1 / (c₁ / 2)) ^ 4 * 24 * Real.exp (c₁ / 2) := ⟨_, rfl⟩
  have hA₃0 : 0 ≤ A₃ := by rw [hA₃]; positivity
  obtain ⟨A₄, hA₄⟩ : ∃ A₄, A₄ = C₀ * A₃ + 2 * A₁ := ⟨_, rfl⟩
  have hA₄0 : 0 ≤ A₄ := by rw [hA₄]; positivity
  obtain ⟨M₄, hM₄⟩ : ∃ M₄, M₄ = kernelMomentBound C₀ c₁ 4 := ⟨_, rfl⟩
  have hM₄0 : 0 ≤ M₄ := by
    rw [hM₄, kernelMomentBound]
    have : 0 ≤ intGeomSum (c₁ / 2 / 4) ^ 4 := by positivity
    positivity
  obtain ⟨c, hcdef⟩ : ∃ c, c = min (min s₈ c₂) (min (2 * Tb.coercivity) 1) := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]
    exact lt_min (lt_min hs₈0 hc₂) (lt_min hcK one_pos)
  have hcs : c ≤ s₈ := hcdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ c₂ := hcdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hcκ : c ≤ min (2 * Tb.coercivity) 1 := hcdef ▸ min_le_right _ _
  obtain ⟨C, hCdef⟩ : ∃ C, C = A₁ + A₂ + D₂ + 3 * M₄ + 4 * A₄ := ⟨_, rfl⟩
  have hCA₄ : 4 * A₄ ≤ C := by rw [hCdef]; linarith [hA₁0, hA₂0, hD₂0, hM₄0]
  refine ⟨kernelMomentBound C₀ c₁, C, c, hc, ?_⟩
  intro k N _ hN
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hexpc : Real.exp (-(c * (N : ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hexp0 := Real.exp_pos (-(c * (N : ℝ)))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r μ ν p
    exact ⟨symbol_contDiff (K := kernelAt Tb y k) r μ ν,
      norm_iteratedFDeriv_symbol_le hC₀0 hc₁ (hdecay k N hN) r μ ν p⟩
  · intro p i μ ν
    exact symbol_periodShift (K := kernelAt Tb y k) p i μ ν
  · intro p μ ν
    obtain ⟨Tq, hT⟩ : ∃ Tq : ℝ, Tq = sqNorm p * (if μ = ν then 1 else 0) - p μ * p ν := ⟨_, rfl⟩
    rw [← hT]
    have hp0 : 0 ≤ sqNorm p := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hre := symbol_re_taylor_le (K := kernelAt Tb y k) hC₀0 hc₁ (hdecay k N hN) p μ ν Tq
    have him := (abs_symbol_im_le (hgauge k N hN) p μ ν).trans (hwrap k N hN μ ν)
    have hz := (abs_zeroth_moment_le (hgauge k N hN) μ ν).trans
      (mul_le_mul_of_nonneg_left (hwrap k N hN μ ν) (by positivity))
    have hm := H2 k N hN p μ ν
    have hlin : ∀ x : TorusSite N, linearPairing (bondMidDisplacement x μ ν) p =
        ∑ i, p i * (torusDisplacement (0 : TorusSite N) x i +
        ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) := fun x => by
      rw [linearPairing_apply]; rfl
    simp only [hlin] at hre
    rw [← hT] at hm
    obtain ⟨e, he⟩ : ∃ e, e = Real.exp (-(c * (N : ℝ))) := ⟨_, rfl⟩
    have he0 : 0 ≤ e := he ▸ hexp0.le
    have he1 : e ≤ 1 := he ▸ hexpc
    have hz2 : ((N : ℝ) + 2) * (A₁ * Real.exp (-(c₁ / 4 * (N : ℝ)))) ≤ A₂ * e := by
      have h3 := add_two_le_exp hs₈0 (N : ℝ) hNR
      have h4 : Real.exp (s₈ * (N : ℝ)) * Real.exp (-(c₁ / 4 * (N : ℝ))) = Real.exp (-(s₈ * (N : ℝ))) := by
        rw [← Real.exp_add]; congr 1; rw [hs₈]; ring
      calc ((N : ℝ) + 2) * (A₁ * Real.exp (-(c₁ / 4 * (N : ℝ))))
          ≤ ((1 / s₈ + 2) * Real.exp (s₈ * (N : ℝ))) * (A₁ * Real.exp (-(c₁ / 4 * (N : ℝ)))) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = A₂ * (Real.exp (s₈ * (N : ℝ)) * Real.exp (-(c₁ / 4 * (N : ℝ)))) := by rw [hA₂]; ring
        _ ≤ A₂ * e := by
            rw [h4, he]
            exact mul_le_mul_of_nonneg_left (exp_neg_mul_antitone hcs hNR) hA₂0
    have him2 : A₁ * Real.exp (-(c₁ / 4 * (N : ℝ))) ≤ A₁ * e := by
      rw [he]
      refine mul_le_mul_of_nonneg_left (exp_neg_mul_antitone ?_ hNR) hA₁0
      rw [hs₈] at hcs
      linarith
    have hm2 : C₂ * sqNorm p * Real.exp (-(c₂ * (N : ℝ))) ≤ D₂ * (sqNorm p ^ 2 + e) := by
      have e2 : Real.exp (-(c₂ * (N : ℝ))) ≤ e := he ▸ exp_neg_mul_antitone hc2 hNR
      have e3 : 0 < Real.exp (-(c₂ * (N : ℝ))) := Real.exp_pos _
      have h5 : sqNorm p * Real.exp (-(c₂ * (N : ℝ))) ≤ sqNorm p ^ 2 + e :=
        mul_le_sq_add hp0 e2 e3.le he1
      calc C₂ * sqNorm p * Real.exp (-(c₂ * (N : ℝ)))
          ≤ D₂ * sqNorm p * Real.exp (-(c₂ * (N : ℝ))) := by gcongr
        _ = D₂ * (sqNorm p * Real.exp (-(c₂ * (N : ℝ)))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h5 hD₂0
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, ← he]
    have hre' : |(maxwellSymbol Tb.coupling (Tb.stepParameters y).side k N p μ ν).re - Tq| ≤ _ := hre
    have him' : |(maxwellSymbol Tb.coupling (Tb.stepParameters y).side k N p μ ν).im| ≤ _ := him
    have hZ : 0 ≤ sqNorm p ^ 2 := sq_nonneg _
    have hfin : A₂ * e + D₂ * (sqNorm p ^ 2 + e) + 3 * sqNorm p ^ 2 * M₄ + A₁ * e ≤
        C * (sqNorm p ^ 2 + e) := by
      rw [hCdef]
      exact constants_combine hA₁0 hA₂0 hM₄0 hA₄0 hZ he0
    rw [← hM₄] at hre'
    have hm3 := hm.trans hm2
    change |(1 / 2 : ℝ) * (∑ x : TorusSite N, kernelAt Tb y k ((0 : TorusSite N), μ) (x, ν) * _) + Tq| ≤ _ at hm3
    linarith
  · intro p v
    obtain ⟨E, hE⟩ : ∃ E, E = ((N : ℝ) + 1) ^ 4 * (C₀ * Real.exp (-(c₁ * (N : ℝ)))) +
        2 * (C₀ * G₀ * Real.exp (-(c₁ / 2 * ((N : ℝ) / 4 - 1)))) := ⟨_, rfl⟩
    have hcmp : ∀ (m : ℕ) [NeZero m], N ≤ m → ∀ (p : Fin 4 → ℝ) (μ ν : Fin 4),
        ‖bondKernelSymbol (kernelAt Tb y k : TorusBond N → TorusBond N → ℝ) p μ ν -
          bondKernelSymbol (kernelAt Tb y k : TorusBond m → TorusBond m → ℝ) p μ ν‖ ≤ E := by
      intro m _ hm p μ ν
      obtain ⟨-, -, -, -, s5⟩ := H1 k N hN
      have h3 := norm_symbol_sub_le hm (K := kernelAt Tb y k) (K' := kernelAt Tb y k)
        (e := C₀ * Real.exp (-(c₁ * (N : ℝ)))) hC₀0 hc₁ (hdecay k N hN) (hdecay k m (hN.trans hm))
        (fun μ ν w hw => (s5 m hm μ ν w hw).trans
          (mul_le_mul_of_nonneg_right hC₁₀ (Real.exp_pos _).le)) (by positivity) p μ ν
      rw [hE, hG₀]
      exact h3
    have hL := symbolWithGradient_lower_everywhere (fun m _ => kernelAt Tb y k) hcK hC₀0 hc₁
      (fun m _ hm => hgauge k m (hN.trans hm)) (fun m _ hm => hdecay k m (hN.trans hm)) hcmp p v
    have hEle : E ≤ A₄ * Real.exp (-(c * (N : ℝ))) := by
      have hs2 : 0 < c₁ / 2 := by positivity
      have h4 := pow_four_le_exp hs2 ((N : ℝ) + 1) (by positivity)
      have h5 : ((N : ℝ) + 1) ^ 4 * Real.exp (-(c₁ * (N : ℝ))) ≤ A₃ * Real.exp (-(c * (N : ℝ))) := by
        have h6 : Real.exp (c₁ / 2 * ((N : ℝ) + 1)) * Real.exp (-(c₁ * (N : ℝ))) =
            Real.exp (c₁ / 2) * Real.exp (-(c₁ / 2 * (N : ℝ))) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        calc ((N : ℝ) + 1) ^ 4 * Real.exp (-(c₁ * (N : ℝ)))
            ≤ ((1 / (c₁ / 2)) ^ 4 * 24 * Real.exp (c₁ / 2 * ((N : ℝ) + 1))) * Real.exp (-(c₁ * (N : ℝ))) :=
              mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
          _ = A₃ * Real.exp (-(c₁ / 2 * (N : ℝ))) := by
              rw [mul_assoc ((1 / (c₁ / 2)) ^ 4 * 24), h6, hA₃]; ring
          _ ≤ _ := by
              refine mul_le_mul_of_nonneg_left (exp_neg_mul_antitone ?_ hNR) hA₃0
              rw [hs₈] at hcs
              linarith
      have h7 : C₀ * G₀ * Real.exp (-(c₁ / 2 * ((N : ℝ) / 4 - 1))) ≤ A₁ * Real.exp (-(c * (N : ℝ))) := by
        have h8 : Real.exp (-(c₁ / 2 * ((N : ℝ) / 4 - 1))) =
            Real.exp (c₁ / 2) * Real.exp (-(s₈ * (N : ℝ))) := by
          rw [← Real.exp_add]; congr 1; rw [hs₈]; ring
        rw [h8, hA₁, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left (exp_neg_mul_antitone hcs hNR) (by positivity)
      rw [hE, hA₄]
      have h9 := mul_le_mul_of_nonneg_left h5 hC₀0
      have h12 : ((N : ℝ) + 1) ^ 4 * (C₀ * Real.exp (-(c₁ * (N : ℝ)))) =
          C₀ * (((N : ℝ) + 1) ^ 4 * Real.exp (-(c₁ * (N : ℝ)))) := by ring
      have h13 : (C₀ * A₃ + 2 * A₁) * Real.exp (-(c * (N : ℝ))) =
          C₀ * (A₃ * Real.exp (-(c * (N : ℝ)))) + 2 * (A₁ * Real.exp (-(c * (N : ℝ)))) := by ring
      rw [h12, h13]
      linarith
    have hV0 : 0 ≤ ∑ m, ‖v m‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hsq : 0 ≤ sqNorm (latticeMomentum p) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine le_trans ?_ hL
    have h10 : c * sqNorm (latticeMomentum p) * ∑ m, ‖v m‖ ^ 2 ≤
        min (2 * Tb.coercivity) 1 * sqNorm (latticeMomentum p) * ∑ m, ‖v m‖ ^ 2 := by gcongr
    have h11 : 4 * E * ∑ m, ‖v m‖ ^ 2 ≤ C * Real.exp (-(c * (N : ℝ))) * ∑ m, ‖v m‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ hV0
      calc 4 * E ≤ 4 * (A₄ * Real.exp (-(c * (N : ℝ)))) := by linarith
        _ = (4 * A₄) * Real.exp (-(c * (N : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCA₄ hexp0.le
    linarith
  · intro Tt hT p hp p' hp'
    exact covariance_eq_fourierSum (hgauge k N hN) hcK Tt hT.1 hT.2 hp hp'
theorem maxwellSymbolStatement_of_kernel_bounds (h₀ : gradientMaxwellStatement)
    (h₁ : maxwellKernelBoundsStatement) (h₂ : maxwellKernelSecondMomentStatement) :
    maxwellSymbolStatement :=
  holdsOnParameters_of_three (fun T y hD a b c => maxwellSymbolBounds_of T y hD a b c) h₀ h₁ h₂
end
end ResponseInTheExpansion
end
end YangMills.Construction
