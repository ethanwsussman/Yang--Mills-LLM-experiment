import YangMills.Construction.PeriodicOperators.BoundOfTheKernelOfAMatrixFunctionProof
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Coordinates.ComplexCoordinates (stdBasisVector)
theorem intervalIntegral_translate_eq_of_periodic {ς : ℝ} (G : ℂ → ℂ)
    (hd : ∀ z : ℂ, |z.im| ≤ ς → DifferentiableAt ℂ G z)
    (hp : ∀ z : ℂ, |z.im| ≤ ς → G (z + 2 * Real.pi) = G z) {a w : ℂ} (ha : |a.im| ≤ ς)
    (hw : |w.im| ≤ ς) :
    ∫ t in (-Real.pi)..Real.pi, G ((t : ℂ) + a) = ∫ t in (-Real.pi)..Real.pi, G ((t : ℂ) + w) := by
  have hreal : ∀ (b : ℂ) (r : ℝ), |b.im| ≤ ς →
      ∫ t in (-Real.pi)..Real.pi, G ((t : ℂ) + (b + r)) =
        ∫ t in (-Real.pi)..Real.pi, G ((t : ℂ) + b) := by
    intro b r hb
    have hper : Function.Periodic (fun t : ℝ => G ((t : ℂ) + b)) (2 * Real.pi) := by
      intro t
      have := hp ((t : ℂ) + b) (by simpa using hb)
      show G _ = G _
      rw [← this]
      congr 1
      push_cast
      ring
    have h1 : ∫ t in (-Real.pi)..Real.pi, G ((t : ℂ) + (b + r)) =
        ∫ t in (-Real.pi + r)..(Real.pi + r), G ((t : ℂ) + b) := by
      rw [← intervalIntegral.integral_comp_add_right (fun t : ℝ => G ((t : ℂ) + b)) r]
      refine intervalIntegral.integral_congr fun t _ => ?_
      show G _ = G _
      congr 1
      push_cast
      ring
    rw [h1]
    have h2 := hper.intervalIntegral_add_eq (-Real.pi + r) (-Real.pi)
    have e1 : -Real.pi + r + 2 * Real.pi = Real.pi + r := by ring
    have e2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rwa [e1, e2] at h2
  have himag : ∀ u v : ℝ, |u| ≤ ς → |v| ≤ ς →
      ∫ t in (-Real.pi)..Real.pi, G ((t : ℂ) + u * Complex.I) =
        ∫ t in (-Real.pi)..Real.pi, G ((t : ℂ) + v * Complex.I) := by
    intro u v hu hv
    have hmem : ∀ y ∈ uIcc u v, |y| ≤ ς := by
      intro y hy
      rcases Set.mem_uIcc.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le.2 ⟨by linarith [(abs_le.1 hu).1], by linarith [(abs_le.1 hv).2]⟩
      · exact abs_le.2 ⟨by linarith [(abs_le.1 hv).1], by linarith [(abs_le.1 hu).2]⟩
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
      (((-Real.pi : ℝ) : ℂ) + u * Complex.I) (((Real.pi : ℝ) : ℂ) + v * Complex.I) (by
        intro z hz
        refine (hd z (hmem _ ?_)).differentiableWithinAt
        simpa using hz.2)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
      zero_add] at hrect
    have hside : ∫ y in u..v, G ((Real.pi : ℂ) + y * Complex.I) =
        ∫ y in u..v, G (((-Real.pi : ℝ) : ℂ) + y * Complex.I) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      have hy' : |y| ≤ ς := hmem y hy
      have := hp (((-Real.pi : ℝ) : ℂ) + y * Complex.I) (by simpa using hy')
      show G _ = G _
      rw [← this]
      congr 1
      push_cast
      ring
    rw [hside] at hrect
    have := sub_eq_zero.1 (by simpa using hrect)
    exact this
  have hdecomp : ∀ b : ℂ, |b.im| ≤ ς →
      ∫ t in (-Real.pi)..Real.pi, G ((t : ℂ) + b) =
        ∫ t in (-Real.pi)..Real.pi, G ((t : ℂ) + (b.im : ℝ) * Complex.I) := by
    intro b hb
    have := hreal ((b.im : ℝ) * Complex.I) b.re (by simpa using hb)
    rw [← this]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show G _ = G _
    congr 2
    rw [add_comm, Complex.re_add_im]
  rw [hdecomp a ha, hdecomp w hw]
  exact himag _ _ ha hw
abbrev boxMeasure : Measure AmbientSpace :=
  Measure.pi fun _ : Fin 4 => (volume : Measure ℝ).restrict (Icc (-Real.pi) Real.pi)
theorem setIntegral_box_eq (f : AmbientSpace → ℂ) :
    ∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), f κ = ∫ κ, f κ ∂boxMeasure := by
  rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
theorem integral_boxMeasure_eq_of_fibers (F F' : AmbientSpace → ℂ) (hF : Integrable F boxMeasure)
    (hF' : Integrable F' boxMeasure) (μ : Fin 4)
    (h : ∀ y : Fin 3 → ℝ, ∫ t in (-Real.pi)..Real.pi, F (μ.insertNth t y) =
      ∫ t in (-Real.pi)..Real.pi, F' (μ.insertNth t y)) :
    ∫ x, F x ∂boxMeasure = ∫ x, F' x ∂boxMeasure := by
  have mp := measurePreserving_piFinSuccAbove
    (fun _ : Fin 4 => (volume : Measure ℝ).restrict (Icc (-Real.pi) Real.pi)) μ
  have key : ∀ H : AmbientSpace → ℂ, Integrable H boxMeasure → ∫ x, H x ∂boxMeasure =
      ∫ y : Fin 3 → ℝ, (∫ t in (-Real.pi)..Real.pi, H (μ.insertNth t y)) ∂(Measure.pi fun _ : Fin 3 =>
        (volume : Measure ℝ).restrict (Icc (-Real.pi) Real.pi)) := by
    intro H hH
    have hsymm := mp.symm
    rw [← hsymm.integral_comp' H]
    have hi : Integrable (H ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) μ).symm) _ :=
      hsymm.integrable_comp_of_integrable hH
    refine (integral_prod_symm _ hi).trans ?_
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ∫ t in Icc (-Real.pi) Real.pi, H (μ.insertNth t y) =
      ∫ t in (-Real.pi)..Real.pi, H (μ.insertNth t y)
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Icc_eq_integral_Ioc]
  rw [key F hF, key F' hF']
  exact integral_congr_ae (Eventually.of_forall h)
structure StripRegular (ς : ℝ) (h : (Fin 4 → ℂ) → ℂ) : Prop where
  contOn : ContinuousOn h (imStrip ς)
  lineDiff : ∀ a ∈ imStrip ς, ∀ j : Fin 4,
    DifferentiableAt ℂ (fun ζ : ℂ => h (a + ζ • stdBasisVector j)) 0
  periodic : PeriodicOnStrip ς h
  bounded : BoundedOnStrip ς h
theorem stripRegular_of_holomorphic {ς : ℝ} {g : (Fin 4 → ℂ) → ℂ} (hh : HolomorphicNearStrip ς g)
    (hp : PeriodicOnStrip ς g) (hb : BoundedOnStrip ς g) : StripRegular ς g := by
  obtain ⟨O, hO, -, hc, hd⟩ := hh
  refine ⟨(continuousOn_pi.1 hc 0).mono hO, fun a ha j => ?_, hp, hb⟩
  exact differentiableAt_pi.1 (hd a (hO ha) j).self_of_nhds 0
theorem continuous_toComplexVec : Continuous toComplexVec := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
theorem toComplexVec_add_mem_imStrip {ς : ℝ} {a : Fin 4 → ℂ} (ha : a ∈ imStrip ς)
    (x : AmbientSpace) : toComplexVec x + a ∈ imStrip ς := by
  intro μ
  simpa [toComplexVec] using ha μ
theorem StripRegular.continuous_translate {ς : ℝ} {h : (Fin 4 → ℂ) → ℂ} (hN : StripRegular ς h)
    {a : Fin 4 → ℂ} (ha : a ∈ imStrip ς) :
    Continuous fun x : AmbientSpace => h (toComplexVec x + a) :=
  hN.contOn.comp_continuous (continuous_toComplexVec.add continuous_const)
    (toComplexVec_add_mem_imStrip ha)
theorem StripRegular.integrable_translate {ς : ℝ} {h : (Fin 4 → ℂ) → ℂ} (hN : StripRegular ς h)
    {a : Fin 4 → ℂ} (ha : a ∈ imStrip ς) :
    Integrable (fun x : AmbientSpace => h (toComplexVec x + a)) boxMeasure := by
  obtain ⟨C, hC⟩ := hN.bounded
  exact Integrable.of_bound (hN.continuous_translate ha).aestronglyMeasurable C
    (Eventually.of_forall fun x => hC _ (toComplexVec_add_mem_imStrip ha x))
theorem StripRegular.integral_update_eq {ς : ℝ} {h : (Fin 4 → ℂ) → ℂ} (hN : StripRegular ς h)
    {a : Fin 4 → ℂ} (ha : a ∈ imStrip ς) (μ : Fin 4) {w : ℂ} (hw : |w.im| ≤ ς) :
    ∫ x, h (toComplexVec x + Function.update a μ w) ∂boxMeasure =
      ∫ x, h (toComplexVec x + a) ∂boxMeasure := by
  have hu : ∀ b : ℂ, |b.im| ≤ ς → Function.update a μ b ∈ imStrip ς := by
    intro b hb ν
    by_cases e : ν = μ
    · subst e; simpa using hb
    · simpa [Function.update_of_ne e] using ha ν
  refine integral_boxMeasure_eq_of_fibers _ _ (hN.integrable_translate (hu w hw))
    (hN.integrable_translate ha) μ fun y => ?_
  let p : Fin 4 → ℂ := toComplexVec (μ.insertNth (0 : ℝ) y) + Function.update a μ 0
  let G : ℂ → ℂ := fun z => h (p + z • stdBasisVector μ)
  have hpt : ∀ z : ℂ, p + z • stdBasisVector μ =
      toComplexVec (μ.insertNth (0 : ℝ) y) + Function.update a μ z := by
    intro z
    funext ν
    by_cases e : ν = μ
    · subst e; simp [p, stdBasisVector, toComplexVec]
    · simp [p, stdBasisVector, Function.update_of_ne e, Pi.single_eq_of_ne e]
  have hmem : ∀ z : ℂ, |z.im| ≤ ς → p + z • stdBasisVector μ ∈ imStrip ς := by
    intro z hz
    rw [hpt]
    exact toComplexVec_add_mem_imStrip (hu z hz) _
  have hval : ∀ (t : ℝ) (b : ℂ), toComplexVec (μ.insertNth t y) + Function.update a μ b =
      p + ((t : ℂ) + b) • stdBasisVector μ := by
    intro t b
    rw [hpt]
    funext ν
    by_cases e : ν = μ
    · subst e; simp [toComplexVec]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq e
      simp [toComplexVec]
  have hGd : ∀ z : ℂ, |z.im| ≤ ς → DifferentiableAt ℂ G z := by
    intro z hz
    have h0 := hN.lineDiff _ (hmem z hz) μ
    have h1 : DifferentiableAt ℂ (fun z' : ℂ => z' - z) z := by fun_prop
    have h2 : DifferentiableAt ℂ
        ((fun ζ : ℂ => h (p + z • stdBasisVector μ + ζ • stdBasisVector μ)) ∘
          fun z' : ℂ => z' - z) z :=
      DifferentiableAt.comp z (by simpa using h0) h1
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun z' => ?_)
    have e : z + (z' - z) = z' := by ring
    have e' : p + z' • stdBasisVector μ =
        p + z • stdBasisVector μ + (z' - z) • stdBasisVector μ := by
      have e2 := add_smul z (z' - z) (stdBasisVector μ)
      rw [e] at e2
      rw [e2]
      exact (add_assoc _ _ _).symm
    exact congrArg h e'
  have hGp : ∀ z : ℂ, |z.im| ≤ ς → G (z + 2 * Real.pi) = G z := by
    intro z hz
    have hper : (Pi.single μ (2 * Real.pi) : AmbientSpace) ∈ periodLattice := by
      refine ⟨Pi.single μ 1, fun ν => ?_⟩
      by_cases e : ν = μ
      · subst e; simp
      · simp [Pi.single_eq_of_ne e]
    have := hN.periodic _ (hmem z hz) _ hper
    show h _ = h _
    rw [← this]
    congr 1
    funext ν
    by_cases e : ν = μ
    · subst e; simp [stdBasisVector, toComplexVec]; ring
    · simp [stdBasisVector, toComplexVec, Pi.single_eq_of_ne e]
  have key := intervalIntegral_translate_eq_of_periodic G hGd hGp hw
    (show |(a μ).im| ≤ ς from ha μ)
  have e1 : ∀ x : ℝ, toComplexVec (μ.insertNth x y) + a =
      toComplexVec (μ.insertNth x y) + Function.update a μ (a μ) := by
    intro x; rw [Function.update_eq_self]
  simp only [e1, hval]
  exact key
theorem StripRegular.integral_translate_eq {ς : ℝ} (hς : 0 ≤ ς) {h : (Fin 4 → ℂ) → ℂ}
    (hN : StripRegular ς h) {ϑ : Fin 4 → ℂ} (hϑ : ϑ ∈ imStrip ς) :
    ∫ x, h (toComplexVec x + ϑ) ∂boxMeasure = ∫ x, h (toComplexVec x) ∂boxMeasure := by
  have hb : ∀ S : Finset (Fin 4), (fun ν => if ν ∈ S then ϑ ν else 0) ∈ imStrip ς := by
    intro S ν
    by_cases e : ν ∈ S
    · simpa [e] using hϑ ν
    · simpa [e] using hς
  have hS : ∀ S : Finset (Fin 4),
      ∫ x, h (toComplexVec x + fun ν => if ν ∈ S then ϑ ν else 0) ∂boxMeasure =
        ∫ x, h (toComplexVec x) ∂boxMeasure := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, if_false]; simp [Pi.add_def]
    | insert i S hi ih =>
      have e : (fun ν => if ν ∈ insert i S then ϑ ν else 0) =
          Function.update (fun ν => if ν ∈ S then ϑ ν else 0) i (ϑ i) := by
        funext ν
        by_cases e : ν = i
        · subst e; simp
        · simp [e]
      rw [e, hN.integral_update_eq (hb S) i (hϑ i), ih]
  simpa using hS Finset.univ
theorem StripRegular.torusAverage_translate {ς : ℝ} (hς : 0 ≤ ς) {h : (Fin 4 → ℂ) → ℂ}
    (hN : StripRegular ς h) {ϑ : Fin 4 → ℂ} (hϑ : ϑ ∈ imStrip ς) :
    (torusAverage fun κ => h (toComplexVec κ + ϑ)) = torusAverage fun κ => h (toComplexVec κ) := by
  unfold torusAverage
  rw [setIntegral_box_eq, setIntegral_box_eq, hN.integral_translate_eq hς hϑ]
theorem norm_torusAverage_le (f : AmbientSpace → ℂ) {C : ℝ} (hC : ∀ κ, ‖f κ‖ ≤ C) :
    ‖torusAverage f‖ ≤ C := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.norm_torusAverage_le <;> assumption
def expChar (n : Fin 4 → ℤ) (κ : Fin 4 → ℂ) : ℂ :=
  Complex.exp (-(Complex.I * bilinDot (toComplexVec (castVec n)) κ))
theorem bilinDot_add_right (x κ κ' : Fin 4 → ℂ) :
    bilinDot x (κ + κ') = bilinDot x κ + bilinDot x κ' := by
  simp [bilinDot, mul_add, Finset.sum_add_distrib]
theorem expChar_add (n : Fin 4 → ℤ) (κ κ' : Fin 4 → ℂ) :
    expChar n (κ + κ') = expChar n κ * expChar n κ' := by
  simp only [expChar, bilinDot_add_right, ← Complex.exp_add]
  congr 1
  ring
theorem norm_expChar (n : Fin 4 → ℤ) (κ : Fin 4 → ℂ) :
    ‖expChar n κ‖ = Real.exp (∑ μ, (n μ : ℝ) * (κ μ).im) := by
  rw [expChar, Complex.norm_exp]
  congr 1
  simp [bilinDot, toComplexVec, castVec, Complex.mul_re]
theorem expChar_period (n : Fin 4 → ℤ) {p : AmbientSpace} (hp : p ∈ periodLattice) :
    expChar n (toComplexVec p) = 1 := by
  obtain ⟨m, hm⟩ := hp
  rw [expChar, Complex.exp_eq_one_iff]
  refine ⟨-∑ μ, n μ * m μ, ?_⟩
  simp only [bilinDot, toComplexVec, castVec, hm]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring
theorem continuous_expChar (n : Fin 4 → ℤ) : Continuous (expChar n) := by
  unfold expChar bilinDot
  fun_prop
theorem differentiable_expChar_line (n : Fin 4 → ℤ) (a e : Fin 4 → ℂ) :
    Differentiable ℂ fun ζ : ℂ => expChar n (a + ζ • e) := by
  simp only [expChar, bilinDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop
theorem StripRegular.mul_expChar {ς : ℝ} {h : (Fin 4 → ℂ) → ℂ} (hN : StripRegular ς h)
    (n : Fin 4 → ℤ) : StripRegular ς fun κ => h κ * expChar n κ := by
  refine ⟨hN.contOn.mul (continuous_expChar n).continuousOn, fun a ha j => ?_, ?_, ?_⟩
  · exact (hN.lineDiff a ha j).mul (differentiable_expChar_line n a _ 0)
  · intro κ hκ p hp
    show h _ * expChar n _ = h _ * expChar n _
    rw [expChar_add, expChar_period n hp, mul_one, hN.periodic κ hκ p hp]
  · obtain ⟨C, hC⟩ := hN.bounded
    refine ⟨C * Real.exp (∑ μ, |(n μ : ℝ)| * ς), fun κ hκ => ?_⟩
    rw [norm_mul, norm_expChar]
    refine mul_le_mul (hC κ hκ) ?_ (Real.exp_pos _).le ((norm_nonneg _).trans (hC κ hκ))
    refine Real.exp_le_exp.2 (Finset.sum_le_sum fun μ _ => ?_)
    calc (n μ : ℝ) * (κ μ).im ≤ |(n μ : ℝ) * (κ μ).im| := le_abs_self _
      _ = |(n μ : ℝ)| * |(κ μ).im| := abs_mul _ _
      _ ≤ |(n μ : ℝ)| * ς := by gcongr; exact hκ μ
def fourierCoeff4 (g : (Fin 4 → ℂ) → ℂ) (n : Fin 4 → ℤ) : ℂ :=
  torusAverage fun κ => g (toComplexVec κ) * expChar n (toComplexVec κ)
theorem StripRegular.norm_le_stripSup {ς : ℝ} {g : (Fin 4 → ℂ) → ℂ} (hN : StripRegular ς g)
    {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip ς) : ‖g κ‖ ≤ stripSup ς g := by
  obtain ⟨C, hC⟩ := hN.bounded
  have hb : BddAbove (range fun κ : imStrip ς => ‖g κ‖) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hC x x.2
  exact le_ciSup hb (⟨κ, hκ⟩ : imStrip ς)
theorem StripRegular.norm_fourierCoeff4_le {ς : ℝ} (hς : 0 < ς) {g : (Fin 4 → ℂ) → ℂ}
    (hN : StripRegular ς g) (n : Fin 4 → ℤ) :
    ‖fourierCoeff4 g n‖ ≤ stripSup ς g * ∏ μ, Real.exp (-ς * |(n μ : ℝ)|) := by
  let ϑ : Fin 4 → ℂ := fun μ => ((-(ς * ((n μ).sign : ℝ)) : ℝ) : ℂ) * Complex.I
  have him : ∀ μ, (ϑ μ).im = -(ς * ((n μ).sign : ℝ)) := by
    intro μ
    simp [ϑ]
  have hsign : ∀ μ, |((n μ).sign : ℝ)| ≤ 1 := by
    intro μ
    rcases lt_trichotomy (n μ) 0 with h | h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [h]
    · simp [Int.sign_eq_one_of_pos h]
  have hϑ : ϑ ∈ imStrip ς := by
    intro μ
    rw [him, abs_neg, abs_mul, abs_of_pos hς]
    exact mul_le_of_le_one_right hς.le (hsign μ)
  have hshift := (hN.mul_expChar n).torusAverage_translate hς.le hϑ
  rw [fourierCoeff4, ← hshift]
  refine norm_torusAverage_le _ fun κ => ?_
  rw [norm_mul, norm_expChar, ← Real.exp_sum]
  refine mul_le_mul (hN.norm_le_stripSup (toComplexVec_add_mem_imStrip hϑ κ)) (le_of_eq ?_)
    (Real.exp_pos _).le
    ((norm_nonneg _).trans (hN.norm_le_stripSup (toComplexVec_add_mem_imStrip hϑ κ)))
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  have : (toComplexVec κ + ϑ) μ = (κ μ : ℂ) + ϑ μ := rfl
  rw [this, Complex.add_im, Complex.ofReal_im, zero_add, him]
  have hs : (n μ : ℝ) * ((n μ).sign : ℝ) = |(n μ : ℝ)| := by
    rw [← Int.cast_mul, Int.mul_sign_self]
    simp [Nat.cast_natAbs, Int.cast_abs]
  linear_combination (-ς) * hs
theorem hasSum_prod_mul_of_nonneg {α β : Type} (f : α → ℝ) (g : β → ℝ) (hf : ∀ m, 0 ≤ f m)
    (hg : ∀ m, 0 ≤ g m) {A B : ℝ} (h1 : HasSum f A) (h2 : HasSum g B) :
    HasSum (fun x : α × β => f x.1 * g x.2) (A * B) := by
  have h1' : Summable fun m => ‖f m‖ :=
    h1.summable.congr fun m => by rw [Real.norm_of_nonneg (hf m)]
  have h2' : Summable fun m => ‖g m‖ :=
    h2.summable.congr fun m => by rw [Real.norm_of_nonneg (hg m)]
  exact h1.mul h2 (summable_mul_of_summable_norm h1' h2')
theorem hasSum_prod_pi (a : ℤ → ℝ) (ha : ∀ m, 0 ≤ a m) (hs : Summable a) (d : ℕ) :
    HasSum (fun n : Fin d → ℤ => ∏ i, a (n i)) ((∑' m, a m) ^ d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hprod : HasSum (fun x : ℤ × (Fin d → ℤ) => a x.1 * ∏ i, a (x.2 i))
        ((∑' m, a m) * (∑' m, a m) ^ d) :=
      hasSum_prod_mul_of_nonneg a (fun n : Fin d → ℤ => ∏ i, a (n i)) ha
        (fun n => Finset.prod_nonneg fun i _ => ha _) hs.hasSum ih
    rw [pow_succ']
    convert ((Fin.consEquiv fun _ => ℤ).symm.hasSum_iff).2 hprod using 1
    funext n
    simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]
theorem hasSum_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    HasSum (fun m : ℤ => Real.exp (-c * |(m : ℝ)|)) (1 + 2 * (Real.exp c - 1)⁻¹) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hg := hasSum_geometric_of_lt_one hr0 hr1
  have h1 : HasSum (fun n : ℕ => Real.exp (-c * |((n : ℤ) : ℝ)|)) (1 - Real.exp (-c))⁻¹ := by
    convert hg using 1
    funext n
    rw [← Real.exp_nat_mul]
    simp only [Int.cast_natCast, Nat.abs_cast]
    congr 1
    ring
  have h2 : HasSum (fun n : ℕ => Real.exp (-c * |((-((n : ℤ) + 1) : ℤ) : ℝ)|))
      (Real.exp (-c) * (1 - Real.exp (-c))⁻¹) := by
    have e : (fun n : ℕ => Real.exp (-c * |((-((n : ℤ) + 1) : ℤ) : ℝ)|)) =
        fun n : ℕ => Real.exp (-c) * Real.exp (-c) ^ n := by
      funext n
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      have : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
        push_cast
        rw [abs_neg, abs_of_nonneg (by positivity)]
      rw [this]
      congr 1
      ring
    rw [e]
    exact hg.mul_left (Real.exp (-c))
  have h3 : HasSum (fun m : ℤ => Real.exp (-c * |(m : ℝ)|))
      ((1 - Real.exp (-c))⁻¹ + Real.exp (-c) * (1 - Real.exp (-c))⁻¹) :=
    HasSum.of_nat_of_neg_add_one h1 h2
  suffices e : 1 + 2 * (Real.exp c - 1)⁻¹ =
      (1 - Real.exp (-c))⁻¹ + Real.exp (-c) * (1 - Real.exp (-c))⁻¹ by
    rw [e]; exact h3
  have hE : Real.exp (-c) = (Real.exp c)⁻¹ := Real.exp_neg c
  have hc1 : 1 < Real.exp c := by rw [Real.one_lt_exp_iff]; exact hc
  have hne : Real.exp c - 1 ≠ 0 := by linarith
  have hne' : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  rw [hE]
  field_simp
  ring
theorem sum_exp_root_of_unity {s : ℕ} (hs : 0 < s) (m : ℤ) :
    ∑ j : Fin s, Complex.exp (Complex.I * ((m : ℂ) * (((j : ℕ) : ℂ) * (2 * Real.pi / s)))) =
      if (s : ℤ) ∣ m then (s : ℂ) else 0 := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set ζ : ℂ := Complex.exp (Complex.I * ((m : ℂ) * (2 * Real.pi / s))) with hζ
  have hterm : ∀ j : Fin s,
      Complex.exp (Complex.I * ((m : ℂ) * (((j : ℕ) : ℂ) * (2 * Real.pi / s)))) = ζ ^ (j : ℕ) := by
    intro j
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun j => ζ ^ j) s]
  have hζ1 : ζ = 1 ↔ (s : ℤ) ∣ m := by
    rw [hζ, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h2 : (m : ℂ) = (s : ℂ) * k := by
        have hI : Complex.I ≠ 0 := Complex.I_ne_zero
        field_simp at hk
        exact hk
      exact_mod_cast h2
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      push_cast
      field_simp
  by_cases hd : (s : ℤ) ∣ m
  · rw [if_pos hd, hζ1.2 hd]
    simp
  · rw [if_neg hd]
    have hne : ζ ≠ 1 := fun h => hd (hζ1.1 h)
    have hpow : ζ ^ s = 1 := by
      rw [hζ, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      field_simp
    rw [geom_sum_eq hne, hpow]
    simp
theorem toComplexVec_add (x y : AmbientSpace) :
    toComplexVec (x + y) = toComplexVec x + toComplexVec y := by apply _root_.YangMills.Construction.PeriodicOperators.CovariantFiniteRangeProof.toComplexVec_add <;> assumption
theorem toComplexVec_mem_imStrip {ς : ℝ} (hς : 0 ≤ ς) (x : AmbientSpace) :
    toComplexVec x ∈ imStrip ς := by
  intro μ
  simpa [toComplexVec] using hς
def latticePoint (s : ℕ) (k : Fin 4 → Fin s) : dualLattice s :=
  ⟨fun μ => ((k μ : ℕ) : ℝ) * (2 * Real.pi / s), fun μ => ((k μ : ℕ) : ℤ), fun μ => by simp⟩
def latticeClass (s : ℕ) (k : Fin 4 → Fin s) : DualClasses s :=
  QuotientAddGroup.mk (latticePoint s k)
theorem dualClasses_mk_eq_iff {s : ℕ} {a b : dualLattice s} :
    (QuotientAddGroup.mk a : DualClasses s) = QuotientAddGroup.mk b ↔
      -(a : AmbientSpace) + (b : AmbientSpace) ∈ periodLattice := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  rfl
theorem latticeClass_bijective {s : ℕ} (hs : 0 < s) : Function.Bijective (latticeClass s) := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hpi := Real.pi_ne_zero
  constructor
  · intro k k' h
    obtain ⟨m, hm⟩ := dualClasses_mk_eq_iff.1 h
    funext μ
    have h1 := hm μ
    have h2 : -((latticePoint s k : AmbientSpace) μ) + (latticePoint s k' : AmbientSpace) μ =
        ((m μ : ℤ) : ℝ) * (2 * Real.pi) := h1
    have h3 : (((k' μ : ℕ) : ℝ) - ((k μ : ℕ) : ℝ)) = (m μ : ℝ) * s := by
      simp only [latticePoint] at h2
      field_simp at h2
      linarith
    have h4 : ((k' μ : ℕ) : ℤ) - ((k μ : ℕ) : ℤ) = m μ * s := by exact_mod_cast h3
    have h5 : ((k' μ : ℕ) : ℤ) - ((k μ : ℕ) : ℤ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd (m := (s : ℤ)) ⟨m μ, by rw [h4]; ring⟩ ?_
      have := (k μ).isLt
      have := (k' μ).isLt
      rw [abs_lt]
      constructor <;> omega
    apply Fin.ext
    omega
  · intro c
    induction c using QuotientAddGroup.induction_on with
    | H z =>
      obtain ⟨x, n, hn⟩ := z
      have hz : (0 : ℤ) < s := by exact_mod_cast hs
      let k : Fin 4 → Fin s := fun μ =>
        ⟨(n μ % s).toNat, by
          have h1 := Int.emod_nonneg (n μ) hz.ne'
          have h2 := Int.emod_lt_of_pos (n μ) hz
          omega⟩
      refine ⟨k, dualClasses_mk_eq_iff.2 ⟨fun μ => n μ / s, fun μ => ?_⟩⟩
      have hk : (((k μ : ℕ) : ℤ)) = n μ % s := by
        have h1 := Int.emod_nonneg (n μ) hz.ne'
        show (((n μ % s).toNat : ℕ) : ℤ) = _
        omega
      have h1 := Int.emod_add_mul_ediv (n μ) (s : ℤ)
      have h2 : ((k μ : ℕ) : ℝ) + (s : ℝ) * ((n μ / s : ℤ) : ℝ) = (n μ : ℝ) := by
        have : ((k μ : ℕ) : ℤ) + (s : ℤ) * (n μ / s) = n μ := by rw [hk]; exact h1
        exact_mod_cast this
      show -((latticePoint s k : AmbientSpace) μ) + x μ = _
      simp only [latticePoint]
      rw [hn μ, ← h2]
      field_simp
      ring
theorem StripRegular.classSum_eq_sum_latticePoint {ς : ℝ} (hς : 0 ≤ ς) {g : (Fin 4 → ℂ) → ℂ}
    (hN : StripRegular ς g) {s : ℕ} (hs : 0 < s) :
    classSum s g = ∑ k, g (toComplexVec (latticePoint s k : AmbientSpace)) := by
  have : Finite (DualClasses s) := Finite.of_surjective _ (latticeClass_bijective hs).2
  unfold classSum
  rw [← finsum_comp (latticeClass s) (latticeClass_bijective hs), finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun k _ => ?_
  set o : dualLattice s := Quotient.out (latticeClass s k) with ho
  have h1 : (QuotientAddGroup.mk o : DualClasses s) = QuotientAddGroup.mk (latticePoint s k) :=
    QuotientAddGroup.out_eq' _
  have h2 := dualClasses_mk_eq_iff.1 h1
  have h3 := hN.periodic _ (toComplexVec_mem_imStrip hς (o : AmbientSpace)) _ h2
  rw [← toComplexVec_add] at h3
  rw [← h3]
  congr 2
  abel
theorem expChar_latticePoint (s : ℕ) (n : Fin 4 → ℤ) (k : Fin 4 → Fin s) :
    expChar (-n) (toComplexVec (latticePoint s k : AmbientSpace)) =
      ∏ μ, Complex.exp (Complex.I * ((n μ : ℂ) * (((k μ : ℕ) : ℂ) * (2 * Real.pi / s)))) := by
  rw [expChar, ← Complex.exp_sum]
  congr 1
  simp only [bilinDot, toComplexVec, castVec, latticePoint, Pi.neg_apply]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring
theorem sum_expChar_latticePoint {s : ℕ} (hs : 0 < s) (n : Fin 4 → ℤ) :
    ∑ k, expChar (-n) (toComplexVec (latticePoint s k : AmbientSpace)) =
      if ∀ μ, (s : ℤ) ∣ n μ then (s : ℂ) ^ 4 else 0 := by
  simp only [expChar_latticePoint]
  have h := Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset (Fin s)))
    (fun μ j => Complex.exp (Complex.I * ((n μ : ℂ) * (((j : ℕ) : ℂ) * (2 * Real.pi / s)))))
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp only [sum_exp_root_of_unity hs]
  rw [Finset.prod_ite_zero]
  simp
def toUnitTorus : AmbientSpace → UnitAddTorus (Fin 4) := fun x μ => (x μ : UnitAddCircle)
theorem isOpenQuotientMap_toUnitTorus : IsOpenQuotientMap toUnitTorus :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
theorem mFourier_toUnitTorus (n : Fin 4 → ℤ) (x : AmbientSpace) :
    UnitAddTorus.mFourier (-n) (toUnitTorus x) =
      expChar n (toComplexVec ((2 * Real.pi) • x)) := by
  rw [UnitAddTorus.mFourier, ContinuousMap.coe_mk, expChar]
  simp only [toUnitTorus, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [bilinDot, toComplexVec, castVec, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [div_one]
  ring
theorem StripRegular.exists_torus_lift {ς : ℝ} (hς : 0 ≤ ς) {g : (Fin 4 → ℂ) → ℂ}
    (hN : StripRegular ς g) :
    ∃ F : C(UnitAddTorus (Fin 4), ℂ), ∀ x : AmbientSpace,
      F (toUnitTorus x) = g (toComplexVec ((2 * Real.pi) • x)) := by
  have hc : Continuous fun x : AmbientSpace => g (toComplexVec ((2 * Real.pi) • x)) :=
    hN.contOn.comp_continuous (continuous_toComplexVec.comp (continuous_const_smul _))
      fun x => toComplexVec_mem_imStrip hς _
  have hf : Function.FactorsThrough
      (fun x : AmbientSpace => g (toComplexVec ((2 * Real.pi) • x))) toUnitTorus := by
    intro x y hxy
    have hm : ∀ μ, ∃ m : ℤ, y μ = x μ + m := by
      intro μ
      have h1 : (x μ : UnitAddCircle) = y μ := congrFun hxy μ
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h1)
      refine ⟨m, ?_⟩
      simp only [zsmul_eq_mul, mul_one] at hm
      linarith
    choose m hm using hm
    have hp : (fun μ => (m μ : ℝ) * (2 * Real.pi) : AmbientSpace) ∈ periodLattice :=
      ⟨m, fun μ => rfl⟩
    have h := hN.periodic _ (toComplexVec_mem_imStrip hς ((2 * Real.pi) • x)) _ hp
    show g _ = g _
    rw [← h, ← toComplexVec_add]
    congr 2
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, hm μ]
    ring
  let q : C(AmbientSpace, UnitAddTorus (Fin 4)) :=
    ⟨toUnitTorus, isOpenQuotientMap_toUnitTorus.continuous⟩
  have hq : Topology.IsQuotientMap q := isOpenQuotientMap_toUnitTorus.isQuotientMap
  exact ⟨hq.lift ⟨_, hc⟩ hf, fun x => DFunLike.congr_fun (hq.lift_comp ⟨_, hc⟩ hf) x⟩
theorem mFourierCoeff_eq_fourierCoeff4 {g : (Fin 4 → ℂ) → ℂ} {F : C(UnitAddTorus (Fin 4), ℂ)}
    (hF : ∀ x : AmbientSpace, F (toUnitTorus x) = g (toComplexVec ((2 * Real.pi) • x)))
    (n : Fin 4 → ℤ) :
    UnitAddTorus.mFourierCoeff F n = fourierCoeff4 g n := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral F n (fun _ => -(1 / 2))]
  let Ψ : AmbientSpace → ℂ := fun κ => g (toComplexVec κ) * expChar n (toComplexVec κ)
  have e1 : ∀ x : AmbientSpace, UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle)) •
      F (fun i => (x i : UnitAddCircle)) = Ψ ((2 * Real.pi) • x) := by
    intro x
    show UnitAddTorus.mFourier (-n) (toUnitTorus x) • F (toUnitTorus x) = _
    rw [hF x, mFourier_toUnitTorus, smul_eq_mul, mul_comm]
  simp only [e1]
  have hpos : 0 < 2 * Real.pi := by positivity
  rw [Measure.setIntegral_comp_smul_of_pos volume Ψ _ hpos]
  have hset : (2 * Real.pi) • {x : Fin 4 → ℝ | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + 1)} =
      Set.pi univ fun i : Fin 4 => Ioc ((fun _ : Fin 4 => -Real.pi) i) ((fun _ => Real.pi) i) := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hpos.ne']
    simp only [Set.mem_ofPred_eq, Set.mem_pi, mem_univ, true_imp_iff, Pi.smul_apply, smul_eq_mul,
      mem_Ioc]
    refine forall_congr' fun i => ?_
    have e : x i = (2 * Real.pi) * ((2 * Real.pi)⁻¹ * x i) := by field_simp
    generalize (2 * Real.pi)⁻¹ * x i = t at e ⊢
    rw [e]
    have hp := Real.pi_pos
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  rw [hset, Module.finrank_fin_fun, volume_pi, setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc,
    ← volume_pi]
  unfold fourierCoeff4 torusAverage
  rw [Complex.real_smul]
theorem StripRegular.summable_fourierCoeff4 {ς : ℝ} (hς : 0 < ς) {g : (Fin 4 → ℂ) → ℂ}
    (hN : StripRegular ς g) : Summable (fourierCoeff4 g) := by
  have hA := hasSum_prod_pi (fun m : ℤ => Real.exp (-ς * |(m : ℝ)|))
    (fun _ => (Real.exp_pos _).le) (hasSum_exp_neg_mul_abs hς).summable 4
  exact Summable.of_norm_bounded
    (g := fun n : Fin 4 → ℤ => stripSup ς g * ∏ μ, Real.exp (-ς * |(n μ : ℝ)|))
    (hA.summable.mul_left _) fun n => hN.norm_fourierCoeff4_le hς n
theorem StripRegular.hasSum_fourierSeries {ς : ℝ} (hς : 0 < ς) {g : (Fin 4 → ℂ) → ℂ}
    (hN : StripRegular ς g) (x : AmbientSpace) :
    HasSum (fun n => fourierCoeff4 g n * expChar (-n) (toComplexVec x)) (g (toComplexVec x)) := by
  obtain ⟨F, hF⟩ := hN.exists_torus_lift hς.le
  have hco : UnitAddTorus.mFourierCoeff F = fourierCoeff4 g :=
    funext (mFourierCoeff_eq_fourierCoeff4 hF)
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := F)
    (by rw [hco]; exact hN.summable_fourierCoeff4 hς) (toUnitTorus ((2 * Real.pi)⁻¹ • x))
  have hpos : 2 * Real.pi ≠ 0 := by positivity
  have hy : (2 * Real.pi) • ((2 * Real.pi)⁻¹ • x) = x := smul_inv_smul₀ hpos x
  have e : ∀ i : Fin 4 → ℤ, UnitAddTorus.mFourier i (toUnitTorus ((2 * Real.pi)⁻¹ • x)) =
      expChar (-i) (toComplexVec x) := by
    intro i
    have := mFourier_toUnitTorus (-i) ((2 * Real.pi)⁻¹ • x)
    rwa [neg_neg, hy] at this
  rw [hF, hy, hco] at h
  simp only [e, smul_eq_mul] at h
  exact h
theorem fourierCoeff4_zero (g : (Fin 4 → ℂ) → ℂ) :
    fourierCoeff4 g 0 = torusAverage fun κ => g (toComplexVec κ) := by
  have h : ∀ κ : Fin 4 → ℂ, expChar 0 κ = 1 := by
    intro κ
    simp [expChar, bilinDot, toComplexVec, castVec]
  simp [fourierCoeff4, h]
theorem hasSum_divisible_bounds {ς : ℝ} (hς : 0 < ς) {s : ℕ} (hs : 0 < s) :
    HasSum (fun n : Fin 4 → ℤ => if ∀ μ, (s : ℤ) ∣ n μ then
        ∏ μ, Real.exp (-ς * |(n μ : ℝ)|) else 0)
      ((1 + 2 * (Real.exp (ς * s) - 1)⁻¹) ^ 4) := by
  have hsz : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  have hc : 0 < ς * s := by positivity
  have h1 := hasSum_exp_neg_mul_abs hc
  have hA := hasSum_prod_pi (fun m : ℤ => Real.exp (-(ς * s) * |(m : ℝ)|))
    (fun _ => (Real.exp_pos _).le) h1.summable 4
  rw [h1.tsum_eq] at hA
  let ι : (Fin 4 → ℤ) → Fin 4 → ℤ := fun m μ => (s : ℤ) * m μ
  have hι : Function.Injective ι := by
    intro m m' h
    funext μ
    exact mul_left_cancel₀ hsz (congrFun h μ)
  refine (hι.hasSum_iff ?_).1 ?_
  · intro n hn
    refine if_neg fun hd => hn ?_
    choose m hm using hd
    exact ⟨m, funext fun μ => (hm μ).symm⟩
  · convert hA using 1
    funext m
    have hd : ∀ μ, (s : ℤ) ∣ ι m μ := fun μ => ⟨m μ, rfl⟩
    simp only [Function.comp, if_pos hd]
    refine Finset.prod_congr rfl fun μ _ => ?_
    congr 1
    simp only [ι]
    push_cast
    rw [abs_mul, Nat.abs_cast]
    ring
theorem claim_holds : Claim := by
  intro s ς g hs hς hh hp hb
  have hN := stripRegular_of_holomorphic hh hp hb
  refine ⟨?_, fun ϑ hϑ => hN.torusAverage_translate hς.le hϑ⟩
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h1 : HasSum (fun n => fourierCoeff4 g n * (if ∀ μ, (s : ℤ) ∣ n μ then (1 : ℂ) else 0))
      (((s : ℂ) ^ 4)⁻¹ * classSum s g) := by
    rw [hN.classSum_eq_sum_latticePoint hς.le hs]
    have h := (hasSum_sum (s := Finset.univ) fun k _ =>
      hN.hasSum_fourierSeries hς (latticePoint s k : AmbientSpace)).mul_left ((s : ℂ) ^ 4)⁻¹
    have e : (fun n => fourierCoeff4 g n * (if ∀ μ, (s : ℤ) ∣ n μ then (1 : ℂ) else 0)) =
        fun n => ((s : ℂ) ^ 4)⁻¹ * ∑ k, fourierCoeff4 g n *
          expChar (-n) (toComplexVec (latticePoint s k : AmbientSpace)) := by
      funext n
      rw [← Finset.mul_sum, sum_expChar_latticePoint hs]
      split_ifs
      · field_simp
      · simp
    rw [e]
    exact h
  have h2 : HasSum (fun n => if n = 0 then (0 : ℂ) else
        fourierCoeff4 g n * (if ∀ μ, (s : ℤ) ∣ n μ then (1 : ℂ) else 0))
      (((s : ℂ) ^ 4)⁻¹ * classSum s g -
        torusAverage fun κ => g (toComplexVec κ)) := by
    rw [← fourierCoeff4_zero]
    have e : (fun n => if n = 0 then (0 : ℂ) else
          fourierCoeff4 g n * (if ∀ μ, (s : ℤ) ∣ n μ then (1 : ℂ) else 0)) =
        fun n => fourierCoeff4 g n * (if ∀ μ, (s : ℤ) ∣ n μ then (1 : ℂ) else 0) -
          if n = 0 then fourierCoeff4 g 0 else 0 := by
      funext n
      by_cases e : n = 0
      · subst e; simp
      · simp [e]
    rw [e]
    exact h1.sub (hasSum_ite_eq (0 : Fin 4 → ℤ) (fourierCoeff4 g 0))
  have h3 : HasSum (fun n : Fin 4 → ℤ => stripSup ς g * (if n = 0 then (0 : ℝ) else
        if ∀ μ, (s : ℤ) ∣ n μ then ∏ μ, Real.exp (-ς * |(n μ : ℝ)|) else 0))
      (stripSup ς g * ((1 + 2 * (Real.exp (ς * s) - 1)⁻¹) ^ 4 - 1)) := by
    refine HasSum.mul_left _ ?_
    have e : (fun n : Fin 4 → ℤ => if n = 0 then (0 : ℝ) else
          if ∀ μ, (s : ℤ) ∣ n μ then ∏ μ, Real.exp (-ς * |(n μ : ℝ)|) else 0) =
        fun n => (if ∀ μ, (s : ℤ) ∣ n μ then ∏ μ, Real.exp (-ς * |(n μ : ℝ)|) else 0) -
          if n = 0 then (1 : ℝ) else 0 := by
      funext n
      by_cases e : n = 0
      · subst e; simp
      · simp [e]
    rw [e]
    exact (hasSum_divisible_bounds hς hs).sub (hasSum_ite_eq (0 : Fin 4 → ℤ) (1 : ℝ))
  refine h2.norm_le_of_bounded h3 fun n => ?_
  by_cases e : n = 0
  · simp [e]
  · by_cases d : ∀ μ, (s : ℤ) ∣ n μ
    · simpa [e, d] using hN.norm_fourierCoeff4_le hς n
    · simp [e, d]
end YangMills.Construction.PeriodicOperators.RiemannSums
end
