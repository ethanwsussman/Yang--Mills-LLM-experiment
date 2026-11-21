import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlates
import YangMills.Construction.TwoPoints.EntireContinuationInTheRotationAngle
import YangMills.Construction.TwoPoints.FirstConsequencesOfThreeProperties
import YangMills.Construction.TwoPoints.IntegralOfAHolomorphicFamily
import YangMills.Construction.TwoPoints.PropertiesOfThePlaneKernel
import YangMills.Construction.TwoPoints.SpectralMeasuresVanishOutsideTheCone
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open SpectralCalculus
open InfiniteLattice (AmbientSpace)
open PeriodicLattice (coordVec)
namespace EntireAngleContinuationProof
theorem isHolomorphicOnOne_iff_differentiableOn {O : Set ℂ} (hO : IsOpen O) (f : ℂ → ℂ) :
    IsHolomorphicOnOne O f ↔ DifferentiableOn ℂ f O := by
  have he : ∀ z : ℂ, (Equiv.funUnique (Fin 1) ℂ).symm z = fun _ => z := by
    intro z
    funext i
    rw [Subsingleton.elim i default]
    simp
  have hes : ∀ w : Fin 1 → ℂ, (Equiv.funUnique (Fin 1) ℂ) w = w 0 := fun w => rfl
  have hmap : ((Equiv.funUnique (Fin 1) ℂ).symm ∘ f ∘ (Equiv.funUnique (Fin 1) ℂ).symm.symm) =
      fun (w : Fin 1 → ℂ) (_ : Fin 1) => f (w 0) := by
    funext w
    simp only [Function.comp, Equiv.symm_symm, he, hes]
  have hline : ∀ (z ζ : ℂ) (j : Fin 1),
      ((fun _ => z : Fin 1 → ℂ) + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0 = z + ζ := by
    intro z ζ j
    rw [Subsingleton.elim j 0]
    simp [Coordinates.ComplexCoordinates.stdBasisVector]
  unfold IsHolomorphicOnOne Coordinates.ComplexCoordinates.IsHolomorphicVia
    Coordinates.ComplexCoordinates.IsHolomorphicIn
  rw [hmap]
  constructor
  · rintro ⟨-, -, h⟩ z hz
    have h0 := (h (fun _ => z) ⟨z, hz, he z⟩ 0).self_of_nhds
    have h1 := differentiableAt_pi.1 h0 0
    simp only [hline] at h1
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (fun ζ : ℂ => f (z + ζ)) (w - z)) z :=
      DifferentiableAt.comp (f := fun w : ℂ => w - z) (g := fun ζ : ℂ => f (z + ζ)) z
        (by simpa using h1) (differentiableAt_id.sub_const z)
    simpa using h2.differentiableWithinAt
  · intro hd
    have himage : (Equiv.funUnique (Fin 1) ℂ).symm '' O = (fun w : Fin 1 → ℂ => w 0) ⁻¹' O := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [he] using hz
      · intro hw
        exact ⟨w 0, hw, by rw [Equiv.symm_apply_eq]; rfl⟩
    rw [himage]
    refine ⟨hO.preimage (continuous_apply 0), ?_, ?_⟩
    · exact continuousOn_pi.2 fun _ => hd.continuousOn.comp (continuous_apply 0).continuousOn
        fun w hw => hw
    · intro a ha j
      have hz : a 0 ∈ O := ha
      have hcont : Continuous fun ζ : ℂ => a 0 + ζ := by fun_prop
      have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a 0 + ζ ∈ O :=
        hcont.continuousAt.eventually_mem (hO.mem_nhds (by simpa using hz))
      have ha' : a = fun _ => a 0 := by
        funext i
        rw [Subsingleton.elim i 0]
      filter_upwards [hnear] with ζ hζ
      refine differentiableAt_pi.2 fun _ => ?_
      have hval : ∀ ξ : ℂ, (a + ξ • Coordinates.ComplexCoordinates.stdBasisVector j) 0 = a 0 + ξ := by
        intro ξ
        conv_lhs => rw [ha']
        exact hline _ _ _
      simp only [hval]
      exact DifferentiableAt.comp (f := fun ξ : ℂ => a 0 + ξ) (g := f) ζ
        ((hd _ hζ).differentiableAt (hO.mem_nhds hζ)) (by fun_prop)
theorem eqOn_of_eventuallyEq_ofReal {U : Set ℂ} (hU : IsOpen U) (hpc : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) {c : ℝ}
    (hc : (c : ℂ) ∈ U) (h : ∀ᶠ x : ℝ in 𝓝 c, f x = g x) : EqOn f g U := by
  refine (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU) hpc hc ?_
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] c) (𝓝[≠] (c : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto c).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using hx)
  exact ht.frequently (h.filter_mono nhdsWithin_le_nhds).frequently
theorem eq_of_forall_ofReal_eq {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ x : ℝ, f x = g x) : f = g :=
  funext fun z => eqOn_of_eventuallyEq_ofReal isOpen_univ isPreconnected_univ hf.differentiableOn
    hg.differentiableOn (c := 0) (mem_univ _) (Eventually.of_forall h) (mem_univ z)
def verticalStrip : Set ℂ := {z | -(Real.pi / 2) < z.re ∧ z.re < Real.pi / 2}
theorem isOpen_verticalStrip : IsOpen verticalStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
theorem isPreconnected_verticalStrip : IsPreconnected verticalStrip :=
  ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).isPreconnected
theorem cos_re_pos_of_mem_verticalStrip {z : ℂ} (hz : z ∈ verticalStrip) : 0 < Real.cos z.re :=
  Real.cos_pos_of_mem_Ioo ⟨hz.1, hz.2⟩
theorem exists_differentiable_extension_of_periodic {g : ℂ → ℂ} {v : ℝ → ℂ}
    (hg : DifferentiableOn ℂ g verticalStrip)
    (hgv : ∀ x : ℝ, -(Real.pi / 2) < x → x < Real.pi / 2 → g x = v x)
    (hper : Function.Periodic v (Real.pi / 2)) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ x : ℝ, G x = v x) ∧
      ∀ z : ℂ, ∃ k : ℤ, |z.re - k * (Real.pi / 2)| ≤ Real.pi / 4 ∧
        G z = g (z - (k : ℂ) * ((Real.pi : ℂ) / 2)) := by
  have hpi := Real.pi_pos
  have hre : ∀ (z : ℂ) (j : ℤ), (z - (j : ℂ) * ((Real.pi : ℂ) / 2)).re = z.re - j * (Real.pi / 2) := by
    intro z j
    simp
  have hadj : ∀ u : ℂ, 0 < u.re → u.re < Real.pi / 2 → g u = g (u - (Real.pi : ℂ) / 2) := by
    intro u hu₀ hu₁
    have hTo : IsOpen {w : ℂ | 0 < w.re ∧ w.re < Real.pi / 2} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hTc : IsPreconnected {w : ℂ | 0 < w.re ∧ w.re < Real.pi / 2} :=
      ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).isPreconnected
    have h1 : DifferentiableOn ℂ g {w : ℂ | 0 < w.re ∧ w.re < Real.pi / 2} :=
      hg.mono fun w hw => ⟨by linarith [hw.1], hw.2⟩
    have h2 : DifferentiableOn ℂ (fun w => g (w - (Real.pi : ℂ) / 2))
        {w : ℂ | 0 < w.re ∧ w.re < Real.pi / 2} := by
      refine DifferentiableOn.comp (t := verticalStrip) hg (by fun_prop) fun w hw => ?_
      have hw' : (w - (Real.pi : ℂ) / 2).re = w.re - Real.pi / 2 := by simp
      exact ⟨by rw [hw']; linarith [hw.1], by rw [hw']; linarith [hw.2]⟩
    refine eqOn_of_eventuallyEq_ofReal hTo hTc h1 h2 (c := Real.pi / 4) ?_ ?_ ⟨hu₀, hu₁⟩
    · constructor
      · simp only [Complex.ofReal_re]; linarith
      · simp only [Complex.ofReal_re]; linarith
    · filter_upwards [Ioo_mem_nhds (a := 0) (b := Real.pi / 2) (by linarith) (by linarith)] with x hx
      have e : (x : ℂ) - (Real.pi : ℂ) / 2 = ((x - Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [e, hgv x (by linarith [hx.1]) hx.2, hgv _ (by linarith [hx.1]) (by linarith [hx.2]),
        ← hper (x - Real.pi / 2), sub_add_cancel]
  let K : ℂ → ℤ := fun z => round (z.re / (Real.pi / 2))
  have hK : ∀ z, |z.re - K z * (Real.pi / 2)| ≤ Real.pi / 4 := by
    intro z
    have h := abs_sub_round (z.re / (Real.pi / 2))
    have e : z.re - K z * (Real.pi / 2) = (z.re / (Real.pi / 2) - K z) * (Real.pi / 2) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (by linarith : 0 < Real.pi / 2)]
    have h' : |z.re / (Real.pi / 2) - K z| ≤ 1 / 2 := h
    calc |z.re / (Real.pi / 2) - K z| * (Real.pi / 2) ≤ 1 / 2 * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_right h' (by linarith)
      _ = Real.pi / 4 := by ring
  let G : ℂ → ℂ := fun z => g (z - (K z : ℂ) * ((Real.pi : ℂ) / 2))
  have hcons : ∀ (z : ℂ) (j : ℤ), |z.re - j * (Real.pi / 2)| < Real.pi / 2 →
      G z = g (z - (j : ℂ) * ((Real.pi : ℂ) / 2)) := by
    intro z j hj
    have hk := abs_le.1 (hK z)
    have hj' := abs_lt.1 hj
    have hd₁ : ((K z - j : ℤ) : ℝ) * (Real.pi / 2) < 3 / 2 * (Real.pi / 2) := by
      push_cast; nlinarith [hk.1, hj'.2]
    have hd₂ : -(3 / 2) * (Real.pi / 2) < ((K z - j : ℤ) : ℝ) * (Real.pi / 2) := by
      push_cast; nlinarith [hk.2, hj'.1]
    have hd₃ : ((K z - j : ℤ) : ℝ) < 2 := by
      have := lt_of_mul_lt_mul_right hd₁ (by linarith); linarith
    have hd₄ : (-2 : ℝ) < ((K z - j : ℤ) : ℝ) := by
      have := lt_of_mul_lt_mul_right hd₂ (by linarith); linarith
    have hd₅ : K z - j < 2 := by exact_mod_cast hd₃
    have hd₆ : -2 < K z - j := by exact_mod_cast hd₄
    have hcases : K z = j ∨ K z = j + 1 ∨ K z = j - 1 := by omega
    rcases hcases with h | h | h
    · show g _ = _
      rw [h]
    · show g _ = _
      have hkz : ((K z : ℤ) : ℂ) = (j : ℂ) + 1 := by rw [h]; push_cast; ring
      have hkr : ((K z : ℤ) : ℝ) = (j : ℝ) + 1 := by rw [h]; push_cast; ring
      rw [hkr] at hk
      have e : z - (K z : ℂ) * ((Real.pi : ℂ) / 2) =
          z - (j : ℂ) * ((Real.pi : ℂ) / 2) - (Real.pi : ℂ) / 2 := by rw [hkz]; ring
      rw [e]
      refine (hadj _ ?_ ?_).symm
      · rw [hre]; nlinarith [hk.1]
      · rw [hre]; linarith [hj'.2]
    · show g _ = _
      have hkz : ((K z : ℤ) : ℂ) = (j : ℂ) - 1 := by rw [h]; push_cast; ring
      have hkr : ((K z : ℤ) : ℝ) = (j : ℝ) - 1 := by rw [h]; push_cast; ring
      have e : z - (j : ℂ) * ((Real.pi : ℂ) / 2) =
          z - (K z : ℂ) * ((Real.pi : ℂ) / 2) - (Real.pi : ℂ) / 2 := by rw [hkz]; ring
      rw [e]
      rw [hkr] at hk
      refine hadj _ ?_ ?_
      · rw [hre, hkr]; nlinarith [hj'.1]
      · rw [hre, hkr]; nlinarith [hk.2]
  refine ⟨G, ?_, ?_, fun z => ⟨K z, hK z, rfl⟩⟩
  · intro z
    have hz : |z.re - K z * (Real.pi / 2)| < Real.pi / 2 := lt_of_le_of_lt (hK z) (by linarith)
    have hopen : IsOpen {u : ℂ | |u.re - K z * (Real.pi / 2)| < Real.pi / 2} :=
      isOpen_lt (by fun_prop) continuous_const
    have hev : G =ᶠ[𝓝 z] fun u => g (u - (K z : ℂ) * ((Real.pi : ℂ) / 2)) := by
      filter_upwards [hopen.mem_nhds hz] with u hu
      exact hcons u (K z) hu
    have hmem : z - (K z : ℂ) * ((Real.pi : ℂ) / 2) ∈ verticalStrip := by
      have := abs_lt.1 hz
      exact ⟨by rw [hre]; exact this.1, by rw [hre]; exact this.2⟩
    have hd : DifferentiableAt ℂ (fun u => g (u - (K z : ℂ) * ((Real.pi : ℂ) / 2))) z :=
      DifferentiableAt.comp (g := g) (f := fun u : ℂ => u - (K z : ℂ) * ((Real.pi : ℂ) / 2)) z
        ((hg _ hmem).differentiableAt (isOpen_verticalStrip.mem_nhds hmem)) (by fun_prop)
    exact hd.congr_of_eventuallyEq hev
  · intro x
    have hk := abs_le.1 (hK (x : ℂ))
    simp only [Complex.ofReal_re] at hk
    have e : (x : ℂ) - (K x : ℂ) * ((Real.pi : ℂ) / 2) = ((x - K x * (Real.pi / 2) : ℝ) : ℂ) := by
      push_cast; ring
    show g _ = _
    rw [e, hgv _ (by linarith [hk.1]) (by linarith [hk.2])]
    exact hper.sub_int_mul_eq _
theorem cos_re_im (z : ℂ) : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im ∧
    (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
  have h : Complex.cos z = Complex.cos (z.re : ℂ) * Complex.cosh (z.im : ℂ) -
      Complex.sin (z.re : ℂ) * Complex.sinh (z.im : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im z]
    exact Complex.cos_add_mul_I _ _
  rw [h]
  constructor <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cosh_ofReal_re,
    Complex.sinh_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im, Complex.cosh_ofReal_im,
    Complex.sinh_ofReal_im]
theorem sin_re_im (z : ℂ) : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im ∧
    (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
  have h : Complex.sin z = Complex.sin (z.re : ℂ) * Complex.cosh (z.im : ℂ) +
      Complex.cos (z.re : ℂ) * Complex.sinh (z.im : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im z]
    exact Complex.sin_add_mul_I _ _
  rw [h]
  constructor <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cosh_ofReal_re,
    Complex.sinh_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im, Complex.cosh_ofReal_im,
    Complex.sinh_ofReal_im]
def boostKernel (r : ℝ) (z : ℂ) (p : SpectralPlane) : ℂ :=
  Complex.exp (-(r : ℂ) * ((p.1 : ℝ) : ℂ) * Complex.cos z +
    Complex.I * (r : ℂ) * (p.2 : ℂ) * Complex.sin z)
def boostIntegral (r : ℝ) (ρ : Measure SpectralPlane) (z : ℂ) : ℂ :=
  ∫ p, boostKernel r z p ∂ρ
theorem boostExponent_re (r E q : ℝ) (z : ℂ) :
    (-(r : ℂ) * (E : ℂ) * Complex.cos z + Complex.I * (r : ℂ) * (q : ℂ) * Complex.sin z).re =
      -(r * Real.cos z.re * (E * Real.cosh z.im + q * Real.sinh z.im)) := by
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, (cos_re_im z).1,
    (cos_re_im z).2, (sin_re_im z).1, (sin_re_im z).2]
  ring
theorem mul_exp_neg_abs_le_cosh_sinh {E q : ℝ} (b : ℝ) (h : |q| ≤ E) :
    E * Real.exp (-|b|) ≤ E * Real.cosh b + q * Real.sinh b := by
  have h1 : Real.cosh b - Real.sinh |b| = Real.exp (-|b|) := by
    rw [← Real.cosh_abs b]
    exact Real.cosh_sub_sinh _
  have h2 : -(E * Real.sinh |b|) ≤ q * Real.sinh b := by
    have h3 : |q * Real.sinh b| ≤ E * Real.sinh |b| := by
      rw [abs_mul, Real.abs_sinh]
      exact mul_le_mul_of_nonneg_right h (Real.sinh_nonneg_iff.2 (abs_nonneg b))
    exact (neg_le_neg h3).trans (neg_abs_le _)
  rw [← h1]
  linarith [mul_sub E (Real.cosh b) (Real.sinh |b|)]
theorem norm_boostKernel_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : 0 < Real.cos z.re)
    {p : SpectralPlane} (hp : |p.2| ≤ (p.1 : ℝ)) :
    ‖boostKernel r z p‖ ≤ energyDecay (r * Real.cos z.re * Real.exp (-|z.im|)) p := by
  rw [boostKernel, Complex.norm_exp, boostExponent_re, energyDecay]
  refine Real.exp_le_exp.2 ?_
  have key := mul_exp_neg_abs_le_cosh_sinh z.im hp
  have hc : 0 ≤ r * Real.cos z.re := (mul_pos hr hz).le
  have := mul_le_mul_of_nonneg_left key hc
  nlinarith
theorem energyDecay_antitone {a b : ℝ} (h : a ≤ b) (p : SpectralPlane) :
    energyDecay b p ≤ energyDecay a p := by
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_right h (NNReal.coe_nonneg p.1)
  linarith
theorem continuous_energyDecay (c : ℝ) : Continuous (energyDecay c) :=
  Real.continuous_exp.comp (continuous_const.mul (NNReal.continuous_coe.comp continuous_fst))
theorem continuous_boostKernel (r : ℝ) (z : ℂ) : Continuous (boostKernel r z) := by
  have h1 : Continuous fun p : SpectralPlane => ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp continuous_fst)
  have h2 : Continuous fun p : SpectralPlane => (p.2 : ℂ) :=
    Complex.continuous_ofReal.comp continuous_snd
  exact Complex.continuous_exp.comp (((continuous_const.mul h1).mul continuous_const).add
    ((continuous_const.mul h2).mul continuous_const))
theorem differentiable_boostKernel (r : ℝ) (p : SpectralPlane) :
    Differentiable ℂ fun z => boostKernel r z p := by
  unfold boostKernel
  fun_prop
structure IsLightConeMeasure (ρ : Measure SpectralPlane) : Prop where
  integrable_energyDecay : ∀ c : ℝ, 0 < c → Integrable (energyDecay c) ρ
  ae_abs_le : ∀ᵐ p ∂ρ, |p.2| ≤ (p.1 : ℝ)
theorem integrable_boostKernel {r : ℝ} (hr : 0 < r) {ρ : Measure SpectralPlane}
    (hρ : IsLightConeMeasure ρ) {z : ℂ} (hz : 0 < Real.cos z.re) :
    Integrable (boostKernel r z) ρ :=
  (hρ.integrable_energyDecay _ (mul_pos (mul_pos hr hz) (Real.exp_pos _))).mono'
    (continuous_boostKernel r z).aestronglyMeasurable
    (hρ.ae_abs_le.mono fun _ hp => norm_boostKernel_le hr hz hp)
theorem norm_boostIntegral_le {r : ℝ} (hr : 0 < r) {ρ : Measure SpectralPlane}
    (hρ : IsLightConeMeasure ρ) {z : ℂ} (hz : 0 < Real.cos z.re) :
    ‖boostIntegral r ρ z‖ ≤ ∫ p, energyDecay (r * Real.cos z.re * Real.exp (-|z.im|)) p ∂ρ :=
  norm_integral_le_of_norm_le
    (hρ.integrable_energyDecay _ (mul_pos (mul_pos hr hz) (Real.exp_pos _)))
    (hρ.ae_abs_le.mono fun _ hp => norm_boostKernel_le hr hz hp)
theorem differentiableOn_boostIntegral (hHolo : HolomorphicParametricIntegral.Statement) {r : ℝ}
    (hr : 0 < r) {ρ : Measure SpectralPlane} (hρ : IsLightConeMeasure ρ) :
    DifferentiableOn ℂ (boostIntegral r ρ) verticalStrip := by
  let X : Set SpectralPlane := {p | |p.2| ≤ (p.1 : ℝ)}
  have hX : MeasurableSet X :=
    (isClosed_le (continuous_abs.comp continuous_snd)
      (NNReal.continuous_coe.comp continuous_fst)).measurableSet
  have hres : ρ.restrict X = ρ := Measure.restrict_eq_self_of_ae_mem hρ.ae_abs_le
  obtain ⟨-, hol⟩ := hHolo X hX (Measure.comap Subtype.val ρ) verticalStrip isOpen_verticalStrip
    (fun z x => boostKernel r z x)
    (fun z _ => ((continuous_boostKernel r z).comp continuous_subtype_val).measurable)
    (fun x => (isHolomorphicOnOne_iff_differentiableOn isOpen_verticalStrip _).2
      (differentiable_boostKernel r x).differentiableOn)
    (by
      intro Z hZ hZO
      rcases Z.eq_empty_or_nonempty with rfl | hne
      · exact ⟨fun _ => 0, fun _ => le_rfl, integrable_zero _ _ _, by simp⟩
      have hcont : ContinuousOn (fun z : ℂ => r * Real.cos z.re * Real.exp (-|z.im|)) Z :=
        ((continuous_const.mul (Real.continuous_cos.comp Complex.continuous_re)).mul
          (Real.continuous_exp.comp (continuous_abs.comp Complex.continuous_im).neg)).continuousOn
      obtain ⟨z₀, hz₀, hmin⟩ := hZ.exists_isMinOn hne hcont
      have hc : 0 < r * Real.cos z₀.re * Real.exp (-|z₀.im|) :=
        mul_pos (mul_pos hr (cos_re_pos_of_mem_verticalStrip (hZO hz₀))) (Real.exp_pos _)
      refine ⟨fun x => energyDecay (r * Real.cos z₀.re * Real.exp (-|z₀.im|)) x,
        fun x => (Real.exp_pos _).le, ?_, ?_⟩
      · exact (integrableOn_iff_comap_subtypeVal hX).1 (hρ.integrable_energyDecay _ hc).integrableOn
      · intro z hz x
        exact (norm_boostKernel_le hr (cos_re_pos_of_mem_verticalStrip (hZO hz)) x.2).trans
          (energyDecay_antitone (hmin hz) x))
  have heq : (fun z => ∫ x : X, boostKernel r z x ∂(Measure.comap Subtype.val ρ)) =
      boostIntegral r ρ := funext fun z => by
    rw [integral_subtype_comap hX (boostKernel r z), hres]
    rfl
  rw [heq] at hol
  exact (isHolomorphicOnOne_iff_differentiableOn isOpen_verticalStrip _).1 hol
theorem boostKernel_I_mul (r b : ℝ) (p : SpectralPlane) :
    boostKernel r (Complex.I * (b : ℂ)) p = ((boostedExpWeight r b p : ℝ) : ℂ) := by
  rw [boostKernel, boostedExpWeight, mul_comm Complex.I (b : ℂ), Complex.cos_mul_I,
    Complex.sin_mul_I, Complex.ofReal_exp]
  congr 1
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (r : ℂ) * (p.2 : ℂ) * Complex.sinh (b : ℂ) * hI
theorem isBoostedLaplaceOnLine_of_eq {r : ℝ} (hr : 0 < r) {ρ : Measure SpectralPlane}
    (hρ : IsLightConeMeasure ρ) {F : ℂ → ℂ} {c : ℝ}
    (hl : ∀ z ∈ verticalStrip, F ((c : ℂ) + z) = boostIntegral r ρ z) :
    IsBoostedLaplaceOnLine F c r ρ := by
  have hpi := Real.pi_pos
  have hmem : ∀ b : ℝ, Complex.I * (b : ℂ) ∈ verticalStrip := fun b => by
    constructor <;> simp <;> linarith
  have hcos : ∀ b : ℝ, 0 < Real.cos (Complex.I * (b : ℂ)).re := fun b =>
    cos_re_pos_of_mem_verticalStrip (hmem b)
  have hnn : ∀ (b : ℝ) (p : SpectralPlane), 0 ≤ boostedExpWeight r b p :=
    fun b p => (Real.exp_pos _).le
  refine ⟨fun b => ?_, fun b => ?_, fun b => integral_nonneg (hnn b)⟩
  · refine (integrable_boostKernel hr hρ (hcos b)).norm.congr (ae_of_all _ fun p => ?_)
    simp only [boostKernel_I_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn b p)]
  · rw [hl _ (hmem b), boostIntegral, ← integral_complex_ofReal]
    exact integral_congr_ae (ae_of_all _ fun p => boostKernel_I_mul r b p)
def radialValue (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (φ : (Fin 2 → ℝ) → ℂ)
    (r x : ℝ) : ℂ :=
  transverseAveragedKernel S φ (planeCoords (r • planeUnit x))
theorem planeCoords_smul_planeUnit (r x : ℝ) :
    planeCoords (r • planeUnit x) = ![r * Real.cos x, r * Real.sin x] := by
  funext i
  fin_cases i <;> simp [planeCoords, planeUnit, PeriodicLattice.coordVec]
theorem planeCoords_smul_planeUnit_ne_zero {r : ℝ} (hr : 0 < r) (x : ℝ) :
    planeCoords (r • planeUnit x) ≠ 0 := by
  intro h
  rw [planeCoords_smul_planeUnit] at h
  have h0 : r * Real.cos x = 0 := congrFun h 0
  have h1 : r * Real.sin x = 0 := congrFun h 1
  have hc := (mul_eq_zero.1 h0).resolve_left hr.ne'
  have hs := (mul_eq_zero.1 h1).resolve_left hr.ne'
  have := Real.sin_sq_add_cos_sq x
  rw [hc, hs] at this
  norm_num at this
theorem embedPlane_planeCoords_smul_planeUnit (r x : ℝ) :
    embedPlane (planeCoords (r • planeUnit x)) = r • planeUnit x := by
  rw [planeCoords_smul_planeUnit]
  simp [embedPlane, planeUnit, smul_add, smul_smul]
theorem radialValue_periodic (hDir : PlaneUnitsAndFrames)
    (hq : ∃ w ∈ dihedralInPlane, ⇑w = ⇑rightAngleRotation)
    {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {φ : (Fin 2 → ℝ) → ℂ}
    (hK : IsRegularAveragedKernel S φ) {r : ℝ} (hr : 0 < r) :
    Function.Periodic (radialValue S φ r) (Real.pi / 2) := by
  intro x
  obtain ⟨w, hw, hwq⟩ := hq
  have h := hK.invariant w hw _ (planeCoords_smul_planeUnit_ne_zero hr x)
  rw [embedPlane_planeCoords_smul_planeUnit] at h
  have e : w (r • planeUnit x) = r • planeUnit (x + Real.pi / 2) := by
    rw [congrFun hwq]
    show rotateInPlane (Real.pi / 2) (r • planeUnit x) = _
    rw [map_smul, (hDir.1 x (Real.pi / 2) _ rfl).2.2.2]
  rw [e] at h
  exact h
theorem radialValue_neg (hq : ∃ w ∈ dihedralInPlane, ⇑w = reflectAcross (coordVec 0))
    {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {φ : (Fin 2 → ℝ) → ℂ}
    (hK : IsRegularAveragedKernel S φ) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    radialValue S φ r (-x) = radialValue S φ r x := by
  obtain ⟨w, hw, hwq⟩ := hq
  have h := hK.invariant w hw _ (planeCoords_smul_planeUnit_ne_zero hr x)
  rw [embedPlane_planeCoords_smul_planeUnit] at h
  have e : w (r • planeUnit x) = r • planeUnit (-x) := by
    rw [congrFun hwq]
    funext i
    fin_cases i <;>
      simp [reflectAcross, planeUnit, euclidDot, Fin.sum_univ_four,
        PeriodicLattice.coordVec]
    ring
  rw [e] at h
  exact h
theorem boostIntegral_ofReal (hDir : PlaneUnitsAndFrames)
    {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {φ : (Fin 2 → ℝ) → ℂ} {m : AmbientSpace}
    {c : ℝ} (hmc : m = planeUnit c) {ρ : Measure SpectralPlane}
    (hρ : IsAveragedKernelSpectralMeasure S φ m ρ) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (h₁ : -(Real.pi / 2) < x) (h₂ : x < Real.pi / 2) :
    boostIntegral r ρ x = radialValue S φ r (c + x) := by
  have ht : 0 < r * Real.cos x := mul_pos hr (Real.cos_pos_of_mem_Ioo ⟨h₁, h₂⟩)
  obtain ⟨t, htv⟩ : ∃ t : NNReal, (t : ℝ) = r * Real.cos x := ⟨⟨_, ht.le⟩, rfl⟩
  have h := hρ.kernel_eq_integral t (NNReal.coe_pos.1 (htv ▸ ht)) (r * Real.sin x)
  have hv : (r * Real.cos x) • m + (r * Real.sin x) • planePerp m = r • planeUnit (c + x) := by
    rw [← (hDir.1 c x m hmc).2.2.1, smul_add, smul_smul, smul_smul]
  rw [htv, hv] at h
  rw [radialValue, h, boostIntegral, integralWrt]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [boostKernel, spectralCharacter, htv]
  congr 1
  push_cast
  ring
theorem two_rpow_neg_half_le_cos {θ : ℝ} (h : |θ| ≤ Real.pi / 4) :
    (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ Real.cos θ := by
  have e : (2 : ℝ) ^ (-(1 / 2) : ℝ) = Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith
  rw [e, ← Real.cos_abs θ]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [Real.pi_pos]) h
theorem entireAngleContinuation (hElem : ReflectionsPlaneFacts.Statement)
    (hFirst : AdmissibleFormConsequences.Statement)
    (hMeas : SpectralMeasuresAtAllNormals.Statement)
    (hKer : AveragedKernelProperties.Statement)
    (hCone : SpectralSupportInCone.Statement)
    (hHolo : HolomorphicParametricIntegral.Statement) :
    EntireAngleContinuation.Statement := by
  intro St S hS hP φ hφ r hr
  obtain ⟨-, -, -, hEight, hDir, hSym, -, -⟩ := hElem
  obtain ⟨-, -, -, hquarter, -⟩ := hSym
  have hpi := Real.pi_pos
  have hK := (hKer St S hS hP φ hφ).1
  have hM := hMeas St S φ hS hP hφ
  have he₁ : coordVec 0 ∈ planeReflectionNormals := by
    rw [hEight.2.1]
    simp
  have hper := radialValue_periodic hDir hquarter hK hr
  have heven := radialValue_neg ((hFirst.1 _ he₁.1).2 he₁) hK hr
  have hcm : ∀ ρ : planeReflectionNormals → Measure SpectralPlane, IsSpectralFamily S φ ρ →
      ∀ m, IsLightConeMeasure (ρ m) := by
    intro ρ hρ m
    refine ⟨fun c hc => ?_, ?_⟩
    · have h := (hρ.decay m).isSpectral.lintegral_decay_lt_top ⟨c, hc.le⟩ (NNReal.coe_pos.1 hc)
      refine ⟨(continuous_energyDecay c).aestronglyMeasurable, ?_⟩
      have hnn : 0 ≤ᵐ[ρ m] energyDecay c := ae_of_all _ fun p => (Real.exp_pos _).le
      rw [hasFiniteIntegral_iff_ofReal hnn]
      exact h
    · have h := hCone St S φ ρ hS hP hφ hρ m
      rw [ae_iff]
      simpa only [not_le] using h
  have hfam₀ : IsSpectralFamily S φ fun m => averagedKernelSpectralMeasure S φ m :=
    ⟨fun m => (hM.1 m m.2).represents, fun m => (hM.1 m m.2).plateNorm⟩
  have hc₀ : IsLightConeMeasure (averagedKernelSpectralMeasure S φ (coordVec 3)) :=
    hcm _ hfam₀ ⟨coordVec 3, coordVec_three_mem_planeReflectionNormals⟩
  have hdir₀ : coordVec 3 = planeUnit 0 := by
    simp [planeUnit]
  obtain ⟨G, hGd, hGv, hGk⟩ := exists_differentiable_extension_of_periodic
    (differentiableOn_boostIntegral hHolo hr hc₀) (v := radialValue S φ r)
    (fun x h₁ h₂ => by
      rw [boostIntegral_ofReal hDir hdir₀
        (hM.1 _ coordVec_three_mem_planeReflectionNormals).represents.isSpectral hr
        h₁ h₂, zero_add]) hper
  have hF : IsAngleFunction S φ r G :=
    ⟨(isHolomorphicOnOne_iff_differentiableOn isOpen_univ G).2 hGd.differentiableOn, hGv⟩
  have hspec : IsAngleFunction S φ r (angleFunction S φ r) :=
    Classical.epsilon_spec ⟨G, hF⟩
  generalize angleFunction S φ r = F at hspec ⊢
  have hFd : Differentiable ℂ F :=
    differentiableOn_univ.1
      ((isHolomorphicOnOne_iff_differentiableOn isOpen_univ F).1 hspec.holomorphic)
  have hFv : ∀ x : ℝ, F x = radialValue S φ r x := hspec.ofReal_eq
  have hFG : F = G := eq_of_forall_ofReal_eq hFd hGd fun x => by rw [hFv, hGv]
  have hline : ∀ (ρ : Measure SpectralPlane) (m : AmbientSpace) (c : ℝ), m = planeUnit c →
      IsAveragedKernelSpectralMeasure S φ m ρ → IsLightConeMeasure ρ →
      ∀ z ∈ verticalStrip, F ((c : ℂ) + z) = boostIntegral r ρ z := by
    intro ρ m c hmc hsp hco
    have hd₁ : DifferentiableOn ℂ (fun z => F ((c : ℂ) + z)) verticalStrip :=
      (hFd.comp (by fun_prop)).differentiableOn
    refine eqOn_of_eventuallyEq_ofReal isOpen_verticalStrip isPreconnected_verticalStrip hd₁
      (differentiableOn_boostIntegral hHolo hr hco) (c := 0) ?_ ?_
    · constructor <;> simp <;> linarith
    · filter_upwards [Ioo_mem_nhds (a := -(Real.pi / 2)) (b := Real.pi / 2) (by linarith)
        (by linarith)] with x hx
      show F ((c : ℂ) + (x : ℂ)) = _
      rw [boostIntegral_ofReal hDir hmc hsp hr hx.1 hx.2, ← Complex.ofReal_add, hFv]
  refine ⟨⟨hspec, fun ϕ => ?_, fun ϕ => ?_, fun ϕ => ?_, fun ϕ₁ ϕ₂ => ?_⟩, fun ρ hρ => ⟨?_, ?_⟩⟩
  · have h : (fun z => F (-z)) = F :=
      eq_of_forall_ofReal_eq (hFd.comp differentiable_neg) hFd fun x => by
        show F (-(x : ℂ)) = F x
        rw [← Complex.ofReal_neg, hFv, hFv, heven]
    exact congrFun h ϕ
  · have h : (fun z => F (z + (Real.pi : ℂ) / 2)) = F :=
      eq_of_forall_ofReal_eq (hFd.comp (by fun_prop)) hFd fun x => by
        have e : (x : ℂ) + (Real.pi : ℂ) / 2 = ((x + Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
        show F ((x : ℂ) + (Real.pi : ℂ) / 2) = F x
        rw [e, hFv, hFv, hper x]
    exact congrFun h ϕ
  · rw [hFv]
    exact hK.im_eq_zero _ (planeCoords_smul_planeUnit_ne_zero hr ϕ)
  · rw [hFG]
    obtain ⟨k, hk, hGz⟩ := hGk ((ϕ₁ : ℂ) + Complex.I * (ϕ₂ : ℂ))
    rw [hGz]
    have hre : ((ϕ₁ : ℂ) + Complex.I * (ϕ₂ : ℂ)).re = ϕ₁ := by simp
    have hwre : ((ϕ₁ : ℂ) + Complex.I * (ϕ₂ : ℂ) - (k : ℂ) * ((Real.pi : ℂ) / 2)).re =
        ϕ₁ - k * (Real.pi / 2) := by simp
    have hwim : ((ϕ₁ : ℂ) + Complex.I * (ϕ₂ : ℂ) - (k : ℂ) * ((Real.pi : ℂ) / 2)).im = ϕ₂ := by
      simp
    rw [hre] at hk
    have hcos := two_rpow_neg_half_le_cos hk
    have hsq : 0 < (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hcpos : 0 < Real.cos
        ((ϕ₁ : ℂ) + Complex.I * (ϕ₂ : ℂ) - (k : ℂ) * ((Real.pi : ℂ) / 2)).re := by
      rw [hwre]
      exact hsq.trans_le hcos
    have hb := norm_boostIntegral_le hr hc₀ hcpos
    rw [hwim, hwre] at hb
    refine hb.trans ?_
    have he := Real.exp_pos (-|ϕ₂|)
    refine (hM.1 _ coordVec_three_mem_planeReflectionNormals).transform_antitoneOn ?_ ?_ ?_
    · exact mul_pos (mul_pos hsq hr) he
    · exact mul_pos (mul_pos hr (hsq.trans_le hcos)) he
    · have := mul_le_mul_of_nonneg_left hcos hr.le
      have h2 := mul_le_mul_of_nonneg_right this he.le
      linarith [h2, mul_comm r ((2 : ℝ) ^ (-(1 / 2) : ℝ))]
  · exact isBoostedLaplaceOnLine_of_eq hr (hcm ρ hρ _)
      (hline _ _ 0 hdir₀ (hρ.decay ⟨_, coordVec_three_mem_planeReflectionNormals⟩).isSpectral
        (hcm ρ hρ _))
  · exact isBoostedLaplaceOnLine_of_eq hr (hcm ρ hρ _)
      (hline _ _ (Real.pi / 4) hEight.2.2.2.1
        (hρ.decay ⟨_, diagNormalPlus_mem_planeReflectionNormals⟩).isSpectral (hcm ρ hρ _))
end EntireAngleContinuationProof
end YangMills.Construction.TwoPoints
end
