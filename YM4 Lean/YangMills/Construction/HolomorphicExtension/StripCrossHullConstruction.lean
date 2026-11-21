import YangMills.Construction.ComplexAnalysis.HalfPiStripIdentityTheorem
import YangMills.Construction.ComplexAnalysis.JoukowskiRadiusProperties
import YangMills.Construction.ComplexAnalysis.SeparateToJointHolomorphy
import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMomentsProof
import YangMills.Construction.HolomorphicExtension.HullConstantsBounds
import YangMills.Construction.HolomorphicExtension.TubeExtensionFromStripCross
import YangMills.Construction.Matrices.UnimodularArgumentHolomorphyProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.HolomorphicExtension.StripCrossHull
open YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates
open YangMills.Construction.Strips YangMills.Construction.Ellipses Filter Set
open scoped Topology ENNReal
noncomputable section
theorem isHolomorphicIn_of_differentiableOn {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hO : IsOpen O)
    (hf : DifferentiableOn ℂ f O) : IsHolomorphicIn O f := by apply _root_.YangMills.SharedProofs.p1029 <;> assumption
theorem differentiableOn_of_isHolomorphicIn
    (hMaps : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {N N' : ℕ} {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'}
    (hf : IsHolomorphicIn O f) : DifferentiableOn ℂ f O := by apply _root_.YangMills.SharedProofs.p33060 <;> assumption
theorem isHolomorphicVia_of_differentiableOn {O : Set ℂ} {h : ℂ → ℂ} (hO : IsOpen O)
    (hh : DifferentiableOn ℂ h O) :
    IsHolomorphicVia (Equiv.funUnique (Fin 1) ℂ).symm (Equiv.funUnique (Fin 1) ℂ).symm O h := by apply _root_.YangMills.Construction.Cumulants.MomentCumulantFormulas.isHolomorphicVia_of_differentiableOn <;> assumption
section SliceExtensions
variable {m : ℕ} [NeZero m]
omit [NeZero m] in
theorem stripExtensionAlong_spec {g : (Fin m → ℝ) → ℂ} (hg : IsSepHolomorphicOnStrips g)
    (j : Fin m) (x : Fin m → ℝ) : IsStripExtensionAlong g j x (stripExtensionAlong g j x) :=
  Classical.epsilon_spec (hg.2 j x)
omit [NeZero m] in
theorem stripExtensionAlong_eqOn (hStrip : EqOnHalfPiStripOfEqOnReal)
    {g : (Fin m → ℝ) → ℂ} {j : Fin m} {x x' : Fin m → ℝ} (hx : ∀ i, i ≠ j → x i = x' i)
    {F F' : ℂ → ℂ} (hF : IsStripExtensionAlong g j x F) (hF' : IsStripExtensionAlong g j x' F') :
    EqOn F F' halfPiStrip := by
  refine hStrip F F' hF.1 hF'.1 fun t => ?_
  rw [hF.2, hF'.2]
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [Function.update_of_ne hi, hx i hi]
end SliceExtensions
def complexPoint {m : ℕ} (x v : Fin m → ℝ) : ComplexCoordinates m :=
  fun i => (x i : ℂ) + (v i : ℂ) * Complex.I
def realEmbed {m : ℕ} (x : Fin m → ℝ) : ComplexCoordinates m := fun i => (x i : ℂ)
def affineLine {m : ℕ} (x v : Fin m → ℝ) (ζ : ℂ) : ComplexCoordinates m :=
  fun i => (x i : ℂ) + ζ * (v i : ℂ)
def IsImaginaryStarShaped {m : ℕ} (D : Set (ComplexCoordinates m)) : Prop :=
  ∀ (x v : Fin m → ℝ) (t : ℝ), complexPoint x v ∈ D → 0 ≤ t → t ≤ 1 →
    complexPoint x (fun i => t * v i) ∈ D
def rescaleChart {m : ℕ} (x0 : Fin m → ℝ) (l : ℝ) (z : ComplexCoordinates m) :
    ComplexCoordinates m :=
  fun i => (z i - (x0 i : ℂ)) / (l : ℂ)
def flatPolyEllipse {m : ℕ} (x0 : Fin m → ℝ) (l ς : ℝ) : Set (ComplexCoordinates m) :=
  {z | ∏ i, joukowskiRadius (rescaleChart x0 l z i) < ς ∧ ∀ j, |(z j).re - x0 j| < l}
theorem isOpen_flatPolyEllipse (hRadius : YangMills.Construction.JoukowskiRadius.JoukowskiRadiusProperties)
    {m : ℕ} (x0 : Fin m → ℝ) (l ς : ℝ) : IsOpen (flatPolyEllipse x0 l ς) := by
  have hc : Continuous joukowskiRadius := hRadius.2.1
  have h1 : IsOpen {z : ComplexCoordinates m | ∏ i, joukowskiRadius (rescaleChart x0 l z i) < ς} := by
    refine isOpen_lt (continuous_finsetProd _ fun i _ => hc.comp ?_) continuous_const
    unfold rescaleChart
    fun_prop
  have h2 : IsOpen {z : ComplexCoordinates m | ∀ j, |(z j).re - x0 j| < l} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  exact h1.inter h2
theorem rescaleChart_complexPoint {m : ℕ} (x0 x v : Fin m → ℝ) (l : ℝ) (i : Fin m) :
    rescaleChart x0 l (complexPoint x v) i
      = (((x i - x0 i) / l : ℝ) : ℂ) + Complex.I * ((v i / l : ℝ) : ℂ) := by
  simp only [rescaleChart, complexPoint]
  push_cast
  ring
theorem complexPoint_re {m : ℕ} (x v : Fin m → ℝ) (i : Fin m) : (complexPoint x v i).re = x i := by
  simp [complexPoint]
theorem complexPoint_im {m : ℕ} (x v : Fin m → ℝ) (i : Fin m) : (complexPoint x v i).im = v i := by
  simp [complexPoint]
theorem isImaginaryStarShaped_flatPolyEllipse
    (hRadius : YangMills.Construction.JoukowskiRadius.JoukowskiRadiusProperties) {m : ℕ}
    (x0 : Fin m → ℝ) {l : ℝ} (hl : 0 < l) (ς : ℝ) :
    IsImaginaryStarShaped (flatPolyEllipse x0 l ς) := by
  obtain ⟨a1, -, -, -, -, -, -, -, -, -, e1, -⟩ := hRadius
  intro x v t hz ht0 ht1
  refine ⟨lt_of_le_of_lt ?_ hz.1, fun j => ?_⟩
  · refine Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_
    · exact zero_le_one.trans (a1 _)
    · rw [rescaleChart_complexPoint, rescaleChart_complexPoint]
      refine e1 _ _ _ ?_
      rw [abs_div, abs_div, abs_mul, abs_of_pos hl, abs_of_nonneg ht0]
      gcongr
      exact mul_le_of_le_one_left (abs_nonneg _) ht1
  · have := hz.2 j
    rwa [complexPoint_re] at this ⊢
theorem eq_of_eqOn_real_of_starShaped {m : ℕ} {D₁ D₂ : Set (ComplexCoordinates m)} (hD₁ : IsOpen D₁)
    (hD₂ : IsOpen D₂) (hs₁ : IsImaginaryStarShaped D₁) (hs₂ : IsImaginaryStarShaped D₂)
    {G₁ G₂ : ComplexCoordinates m → ℂ} (hG₁ : DifferentiableOn ℂ G₁ D₁)
    (hG₂ : DifferentiableOn ℂ G₂ D₂)
    (hreal : ∀ x : Fin m → ℝ, realEmbed x ∈ D₁ ∩ D₂ → G₁ (realEmbed x) = G₂ (realEmbed x))
    {x v : Fin m → ℝ} (h₁ : complexPoint x v ∈ D₁) (h₂ : complexPoint x v ∈ D₂) :
    G₁ (complexPoint x v) = G₂ (complexPoint x v) := by
  have hlineC : Continuous (affineLine x v) := by
    unfold affineLine
    fun_prop
  have hlineD : Differentiable ℂ (affineLine x v) := by
    unfold affineLine
    fun_prop
  set O : Set ℂ := affineLine x v ⁻¹' (D₁ ∩ D₂) with hOdef
  have hO : IsOpen O := (hD₁.inter hD₂).preimage hlineC
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Complex.I * (t : ℂ) ∈ O := by
    intro t ht0 ht1
    have hpt : affineLine x v (Complex.I * (t : ℂ)) = complexPoint x (fun i => t * v i) := by
      funext i
      simp only [affineLine, complexPoint]
      push_cast
      ring
    show affineLine x v _ ∈ D₁ ∩ D₂
    rw [hpt]
    exact ⟨hs₁ x v t h₁ ht0 ht1, hs₂ x v t h₂ ht0 ht1⟩
  have h0O : (0 : ℂ) ∈ O := by simpa using hseg 0 le_rfl zero_le_one
  set O₀ : Set ℂ := connectedComponentIn O 0 with hO₀def
  have hO₀ : IsOpen O₀ := hO.connectedComponentIn
  have hpre : IsPreconnected O₀ := isPreconnected_connectedComponentIn
  have h0 : (0 : ℂ) ∈ O₀ := mem_connectedComponentIn h0O
  have hsub : O₀ ⊆ O := connectedComponentIn_subset O 0
  have hS : IsPreconnected ((fun t : ℝ => Complex.I * (t : ℂ)) '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image _ (by fun_prop)
  have hS0 : (0 : ℂ) ∈ (fun t : ℝ => Complex.I * (t : ℂ)) '' Icc (0 : ℝ) 1 :=
    ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  have hSO : (fun t : ℝ => Complex.I * (t : ℂ)) '' Icc (0 : ℝ) 1 ⊆ O := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact hseg t ht0 ht1
  have hSO₀ := hS.subset_connectedComponentIn hS0 hSO
  have hI : Complex.I ∈ O₀ := hSO₀ ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have hu₁ : DifferentiableOn ℂ (fun ζ => G₁ (affineLine x v ζ)) O₀ :=
    hG₁.comp hlineD.differentiableOn fun ζ hζ => (hsub hζ).1
  have hu₂ : DifferentiableOn ℂ (fun ζ => G₂ (affineLine x v ζ)) O₀ :=
    hG₂.comp hlineD.differentiableOn fun ζ hζ => (hsub hζ).2
  have hfreq : ∃ᶠ ζ in 𝓝[≠] (0 : ℂ), G₁ (affineLine x v ζ) = G₂ (affineLine x v ζ) := by
    have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), (t : ℂ) ∈ O :=
      Complex.continuous_ofReal.continuousAt.eventually (by simpa using hO.mem_nhds h0O)
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
        G₁ (affineLine x v (t : ℂ)) = G₂ (affineLine x v (t : ℂ)) := by
      filter_upwards [nhdsWithin_le_nhds hnear] with t ht
      have hpt : affineLine x v (t : ℂ) = realEmbed (fun i => x i + t * v i) := by
        funext i
        simp [affineLine, realEmbed]
      have ht' : affineLine x v (t : ℂ) ∈ D₁ ∩ D₂ := ht
      rw [hpt] at ht' ⊢
      exact hreal _ ht'
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    exact htend.frequently hev.frequently
  have heq := (hu₁.analyticOnNhd hO₀).eqOn_of_preconnected_of_frequently_eq
    (hu₂.analyticOnNhd hO₀) hpre h0 hfreq hI
  have hpt : affineLine x v Complex.I = complexPoint x v := by
    funext i
    simp only [affineLine, complexPoint]
    ring
  simpa only [hpt] using heq
theorem sub_cube_div_six_le_arsinh {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.arsinh x := by
  have hder : ∀ t : ℝ, HasDerivAt (fun t => Real.arsinh t - t + t ^ 3 / 6)
      ((√(1 + t ^ 2))⁻¹ - 1 + t ^ 2 / 2) t := fun t => by
    have h := ((Real.hasDerivAt_arsinh t).sub (hasDerivAt_id t)).add
      ((hasDerivAt_pow 3 t).div_const 6)
    refine HasDerivAt.congr_deriv h ?_
    norm_num
    ring
  have hmono : Monotone fun t => Real.arsinh t - t + t ^ 3 / 6 := by
    refine monotone_of_deriv_nonneg (fun t => (hder t).differentiableAt) fun t => ?_
    rw [(hder t).deriv]
    have ha1 : 1 ≤ √(1 + t ^ 2) := by
      rw [Real.one_le_sqrt]
      nlinarith [sq_nonneg t]
    have ha2 : √(1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
    generalize √(1 + t ^ 2) = a at ha1 ha2
    have ha0 : 0 < a := by linarith
    have ht : t ^ 2 = a ^ 2 - 1 := by linarith
    rw [ht]
    have hid : a⁻¹ - 1 + (a ^ 2 - 1) / 2 = (a - 1) ^ 2 * (a + 2) / (2 * a) := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
  have h := hmono hx
  simp only [Real.arsinh_zero] at h
  norm_num at h
  linarith
theorem hullConstants_ranges (hArith : HullConstantsBoundsStatement) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε ≤ 1) :
    (0 < HullConstants.halfWidth ε ∧ HullConstants.halfWidth ε < Real.pi / 2 ∧
      0 < HullConstants.length ε ∧
      HullConstants.halfWidth ε / HullConstants.length ε = 1 / 2 * ε ^ (1 / 2 : ℝ)) ∧
    1 < HullConstants.ratio ε ∧
    (0 < (1 - ε / 2) * (1 - ε / 24) ∧ 0 ≤ HullConstants.exponent ε ∧ HullConstants.exponent ε < 1) ∧
    ∀ n : ℕ, 1 ≤ n →
      0 < HullConstants.ratio ε ^ (-(1 - HullConstants.exponent ε) / (n : ℝ)) ∧
      HullConstants.ratio ε ^ (-(1 - HullConstants.exponent ε) / (n : ℝ)) < 1 :=
  hArith ε h0 h1
theorem length_mul_cosh_arsinh {ε : ℝ} (hl : 0 < HullConstants.length ε) :
    HullConstants.length ε *
        Real.cosh (Real.arsinh (HullConstants.halfWidth ε / HullConstants.length ε))
      = HullConstants.radius ε := by
  rw [Real.cosh_arsinh, HullConstants.radius, ← Real.sqrt_eq_rpow]
  have hsq : (HullConstants.length ε *
        √(1 + (HullConstants.halfWidth ε / HullConstants.length ε) ^ 2)) ^ 2
      = HullConstants.length ε ^ 2 + HullConstants.halfWidth ε ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [← hsq, Real.sqrt_sq (by positivity)]
theorem arsinh_ratio_lower {ε : ℝ} (h0 : 0 < ε) (hb : 0 < HullConstants.halfWidth ε)
    (hl : 0 < HullConstants.length ε)
    (hratio : HullConstants.halfWidth ε / HullConstants.length ε = 1 / 2 * ε ^ (1 / 2 : ℝ)) :
    HullConstants.halfWidth ε / HullConstants.length ε * (1 - ε / 24)
      ≤ Real.arsinh (HullConstants.halfWidth ε / HullConstants.length ε) := by
  have hsq : (HullConstants.halfWidth ε / HullConstants.length ε) ^ 2 = ε / 4 := by
    rw [hratio, mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt h0.le]
    ring
  have hpos : 0 ≤ HullConstants.halfWidth ε / HullConstants.length ε := (div_pos hb hl).le
  have h := sub_cube_div_six_le_arsinh hpos
  have hcube : (HullConstants.halfWidth ε / HullConstants.length ε) ^ 3
      = HullConstants.halfWidth ε / HullConstants.length ε * (ε / 4) := by
    rw [pow_succ, hsq]
    ring
  rw [hcube] at h
  linarith
theorem sum_arsinh_le_exponent_mul {ε : ℝ} {m : ℕ} (h0 : 0 < ε) (h1 : ε ≤ 1)
    (hb : 0 < HullConstants.halfWidth ε) (hl : 0 < HullConstants.length ε)
    (hs0 : 0 ≤ HullConstants.exponent ε)
    (hratio : HullConstants.halfWidth ε / HullConstants.length ε = 1 / 2 * ε ^ (1 / 2 : ℝ))
    {v : Fin m → ℝ} (hv : ∑ j, |v j| ≤ (1 - ε) * (Real.pi / 2)) :
    ∑ j, Real.arsinh (|v j| / HullConstants.length ε)
      ≤ HullConstants.exponent ε *
        Real.arsinh (HullConstants.halfWidth ε / HullConstants.length ε) := by
  have hterm : ∀ j, Real.arsinh (|v j| / HullConstants.length ε)
      ≤ |v j| / HullConstants.length ε := by
    intro j
    have hnn : 0 ≤ Real.arsinh (|v j| / HullConstants.length ε) :=
      Real.arsinh_nonneg_iff.2 (by positivity)
    have := Real.self_le_sinh_iff.2 hnn
    rwa [Real.sinh_arsinh] at this
  have hsum : ∑ j, Real.arsinh (|v j| / HullConstants.length ε)
      ≤ (1 - ε) * (Real.pi / 2) / HullConstants.length ε := by
    calc ∑ j, Real.arsinh (|v j| / HullConstants.length ε)
        ≤ ∑ j, |v j| / HullConstants.length ε := Finset.sum_le_sum fun j _ => hterm j
      _ = (∑ j, |v j|) / HullConstants.length ε := by rw [Finset.sum_div]
      _ ≤ (1 - ε) * (Real.pi / 2) / HullConstants.length ε := by gcongr
  have hlow := arsinh_ratio_lower h0 hb hl hratio
  have hkey : HullConstants.exponent ε *
        (HullConstants.halfWidth ε / HullConstants.length ε * (1 - ε / 24))
      = (1 - ε) * (Real.pi / 2) / HullConstants.length ε := by
    simp only [HullConstants.exponent]
    rw [show HullConstants.halfWidth ε = (1 - ε / 2) * (Real.pi / 2) from rfl]
    have h2 : 2 - ε ≠ 0 := by
      intro h
      linarith
    have h3 : 24 - ε ≠ 0 := by
      intro h
      linarith
    field_simp
  calc ∑ j, Real.arsinh (|v j| / HullConstants.length ε)
      ≤ HullConstants.exponent ε *
          (HullConstants.halfWidth ε / HullConstants.length ε * (1 - ε / 24)) := by
        rw [hkey]
        exact hsum
    _ ≤ HullConstants.exponent ε *
          Real.arsinh (HullConstants.halfWidth ε / HullConstants.length ε) :=
        mul_le_mul_of_nonneg_left hlow hs0
theorem exists_boundedSliceExtension (hArith : HullConstantsBoundsStatement)
    (hRadius : YangMills.Construction.JoukowskiRadius.JoukowskiRadiusProperties)
    (hStrip : EqOnHalfPiStripOfEqOnReal) {m : ℕ} [NeZero m]
    {g : (Fin m → ℝ) → ℂ} (hg : IsSepHolomorphicOnStrips g) (x0 : Fin m → ℝ) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε ≤ 1) (hς : 1 < HullConstants.ratio ε)
    (hfin : supOnCross g x0 (HullConstants.radius ε) (HullConstants.halfWidth ε) < ∞)
    (j : Fin m) (x : ComplexCoordinates m) (hx : x ∈ JointHolomorphy.realClosedCube m) :
    ∃ h : ℂ → ℂ, JointHolomorphy.IsBoundedSliceExtension (HullConstants.ratio ε) hς
      (supOnCross g x0 (HullConstants.radius ε) (HullConstants.halfWidth ε)).toReal
      (fun z => g fun i => x0 i + HullConstants.length ε * (z i).re) j x h := by
  obtain ⟨⟨hb0, hb, hl, hratio⟩, -, -, -⟩ := hullConstants_ranges hArith h0 h1
  obtain ⟨-, -, -, hEllOpen, -, -, -, hAxes, -, -, -, -⟩ := hRadius
  set l := HullConstants.length ε with hldef
  set b := HullConstants.halfWidth ε with hbdef
  set C := HullConstants.radius ε with hCdef
  set ς := HullConstants.ratio ε with hςdef
  set τ := Real.arsinh (b / l) with hτdef
  have hςτ : ς = Real.exp τ := rfl
  have hsinh : (1 / 2 : ℝ) * (ς - ς⁻¹) = b / l := by
    rw [hςτ, ← Real.exp_neg]
    have h := Real.sinh_arsinh (b / l)
    rw [Real.sinh_eq] at h
    rw [← h]
    ring
  have hlcosh : l * Real.cosh τ = C := length_mul_cosh_arsinh hl
  have hcosh : l * ((1 / 2 : ℝ) * (ς + ς⁻¹)) = C := by
    rw [← hlcosh, hςτ, ← Real.exp_neg, Real.cosh_eq]
    ring
  have hlC : l ≤ C := by
    rw [← hlcosh]
    exact le_mul_of_one_le_right hl.le (Real.one_le_cosh _)
  let y : Fin m → ℝ := fun i => x0 i + l * (x i).re
  have hE := stripExtensionAlong_spec hg j y
  have hwstrip : ∀ w ∈ focalEllipse ς hς, (x0 j : ℂ) + (l : ℂ) * w ∈ halfPiStrip ∧
      |((x0 j : ℂ) + (l : ℂ) * w).im| ≤ b ∧ |((x0 j : ℂ) + (l : ℂ) * w).re - x0 j| ≤ C := by
    intro w hw
    obtain ⟨hre, him⟩ := hAxes ς hς w hw
    have himz : ((x0 j : ℂ) + (l : ℂ) * w).im = l * w.im := by simp
    have hrez : ((x0 j : ℂ) + (l : ℂ) * w).re = x0 j + l * w.re := by simp
    have hlt : |((x0 j : ℂ) + (l : ℂ) * w).im| < b := by
      rw [himz, abs_mul, abs_of_pos hl]
      rw [hsinh] at him
      calc l * |w.im| < l * (b / l) := mul_lt_mul_of_pos_left him hl
        _ = b := by field_simp
    refine ⟨hlt.trans hb, hlt.le, ?_⟩
    rw [hrez, add_sub_cancel_left, abs_mul, abs_of_pos hl, ← hcosh]
    exact (mul_lt_mul_of_pos_left hre hl).le
  refine ⟨fun w => stripExtensionAlong g j y ((x0 j : ℂ) + (l : ℂ) * w), ?_, ?_, ?_⟩
  · refine isHolomorphicVia_of_differentiableOn (hEllOpen ς hς) ?_
    have hlin : DifferentiableOn ℂ (fun w : ℂ => (x0 j : ℂ) + (l : ℂ) * w) (focalEllipse ς hς) := by
      fun_prop
    exact hE.1.comp hlin fun w hw => (hwstrip w hw).1
  · intro w hw
    obtain ⟨hws, hwim, hwre⟩ := hwstrip w hw
    let z : ComplexCoordinates m :=
      Function.update (fun i => (y i : ℂ)) j ((x0 j : ℂ) + (l : ℂ) * w)
    have hzj : z j = (x0 j : ℂ) + (l : ℂ) * w := by simp [z]
    have hzi : ∀ i, i ≠ j → z i = (y i : ℂ) := fun i hi => by simp [z, Function.update_of_ne hi]
    have hmem : z ∈ armOfCross x0 C b j := by
      refine ⟨by rw [hzj]; exact hwre, by rw [hzj]; exact hwim, fun i hi => ?_⟩
      rw [hzi i hi]
      refine ⟨by simp, ?_⟩
      have hxi : |(x i).re| ≤ 1 := abs_le.2 (hx i).2
      have : (y i : ℂ) - (x0 i : ℂ) = ((l * (x i).re : ℝ) : ℂ) := by
        simp only [y]
        push_cast
        ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hl]
      exact (mul_le_of_le_one_right hl.le hxi).trans hlC
    have hval : valueAlong g j z = stripExtensionAlong g j y ((x0 j : ℂ) + (l : ℂ) * w) := by
      have hagree := stripExtensionAlong_eqOn hStrip (x := fun i => (z i).re) (x' := y)
        (fun i hi => by rw [hzi i hi]; simp) (stripExtensionAlong_spec hg j _) hE hws
      simpa only [valueAlong, hzj] using hagree
    have hle : ‖valueAlong g j z‖ₑ ≤ supOnCross g x0 C b :=
      le_sSup ⟨j, z, hmem, rfl⟩
    rw [hval] at hle
    have := ENNReal.toReal_mono hfin.ne hle
    rwa [toReal_enorm] at this
  · intro t _
    have hcast : (x0 j : ℂ) + (l : ℂ) * (t : ℂ) = ((x0 j + l * t : ℝ) : ℂ) := by push_cast; rfl
    show stripExtensionAlong g j y ((x0 j : ℂ) + (l : ℂ) * (t : ℂ)) = _
    rw [hcast, hE.2]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [Function.update_of_ne hi, y]
theorem exists_flatPolyEllipse_extension (hArith : HullConstantsBoundsStatement)
    (hRadius : YangMills.Construction.JoukowskiRadius.JoukowskiRadiusProperties)
    (hJoint : JointHolomorphy.SeparateImpliesJoint)
    (hMaps : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hStrip : EqOnHalfPiStripOfEqOnReal) (n : ℕ+)
    {g : (Fin n → ℝ) → ℂ} (hg : IsSepHolomorphicOnStrips g)
    (hA : ∀ (x : Fin n → ℝ) (T b : ℝ), 0 ≤ T → 0 ≤ b → b < Real.pi / 2 →
      supOnCross g x T b < ∞)
    (x0 : Fin n → ℝ) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ∃ G : ComplexCoordinates n → ℂ,
      DifferentiableOn ℂ G (flatPolyEllipse x0 (HullConstants.length ε) (HullConstants.ratio ε)) ∧
      (∀ x : Fin n → ℝ,
        realEmbed x ∈ flatPolyEllipse x0 (HullConstants.length ε) (HullConstants.ratio ε) →
          G (realEmbed x) = g x) ∧
      ∀ v : Fin n → ℝ, ∑ j, |v j| ≤ (1 - ε) * (Real.pi / 2) →
        complexPoint x0 v ∈ flatPolyEllipse x0 (HullConstants.length ε) (HullConstants.ratio ε) ∧
        ‖G (complexPoint x0 v)‖ ≤ HullConstants.boundFactor n ε *
          (supOnCross g x0 (HullConstants.radius ε) (HullConstants.halfWidth ε)).toReal := by
  obtain ⟨⟨hb0, hb, hl, hratio⟩, hς, ⟨-, hs0, hs1⟩, hpow⟩ := hullConstants_ranges hArith h0 h1
  have hC0 : 0 ≤ HullConstants.radius ε := by
    rw [← length_mul_cosh_arsinh hl]
    exact mul_nonneg hl.le (Real.cosh_pos _).le
  have hfin := hA x0 _ _ hC0 hb0.le hb
  have hFc : Continuous fun z : ComplexCoordinates n =>
      g fun i => x0 i + HullConstants.length ε * (z i).re :=
    hg.1.comp (by fun_prop)
  obtain ⟨⟨Fhat, hFhol, -, hFeq, hbound⟩, -⟩ := hJoint n n.pos (HullConstants.ratio ε) hς
    (supOnCross g x0 (HullConstants.radius ε) (HullConstants.halfWidth ε)).toReal
    ENNReal.toReal_nonneg
    (fun z => g fun i => x0 i + HullConstants.length ε * (z i).re) hFc.continuousOn
    (fun j x hx => exists_boundedSliceExtension hArith hRadius hStrip hg x0 h0 h1 hς hfin j x hx)
  have hFd : DifferentiableOn ℂ Fhat (polyEllipseDomain n n.pos (HullConstants.ratio ε) hς) :=
    (differentiableOn_pi.1 (differentiableOn_of_isHolomorphicIn hMaps hFhol)) 0
  have hchart : Differentiable ℂ
      (rescaleChart x0 (HullConstants.length ε) : ComplexCoordinates n → _) := by
    unfold rescaleChart
    fun_prop
  refine ⟨fun z => Fhat (rescaleChart x0 (HullConstants.length ε) z), ?_, ?_, ?_⟩
  · exact hFd.comp hchart.differentiableOn fun z hz => hz.1
  · intro x hx
    have hcube : rescaleChart x0 (HullConstants.length ε) (realEmbed x)
        ∈ JointHolomorphy.realClosedCube n := by
      intro j
      have hj := hx.2 j
      have hchj : rescaleChart x0 (HullConstants.length ε) (realEmbed x) j
          = (((x j - x0 j) / HullConstants.length ε : ℝ) : ℂ) := by
        simp only [rescaleChart, realEmbed]
        push_cast
        rfl
      rw [hchj]
      simp only [realEmbed, Complex.ofReal_re] at hj
      refine ⟨Complex.ofReal_im _, ?_⟩
      rw [Complex.ofReal_re]
      have := abs_lt.1 hj
      constructor
      · rw [le_div_iff₀ hl]
        linarith
      · rw [div_le_iff₀ hl]
        linarith
    show Fhat _ = _
    rw [hFeq _ hcube]
    congr 1
    funext i
    have hre : (rescaleChart x0 (HullConstants.length ε) (realEmbed x) i).re
        = (x i - x0 i) / HullConstants.length ε := by
      simp only [rescaleChart, realEmbed]
      rw [← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hre]
    field_simp
    ring
  · intro v hv
    set l := HullConstants.length ε with hldef
    set ς := HullConstants.ratio ε with hςdef
    set τ := Real.arsinh (HullConstants.halfWidth ε / l) with hτdef
    have hςτ : ς = Real.exp τ := rfl
    have hτ : 0 < τ := by
      have : Real.exp 0 < Real.exp τ := by
        rw [Real.exp_zero, ← hςτ]
        exact hς
      exact Real.exp_lt_exp.1 this
    have hlogς : Real.log ς = τ := by rw [hςτ, Real.log_exp]
    have hςpos : 0 < ς := by linarith
    let t : Fin n → ℝ := fun j => Real.arsinh (|v j| / l)
    have htnn : ∀ j, 0 ≤ t j := fun j => Real.arsinh_nonneg_iff.2 (by positivity)
    have hradius : ∀ j, joukowskiRadius (rescaleChart x0 l (complexPoint x0 v) j) = Real.exp (t j) := by
      intro j
      have hpt := rescaleChart_complexPoint x0 x0 v l j
      rw [sub_self, zero_div, Complex.ofReal_zero, zero_add] at hpt
      rw [hpt]
      refine hRadius.2.2.2.2.2.2.2.2.2.1 _ _ (htnn j) ?_
      simp only [t]
      rw [Real.sinh_arsinh, abs_div, abs_of_pos hl]
    have hsum : ∑ j, t j ≤ HullConstants.exponent ε * τ :=
      sum_arsinh_le_exponent_mul h0 h1 hb0 hl hs0 hratio hv
    have hsτ : HullConstants.exponent ε * τ < τ := by nlinarith
    have hmem : complexPoint x0 v ∈ flatPolyEllipse x0 l ς := by
      refine ⟨?_, fun j => ?_⟩
      · simp only [hradius]
        rw [← Real.exp_sum, hςτ]
        exact Real.exp_lt_exp.2 (hsum.trans_lt hsτ)
      · rw [complexPoint_re, sub_self, abs_zero]
        exact hl
    refine ⟨hmem, ?_⟩
    let sv : Fin n → ℝ := fun j => t j / τ
    have hsv : ∑ j, sv j = (∑ j, t j) / τ := by rw [Finset.sum_div]
    have husum : ∑ j, sv j ≤ HullConstants.exponent ε := by
      rw [hsv, div_le_iff₀ hτ]
      exact hsum
    have hb' := hbound sv (fun j => div_nonneg (htnn j) hτ.le) (husum.trans_lt hs1)
      (rescaleChart x0 l (complexPoint x0 v)) (fun j => by
        rw [hradius j]
        apply le_of_eq
        simp only [RealPower.rpowPos, if_pos hςpos, sv, hlogς]
        congr 1
        field_simp)
    set A := (supOnCross g x0 (HullConstants.radius ε) (HullConstants.halfWidth ε)).toReal with hAdef
    have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
    obtain ⟨-, hq1⟩ := hpow n n.pos
    have hnpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    have hpq : RealPower.rpowPos ς (-(1 - ∑ j, sv j) / ((n : ℕ) : ℝ))
        ≤ ς ^ (-(1 - HullConstants.exponent ε) / ((n : ℕ) : ℝ)) := by
      rw [Real.rpow_def_of_pos hςpos]
      simp only [RealPower.rpowPos, if_pos hςpos]
      refine Real.exp_le_exp.2 ?_
      rw [hlogς, mul_comm τ]
      refine mul_le_mul_of_nonneg_right ?_ hτ.le
      gcongr
    have hfac : (1 - RealPower.rpowPos ς (-(1 - ∑ j, sv j) / ((n : ℕ) : ℝ))) ^
          (-((n : ℕ) : ℤ))
        ≤ (1 - ς ^ (-(1 - HullConstants.exponent ε) / ((n : ℕ) : ℝ))) ^ (-((n : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      have hq : 0 < 1 - ς ^ (-(1 - HullConstants.exponent ε) / ((n : ℕ) : ℝ)) := by linarith
      exact inv_anti₀ (pow_pos hq _) (pow_le_pow_left₀ hq.le (by linarith) _)
    show ‖Fhat (rescaleChart x0 l (complexPoint x0 v))‖ ≤ _
    refine hb'.trans ?_
    have hB : HullConstants.boundFactor n ε
        = (2 : ℝ) ^ (n : ℕ) * (1 - ς ^ (-(1 - HullConstants.exponent ε) / ((n : ℕ) : ℝ))) ^
          (-((n : ℕ) : ℤ)) := rfl
    rw [hB]
    calc (2 : ℝ) ^ (n : ℕ) * A *
          (1 - RealPower.rpowPos ς (-(1 - ∑ j, sv j) / ((n : ℕ) : ℝ))) ^ (-((n : ℕ) : ℤ))
        ≤ (2 : ℝ) ^ (n : ℕ) * A *
          (1 - ς ^ (-(1 - HullConstants.exponent ε) / ((n : ℕ) : ℝ))) ^ (-((n : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = _ := by ring
theorem isOpen_halfPiTube (n : ℕ) [NeZero n] : IsOpen (halfPiTube n) :=
  isOpen_lt (by fun_prop) continuous_const
theorem complexPoint_re_im {m : ℕ} (z : ComplexCoordinates m) :
    complexPoint (fun j => (z j).re) (fun j => (z j).im) = z := by
  funext i
  exact Complex.re_add_im (z i)
theorem tubeExtensionFromStripCross_holds (hArith : HullConstantsBoundsStatement)
    (hRadius : YangMills.Construction.JoukowskiRadius.JoukowskiRadiusProperties)
    (hJoint : JointHolomorphy.SeparateImpliesJoint)
    (hMaps : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hStrip : EqOnHalfPiStripOfEqOnReal) :
    YangMills.Construction.HolomorphicExtension.TubeExtensionFromStripCross := by
  intro n g hg hA
  have hloc := exists_flatPolyEllipse_extension hArith hRadius hJoint hMaps hStrip n hg hA
  choose! G hGd hGr hGb using hloc
  have hpi : 0 < Real.pi := Real.pi_pos
  let eps : ComplexCoordinates n → ℝ := fun z => 1 - 2 / Real.pi * ∑ j, |(z j).im|
  let gHat : ComplexCoordinates n → ℂ := fun z => G (fun j => (z j).re) (eps z) z
  have heps : ∀ z ∈ halfPiTube n, 0 < eps z ∧ eps z ≤ 1 ∧
      ∑ j, |(z j).im| = (1 - eps z) * (Real.pi / 2) := by
    intro z hz
    have hz' : ∑ j, |(z j).im| < Real.pi / 2 := hz
    have hnn : 0 ≤ ∑ j, |(z j).im| := Finset.sum_nonneg fun j _ => abs_nonneg _
    refine ⟨?_, ?_, ?_⟩
    · have : 2 / Real.pi * ∑ j, |(z j).im| < 1 := by
        rw [div_mul_eq_mul_div, div_lt_one hpi]
        linarith
      simp only [eps]
      linarith
    · have : 0 ≤ 2 / Real.pi * ∑ j, |(z j).im| := by positivity
      simp only [eps]
      linarith
    · simp only [eps]
      field_simp
      ring
  have hflatl : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 0 < HullConstants.length ε := fun ε h0 h1 =>
    (hullConstants_ranges hArith h0 h1).1.2.2.1
  have hself : ∀ z ∈ halfPiTube n, z ∈ flatPolyEllipse (fun j => (z j).re)
      (HullConstants.length (eps z)) (HullConstants.ratio (eps z)) := by
    intro z hz
    obtain ⟨h0, h1, hs⟩ := heps z hz
    have := (hGb (fun j => (z j).re) (eps z) h0 h1 (fun j => (z j).im) hs.le).1
    rwa [complexPoint_re_im] at this
  have hagree : ∀ (x0 : Fin n → ℝ) (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ z ∈ halfPiTube n,
      z ∈ flatPolyEllipse x0 (HullConstants.length ε) (HullConstants.ratio ε) →
        gHat z = G x0 ε z := by
    intro x0 ε h0 h1 z hz hzD
    obtain ⟨e0, e1, -⟩ := heps z hz
    have hmain := eq_of_eqOn_real_of_starShaped (x := fun j => (z j).re) (v := fun j => (z j).im)
      (isOpen_flatPolyEllipse hRadius (fun j => (z j).re) (HullConstants.length (eps z))
        (HullConstants.ratio (eps z)))
      (isOpen_flatPolyEllipse hRadius x0 (HullConstants.length ε) (HullConstants.ratio ε))
      (isImaginaryStarShaped_flatPolyEllipse hRadius _ (hflatl _ e0 e1) _)
      (isImaginaryStarShaped_flatPolyEllipse hRadius _ (hflatl _ h0 h1) _)
      (hGd _ _ e0 e1) (hGd _ _ h0 h1)
      (fun x hx => by rw [hGr _ _ e0 e1 x hx.1, hGr _ _ h0 h1 x hx.2])
      (by rw [complexPoint_re_im]; exact hself z hz) (by rw [complexPoint_re_im]; exact hzD)
    rwa [complexPoint_re_im] at hmain
  have hdiff : DifferentiableOn ℂ gHat (halfPiTube n) := by
    intro a ha
    obtain ⟨e0, e1, -⟩ := heps a ha
    set x0 : Fin n → ℝ := fun j => (a j).re with hx0
    have hopen := isOpen_flatPolyEllipse hRadius x0 (HullConstants.length (eps a))
      (HullConstants.ratio (eps a))
    have hnhds : flatPolyEllipse x0 (HullConstants.length (eps a)) (HullConstants.ratio (eps a))
        ∩ halfPiTube n ∈ 𝓝 a := (hopen.inter (isOpen_halfPiTube n)).mem_nhds ⟨hself a ha, ha⟩
    have hat : DifferentiableAt ℂ (G x0 (eps a)) a :=
      (hGd x0 _ e0 e1).differentiableAt (hopen.mem_nhds (hself a ha))
    refine (hat.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hnhds] with z hz
    exact hagree x0 _ e0 e1 z hz.2 hz.1
  refine ⟨gHat, ?_, ?_, ?_⟩
  · refine isHolomorphicIn_of_differentiableOn (isOpen_halfPiTube n) ?_
    rw [differentiableOn_pi]
    exact fun _ => hdiff
  · intro x
    have hpt : (fun j => (x j : ℂ)) = complexPoint x 0 := by
      funext j
      simp [complexPoint]
    have hz : complexPoint x 0 ∈ halfPiTube n := by
      show ∑ j, |(complexPoint x 0 j).im| < Real.pi / 2
      simp only [complexPoint_im, Pi.zero_apply, abs_zero, Finset.sum_const_zero]
      positivity
    have hv0 : ∑ j : Fin n, |(0 : Fin n → ℝ) j| ≤ (1 - (1 : ℝ)) * (Real.pi / 2) := by simp
    have hD := (hGb x 1 one_pos le_rfl 0 hv0).1
    have hreal : complexPoint x 0 = realEmbed x := by
      rw [← hpt]
      rfl
    rw [hpt, hagree x 1 one_pos le_rfl _ hz hD, hreal]
    rw [hreal] at hD
    exact hGr x 1 one_pos le_rfl x hD
  · intro ε h0 h1
    obtain ⟨⟨hb0, hb, -, -⟩, -, -, -⟩ := hullConstants_ranges hArith h0 h1
    refine ⟨hb, fun x v hv => ?_⟩
    obtain ⟨hD, hbd⟩ := hGb x ε h0 h1 v hv
    have hz : complexPoint x v ∈ halfPiTube n := by
      show ∑ j, |(complexPoint x v j).im| < Real.pi / 2
      simp only [complexPoint_im]
      have : (1 - ε) * (Real.pi / 2) < Real.pi / 2 := by nlinarith
      linarith
    have heq : gHat (complexPoint x v) = G x ε (complexPoint x v) := hagree x ε h0 h1 _ hz hD
    have hfin : supOnCross g x (HullConstants.radius ε) (HullConstants.halfWidth ε) < ∞ := by
      refine hA x _ _ ?_ hb0.le hb
      rw [← length_mul_cosh_arsinh (hflatl ε h0 h1)]
      exact mul_nonneg (hflatl ε h0 h1).le (Real.cosh_pos _).le
    show ‖gHat (complexPoint x v)‖ₑ ≤ _
    rw [heq, ← ofReal_norm]
    calc ENNReal.ofReal ‖G x ε (complexPoint x v)‖
        ≤ ENNReal.ofReal (HullConstants.boundFactor n ε *
            (supOnCross g x (HullConstants.radius ε) (HullConstants.halfWidth ε)).toReal) :=
          ENNReal.ofReal_le_ofReal hbd
      _ = _ := by
          rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
end
end YangMills.Construction.HolomorphicExtension.StripCrossHull
