import YangMills.Construction.ComplexAnalysis.RealPieceIdentity
import YangMills.Construction.Towers.TaylorCoefficientsInTheLeftChartAreRealAnalyticProof
import Mathlib
open Filter Set
open scoped ComplexConjugate Topology
namespace YangMills.Construction.ComplexAnalysis.RealPiece
open YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates
variable {N N' : ℕ}
private theorem differentiableOn_of_isHolomorphicIn
    (h : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (hf : IsHolomorphicIn O f) :
    DifferentiableOn ℂ f O := by apply _root_.YangMills.Construction.Tower.LeftChartTaylor.differentiableOn_of_isHolomorphicIn <;> assumption
private theorem eq_zero_on_complexLine {O : Set (ComplexCoordinates N)}
    {g : ComplexCoordinates N → ComplexCoordinates N'}
    (hg : DifferentiableOn ℂ g O) (x y : ComplexCoordinates N) {r : ℝ} (hr : 0 < r)
    (hline : ∀ ζ ∈ Metric.ball (0 : ℂ) r, x + ζ • y ∈ O)
    (hzero : ∃ᶠ ζ in 𝓝[≠] (0 : ℂ), g (x + ζ • y) = 0) :
    ∀ ζ ∈ Metric.ball (0 : ℂ) r, g (x + ζ • y) = 0 := by
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => g (x + ζ • y)) (Metric.ball (0 : ℂ) r) :=
    hg.comp (f := fun ζ : ℂ => x + ζ • y) (by fun_prop) hline
  have ha := hd.analyticOnNhd Metric.isOpen_ball
  exact ha.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
    (Metric.mem_ball_self hr) hzero
private theorem eq_zero_on_ball_of_eventually_zero_at_center {O : Set (ComplexCoordinates N)}
    {g : ComplexCoordinates N → ComplexCoordinates N'} (hg : DifferentiableOn ℂ g O)
    {b : ComplexCoordinates N} {s : ℝ} (hball : Metric.ball b s ⊆ O)
    (hnear : ∀ᶠ w in 𝓝 b, g w = 0) : ∀ z ∈ Metric.ball b s, g z = 0 := by
  intro z hz
  have hzs : ‖z - b‖ < s := by simpa [dist_eq_norm] using hz
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg _) hzs
  set m : ℝ := (‖z - b‖ + s) / 2 with hm
  have hm0 : 0 < m := by have := norm_nonneg (z - b); rw [hm]; linarith
  have hms : m < s := by rw [hm]; linarith
  have hym : ‖z - b‖ ≤ m := by rw [hm]; linarith
  have hr : 1 < s / m := (one_lt_div hm0).2 hms
  have hline : ∀ ζ ∈ Metric.ball (0 : ℂ) (s / m), b + ζ • (z - b) ∈ O := by
    intro ζ hζ
    apply hball
    have hζ' : ‖ζ‖ < s / m := by simpa using hζ
    have h1 : ‖ζ‖ * m < s := (lt_div_iff₀ hm0).1 hζ'
    have h2 : ‖ζ‖ * ‖z - b‖ ≤ ‖ζ‖ * m := mul_le_mul_of_nonneg_left hym (norm_nonneg _)
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    linarith
  have hcont : Tendsto (fun ζ : ℂ => b + ζ • (z - b)) (𝓝 0) (𝓝 b) := by
    have : Continuous (fun ζ : ℂ => b + ζ • (z - b)) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), g (b + ζ • (z - b)) = 0 :=
    (hcont.eventually hnear).filter_mono nhdsWithin_le_nhds
  have h1 := eq_zero_on_complexLine hg b (z - b) (by linarith) hline hev.frequently 1
    (by simpa using hr)
  simpa using h1
private theorem eq_zero_near_realLocus_point {O : Set (ComplexCoordinates N)}
    {g : ComplexCoordinates N → ComplexCoordinates N'} (hg : DifferentiableOn ℂ g O)
    {p : ComplexCoordinates N} (hp : p ∈ realLocus N) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball p (3 * δ) ⊆ O)
    (hreal : ∀ z ∈ Metric.ball p (3 * δ), z ∈ realLocus N → g z = 0) :
    ∀ z ∈ Metric.ball p δ, g z = 0 := by
  intro z hz
  have hzp : ‖z - p‖ < δ := by simpa [dist_eq_norm] using hz
  have hcoord : ∀ j, ‖z j - p j‖ < δ := (pi_norm_lt_iff hδ).1 hzp
  set x : ComplexCoordinates N := fun j => ((z j).re : ℂ) with hx
  set y : ComplexCoordinates N := fun j => ((z j).im : ℂ) with hy
  have hpj : ∀ j, p j = ((p j).re : ℂ) := fun j => by
    apply Complex.ext
    · simp
    · simpa using hp j
  have hxp : ‖x - p‖ < δ := by
    refine (pi_norm_lt_iff hδ).2 fun j => ?_
    have h1 : (x - p) j = (((z j - p j).re : ℝ) : ℂ) := by
      rw [Pi.sub_apply, hx, hpj j]
      simp
    rw [h1, Complex.norm_real]
    exact lt_of_le_of_lt (Complex.abs_re_le_norm _) (hcoord j)
  have hyn : ‖y‖ < δ := by
    refine (pi_norm_lt_iff hδ).2 fun j => ?_
    have h1 : y j = (((z j - p j).im : ℝ) : ℂ) := by
      have : (p j).im = 0 := hp j
      simp [hy, this]
    rw [h1, Complex.norm_real]
    exact lt_of_le_of_lt (Complex.abs_im_le_norm _) (hcoord j)
  have hnear : ∀ ζ : ℂ, ‖ζ‖ < 2 → x + ζ • y ∈ Metric.ball p (3 * δ) := by
    intro ζ hζ
    have h1 : ‖ζ‖ * ‖y‖ ≤ 2 * δ := by
      have := norm_nonneg y
      have := norm_nonneg ζ
      nlinarith
    have h2 : x + ζ • y - p = (x - p) + ζ • y := by abel
    rw [Metric.mem_ball, dist_eq_norm, h2]
    calc ‖(x - p) + ζ • y‖ ≤ ‖x - p‖ + ‖ζ • y‖ := norm_add_le _ _
      _ = ‖x - p‖ + ‖ζ‖ * ‖y‖ := by rw [norm_smul]
      _ < 3 * δ := by linarith
  have hline : ∀ ζ ∈ Metric.ball (0 : ℂ) 2, x + ζ • y ∈ O := fun ζ hζ =>
    hball (hnear ζ (by simpa using hζ))
  have hu : Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h0 := (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [Complex.ofReal_zero] at h0
      exact h0
    · have : (1 : ℝ) / ((n : ℝ) + 1) ≠ 0 := by positivity
      exact Complex.ofReal_ne_zero.2 this
  have hfreq : ∃ᶠ ζ in 𝓝[≠] (0 : ℂ), g (x + ζ • y) = 0 := by
    refine hu.frequently (Eventually.frequently (Eventually.of_forall fun n => ?_))
    set t : ℝ := (1 : ℝ) / ((n : ℝ) + 1) with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hnorm : ‖(t : ℂ)‖ < 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      linarith
    refine hreal _ (hnear _ hnorm) fun j => ?_
    simp [hx, hy]
  have hI := eq_zero_on_complexLine hg x y (by norm_num) hline hfreq Complex.I (by simp)
  have hzxy : x + Complex.I • y = z := by
    funext j
    apply Complex.ext <;> simp [hx, hy]
  rwa [hzxy] at hI
private theorem continuous_conjCoords {N : ℕ} :
    Continuous (conjCoords : ComplexCoordinates N → ComplexCoordinates N) :=
  continuous_pi fun j => Complex.continuous_conj.comp (continuous_apply j)
theorem eqOfEqOnRealOpenAndConjHolomorphic_of_powerSeries
    (h : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    EqOfEqOnRealOpenAndConjHolomorphic := by
  constructor
  · intro N N' O R f₁ f₂ hO hconn hf₁ hf₂ hne hRO hRopen heq
    have hd₁ := differentiableOn_of_isHolomorphicIn h hf₁
    have hd₂ := differentiableOn_of_isHolomorphicIn h hf₂
    set g : ComplexCoordinates N → ComplexCoordinates N' := fun z => f₁ z - f₂ z with hgdef
    have hg : DifferentiableOn ℂ g O := hd₁.fun_sub hd₂
    have hopen : IsOpen {z | ∀ᶠ w in 𝓝 z, g w = 0} := isOpen_setOfPred_eventually_nhds
    have hstart : (O ∩ {z | ∀ᶠ w in 𝓝 z, g w = 0}).Nonempty := by
      obtain ⟨p, hpR⟩ := hne
      obtain ⟨U, hU, rfl⟩ := hRopen
      have hpO : p ∈ O := (hRO hpR).1
      have hpr : p ∈ realLocus N := (hRO hpR).2
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hO.inter hU) p ⟨hpO, hpR.1⟩
      have hδ : 0 < ε / 3 := by positivity
      have hball' : Metric.ball p (3 * (ε / 3)) ⊆ O ∩ U := by
        rwa [mul_div_cancel₀ ε (by norm_num : (3 : ℝ) ≠ 0)]
      have hzero := eq_zero_near_realLocus_point hg hpr hδ (fun z hz => (hball' hz).1)
        (fun z hz hzr => sub_eq_zero.2 (heq ⟨(hball' hz).2, hzr⟩))
      refine ⟨p, hpO, ?_⟩
      filter_upwards [Metric.ball_mem_nhds p hδ] with z hz using hzero z hz
    have hclosed : closure {z | ∀ᶠ w in 𝓝 z, g w = 0} ∩ O ⊆ {z | ∀ᶠ w in 𝓝 z, g w = 0} := by
      rintro a ⟨hac, haO⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO a haO
      obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.1 hac (ε / 2) (by positivity)
      have hsub : Metric.ball b (ε / 2) ⊆ O := by
        intro w hw
        apply hball
        rw [Metric.mem_ball] at hw ⊢
        have := dist_triangle w b a
        rw [dist_comm b a] at this
        linarith
      have hzero := eq_zero_on_ball_of_eventually_zero_at_center hg hsub hb
      have ha : a ∈ Metric.ball b (ε / 2) := by
        rw [Metric.mem_ball]
        exact hab
      show ∀ᶠ w in 𝓝 a, g w = 0
      filter_upwards [Metric.isOpen_ball.mem_nhds ha] with z hz using hzero z hz
    have hall := hconn.isPreconnected.subset_of_closure_inter_subset hopen hstart hclosed
    intro z hz
    have hz0 : z ∈ {w | g w = 0} := mem_of_mem_nhds (hall hz)
    exact sub_eq_zero.1 hz0
  · intro N N' O f hO hmap hf
    refine ⟨hO, ?_, ?_⟩
    · exact continuous_conjCoords.comp_continuousOn
        (hf.2.1.comp continuous_conjCoords.continuousOn hmap)
    · intro a ha j
      have hev := hf.2.2 _ (hmap ha) j
      have ht : Tendsto (fun ζ : ℂ => conj ζ) (𝓝 0) (𝓝 0) := by
        simpa using Complex.continuous_conj.tendsto 0
      filter_upwards [ht.eventually hev] with ζ hζ
      have hfun : (fun ζ : ℂ => conjCoords (f (conjCoords (a + ζ • stdBasisVector j)))) =
          star ∘ (fun w : ℂ => f (conjCoords a + w • stdBasisVector j)) ∘ conj := by
        funext w
        have : conjCoords (a + w • stdBasisVector j) =
            conjCoords a + conj w • stdBasisVector j := by
          funext i
          by_cases hij : i = j
          · subst hij
            simp [conjCoords, stdBasisVector]
          · simp [conjCoords, stdBasisVector, Pi.single_eq_of_ne hij]
        rw [this]
        rfl
      rw [hfun]
      exact differentiableAt_star_conj_iff.2 hζ
end YangMills.Construction.ComplexAnalysis.RealPiece
