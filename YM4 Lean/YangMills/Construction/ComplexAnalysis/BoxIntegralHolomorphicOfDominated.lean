import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.ComplexAnalysis.BoxIntegralHolomorphic
import YangMills.Construction.ComplexAnalysis.DifferentiationUnderIntegral
import Mathlib
set_option autoImplicit false
open Filter Set Topology MeasureTheory Metric
open YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates
namespace YangMills.Construction.ComplexAnalysis.ParameterBox
variable {N : ℕ}
lemma norm_smul_stdBasisVector (ζ : ℂ) (j : Fin N) : ‖ζ • stdBasisVector j‖ = ‖ζ‖ := by
  simp [stdBasisVector, norm_smul, Pi.norm_single]
lemma differentiableAt_along_axis {O : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    (hu : IsHolomorphicIn (N' := 1) O fun p _ => u p) {q : ComplexCoordinates N} (j : Fin N)
    {w : ℂ} (hq : q + w • stdBasisVector j ∈ O) :
    DifferentiableAt ℂ (fun ζ : ℂ => u (q + ζ • stdBasisVector j)) w := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.HolomorphicFnOn.onLine_at <;> assumption
lemma norm_sub_le_along_axis {O : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    {m : ℝ} (hu : IsHolomorphicIn (N' := 1) O fun p _ => u p) (hm : ∀ p ∈ O, ‖u p‖ ≤ m)
    {q : ComplexCoordinates N} (j : Fin N) {υ : ℝ}
    (hO : ∀ w : ℂ, ‖w‖ < υ → q + w • stdBasisVector j ∈ O) {z : ℂ} (hz : ‖z‖ < υ) :
    ‖u (q + z • stdBasisVector j) - u q‖ ≤ 2 * m / υ * ‖z‖ := by
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => u (q + ζ • stdBasisVector j)) (ball 0 υ) :=
    fun w hw => (differentiableAt_along_axis hu j (hO w (by simpa using hw))).differentiableWithinAt
  have h0 : q + (0 : ℂ) • stdBasisVector j ∈ O :=
    hO 0 (by simpa using (norm_nonneg z).trans_lt hz)
  have hmaps : MapsTo (fun ζ : ℂ => u (q + ζ • stdBasisVector j)) (ball 0 υ)
      (closedBall (u (q + (0 : ℂ) • stdBasisVector j)) (2 * m)) := by
    intro w hw
    have h1 := hm _ (hO w (by simpa using hw))
    have h2 := hm _ h0
    rw [mem_closedBall, dist_eq_norm]
    calc _ ≤ ‖u (q + w • stdBasisVector j)‖ + ‖u (q + (0 : ℂ) • stdBasisVector j)‖ :=
          norm_sub_le _ _
      _ ≤ 2 * m := by linarith
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps
    (show z ∈ ball (0 : ℂ) υ by simpa using hz)
  simpa [dist_eq_norm] using hs
def mixPoint (S : Finset (Fin N)) (p p₀ : ComplexCoordinates N) : ComplexCoordinates N :=
  fun i => if i ∈ S then p i else p₀ i
lemma norm_mixPoint_sub_le {O : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    {m : ℝ} (hu : IsHolomorphicIn (N' := 1) O fun p _ => u p) (hm : ∀ p ∈ O, ‖u p‖ ≤ m)
    {p₀ p : ComplexCoordinates N} {υ : ℝ} (hυ : 0 < υ) (hO : ball p₀ (2 * υ) ⊆ O)
    (hp : p ∈ ball p₀ υ) (S : Finset (Fin N)) :
    ‖u (mixPoint S p p₀) - u p₀‖ ≤ 2 * m / υ * ∑ i ∈ S, ‖p i - p₀ i‖ := by
  have hcoord : ∀ i, ‖p i - p₀ i‖ < υ := fun i => by
    have h1 : ‖p - p₀‖ < υ := by simpa [dist_eq_norm] using hp
    exact (norm_le_pi_norm (p - p₀) i).trans_lt h1
  induction S using Finset.induction_on with
  | empty =>
    have : mixPoint ∅ p p₀ = p₀ := by funext i; simp [mixPoint]
    simp [this]
  | insert j S hj ih =>
    have hmix : mixPoint (insert j S) p p₀ = mixPoint S p p₀ + (p j - p₀ j) • stdBasisVector j := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp [mixPoint, hj, stdBasisVector]
      · simp [mixPoint, stdBasisVector, hij]
    have hq : ‖mixPoint S p p₀ - p₀‖ < υ := by
      refine (pi_norm_lt_iff hυ).2 fun i => ?_
      by_cases hi : i ∈ S
      · simpa [mixPoint, hi] using hcoord i
      · simpa [mixPoint, hi] using hυ
    have hline : ∀ w : ℂ, ‖w‖ < υ → mixPoint S p p₀ + w • stdBasisVector j ∈ O := by
      intro w hw
      apply hO
      rw [mem_ball, dist_eq_norm]
      have hsplit : mixPoint S p p₀ + w • stdBasisVector j - p₀
          = (mixPoint S p p₀ - p₀) + w • stdBasisVector j := by abel
      rw [hsplit]
      calc _ ≤ ‖mixPoint S p p₀ - p₀‖ + ‖w • stdBasisVector j‖ := norm_add_le _ _
        _ < 2 * υ := by rw [norm_smul_stdBasisVector]; linarith
    have hstep := norm_sub_le_along_axis hu hm j hline (hcoord j)
    rw [hmix, Finset.sum_insert hj, mul_add]
    calc _ ≤ ‖u (mixPoint S p p₀ + (p j - p₀ j) • stdBasisVector j) - u (mixPoint S p p₀)‖
          + ‖u (mixPoint S p p₀) - u p₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add hstep ih
lemma norm_sub_le_of_holomorphic {O : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    {m : ℝ} (hm₀ : 0 ≤ m)
    (hu : IsHolomorphicIn (N' := 1) O fun p _ => u p) (hm : ∀ p ∈ O, ‖u p‖ ≤ m)
    {p₀ p : ComplexCoordinates N} {υ : ℝ} (hυ : 0 < υ) (hO : ball p₀ (2 * υ) ⊆ O)
    (hp : p ∈ ball p₀ υ) :
    ‖u p - u p₀‖ ≤ 2 * m / υ * N * ‖p - p₀‖ := by
  have h := norm_mixPoint_sub_le hu hm hυ hO hp Finset.univ
  have hmix : mixPoint Finset.univ p p₀ = p := by funext i; simp [mixPoint]
  rw [hmix] at h
  have hsum : ∑ i : Fin N, ‖p i - p₀ i‖ ≤ N * ‖p - p₀‖ := by
    calc _ ≤ ∑ _i : Fin N, ‖p - p₀‖ := Finset.sum_le_sum fun i _ => norm_le_pi_norm (p - p₀) i
      _ = N * ‖p - p₀‖ := by simp
  have hC : 0 ≤ 2 * m / υ := by positivity
  calc _ ≤ 2 * m / υ * ∑ i : Fin N, ‖p i - p₀ i‖ := h
    _ ≤ 2 * m / υ * (N * ‖p - p₀‖) := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by ring
lemma continuousOn_uncurry_of_bounded {T : Type} [PseudoMetricSpace T] {J : Set T}
    {O : Set (ComplexCoordinates N)} (hOpen : IsOpen O) {γ : T → ComplexCoordinates N → ℂ}
    {m : ℝ} (hm : ∀ t ∈ J, ∀ p ∈ O, ‖γ t p‖ ≤ m)
    (hcont : ∀ p ∈ O, ContinuousOn (fun t => γ t p) J)
    (hhol : ∀ t ∈ J, IsHolomorphicIn (N' := 1) O fun p _ => γ t p) :
    ContinuousOn (Function.uncurry γ) (J ×ˢ O) := by
  rintro ⟨t₀, p₀⟩ ⟨ht₀, hp₀⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hOpen p₀ hp₀
  have hm₀ : 0 ≤ m := (norm_nonneg _).trans (hm t₀ ht₀ p₀ hp₀)
  have hυ : 0 < r / 2 := by positivity
  have hO : ball p₀ (2 * (r / 2)) ⊆ O := by simpa [mul_div_cancel₀] using hball
  set C : ℝ := 2 * m / (r / 2) * N with hCdef
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ :=
    Metric.continuousWithinAt_iff.1 (hcont p₀ hp₀ t₀ ht₀) (ε / 2) (by positivity)
  refine ⟨min δ (min (r / 2) (ε / 2 / (C + 1))), by positivity, ?_⟩
  rintro ⟨t, p⟩ ⟨ht, hp⟩ hdist
  rw [Prod.dist_eq, max_lt_iff] at hdist
  obtain ⟨hdt, hdp⟩ := hdist
  simp only [lt_min_iff] at hdt hdp
  have hdt' : dist t t₀ < δ := hdt.1
  have hdp₁ : dist p p₀ < r / 2 := hdp.2.1
  have hdp₂ : ‖p - p₀‖ < ε / 2 / (C + 1) := by simpa [dist_eq_norm] using hdp.2.2
  have h1 : ‖γ t p - γ t p₀‖ ≤ C * ‖p - p₀‖ :=
    norm_sub_le_of_holomorphic hm₀ (hhol t ht) (hm t ht) hυ hO (by simpa using hdp₁)
  have h2 : dist (γ t p₀) (γ t₀ p₀) < ε / 2 := hnear ht hdt'
  have h3 : ‖p - p₀‖ * (C + 1) < ε / 2 := (lt_div_iff₀ (by positivity)).1 hdp₂
  have h4 : ‖γ t p - γ t p₀‖ < ε / 2 := by nlinarith [norm_nonneg (p - p₀)]
  show dist (γ t p) (γ t₀ p₀) < ε
  calc dist (γ t p) (γ t₀ p₀) ≤ dist (γ t p) (γ t p₀) + dist (γ t p₀) (γ t₀ p₀) :=
        dist_triangle _ _ _
    _ < ε := by rw [dist_eq_norm (γ t p)]; linarith
theorem boxIntegralHolomorphicInParameter_of_dominated
    (hDep : DominatedIntegralHolomorphicAndDeriv) : BoxIntegralHolomorphicInParameter := by
  intro n N _ hN a b _ O hO γ hbound hcont hhol
  obtain ⟨m, hm⟩ := hbound
  refine ⟨continuousOn_uncurry_of_bounded hO hm hcont hhol, ?_⟩
  have hint : Integrable (fun _ : Icc a b => m)
      (Measure.comap (Subtype.val : Icc a b → Fin n → ℝ) volume) := by
    have hon : IntegrableOn (fun _ : Fin n → ℝ => m) (Icc a b) volume :=
      continuous_const.continuousOn.integrableOn_compact isCompact_Icc
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).1 hon
  have hmeas : ∀ z ∈ O, Measurable fun ω : Icc a b => γ ω z := fun z hz =>
    (continuousOn_iff_continuous_domRestrict.1 (hcont z hz)).measurable
  have h := (hDep (Icc a b) (Measure.comap (Subtype.val : Icc a b → Fin n → ℝ) volume) N hN O hO
    (fun z ω => γ ω z) (fun _ => m) hmeas (fun ω => hhol ω.1 ω.2)
    (fun z hz ω => hm ω.1 ω.2 z hz) hint).1
  have hfun : (fun (p : ComplexCoordinates N) (_ : Fin 1) => ∫ t in Icc a b, γ t p)
      = fun p _ => ∫ ω : Icc a b, γ ω p
          ∂(Measure.comap (Subtype.val : Icc a b → Fin n → ℝ) volume) := by
    funext p _
    exact (integral_subtype_comap measurableSet_Icc fun t => γ t p).symm
  rw [hfun]
  exact h
end YangMills.Construction.ComplexAnalysis.ParameterBox
