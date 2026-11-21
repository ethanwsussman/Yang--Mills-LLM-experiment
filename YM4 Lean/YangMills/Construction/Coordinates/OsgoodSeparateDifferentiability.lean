import YangMills.Construction.Coordinates.HolomorphicIffDifferentiable
import Mathlib
open Asymptotics Filter Metric Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.Coordinates.ComplexCoordinates.HolomorphicDifferentiable
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [CompleteSpace F]
theorem norm_sub_sub_smul_deriv_le_of_bounded {h : ℂ → F} {c z : ℂ} {r M : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ h (ball c r)) (hb : ∀ ζ ∈ ball c r, ‖h ζ‖ ≤ M)
    (hz : z ∈ ball c r) :
    ‖h z - h c - (z - c) • deriv h c‖ ≤ 4 * M / r ^ 2 * ‖z - c‖ ^ 2 := by
  have hc : c ∈ ball c r := mem_ball_self hr
  have hmaps : MapsTo h (ball c r) (closedBall (h c) (2 * M)) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm]
    calc ‖h y - h c‖ ≤ ‖h y‖ + ‖h c‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hb y hy) (hb c hc)
      _ = 2 * M := by ring
  have hg : ∀ y ∈ ball c r, ‖dslope h c y‖ ≤ 2 * M / r := fun y hy =>
    Complex.norm_dslope_le_div_of_mapsTo_ball hd hmaps hy
  have hgd : DifferentiableOn ℂ (dslope h c) (ball c r) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds c hr)).2 hd
  have hmaps' : MapsTo (dslope h c) (ball c r) (closedBall (dslope h c c) (2 * (2 * M / r))) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm]
    calc ‖dslope h c y - dslope h c c‖ ≤ ‖dslope h c y‖ + ‖dslope h c c‖ := norm_sub_le _ _
      _ ≤ 2 * M / r + 2 * M / r := add_le_add (hg y hy) (hg c hc)
      _ = 2 * (2 * M / r) := by ring
  have hgg : ‖dslope (dslope h c) c z‖ ≤ 2 * (2 * M / r) / r :=
    Complex.norm_dslope_le_div_of_mapsTo_ball hgd hmaps' hz
  have hid : h z - h c - (z - c) • deriv h c = (z - c) • (z - c) • dslope (dslope h c) c z := by
    rw [sub_smul_dslope, ← sub_smul_dslope h c z, dslope_same, smul_sub]
  rw [hid, norm_smul, norm_smul]
  calc ‖z - c‖ * (‖z - c‖ * ‖dslope (dslope h c) c z‖)
      ≤ ‖z - c‖ * (‖z - c‖ * (2 * (2 * M / r) / r)) := by gcongr
    _ = 4 * M / r ^ 2 * ‖z - c‖ ^ 2 := by field_simp; ring
theorem differentiableAt_prod_of_partial {g : ℂ × E → F} {z₀ : ℂ} {w₀ : E}
    (hU : ∀ᶠ p in 𝓝 (z₀, w₀), ContinuousAt g p ∧
      DifferentiableAt ℂ (fun z : ℂ => g (z, p.2)) p.1)
    (hw : DifferentiableAt ℂ (fun w : E => g (z₀, w)) w₀) :
    DifferentiableAt ℂ g (z₀, w₀) := by
  have hc₀ : ContinuousAt g (z₀, w₀) := hU.self_of_nhds.1
  set M : ℝ := ‖g (z₀, w₀)‖ + 1 with hM
  have hbound : ∀ᶠ p in 𝓝 (z₀, w₀), ‖g p‖ ≤ M := by
    have : ∀ᶠ p in 𝓝 (z₀, w₀), ‖g p‖ < M :=
      hc₀.norm.eventually_lt_const (by simp [hM])
    exact this.mono fun p hp => hp.le
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hU.and hbound)
  have hmem : ∀ {z : ℂ} {w : E}, z ∈ ball z₀ r → w ∈ ball w₀ r → (z, w) ∈ ball (z₀, w₀) r := by
    intro z w hz hw'
    rw [← ball_prod_same]
    exact ⟨hz, hw'⟩
  have hw₀ : w₀ ∈ ball w₀ r := mem_ball_self hr
  set a : E → F := fun w => deriv (fun z : ℂ => g (z, w)) z₀ with ha
  set C : ℝ := 4 * M / r ^ 2 with hC
  have hCpos : 0 < C := by positivity
  have hT : ∀ w ∈ ball w₀ r, ∀ z ∈ ball z₀ r,
      ‖g (z, w) - g (z₀, w) - (z - z₀) • a w‖ ≤ C * ‖z - z₀‖ ^ 2 := by
    intro w hw' z hz
    refine norm_sub_sub_smul_deriv_le_of_bounded (h := fun z : ℂ => g (z, w)) hr ?_ ?_ hz
    · intro y hy
      exact (hball _ (hmem hy hw')).1.2.differentiableWithinAt
    · intro y hy
      exact (hball _ (hmem hy hw')).2
  have hA : Tendsto a (𝓝 w₀) (𝓝 (a w₀)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set t : ℝ := min (r / 2) (ε / (8 * C)) with ht
    have htpos : 0 < t := lt_min (by positivity) (by positivity)
    have htr : t < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htε : C * t ≤ ε / 8 := by
      have : t ≤ ε / (8 * C) := min_le_right _ _
      calc C * t ≤ C * (ε / (8 * C)) := by gcongr
        _ = ε / 8 := by field_simp
    set z₁ : ℂ := z₀ + (t : ℂ) with hz₁
    have hnt : ‖(t : ℂ)‖ = t := by simp [abs_of_pos htpos]
    have hz₁b : z₁ ∈ ball z₀ r := by
      rw [mem_ball, dist_eq_norm, hz₁, add_sub_cancel_left, hnt]
      exact htr
    have hcz₁ : ContinuousAt (fun w : E => g (z₁, w)) w₀ :=
      ContinuousAt.comp (f := fun w : E => (z₁, w)) (g := g)
        (hball _ (hmem hz₁b hw₀)).1.1 (by fun_prop)
    have hcz₀ : ContinuousAt (fun w : E => g (z₀, w)) w₀ :=
      ContinuousAt.comp (f := fun w : E => (z₀, w)) (g := g) hc₀ (by fun_prop)
    have hpos : 0 < ε * t / 8 := by positivity
    filter_upwards [Metric.tendsto_nhds.1 hcz₁ _ hpos, Metric.tendsto_nhds.1 hcz₀ _ hpos,
      ball_mem_nhds w₀ hr] with w h₁ h₀ hwb
    rw [dist_eq_norm] at h₁ h₀ ⊢
    have e₁ := hT w hwb z₁ hz₁b
    have e₀ := hT w₀ hw₀ z₁ hz₁b
    have hzz : z₁ - z₀ = (t : ℂ) := by rw [hz₁, add_sub_cancel_left]
    rw [hzz, hnt] at e₁ e₀
    have hid : (t : ℂ) • (a w - a w₀) =
        (g (z₁, w) - g (z₁, w₀)) - (g (z₀, w) - g (z₀, w₀))
          - (g (z₁, w) - g (z₀, w) - (t : ℂ) • a w)
          + (g (z₁, w₀) - g (z₀, w₀) - (t : ℂ) • a w₀) := by
      rw [smul_sub]; abel
    have hle : t * ‖a w - a w₀‖ ≤ ε * t / 8 + ε * t / 8 + C * t ^ 2 + C * t ^ 2 := by
      have hnorm : ‖(t : ℂ) • (a w - a w₀)‖ = t * ‖a w - a w₀‖ := by rw [norm_smul, hnt]
      rw [← hnorm, hid]
      refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add ((norm_sub_le _ _).trans (add_le_add h₁.le h₀.le)) e₁)) e₀)
    have hCt : C * t ^ 2 ≤ ε * t / 8 := by
      calc C * t ^ 2 = (C * t) * t := by ring
        _ ≤ ε / 8 * t := by gcongr
        _ = ε * t / 8 := by ring
    have : t * ‖a w - a w₀‖ < t * ε := by nlinarith
    exact lt_of_mul_lt_mul_left this htpos.le
  set L : E →L[ℂ] F := fderiv ℂ (fun w : E => g (z₀, w)) w₀ with hL
  have hLd : HasFDerivAt (fun w : E => g (z₀, w)) L w₀ := hw.hasFDerivAt
  set D : ℂ × E →L[ℂ] F :=
    (ContinuousLinearMap.fst ℂ ℂ E).smulRight (a w₀) + L.comp (ContinuousLinearMap.snd ℂ ℂ E)
    with hD
  have hfd : HasFDerivAt g D (z₀, w₀) := by
    refine HasFDerivAt.of_isLittleO ?_
    rw [isLittleO_iff]
    intro c hc
    have hc3 : 0 < c / 3 := by positivity
    have h₁ : ∀ᶠ w in 𝓝 w₀, ‖a w - a w₀‖ ≤ c / 3 := by
      filter_upwards [Metric.tendsto_nhds.1 hA _ hc3] with w hw'
      rw [dist_eq_norm] at hw'
      exact hw'.le
    have h₂ : ∀ᶠ w in 𝓝 w₀, ‖g (z₀, w) - g (z₀, w₀) - L (w - w₀)‖ ≤ c / 3 * ‖w - w₀‖ :=
      (isLittleO_iff.1 hLd.isLittleO) hc3
    have h₃ : ∀ᶠ z in 𝓝 z₀, ‖z - z₀‖ < c / 3 / C := by
      have : ball z₀ (c / 3 / C) ∈ 𝓝 z₀ := ball_mem_nhds z₀ (by positivity)
      filter_upwards [this] with z hz
      rwa [mem_ball, dist_eq_norm] at hz
    have hsnd : Tendsto (Prod.snd : ℂ × E → E) (𝓝 (z₀, w₀)) (𝓝 w₀) := continuous_snd.tendsto _
    have hfst : Tendsto (Prod.fst : ℂ × E → ℂ) (𝓝 (z₀, w₀)) (𝓝 z₀) := continuous_fst.tendsto _
    filter_upwards [hsnd.eventually h₁, hsnd.eventually h₂, hfst.eventually h₃,
      hsnd.eventually (ball_mem_nhds w₀ hr), hfst.eventually (ball_mem_nhds z₀ hr)]
      with p p₁ p₂ p₃ pw pz
    obtain ⟨z, w⟩ := p
    simp only at p₁ p₂ p₃ pw pz
    have hz' : ‖z - z₀‖ ≤ ‖(z, w) - (z₀, w₀)‖ := by
      simp
    have hw' : ‖w - w₀‖ ≤ ‖(z, w) - (z₀, w₀)‖ := by
      simp
    have hid : g (z, w) - g (z₀, w₀) - D ((z, w) - (z₀, w₀)) =
        (g (z, w) - g (z₀, w) - (z - z₀) • a w) + (z - z₀) • (a w - a w₀)
          + (g (z₀, w) - g (z₀, w₀) - L (w - w₀)) := by
      simp only [hD, add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub, smul_sub]
      abel
    rw [hid]
    have hq : C * ‖z - z₀‖ ^ 2 ≤ c / 3 * ‖z - z₀‖ := by
      have : C * ‖z - z₀‖ ≤ c / 3 := by
        rw [lt_div_iff₀ hCpos] at p₃
        linarith
      calc C * ‖z - z₀‖ ^ 2 = (C * ‖z - z₀‖) * ‖z - z₀‖ := by ring
        _ ≤ c / 3 * ‖z - z₀‖ := by gcongr
    have hs : ‖(z - z₀) • (a w - a w₀)‖ ≤ c / 3 * ‖z - z₀‖ := by
      rw [norm_smul, mul_comm]
      gcongr
    calc _ ≤ ‖g (z, w) - g (z₀, w) - (z - z₀) • a w‖ + ‖(z - z₀) • (a w - a w₀)‖
            + ‖g (z₀, w) - g (z₀, w₀) - L (w - w₀)‖ := norm_add₃_le
      _ ≤ c / 3 * ‖z - z₀‖ + c / 3 * ‖z - z₀‖ + c / 3 * ‖w - w₀‖ := by
          have := hT w pw z pz
          gcongr
          exact this.trans hq
      _ ≤ c / 3 * ‖(z, w) - (z₀, w₀)‖ + c / 3 * ‖(z, w) - (z₀, w₀)‖
            + c / 3 * ‖(z, w) - (z₀, w₀)‖ := by gcongr
      _ = c * ‖(z, w) - (z₀, w₀)‖ := by ring
  exact hfd.differentiableAt
theorem fin_cons_eq_add_smul_stdBasisVector_zero {n : ℕ} (z z' : ℂ) (w : ComplexCoordinates n) :
    (Fin.cons z w : ComplexCoordinates (n + 1)) =
      (Fin.cons z' w : ComplexCoordinates (n + 1)) + (z - z') • stdBasisVector 0 := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [stdBasisVector]
  · simp [stdBasisVector]
theorem fin_cons_add_smul_stdBasisVector {n : ℕ} (z ζ : ℂ) (b : ComplexCoordinates n)
    (j : Fin n) :
    (Fin.cons z (b + ζ • stdBasisVector j) : ComplexCoordinates (n + 1)) =
      (Fin.cons z b : ComplexCoordinates (n + 1)) + ζ • stdBasisVector j.succ := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [stdBasisVector]
  · simp [stdBasisVector, Pi.single_apply]
theorem differentiableOn_of_continuousOn_of_coordinate_lines (n : ℕ) :
    ∀ (O : Set (ComplexCoordinates n)) (f : ComplexCoordinates n → F), IsOpen O →
      ContinuousOn f O →
      (∀ a ∈ O, ∀ j : Fin n,
        DifferentiableAt ℂ (fun ζ : ℂ => f (a + ζ • stdBasisVector j)) 0) →
      DifferentiableOn ℂ f O := by
  induction n with
  | zero =>
    intro O f _ _ _
    have : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
    rw [this]
    exact differentiableOn_const _
  | succ n ih =>
    intro O f hO hc hs
    set e : (ℂ × ComplexCoordinates n) ≃L[ℂ] ComplexCoordinates (n + 1) :=
      Fin.consEquivL ℂ (fun _ : Fin (n + 1) => ℂ) with he
    have happ : ∀ (z : ℂ) (w : ComplexCoordinates n),
        e (z, w) = (Fin.cons z w : ComplexCoordinates (n + 1)) := fun _ _ => rfl
    have hkey : ∀ p : ℂ × ComplexCoordinates n, e p ∈ O → DifferentiableAt ℂ (f ∘ e) p := by
      rintro ⟨z₀, w₀⟩ hp
      have hev : ∀ᶠ p in 𝓝 (z₀, w₀), e p ∈ O :=
        e.continuous.continuousAt.eventually_mem (hO.mem_nhds hp)
      refine differentiableAt_prod_of_partial ?_ ?_
      · filter_upwards [hev] with p hpO
        refine ⟨ContinuousAt.comp (g := f) (hc.continuousAt (hO.mem_nhds hpO))
          e.continuous.continuousAt, ?_⟩
        obtain ⟨z₁, w₁⟩ := p
        have hline := hs _ hpO 0
        have hsub : DifferentiableAt ℂ (fun z : ℂ => z - z₁) z₁ := by fun_prop
        have hline' : DifferentiableAt ℂ (fun ζ : ℂ => f (e (z₁, w₁) + ζ • stdBasisVector 0))
            ((fun z : ℂ => z - z₁) z₁) := by simpa using hline
        have := DifferentiableAt.comp (f := fun z : ℂ => z - z₁) z₁ hline' hsub
        refine this.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
        simp only [Function.comp_apply]
        rw [happ, happ, fin_cons_eq_add_smul_stdBasisVector_zero z z₁ w₁]
      · have hO' : IsOpen {w : ComplexCoordinates n | e (z₀, w) ∈ O} :=
          hO.preimage (e.continuous.comp (by fun_prop))
        have hd := ih {w | e (z₀, w) ∈ O} (fun w => f (e (z₀, w))) hO'
          (hc.comp (e.continuous.comp (by fun_prop)).continuousOn fun _ hw => hw)
          (fun b hb j => by
            have hline := hs _ hb j.succ
            refine hline.congr_of_eventuallyEq (Eventually.of_forall fun ζ => ?_)
            simp only [happ]
            rw [fin_cons_add_smul_stdBasisVector])
        exact (hd w₀ hp).differentiableAt (hO'.mem_nhds hp)
    intro x hx
    have hx' : e (e.symm x) ∈ O := by simpa using hx
    have hcomp : DifferentiableAt ℂ ((f ∘ e) ∘ e.symm) x :=
      DifferentiableAt.comp x (hkey _ hx') e.symm.differentiableAt
    have hf : (f ∘ e) ∘ e.symm = f := by
      funext y
      simp
    rw [hf] at hcomp
    exact hcomp.differentiableWithinAt
theorem holomorphicIffDifferentiableStatement_holds : HolomorphicIffDifferentiableStatement := by
  intro N N' O f hO
  constructor
  · rintro ⟨_, hc, hs⟩
    exact differentiableOn_of_continuousOn_of_coordinate_lines N O f hO hc
      fun a ha j => (hs a ha j).self_of_nhds
  · intro hd
    refine ⟨hO, hd.continuousOn, fun a ha j => ?_⟩
    have hcont : ContinuousAt (fun ζ : ℂ => a + ζ • stdBasisVector j) 0 := by fun_prop
    have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • stdBasisVector j ∈ O :=
      hcont.eventually_mem (by simpa using hO.mem_nhds ha)
    filter_upwards [hev] with ζ hζ
    exact DifferentiableAt.comp ζ ((hd _ hζ).differentiableAt (hO.mem_nhds hζ)) (by fun_prop)
end YangMills.Construction.Coordinates.ComplexCoordinates.HolomorphicDifferentiable
