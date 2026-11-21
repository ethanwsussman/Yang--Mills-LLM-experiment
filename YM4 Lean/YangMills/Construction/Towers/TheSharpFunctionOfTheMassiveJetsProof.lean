import YangMills.Construction.Towers.TheMassiveCoefficientIsRealAnalytic
import YangMills.Construction.Towers.TheMassiveFunctionIsLocallyHolomorphic
import YangMills.Construction.Towers.TheMixedDerivativeOfTheMassiveFunction
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import YangMills.Construction.Towers.TheSharpFunctionOfTheMassiveJets
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.SharpLogFn
open YangMills.Construction.Tower.FullSpace.BackgroundJets YangMills.Construction.PeriodicOperators
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn asLine)
open YangMills.Construction.OneLoopLaw.TemperedStiffness (secondPartialAtZero)
def partialAlong {N : ℕ} (v : ComplexCoordinates N) (g : ComplexCoordinates N → ComplexCoordinates 1) :
    ComplexCoordinates N → ComplexCoordinates 1 :=
  fun w => fderiv ℝ g w v
section Holomorphic
variable {N : ℕ} {O : Set (ComplexCoordinates N)} {g g₁ g₂ g₃ : ComplexCoordinates N → ComplexCoordinates 1}
theorem differentiableAt_of_isHolomorphicIn
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hg : IsHolomorphicIn O g) {b : ComplexCoordinates N} (hb : b ∈ O) : DifferentiableAt ℝ g b := by
  obtain ⟨L, hL⟩ := ((hH.1 N O hg.1).1 1 g hg).2.2.1 b hb
  exact hL.differentiableAt
theorem isHolomorphicIn_partialAlong
    (hD : YangMills.Construction.SeparatedFrame.HolomorphicDerivatives.Claim)
    (hg : IsHolomorphicIn O g) (v : ComplexCoordinates N) : IsHolomorphicIn O (partialAlong v g) :=
  (hD N 1 O g hg).1 v
theorem hasDerivAt_affineLine {a v : ComplexCoordinates N} {t : ℝ}
    (hd : DifferentiableAt ℝ g (a + t • v)) :
    HasDerivAt (fun s : ℝ => g (a + s • v) 0) (partialAlong v g (a + t • v) 0) t := by
  have h1 : HasDerivAt (fun s : ℝ => a + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add a
  have h2 : HasDerivAt (fun s : ℝ => g (a + s • v)) (fderiv ℝ g (a + t • v) v) t :=
    hd.hasFDerivAt.comp_hasDerivAt t h1
  exact (hasDerivAt_pi.1 h2) 0
theorem partialAlong_comm
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : YangMills.Construction.SeparatedFrame.HolomorphicDerivatives.Claim)
    (hg : IsHolomorphicIn O g) (u v : ComplexCoordinates N) {b : ComplexCoordinates N} (hb : b ∈ O) :
    partialAlong u (partialAlong v g) b = partialAlong v (partialAlong u g) b := by
  have key : ∀ u v : ComplexCoordinates N, secondDeriv g b u v = partialAlong u (partialAlong v g) b := by
    intro u v
    have hd : DifferentiableAt ℝ (partialAlong v g) b :=
      differentiableAt_of_isHolomorphicIn hH (isHolomorphicIn_partialAlong hD hg v) hb
    have h1 : HasDerivAt (fun s : ℝ => b + s • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add b
    have hd' : DifferentiableAt ℝ (partialAlong v g) (b + (0 : ℝ) • u) := by simpa using hd
    have hh : HasFDerivAt (partialAlong v g) (fderiv ℝ (partialAlong v g) (b + (0 : ℝ) • u))
        ((fun s : ℝ => b + s • u) 0) := hd'.hasFDerivAt
    have h2 : HasDerivAt ((partialAlong v g) ∘ fun s : ℝ => b + s • u)
        (fderiv ℝ (partialAlong v g) (b + (0 : ℝ) • u) u) 0 :=
      hh.comp_hasDerivAt (0 : ℝ) h1
    have h3 := h2.deriv
    simp only [zero_smul, add_zero] at h3
    exact h3
  have hs := ((hD N 1 O g hg).2 b hb).2.2 u v
  rw [← key, ← key, hs]
theorem partialAlong_congr (hO : IsOpen O) (v : ComplexCoordinates N) (h : ∀ w ∈ O, g₁ w = g₂ w)
    {b : ComplexCoordinates N} (hb : b ∈ O) : partialAlong v g₁ b = partialAlong v g₂ b := by
  have he : g₁ =ᶠ[𝓝 b] g₂ := by
    filter_upwards [hO.mem_nhds hb] with w hw using h w hw
  simp only [partialAlong, he.fderiv_eq]
theorem isHolomorphicIn_taylorCombination (h₁ : IsHolomorphicIn O g₁) (h₂ : IsHolomorphicIn O g₂)
    (h₃ : IsHolomorphicIn O g₃) :
    IsHolomorphicIn O (fun w => g₁ w - g₂ w + (1 / 2 : ℂ) • g₃ w) := by
  have hc : ContinuousOn (fun w => (1 / 2 : ℂ) • g₃ w) O := fun w hw => (h₃.2.1 w hw).const_smul (1 / 2 : ℂ)
  refine ⟨h₁.1, (h₁.2.1.sub h₂.2.1).add hc, fun a ha j => ?_⟩
  filter_upwards [h₁.2.2 a ha j, h₂.2.2 a ha j, h₃.2.2 a ha j] with ζ d₁ d₂ d₃
  exact (d₁.sub d₂).add (d₃.const_smul (1 / 2 : ℂ))
theorem partialAlong_taylorCombination
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (h₁ : IsHolomorphicIn O g₁) (h₂ : IsHolomorphicIn O g₂) (h₃ : IsHolomorphicIn O g₃)
    (v : ComplexCoordinates N) {b : ComplexCoordinates N} (hb : b ∈ O) :
    partialAlong v (fun w => g₁ w - g₂ w + (1 / 2 : ℂ) • g₃ w) b =
      partialAlong v g₁ b - partialAlong v g₂ b + (1 / 2 : ℂ) • partialAlong v g₃ b := by
  have d₁ := (differentiableAt_of_isHolomorphicIn hH h₁ hb).hasFDerivAt
  have d₂ := (differentiableAt_of_isHolomorphicIn hH h₂ hb).hasFDerivAt
  have d₃ := (differentiableAt_of_isHolomorphicIn hH h₃ hb).hasFDerivAt
  have hf := ((d₁.sub d₂).add (d₃.const_smul (1 / 2 : ℂ))).fderiv
  simp only [partialAlong]
  rw [show (fun w => g₁ w - g₂ w + (1 / 2 : ℂ) • g₃ w) = (g₁ - g₂) + (1 / 2 : ℂ) • g₃ from rfl, hf]
  rfl
end Holomorphic
def joinPoint (z : ℂ) (p : ComplexCoordinates 4) : ComplexCoordinates 5 := fun i => Fin.cases z p i
abbrev zDirection : ComplexCoordinates 5 := stdBasisVector 0
abbrev pDirectionOne : ComplexCoordinates 5 := stdBasisVector (Fin.succ (0 : Fin 4))
abbrev pDirectionTwo : ComplexCoordinates 5 := stdBasisVector (Fin.succ (1 : Fin 4))
theorem joinPoint_ofReal (z : ℝ) (p : ComplexCoordinates 4) :
    joinPoint (z : ℂ) p = joinPoint 0 p + z • zDirection := by
  funext i
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [joinPoint, stdBasisVector]
  · simp [joinPoint, stdBasisVector, Fin.succ_ne_zero]
theorem joinPoint_plane (z : ℂ) (s t : ℝ) :
    joinPoint z (toComplexVec (Pi.single 0 s + Pi.single 1 t)) =
      joinPoint z 0 + s • pDirectionOne + t • pDirectionTwo := by
  funext i
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [joinPoint, stdBasisVector]
  · have hm : ∀ (q : ComplexCoordinates 4) (w : ℂ), joinPoint w q m.succ = q m := fun _ _ => rfl
    simp only [Pi.add_apply, Pi.smul_apply, hm]
    fin_cases m <;> simp [stdBasisVector, toComplexVec]
theorem isHolomorphicIn_joinPoint (z : ℂ) {O : Set (ComplexCoordinates 4)} (hO : IsOpen O) :
    IsHolomorphicIn O (joinPoint z) := by
  refine ⟨hO, ?_, fun a _ j => Eventually.of_forall fun ζ => ?_⟩
  · refine Continuous.continuousOn (continuous_pi fun i => ?_)
    refine Fin.cases ?_ (fun m => ?_) i
    · simpa [joinPoint] using continuous_const
    · simpa [joinPoint] using continuous_apply m
  · refine differentiableAt_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun m => ?_) i
    · simp [joinPoint]
    · simp only [joinPoint, Fin.cases_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
theorem secondPartialAtZero_congr {g₁ g₂ : (Fin 4 → ℂ) → ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ p ∈ Metric.ball (0 : ComplexCoordinates 4) r, p ∈ realLocus 4 → g₁ p = g₂ p) :
    secondPartialAtZero g₁ 0 1 = secondPartialAtZero g₂ 0 1 := by
  unfold secondPartialAtZero
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with s hs
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
  have hs' : |s| < r := by simpa [Real.dist_eq] using hs
  have ht' : |t| < r := by simpa [Real.dist_eq] using ht
  refine h _ ?_ ?_
  · rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
    intro μ
    fin_cases μ <;> simp [toComplexVec, hs', ht', hr]
  · intro μ
    simp [toComplexVec]
theorem secondPartialAtZero_joinPoint
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : YangMills.Construction.SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates 5)} {g : ComplexCoordinates 5 → ComplexCoordinates 1}
    (hg : IsHolomorphicIn O g) {z : ℂ} (hb : joinPoint z 0 ∈ O) :
    secondPartialAtZero (fun p => g (joinPoint z p) 0) 0 1 =
      partialAlong pDirectionOne (partialAlong pDirectionTwo g) (joinPoint z 0) 0 := by
  have hcont : ∀ᶠ s : ℝ in 𝓝 0, joinPoint z 0 + s • pDirectionOne ∈ O := by
    have hc : Continuous (fun s : ℝ => joinPoint z 0 + s • pDirectionOne) := by fun_prop
    refine hc.continuousAt.eventually_mem ?_
    simpa using hg.1.mem_nhds hb
  have hinner : ∀ s : ℝ, joinPoint z 0 + s • pDirectionOne ∈ O →
      deriv (fun t : ℝ => g (joinPoint z (toComplexVec (Pi.single 0 s + Pi.single 1 t))) 0) 0 =
        partialAlong pDirectionTwo g (joinPoint z 0 + s • pDirectionOne) 0 := by
    intro s hs
    have hd : DifferentiableAt ℝ g ((joinPoint z 0 + s • pDirectionOne) + (0 : ℝ) • pDirectionTwo) := by
      simpa using differentiableAt_of_isHolomorphicIn hH hg hs
    have h := (hasDerivAt_affineLine hd).deriv
    simp only [zero_smul, add_zero] at h
    simpa only [joinPoint_plane] using h
  have heq : (fun s : ℝ => deriv (fun t : ℝ =>
      g (joinPoint z (toComplexVec (Pi.single 0 s + Pi.single 1 t))) 0) 0) =ᶠ[𝓝 0]
      (fun s : ℝ => partialAlong pDirectionTwo g (joinPoint z 0 + s • pDirectionOne) 0) :=
    hcont.mono hinner
  have hd : DifferentiableAt ℝ (partialAlong pDirectionTwo g)
      (joinPoint z 0 + (0 : ℝ) • pDirectionOne) := by
    simpa using differentiableAt_of_isHolomorphicIn hH (isHolomorphicIn_partialAlong hD hg pDirectionTwo) hb
  have houter := (hasDerivAt_affineLine hd).deriv
  simp only [zero_smul, add_zero] at houter
  unfold secondPartialAtZero
  exact heq.deriv_eq.trans houter
theorem hasDerivAt_firstCoord
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (ComplexCoordinates 5)} {g : ComplexCoordinates 5 → ComplexCoordinates 1}
    (hg : IsHolomorphicIn O g) {φ : ℝ → ℂ} {p : ComplexCoordinates 4} {U : Set ℝ} (hU : IsOpen U)
    (hUO : ∀ z ∈ U, joinPoint (z : ℂ) p ∈ O) (hφ : ∀ z ∈ U, φ z = g (joinPoint (z : ℂ) p) 0)
    {z : ℝ} (hz : z ∈ U) : HasDerivAt φ (partialAlong zDirection g (joinPoint (z : ℂ) p) 0) z := by
  have hd : DifferentiableAt ℝ g (joinPoint 0 p + z • zDirection) := by
    rw [← joinPoint_ofReal]
    exact differentiableAt_of_isHolomorphicIn hH hg (hUO z hz)
  have h := hasDerivAt_affineLine hd
  rw [← joinPoint_ofReal] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hz] with y hy
  rw [hφ y hy, joinPoint_ofReal]
theorem hasDerivAt_comp_mul {γ : ℝ → ℝ} (hγ : AnalyticOnNhd ℝ γ (Ioi 0)) {c z : ℝ} (hc : 0 < c)
    (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => (γ (c * y) : ℂ)) ((deriv γ (c * z) * c : ℝ) : ℂ) z := by
  have h1 : HasDerivAt γ (deriv γ (c * z)) (c * z) :=
    (hγ (c * z) (mul_pos hc hz)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => c * y) c z := by
    simpa using (hasDerivAt_id z).const_mul c
  exact (h1.comp z h2).ofReal_comp
theorem stripHalfWidth_pos
    (hN : YangMills.Construction.Tower.FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    0 < stripHalfWidth := by
  obtain ⟨-, -, δ, hδ, -, -, hpos, -⟩ := hN
  have hmem := stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨δ, hδ⟩)
  rw [Part.mem_unique hmem hδ]
  exact hpos.1
theorem min_le_massWidth {z : ℝ} (hz : 1 / 4 ≤ z) : min stripHalfWidth (1 / 10) ≤ massWidth z := by
  unfold massWidth
  refine min_le_min_left _ ?_
  have h : (1 / 2 : ℝ) ≤ Real.sqrt z := by
    rw [Real.le_sqrt' (by norm_num)]
    linarith
  linarith
theorem sharpMixedDerivative_holds
    (hF : YangMills.Construction.Tower.MassiveOpFunctions.LocallyHolomorphic.Claim)
    (hM : YangMills.Construction.Tower.MassiveOpFunctions.MixedPartialOfMassiveLogFn.Claim)
    (hA : YangMills.Construction.Tower.MassiveStiffnessFunctions.StiffnessAnalytic)
    (hH : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hD : YangMills.Construction.SeparatedFrame.HolomorphicDerivatives.Claim)
    (hN : YangMills.Construction.Tower.FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    SharpMixedDerivative := by
  intro L hL hS k hk
  have hδ : 0 < stripHalfWidth := stripHalfWidth_pos hN
  obtain ⟨O, ⟨w₀, hw₀, hz₀, hp₀⟩, H, hHol, hEq⟩ := hF L hS k hk 1 one_pos
  have hOopen : IsOpen O := hHol.1
  have hw₀' : w₀ = joinPoint ((1 : ℝ) : ℂ) 0 := by
    funext i
    refine Fin.cases ?_ (fun m => ?_) i
    · simpa [joinPoint] using hz₀
    · simpa [joinPoint] using hp₀ m
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hOopen w₀ hw₀
  set r : ℝ := min ε (min stripHalfWidth (1 / 10)) with hr_def
  have hr : 0 < r := lt_min hε (lt_min hδ (by norm_num))
  have hrε : r ≤ ε := min_le_left _ _
  have hrw : r ≤ min stripHalfWidth (1 / 10) := min_le_right _ _
  have hrδ : r ≤ stripHalfWidth := hrw.trans (min_le_left _ _)
  have hrt : r ≤ 1 / 10 := hrw.trans (min_le_right _ _)
  have hin : ∀ (z : ℝ) (p : ComplexCoordinates 4), z ∈ Metric.ball (1 : ℝ) r →
      p ∈ Metric.ball (0 : ComplexCoordinates 4) r → joinPoint (z : ℂ) p ∈ O := by
    intro z p hz hp
    apply hball
    rw [hw₀', Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
    have hz' : |z - 1| < r := by simpa [Real.dist_eq] using hz
    have hp' := (pi_norm_lt_iff hr).1 (mem_ball_zero_iff.1 hp)
    intro i
    refine Fin.cases ?_ (fun m => ?_) i
    · have h1 : ‖((z : ℂ) - ((1 : ℝ) : ℂ))‖ = |z - 1| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      change ‖(z : ℂ) - ((1 : ℝ) : ℂ)‖ < ε
      rw [h1]
      exact lt_of_lt_of_le hz' hrε
    · simpa [joinPoint] using lt_of_lt_of_le (hp' m) hrε
  have hagree : ∀ (z : ℝ) (p : ComplexCoordinates 4), z ∈ Metric.ball (1 : ℝ) r →
      p ∈ Metric.ball (0 : ComplexCoordinates 4) r → p ∈ realLocus 4 →
      massiveLogFn L k p 0 1 z = asLine H (joinPoint (z : ℂ) p) 0 := by
    intro z p hz hp hreal
    have hz' : |z - 1| < r := by simpa [Real.dist_eq] using hz
    have hz1 : 9 / 10 ≤ z := by
      have := (abs_lt.1 hz').1
      linarith
    have hp' := (pi_norm_lt_iff hr).1 (mem_ball_zero_iff.1 hp)
    have hre : (joinPoint (z : ℂ) p 0).re = z := by simp [joinPoint]
    have hreal' : joinPoint (z : ℂ) p ∈ realLocus 5 := by
      intro i
      refine Fin.cases ?_ (fun m => ?_) i
      · simp [joinPoint]
      · simpa [joinPoint] using hreal m
    have hw := hEq (joinPoint (z : ℂ) p) (hin z p hz hp) hreal' (by rw [hre]; linarith) (by
      intro μ
      rw [hre]
      have hμ : ‖joinPoint (z : ℂ) p μ.succ‖ = ‖p μ‖ := rfl
      rw [hμ]
      exact lt_of_lt_of_le (hp' μ) (hrw.trans (min_le_massWidth (by linarith))))
    rw [hre] at hw
    exact hw.symm
  set f : ComplexCoordinates 5 → ComplexCoordinates 1 := asLine H with hf_def
  have hf : IsHolomorphicIn O f := hHol
  set f₁ := partialAlong zDirection f with hf₁_def
  have hf₁ : IsHolomorphicIn O f₁ := isHolomorphicIn_partialAlong hD hf _
  set f₂ := partialAlong zDirection f₁ with hf₂_def
  have hf₂ : IsHolomorphicIn O f₂ := isHolomorphicIn_partialAlong hD hf₁ _
  set g : ComplexCoordinates 5 → ComplexCoordinates 1 := fun w => f w - f₁ w + (1 / 2 : ℂ) • f₂ w with hg_def
  have hg : IsHolomorphicIn O g := isHolomorphicIn_taylorCombination hf hf₁ hf₂
  set U : Set ℝ := Metric.ball (1 : ℝ) r with hU_def
  have hUopen : IsOpen U := Metric.isOpen_ball
  have h1U : (1 : ℝ) ∈ U := Metric.mem_ball_self hr
  have hUpos : ∀ z ∈ U, 0 < z := by
    intro z hz
    have hz' : |z - 1| < r := by simpa [hU_def, Real.dist_eq] using hz
    have := (abs_lt.1 hz').1
    linarith
  have hb0 : (0 : ComplexCoordinates 4) ∈ Metric.ball (0 : ComplexCoordinates 4) r :=
    Metric.mem_ball_self hr
  have hsharp : ∀ p ∈ Metric.ball (0 : ComplexCoordinates 4) r, p ∈ realLocus 4 →
      massiveLogFnSharp L k p 0 1 = g (joinPoint ((1 : ℝ) : ℂ) p) 0 := by
    intro p hp hreal
    have hd₁ : ∀ z ∈ U, deriv (massiveLogFn L k p 0 1) z = f₁ (joinPoint (z : ℂ) p) 0 := fun z hz =>
      (hasDerivAt_firstCoord hH hf hUopen (fun y hy => hin y p hy hp)
        (fun y hy => hagree y p hy hp hreal) hz).deriv
    have hd₂ : deriv (deriv (massiveLogFn L k p 0 1)) 1 = f₂ (joinPoint ((1 : ℝ) : ℂ) p) 0 :=
      (hasDerivAt_firstCoord hH hf₁ hUopen (fun y hy => hin y p hy hp) hd₁ h1U).deriv
    have h0 := hagree 1 p h1U hp hreal
    simp only [massiveLogFnSharp, hd₂, hd₁ 1 h1U, h0, hg_def, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
  set M := partialAlong pDirectionOne (partialAlong pDirectionTwo f) with hM_def
  have hMhol : IsHolomorphicIn O M :=
    isHolomorphicIn_partialAlong hD (isHolomorphicIn_partialAlong hD hf _) _
  have hM₁ : IsHolomorphicIn O (partialAlong zDirection M) := isHolomorphicIn_partialAlong hD hMhol _
  have hswap : ∀ {h : ComplexCoordinates 5 → ComplexCoordinates 1}, IsHolomorphicIn O h →
      ∀ w ∈ O, partialAlong pDirectionOne (partialAlong pDirectionTwo (partialAlong zDirection h)) w =
        partialAlong zDirection (partialAlong pDirectionOne (partialAlong pDirectionTwo h)) w := by
    intro h hh w hw
    rw [partialAlong_congr hOopen pDirectionOne (fun u hu => partialAlong_comm hH hD hh pDirectionTwo zDirection hu) hw]
    exact partialAlong_comm hH hD (isHolomorphicIn_partialAlong hD hh pDirectionTwo) pDirectionOne zDirection hw
  have hbO : joinPoint ((1 : ℝ) : ℂ) 0 ∈ O := hin 1 0 h1U hb0
  have hcomb : partialAlong pDirectionOne (partialAlong pDirectionTwo g) (joinPoint ((1 : ℝ) : ℂ) 0) =
      M (joinPoint ((1 : ℝ) : ℂ) 0) - partialAlong zDirection M (joinPoint ((1 : ℝ) : ℂ) 0) +
        (1 / 2 : ℂ) • partialAlong zDirection (partialAlong zDirection M) (joinPoint ((1 : ℝ) : ℂ) 0) := by
    have ha₀ := isHolomorphicIn_partialAlong hD hf pDirectionTwo
    have ha₁ := isHolomorphicIn_partialAlong hD hf₁ pDirectionTwo
    have ha₂ := isHolomorphicIn_partialAlong hD hf₂ pDirectionTwo
    rw [partialAlong_congr hOopen pDirectionOne
      (fun u hu => partialAlong_taylorCombination hH hf hf₁ hf₂ pDirectionTwo hu) hbO,
      partialAlong_taylorCombination hH ha₀ ha₁ ha₂ pDirectionOne hbO, hswap hf _ hbO, hswap hf₁ _ hbO,
      partialAlong_congr hOopen zDirection (fun u hu => hswap hf u hu) hbO]
  have hmixed : ∀ z ∈ U, -((massiveStiffness hL (finestMesh L k ^ 2 * z) : ℝ) : ℂ) =
      M (joinPoint (z : ℂ) 0) 0 := by
    intro z hz
    have hzO := hin z 0 hz hb0
    have e : secondPartialAtZero (fun p => f (joinPoint (z : ℂ) p) 0) 0 1 = M (joinPoint (z : ℂ) 0) 0 :=
      secondPartialAtZero_joinPoint hH hD hf hzO
    rw [← e, ← hM L hL hS k hk z (hUpos z hz), neg_neg]
    exact secondPartialAtZero_congr hr fun p hp hreal => hagree z p hz hp hreal
  have hη : 0 < finestMesh L k ^ 2 := by
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have : 0 < finestMesh L k := zpow_pos hLpos _
    positivity
  set c : ℝ := finestMesh L k ^ 2 with hc_def
  have hβ : AnalyticOnNhd ℝ (massiveStiffness hL) (Ioi 0) := hA L hL hS
  have hβ' : AnalyticOnNhd ℝ (deriv (massiveStiffness hL)) (Ioi 0) := hβ.deriv
  have hfirst : ∀ z ∈ U, -((deriv (massiveStiffness hL) (c * z) * c : ℝ) : ℂ) =
      partialAlong zDirection M (joinPoint (z : ℂ) 0) 0 := by
    intro z hz
    exact ((hasDerivAt_comp_mul hβ hη (hUpos z hz)).neg).unique
      (hasDerivAt_firstCoord hH hMhol hUopen (fun y hy => hin y 0 hy hb0) hmixed hz)
  have hsecond : -(((deriv (deriv (massiveStiffness hL)) (c * 1) * c : ℝ) : ℂ) * (c : ℂ)) =
      partialAlong zDirection (partialAlong zDirection M) (joinPoint ((1 : ℝ) : ℂ) 0) 0 := by
    have h := ((hasDerivAt_comp_mul hβ' hη one_pos).mul_const (c : ℂ)).neg
    have hphi : ∀ z ∈ U, -(((deriv (massiveStiffness hL) (c * z) : ℝ) : ℂ) * (c : ℂ)) =
        partialAlong zDirection M (joinPoint (z : ℂ) 0) 0 := by
      intro z hz
      rw [← hfirst z hz]
      push_cast
      ring
    exact h.unique (hasDerivAt_firstCoord hH hM₁ hUopen (fun y hy => hin y 0 hy hb0) hphi h1U)
  refine ⟨⟨Metric.ball 0 r, hb0, ?_, fun p => g (joinPoint ((1 : ℝ) : ℂ) p) 0, ?_,
    fun w hw hreal => (hsharp w hw hreal).symm⟩, ?_⟩
  · intro p hp μ
    exact ((pi_norm_lt_iff hr).1 (mem_ball_zero_iff.1 hp) μ).le.trans hrδ
  · have hcomp : IsHolomorphicIn (Metric.ball (0 : ComplexCoordinates 4) r)
        (g ∘ joinPoint ((1 : ℝ) : ℂ)) :=
      ((hH.1 5 O hOopen).1 1 g hg).2.2.2.1 4 _ (joinPoint ((1 : ℝ) : ℂ))
        (isHolomorphicIn_joinPoint _ Metric.isOpen_ball) (fun p hp => hin 1 p h1U hp)
    have hline : asLine (fun p => g (joinPoint ((1 : ℝ) : ℂ) p) 0) = g ∘ joinPoint ((1 : ℝ) : ℂ) := by
      funext p i
      rw [Subsingleton.elim i 0]
      rfl
    change IsHolomorphicIn _ (asLine _)
    rw [hline]
    exact hcomp
  · have e₁ : secondPartialAtZero (fun p => massiveLogFnSharp L k p 0 1) 0 1 =
        secondPartialAtZero (fun p => g (joinPoint ((1 : ℝ) : ℂ) p) 0) 0 1 :=
      secondPartialAtZero_congr hr hsharp
    have e₂ := secondPartialAtZero_joinPoint hH hD hg hbO
    have hc4 : finestMesh L k ^ 4 = c * c := by
      rw [hc_def]
      ring
    rw [e₁, e₂, hcomb]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hmixed 1 h1U, ← hfirst 1 h1U, ← hsecond]
    simp only [mul_one, massiveStiffnessDeriv, massiveStiffnessDeriv2, hc4]
    push_cast
    ring
end YangMills.Construction.Tower.MassiveOpFunctions.SharpLogFn
end
