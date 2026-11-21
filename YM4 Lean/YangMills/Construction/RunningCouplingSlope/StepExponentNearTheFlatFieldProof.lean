import YangMills.Construction.RunningCouplingSlope.RestOfTheCurveHasJetsProof
import YangMills.Construction.RunningCouplingSlope.StepExponentNearTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion Nat
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields YangMills.Construction.StepSettings YangMills.Construction.LaplaceAsymptotics
namespace YangMills.Construction.RunningCouplingSlope
namespace StepExponentNearTrivialLemmas
section Calculus
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
private theorem iteratedFDeriv_sub_const_of_pos (g : G → H) (κ : H) {i : ℕ} (hi : 1 ≤ i) (x : G) :
    iteratedFDeriv ℝ i (fun y => g y - κ) x = iteratedFDeriv ℝ i g x := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have e : (fun y => fderiv ℝ (fun y => g y - κ) y) = fun y => fderiv ℝ g y := by
    funext y
    exact fderiv_sub_const κ
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, e]
private theorem norm_iteratedFDeriv_comp_le_of_pos {g : G → H} {f : E → G} {x : E} {N : ℕ}
    (hg : ContDiffAt ℝ N g (f x))
    (hf : ContDiffAt ℝ N f x) {C D : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) (hN : 1 ≤ N) :
    ‖iteratedFDeriv ℝ N (g ∘ f) x‖ ≤ N ! * C * D ^ N := by
  set g' : G → H := fun y => g y - g (f x) with hg'd
  have hg' : ContDiffAt ℝ N g' (f x) := hg.sub contDiffAt_const
  obtain ⟨u, hu, hc⟩ := hg'.contDiffOn (m := N) le_rfl (by simp)
  obtain ⟨U, hUu, hUo, hxU⟩ := mem_nhds_iff.1 hu
  have hcU : ContDiffOn ℝ N g' U := hc.mono hUu
  obtain ⟨v, hv, hd⟩ := hf.contDiffOn (m := N) le_rfl (by simp)
  have hpre : f ⁻¹' U ∈ 𝓝 x := hf.continuousAt (hUo.mem_nhds hxU)
  obtain ⟨S, hS, hSo, hxS⟩ := mem_nhds_iff.1 (Filter.inter_mem hv hpre)
  have hdS : ContDiffOn ℝ N f S := hd.mono fun z hz => (hS hz).1
  have hmap : Set.MapsTo f S U := fun z hz => (hS hz).2
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := N) (N := N) hcU hdS le_rfl
    hUo.uniqueDiffOn hSo.uniqueDiffOn hmap hxS (C := C) (D := D)
    (by
      intro i hi
      rw [iteratedFDerivWithin_of_isOpen i hUo hxU]
      rcases Nat.eq_zero_or_pos i with rfl | h
      · simpa [hg'd] using hC0
      · rw [hg'd, iteratedFDeriv_sub_const_of_pos g _ h]
        exact hC i h hi)
    (by
      intro i h1 h2
      rw [iteratedFDerivWithin_of_isOpen i hSo hxS]
      exact hD i h1 h2)
  rw [iteratedFDerivWithin_of_isOpen N hSo hxS] at key
  have e : iteratedFDeriv ℝ N (g' ∘ f) x = iteratedFDeriv ℝ N (g ∘ f) x := by
    have e' : (g' ∘ f) = fun y => (g ∘ f) y - g (f x) := rfl
    rw [e']
    exact iteratedFDeriv_sub_const_of_pos _ _ hN x
  rwa [e] at key
private theorem norm_iteratedFDeriv_clm_le_one (A : E →L[ℝ] G) (hA : ‖A‖ ≤ 1) (x : E) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i A x‖ ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rcases m with _ | m
  · rw [norm_iteratedFDeriv_one, A.fderiv]
    exact hA
  · have e : fderiv ℝ (A : E → G) = fun _ => A := by
      funext y
      exact A.fderiv
    rw [← norm_iteratedFDeriv_fderiv, e, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m) A]
    simp
private theorem iteratedFDeriv_comp_clm {n : ℕ} {f : E → H} (A : G →L[ℝ] E) {x : G}
    (hf : ContDiffAt ℝ n f (A x)) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv ℝ i (f ∘ A) x =
      (iteratedFDeriv ℝ i f (A x)).compContinuousLinearMap fun _ => A := by apply _root_.YangMills.SharedProofs.p40845 <;> assumption
private theorem norm_iteratedFDeriv_comp_clm_le {n : ℕ} {f : E → H} (A : G →L[ℝ] E) (hA : ‖A‖ ≤ 1) {x : G}
    (hf : ContDiffAt ℝ n f (A x)) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv ℝ i (f ∘ A) x‖ ≤ ‖iteratedFDeriv ℝ i f (A x)‖ := by
  rw [iteratedFDeriv_comp_clm A hf hi]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h : ∏ _j : Fin i, ‖A‖ ≤ 1 := by
    rw [Finset.prod_const]
    exact pow_le_one₀ (norm_nonneg _) hA
  exact mul_le_of_le_one_right (norm_nonneg _) h
end Calculus
section Composite
variable {P Z : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
private theorem factorial_le_of_le_five {j : ℕ} (hj : j ≤ 5) : ((j ! : ℕ) : ℝ) ≤ 120 := by
  have h := Nat.factorial_le hj
  have e : (5 ! : ℕ) = 120 := rfl
  rw [e] at h
  exact_mod_cast h
private theorem shiftedGraph_jets (Γ : P → Z) (A : (P × Z) →L[ℝ] (Z × P)) (hA : ‖A‖ ≤ 1) (q₀ : P × Z)
    (hΓ : ContDiffAt ℝ 5 Γ q₀.1) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, 1 ≤ i → i ≤ 5 → ‖iteratedFDeriv ℝ i Γ q₀.1‖ ≤ M) :
    ContDiffAt ℝ 5 (fun q : P × Z => ((Γ q.1, 0) : Z × P) + A q) q₀ ∧
    ∀ i, 1 ≤ i → i ≤ 5 →
      ‖iteratedFDeriv ℝ i (fun q : P × Z => ((Γ q.1, 0) : Z × P) + A q) q₀‖ ≤ (121 * (120 * M + 1)) ^ i := by
  set fstL := ContinuousLinearMap.fst ℝ P Z with hfstL
  set inlL := ContinuousLinearMap.inl ℝ Z P with hinlL
  have hfst : ‖fstL‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
    simp only [hfstL, ContinuousLinearMap.coe_fst', one_mul]
    exact norm_fst_le q
  have hinl : ‖inlL‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    simp [hinlL, Prod.norm_def]
  have h1 : ContDiffAt ℝ 5 (Γ ∘ fstL) q₀ := ContDiffAt.comp q₀ hΓ fstL.contDiff.contDiffAt
  have h2 : ContDiffAt ℝ 5 (inlL ∘ (Γ ∘ fstL)) q₀ := ContDiffAt.comp q₀ inlL.contDiff.contDiffAt h1
  have hA5 : ContDiffAt ℝ 5 A q₀ := A.contDiff.contDiffAt
  have e : (fun q : P × Z => ((Γ q.1, 0) : Z × P) + A q) = (inlL ∘ (Γ ∘ fstL)) + A := by
    funext q
    rfl
  have b1 : ∀ i, 1 ≤ i → i ≤ 5 → ‖iteratedFDeriv ℝ i (Γ ∘ fstL) q₀‖ ≤ 120 * M + 1 := by
    intro i hi hi5
    have hc : ContDiffAt ℝ i Γ (fstL q₀) := hΓ.of_le (by exact_mod_cast hi5)
    have hl := norm_iteratedFDeriv_comp_clm_le fstL hfst hc le_rfl
    have := hM i hi hi5
    have e2 : fstL q₀ = q₀.1 := rfl
    rw [e2] at hl
    linarith
  have b2 : ∀ i, 1 ≤ i → i ≤ 5 → ‖iteratedFDeriv ℝ i (inlL ∘ (Γ ∘ fstL)) q₀‖ ≤ 120 * (120 * M + 1) ^ i := by
    intro i hi hi5
    have hi5' : (i : WithTop ℕ∞) ≤ 5 := by exact_mod_cast hi5
    have hD1 : 1 ≤ 120 * M + 1 := by linarith
    have key := norm_iteratedFDeriv_comp_le_of_pos (g := inlL) (f := Γ ∘ fstL) (x := q₀) (N := i) (C := 1)
      (D := 120 * M + 1)
      inlL.contDiff.contDiffAt (h1.of_le hi5') zero_le_one
      (fun l hl _ => norm_iteratedFDeriv_clm_le_one inlL hinl _ hl)
      (fun l hl hli => (b1 l hl (hli.trans hi5)).trans (le_self_pow₀ hD1 (by omega))) hi
    refine key.trans ?_
    have h3 := factorial_le_of_le_five hi5
    have h4 : 0 ≤ (120 * M + 1) ^ i := by positivity
    nlinarith
  refine ⟨by rw [e]; exact h2.add hA5, fun i hi hi5 => ?_⟩
  have hi5' : (i : WithTop ℕ∞) ≤ 5 := by exact_mod_cast hi5
  rw [e, iteratedFDeriv_add_apply (h2.of_le hi5') (hA5.of_le hi5')]
  refine (norm_add_le _ _).trans ?_
  have h3 := b2 i hi hi5
  have h4 := norm_iteratedFDeriv_clm_le_one A hA q₀ hi
  have hU : (1 : ℝ) ≤ (120 * M + 1) ^ i := one_le_pow₀ (by linarith)
  have h5 : (121 : ℝ) ≤ 121 ^ i := le_self_pow₀ (by norm_num) (by omega)
  rw [mul_pow]
  nlinarith
private theorem shiftedDifference_jets (Γ : P → Z) (Sh : Z × P → ℝ) (η : Z) (hΓ0 : Γ 0 = 0)
    (hΓ : ContDiffAt ℝ 5 Γ 0) {M₁ M₂ : ℝ} (h1 : 0 ≤ M₁) (h2 : 0 ≤ M₂)
    (hM₁ : ∀ i, 1 ≤ i → i ≤ 5 → ‖iteratedFDeriv ℝ i Γ 0‖ ≤ M₁)
    (hS : ContDiffAt ℝ 5 Sh (η, 0)) (hS0 : ContDiffAt ℝ 5 Sh (0, 0))
    (hB : ∀ i, 1 ≤ i → i ≤ 5 → ‖iteratedFDeriv ℝ i Sh (η, 0)‖ ≤ M₂)
    (hB0 : ∀ i, 1 ≤ i → i ≤ 5 → ‖iteratedFDeriv ℝ i Sh (0, 0)‖ ≤ M₂) :
    ContDiffAt ℝ 5 (fun q : P × Z => Sh (Γ q.1 + q.2, q.1) - Sh (Γ q.1, q.1)) (0, η) ∧
    ∀ j, 1 ≤ j → j ≤ 5 →
      ‖iteratedFDeriv ℝ j (fun q : P × Z => Sh (Γ q.1 + q.2, q.1) - Sh (Γ q.1, q.1)) (0, η)‖ ≤
        240 * M₂ * (121 * (120 * M₁ + 1)) ^ 5 := by
  set L : (P × Z) →L[ℝ] (Z × P) := (ContinuousLinearMap.snd ℝ P Z).prod (ContinuousLinearMap.fst ℝ P Z) with hL
  set L₀ : (P × Z) →L[ℝ] (Z × P) := (0 : (P × Z) →L[ℝ] Z).prod (ContinuousLinearMap.fst ℝ P Z) with hL₀
  have nL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
    simp [hL, Prod.norm_def, max_comm]
  have nL₀ : ‖L₀‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
    simp [hL₀, Prod.norm_def]
  set f : P × Z → Z × P := fun q => ((Γ q.1, 0) : Z × P) + L q with hf
  set f₀ : P × Z → Z × P := fun q => ((Γ q.1, 0) : Z × P) + L₀ q with hf₀
  obtain ⟨cf, jf⟩ := shiftedGraph_jets Γ L nL (0, η) hΓ h1 hM₁
  obtain ⟨cf₀, jf₀⟩ := shiftedGraph_jets Γ L₀ nL₀ (0, η) hΓ h1 hM₁
  have ef : f (0, η) = (η, 0) := by
    simp [hf, hL, hΓ0]
  have ef₀ : f₀ (0, η) = (0, 0) := by
    simp [hf₀, hL₀, hΓ0]
  have hS' : ContDiffAt ℝ 5 Sh (f (0, η)) := by rw [ef]; exact hS
  have hS0' : ContDiffAt ℝ 5 Sh (f₀ (0, η)) := by rw [ef₀]; exact hS0
  have c1 : ContDiffAt ℝ 5 (Sh ∘ f) (0, η) := ContDiffAt.comp _ hS' cf
  have c2 : ContDiffAt ℝ 5 (Sh ∘ f₀) (0, η) := ContDiffAt.comp _ hS0' cf₀
  have e : (fun q : P × Z => Sh (Γ q.1 + q.2, q.1) - Sh (Γ q.1, q.1)) = (Sh ∘ f) - (Sh ∘ f₀) := by
    funext q
    simp [hf, hf₀, hL, hL₀]
  set D : ℝ := 121 * (120 * M₁ + 1) with hD
  have hD1 : 1 ≤ D := by rw [hD]; nlinarith
  have bound : ∀ (g : P × Z → Z × P), ContDiffAt ℝ 5 g (0, η) → ContDiffAt ℝ 5 Sh (g (0, η)) →
      (∀ i, 1 ≤ i → i ≤ 5 → ‖iteratedFDeriv ℝ i Sh (g (0, η))‖ ≤ M₂) →
      (∀ i, 1 ≤ i → i ≤ 5 → ‖iteratedFDeriv ℝ i g (0, η)‖ ≤ D ^ i) →
      ∀ j, 1 ≤ j → j ≤ 5 → ‖iteratedFDeriv ℝ j (Sh ∘ g) (0, η)‖ ≤ 120 * M₂ * D ^ 5 := by
    intro g cg cs bs bg j hj hj5
    have hj5' : (j : WithTop ℕ∞) ≤ 5 := by exact_mod_cast hj5
    have key := norm_iteratedFDeriv_comp_le_of_pos (g := Sh) (f := g) (x := ((0 : P), η)) (N := j) (C := M₂)
      (D := D) (cs.of_le hj5')
      (cg.of_le hj5') h2 (fun i h h' => bs i h (h'.trans hj5)) (fun i h h' => bg i h (h'.trans hj5)) hj
    refine key.trans ?_
    have h3 := factorial_le_of_le_five hj5
    have h4 : D ^ j ≤ D ^ 5 := pow_le_pow_right₀ hD1 hj5
    have h5 : 0 ≤ D ^ j := by positivity
    calc (j ! : ℝ) * M₂ * D ^ j ≤ 120 * M₂ * D ^ j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 h2) h5
      _ ≤ 120 * M₂ * D ^ 5 := mul_le_mul_of_nonneg_left h4 (by positivity)
  refine ⟨by rw [e]; exact c1.sub c2, fun j hj hj5 => ?_⟩
  have hj5' : (j : WithTop ℕ∞) ≤ 5 := by exact_mod_cast hj5
  rw [e, iteratedFDeriv_sub_apply (c1.of_le hj5') (c2.of_le hj5')]
  refine (norm_sub_le _ _).trans ?_
  have b1 := bound f cf hS' (by rw [ef]; exact hB) jf j hj hj5
  have b2 := bound f₀ cf₀ hS0' (by rw [ef₀]; exact hB0) jf₀ j hj hj5
  linarith
end Composite
section Scaled
variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
private theorem admissibleFamily_comp_scale {ρ lam K : ℝ} {Q B : (Fin k → ℝ) × BondField ι → ℝ}
    (h : IsAdmissibleExponentFamily ρ lam K Q B) (s : Fin k → ℝ) (hs : ∀ l, |s l| ≤ 1) :
    IsAdmissibleExponentFamily ρ lam K (fun q => Q (s * q.1, q.2)) (fun q => B (s * q.1, q.2)) := by
  set Sc : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun l => s l • ContinuousLinearMap.proj l with hSc
  set A : ((Fin k → ℝ) × BondField ι) →L[ℝ] ((Fin k → ℝ) × BondField ι) :=
    (Sc.comp (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _) with hA
  have eA : ∀ q, A q = (s * q.1, q.2) := fun q => by
    refine Prod.ext ?_ rfl
    funext l
    simp [hA, hSc]
  have nA : ‖A‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
    rw [eA, one_mul, Prod.norm_def, Prod.norm_def]
    refine max_le_max ?_ le_rfl
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l => ?_
    show ‖(s * q.1) l‖ ≤ ‖q.1‖
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hs l)).trans (norm_le_pi_norm q.1 l)
  have e0 : ∀ η : BondField ι, A ((0 : Fin k → ℝ), η) = (0, η) := fun η => by
    rw [eA]
    simp
  have eQ : (fun q => Q (s * q.1, q.2)) = Q ∘ A := by
    funext q
    simp only [Function.comp, eA]
  have eB : (fun q => B (s * q.1, q.2)) = B ∘ A := by
    funext q
    simp only [Function.comp, eA]
  refine
    { contDiff_Q := fun η hη => ?_
      contDiff_B := fun η hη => ?_
      value_zero := fun τ => ?_
      critical_zero := ?_
      hessian_lower := fun η hη v => ?_
      deriv_bound_Q := fun η hη j h2 h5 => ?_
      deriv_bound_B := fun η hη j h1 h3 => ?_ }
  · rw [eQ]
    have hc : ContDiffAt ℝ 5 Q (A (0, η)) := by rw [e0]; exact h.contDiff_Q η hη
    exact ContDiffAt.comp _ hc A.contDiff.contDiffAt
  · rw [eB]
    have hc : ContDiffAt ℝ 3 B (A (0, η)) := by rw [e0]; exact h.contDiff_B η hη
    exact ContDiffAt.comp _ hc A.contDiff.contDiffAt
  · exact h.value_zero _
  · have ht : Filter.Tendsto (fun τ : Fin k → ℝ => s * τ) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous fun τ : Fin k → ℝ => s * τ := continuous_const.mul continuous_id
      have := hcont.tendsto (0 : Fin k → ℝ)
      simpa using this
    exact ht.eventually h.critical_zero
  · have e : (fun ζ => (fun q : (Fin k → ℝ) × BondField ι => Q (s * q.1, q.2)) (0, ζ)) =
        fun ζ => Q (0, ζ) := by
      funext ζ
      simp
    rw [e]
    exact h.hessian_lower η hη v
  · have hc : ContDiffAt ℝ (j : ℕ) Q (A (0, η)) := by
      rw [e0]
      exact (h.contDiff_Q η hη).of_le (by exact_mod_cast h5)
    rw [eQ]
    refine (norm_iteratedFDeriv_comp_clm_le A nA hc le_rfl).trans ?_
    rw [e0]
    exact h.deriv_bound_Q η hη j h2 h5
  · have hc : ContDiffAt ℝ (j : ℕ) B (A (0, η)) := by
      rw [e0]
      exact (h.contDiff_B η hη).of_le (by exact_mod_cast h3)
    rw [eB]
    refine (norm_iteratedFDeriv_comp_clm_le A nA hc le_rfl).trans ?_
    rw [e0]
    exact h.deriv_bound_B η hη j h1 h3
end Scaled
section Curve
variable {k : ℕ} (R : StepSetup) (n : ℕ) (c : Fin k → TorusBond n)
private theorem toImaginary_imaginaryToEuclidean (v : imaginaryQuaternions) :
    toImaginary (imaginaryToEuclidean v) = v := by apply _root_.YangMills.SharedProofs.p66610 <;> assumption
private theorem toImaginary_add (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
private theorem minimizingBondCoordinate_of_not_mem {F : BlockFrame} (a ρ : ℝ) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4)
    (hb : b ∉ chordBonds S) : minimizingBondCoordinate a ρ S b V = 0 := by apply _root_.YangMills.SharedProofs.p604 <;> assumption
private theorem coordsAboveFrame_eq (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (η : StepVariable (finiteCells (torusFrame R.params.side R.depth n))) :
    coordsAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c X τ) η =
      stepCoordinates (minimizerCoordinatesAlong R n c X τ + η) := by
  funext x i
  unfold coordsAboveFrame ColdStepAtMirrorFrames.stepFrame
  simp only [if_true]
  by_cases hb : (x, i) ∈ chordBonds (finiteCells (torusFrame R.params.side R.depth n))
  · unfold stepCoordinates
    rw [dif_pos hb, dif_pos hb]
    simp only [Pi.add_apply, minimizerCoordinatesAlong]
    rw [toImaginary_add, toImaginary_imaginaryToEuclidean]
  · unfold stepCoordinates
    rw [dif_neg hb, dif_neg hb, minimizingBondCoordinate_of_not_mem _ _ _ _ _ hb, add_zero]
private theorem chartEnergyAlongCurve_eq (X : Fin k → imaginaryQuaternions) :
    chartEnergyAlongCurve R n c X = fun q =>
      chartedEnergyAlong R n c X (minimizerCoordinatesAlong R n c X q.1 + q.2, q.1) -
        chartedEnergyAlong R n c X (minimizerCoordinatesAlong R n c X q.1, q.1) := by
  funext q
  unfold chartEnergyAlongCurve ReferenceDensity.chartedEnergyAtMinimizer chartedEnergyAlong
  rw [coordsAboveFrame_eq, coordsAboveFrame_eq, add_zero]
private theorem perturbedTop_scale {X X' : Fin k → imaginaryQuaternions} {s : Fin k → ℝ}
    (h : ∀ l, X l = s l • X' l) (τ : Fin k → ℝ) :
    perturbedTop R n c X τ = perturbedTop R n c X' (s * τ) := by
  unfold perturbedTop
  have e : perturb c X τ (trivialField n) = perturb c X' (s * τ) (trivialField n) := by
    funext x i
    have e' : ∀ l, τ l • X l = (s * τ) l • X' l := fun l => by
      rw [h l, smul_smul, Pi.mul_apply, mul_comm]
    simp only [perturb, e']
  rw [e]
private theorem chartEnergyAlongCurve_scale {X X' : Fin k → imaginaryQuaternions} {s : Fin k → ℝ}
    (h : ∀ l, X l = s l • X' l) :
    chartEnergyAlongCurve R n c X = fun q => chartEnergyAlongCurve R n c X' (s * q.1, q.2) := by
  funext q
  unfold chartEnergyAlongCurve
  rw [perturbedTop_scale R n c h]
private theorem exponentRemainderAlongCurve_scale {X X' : Fin k → imaginaryQuaternions} {s : Fin k → ℝ}
    (h : ∀ l, X l = s l • X' l) :
    exponentRemainderAlongCurve R n c X = fun q => exponentRemainderAlongCurve R n c X' (s * q.1, q.2) := by
  funext q
  unfold exponentRemainderAlongCurve
  rw [perturbedTop_scale R n c h, chartEnergyAlongCurve_scale R n c h]
end Curve
private theorem norm_imaginaryUnit_zero : ‖imaginaryUnit 0‖ = 1 := by
  have h1 : ‖imaginaryUnit 0‖ ^ 2 = 1 := by
    have e : ‖imaginaryUnit 0‖ = ‖((imaginaryUnit 0 : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
    rw [e, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp [imaginaryUnit]
  have h2 := norm_nonneg (imaginaryUnit 0)
  nlinarith
private theorem exists_unit_scaling {k : ℕ} (X : Fin k → imaginaryQuaternions) (hX : ∀ l, ‖X l‖ ≤ 1) :
    ∃ (X' : Fin k → imaginaryQuaternions) (s : Fin k → ℝ),
      AreUnitVectors X' ∧ (∀ l, |s l| ≤ 1) ∧ ∀ l, X l = s l • X' l := by
  classical
  refine ⟨fun l => if X l = 0 then imaginaryUnit 0 else ‖X l‖⁻¹ • X l, fun l => ‖X l‖,
    fun l => ?_, fun l => ?_, fun l => ?_⟩
  · by_cases h : X l = 0
    · simp only [h, if_true]
      exact norm_imaginaryUnit_zero
    · simp only [h, if_false]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
  · rw [abs_of_nonneg (norm_nonneg _)]
    exact hX l
  · by_cases h : X l = 0
    · simp [h]
    · simp only [h, if_false]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_smul]
private theorem card_finiteCells_torusFrame (L t n : ℕ) [NeZero n] :
    (finiteCells (torusFrame L t n)).card = n ^ 4 := by apply _root_.YangMills.SharedProofs.p57413 <;> assumption
private theorem mul_rpow_le_mul_rpow {a A b B N : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) (hA : a ≤ A) (hb : b ≤ B) :
    a * N ^ b ≤ A * N ^ B := by
  have h1 : N ^ b ≤ N ^ B := Real.rpow_le_rpow_of_exponent_le hN hb
  have h0 : 0 ≤ N ^ b := Real.rpow_nonneg (by linarith) _
  calc a * N ^ b ≤ A * N ^ b := mul_le_mul_of_nonneg_right hA h0
    _ ≤ A * N ^ B := mul_le_mul_of_nonneg_left h1 (ha.trans hA)
private theorem composite_rpow_bound {C₁ C₂ q₁ q₂ N : ℝ} (hN : 1 ≤ N) (h1 : 0 < C₁) (h2 : 0 < C₂)
    (hq₁ : 0 ≤ q₁) :
    240 * (C₂ * N ^ q₂) * (121 * (120 * (C₁ * N ^ q₁) + 1)) ^ 5 ≤
      240 * C₂ * (121 * (120 * C₁ + 1)) ^ 5 * N ^ (q₂ + q₁ * 5) := by
  have hN0 : 0 < N := by linarith
  have hu : 1 ≤ N ^ q₁ := Real.one_le_rpow hN hq₁
  have e : N ^ (q₂ + q₁ * 5) = N ^ q₂ * (N ^ q₁) ^ 5 := by
    rw [Real.rpow_add hN0, show q₁ * 5 = q₁ * ((5 : ℕ) : ℝ) by norm_num, Real.rpow_mul hN0.le,
      Real.rpow_natCast]
  rw [e]
  set u := N ^ q₁ with hud
  have h3 : 121 * (120 * (C₁ * u) + 1) ≤ 121 * (120 * C₁ + 1) * u := by nlinarith
  have h4 : (121 * (120 * (C₁ * u) + 1)) ^ 5 ≤ (121 * (120 * C₁ + 1) * u) ^ 5 :=
    pow_le_pow_left₀ (by positivity) h3 5
  rw [mul_pow (121 * (120 * C₁ + 1)) u 5] at h4
  calc 240 * (C₂ * N ^ q₂) * (121 * (120 * (C₁ * u) + 1)) ^ 5
      ≤ 240 * (C₂ * N ^ q₂) * ((121 * (120 * C₁ + 1)) ^ 5 * u ^ 5) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring
end StepExponentNearTrivialLemmas
open StepExponentNearTrivialLemmas in
theorem stepExponentNearTrivial (hN : BondCount) (hB : SiteDecomposition)
    (hCov : BlocksCoverLowerLevel) (h1 : MinimizerCoordinatesJetBound)
    (h2 : ChartedEnergyJetBounds) (h3 : ChartEnergyCriticalWithFloor)
    (h4 : ExponentRemainderJetBounds) : stepExponentNearTrivialStatement := by
  intro T hT k
  obtain ⟨C₁, q₁, hC₁, hq₁, g₁⟩ := h1 T hT k
  obtain ⟨C₂, q₂, hC₂, hq₂, g₂⟩ := h2 T hT k
  obtain ⟨C₃, q₃, hC₃, hq₃, g₃⟩ := h4 T hT k
  obtain ⟨nb, hnb⟩ := hN T.side hT.L_odd
  set Cq : ℝ := 240 * C₂ * (121 * (120 * C₁ + 1)) ^ 5 with hCq
  have hCq0 : 0 < Cq := by positivity
  set qq : ℝ := q₂ + q₁ * 5 with hqq
  have hqq0 : 0 ≤ qq := by positivity
  refine ⟨Cq + C₃ + nb + 1, qq + q₃ + 4, by positivity, by positivity, ?_⟩
  intro y R hy hR n _ c X hn hX
  have hn4096 : 4096 ≤ n := hT.n₀_ge.trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hodd : Odd (torusFrame R.params.side R.depth n).blockSide := by
    show Odd R.params.side
    rw [hL]
    exact hT.L_odd
  have hside : ∀ i, (torusFrame R.params.side R.depth n).extent i = n := fun _ => rfl
  have hne : Nonempty ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))) :=
    ResponseInTheExpansion.RemainderCalculus.nonempty_chordBonds hB hCov hodd fun i => by
      rw [hside]
      omega
  have hcount : (Fintype.card ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))) : ℝ) ≤
      (Cq + C₃ + nb + 1) * (n : ℝ) ^ (qq + q₃ + 4) := by
    have e := (hnb (torusFrame R.params.side R.depth n) n hL (by omega) hside).2
    rw [Fintype.card_coe, e, StepExponentNearTrivialLemmas.card_finiteCells_torusFrame]
    push_cast
    have e4 : (n : ℝ) ^ 4 = (n : ℝ) ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e4]
    exact mul_rpow_le_mul_rpow hn1 (by positivity) (by linarith) (by linarith)
  refine ⟨hne, hcount, ?_⟩
  obtain ⟨X', s, hX', hs, hXs⟩ := exists_unit_scaling X hX
  have hρ : 0 ≤ T.ballRadius := by
    have := hT.σ_pos
    unfold RenormalizationStepParameters.ParameterAssignment.ballRadius
    positivity
  have hunit : IsAdmissibleExponentFamily T.ballRadius T.lam ((Cq + C₃ + nb + 1) * (n : ℝ) ^ (qq + q₃ + 4))
      (chartEnergyAlongCurve R n c X') (exponentRemainderAlongCurve R n c X') := by
    obtain ⟨hΓ0, hΓ, hΓj⟩ := g₁ y R hy hR n c X' hn hX'
    have hS := g₂ y R hy hR n c X' hn hX'
    have hRest := g₃ y R hy hR n c X' hn hX'
    obtain ⟨hcrit, hfloor⟩ := h3 T hT k y R hy hR n c X' hn hX'
    have hz : ∀ b, ‖(0 : StepVariable (finiteCells (torusFrame R.params.side R.depth n))) b‖ ≤ T.ballRadius :=
      fun b => by
        simpa using hρ
    have hM₁ : 0 ≤ C₁ * (n : ℝ) ^ q₁ := by positivity
    have hM₂ : 0 ≤ C₂ * (n : ℝ) ^ q₂ := by positivity
    have hdiff := fun (η : StepVariable (finiteCells (torusFrame R.params.side R.depth n)))
        (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) =>
      shiftedDifference_jets (minimizerCoordinatesAlong R n c X') (chartedEnergyAlong R n c X') η hΓ0 hΓ
        hM₁ hM₂ hΓj (hS η hη).1 (hS 0 hz).1 (hS η hη).2 (hS 0 hz).2
    rw [StepExponentNearTrivialLemmas.chartEnergyAlongCurve_eq R n c X'] at hcrit hfloor ⊢
    refine
      { contDiff_Q := fun η hη => (hdiff η hη).1
        contDiff_B := fun η hη => (hRest η hη).1
        value_zero := fun τ => by simp
        critical_zero := hcrit
        hessian_lower := hfloor
        deriv_bound_Q := fun η hη j hj2 hj5 => ?_
        deriv_bound_B := fun η hη j hj1 hj3 => ?_ }
    · refine ((hdiff η hη).2 j (by omega) hj5).trans ?_
      refine (composite_rpow_bound hn1 hC₁ hC₂ hq₁).trans ?_
      exact mul_rpow_le_mul_rpow hn1 hCq0.le (by linarith) (by linarith)
    · refine ((hRest η hη).2 j hj1 hj3).trans ?_
      exact mul_rpow_le_mul_rpow hn1 hC₃.le (by linarith) (by linarith)
  rw [StepExponentNearTrivialLemmas.chartEnergyAlongCurve_scale R n c hXs,
    StepExponentNearTrivialLemmas.exponentRemainderAlongCurve_scale R n c hXs]
  exact admissibleFamily_comp_scale hunit s hs
end YangMills.Construction.RunningCouplingSlope
end
