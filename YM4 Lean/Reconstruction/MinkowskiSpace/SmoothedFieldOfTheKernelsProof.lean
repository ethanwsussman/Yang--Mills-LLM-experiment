import Reconstruction.MinkowskiSpace.ConjugatedInsertionsOfTheKernels
import Reconstruction.MinkowskiSpace.FormWithNoFieldOfAFunctional
import Reconstruction.MinkowskiSpace.InsertionOperatorsOfOneField
import Reconstruction.MinkowskiSpace.SmoothedFieldOfTheKernels
import Reconstruction.MinkowskiSpace.TranslationOperatorsOfABoundedFieldFormProof
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff Topology
noncomputable section
namespace YangMills.Construction.SmoothedKernelField
section ComplexCalculus
open Function
structure SmoothCLinearOn (O : Set (Fin 4 → ℂ)) (G : (Fin 4 → ℂ) → ℂ) : Prop where
  contDiffOn : ContDiffOn ℝ ∞ G O
  map_I_smul : ∀ w ∈ O, ∀ v, fderiv ℝ G w (Complex.I • v) = Complex.I • fderiv ℝ G w v
def cPartial (μ : Fin 4) (G : (Fin 4 → ℂ) → ℂ) : (Fin 4 → ℂ) → ℂ :=
  fun w => fderiv ℝ G w (Pi.single μ 1)
variable {O : Set (Fin 4 → ℂ)} {G H : (Fin 4 → ℂ) → ℂ}
theorem SmoothCLinearOn.differentiableAt
    (hG : SmoothCLinearOn O G) (hO : IsOpen O) {w : Fin 4 → ℂ} (hw : w ∈ O) :
    DifferentiableAt ℝ G w :=
  ((hG.contDiffOn.contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp))
theorem SmoothCLinearOn.coordPartial
    (hG : SmoothCLinearOn O G) (hO : IsOpen O) (μ : Fin 4) :
    SmoothCLinearOn O (cPartial μ G) := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ G) O := hG.contDiffOn.fderiv_of_isOpen hO (by simp)
  refine ⟨hD.clm_apply contDiffOn_const, fun w hw v => ?_⟩
  have hDw : DifferentiableAt ℝ (fderiv ℝ G) w :=
    (hD.contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp)
  have happ : ∀ u : Fin 4 → ℂ, HasFDerivAt (fun w' => fderiv ℝ G w' u)
      ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ G) w)) w := fun u =>
    (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp w hDw.hasFDerivAt
  have hsym : ∀ x y, fderiv ℝ (fderiv ℝ G) w x y = fderiv ℝ (fderiv ℝ G) w y x := fun x y =>
    ((hG.contDiffOn.contDiffAt (hO.mem_nhds hw)).isSymmSndFDerivAt (by
      simpa using (ENat.LEInfty.out : (2 : WithTop ℕ∞) ≤ ∞))).eq x y
  have hnear : (fun w' => fderiv ℝ G w' (Complex.I • v)) =ᶠ[𝓝 w]
      fun w' => Complex.I • fderiv ℝ G w' v := by
    filter_upwards [hO.mem_nhds hw] with w' hw' using hG.map_I_smul w' hw' v
  have e₁ := (happ (Complex.I • v)).congr_of_eventuallyEq hnear.symm
  have e₂ := (happ v).const_smul Complex.I
  have e₃ := e₁.unique e₂
  have hfd : ∀ u, fderiv ℝ (cPartial μ G) w u =
      fderiv ℝ (fderiv ℝ G) w u (Pi.single μ 1) := fun u => by
    have := (happ (Pi.single μ 1)).fderiv
    show fderiv ℝ (fun w' => fderiv ℝ G w' (Pi.single μ 1)) w u = _
    simpa using congrArg (fun L => L u) this
  rw [hfd, hfd, hsym, hsym v]
  have := congrArg (fun L => L (Pi.single μ 1)) e₃
  simpa using this
theorem SmoothCLinearOn.exists_hasFDerivAt_clm
    (hG : SmoothCLinearOn O G) (hO : IsOpen O) {w : Fin 4 → ℂ} (hw : w ∈ O) :
    ∃ L : (Fin 4 → ℂ) →L[ℂ] ℂ, HasFDerivAt G L w ∧ ∀ v, L v = fderiv ℝ G w v := by
  set D := fderiv ℝ G w with hDdef
  have hsm : ∀ (c : ℂ) (v : Fin 4 → ℂ), D (c • v) = c • D v := by
    intro c v
    have hc : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    rw [hc, map_add, map_smul, map_smul, hDdef, hG.map_I_smul w hw]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [smul_eq_mul, Complex.real_smul]
    ring
  let L : (Fin 4 → ℂ) →L[ℂ] ℂ :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun c v => by simpa using hsm c v
      cont := D.continuous }
  refine ⟨L, ?_, fun v => rfl⟩
  have hd : HasFDerivAt G D w := (hG.differentiableAt hO hw).hasFDerivAt
  exact hasFDerivAt_of_restrictScalars ℝ hd (by ext; rfl)
theorem SmoothCLinearOn.hasDerivAt_update
    (hG : SmoothCLinearOn O G) (hO : IsOpen O) (z : Fin 4 → ℂ) (μ : Fin 4) (t : ℂ)
    (ht : update z μ t ∈ O) :
    HasDerivAt (fun s : ℂ => G (update z μ s)) (cPartial μ G (update z μ t)) t := by
  obtain ⟨L, hL, hLv⟩ := hG.exists_hasFDerivAt_clm hO ht
  have := hL.comp_hasDerivAt t (_root_.hasDerivAt_update z μ t)
  rw [hLv] at this
  exact this
theorem iterate_cPartial (hG : SmoothCLinearOn O G) (hO : IsOpen O) (μ : Fin 4)
    (k : ℕ) : SmoothCLinearOn O ((cPartial μ)^[k] G) := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.coordPartial hO μ
theorem norm_iterate_three_cPartial_le (hH : SmoothCLinearOn O H) (hO : IsOpen O) (z : Fin 4 → ℂ)
    (μ : Fin 4) {r B : ℝ} (hr : 0 < r)
    (hz : ∀ t : ℂ, ‖t - z μ‖ ≤ r → update z μ t ∈ O)
    (hB : ∀ t : ℂ, ‖t - z μ‖ ≤ r → ‖H (update z μ t)‖ ≤ B) :
    ‖(cPartial μ)^[3] H z‖ ≤ 6 / r ^ 3 * B := by
  set g : ℕ → ℂ → ℂ := fun k t => (cPartial μ)^[k] H (update z μ t) with hg
  have hcont : Continuous fun t : ℂ => update z μ t := continuous_const.update μ continuous_id
  set S : Set ℂ := (fun t : ℂ => update z μ t) ⁻¹' O with hS
  have hSo : IsOpen S := hO.preimage hcont
  have hder : ∀ k, ∀ t ∈ S, HasDerivAt (g k) (g (k + 1) t) t := by
    intro k t ht
    have := (iterate_cPartial hH hO μ k).hasDerivAt_update hO z μ t ht
    simpa [hg, Function.iterate_succ_apply'] using this
  have hit : ∀ k, ∀ t ∈ S, iteratedDeriv k (g 0) t = g k t := by
    intro k
    induction k with
    | zero => intro t _; simp
    | succ k ih =>
      intro t ht
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (g 0) =ᶠ[𝓝 t] g k := by
        filter_upwards [hSo.mem_nhds ht] with s hs using ih s hs
      rw [hev.deriv_eq]
      exact (hder k t ht).deriv
  have hzS : z μ ∈ S := by
    have := hz (z μ) (by simpa using hr.le)
    exact this
  have hball : Metric.closedBall (z μ) r ⊆ S := fun t ht => hz t (by simpa [dist_eq_norm] using ht)
  have hdc : DiffContOnCl ℂ (g 0) (Metric.ball (z μ) r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    exact fun t ht => (hder 0 t (hball ht)).differentiableAt.differentiableWithinAt
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 3 hr hdc
    (C := B) (fun t ht => hB t (by simpa [dist_eq_norm] using ht.le))
  rw [hit 3 _ hzS] at hc
  have hval : g 3 (z μ) = (cPartial μ)^[3] H z := by simp [hg]
  rw [hval] at hc
  calc _ ≤ _ := hc
    _ = 6 / r ^ 3 * B := by simp [Nat.factorial]; ring
end ComplexCalculus
section RealPartialsAndPolydiscs
open Function Set MinkowskiSpace
variable {O : Set (Fin 4 → ℂ)} {G H : (Fin 4 → ℂ) → ℂ}
theorem toComplex_add_smul_single (x : Fin 4 → ℝ) (μ : Fin 4) (t : ℝ) :
    toComplex (x + t • Pi.single μ (1 : ℝ)) = toComplex x + t • (Pi.single μ 1 : Fin 4 → ℂ) := by
  funext j
  by_cases h : j = μ
  · subst h
    simp [toComplex]
  · simp [toComplex, Pi.single_eq_of_ne h]
theorem partialDerivR4_eqOn (hH : SmoothCLinearOn O H) (hO : IsOpen O)
    {U : Set (Fin 4 → ℝ)} (hU : IsOpen U) (hUO : MapsTo toComplex U O) {f : (Fin 4 → ℝ) → ℂ}
    (hf : EqOn f (H ∘ toComplex) U) (μ : Fin 4) :
    EqOn (TestFunctions.partialDerivR4 μ f) (cPartial μ H ∘ toComplex) U := by
  intro x hx
  have hp : HasDerivAt (fun t : ℝ => toComplex x + t • (Pi.single μ 1 : Fin 4 → ℂ))
      (Pi.single μ 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single μ 1 : Fin 4 → ℂ)).const_add
      (toComplex x)
  have hH' : HasFDerivAt H (fderiv ℝ H (toComplex x))
      (toComplex x + (0 : ℝ) • (Pi.single μ 1 : Fin 4 → ℂ)) := by
    simpa using (hH.differentiableAt hO (hUO hx)).hasFDerivAt
  have hcomp := hH'.comp_hasDerivAt (0 : ℝ) hp
  have hev : (fun t : ℝ => f (x + t • Pi.single μ (1 : ℝ))) =ᶠ[𝓝 0]
      (H ∘ fun t : ℝ => toComplex x + t • (Pi.single μ 1 : Fin 4 → ℂ)) := by
    have hc : Continuous fun t : ℝ => x + t • Pi.single μ (1 : ℝ) := by fun_prop
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • Pi.single μ (1 : ℝ) ∈ U :=
      hc.continuousAt.eventually_mem (by simpa using hU.mem_nhds hx)
    filter_upwards [hmem] with t ht
    rw [hf ht, Function.comp, Function.comp, toComplex_add_smul_single]
  exact (hcomp.congr_of_eventuallyEq hev).deriv
theorem iterate_partialDerivR4_eqOn (hH : SmoothCLinearOn O H) (hO : IsOpen O)
    {U : Set (Fin 4 → ℝ)} (hU : IsOpen U) (hUO : MapsTo toComplex U O) {f : (Fin 4 → ℝ) → ℂ}
    (hf : EqOn f (H ∘ toComplex) U) (μ : Fin 4) (k : ℕ) :
    EqOn ((TestFunctions.partialDerivR4 μ)^[k] f) ((cPartial μ)^[k] H ∘ toComplex) U := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact partialDerivR4_eqOn (iterate_cPartial hH hO μ k) hO hU hUO ih μ
def cubeExponent (Γ : Finset (Fin 4)) (μ : Fin 4) : ℕ := if μ ∈ Γ then 3 else 0
def cCubedPartial (Γ : Finset (Fin 4)) (H : (Fin 4 → ℂ) → ℂ) : (Fin 4 → ℂ) → ℂ :=
  (cPartial 0)^[cubeExponent Γ 0] ((cPartial 1)^[cubeExponent Γ 1]
    ((cPartial 2)^[cubeExponent Γ 2] ((cPartial 3)^[cubeExponent Γ 3] H)))
theorem smoothCLinearOn_cCubedPartial (hH : SmoothCLinearOn O H) (hO : IsOpen O)
    (Γ : Finset (Fin 4)) : SmoothCLinearOn O (cCubedPartial Γ H) :=
  iterate_cPartial (iterate_cPartial (iterate_cPartial
    (iterate_cPartial hH hO 3 _) hO 2 _) hO 1 _) hO 0 _
theorem cubedPartial_eqOn (hH : SmoothCLinearOn O H) (hO : IsOpen O)
    {U : Set (Fin 4 → ℝ)} (hU : IsOpen U) (hUO : MapsTo toComplex U O) {f : (Fin 4 → ℝ) → ℂ}
    (hf : EqOn f (H ∘ toComplex) U) (Γ : Finset (Fin 4)) :
    EqOn (CubeKernels.cubedPartial Γ f) (cCubedPartial Γ H ∘ toComplex) U := by
  have h3 := iterate_cPartial hH hO 3 (cubeExponent Γ 3)
  have h2 := iterate_cPartial h3 hO 2 (cubeExponent Γ 2)
  have h1 := iterate_cPartial h2 hO 1 (cubeExponent Γ 1)
  exact iterate_partialDerivR4_eqOn h1 hO hU hUO (iterate_partialDerivR4_eqOn h2 hO hU hUO
    (iterate_partialDerivR4_eqOn h3 hO hU hUO (iterate_partialDerivR4_eqOn hH hO hU hUO hf 3 _) 2 _)
    1 _) 0 _
theorem cPartial_linear_comb {G₁ G₂ G₃ : (Fin 4 → ℂ) → ℂ}
    (h₁ : SmoothCLinearOn O G₁) (h₂ : SmoothCLinearOn O G₂)
    (hO : IsOpen O) (c : ℂ) (he : EqOn G₃ (fun z => c * G₁ z + G₂ z) O) (μ : Fin 4) :
    EqOn (cPartial μ G₃) (fun z => c * cPartial μ G₁ z + cPartial μ G₂ z) O := by
  intro w hw
  have hev : G₃ =ᶠ[𝓝 w] fun z => c * G₁ z + G₂ z := by
    filter_upwards [hO.mem_nhds hw] with z hz using he hz
  have hd := ((h₁.differentiableAt hO hw).hasFDerivAt.const_mul c).add
    (h₂.differentiableAt hO hw).hasFDerivAt
  have hfd : fderiv ℝ G₃ w = _ := hev.fderiv_eq.trans hd.fderiv
  simp only [cPartial]
  rw [hfd]
  simp
theorem iterate_cPartial_linear_comb {G₁ G₂ G₃ : (Fin 4 → ℂ) → ℂ}
    (h₁ : SmoothCLinearOn O G₁) (h₂ : SmoothCLinearOn O G₂)
    (hO : IsOpen O) (c : ℂ) (he : EqOn G₃ (fun z => c * G₁ z + G₂ z) O) (μ : Fin 4) (k : ℕ) :
    EqOn ((cPartial μ)^[k] G₃)
      (fun z => c * (cPartial μ)^[k] G₁ z + (cPartial μ)^[k] G₂ z) O := by
  induction k with
  | zero => exact he
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact cPartial_linear_comb (iterate_cPartial h₁ hO μ k)
      (iterate_cPartial h₂ hO μ k) hO c ih μ
theorem cCubedPartial_linear_comb {G₁ G₂ G₃ : (Fin 4 → ℂ) → ℂ}
    (h₁ : SmoothCLinearOn O G₁) (h₂ : SmoothCLinearOn O G₂)
    (hO : IsOpen O) (c : ℂ) (he : EqOn G₃ (fun z => c * G₁ z + G₂ z) O) (Γ : Finset (Fin 4)) :
    EqOn (cCubedPartial Γ G₃)
      (fun z => c * cCubedPartial Γ G₁ z + cCubedPartial Γ G₂ z) O := by
  have a3 := iterate_cPartial h₁ hO 3 (cubeExponent Γ 3)
  have b3 := iterate_cPartial h₂ hO 3 (cubeExponent Γ 3)
  have a2 := iterate_cPartial a3 hO 2 (cubeExponent Γ 2)
  have b2 := iterate_cPartial b3 hO 2 (cubeExponent Γ 2)
  have a1 := iterate_cPartial a2 hO 1 (cubeExponent Γ 1)
  have b1 := iterate_cPartial b2 hO 1 (cubeExponent Γ 1)
  exact iterate_cPartial_linear_comb a1 b1 hO c (iterate_cPartial_linear_comb a2 b2 hO c
    (iterate_cPartial_linear_comb a3 b3 hO c (iterate_cPartial_linear_comb h₁ h₂ hO c he 3 _)
      2 _) 1 _) 0 _
def polydiscSlice (a : Fin 4 → ℂ) (r : ℝ) (S : Finset (Fin 4)) : Set (Fin 4 → ℂ) :=
  {w | ∀ μ, (μ ∈ S → ‖w μ - a μ‖ ≤ r) ∧ (μ ∉ S → w μ = a μ)}
theorem polydiscSlice_subset_univ {a : Fin 4 → ℂ} {r : ℝ} (hr : 0 < r) (S : Finset (Fin 4)) :
    polydiscSlice a r S ⊆ polydiscSlice a r Finset.univ := by
  intro w hw μ
  refine ⟨fun _ => ?_, fun hμ => absurd (Finset.mem_univ μ) hμ⟩
  by_cases h : μ ∈ S
  · exact (hw μ).1 h
  · rw [(hw μ).2 h]
    simpa using hr.le
theorem update_mem_polydiscSlice {a w : Fin 4 → ℂ} {r : ℝ} {S : Finset (Fin 4)} {μ : Fin 4}
    (hμ : μ ∉ S) (hw : w ∈ polydiscSlice a r S) {t : ℂ} (ht : ‖t - w μ‖ ≤ r) :
    update w μ t ∈ polydiscSlice a r (insert μ S) := by
  have hwμ : w μ = a μ := (hw μ).2 hμ
  intro ν
  by_cases hν : ν = μ
  · subst hν
    refine ⟨fun _ => ?_, fun h => absurd (Finset.mem_insert_self _ _) h⟩
    simpa [hwμ] using ht
  · have hνS : ν ∈ insert μ S ↔ ν ∈ S := by simp [hν]
    simpa [hνS, update_of_ne hν] using hw ν
theorem norm_iterate_cPartial_le_step (Γ : Finset (Fin 4)) (hH : SmoothCLinearOn O H)
    (hO : IsOpen O) (a : Fin 4 → ℂ) {r B : ℝ} (hr : 0 < r) (μ : Fin 4) (S : Finset (Fin 4))
    (hμ : μ ∉ S) (hsub : polydiscSlice a r Finset.univ ⊆ O)
    (hB : ∀ w ∈ polydiscSlice a r (insert μ S), ‖H w‖ ≤ B) :
    ∀ w ∈ polydiscSlice a r S, ‖(cPartial μ)^[cubeExponent Γ μ] H w‖ ≤
      (if μ ∈ Γ then 6 / r ^ 3 else 1) * B := by
  intro w hw
  by_cases hΓ : μ ∈ Γ
  · simp only [cubeExponent, hΓ, if_true]
    exact norm_iterate_three_cPartial_le hH hO w μ hr
      (fun t ht => hsub (polydiscSlice_subset_univ hr _ (update_mem_polydiscSlice hμ hw ht)))
      (fun t ht => hB _ (update_mem_polydiscSlice hμ hw ht))
  · simp only [cubeExponent, hΓ, if_false, Function.iterate_zero, id, one_mul]
    refine hB w fun ν => ?_
    by_cases hν : ν = μ
    · subst hν
      refine ⟨fun _ => ?_, fun h => absurd (Finset.mem_insert_self _ _) h⟩
      rw [(hw ν).2 hμ]
      simpa using hr.le
    · have hνS : ν ∈ insert μ S ↔ ν ∈ S := by simp [hν]
      simpa [hνS] using hw ν
theorem norm_cCubedPartial_le (Γ : Finset (Fin 4)) (hH : SmoothCLinearOn O H)
    (hO : IsOpen O) (a : Fin 4 → ℂ) {r B : ℝ} (hr : 0 < r)
    (hsub : polydiscSlice a r Finset.univ ⊆ O) (hB : ∀ w ∈ O, ‖H w‖ ≤ B) :
    ‖cCubedPartial Γ H a‖ ≤ (6 / r ^ 3) ^ Γ.card * B := by
  have e2 : insert (2 : Fin 4) ({0, 1} : Finset (Fin 4)) = {0, 1, 2} := by decide
  have e1 : insert (1 : Fin 4) ({0} : Finset (Fin 4)) = {0, 1} := by decide
  have e0 : insert (0 : Fin 4) (∅ : Finset (Fin 4)) = {0} := by decide
  have s3 := norm_iterate_cPartial_le_step Γ hH hO a hr 3 {0, 1, 2} (by decide) hsub
    (fun w hw => hB w (hsub (polydiscSlice_subset_univ hr _ hw)))
  have s2 := norm_iterate_cPartial_le_step Γ (iterate_cPartial hH hO 3 (cubeExponent Γ 3)) hO a hr
    2 {0, 1} (by decide) hsub (by rw [e2]; exact s3)
  have s1 := norm_iterate_cPartial_le_step Γ (iterate_cPartial (iterate_cPartial hH hO 3
    (cubeExponent Γ 3)) hO 2 (cubeExponent Γ 2)) hO a hr 1 {0} (by decide) hsub
    (by rw [e1]; exact s2)
  have s0 := norm_iterate_cPartial_le_step Γ (iterate_cPartial (iterate_cPartial (iterate_cPartial
    hH hO 3 (cubeExponent Γ 3)) hO 2 (cubeExponent Γ 2)) hO 1 (cubeExponent Γ 1)) hO a hr 0 ∅
    (by decide) hsub (by rw [e0]; exact s1)
  have ha : a ∈ polydiscSlice a r ∅ := fun μ => ⟨fun h => absurd h (by simp), fun _ => rfl⟩
  have hfin := s0 a ha
  have hprod : (6 / r ^ 3) ^ Γ.card =
      (if (0 : Fin 4) ∈ Γ then 6 / r ^ 3 else 1) * ((if (1 : Fin 4) ∈ Γ then 6 / r ^ 3 else 1) *
        ((if (2 : Fin 4) ∈ Γ then 6 / r ^ 3 else 1) * (if (3 : Fin 4) ∈ Γ then 6 / r ^ 3 else 1))) := by
    have := Finset.prod_ite_mem Finset.univ Γ (fun _ : Fin 4 => 6 / r ^ 3)
    rw [Fin.prod_univ_four] at this
    simp only [Finset.univ_inter, Finset.prod_const] at this
    rw [← this]
    ring
  rw [hprod]
  calc _ ≤ _ := hfin
    _ = _ := by ring
end RealPartialsAndPolydiscs
section MatrixCoefficients
open Set MinkowskiSpace FieldForms FieldFormTranslations ProjectionMeasures OneLoopNotation Coordinates
set_option linter.unusedSectionVars false
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem imInClosedCone_of_mem_futureTube {ζ : ComplexVec4} (h : ζ ∈ futureTube) :
    ImInClosedCone ζ :=
  show coneGap (imPart ζ) ≥ 0 from (show coneGap (imPart ζ) > 0 from h).le
theorem continuousOn_spectralTranslation {E : FourBorelSet → BddOp K}
    (hL : LipschitzInTube E) : ContinuousOn (spectralTranslation E) futureTube := by apply _root_.YangMills.Construction.FieldFormTranslations.continuousOn_spectralTranslation <;> assumption
def fstVec (w : Fin (4 + 4) → ℂ) : ComplexVec4 := fun i => w (Fin.castAdd 4 i)
def sndVec (w : Fin (4 + 4) → ℂ) : ComplexVec4 := fun i => w (Fin.natAdd 4 i)
theorem continuous_fstVec : Continuous fstVec := by
  unfold fstVec
  fun_prop
theorem continuous_sndVec : Continuous sndVec := by
  unfold sndVec
  fun_prop
def matrixCoeff (E : FourBorelSet → BddOp K) (A : BddOp K) (χ χ' : K)
    (w : Fin (4 + 4) → ℂ) : Fin 1 → ℂ :=
  fun _ => ⟪χ, spectralTranslation E (fstVec w)
    (A (spectralTranslation E (sndVec w) χ'))⟫_ℂ
def futureTubePair : Set (Fin (4 + 4) → ℂ) :=
  {w | fstVec w ∈ futureTube ∧ sndVec w ∈ futureTube}
theorem matrixCoeff_isHolomorphicIn {E : FourBorelSet → BddOp K}
    (hL : LipschitzInTube E) (hM : HolomorphicMatrixCoeffs E)
    (A : BddOp K) (χ χ' : K) :
    ComplexCoordinates.IsHolomorphicIn futureTubePair (matrixCoeff E A χ χ') := by
  have htube : IsOpen futureTube := (hM χ χ').1
  have hT := continuousOn_spectralTranslation hL
  refine ⟨(htube.preimage continuous_fstVec).inter (htube.preimage continuous_sndVec),
    ?_, ?_⟩
  · refine continuousOn_pi.2 fun _ => ?_
    have h₁ : ContinuousOn (fun w => spectralTranslation E (fstVec w)) futureTubePair :=
      hT.comp continuous_fstVec.continuousOn fun w hw => hw.1
    have h₂ : ContinuousOn (fun w => spectralTranslation E (sndVec w)) futureTubePair :=
      hT.comp continuous_sndVec.continuousOn fun w hw => hw.2
    have h₃ : ContinuousOn (fun w => spectralTranslation E (sndVec w) χ') futureTubePair :=
      h₂.clm_apply continuousOn_const
    have h₄ : ContinuousOn (fun w => A (spectralTranslation E (sndVec w) χ')) futureTubePair :=
      A.continuous.comp_continuousOn h₃
    exact continuousOn_const.inner (h₁.clm_apply h₄)
  · intro a ha j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have hf : ∀ ζ : ℂ, fstVec (a + ζ • ComplexCoordinates.stdBasisVector (Fin.castAdd 4 i)) =
          fstVec a + ζ • ComplexCoordinates.stdBasisVector i := by
        intro ζ
        funext l
        by_cases hl : l = i
        · subst hl
          simp [fstVec, ComplexCoordinates.stdBasisVector]
        · have : Fin.castAdd 4 l ≠ Fin.castAdd 4 i := fun h => hl (Fin.castAdd_injective _ _ h)
          simp [fstVec, ComplexCoordinates.stdBasisVector, Pi.single_eq_of_ne this,
            Pi.single_eq_of_ne hl]
      have hs : ∀ ζ : ℂ, sndVec (a + ζ • ComplexCoordinates.stdBasisVector (Fin.castAdd 4 i)) =
          sndVec a := by
        intro ζ
        funext l
        have : Fin.natAdd 4 l ≠ Fin.castAdd 4 i := fun h => by
          have := congrArg Fin.val h
          simp at this
          omega
        show a (Fin.natAdd 4 l) + ζ * (Pi.single (Fin.castAdd 4 i) (1 : ℂ) : Fin (4 + 4) → ℂ)
          (Fin.natAdd 4 l) = a (Fin.natAdd 4 l)
        rw [Pi.single_eq_of_ne this]
        simp
      have hev := (hM χ (A (spectralTranslation E (sndVec a) χ'))).2.2 (fstVec a) ha.1 i
      filter_upwards [hev] with ζ hζ
      refine differentiableAt_pi.2 fun _ => ?_
      have := differentiableAt_pi.1 hζ 0
      simpa [matrixCoeff, hf, hs] using this
    · have hs : ∀ ζ : ℂ, sndVec (a + ζ • ComplexCoordinates.stdBasisVector (Fin.natAdd 4 i)) =
          sndVec a + ζ • ComplexCoordinates.stdBasisVector i := by
        intro ζ
        funext l
        by_cases hl : l = i
        · subst hl
          show a (Fin.natAdd 4 l) + ζ * (Pi.single (Fin.natAdd 4 l) (1 : ℂ) : Fin (4 + 4) → ℂ)
            (Fin.natAdd 4 l) = a (Fin.natAdd 4 l) + ζ * (Pi.single l (1 : ℂ) : Fin 4 → ℂ) l
          simp only [Pi.single_eq_same]
        · have : Fin.natAdd 4 l ≠ Fin.natAdd 4 i := fun h => hl (Fin.natAdd_injective _ _ h)
          show a (Fin.natAdd 4 l) + ζ * (Pi.single (Fin.natAdd 4 i) (1 : ℂ) : Fin (4 + 4) → ℂ)
            (Fin.natAdd 4 l) = a (Fin.natAdd 4 l) + ζ * (Pi.single i (1 : ℂ) : Fin 4 → ℂ) l
          rw [Pi.single_eq_of_ne this, Pi.single_eq_of_ne hl]
      have hf : ∀ ζ : ℂ, fstVec (a + ζ • ComplexCoordinates.stdBasisVector (Fin.natAdd 4 i)) =
          fstVec a := by
        intro ζ
        funext l
        have : Fin.castAdd 4 l ≠ Fin.natAdd 4 i := fun h => by
          have := congrArg Fin.val h
          simp at this
          omega
        show a (Fin.castAdd 4 l) + ζ * (Pi.single (Fin.natAdd 4 i) (1 : ℂ) : Fin (4 + 4) → ℂ)
          (Fin.castAdd 4 l) = a (Fin.castAdd 4 l)
        rw [Pi.single_eq_of_ne this]
        simp
      set B : K →L[ℂ] K := spectralTranslation E (fstVec a) ∘L A with hB
      have hev := (hM (ContinuousLinearMap.adjoint B χ) χ').2.2 (sndVec a) ha.2 i
      filter_upwards [hev] with ζ hζ
      refine differentiableAt_pi.2 fun _ => ?_
      have := differentiableAt_pi.1 hζ 0
      have hadj : ∀ ξ : K, ⟪ContinuousLinearMap.adjoint B χ, ξ⟫_ℂ =
          ⟪χ, spectralTranslation E (fstVec a) (A ξ)⟫_ℂ := fun ξ => by
        rw [ContinuousLinearMap.adjoint_inner_left]
        rfl
      simp only [matrixCoeff, hf, hs]
      simpa [hadj] using this
theorem smoothCLinearOn_of_isHolomorphicIn
    (hMX : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (Fin 4 → ℂ)} {F : ComplexCoordinates 4 → ComplexCoordinates 1}
    (hF : ComplexCoordinates.IsHolomorphicIn O F) :
    SmoothCLinearOn O fun z => F z 0 := by
  obtain ⟨_, hs, hl, _, _⟩ := (hMX.1 4 O hF.1).1 1 F hF
  refine ⟨contDiffOn_pi.1 hs 0, fun w hw v => ?_⟩
  obtain ⟨L, hL⟩ := hl w hw
  have h0 := (hasFDerivAt_pi'.1 hL 0).fderiv
  rw [h0]
  simp
def timeShift (η : ℝ) : ComplexVec4 := toComplex (η • FieldFormConditions.timeUnitVec)
def wickPlus (η : ℝ) (z : ComplexVec4) : ComplexVec4 := wickMap (timeShift η + z)
def wickMinus (η : ℝ) (z : ComplexVec4) : ComplexVec4 := wickMap (timeShift η - z)
def slabDomain (η : ℝ) : Set ComplexVec4 :=
  {z | wickPlus η z ∈ futureTube ∧ wickMinus η z ∈ futureTube}
def wickPair (η : ℝ) (z : Fin 4 → ℂ) : Fin (4 + 4) → ℂ := Fin.append (wickPlus η z) (wickMinus η z)
theorem fstVec_wickPair (η : ℝ) (z : Fin 4 → ℂ) : fstVec (wickPair η z) = wickPlus η z := by
  funext i
  simp [fstVec, wickPair, Fin.append_left]
theorem sndVec_wickPair (η : ℝ) (z : Fin 4 → ℂ) :
    sndVec (wickPair η z) = wickMinus η z := by
  funext i
  exact Fin.append_right _ _ i
theorem differentiable_wickMap :
    Differentiable ℂ fun x : ComplexVec4 => wickMap x :=
  (LinearMap.toContinuousLinearMap wickMap.toLinearMap).differentiable
theorem differentiable_wickPlus (η : ℝ) : Differentiable ℂ (wickPlus η) :=
  differentiable_wickMap.comp ((differentiable_const _).add differentiable_id)
theorem differentiable_wickMinus (η : ℝ) : Differentiable ℂ (wickMinus η) :=
  differentiable_wickMap.comp ((differentiable_const _).sub differentiable_id)
theorem differentiable_wickPair (η : ℝ) : Differentiable ℂ (wickPair η) := by
  refine differentiable_pi.2 fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have h : (fun z => wickPair η z (Fin.castAdd 4 i)) = fun z => wickPlus η z i := by
      funext z
      simp [wickPair, Fin.append_left]
    rw [h]
    exact differentiable_pi.1 (differentiable_wickPlus η) i
  · have h : (fun z => wickPair η z (Fin.natAdd 4 i)) = fun z => wickMinus η z i := by
      funext z
      exact Fin.append_right _ _ i
    rw [h]
    exact differentiable_pi.1 (differentiable_wickMinus η) i
theorem isOpen_slabDomain (η : ℝ) (htube : IsOpen futureTube) : IsOpen (slabDomain η) :=
  (htube.preimage (differentiable_wickPlus η).continuous).inter
    (htube.preimage (differentiable_wickMinus η).continuous)
theorem wickPair_isHolomorphicIn (η : ℝ) (hO : IsOpen (slabDomain η)) :
    ComplexCoordinates.IsHolomorphicIn (slabDomain η) (wickPair η) := by
  refine ⟨hO, (differentiable_wickPair η).continuous.continuousOn, fun a _ j =>
    Filter.Eventually.of_forall fun ζ => ?_⟩
  exact (differentiable_wickPair η _).comp ζ (by fun_prop)
def slabCoeff (E : FourBorelSet → BddOp K) (A : BddOp K) (χ χ' : K) (η : ℝ)
    (z : ComplexVec4) : ℂ :=
  ⟪χ, spectralTranslation E (wickPlus η z) (A (spectralTranslation E (wickMinus η z) χ'))⟫_ℂ
theorem smoothCLinearOn_slabCoeff (hMX : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {E : FourBorelSet → BddOp K} (hL : LipschitzInTube E)
    (hM : HolomorphicMatrixCoeffs E) (A : BddOp K) (χ χ' : K) (η : ℝ) :
    SmoothCLinearOn (slabDomain η) (slabCoeff E A χ χ' η) := by
  have hs := matrixCoeff_isHolomorphicIn hL hM A χ χ'
  have hO := isOpen_slabDomain η (hM χ χ').1
  have hc := ((hMX.1 (4 + 4) futureTubePair hs.1).1 1 _ hs).2.2.2.1 4 (slabDomain η) (wickPair η)
    (wickPair_isHolomorphicIn η hO) (fun z hz => by
      refine ⟨?_, ?_⟩
      · rw [fstVec_wickPair]
        exact hz.1
      · rw [sndVec_wickPair]
        exact hz.2)
  have h := smoothCLinearOn_of_isHolomorphicIn hMX hc
  have heq : (fun z => (matrixCoeff E A χ χ' ∘ wickPair η) z 0) = slabCoeff E A χ χ' η := by
    funext z
    simp [matrixCoeff, slabCoeff, fstVec_wickPair, sndVec_wickPair]
  rwa [heq] at h
theorem tubeGap_wickMap (x : ComplexVec4) :
    tubeGap (wickMap x) =
      (x 3).re - spaceNorm ![(x 0).im, (x 1).im, (x 2).im] := by
  have h1 : imPart (wickMap x) 0 = (x 3).re := by
    show (wickMap x 0).im = _
    rw [wickMap_apply_zero]
    simp
  have h2 : spacePart (imPart (wickMap x)) = ![(x 0).im, (x 1).im, (x 2).im] := by
    funext i
    fin_cases i <;> rfl
  unfold tubeGap coneGap
  rw [h1, h2]
theorem timeShift_apply_three (η : ℝ) : timeShift η 3 = (η : ℂ) := by
  simp [timeShift, toComplex, PeriodicLattice.coordVec, TimeAxis.timeIdx]
theorem timeShift_im (η : ℝ) (j : Fin 4) : (timeShift η j).im = 0 := by
  simp [timeShift, toComplex]
theorem spaceNorm_neg (x y w : ℝ) : spaceNorm ![-x, -y, -w] = spaceNorm ![x, y, w] := by
  simp [spaceNorm, Fin.sum_univ_three]
theorem mem_slabDomain {η : ℝ} {z : ComplexVec4}
    (hz : |(z 3).re| + spaceNorm ![(z 0).im, (z 1).im, (z 2).im] < η) : z ∈ slabDomain η := by
  have hle := le_abs_self (z 3).re
  have hge := neg_abs_le (z 3).re
  refine ⟨?_, ?_⟩
  · show tubeGap _ > 0
    rw [wickPlus, tubeGap_wickMap]
    simp only [Pi.add_apply, Complex.add_im, Complex.add_re, timeShift_im, zero_add,
      timeShift_apply_three, Complex.ofReal_re]
    linarith
  · show tubeGap _ > 0
    rw [wickMinus, tubeGap_wickMap]
    simp only [Pi.sub_apply, Complex.sub_im, Complex.sub_re, timeShift_im, zero_sub,
      timeShift_apply_three, Complex.ofReal_re, spaceNorm_neg]
    linarith
theorem toComplex_mem_slabDomain {η : ℝ} {a : Fin 4 → ℝ} (ha : |a 3| < η) :
    toComplex a ∈ slabDomain η := by
  apply mem_slabDomain
  simpa [toComplex, spaceNorm, Fin.sum_univ_three] using ha
theorem spaceNorm_le {x y w r : ℝ} (hr : 0 ≤ r) (hx : |x| ≤ r) (hy : |y| ≤ r) (hw : |w| ≤ r) :
    spaceNorm ![x, y, w] ≤ 2 * r := by
  have h : ∀ u : ℝ, |u| ≤ r → u ^ 2 ≤ r ^ 2 := fun u hu =>
    sq_le_sq' (by linarith [neg_abs_le u, hu]) (le_of_abs_le hu)
  simp only [spaceNorm, Fin.sum_univ_three]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have := h x hx
  have := h y hy
  have := h w hw
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  nlinarith
theorem polydiscSlice_subset_slabDomain {η : ℝ} (hη : 0 < η) {a : Fin 4 → ℝ} (ha : |a 3| ≤ η / 2) :
    polydiscSlice (toComplex a) (η / 8) Finset.univ ⊆ slabDomain η := by
  intro w hw
  have hb : ∀ μ, ‖w μ - toComplex a μ‖ ≤ η / 8 := fun μ => (hw μ).1 (Finset.mem_univ μ)
  have him : ∀ μ, |(w μ).im| ≤ η / 8 := fun μ => by
    have := (Complex.abs_im_le_norm _).trans (hb μ)
    simpa [toComplex] using this
  have hre : |(w 3).re| ≤ η / 2 + η / 8 := by
    have h₁ := (Complex.abs_re_le_norm _).trans (hb 3)
    have h₂ : (w 3 - toComplex a 3).re = (w 3).re - a 3 := by simp [toComplex]
    rw [h₂] at h₁
    calc |(w 3).re| = |((w 3).re - a 3) + a 3| := by ring_nf
      _ ≤ |(w 3).re - a 3| + |a 3| := abs_add_le _ _
      _ ≤ _ := by linarith
  apply mem_slabDomain
  have := spaceNorm_le (by positivity) (him 0) (him 1) (him 2)
  linarith
theorem norm_slabCoeff_le {E : FourBorelSet → BddOp K} {Ω : K}
    (hC : IsContractionSemigroup E Ω) (A : BddOp K) (χ χ' : K) {η : ℝ}
    {z : ComplexVec4} (hz : z ∈ slabDomain η) :
    ‖slabCoeff E A χ χ' η z‖ ≤ ‖χ‖ * ‖A‖ * ‖χ'‖ := by
  have hT : ∀ ζ ∈ futureTube, ‖spectralTranslation E ζ‖ ≤ 1 := fun ζ hζ =>
    (hC.1 ζ ζ (imInClosedCone_of_mem_futureTube hζ) (imInClosedCone_of_mem_futureTube hζ)).1
  have h₂ : ‖spectralTranslation E (wickMinus η z) χ'‖ ≤ ‖χ'‖ := by
    calc _ ≤ ‖spectralTranslation E (wickMinus η z)‖ * ‖χ'‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖χ'‖ := by gcongr; exact hT _ hz.2
      _ = _ := one_mul _
  have h₃ : ‖A (spectralTranslation E (wickMinus η z) χ')‖ ≤ ‖A‖ * ‖χ'‖ :=
    (A.le_opNorm _).trans (by gcongr)
  have h₄ : ‖spectralTranslation E (wickPlus η z)
      (A (spectralTranslation E (wickMinus η z) χ'))‖ ≤ ‖A‖ * ‖χ'‖ := by
    calc _ ≤ ‖spectralTranslation E (wickPlus η z)‖ * _ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (‖A‖ * ‖χ'‖) := by
        gcongr
        exact hT _ hz.1
      _ = _ := one_mul _
  calc _ ≤ ‖χ‖ * _ := norm_inner_le_norm _ _
    _ ≤ ‖χ‖ * (‖A‖ * ‖χ'‖) := by gcongr
    _ = _ := by ring
end MatrixCoefficients
section MainArgument
open Set MinkowskiSpace FieldForms FieldFormTranslations FieldFormConditions ProjectionMeasures HilbertToolkit OneLoopNotation InsertedFieldForm SesquilinearForms Coordinates
theorem cCubedPartial_add {O : Set (Fin 4 → ℂ)} {G₁ G₂ G₃ : (Fin 4 → ℂ) → ℂ}
    (h₁ : SmoothCLinearOn O G₁) (h₂ : SmoothCLinearOn O G₂)
    (hO : IsOpen O) (he : EqOn G₃ (fun z => G₁ z + G₂ z) O) (Γ : Finset (Fin 4)) {w : Fin 4 → ℂ}
    (hw : w ∈ O) :
    cCubedPartial Γ G₃ w = cCubedPartial Γ G₁ w + cCubedPartial Γ G₂ w := by
  have := cCubedPartial_linear_comb h₁ h₂ hO 1 (fun z hz => by simpa using he hz) Γ hw
  simpa using this
theorem cCubedPartial_smul {O : Set (Fin 4 → ℂ)} {G₁ G₃ : (Fin 4 → ℂ) → ℂ}
    (h₁ : SmoothCLinearOn O G₁) (hO : IsOpen O) (c : ℂ)
    (he : EqOn G₃ (fun z => c * G₁ z) O) (Γ : Finset (Fin 4)) {w : Fin 4 → ℂ} (hw : w ∈ O) :
    cCubedPartial Γ G₃ w = c * cCubedPartial Γ G₁ w := by
  have h₀ : SmoothCLinearOn O (fun _ => 0) :=
    ⟨contDiffOn_const, fun w _ v => by simp⟩
  have hz := cCubedPartial_linear_comb h₀ h₀ hO 1 (G₃ := fun _ => 0)
    (fun z _ => by simp) Γ hw
  have hzero : cCubedPartial Γ (fun _ => 0) w = 0 := by
    simpa using hz
  have := cCubedPartial_linear_comb h₁ h₀ hO c (fun z hz => by simpa using he hz) Γ hw
  simpa [hzero] using this
theorem supC1Norm_translateFun (a : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℂ) :
    WightmanReconstruction.supC1Norm (translateFun a f) = WightmanReconstruction.supC1Norm f := by
  have hp : ∀ μ x, TestFunctions.partialDerivR4 μ (translateFun a f) x =
      TestFunctions.partialDerivR4 μ f (x - a) := by
    intro μ x
    unfold TestFunctions.partialDerivR4
    congr 1
    funext t
    simp only [translateFun]
    congr 1
    abel
  have h₁ : TestFunctions.uniformNorm (translateFun a f) = TestFunctions.uniformNorm f :=
    (Equiv.subRight a).iSup_comp (g := fun x => ‖f x‖)
  have h₂ : (⨆ x, Real.sqrt (∑ μ, ‖TestFunctions.partialDerivR4 μ (translateFun a f) x‖ ^ 2)) =
      ⨆ x, Real.sqrt (∑ μ, ‖TestFunctions.partialDerivR4 μ f x‖ ^ 2) := by
    simp_rw [hp]
    exact (Equiv.subRight a).iSup_comp
      (g := fun x => Real.sqrt (∑ μ, ‖TestFunctions.partialDerivR4 μ f x‖ ^ 2))
  unfold WightmanReconstruction.supC1Norm
  rw [h₁, h₂]
theorem cubeKernelConst_nonneg : 0 ≤ CubeKernels.cubeKernelConst := by
  unfold CubeKernels.cubeKernelConst
  have : (0 : ℝ) ≤ max 1 (max (TestFunctions.uniformNorm CubeKernels.quadBump)
      (max (TestFunctions.uniformNorm (deriv CubeKernels.quadBump))
        (max (TestFunctions.uniformNorm CubeKernels.thirdDerivBump)
          (TestFunctions.uniformNorm (deriv CubeKernels.thirdDerivBump))))) :=
    zero_le_one.trans (le_max_left _ _)
  positivity
theorem sum_six_pow_card : ∑ Γ : Finset (Fin 4), (6 : ℝ) ^ Γ.card = 7 ^ 4 := by
  have := Finset.sum_pow_mul_eq_add_pow (6 : ℝ) 1 (Finset.univ : Finset (Fin 4))
  rw [Finset.powerset_univ] at this
  simp only [one_pow, mul_one, Finset.card_univ, Fintype.card_fin] at this
  rw [this]
  norm_num
theorem cauchy_factor_eq {η : ℝ} (hη : 0 < η) (n : ℕ) (p : ℝ) :
    (6 / (η / 8) ^ 3) ^ n * (η ^ (-p) * (η / 8) ^ (3 * (n : ℤ) - 5)) =
      6 ^ n * (8 ^ 5 * η ^ (-p - 5)) := by
  have hr : η / 8 ≠ 0 := by positivity
  have h₁ : (η / 8) ^ (3 * (n : ℤ) - 5) = ((η / 8) ^ 3) ^ n / (η / 8) ^ 5 := by
    rw [zpow_sub₀ hr]
    congr 1
    · rw [← pow_mul]
      exact_mod_cast zpow_natCast (η / 8) (3 * n)
  have h₂ : η ^ (-p - 5) = η ^ (-p) / η ^ 5 := by
    rw [Real.rpow_sub hη]
    congr 1
    exact_mod_cast Real.rpow_natCast η 5
  rw [h₁, h₂, div_pow]
  field_simp
theorem regularity_holds (hMX : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hT : FieldFormTranslations.TranslationOperatorFacts)
    (hNF : InsertedFieldForm.ZeroFieldForm)
    (hIns : InsertionOperators.InsertionOperatorBounds)
    (hConj : InsertedFieldForm.KernelInsertionConjugation)
    (hKer : CubeKernels.KernelFacts)
    (hH : HilbertToolkit.HilbertCompletionExtensionRiesz) : Regularity := by
  intro σ E p C hc η hη hη1
  obtain ⟨hCt, hLt, hMt⟩ := hT (StateSpace σ) E (vacuumState σ) (fun _ => 0) 0 1 (hNF σ E p C hc)
  have htube : IsOpen futureTube := (hMt 0 0).1
  have hSo : IsOpen (slabDomain η) := isOpen_slabDomain η htube
  set U : Set (Fin 4 → ℝ) := {a | |a TimeAxis.timeIdx| < η} with hUdef
  have hUo : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hUS : MapsTo toComplex U (slabDomain η) := fun a ha => toComplex_mem_slabDomain ha
  have hofR : ContDiff ℝ ∞ (toComplex : (Fin 4 → ℝ) → ComplexVec4) :=
    contDiff_pi.2 fun μ => Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ μ)
  let el : Finset (Fin 4) → StateSpace σ → StateSpace σ → ComplexVec4 → ℂ :=
    fun Γ χ χ' => slabCoeff E (kernelInsertion σ η Γ) χ χ' η
  have hel : ∀ Γ χ χ', SmoothCLinearOn (slabDomain η) (el Γ χ χ') :=
    fun Γ χ χ' => smoothCLinearOn_slabCoeff hMX hLt hMt _ χ χ' η
  have hre : ∀ Γ χ χ' a, ⟪χ, conjKernelInsertion σ E η Γ a χ'⟫_ℂ = el Γ χ χ' (toComplex a) := by
    intro Γ χ χ' a
    have h₁ : realWickPoint (η • timeUnitVec + a) = wickPlus η (toComplex a) := by
      simp only [realWickPoint, wickPlus, timeShift]
      congr 1
      funext μ
      simp [toComplex]
    have h₂ : realWickPoint (η • timeUnitVec - a) = wickMinus η (toComplex a) := by
      simp only [realWickPoint, wickMinus, timeShift]
      congr 1
      funext μ
      simp [toComplex]
    simp only [conjKernelInsertion, h₁, h₂]
    rfl
  have hthird : ∀ Γ χ χ', EqOn (CubeKernels.cubedPartial Γ
      (fun a' => ⟪χ, conjKernelInsertion σ E η Γ a' χ'⟫_ℂ))
      (cCubedPartial Γ (el Γ χ χ') ∘ toComplex) U := fun Γ χ χ' =>
    cubedPartial_eqOn (hel Γ χ χ') hSo hUo hUS (fun a _ => hre Γ χ χ' a) Γ
  have hval : ∀ a ∈ U, ∀ χ χ', smoothedPairing σ E η a χ χ' =
      ∑ Γ : Finset (Fin 4), (-1 : ℂ) ^ Γ.card * cCubedPartial Γ (el Γ χ χ') (toComplex a) := by
    intro a ha χ χ'
    unfold smoothedPairing
    refine Finset.sum_congr rfl fun Γ _ => ?_
    rw [hthird Γ χ χ' ha]
    rfl
  have hform : ∀ a ∈ U, IsSesqForm fun χ χ' => smoothedPairing σ E η a χ χ' := by
    intro a ha
    have hw := hUS ha
    refine ⟨fun F₁ F₂ F' => ?_, fun c F F' => ?_, fun F F₁ F₂ => ?_, fun c F F' => ?_⟩
    · simp only [hval a ha]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun Γ _ => ?_
      rw [cCubedPartial_add (hel Γ F₁ F') (hel Γ F₂ F') hSo
        (fun z _ => by simp [el, slabCoeff]) Γ hw]
      ring
    · simp only [hval a ha]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun Γ _ => ?_
      rw [cCubedPartial_smul (hel Γ F F') hSo ((starRingEnd ℂ) c)
        (fun z _ => by simp [el, slabCoeff, mul_comm]) Γ hw]
      ring
    · simp only [hval a ha]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun Γ _ => ?_
      rw [cCubedPartial_add (hel Γ F F₁) (hel Γ F F₂) hSo
        (fun z _ => by simp [el, slabCoeff, map_add]) Γ hw]
      ring
    · simp only [hval a ha]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun Γ _ => ?_
      rw [cCubedPartial_smul (hel Γ F F') hSo c
        (fun z _ => by simp [el, slabCoeff, map_smul]) Γ hw]
      ring
  have hIns' := hIns σ E p C hc η hη hη1
  obtain ⟨-, -, -, hNorm⟩ := hKer
  have hA : ∀ Γ : Finset (Fin 4), ‖kernelInsertion σ η Γ‖ ≤
      C * (η ^ (-p) * (CubeKernels.cubeKernelConst *
        (η / 8) ^ (3 * (Γ.card : ℤ) - 5))) := by
    intro Γ
    have hadm := (hConj σ E p C hc η Γ 0 hη hη1 (by simp; positivity)).1
    rw [add_zero] at hadm
    have h₁ := (hIns'.1 _ hadm).2
    have h₂ := hNorm Γ (η / 8) (by positivity) (by linarith)
    rw [supC1Norm_translateFun] at h₁
    have hC0 : 0 ≤ C := zero_le_one.trans hc.one_le_const
    calc ‖kernelInsertion σ η Γ‖ ≤ C * η ^ (-p) *
          WightmanReconstruction.supC1Norm (scaledKernel η Γ) := h₁
      _ ≤ C * η ^ (-p) * (CubeKernels.cubeKernelConst *
            (η / 8) ^ (3 * (Γ.card : ℤ) - 5)) := by
          gcongr
          exact h₂
      _ = _ := by ring
  have hC0 : 0 ≤ C := zero_le_one.trans hc.one_le_const
  have hκ := cubeKernelConst_nonneg
  set cc : ℝ := 8 ^ 5 * CubeKernels.cubeKernelConst * C * η ^ (-p - 5) with hcc
  have hcc0 : 0 ≤ cc := by positivity
  have hterm : ∀ (a : Fin 4 → ℝ), |a 3| ≤ η / 2 → ∀ (Γ : Finset (Fin 4)) (χ χ' : StateSpace σ),
      ‖cCubedPartial Γ (el Γ χ χ') (toComplex a)‖ ≤ 6 ^ Γ.card * cc * (‖χ‖ * ‖χ'‖) := by
    intro a ha Γ χ χ'
    have h₁ := norm_cCubedPartial_le Γ (hel Γ χ χ') hSo (toComplex a) (r := η / 8)
      (B := ‖χ‖ * ‖kernelInsertion σ η Γ‖ * ‖χ'‖) (by positivity)
      (polydiscSlice_subset_slabDomain hη ha) (fun w hw => norm_slabCoeff_le hCt _ χ χ' hw)
    refine h₁.trans ?_
    have hx : 0 ≤ (6 / (η / 8) ^ 3) ^ Γ.card := by positivity
    calc _ ≤ (6 / (η / 8) ^ 3) ^ Γ.card * (‖χ‖ * (C * (η ^ (-p) *
            (CubeKernels.cubeKernelConst * (η / 8) ^ (3 * (Γ.card : ℤ) - 5)))) * ‖χ'‖) := by
          gcongr
          exact hA Γ
      _ = ((6 / (η / 8) ^ 3) ^ Γ.card * (η ^ (-p) * (η / 8) ^ (3 * (Γ.card : ℤ) - 5))) *
            (CubeKernels.cubeKernelConst * C * (‖χ‖ * ‖χ'‖)) := by ring
      _ = _ := by
          rw [cauchy_factor_eq hη, hcc]
          ring
  have hbound : ∀ (a : Fin 4 → ℝ), |a 3| ≤ η / 2 → ∀ χ χ' : StateSpace σ,
      ‖smoothedPairing σ E η a χ χ'‖ ≤ smoothedFieldConst C * η ^ (-p - 5) * ‖χ‖ * ‖χ'‖ := by
    intro a ha χ χ'
    have haU : a ∈ U := show |a 3| < η by linarith
    rw [hval a haU]
    calc _ ≤ ∑ Γ : Finset (Fin 4), ‖(-1 : ℂ) ^ Γ.card * cCubedPartial Γ (el Γ χ χ') (toComplex a)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ Γ : Finset (Fin 4), 6 ^ Γ.card * cc * (‖χ‖ * ‖χ'‖) := by
          refine Finset.sum_le_sum fun Γ _ => ?_
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact hterm a ha Γ χ χ'
      _ = (∑ Γ : Finset (Fin 4), (6 : ℝ) ^ Γ.card) * cc * (‖χ‖ * ‖χ'‖) := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ = _ := by
          rw [sum_six_pow_card, hcc, smoothedFieldConst]
          ring
  have hconc : ∀ (a : Fin 4 → ℝ), |a 3| ≤ η / 2 →
      RepresentsForm (fun χ χ' => smoothedPairing σ E η a χ χ') (smoothedFieldOp σ E η a) ∧
        opNormOf (smoothedFieldOp σ E η a) ≤ smoothedFieldConst C * η ^ (-p - 5) := by
    intro a ha
    have haU : a ∈ U := show |a 3| < η by linarith
    have hc0 : 0 ≤ smoothedFieldConst C * η ^ (-p - 5) := by
      rw [smoothedFieldConst]
      positivity
    obtain ⟨⟨A, hAg, -⟩, hAn⟩ := hH.2.2.2.2.1 (StateSpace σ) _ _ hc0 (hform a haU) (hbound a ha)
    have hsp : RepresentsForm (fun χ χ' => smoothedPairing σ E η a χ χ') (smoothedFieldOp σ E η a) :=
      Classical.epsilon_spec (p := RepresentsForm fun χ χ' => smoothedPairing σ E η a χ χ') ⟨A, hAg⟩
    exact ⟨hsp, hAn _ hsp⟩
  refine ⟨fun Γ χ χ' => ?_, hconc, fun χ χ' => ?_⟩
  · have h₁ : ContDiffOn ℝ ∞ (el Γ χ χ' ∘ toComplex) U :=
      (hel Γ χ χ').contDiffOn.comp hofR.contDiffOn hUS
    exact h₁.congr fun a _ => hre Γ χ χ' a
  · have hsub : {a : Fin 4 → ℝ | |a TimeAxis.timeIdx| ≤ η / 2} ⊆ U := fun a ha =>
      show |a 3| < η from lt_of_le_of_lt ha (by linarith)
    have hcont : ContinuousOn (fun a => ∑ Γ : Finset (Fin 4),
        (-1 : ℂ) ^ Γ.card * cCubedPartial Γ (el Γ χ χ') (toComplex a)) U := by
      refine continuousOn_finsetSum _ fun Γ _ => continuousOn_const.mul ?_
      exact (smoothCLinearOn_cCubedPartial (hel Γ χ χ') hSo Γ).contDiffOn.continuousOn.comp
        hofR.continuous.continuousOn hUS
    refine (hcont.mono hsub).congr fun a ha => ?_
    exact ((hconc a ha).1 χ χ').trans (hval a (hsub ha) χ χ')
end MainArgument
end YangMills.Construction.SmoothedKernelField
end
