import YangMills.Construction.SummableBoundsOfTheFlow.DerivativeOfATurnedDerivative
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.TopFieldDecays
import Mathlib
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation Estimates
namespace TopVariationFieldDecay
instance endoNormedAddCommGroup : NormedAddCommGroup (imaginaryQuaternions →L[ℝ] imaginaryQuaternions) :=
  inferInstance
instance endoNormedSpace : NormedSpace ℝ (imaginaryQuaternions →L[ℝ] imaginaryQuaternions) := inferInstance
instance bilinNormedAddCommGroup :
    NormedAddCommGroup (imaginaryQuaternions →L[ℝ] imaginaryQuaternions →L[ℝ] imaginaryQuaternions) :=
  inferInstance
instance bilinNormedSpace :
    NormedSpace ℝ (imaginaryQuaternions →L[ℝ] imaginaryQuaternions →L[ℝ] imaginaryQuaternions) := inferInstance
variable {P D E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem second_fderiv_comp_apply (G : D → E) (φ : P → D) (x u v : P)
    (hG : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) G (φ x)) (hφ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) φ x) :
    fderiv ℝ (fderiv ℝ (G ∘ φ)) x u v =
      fderiv ℝ (fderiv ℝ G) (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) +
        fderiv ℝ G (φ x) (fderiv ℝ (fderiv ℝ φ) x u v) := by
  have hc : ContinuousAt φ x := hφ.continuousAt
  have h1 : ∀ᶠ q in 𝓝 x, DifferentiableAt ℝ G (φ q) := by
    have := hG.eventually (by simp)
    filter_upwards [hc.eventually this] with q hq
    exact hq.differentiableAt (by simp)
  have h2 : ∀ᶠ q in 𝓝 x, DifferentiableAt ℝ φ q := by
    filter_upwards [hφ.eventually (by simp)] with q hq
    exact hq.differentiableAt (by simp)
  have e : fderiv ℝ (G ∘ φ) =ᶠ[𝓝 x] fun q => (fderiv ℝ G (φ q)).comp (fderiv ℝ φ q) := by
    filter_upwards [h1, h2] with q hq1 hq2
    exact fderiv_comp q hq1 hq2
  have dG : DifferentiableAt ℝ (fderiv ℝ G) (φ x) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have dφ : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have d0 : DifferentiableAt ℝ φ x := hφ.differentiableAt (by simp)
  have hA : HasFDerivAt (fun q => fderiv ℝ G (φ q))
      ((fderiv ℝ (fderiv ℝ G) (φ x)).comp (fderiv ℝ φ x)) x :=
    dG.hasFDerivAt.comp x d0.hasFDerivAt
  have hB := hA.clm_comp dφ.hasFDerivAt
  rw [e.fderiv_eq, hB.fderiv]
  simp [add_comm]
section Shift
variable {Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions} {CT : ℝ}
theorem norm_fderiv_apply_comp_le {φ : P → imaginaryQuaternions} {x : P} (u : P) (X : imaginaryQuaternions)
    (hX : ‖X‖ = 1)
    (hTh : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th (φ x)) (hb : ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j Th (φ x)‖ ≤ CT)
    (hφ : DifferentiableAt ℝ φ x) :
    ‖fderiv ℝ (fun q => Th (φ q) X) x u‖ ≤ CT * ‖fderiv ℝ φ x u‖ := by
  have dT : DifferentiableAt ℝ Th (φ x) := hTh.differentiableAt (by simp)
  have hc : HasFDerivAt (fun q => Th (φ q)) ((fderiv ℝ Th (φ x)).comp (fderiv ℝ φ x)) x :=
    HasFDerivAt.comp (g := Th) (f := φ) x dT.hasFDerivAt hφ.hasFDerivAt
  have h := hc.clm_apply (hasFDerivAt_const X x)
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, ContinuousLinearMap.flip_apply, map_zero,
    zero_add]
  have h1 : ‖fderiv ℝ Th (φ x)‖ ≤ CT := by
    rw [← norm_iteratedFDeriv_one]
    exact hb 1 (by omega)
  have h2 := ContinuousLinearMap.le_opNorm (fderiv ℝ Th (φ x) (fderiv ℝ φ x u)) X
  have h3 := ContinuousLinearMap.le_opNorm (fderiv ℝ Th (φ x)) (fderiv ℝ φ x u)
  rw [hX, mul_one] at h2
  have h4 : ‖fderiv ℝ Th (φ x)‖ * ‖fderiv ℝ φ x u‖ ≤ CT * ‖fderiv ℝ φ x u‖ :=
    mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  linarith
theorem norm_second_fderiv_apply_comp_le {φ : P → imaginaryQuaternions} {x : P} (u v : P)
    (X : imaginaryQuaternions) (hX : ‖X‖ = 1)
    (hTh : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th (φ x)) (hb : ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j Th (φ x)‖ ≤ CT)
    (hφ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) φ x) :
    ‖fderiv ℝ (fderiv ℝ (fun q => Th (φ q) X)) x u v‖ ≤
      CT * (‖fderiv ℝ φ x u‖ * ‖fderiv ℝ φ x v‖ + ‖fderiv ℝ (fderiv ℝ φ) x u v‖) := by
  set ev : (imaginaryQuaternions →L[ℝ] imaginaryQuaternions) →L[ℝ] imaginaryQuaternions :=
    ContinuousLinearMap.apply ℝ imaginaryQuaternions X with hev
  set G : imaginaryQuaternions → imaginaryQuaternions := fun w => ev (Th w) with hG
  have hGs : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) G (φ x) := ev.contDiff.contDiffAt.comp (φ x) hTh
  have e1 : (fun q => Th (φ q) X) = G ∘ φ := rfl
  rw [e1, second_fderiv_comp_apply G φ x u v hGs hφ]
  have hGT : ∀ a b : imaginaryQuaternions,
      fderiv ℝ (fderiv ℝ G) (φ x) a b = fderiv ℝ (fderiv ℝ Th) (φ x) a b X := by
    intro a b
    have h1 := second_fderiv_comp_apply ev Th (φ x) a b ev.contDiff.contDiffAt hTh
    have h2 : fderiv ℝ (fderiv ℝ ev) (Th (φ x)) = 0 := by
      have : fderiv ℝ ev = fun _ => ev := by
        funext y
        exact ev.fderiv
      rw [this]
      simp
    have e2 : ev ∘ Th = G := rfl
    rw [e2] at h1
    rw [h1, h2, ev.fderiv]
    simp [hev]
  have h1T : ∀ a : imaginaryQuaternions, fderiv ℝ G (φ x) a = fderiv ℝ Th (φ x) a X := by
    intro a
    have dT : DifferentiableAt ℝ Th (φ x) := hTh.differentiableAt (by simp)
    have := (ev.hasFDerivAt.comp (φ x) dT.hasFDerivAt).fderiv
    change fderiv ℝ (ev ∘ Th) (φ x) a = _
    rw [this]
    simp [hev]
  rw [hGT, h1T]
  have n1 : ‖fderiv ℝ Th (φ x)‖ ≤ CT := by
    rw [← norm_iteratedFDeriv_one]
    exact hb 1 (by omega)
  have n2 : ‖fderiv ℝ (fderiv ℝ Th) (φ x)‖ ≤ CT := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hb 2 le_rfl
  have t1 : ‖fderiv ℝ (fderiv ℝ Th) (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) X‖ ≤
      CT * (‖fderiv ℝ φ x u‖ * ‖fderiv ℝ φ x v‖) := by
    have a1 := ContinuousLinearMap.le_opNorm (fderiv ℝ (fderiv ℝ Th) (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v)) X
    have a2 := ContinuousLinearMap.le_opNorm (fderiv ℝ (fderiv ℝ Th) (φ x) (fderiv ℝ φ x u)) (fderiv ℝ φ x v)
    have a3 := ContinuousLinearMap.le_opNorm (fderiv ℝ (fderiv ℝ Th) (φ x)) (fderiv ℝ φ x u)
    rw [hX, mul_one] at a1
    refine a1.trans (a2.trans ?_)
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ Th) (φ x)‖ * ‖fderiv ℝ φ x u‖ * ‖fderiv ℝ φ x v‖ :=
          mul_le_mul_of_nonneg_right a3 (norm_nonneg _)
      _ ≤ CT * ‖fderiv ℝ φ x u‖ * ‖fderiv ℝ φ x v‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right n2 (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have t2 : ‖fderiv ℝ Th (φ x) (fderiv ℝ (fderiv ℝ φ) x u v) X‖ ≤ CT * ‖fderiv ℝ (fderiv ℝ φ) x u v‖ := by
    have a1 := ContinuousLinearMap.le_opNorm (fderiv ℝ Th (φ x) (fderiv ℝ (fderiv ℝ φ) x u v)) X
    have a2 := ContinuousLinearMap.le_opNorm (fderiv ℝ Th (φ x)) (fderiv ℝ (fderiv ℝ φ) x u v)
    rw [hX, mul_one] at a1
    exact a1.trans (a2.trans (mul_le_mul_of_nonneg_right n1 (norm_nonneg _)))
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring
end Shift
section Lists
variable {F : BlockFrame}
theorem leftTranslate_bondSpread_zero {j : ℕ} {W : F.GaugeField j} {k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.Construction.Interpolation.TopVariation.leftTranslate_bondSpread_zero <;> assumption
theorem fderiv_bondSpread_single {j k : ℕ} (f : F.GaugeField j → imaginaryQuaternions) (V : F.GaugeField j)
    (c' : Fin k → F.Site j × Fin 4) (X' : Fin k → imaginaryQuaternions) (l : Fin k)
    (hd : DifferentiableAt ℝ (fun τ : Fin k → ℝ => f (leftTranslate (bondSpread c' X' τ) V)) 0) :
    fderiv ℝ (fun τ : Fin k → ℝ => f (leftTranslate (bondSpread c' X' τ) V)) 0 (Pi.single l 1) =
      bondDeriv f V (fun _ : Fin 1 => c' l) (fun _ => X' l) := by
  classical
  unfold bondDeriv
  rw [iteratedFDeriv_one_apply]
  have e : (fun σ : Fin 1 → ℝ => f (leftTranslate (bondSpread (fun _ : Fin 1 => c' l) (fun _ => X' l) σ) V)) =
      (fun τ : Fin k → ℝ => f (leftTranslate (bondSpread c' X' τ) V)) ∘
        fun σ : Fin 1 → ℝ => σ 0 • (Pi.single l 1 : Fin k → ℝ) := by
    funext σ
    have e1 : bondSpread (fun _ : Fin 1 => c' l) (fun _ => X' l) σ =
        bondSpread c' X' (σ 0 • (Pi.single l 1 : Fin k → ℝ)) := by
      funext y i
      simp only [bondSpread, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply]
      rw [Finset.sum_eq_single l]
      · simp
      · intro l' _ hl
        simp [Pi.single_eq_of_ne hl]
      · simp
    simp only [Function.comp]
    rw [e1]
  rw [e]
  have hline : HasFDerivAt (fun σ : Fin 1 → ℝ => σ 0 • (Pi.single l 1 : Fin k → ℝ))
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight (Pi.single l 1)) 0 :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight
      (Pi.single l 1 : Fin k → ℝ)).hasFDerivAt
  have hd' : HasFDerivAt (fun τ : Fin k → ℝ => f (leftTranslate (bondSpread c' X' τ) V))
      (fderiv ℝ (fun τ : Fin k → ℝ => f (leftTranslate (bondSpread c' X' τ) V)) 0)
      ((fun σ : Fin 1 → ℝ => σ 0 • (Pi.single l 1 : Fin k → ℝ)) 0) := by
    simpa using hd.hasFDerivAt
  rw [(hd'.comp (0 : Fin 1 → ℝ) hline).fderiv]
  simp
theorem shifted_term_bound {k : ℕ} {Th : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions}
    {CT r : ℝ} {K : ℕ → ℝ} (f : F.GaugeField F.top → imaginaryQuaternions)
    (V : F.GaugeField F.top) (z : F.Cell) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions)
    (u X : imaginaryQuaternions) (hk : k ≤ 2)
    (hr : 0 ≤ r) (hK : ∀ k, 0 ≤ K k) (hCT : 0 ≤ CT)
    (hTh : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th w)
    (hb : ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 2 → ‖iteratedFDeriv ℝ j Th w‖ ≤ CT)
    (h3 : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ : Fin k → ℝ => f (leftTranslate (bondSpread c' X' τ) V)) 0)
    (h3₁ : ∀ (i : ℕ) (cs : Fin i → F.Site F.top × Fin 4) (Xs : Fin i → imaginaryQuaternions), 1 ≤ i →
      AreUnitVectors Xs → ‖bondDeriv f V cs Xs‖ ≤ K i * Real.exp (-(r * bondListDistance z cs)))
    (hu : ‖f V + u‖ ≤ 1) (hX : ‖X‖ = 1) (hX' : AreUnitVectors X') :
    ContDiffAt ℝ (k : WithTop ℕ∞) (fun τ : Fin k → ℝ => Th (f (leftTranslate (bondSpread c' X' τ) V) + u) X) 0 ∧
    ‖iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => Th (f (leftTranslate (bondSpread c' X' τ) V) + u) X) 0
      (fun l => Pi.single l 1)‖ ≤ CT * (1 + K 1 + K 1 ^ 2 + K 2) * Real.exp (-(r * bondListDistance z c')) := by
  set Ψ : (Fin k → ℝ) → imaginaryQuaternions := fun τ => f (leftTranslate (bondSpread c' X' τ) V) with hΨ
  set φ : (Fin k → ℝ) → imaginaryQuaternions := fun τ => Ψ τ + u with hφ
  have hφ0 : φ 0 = f V + u := by
    simp only [hφ, hΨ, leftTranslate_bondSpread_zero]
  have hφ1 : ‖φ 0‖ ≤ 1 := by rw [hφ0]; exact hu
  have hφs : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) φ 0 := h3.add contDiffAt_const
  have hφ2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) φ 0 := hφs.of_le (by norm_num)
  have hT := hTh _ hφ1
  have hg : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun τ => Th (φ τ) X) 0 :=
    (ContDiffAt.comp (g := Th) (f := φ) (0 : Fin k → ℝ) hT hφ2).clm_apply contDiffAt_const
  refine ⟨hg.of_le (by exact_mod_cast hk), ?_⟩
  have hd : DifferentiableAt ℝ Ψ 0 := h3.differentiableAt (by simp)
  have hfd : ∀ v, fderiv ℝ φ 0 v = fderiv ℝ Ψ 0 v := fun v => by
    simp only [hφ]
    rw [fderiv_add_const]
  have hone : ∀ (l : Fin k), ‖fderiv ℝ φ 0 (Pi.single l 1)‖ ≤
      K 1 * Real.exp (-(r * cellSupDist z (c' l).1)) := by
    intro l
    rw [hfd, fderiv_bondSpread_single f V c' X' l hd]
    have := h3₁ 1 (fun _ => c' l) (fun _ => X' l) le_rfl (fun _ => hX' l)
    have e : bondListDistance z (fun _ : Fin 1 => c' l) = cellSupDist z (c' l).1 := by
      simp [bondListDistance]
    rwa [e] at this
  have hK1 := hK 1
  have hK2 := hK 2
  have hK₁ : K 1 ≤ 1 + K 1 + K 1 ^ 2 + K 2 := by nlinarith [sq_nonneg (K 1)]
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · have hL : bondListDistance z c' = 0 := by simp [bondListDistance]
    rw [hL, iteratedFDeriv_zero_apply]
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    have h1 := ContinuousLinearMap.le_opNorm (Th (φ 0)) X
    have h2 : ‖Th (φ 0)‖ ≤ CT := by
      rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
      exact hb _ 0 hφ1 (by omega)
    rw [hX, mul_one] at h1
    have h3' : CT * 1 ≤ CT * (1 + K 1 + K 1 ^ 2 + K 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (K 1)]) hCT
    linarith
  · rw [iteratedFDeriv_one_apply]
    have h1 := norm_fderiv_apply_comp_le (Pi.single (0 : Fin 1) (1 : ℝ)) X hX hT (fun j hj => hb _ j hφ1 hj)
      (hφ2.differentiableAt (by simp))
    have h2 := hone 0
    have hL : bondListDistance z c' = cellSupDist z (c' 0).1 := by
      simp [bondListDistance]
    rw [hL]
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 hCT).trans ?_)
    have h3' := mul_le_mul_of_nonneg_right hK₁ (Real.exp_pos (-(r * (cellSupDist z (c' 0).1 : ℝ)))).le
    have := mul_le_mul_of_nonneg_left h3' hCT
    nlinarith
  · rw [iteratedFDeriv_two_apply]
    have h1 := norm_second_fderiv_apply_comp_le (Pi.single (0 : Fin 2) (1 : ℝ)) (Pi.single (1 : Fin 2) (1 : ℝ))
      X hX hT (fun j hj => hb _ j hφ1 hj) hφ2
    have hfun : fderiv ℝ φ = fderiv ℝ Ψ := by
      funext y
      simp only [hφ]
      rw [fderiv_add_const]
    have e2 : fderiv ℝ (fderiv ℝ φ) 0 (Pi.single 0 1) (Pi.single 1 1) = bondDeriv f V c' X' := by
      rw [hfun]
      unfold bondDeriv
      rw [iteratedFDeriv_two_apply]
    rw [e2] at h1
    refine h1.trans ?_
    set d₀ : ℝ := (cellSupDist z (c' 0).1 : ℝ)
    set d₁ : ℝ := (cellSupDist z (c' 1).1 : ℝ)
    set L : ℝ := (bondListDistance z c' : ℝ) with hL
    have hLd : L ≤ d₀ + d₁ := by
      have : bondListDistance z c' ≤ cellSupDist z (c' 0).1 + cellSupDist z (c' 1).1 := by
        refine Finset.sup_le fun l _ => ?_
        fin_cases l
        · simp
        · simp
      have h2 : ((bondListDistance z c' : ℕ) : ℝ) ≤
          ((cellSupDist z (c' 0).1 + cellSupDist z (c' 1).1 : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at h2
      exact h2
    have hd0 : 0 ≤ d₀ := Nat.cast_nonneg _
    have hd1 : 0 ≤ d₁ := Nat.cast_nonneg _
    have a0 := hone 0
    have a1 := hone 1
    have a2 := h3₁ 2 c' X' (by omega) hX'
    have hexp : Real.exp (-(r * d₀)) * Real.exp (-(r * d₁)) ≤ Real.exp (-(r * L)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith
    have hprod : ‖fderiv ℝ φ 0 (Pi.single 0 1)‖ * ‖fderiv ℝ φ 0 (Pi.single 1 1)‖ ≤
        K 1 ^ 2 * Real.exp (-(r * L)) := by
      calc _ ≤ (K 1 * Real.exp (-(r * d₀))) * (K 1 * Real.exp (-(r * d₁))) :=
            mul_le_mul a0 a1 (norm_nonneg _) (by positivity)
        _ = K 1 ^ 2 * (Real.exp (-(r * d₀)) * Real.exp (-(r * d₁))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
    have hsum : ‖fderiv ℝ φ 0 (Pi.single 0 1)‖ * ‖fderiv ℝ φ 0 (Pi.single 1 1)‖ + ‖bondDeriv f V c' X'‖ ≤
        (1 + K 1 + K 1 ^ 2 + K 2) * Real.exp (-(r * L)) := by
      have hEp := Real.exp_pos (-(r * L))
      have : (K 1 ^ 2 + K 2) * Real.exp (-(r * L)) ≤ (1 + K 1 + K 1 ^ 2 + K 2) * Real.exp (-(r * L)) :=
        mul_le_mul_of_nonneg_right (by linarith) hEp.le
      nlinarith
    calc _ ≤ CT * ((1 + K 1 + K 1 ^ 2 + K 2) * Real.exp (-(r * L))) := mul_le_mul_of_nonneg_left hsum hCT
      _ = _ := by ring
end Lists
end TopVariationFieldDecay
open TopVariationFieldDecay in
theorem Interpolation.topVariationField_decay (hT : TranslatedDerivativeBound) :
    topVariationFieldDecayStatement := by
  classical
  obtain ⟨M, hM0, hM⟩ := hT
  refine ⟨M, hM0, ?_⟩
  intro F s a ρA r CT m V Th K b c X u k c' X' hper hr hK hCT hThs hThb hAn hdec hu hX hk hX'
  set f := interpolatedFrame s a ρA m b with hf
  set z : F.Cell := enclosingCell b.1 with hz
  set L : ℕ := bondListDistance z (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4) with hL
  have h3 : ∀ (q : ℕ) (c'' : Fin q → F.Site F.top × Fin 4) (X'' : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ : Fin q → ℝ => f (leftTranslate (bondSpread c'' X'' τ) V)) 0 :=
    fun q c'' X'' => (hAn q c'' X'').contDiffAt
  have hE0 := Real.exp_pos (-(r * (L : ℝ)))
  have hKs : 0 ≤ K 1 + K 2 + K 3 := by have := hK 1; have := hK 2; have := hK 3; positivity
  obtain ⟨hHs, hHb⟩ := hM F F.top k f V c X c' X' (fun i bs => K i * Real.exp (-(r * bondListDistance z bs)))
    ((K 1 + K 2 + K 3) * Real.exp (-(r * (L : ℝ)))) hk hper hX hX' (mul_nonneg hKs hE0.le) h3
    (fun i bs Xs h1 _ hXs => hdec i bs Xs h1 hXs) (fun i bs h1 h3' hall => by
      have hLb : L ≤ bondListDistance z bs := by
        refine Finset.sup_le fun l _ => ?_
        obtain ⟨m', hm⟩ := hall l
        rw [hm]
        exact Finset.le_sup (f := fun l => cellSupDist z (bs l).1) (Finset.mem_univ m')
      have hLb' : (L : ℝ) ≤ bondListDistance z bs := by exact_mod_cast hLb
      have hex : Real.exp (-(r * (bondListDistance z bs : ℝ))) ≤ Real.exp (-(r * (L : ℝ))) :=
        Real.exp_le_exp.2 (by nlinarith)
      have hKi : K i ≤ K 1 + K 2 + K 3 := by
        have a1 := hK 1
        have a2 := hK 2
        have a3 := hK 3
        interval_cases i <;> linarith
      exact mul_le_mul hKi hex (Real.exp_pos _).le hKs)
  have hC0 : 0 ≤ CT * (1 + K 1 + K 1 ^ 2 + K 2) := by
    have a1 := hK 1
    have a2 := hK 2
    positivity
  by_cases hcr : IsCrossingBond b ∧ (enclosingCell b.1, b.2) = c
  · obtain ⟨hSs, hSb⟩ := shifted_term_bound f V z c' X' u X hk hr hK hCT hThs hThb (h3 k c' X') hdec hu hX hX'
    have e : (fun τ : Fin k → ℝ =>
          topVariationField (fun w X => Th w X) s a ρA m c X b u (leftTranslate (bondSpread c' X' τ) V)) =
        (fun τ => bondDeriv f (leftTranslate (bondSpread c' X' τ) V) (fun _ : Fin 1 => c) (fun _ => X)) +
        fun τ => Th (f (leftTranslate (bondSpread c' X' τ) V) + u) X := by
      funext τ
      simp only [topVariationField, if_pos hcr, Pi.add_apply]
      rfl
    change ‖iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => topVariationField (fun w X => Th w X) s a ρA m c X b u
      (leftTranslate (bondSpread c' X' τ) V)) 0 (fun l => Pi.single l 1)‖ ≤ _
    rw [e, iteratedFDeriv_add_apply hHs hSs]
    refine (norm_add_le _ _).trans ?_
    have hLL : (L : ℝ) ≤ bondListDistance z c' := by
      have : L ≤ bondListDistance z c' := by
        refine Finset.sup_le fun l _ => ?_
        refine Fin.cases ?_ (fun i => ?_) l
        · have hc : c.1 = z := by rw [← hcr.2]
          simp [hc, cellSupDist]
        · have h := Finset.le_sup (f := fun l => cellSupDist z (c' l).1) (Finset.mem_univ i)
          simpa [bondListDistance] using h
      exact_mod_cast this
    have hex : Real.exp (-(r * (bondListDistance z c' : ℝ))) ≤ Real.exp (-(r * (L : ℝ))) :=
      Real.exp_le_exp.2 (by nlinarith)
    have t2 := hSb.trans (mul_le_mul_of_nonneg_left hex hC0)
    have t1 : ‖iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => bondDeriv f (leftTranslate (bondSpread c' X' τ) V)
        (fun _ : Fin 1 => c) (fun _ => X)) 0 (fun l => Pi.single l 1)‖ ≤
        M * ((K 1 + K 2 + K 3) * Real.exp (-(r * (L : ℝ)))) := hHb
    calc _ ≤ M * ((K 1 + K 2 + K 3) * Real.exp (-(r * (L : ℝ)))) +
          CT * (1 + K 1 + K 1 ^ 2 + K 2) * Real.exp (-(r * (L : ℝ))) := add_le_add t1 t2
      _ = _ := by ring
  · have e : (fun τ : Fin k → ℝ =>
          topVariationField (fun w X => Th w X) s a ρA m c X b u (leftTranslate (bondSpread c' X' τ) V)) =
        fun τ => bondDeriv f (leftTranslate (bondSpread c' X' τ) V) (fun _ : Fin 1 => c) (fun _ => X) := by
      funext τ
      simp only [topVariationField, if_neg hcr, add_zero]
      rfl
    change ‖iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => topVariationField (fun w X => Th w X) s a ρA m c X b u
      (leftTranslate (bondSpread c' X' τ) V)) 0 (fun l => Pi.single l 1)‖ ≤ _
    rw [e]
    have t1 : ‖iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => bondDeriv f (leftTranslate (bondSpread c' X' τ) V)
        (fun _ : Fin 1 => c) (fun _ => X)) 0 (fun l => Pi.single l 1)‖ ≤
        M * ((K 1 + K 2 + K 3) * Real.exp (-(r * (L : ℝ)))) := hHb
    have t2 : 0 ≤ CT * (1 + K 1 + K 1 ^ 2 + K 2) * Real.exp (-(r * (L : ℝ))) := mul_nonneg hC0 hE0.le
    calc _ ≤ M * ((K 1 + K 2 + K 3) * Real.exp (-(r * (L : ℝ)))) +
          CT * (1 + K 1 + K 1 ^ 2 + K 2) * Real.exp (-(r * (L : ℝ))) := by linarith
      _ = _ := by ring
end YangMills.Construction
end
