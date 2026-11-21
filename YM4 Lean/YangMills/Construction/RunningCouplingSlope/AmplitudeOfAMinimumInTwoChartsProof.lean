import YangMills.Construction.RunningCouplingSlope.AmplitudeOfAMinimumInTwoCharts
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Matrix
open Filter
namespace YangMills.Construction.Slope
namespace ChartChange
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {Ci : Type} [Fintype Ci] [DecidableEq Ci]
private def coordJacobian (c : X ≃ₗ[ℝ] (Ci → ℝ)) (Φ : X → X) : Matrix Ci Ci ℝ :=
  Matrix.of fun i j => c (fderiv ℝ Φ 0 (c.symm (Pi.single j 1))) i
private theorem eq_sum_coords (c : X ≃ₗ[ℝ] (Ci → ℝ)) (v : X) :
    v = ∑ i, c v i • c.symm (Pi.single i 1) := by
  apply c.injective
  simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
  ext j
  simp [Finset.sum_apply, Pi.single_apply]
private theorem apply_eq_sum_coords (c : X ≃ₗ[ℝ] (Ci → ℝ)) (L : X →L[ℝ] ℝ) (v : X) :
    L v = ∑ i, c v i * L (c.symm (Pi.single i 1)) := by
  conv_lhs => rw [eq_sum_coords c v]
  simp [map_sum]
private theorem coords_fderiv_eq_mulVec (c : X ≃ₗ[ℝ] (Ci → ℝ)) (Φ : X → X) (v : X) :
    c (fderiv ℝ Φ 0 v) = coordJacobian c Φ *ᵥ c v := by
  conv_lhs => rw [eq_sum_coords c v]
  ext i
  simp [map_sum, coordJacobian, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
private theorem differentiableAt_partial (c : X ≃ₗ[ℝ] (Ci → ℝ)) (f : X → ℝ)
    (hpd : (hessianMatrix c f).PosDef) (i : Ci) :
    DifferentiableAt ℝ (fun ζ => fderiv ℝ f ζ (c.symm (Pi.single i 1))) 0 := by
  by_contra hnd
  have h0 : hessianMatrix c f i i = 0 := by
    simp [hessianMatrix, fderiv_zero_of_not_differentiableAt hnd]
  have := hpd.diag_pos (i := i)
  linarith
private theorem eventually_differentiableAt_punctured (c : X ≃ₗ[ℝ] (Ci → ℝ)) (f : X → ℝ)
    (hpd : (hessianMatrix c f).PosDef)
    (hmin : IsLocalMin f 0) : ∀ᶠ y in 𝓝[≠] (0 : X), DifferentiableAt ℝ f y := by
  let g : Ci → X → ℝ := fun i ζ => fderiv ℝ f ζ (c.symm (Pi.single i 1))
  have hgd : ∀ i, DifferentiableAt ℝ (g i) 0 := differentiableAt_partial c f hpd
  let B : X →L[ℝ] (Ci → ℝ) := ContinuousLinearMap.pi fun i => fderiv ℝ (g i) 0
  have hB : HasFDerivAt (fun ζ i => g i ζ) B 0 :=
    hasFDerivAt_pi.2 fun i => (hgd i).hasFDerivAt
  have hBv : ∀ v, B v = hessianMatrix c f *ᵥ c v := by
    intro v
    ext i
    change fderiv ℝ (g i) 0 v = _
    rw [apply_eq_sum_coords c _ v]
    simp [Matrix.mulVec, dotProduct, hessianMatrix, mul_comm, g]
  have hinj : Function.Injective (B : X →ₗ[ℝ] (Ci → ℝ)) := by
    intro a b hab
    have h1 : hessianMatrix c f *ᵥ (c a - c b) = 0 := by
      have : B a = B b := hab
      rw [hBv, hBv] at this
      rw [Matrix.mulVec_sub, this, sub_self]
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hpd.det_pos.ne' h1
    exact c.injective (sub_eq_zero.mp h2)
  obtain ⟨K, -, hK⟩ := (B : X →ₗ[ℝ] (Ci → ℝ)).injective_iff_antilipschitz.mp hinj
  have hne := hB.eventually_ne (c := fun i => g i 0) ⟨K, hK⟩
  filter_upwards [hne] with y hy
  by_contra hnd
  apply hy
  ext i
  simp [g, fderiv_zero_of_not_differentiableAt hnd, hmin.fderiv_eq_zero]
private theorem hessianMatrix_eq_of_comp (c : X ≃ₗ[ℝ] (Ci → ℝ)) (f f' : X → ℝ) (Φ : X → X)
    (hΦ : ContDiffAt ℝ 2 Φ 0) (hΦ0 : Φ 0 = 0) (hJ : Function.Injective (fderiv ℝ Φ 0))
    (hf : f =ᶠ[𝓝 0] f' ∘ Φ) (hmin : IsLocalMin f 0) (hmin' : IsLocalMin f' 0)
    (hpd : (hessianMatrix c f').PosDef) :
    hessianMatrix c f = (coordJacobian c Φ)ᵀ * hessianMatrix c f' * coordJacobian c Φ := by
  let g : Ci → X → ℝ := fun i ζ => fderiv ℝ f' ζ (c.symm (Pi.single i 1))
  have hgd : ∀ i, DifferentiableAt ℝ (g i) 0 := differentiableAt_partial c f' hpd
  have hg0 : ∀ i, g i 0 = 0 := by
    intro i
    simp [g, hmin'.fderiv_eq_zero]
  have hdiff := eventually_differentiableAt_punctured c f' hpd hmin'
  have hΦd : HasFDerivAt Φ (fderiv ℝ Φ 0) 0 := (hΦ.differentiableAt (by norm_num)).hasFDerivAt
  have hanti : ∃ C, AntilipschitzWith C (fderiv ℝ Φ 0) := by
    obtain ⟨K, -, hK⟩ :=
      ((fderiv ℝ Φ 0 : X →L[ℝ] X) : X →ₗ[ℝ] X).injective_iff_antilipschitz.mp hJ
    exact ⟨K, hK⟩
  have htend : Tendsto Φ (𝓝[≠] 0) (𝓝[≠] 0) := by
    simpa [hΦ0] using hΦd.tendsto_nhdsNE hanti
  have h1 : ∀ᶠ ζ in 𝓝 (0 : X), ζ ≠ 0 → DifferentiableAt ℝ f' (Φ ζ) :=
    eventually_nhdsWithin_iff.mp (htend.eventually hdiff)
  have h2 : ∀ᶠ ζ in 𝓝 (0 : X), DifferentiableAt ℝ Φ ζ :=
    (hΦ.eventually (by simp)).mono fun ζ h => h.differentiableAt (by norm_num)
  have h3 : ∀ᶠ ζ in 𝓝 (0 : X), fderiv ℝ f ζ = fderiv ℝ (f' ∘ Φ) ζ :=
    hf.eventuallyEq_nhds.mono fun ζ h => h.fderiv_eq
  have key : ∀ v, (fun ζ => fderiv ℝ f ζ v) =ᶠ[𝓝 0]
      fun ζ => ∑ i, c (fderiv ℝ Φ ζ v) i * g i (Φ ζ) := by
    intro v
    filter_upwards [h1, h2, h3] with ζ ha hb hc
    by_cases hz : ζ = 0
    · subst hz
      simp [hmin.fderiv_eq_zero, hΦ0, hg0]
    · rw [hc, fderiv_comp ζ (ha hz) hb]
      simp only [ContinuousLinearMap.comp_apply]
      exact apply_eq_sum_coords c _ _
  have hΦ2 : DifferentiableAt ℝ (fderiv ℝ Φ) 0 :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let ℓ : Ci → X →L[ℝ] ℝ := fun i =>
    LinearMap.toContinuousLinearMap ((LinearMap.proj i : (Ci → ℝ) →ₗ[ℝ] ℝ) ∘ₗ c.toLinearMap)
  have val : ∀ v w, fderiv ℝ (fun ζ => fderiv ℝ f ζ v) 0 w =
      ∑ i, c (fderiv ℝ Φ 0 v) i * fderiv ℝ (g i) 0 (fderiv ℝ Φ 0 w) := by
    intro v w
    rw [(key v).fderiv_eq]
    have hv : DifferentiableAt ℝ (fun ζ => fderiv ℝ Φ ζ v) 0 :=
      hΦ2.clm_apply (differentiableAt_const v)
    have ha : ∀ i, DifferentiableAt ℝ (fun ζ => c (fderiv ℝ Φ ζ v) i) 0 := fun i =>
      (ℓ i).differentiableAt.comp (0 : X) hv
    have hb : ∀ i, HasFDerivAt (fun ζ => g i (Φ ζ)) ((fderiv ℝ (g i) 0).comp (fderiv ℝ Φ 0)) 0 := by
      intro i
      have hgi : HasFDerivAt (g i) (fderiv ℝ (g i) 0) (Φ 0) := by
        rw [hΦ0]
        exact (hgd i).hasFDerivAt
      exact hgi.comp (0 : X) hΦd
    have hsum : HasFDerivAt (fun ζ => ∑ i, c (fderiv ℝ Φ ζ v) i * g i (Φ ζ))
        (∑ i, (c (fderiv ℝ Φ 0 v) i • ((fderiv ℝ (g i) 0).comp (fderiv ℝ Φ 0)) +
          g i (Φ 0) • fderiv ℝ (fun ζ => c (fderiv ℝ Φ ζ v) i) 0)) 0 :=
      HasFDerivAt.fun_sum fun i _ => (ha i).hasFDerivAt.mul (hb i)
    rw [hsum.fderiv]
    simp [hΦ0, hg0]
  ext a b
  have hexp : ∀ i, fderiv ℝ (g i) 0 (fderiv ℝ Φ 0 (c.symm (Pi.single b 1))) =
      ∑ j, c (fderiv ℝ Φ 0 (c.symm (Pi.single b 1))) j * hessianMatrix c f' i j := fun i =>
    apply_eq_sum_coords c _ _
  have hl : hessianMatrix c f a b = fderiv ℝ (fun ζ => fderiv ℝ f ζ (c.symm (Pi.single a 1))) 0
      (c.symm (Pi.single b 1)) := rfl
  rw [hl, val]
  simp only [hexp, Matrix.mul_apply, Matrix.transpose_apply, coordJacobian, Matrix.of_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring
variable {Oi Ti : Type} [Fintype Oi] [DecidableEq Oi] [Fintype Ti] [DecidableEq Ti]
private theorem exists_local_lift (c : X ≃ₗ[ℝ] (Ci → ℝ)) (e : Ci ⊕ Oi ≃ Ti)
    (Ψ : X × (Oi → ℝ) → Ti → ℝ) (ν : X → Ti → ℝ) (P' : Matrix Ti Ci ℝ) (D' : Matrix Ti Oi ℝ)
    (hΨ : ContDiffAt ℝ 2 Ψ 0) (hΨ0 : Ψ 0 = 0)
    (hdΨ : ∀ x z, fderiv ℝ Ψ 0 (x, z) = P' *ᵥ c x + D' *ᵥ z)
    (hν : ContDiffAt ℝ 2 ν 0) (hν0 : ν 0 = 0)
    (hdet : ((Matrix.fromCols P' D').submatrix id e.symm).det ≠ 0) :
    ∃ W : X → X × (Oi → ℝ), ContDiffAt ℝ 2 W 0 ∧ W 0 = 0 ∧ (∀ᶠ x in 𝓝 0, Ψ (W x) = ν x) ∧
      ∀ x, fderiv ℝ Ψ 0 (fderiv ℝ W 0 x) = fderiv ℝ ν 0 x := by
  have : CompleteSpace X := FiniteDimensional.complete ℝ X
  have hinj : Function.Injective ((fderiv ℝ Ψ 0 : X × (Oi → ℝ) →L[ℝ] (Ti → ℝ)) :
      X × (Oi → ℝ) →ₗ[ℝ] (Ti → ℝ)) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, z⟩ h
    have h0 : P' *ᵥ c x + D' *ᵥ z = 0 := by
      rw [← hdΨ]
      exact h
    have h1 : (Matrix.fromCols P' D').submatrix id e.symm *ᵥ (Sum.elim (c x) z ∘ e.symm) = 0 := by
      rw [← h0]
      ext t
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Function.comp_apply,
        Pi.add_apply]
      rw [Equiv.sum_comp e.symm fun s => Matrix.fromCols P' D' t s * Sum.elim (c x) z s]
      simp [Fintype.sum_sum_type]
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1
    have hx : c x = 0 := by
      ext i
      simpa using congrFun h2 (e (Sum.inl i))
    have hz : z = 0 := by
      ext i
      simpa using congrFun h2 (e (Sum.inr i))
    have hx0 : x = 0 := by simpa using hx
    simp [hx0, hz]
  have hdim : Module.finrank ℝ (X × (Oi → ℝ)) = Module.finrank ℝ (Ti → ℝ) := by
    rw [Module.finrank_prod, c.finrank_eq]
    simp [Fintype.card_congr e.symm]
  let f₀ : (X × (Oi → ℝ)) ≃ₗ[ℝ] (Ti → ℝ) := LinearMap.linearEquivOfInjective _ hinj hdim
  let f' : (X × (Oi → ℝ)) ≃L[ℝ] (Ti → ℝ) := f₀.toContinuousLinearEquiv
  have hcoe : (f' : (X × (Oi → ℝ)) →L[ℝ] (Ti → ℝ)) = fderiv ℝ Ψ 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact LinearMap.linearEquivOfInjective_apply hinj hdim v
  have hf' : HasFDerivAt Ψ (f' : (X × (Oi → ℝ)) →L[ℝ] (Ti → ℝ)) 0 := by
    rw [hcoe]
    exact (hΨ.differentiableAt (by norm_num)).hasFDerivAt
  have hn : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  let G := hΨ.localInverse hf' hn
  have hG : ContDiffAt ℝ 2 G (Ψ 0) := hΨ.to_localInverse hf' hn
  have hG0 : G 0 = 0 := by
    have := hΨ.localInverse_apply_image hf' hn
    rwa [hΨ0] at this
  have hright : ∀ᶠ y in 𝓝 (Ψ 0), Ψ (G y) = y :=
    (hΨ.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  have hνΨ : ν 0 = Ψ 0 := by rw [hν0, hΨ0]
  have hW : ContDiffAt ℝ 2 (G ∘ ν) 0 := by
    refine ContDiffAt.comp (0 : X) ?_ hν
    rw [hνΨ]
    exact hG
  have hW0 : (G ∘ ν) 0 = 0 := by simp [hν0, hG0]
  have hev : ∀ᶠ x in 𝓝 (0 : X), Ψ ((G ∘ ν) x) = ν x := by
    have ht : Tendsto ν (𝓝 0) (𝓝 (Ψ 0)) := by
      rw [← hνΨ]
      exact hν.continuousAt
    exact ht.eventually hright
  refine ⟨G ∘ ν, hW, hW0, hev, fun x => ?_⟩
  have hWd : HasFDerivAt (G ∘ ν) (fderiv ℝ (G ∘ ν) 0) 0 :=
    (hW.differentiableAt (by norm_num)).hasFDerivAt
  have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ 0) ((G ∘ ν) 0) := by
    rw [hW0]
    exact (hΨ.differentiableAt (by norm_num)).hasFDerivAt
  have hcomp := hΨd.comp (0 : X) hWd
  have heq : (Ψ ∘ (G ∘ ν)) =ᶠ[𝓝 0] ν := hev
  have h2 := (heq.hasFDerivAt_iff.mp hcomp).fderiv
  rw [h2]
  rfl
end ChartChange
open ChartChange in
theorem hessianDetRatioInvariant_holds : HessianDetRatioInvariant := by
  intro X _ _ _ Ci Oi Ti _ _ _ _ _ _ c e S S' Ψ ν P P' D D' Θ R hΨ hΨ0 hdΨ hν hν0 hdν hΘ hR hTD hA hA'
    hagree hm hm' hp
  obtain ⟨W, hW, hW0, hWr, hWd⟩ := exists_local_lift c e Ψ ν P' D' hΨ hΨ0 hdΨ hν hν0 hA'
  let Φ : X → X := fun x => (W x).1
  have hΦ : ContDiffAt ℝ 2 Φ 0 := hW.fst
  have hΦ0 : Φ 0 = 0 := by simp [Φ, hW0]
  have hWh : HasFDerivAt W (fderiv ℝ W 0) 0 := (hW.differentiableAt (by norm_num)).hasFDerivAt
  have hΦd : ∀ x, fderiv ℝ Φ 0 x = (fderiv ℝ W 0 x).1 := by
    intro x
    rw [hWh.fst.fderiv]
    rfl
  let Jm : Matrix Ci Ci ℝ := coordJacobian c Φ
  let Km : Matrix Oi Ci ℝ := Matrix.of fun o j => (fderiv ℝ W 0 (c.symm (Pi.single j 1))).2 o
  have hrel : P' * Jm + D' * Km = Θ * P := by
    ext t j
    have h1 := hWd (c.symm (Pi.single j 1))
    have hpair : fderiv ℝ W 0 (c.symm (Pi.single j 1)) =
        ((fderiv ℝ W 0 (c.symm (Pi.single j 1))).1, (fderiv ℝ W 0 (c.symm (Pi.single j 1))).2) := rfl
    rw [hpair, hdΨ, hdν, LinearEquiv.apply_symm_apply, ← hΦd, Matrix.mulVec_mulVec] at h1
    have h2 := congrFun h1 t
    simpa [Jm, Km, coordJacobian, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using h2
  have hM : Matrix.fromCols P' D' * Matrix.fromBlocks Jm 0 Km R = Θ * Matrix.fromCols P D := by
    rw [Matrix.fromCols_mul_fromBlocks, hrel, Matrix.mul_zero, zero_add, ← hTD, Matrix.mul_fromCols]
  have hd : ((Matrix.fromCols P' D').submatrix id e.symm).det * (Jm.det * R.det) =
      Θ.det * ((Matrix.fromCols P D).submatrix id e.symm).det := by
    have h1 : (Matrix.fromCols P' D').submatrix id e.symm *
        (Matrix.fromBlocks Jm 0 Km R).submatrix e.symm e.symm =
        Θ * (Matrix.fromCols P D).submatrix id e.symm := by
      have h2 : (Matrix.fromCols P' D').submatrix id e.symm *
          (Matrix.fromBlocks Jm 0 Km R).submatrix e.symm e.symm =
          (Matrix.fromCols P' D' * Matrix.fromBlocks Jm 0 Km R).submatrix id e.symm :=
        Matrix.submatrix_mul_equiv _ _ _ _ _
      rw [h2, hM]
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
    have h3 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self,
      Matrix.det_fromBlocks_zero₁₂] at h3
    exact h3
  have hΘ2 : Θ.det ^ 2 = 1 := by
    have := congrArg Matrix.det hΘ
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rw [sq]
    exact this
  have hR2 : R.det ^ 2 = 1 := by
    have := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rw [sq]
    exact this
  have hJ0 : Jm.det ≠ 0 := by
    intro h0
    have hΘ0 : Θ.det ≠ 0 := by
      intro h
      rw [h] at hΘ2
      norm_num at hΘ2
    rw [h0, zero_mul, mul_zero] at hd
    exact (mul_ne_zero hΘ0 hA) hd.symm
  have hJinj : Function.Injective (fderiv ℝ Φ 0) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : Jm *ᵥ c v = 0 := by
      rw [← coords_fderiv_eq_mulVec, hv, map_zero]
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hJ0 h1
    simpa using h2
  have hS : S =ᶠ[𝓝 0] S' ∘ Φ := by
    have ht : Tendsto (fun x => (W x, x)) (𝓝 (0 : X)) (𝓝 ((0 : X × (Oi → ℝ)), (0 : X))) := by
      have hc : Tendsto W (𝓝 (0 : X)) (𝓝 0) := by
        have := hW.continuousAt.tendsto
        rwa [hW0] at this
      exact hc.prodMk_nhds tendsto_id
    filter_upwards [ht.eventually hagree, hWr] with x h1 h2
    exact (h1 h2).symm
  have hH := hessianMatrix_eq_of_comp c S S' Φ hΦ hΦ0 hJinj hS hm hm' hp
  have hdet : (hessianMatrix c S).det = Jm.det ^ 2 * (hessianMatrix c S').det := by
    rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [hdet]
  have hsq : ((Matrix.fromCols P' D').submatrix id e.symm).det ^ 2 * Jm.det ^ 2 =
      ((Matrix.fromCols P D).submatrix id e.symm).det ^ 2 := by
    have := congrArg (· ^ 2) hd
    simp only [mul_pow, hΘ2, hR2, mul_one, one_mul] at this
    exact this
  linear_combination (hessianMatrix c S').det * hsq
end YangMills.Construction.Slope
end
