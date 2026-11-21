import YangMills.Construction.RunningCouplingSlope.SaddleDeterminantInCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
theorem saddleDetInOrthonormalCoords : SaddleDetInOrthonormalCoords := by
  intro V V' I T _ _ _ _ _ _ _ _ _ _ c c' Φ Φ' hc hc' X M Xm Mm hX hM
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c.toCore
  let := c'.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c'.toCore
  unfold YangMills.Construction.GaussianConstraint.saddleDetOfCores
  have hin : ∀ x y : V, inner ℝ x y = ∑ i, Φ x i * Φ y i := hc
  have hin' : ∀ x y : V', inner ℝ x y = ∑ t, Φ' x t * Φ' y t := hc'
  have hsum : ∀ {J : Type} [Fintype J] [DecidableEq J] (f : J → ℂ) (j : J),
      ∑ x, f x * (((Pi.single j (1 : ℝ) : J → ℝ) x : ℝ) : ℂ) = f j := by
    intro J _ _ f j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have hadj : ∀ (y : V') (i : I), ((Φ (LinearMap.adjoint M y) i : ℝ) : ℂ) =
      ∑ t, Mm t i * ((Φ' y t : ℝ) : ℂ) := by
    intro y i
    have e1 : Φ (LinearMap.adjoint M y) i =
        inner ℝ (LinearMap.adjoint M y) (Φ.symm (Pi.single i 1)) := by
      rw [hin]
      simp [Pi.single_apply]
    rw [e1, LinearMap.adjoint_inner_left, hin']
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    have h := hM (Φ.symm (Pi.single i 1)) t
    simp only [LinearEquiv.apply_symm_apply] at h
    rw [hsum] at h
    rw [h, mul_comm]
  set S := YangMills.Construction.GaussianConstraint.saddlePointOperator X M with hS
  set F : Matrix (I ⊕ T) (I ⊕ T) ℂ := Matrix.fromBlocks Xm Mm.transpose Mm 0 with hF
  let Ψ : (V × V') ≃ₗ[ℝ] (I ⊕ T → ℝ) :=
    (Φ.prodCongr Φ').trans (LinearEquiv.sumArrowLequivProdArrow I T ℝ ℝ).symm
  have hΨl : ∀ (z : V × V') i, Ψ z (Sum.inl i) = Φ z.1 i := fun _ _ => rfl
  have hΨr : ∀ (z : V × V') t, Ψ z (Sum.inr t) = Φ' z.2 t := fun _ _ => rfl
  have hact : ∀ (z : V × V') κ, ((Ψ (S z) κ : ℝ) : ℂ) = ∑ κ', F κ κ' * ((Ψ z κ' : ℝ) : ℂ) := by
    intro z κ
    rw [Fintype.sum_sum_type]
    rcases κ with i | t
    · have e : (S z).1 = X z.1 + LinearMap.adjoint M z.2 := rfl
      rw [hΨl, e, map_add, Pi.add_apply, Complex.ofReal_add, hX, hadj]
      simp [hF, hΨl, hΨr]
    · have e : (S z).2 = M z.1 := rfl
      rw [hΨr, e, hM]
      simp [hF, hΨl, hΨr]
  have hdet : LinearMap.det (Ψ.conj S) = LinearMap.det S := LinearMap.det_conj S Ψ
  have hentry : ∀ i j, F i j = ((LinearMap.toMatrix' (Ψ.conj S) i j : ℝ) : ℂ) := by
    intro i j
    have h1 := hact (Ψ.symm (Pi.single j 1)) i
    simp only [LinearEquiv.apply_symm_apply] at h1
    rw [hsum] at h1
    rw [LinearMap.toMatrix'_apply, ← h1]
    simp [LinearEquiv.conj_apply]
  have hFm : F = (LinearMap.toMatrix' (Ψ.conj S)).map Complex.ofRealHom := by
    ext i j
    simp [hentry]
  have h4 : Matrix.det F = ((LinearMap.det S : ℝ) : ℂ) := by
    rw [hFm, ← hdet, ← LinearMap.det_toMatrix' (Ψ.conj S)]
    exact (RingHom.map_det Complex.ofRealHom _).symm
  rw [h4, Complex.norm_real, Real.norm_eq_abs]
end YangMills.Construction.RunningCouplingSlope
end
