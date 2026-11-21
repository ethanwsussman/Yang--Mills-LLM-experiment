import YangMills.Construction.RunningCouplingSlope.ColourCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.GhostOfTheSoftChainIsTheMixedGhost
import YangMills.Construction.RunningCouplingSlope.MapsOfTheBackgroundGaugeInColours
import YangMills.Construction.RunningCouplingSlope.PlainKernelsGiveTheirMaps
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Matrix Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace GhostDeterminant
open Tower PeriodicOperators Matrices
section Blocks
variable {I T : Type} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
private theorem det_fromBlocks_scaled (x y x' y' : ℂ) (A : Matrix I I ℂ) (B : Matrix I T ℂ)
    (C : Matrix T I ℂ) (D : Matrix T T ℂ) :
    det (fromBlocks ((x * x') • A) ((x * y') • B) ((y * x') • C) ((y * y') • D)) =
      x ^ Fintype.card I * y ^ Fintype.card T * det (fromBlocks A B C D) *
        (x' ^ Fintype.card I * y' ^ Fintype.card T) := by
  have e : fromBlocks ((x * x') • A) ((x * y') • B) ((y * x') • C) ((y * y') • D) =
      fromBlocks (x • (1 : Matrix I I ℂ)) 0 0 (y • (1 : Matrix T T ℂ)) * fromBlocks A B C D *
        fromBlocks (x' • (1 : Matrix I I ℂ)) 0 0 (y' • (1 : Matrix T T ℂ)) := by
    simp only [fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, smul_smul]
    congr 1 <;> rw [mul_comm]
  rw [e, det_mul, det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂, det_smul, det_smul,
    det_smul, det_smul, det_one, det_one]
  simp
abbrev _root_.YangMills.SharedProofs.p77281 := @det_fromBlocks_scaled
end Blocks
private theorem abs_det_eq_norm_det_of_action {V J : Type} [AddCommGroup V] [Module ℝ V]
    [Fintype J] [DecidableEq J] (Ψ : V ≃ₗ[ℝ] (J → ℝ)) (m : V →ₗ[ℝ] V) (F : Matrix J J ℂ)
    (h : ∀ v j, ((Ψ (m v) j : ℝ) : ℂ) = ∑ j', F j j' * ((Ψ v j' : ℝ) : ℂ)) :
    |LinearMap.det m| = ‖det F‖ := by
  have hsum : ∀ (f : J → ℂ) (j : J),
      ∑ x, f x * (((Pi.single j (1 : ℝ) : J → ℝ) x : ℝ) : ℂ) = f j := by
    intro f j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have hdet : LinearMap.det (Ψ.conj m) = LinearMap.det m := LinearMap.det_conj m Ψ
  have hentry : ∀ i j, F i j = ((LinearMap.toMatrix' (Ψ.conj m) i j : ℝ) : ℂ) := by
    intro i j
    have h1 := h (Ψ.symm (Pi.single j 1)) i
    simp only [LinearEquiv.apply_symm_apply] at h1
    rw [hsum] at h1
    rw [LinearMap.toMatrix'_apply, ← h1]
    simp [LinearEquiv.conj_apply]
  have hFm : F = (LinearMap.toMatrix' (Ψ.conj m)).map Complex.ofRealHom := by
    ext i j
    simp [hentry]
  have h4 : det F = ((LinearMap.det m : ℝ) : ℂ) := by
    rw [hFm, ← hdet, ← LinearMap.det_toMatrix' (Ψ.conj m)]
    exact (RingHom.map_det Complex.ofRealHom _).symm
  rw [h4, Complex.norm_real, Real.norm_eq_abs]
private theorem ofPauliCoeffs_toPauliCoeffs {σ : Type} {l : σ → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    ofPauliCoeffs (toPauliCoeffs l) = l := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
end GhostDeterminant
open GhostDeterminant Tower PeriodicOperators Matrices in
theorem ghostDeterminantAtQuietPoint_holds (h₁ : PauliCoordsOrthonormal)
    (h₂ : BackgroundGaugeMapsInColourCoeffs)
    (h₃ : MeanKernelsRepresent) :
    GhostDeterminantAtQuietPoint := by
  intro L hL k n hk hn _ _ _ _ _ _ _ _
  classical
  obtain ⟨ΨS, hΨS, -⟩ := (h₁ L n k 0 hL hn (Nat.zero_le _)).2
  obtain ⟨ΨY, hΨY, -⟩ := (h₁ L n k k hL hn le_rfl).2
  have hLpos : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  set η : ℝ := finestMesh L k with hη
  have heta : 0 < η := zpow_pos hLpos _
  have hetaC : ((η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have htop : meshAt L k k = 1 := by
    change (L : ℝ) ^ ((k : ℤ) - (k : ℤ)) = 1
    simp
  refine ⟨(η ^ 2) ^ (Fintype.card (Fin 3 × Vertex L n k 0) + Fintype.card (Fin 3 × Vertex L n k k)),
    by positivity, ?_⟩
  have e₂ := h₂ L hL k n hk hn
  have e₃ := h₃ L hL k n hk hn
  unfold EventuallyNearIdentity at e₂ e₃ ⊢
  filter_upwards [e₂, e₃] with U f₂ f₃
  obtain ⟨-, -, fRt, fΔ⟩ := f₂
  obtain ⟨-, -, fR, -, fre, -, flin⟩ := f₃
  set p := rescaledOperators L n k U with hp
  have hpη : p.eta = η := rfl
  have hptop : p.coarse = 1 := htop
  have hreal : ∀ l : vertexFunctionSpace L n k 0,
      composedCubeAverage (quietPoint U) k l ∈ vertexFunctionSpace L n k k :=
    fun l y _ => fre k le_rfl l (fun x => l.2 x (Set.mem_univ x)) y
  have hsl : ∀ l : vertexFunctionSpace L n k 0, ∀ x,
      (l : Vertex L n k 0 → ComplexMatrix2) x ∈ ComplexMatrix2.traceless := fun l x =>
    (l.2 x (Set.mem_univ x)).2
  let T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k :=
    { toFun := fun l => ⟨composedCubeAverage (quietPoint U) k l, hreal l⟩
      map_add' := fun l l' => by
        apply Subtype.ext
        have := flin l l' (hsl l) (hsl l') 1
        simpa using this
      map_smul' := fun r l => by
        apply Subtype.ext
        have h0 := flin 0 0 (fun _ => ComplexMatrix2.traceless.zero_mem)
          (fun _ => ComplexMatrix2.traceless.zero_mem) 1
        have hz : composedCubeAverage (quietPoint U) k (0 : Vertex L n k 0 → ComplexMatrix2) = 0 := by
          simpa using h0
        have := flin l 0 (hsl l) (fun _ => ComplexMatrix2.traceless.zero_mem) (r : ℂ)
        simp only [add_zero, hz] at this
        simpa [Complex.coe_smul] using this }
  have hT : ∀ l : vertexFunctionSpace L n k 0,
      (composedCubeAverageLinear (quietPoint U) l : Vertex L n k k → ComplexMatrix2) =
        composedCubeAverage (quietPoint U) k l :=
    Classical.epsilon_spec
      (p := fun T' : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k =>
        ∀ x : vertexFunctionSpace L n k 0,
          (T' x : Vertex L n k k → ComplexMatrix2) = composedCubeAverage (quietPoint U) k x)
      ⟨T, fun _ => rfl⟩
  have cRu : ∀ (l : vertexFunctionSpace L n k 0) y,
      toPauliCoeffs (composedCubeAverageLinear (quietPoint U) l : Vertex L n k k → ComplexMatrix2) y =
        ∑ x, meanKernelR L n k U y x * toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2) x := by
    intro l y
    have g := congrFun (fR (toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2))).2 y
    change applyKernel (meanKernelR L n k U) (toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2)) y =
      toPauliCoeffs (composedCubeAverage (quietPoint U) k
        (ofPauliCoeffs (toPauliCoeffs (l : Vertex L n k 0 → ComplexMatrix2)))) y at g
    rw [ofPauliCoeffs_toPauliCoeffs (hsl l), ← hT l] at g
    simp only [applyKernel, tsum_fintype] at g
    exact g.symm
  let Ψ : (vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k) ≃ₗ[ℝ]
      (Fin 3 × Vertex L n k 0 ⊕ Fin 3 × Vertex L n k k → ℝ) :=
    (ΨS.prodCongr ΨY).trans (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm
  have hΨl : ∀ w i, Ψ w (Sum.inl i) = ΨS w.1 i := fun _ _ => rfl
  have hΨr : ∀ w t, Ψ w (Sum.inr t) = ΨY w.2 t := fun _ _ => rfl
  set F : Matrix (Fin 3 × Vertex L n k 0 ⊕ Fin 3 × Vertex L n k k)
      (Fin 3 × Vertex L n k 0 ⊕ Fin 3 × Vertex L n k k) ℂ :=
    fromBlocks ((((η : ℂ) ^ 2) * 1) • Matrix.of p.Delta)
      ((((η : ℂ) ^ 2) * ((η : ℂ) ^ 2)) • Matrix.of p.Rt)
      (((1 : ℂ) * 1) • Matrix.of (meanKernelR L n k U))
      (((1 : ℂ) * ((η : ℂ) ^ 2)) • (0 : Matrix _ _ ℂ)) with hF
  have key := abs_det_eq_norm_det_of_action Ψ (ghostBlockOperator (quietPoint U)) F (fun w κ => by
    rw [Fintype.sum_sum_type]
    rcases κ with x | y
    · have e : (ghostBlockOperator (quietPoint U) w).1 =
          covDiffRealTranspose L n k U (covDiffLinear L n k U w.1) +
            iterAverageRealTranspose L n k U w.2 := rfl
      rw [hΨl, e, map_add, Pi.add_apply, Complex.ofReal_add, ← hΨS, ← hΨS, fΔ w.1 x, fRt w.2 x]
      simp only [hF, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.smul_apply, Matrix.of_apply,
        smul_eq_mul, hΨl, hΨr]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΨS]
        push_cast
        ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΨY]
        push_cast
        ring
    · have e : (ghostBlockOperator (quietPoint U) w).2 =
          composedCubeAverageLinear (quietPoint U) w.1 := rfl
      rw [hΨr, e, ← hΨY, cRu w.1 y]
      simp only [hF, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.of_apply,
        smul_eq_mul, hΨl, hΨr, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
        add_zero, one_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [hΨS])
  rw [key, hF, det_fromBlocks_scaled]
  have hs : fromBlocks (Matrix.of p.Delta) (Matrix.of p.Rt) (Matrix.of (meanKernelR L n k U)) 0 =
      ghostMatrix U := rfl
  rw [hs]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heta,
    one_pow, mul_one, one_mul, norm_one]
  ring
end YangMills.Construction.RunningCouplingSlope
end
