import YangMills.Construction.Lattice.SignedPermutationMatricesAndAffineHypercubicMaps
import YangMills.Construction.EuclideanAnalysis.RotationsOfCoordinatePlanesGenerateTheSpecialOrthogonalGroup
import YangMills.Construction.RotationInvariance.FromOnePlaneToTheFullOrthogonalGroup
import YangMills.Construction.RotationInvariance.MomentsAndConnectedFunctionsUnderAnOrthogonalMap
import YangMills.Construction.RotationInvariance.MotionsOfPlatesAndQuarterRotationsProof
import YangMills.Construction.RotationInvariance.PassageFromPlatesToAllSeparatedTestFunctions
import YangMills.Construction.RotationInvariance.WhatAnOrthogonalMapPreserves
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
namespace OrthogonalClosure
open EuclideanAnalysis.PlaneRotations OrthogonalInvariance
def Stabilizes (S : ConnFamily) (Q : Matrix.orthogonalGroup (Fin 4) ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ f ∈ disjointComplexTuples n,
    centeredFnFree S ((EuclidMotion.ofOrthogonalMatrix Q).actFree (complexTuple f)) =
      centeredFnFree S (complexTuple f)
theorem Stabilizes.mul {S : ConnFamily} {Q Q' : Matrix.orthogonalGroup (Fin 4) ℝ}
    (himg : ComplexTupleImages) (hact : FreeAction)
    (hQ : Stabilizes S Q) (hQ' : Stabilizes S Q') : Stabilizes S (Q * Q') := by
  intro n hn f hf
  have h1 := himg Q' 0 n f hf
  rw [← (hact Q Q' 0 (complexTuple f) 0).1, h1.2.1, hQ n hn _ h1.1, ← h1.2.1,
    hQ' n hn f hf]
def signedPermMatrix (w : PeriodicLattice.SignedFrame) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => if ν = w.1 μ then ((w.2 μ : ℤ) : ℝ) else 0
theorem signedPermMatrix_mulVec (w : PeriodicLattice.SignedFrame) (x : R4) :
    signedPermMatrix w *ᵥ x = w.actOnVector x := by apply _root_.YangMills.Construction.PeriodicLattice.SignedFrame.toMatrix_mulVec <;> assumption
theorem signedPermMatrix_mem (w : PeriodicLattice.SignedFrame) :
    signedPermMatrix w ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext μ κ
  by_cases h : μ = κ
  · subst h
    simp [signedPermMatrix, Matrix.mul_apply, intUnit_mul_self]
  · have hne : w.1 κ ≠ w.1 μ := fun e => h (w.1.injective e).symm
    simp [signedPermMatrix, Matrix.mul_apply, h, hne]
def signedPermOrth (w : PeriodicLattice.SignedFrame) : Matrix.orthogonalGroup (Fin 4) ℝ :=
  ⟨signedPermMatrix w, signedPermMatrix_mem w⟩
theorem ofOrthogonalMatrix_signedPermOrth (w : PeriodicLattice.SignedFrame) :
    EuclidMotion.ofOrthogonalMatrix (signedPermOrth w) = ofSignedFrame w :=
  EuclidMotion.ext_of_apply fun x => by
    rw [EuclidMotion.ofOrthogonalMatrix_apply, ofSignedFrame_apply]
    exact signedPermMatrix_mulVec w x
theorem stabilizes_signedPerm {S : ConnFamily} (hW : MomentSymmetry.MotionInvariant S)
    (w : PeriodicLattice.SignedFrame) : Stabilizes S (signedPermOrth w) := by
  intro n _ f _
  rw [ofOrthogonalMatrix_signedPermOrth]
  exact (hW _).2 _ ⟨w, rfl⟩
theorem rotateLin_toMatrix (t : ℝ) :
    LinearMap.toMatrix' (rotateLin t) =
      !![Real.cos t, 0, 0, Real.sin t; 0, 1, 0, 0; 0, 0, 1, 0; -Real.sin t, 0, 0, Real.cos t] := by apply _root_.YangMills.Construction.EuclideanFunctionals.ProductMotions.toMatrix'_rotateLin <;> assumption
def rotateOrth (hr : RotationRules) (t : ℝ) : Matrix.orthogonalGroup (Fin 4) ℝ :=
  ⟨LinearMap.toMatrix' (rotateLin t), (Matrix.mem_specialOrthogonalGroup_iff.1 (hr t).1).1⟩
theorem ofOrthogonalMatrix_rotateOrth (hr : RotationRules) (t : ℝ) :
    EuclidMotion.ofOrthogonalMatrix (rotateOrth hr t) = rotateMotion t :=
  EuclidMotion.ext_of_apply fun x => by
    rw [EuclidMotion.ofOrthogonalMatrix_apply]
    show LinearMap.toMatrix' (rotateLin t) *ᵥ x = rotateLin t x + 0
    rw [LinearMap.toMatrix'_mulVec, add_zero]
theorem stabilizes_rotate {S : ConnFamily} (himg : ComplexTupleImages) (hr : RotationRules)
    (hpass : ∀ n : ℕ, 2 ≤ n → ∀ t : ℝ, ∀ g ∈ disjointComplexTuples n,
      centeredFnFree S
          (complexTuple fun l => (rotateMotion t).actFn (g l)) =
        centeredFnFree S (complexTuple g))
    (t : ℝ) : Stabilizes S (rotateOrth hr t) := by
  intro n hn f hf
  rw [(himg _ 0 n f hf).2.1, ofOrthogonalMatrix_rotateOrth]
  exact hpass n hn t f hf
theorem exists_perm_to_last_first {i j : Fin 4} (hij : i ≠ j) :
    ∃ π : Equiv.Perm (Fin 4), π i = 3 ∧ π j = 0 := by
  have hj : Equiv.swap i 3 j ≠ 3 := fun e =>
    hij ((Equiv.swap i 3).injective (e.trans (Equiv.swap_apply_left i 3).symm)).symm
  refine ⟨Equiv.swap (Equiv.swap i 3 j) 0 * Equiv.swap i 3, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hj.symm (by decide)]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
theorem toEuclideanLin_stdBasisVector_apply (A : Matrix (Fin 4) (Fin 4) ℝ) (k μ : Fin 4) :
    (toEuclideanLin A (EuclideanAnalysis.stdBasisVector k)) μ = A μ k := by
  simp [EuclideanAnalysis.stdBasisVector, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
    Pi.single_apply]
theorem stdBasisVector_apply (k μ : Fin 4) :
    (EuclideanAnalysis.stdBasisVector k : EuclideanAnalysis.RealSpace 4) μ =
      if μ = k then 1 else 0 := by
  simp [EuclideanAnalysis.stdBasisVector]
theorem entry_eq_zero_of_map_plane {A : Matrix (Fin 4) (Fin 4) ℝ} {i j k μ : Fin 4}
    (hmap : (coordPlane i j).map (toEuclideanLin A) = coordPlane i j)
    (hk : k = i ∨ k = j) (hi : μ ≠ i) (hj : μ ≠ j) : A μ k = 0 := by
  have hmem : EuclideanAnalysis.stdBasisVector k ∈ coordPlane i j := by
    apply Submodule.subset_span
    rcases hk with rfl | rfl <;> simp
  have himage : toEuclideanLin A (EuclideanAnalysis.stdBasisVector k) ∈ coordPlane i j := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hmem
  obtain ⟨a, b, e⟩ := Submodule.mem_span_pair.1 himage
  refine (toEuclideanLin_stdBasisVector_apply A k μ).symm.trans ?_
  rw [← e]
  simp [stdBasisVector_apply, hi, hj]
theorem signedPerm_mul_mul_signedPerm (π : Equiv.Perm (Fin 4)) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    signedPermMatrix (π, fun _ => 1) * B * signedPermMatrix (π⁻¹, fun _ => 1) =
      B.submatrix π π := by
  ext μ ν
  simp [signedPermMatrix, Matrix.mul_apply, Equiv.eq_symm_apply]
theorem exists_angle_of_rotation {p q r s : ℝ} (h₁ : q ^ 2 + p ^ 2 = 1) (h₃ : s * q + r * p = 0)
    (h₄ : s * p - q * r = 1) :
    ∃ t : ℝ, Real.cos t = p ∧ Real.sin t = q ∧ s = p ∧ r = -q := by
  have hn : ‖(⟨p, q⟩ : ℂ)‖ = 1 := by
    have h : ‖(⟨p, q⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      linarith
    have h0 := norm_nonneg (⟨p, q⟩ : ℂ)
    nlinarith
  have h0 : (⟨p, q⟩ : ℂ) ≠ 0 := fun e => by
    rw [e, norm_zero] at hn
    exact zero_ne_one hn
  refine ⟨Complex.arg ⟨p, q⟩, ?_, ?_, ?_, ?_⟩
  · rw [Complex.cos_arg h0, hn]
    simp
  · rw [Complex.sin_arg, hn]
    simp
  · linear_combination (-s) * h₁ + q * h₃ + p * h₄
  · linear_combination (-r) * h₁ + p * h₃ - q * h₄
theorem stabilizes_of_isPlaneRotation {S : ConnFamily} (himg : ComplexTupleImages)
    (hact : FreeAction) (hr : RotationRules)
    (hW : MomentSymmetry.MotionInvariant S)
    (hrot : ∀ t : ℝ, Stabilizes S (rotateOrth hr t))
    (Q : specialOrthogonalGroup (Fin 4) ℝ) (hQ : IsPlaneRotation Q)
    (hO : Q.1 ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : Stabilizes S ⟨Q.1, hO⟩ := by
  obtain ⟨i, j, hij, hmap, hfix⟩ := hQ
  obtain ⟨π, hπi, hπj⟩ := exists_perm_to_last_first hij
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin 4) (Fin 4) ℝ, A = Q.1 := ⟨_, rfl⟩
  simp only [← hAdef] at hmap hfix hO ⊢
  have hcol : ∀ k, k ≠ i → k ≠ j → ∀ μ, A μ k = if μ = k then 1 else 0 := by
    intro k hi hj μ
    refine (toEuclideanLin_stdBasisVector_apply A k μ).symm.trans ?_
    rw [hfix k hi hj, stdBasisVector_apply]
  have hsi : π.symm 3 = i := by rw [← hπi]; simp
  have hsj : π.symm 0 = j := by rw [← hπj]; simp
  have hne : ∀ a : Fin 4, a ≠ 3 → a ≠ 0 → π.symm a ≠ i ∧ π.symm a ≠ j := by
    intro a h3 h0
    exact ⟨fun e => h3 (by rw [← hsi] at e; exact π.symm.injective e),
      fun e => h0 (by rw [← hsj] at e; exact π.symm.injective e)⟩
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin 4) (Fin 4) ℝ, M = A.submatrix π.symm π.symm := ⟨_, rfl⟩
  have hMa : ∀ a b, M a b = A (π.symm a) (π.symm b) := fun a b => by rw [hMdef]; rfl
  have c1 : ∀ μ, M μ 1 = if μ = 1 then 1 else 0 := fun μ => by
    rw [hMa, hcol _ (hne 1 (by decide) (by decide)).1 (hne 1 (by decide) (by decide)).2]
    simp
  have c2 : ∀ μ, M μ 2 = if μ = 2 then 1 else 0 := fun μ => by
    rw [hMa, hcol _ (hne 2 (by decide) (by decide)).1 (hne 2 (by decide) (by decide)).2]
    simp
  have z : ∀ a b : Fin 4, a ≠ 3 → a ≠ 0 → (b = 3 ∨ b = 0) → M a b = 0 := by
    intro a b h3 h0 hb
    rw [hMa]
    refine entry_eq_zero_of_map_plane hmap ?_ (hne a h3 h0).1 (hne a h3 h0).2
    rcases hb with rfl | rfl
    · exact Or.inl hsi
    · exact Or.inr hsj
  have hMeq : M = !![M 0 0, 0, 0, M 0 3; 0, 1, 0, 0; 0, 0, 1, 0; M 3 0, 0, 0, M 3 3] := by
    have e10 := z 1 0 (by decide) (by decide) (Or.inr rfl)
    have e13 := z 1 3 (by decide) (by decide) (Or.inl rfl)
    have e20 := z 2 0 (by decide) (by decide) (Or.inr rfl)
    have e23 := z 2 3 (by decide) (by decide) (Or.inl rfl)
    have d01 := c1 0
    have d11 := c1 1
    have d21 := c1 2
    have d31 := c1 3
    have d02 := c2 0
    have d12 := c2 1
    have d22 := c2 2
    have d32 := c2 3
    simp at d01 d11 d21 d31 d02 d12 d22 d32
    ext μ ν
    fin_cases μ <;> fin_cases ν <;> simp [e10, e13, e20, e23, d01, d11, d21, d31, d02, d12, d22, d32]
  have hdet : M.det = 1 := by
    rw [hMdef, Matrix.det_submatrix_equiv_self]
    rw [hAdef]
    exact (Matrix.mem_specialOrthogonalGroup_iff.1 Q.2).2
  have hMM : Mᵀ * M = 1 := by
    have h := (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).1 hO
    rw [hMdef, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, h,
      Matrix.submatrix_one_equiv]
  obtain ⟨p, hp⟩ : ∃ p, p = M 3 3 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = M 0 3 := ⟨_, rfl⟩
  obtain ⟨r, hr'⟩ : ∃ r, r = M 3 0 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = M 0 0 := ⟨_, rfl⟩
  rw [← hp, ← hq, ← hr', ← hs] at hMeq
  rw [hMeq] at hdet hMM
  have h₄ : s * p - q * r = 1 := by
    rw [Matrix.det_succ_row_zero] at hdet
    simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove] at hdet
    linarith
  have h₁ : q ^ 2 + p ^ 2 = 1 := by
    have h := congrFun (congrFun hMM 3) 3
    simp [Matrix.mul_apply, Fin.sum_univ_four] at h
    linarith
  have h₃ : s * q + r * p = 0 := by
    have h := congrFun (congrFun hMM 0) 3
    simp [Matrix.mul_apply, Fin.sum_univ_four] at h
    linarith
  obtain ⟨t, hc, hsin, hsp, hrq⟩ := exists_angle_of_rotation h₁ h₃ h₄
  have hMR : M = LinearMap.toMatrix' (rotateLin t) := by
    rw [rotateLin_toMatrix, hc, hsin, hMeq, hsp, hrq]
  have hA : A = (LinearMap.toMatrix' (rotateLin t)).submatrix π π := by
    rw [← hMR, hMdef, Matrix.submatrix_submatrix]
    simp
  have e : (⟨A, hO⟩ : Matrix.orthogonalGroup (Fin 4) ℝ) =
      signedPermOrth (π, fun _ => 1) * rotateOrth hr t *
        signedPermOrth (π⁻¹, fun _ => 1) :=
    Subtype.ext (hA.trans (signedPerm_mul_mul_signedPerm π _).symm)
  rw [e]
  exact ((stabilizes_signedPerm hW _).mul himg hact (hrot t)).mul himg hact
    (stabilizes_signedPerm hW _)
theorem mem_orthogonalGroup_of_special (Q : specialOrthogonalGroup (Fin 4) ℝ) :
    Q.1 ∈ Matrix.orthogonalGroup (Fin 4) ℝ :=
  (Matrix.mem_specialOrthogonalGroup_iff.1 Q.2).1
theorem signedPermOrth_one : signedPermOrth (1, fun _ => 1) = 1 :=
  Subtype.ext (by
    ext μ ν
    simp [signedPermOrth, signedPermMatrix, Matrix.one_apply, eq_comm])
theorem stabilizes_prod {S : ConnFamily} (himg : ComplexTupleImages) (hact : FreeAction)
    (hW : MomentSymmetry.MotionInvariant S)
    (hplane : ∀ Q : specialOrthogonalGroup (Fin 4) ℝ, IsPlaneRotation Q →
      Stabilizes S ⟨Q.1, mem_orthogonalGroup_of_special Q⟩)
    (l : List (specialOrthogonalGroup (Fin 4) ℝ)) (hl : ∀ Q ∈ l, IsPlaneRotation Q) :
    Stabilizes S ⟨l.prod.1, mem_orthogonalGroup_of_special l.prod⟩ := by
  induction l with
  | nil =>
    have e : (⟨(([] : List (specialOrthogonalGroup (Fin 4) ℝ)).prod).1,
        mem_orthogonalGroup_of_special _⟩ : Matrix.orthogonalGroup (Fin 4) ℝ) =
        signedPermOrth (1, fun _ => 1) := by
      rw [signedPermOrth_one]
      exact Subtype.ext rfl
    rw [e]
    exact stabilizes_signedPerm hW _
  | cons a l ih =>
    have e : (⟨((a :: l).prod).1, mem_orthogonalGroup_of_special _⟩ :
        Matrix.orthogonalGroup (Fin 4) ℝ) =
        ⟨a.1, mem_orthogonalGroup_of_special a⟩ *
          ⟨l.prod.1, mem_orthogonalGroup_of_special l.prod⟩ :=
      Subtype.ext (by simp)
    rw [e]
    exact (hplane a (hl a (by simp))).mul himg hact (ih fun Q hQ => hl Q (by simp [hQ]))
theorem signedPermMatrix_reflection :
    signedPermMatrix (1, ![1, 1, 1, -1]) = lastCoordReflection := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;> simp [signedPermMatrix, lastCoordReflection]
theorem stabilizes_all {S : ConnFamily} (himg : ComplexTupleImages) (hact : FreeAction)
    (hW : MomentSymmetry.MotionInvariant S)
    (hplanes : EuclideanAnalysis.PlaneRotationsGenerate)
    (hplane : ∀ Q : specialOrthogonalGroup (Fin 4) ℝ, IsPlaneRotation Q →
      Stabilizes S ⟨Q.1, mem_orthogonalGroup_of_special Q⟩)
    (Q : Matrix.orthogonalGroup (Fin 4) ℝ) : Stabilizes S Q := by
  have hso : ∀ A : specialOrthogonalGroup (Fin 4) ℝ,
      Stabilizes S ⟨A.1, mem_orthogonalGroup_of_special A⟩ := by
    intro A
    obtain ⟨l, hl, rfl⟩ := hplanes.1 4 (by norm_num) A
    exact stabilizes_prod himg hact hW hplane l hl
  have hmem : Q.1 ∈ (Matrix.orthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ)) := Q.2
  rw [hplanes.2.1] at hmem
  rcases hmem with h | ⟨A, hA, e⟩
  · exact hso ⟨Q.1, h⟩
  · have e' : Q = ⟨A, mem_orthogonalGroup_of_special ⟨A, hA⟩⟩ *
        signedPermOrth (1, ![1, 1, 1, -1]) :=
      Subtype.ext (by
        show Q.1 = A * signedPermMatrix (1, ![1, 1, 1, -1])
        rw [signedPermMatrix_reflection]
        exact e.symm)
    rw [e']
    exact (hso ⟨A, hA⟩).mul himg hact (stabilizes_signedPerm hW _)
theorem actFree_toFree (r : EuclidMotion) {Y : FnList} (hY : Y ∈ sepAll) :
    r.actFree (toFree Y) = toFree (r.actList Y) :=
  liftLin_toFree _ ⟨Y, hY⟩
end OrthogonalClosure
open OrthogonalClosure OrthogonalInvariance in
theorem FullOrthogonalInvariance.holds_of_parts
    (hplanes : EuclideanAnalysis.PlaneRotationsGenerate)
    (hinv : MomentSymmetry.ReductionHolds)
    (hiso : OrthogonalInvariance.Holds)
    (hmom : OrthogonalInvariance.OrthogonalMapStatement)
    (hpass : RotationFromProducts.InvariantOnComplexTuples) :
    FullOrthogonalInvariance.Holds := by
  intro m S d φ₀ hm n hn R
  obtain ⟨-, hsupp, -, -, hr, -, himg, -, hact, -, -⟩ := hiso
  have hW := (hinv m S d.fnl).2.1
  have hrot := stabilizes_rotate (S := S) himg hr (hpass m S d φ₀ hm)
  have hG : ∀ Q, Stabilizes S Q := stabilizes_all himg hact hW hplanes
    fun Q hQ => stabilizes_of_isPlaneRotation himg hact hr hW hrot Q hQ _
  refine ⟨fun f hf => hG R n hn f hf, ?_⟩
  obtain ⟨-, hab, -, -, -, hagree, -⟩ := hmom m S d.fnl R
  have hbeta : OrthogonalInvariance.MomentsInvariant S
      (EuclidMotion.ofOrthogonalMatrix R) := by
    intro k hk Y hY
    have hYs : Y ∈ sepAll := Set.mem_iUnion.2 ⟨k, hY⟩
    have hRY : (EuclidMotion.ofOrthogonalMatrix R).actList Y ∈ sepN k := by
      rw [← (hsupp R).2.2.2 k |>.2]
      exact ⟨Y, hY, rfl⟩
    have hRYs : (EuclidMotion.ofOrthogonalMatrix R).actList Y ∈ sepAll :=
      Set.mem_iUnion.2 ⟨k, hRY⟩
    have hlen : Y.length = k := hY.1
    have hG' := hG R Y.length (by omega) (complexify Y) (complexify_mem hYs)
    rw [complexTuple_complexify, actFree_toFree _ hYs] at hG'
    apply Complex.ofReal_injective
    rw [hagree k (by omega) _ hRY, hagree k (by omega) _ hY,
      complexTuple_complexify, complexTuple_complexify]
    exact hG'
  have halpha := hab.2 hbeta
  intro X hX
  have hlen : X.length = n := hX.1
  subst hlen
  have h := halpha X.length hn X.get (by rw [List.ofFn_get]; exact hX)
  have e : (List.ofFn fun l => (EuclidMotion.ofOrthogonalMatrix R).actFn (X.get l)) =
      (EuclidMotion.ofOrthogonalMatrix R).actList X := by
    apply List.ext_get (by simp [EuclidMotion.actList])
    intro i h₁ h₂
    simp [EuclidMotion.actList]
  have h' : S.evalAt X.length ((EuclidMotion.ofOrthogonalMatrix R).actList X) =
      S.evalAt X.length X :=
    (congrArg (S.evalAt X.length) e.symm).trans
      (h.trans (congrArg (S.evalAt X.length) (List.ofFn_get X)))
  simpa [ReflectionPositivity.AxisMirror.Ambient.ConnectedFamily.evalAt, hn] using h'
end YangMills.Construction.EuclideanFunctionals
end
