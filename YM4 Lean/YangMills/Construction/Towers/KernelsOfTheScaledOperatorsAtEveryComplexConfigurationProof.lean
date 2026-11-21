import YangMills.Construction.Towers.KernelsOfTheScaledOperatorsAtEveryComplexConfiguration
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.RescaledKernels
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.HessianKernel (IsSymmBilinearOn IsSymm)
section Kernels
variable {N N' N'' : Type}
theorem entry_eq_apply_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) (i : N) (i' : N') :
    ∃ f : N → ℂ, (∀ j, j ≠ i → f j = 0) ∧ T i' i = M f i' := by
  classical
  refine ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne hj _, ?_⟩
  rw [← (h _).2]
  unfold applyKernel
  rw [tsum_eq_single i]
  · simp
  · intro b hb
    simp [Pi.single_eq_of_ne hb]
theorem applySummable_of_rowFinite {T : KernelMatrix N N'} (hT : RowFinite T) (f : N → ℂ) :
    ApplySummable T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applySummable_of_rowFinite <;> assumption
theorem compSumsFinite_of_rowFinite {T : KernelMatrix N' N''} (S : KernelMatrix N N')
    (hT : RowFinite T) : CompSumsFinite T S := fun i'' i =>
  (hT i'').subset fun j hj h0 => hj (by rw [h0, zero_mul])
theorem compSummable_of_rowFinite {T : KernelMatrix N' N''} (S : KernelMatrix N N')
    (hT : RowFinite T) : CompSummable T S := by
  intro i'' i
  refine summable_of_hasFiniteSupport ((hT i'').subset ?_)
  intro j hj h0
  apply hj
  have h0' : T i'' j = 0 := by simpa using h0
  simp [h0']
theorem exists_ne_zero_of_compKernel_ne_zero {T : KernelMatrix N' N''} {S : KernelMatrix N N'}
    {i'' : N''} {i : N} (h : compKernel T S i'' i ≠ 0) : ∃ j, T i'' j ≠ 0 ∧ S j i ≠ 0 := by
  by_contra hc
  apply h
  have e : ∀ j, T i'' j * S j i = 0 := fun j => by
    by_cases t : T i'' j = 0
    · rw [t, zero_mul]
    · have s : S j i = 0 := by
        by_contra s
        exact hc ⟨j, t, s⟩
      rw [s, mul_zero]
  simp [compKernel, e]
theorem rowFinite_compKernel {T : KernelMatrix N' N''} {S : KernelMatrix N N'} (hT : RowFinite T)
    (hS : RowFinite S) : RowFinite (compKernel T S) := fun i'' =>
  ((hT i'').biUnion fun j _ => hS j).subset fun i h => by
    obtain ⟨j, t, s⟩ := exists_ne_zero_of_compKernel_ne_zero h
    exact mem_biUnion t s
theorem columnFinite_compKernel {T : KernelMatrix N' N''} {S : KernelMatrix N N'}
    (hT : ColumnFinite T) (hS : ColumnFinite S) :
    ColumnFinite (compKernel T S) := fun i =>
  ((hS i).biUnion fun j _ => hT j).subset fun i'' h => by
    obtain ⟨j, t, s⟩ := exists_ne_zero_of_compKernel_ne_zero h
    exact mem_biUnion s t
theorem rowFinite_add {T T' : KernelMatrix N N'} (hT : RowFinite T) (hT' : RowFinite T') :
    RowFinite (T + T') := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.rowFinite_add <;> assumption
theorem columnFinite_add {T T' : KernelMatrix N N'} (hT : ColumnFinite T)
    (hT' : ColumnFinite T') : ColumnFinite (T + T') := fun i =>
  ((hT i).union (hT' i)).subset fun i' h => by
    by_contra hc
    have h₁ : T i' i = 0 := by
      by_contra e
      exact hc (Or.inl e)
    have h₂ : T' i' i = 0 := by
      by_contra e
      exact hc (Or.inr e)
    exact h (by simp [h₁, h₂])
theorem rowFinite_wTranspose {T : KernelMatrix N N'} (w : N' → ℝ) (w' : N → ℝ)
    (hT : ColumnFinite T) : RowFinite (YangMills.Construction.PeriodicOperators.wTranspose w' w T) :=
  fun i => (hT i).subset fun i' h h0 =>
    h (by simp [YangMills.Construction.PeriodicOperators.wTranspose, h0])
theorem columnFinite_wTranspose {T : KernelMatrix N N'} (w : N' → ℝ) (w' : N → ℝ)
    (hT : RowFinite T) : ColumnFinite (YangMills.Construction.PeriodicOperators.wTranspose w' w T) :=
  fun i' => (hT i').subset fun _ h h0 =>
    h (by simp [YangMills.Construction.PeriodicOperators.wTranspose, h0])
end Kernels
theorem kernelsWellFormed_of_kernels {S₀ B₀ S B : Type} (p : RescaledOperators S₀ B₀ S B)
    (Dm : (Fin 3 × S₀ → ℂ) → Fin 3 × B₀ → ℂ) (src tgt : B₀ → S₀)
    (vertexFns : Set (S₀ → ComplexMatrix2)) (edgeFns : Set (B₀ → ComplexMatrix2))
    (hrep : Represents p.D Dm)
    (hzero : ∀ (a' : Fin 3) (b : B₀) (a : Fin 3) (x : S₀), x ≠ src b → x ≠ tgt b →
      p.D (a', b) (a, x) = 0)
    (Dr : RowFinite p.D) (Dc : ColumnFinite p.D)
    (Hr : RowFinite p.H) (Hc : ColumnFinite p.H) :
    KernelsWellFormed p Dm src tgt vertexFns edgeFns := by
  have Tr : RowFinite p.Dt := rowFinite_wTranspose _ _ Dc
  have Tc : ColumnFinite p.Dt := columnFinite_wTranspose _ _ Dr
  have Kr : RowFinite p.K := rowFinite_add Hr (rowFinite_compKernel Dr Tr)
  have Kc : ColumnFinite p.K := columnFinite_add Hc (columnFinite_compKernel Dc Tc)
  have Er : RowFinite p.Delta := rowFinite_compKernel Tr Dr
  have Ec : ColumnFinite p.Delta := columnFinite_compKernel Tc Dc
  exact
    { represents := hrep
      D_eq_zero := hzero
      D_rowFinite := Dr
      D_columnFinite := Dc
      H_rowFinite := Hr
      H_columnFinite := Hc
      D_Dt_sumsFinite := compSumsFinite_of_rowFinite _ Dr
      Dt_D_sumsFinite := compSumsFinite_of_rowFinite _ Tr
      D_Dt_summable := compSummable_of_rowFinite _ Dr
      Dt_D_summable := compSummable_of_rowFinite _ Tr
      K_rowFinite := Kr
      K_columnFinite := Kc
      Delta_rowFinite := Er
      Delta_columnFinite := Ec
      K_applySummable := fun _ _ => applySummable_of_rowFinite Kr _
      Delta_applySummable := fun _ _ => applySummable_of_rowFinite Er _ }
theorem kernel_smul_of_mapOnCoeffs_eq (r r' : PauliComponentsOfSymmetricKernel)
    (m m' : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2)
    (z : ℂ) (hm : PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m' = z • PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m)
    (h : PauliComponentsOfSymmetricKernel.HasLocalKernel r r' m)
    (hu : KernelUnique r.Index r'.Index) :
    Represents (PauliComponentsOfSymmetricKernel.kernel r r' m') (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m') ∧
      PauliComponentsOfSymmetricKernel.kernel r r' m' = z • PauliComponentsOfSymmetricKernel.kernel r r' m := by
  have g : Represents (z • PauliComponentsOfSymmetricKernel.kernel r r' m) (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m') := by
    rw [hm]
    exact h.smul_represents z
  have e : Represents (PauliComponentsOfSymmetricKernel.kernel r r' m') (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m') :=
    Classical.epsilon_spec (p := fun T => Represents T (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m')) ⟨_, g⟩
  exact ⟨e, hu _ _ _ e g⟩
theorem pauliFamily_mem_traceless (a : Fin 3) : ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_real_smul {r : ℝ} (hr : r ≠ 0) (a : Fin 3) (X : ComplexMatrix2) :
    pauliCoeff a (r • X) = (r : ℂ) * pauliCoeff a X := by
  have e : r • X = (r : ℂ) • X := by
    ext i j
    simp
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [e]
  unfold pauliCoeff
  by_cases h : X ∈ ComplexMatrix2.traceless
  · have h' : (r : ℂ) • X ∈ ComplexMatrix2.traceless := ComplexMatrix2.traceless.smul_mem _ h
    rw [dif_pos h', dif_pos h]
    have e' : (⟨(r : ℂ) • X, h'⟩ : ComplexMatrix2.traceless) = (r : ℂ) • ⟨X, h⟩ := rfl
    rw [e', map_smul]
    rfl
  · have h' : (r : ℂ) • X ∉ ComplexMatrix2.traceless := fun hh => h (by
      have := ComplexMatrix2.traceless.smul_mem (r : ℂ)⁻¹ hh
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this)
    rw [dif_neg h', dif_neg h, mul_zero]
theorem ofPauliCoeffs_eq_zero_of_ne {σ : Type} {a : Fin 3} {x y : σ} {f : Fin 3 × σ → ℂ}
    (hf : ∀ j, j ≠ (a, x) → f j = 0) (h : y ≠ x) : ofPauliCoeffs f y = 0 := by
  unfold ofPauliCoeffs
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [hf _ (fun e => h (Prod.ext_iff.1 e).2), zero_smul]
theorem apply_real_smul_real_smul {α : Type} {𝒮 : Set (α → ComplexMatrix2)}
    {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsSymmBilinearOn 𝒮 Q) (h0 : (0 : α → ComplexMatrix2) ∈ 𝒮) (r : ℝ)
    {E E' : α → ComplexMatrix2}
    (hE : E ∈ 𝒮) (hE' : E' ∈ 𝒮) (hY : (r : ℂ) • E' ∈ 𝒮) :
    Q (r • E) (r • E') = (r : ℂ) * ((r : ℂ) * Q E E') := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.symmBilinear_real_smul_smul <;> assumption
theorem rowFinite_columnFinite_of_hessian_eq_zero {σ : Type}
    {A H : KernelMatrix (Fin 3 × σ) (Fin 3 × σ)}
    (h : ∀ i i', A i i' = 0 → H i i' = 0)
    (hr : HessianKernel.RowFinite A) (hs : IsSymm A) :
    RowFinite H ∧ ColumnFinite H :=
  ⟨fun i' => (hr i').subset fun _ hne e => hne (h _ _ e),
    fun i => (hr i).subset fun i' hne e => hne (h _ _ ((hs i' i).trans e))⟩
theorem finestMesh_ne_zero {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    finestMesh L k ≠ 0 := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.finestMesh_ne_zero <;> assumption
section Torus
variable {L n k : ℕ}
theorem basisForm_mem_complexEdgeForms
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (a : Fin 3) (b : PositiveEdge L n k 0) :
    basisForm a b ∈ complexEdgeForms L n k 0 := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.basisForm_mem <;> assumption
theorem covDiff_ofPauliCoeffs_eq_zero (U : Edge L n k 0 → ComplexMatrix2) {a : Fin 3}
    (b : PositiveEdge L n k 0)
    {x : Vertex L n k 0} {f : Fin 3 × Vertex L n k 0 → ℂ} (hf : ∀ j, j ≠ (a, x) → f j = 0)
    (hx : x ≠ b.1.source) (hy : x ≠ b.1.target) :
    covDiff U (ofPauliCoeffs f) b.1 = 0 := by
  classical
  simp only [covDiff, extendOddly, if_pos b.2]
  rw [ofPauliCoeffs_eq_zero_of_ne hf hx.symm, ofPauliCoeffs_eq_zero_of_ne hf hy.symm]
  simp [ComplexMatrix2.conjugateBy]
theorem onTorus (h₁ : ThreeMapKernels.Claim)
    (h₂ : HessianKernel.KernelProperties)
    (h₃ : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n) : OnTorus L n k := by
  classical
  intro U hU
  have hη := finestMesh_ne_zero hL k
  have hη' : (finestMesh L k)⁻¹ ≠ 0 := inv_ne_zero hη
  have hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => (h₃ ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ 0 (Nat.zero_le _)).2.2.2 b |>.2.2.2.2.2
  have A := (h₁ L hL k hk).1 n hn
  have Uq := (A.1 0 0 (Nat.zero_le _) (Nat.zero_le _)).2.1
  have Dk := A.2.1 U hU
  obtain ⟨hrep, eq⟩ := kernel_smul_of_mapOnCoeffs_eq (vertexCoordinate (Vertex L n k 0))
    (edgePauliCoordinates L n k 0)
    (covDiff U) (fun l => (finestMesh L k)⁻¹ • covDiff U l)
    (((finestMesh L k)⁻¹ : ℝ) : ℂ)
    (by
      funext f i
      exact pauliCoeff_real_smul hη' i.1 _)
    Dk Uq
  obtain ⟨bil, -, standingConstraints, -, -, symm⟩ := ((h₂ L hL k 0 (Nat.zero_le _)).1 n hn) U hU
  have Hh := rowFinite_columnFinite_of_hessian_eq_zero (H := (rescaledOperators L n k U).H)
    (fun i i' e => by
      have e' : complexActionHessian U (basisForm i.1 i.2)
          (basisForm i'.1 i'.2) = 0 := e
      show (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) * complexActionHessian U _ _ = 0
      rw [apply_real_smul_real_smul bil (complexEdgeForms L n k 0).zero_mem (finestMesh L k)
        (basisForm_mem_complexEdgeForms hx i.1 i.2) (basisForm_mem_complexEdgeForms hx i'.1 i'.2)
        ((complexEdgeForms L n k 0).smul_mem _ (basisForm_mem_complexEdgeForms hx i'.1 i'.2)), e']
      simp)
    standingConstraints symm
  refine kernelsWellFormed_of_kernels _ _ _ _ _ _ hrep ?_ ?_ ?_ Hh.1 Hh.2
  · intro a' b a x hx₁ hx₂
    obtain ⟨f, hf, e⟩ := entry_eq_apply_of_represents hrep (a, x) (a', b)
    have hf' : ∀ j : Fin 3 × Vertex L n k 0, j ≠ (a, x) → (f j : ℂ) = 0 := hf
    refine e.trans ?_
    show pauliCoeff a' (((finestMesh L k)⁻¹ •
      covDiff U (ofPauliCoeffs f)) b.1) = 0
    rw [Pi.smul_apply, covDiff_ofPauliCoeffs_eq_zero U b hf' hx₁ hx₂, smul_zero, pauliCoeff_zero]
  · show RowFinite (PauliComponentsOfSymmetricKernel.kernel _ _ _)
    rw [eq]
    exact Dk.smul_row_finite _
  · show ColumnFinite (PauliComponentsOfSymmetricKernel.kernel _ _ _)
    rw [eq]
    exact Dk.smul_column_finite _
end Torus
section FullSpace
variable {L k : ℕ}
theorem fullSpace_basisForm_mem (hx : ∀ b : FullSpace.Edge L k 0,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L k 0)) :
    FullSpace.basisForm a b ∈ FullSpace.complexEdgeForms (meshAt L k 0) := by
  classical
  unfold FullSpace.basisForm
  refine ⟨fun b' hb' => ?_, fun b' => ?_⟩
  · simp only [FullSpace.extendOddly, if_pos hb']
    split_ifs
    · exact pauliFamily_mem_traceless a
    · exact ComplexMatrix2.traceless.zero_mem
  · rcases hx b' with h | h
    · simp only [FullSpace.extendOddly, if_pos h.1, if_neg h.2]
      rfl
    · simp only [FullSpace.extendOddly, if_pos h.1, if_neg h.2, neg_neg]
theorem fullSpace_basisForm_finiteSupport (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L k 0)) :
    FullSpace.HasFiniteEdgeSupport (FullSpace.basisForm (L := L) (k := k) (j := 0) a b) := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.basisForm_finiteSupport <;> assumption
theorem fullSpace_zero_mem :
    (0 : FullSpace.Edge L k 0 → ComplexMatrix2) ∈
      HessianKernel.finiteSupportComplexForms L k 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.zero_mem_finiteSupport <;> assumption
theorem fullSpace_smul_mem (z : ℂ) {B : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ HessianKernel.finiteSupportComplexForms L k 0) :
    z • B ∈ HessianKernel.finiteSupportComplexForms L k 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.smul_mem_finiteSupport <;> assumption
theorem fullSpace_covDiff_ofPauliCoeffs_eq_zero (U : FullSpace.Edge L k 0 → ComplexMatrix2) {a : Fin 3}
    (b : FullSpace.PositiveEdge (meshAt L k 0)) {x : FullSpace.Vertex L k 0}
    {f : Fin 3 × FullSpace.Vertex L k 0 → ℂ} (hf : ∀ j, j ≠ (a, x) → f j = 0)
    (hx : x ≠ b.1.initial) (hy : x ≠ b.1.terminal) :
    FullSpace.covDiff U (ofPauliCoeffs f) b.1 = 0 := by
  classical
  simp only [FullSpace.covDiff, FullSpace.extendOddly, if_pos b.2]
  rw [ofPauliCoeffs_eq_zero_of_ne hf hx.symm, ofPauliCoeffs_eq_zero_of_ne hf hy.symm]
  simp [ComplexMatrix2.conjugateBy]
theorem onFullSpace (h₁ : ThreeMapKernels.Claim)
    (h₂ : HessianKernel.KernelProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) : OnFullSpace L k := by
  classical
  intro U hU
  have hη := finestMesh_ne_zero hL k
  have hη' : (finestMesh L k)⁻¹ ≠ 0 := inv_ne_zero hη
  have hpos : 0 < meshAt L k 0 := by
    have h0 : (0 : ℝ) < L := by
      have := hL.2
      have : 0 < L := by omega
      exact_mod_cast this
    exact zpow_pos h0 _
  have hx : ∀ b : FullSpace.Edge L k 0,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun b => by
    rcases InfiniteLattice.xor_mem_positiveLinks hpos b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
    · exact Or.inr ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
  have A := (h₁ L hL k hk).2
  have Uq := (A.1 0 0 (Nat.zero_le _) (Nat.zero_le _)).2.1
  have Dk := A.2.1 U hU
  obtain ⟨hrep, eq⟩ := kernel_smul_of_mapOnCoeffs_eq (vertexCoordinate (FullSpace.Vertex L k 0))
    (FullSpace.edgePauliCoordinates L k 0)
    (FullSpace.covDiff U) (fun l => (finestMesh L k)⁻¹ • FullSpace.covDiff U l)
    (((finestMesh L k)⁻¹ : ℝ) : ℂ)
    (by
      funext f i
      exact pauliCoeff_real_smul hη' i.1 _)
    Dk Uq
  obtain ⟨bil, -, standingConstraints, -, -, symm⟩ := (h₂ L hL k 0 (Nat.zero_le _)).2 U hU
  have mem : ∀ (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L k 0)),
      FullSpace.basisForm a b ∈ HessianKernel.finiteSupportComplexForms L k 0 := fun a b =>
    ⟨fullSpace_basisForm_mem hx a b, fullSpace_basisForm_finiteSupport a b⟩
  have Hh := rowFinite_columnFinite_of_hessian_eq_zero (H := (FullSpace.rescaledOperators L k U).H)
    (fun i i' e => by
      have e' : FullSpace.complexActionHessian U (FullSpace.basisForm i.1 i.2)
          (FullSpace.basisForm i'.1 i'.2) = 0 := e
      show (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) * FullSpace.complexActionHessian U _ _ = 0
      rw [apply_real_smul_real_smul bil fullSpace_zero_mem (finestMesh L k)
        (mem i.1 i.2) (mem i'.1 i'.2) (fullSpace_smul_mem _ (mem i'.1 i'.2)), e']
      simp)
    standingConstraints symm
  refine kernelsWellFormed_of_kernels _ _ _ _ _ _ hrep ?_ ?_ ?_ Hh.1 Hh.2
  · intro a' b a x hx₁ hx₂
    obtain ⟨f, hf, e⟩ := entry_eq_apply_of_represents hrep (a, x) (a', b)
    have hf' : ∀ j : Fin 3 × FullSpace.Vertex L k 0, j ≠ (a, x) → (f j : ℂ) = 0 := hf
    refine e.trans ?_
    show pauliCoeff a' (((finestMesh L k)⁻¹ •
      FullSpace.covDiff U (ofPauliCoeffs f)) b.1) = 0
    rw [Pi.smul_apply, fullSpace_covDiff_ofPauliCoeffs_eq_zero U b hf' hx₁ hx₂, smul_zero,
      pauliCoeff_zero]
  · show RowFinite (PauliComponentsOfSymmetricKernel.kernel _ _ _)
    rw [eq]
    exact Dk.smul_row_finite _
  · show ColumnFinite (PauliComponentsOfSymmetricKernel.kernel _ _ _)
    rw [eq]
    exact Dk.smul_column_finite _
end FullSpace
theorem kernelsWellFormedEverywhere (h₁ : ThreeMapKernels.Claim)
    (h₂ : HessianKernel.KernelProperties)
    (h₃ : PeriodicLattice.BondEndpointsOrientation.Statement) : KernelsWellFormedEverywhere :=
  fun _ hL _ hk => ⟨fun _ hn => onTorus h₁ h₂ h₃ hL hk hn, onFullSpace h₁ h₂ hL hk⟩
end YangMills.Construction.Tower.RescaledKernels
end
