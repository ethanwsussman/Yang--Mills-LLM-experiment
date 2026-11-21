import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Matrices.ConjugationOnTraceless
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATowerProof
import YangMills.Construction.Towers.ConfigurationsWhoseAveragesStayInThePolydiscsProof
import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import YangMills.Construction.Towers.CurvesAtTheSideInfinityInTheLeftChartProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.ThreeMapKernels
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Matrices
section KernelMaps
variable {N N' N'' : Type}
theorem applyKernel_single [DecidableEq N] (T : KernelMatrix N N') (i : N) (i' : N') :
    applyKernel T (Pi.single i 1) i' = T i' i := by
  unfold applyKernel
  rw [tsum_eq_single i]
  · simp
  · intro b hb
    simp [Pi.single_eq_of_ne hb]
theorem kernelUnique (N N' : Type) : KernelUnique N N' := by
  classical
  intro M T T' h h'
  funext i' i
  rw [← applyKernel_single T i i', ← applyKernel_single T' i i', (h _).2, (h' _).2]
theorem applySummable_of_rowFinite {T : KernelMatrix N N'} (hT : RowFinite T) (f : N → ℂ) :
    ApplySummable T f := by
  intro i'
  refine summable_of_hasFiniteSupport ((hT i').subset ?_)
  intro i hi h0
  apply hi
  have h0' : T i' i = 0 := by simpa using h0
  simp [h0']
theorem applyKernel_add {T : KernelMatrix N N'} (hT : RowFinite T) (f g : N → ℂ) :
    applyKernel T (f + g) = applyKernel T f + applyKernel T g := by
  funext i'
  simp only [applyKernel, Pi.add_apply, mul_add]
  exact Summable.tsum_add (Summable.of_norm (applySummable_of_rowFinite hT f i'))
    (Summable.of_norm (applySummable_of_rowFinite hT g i'))
theorem applyKernel_smul (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel T (z • f) = z • applyKernel T f := by
  funext i'
  simp only [applyKernel, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun i => by ring
theorem represents_smul {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ} (h : Represents T M)
    (z : ℂ) : Represents (z • T) (z • M) := by
  intro f
  refine ⟨fun i' => ?_, ?_⟩
  · have := ((h f).1 i').mul_left ‖z‖
    refine this.congr fun i => ?_
    simp [mul_assoc]
  · funext i'
    have e := congrFun (h f).2 i'
    simp only [Pi.smul_apply, smul_eq_mul, ← e, applyKernel]
    rw [← tsum_mul_left]
    exact tsum_congr fun i => by ring
theorem rowFinite_smul {T : KernelMatrix N N'} (h : RowFinite T) (z : ℂ) :
    RowFinite (z • T) := fun i' =>
  (h i').subset fun i hi h0 => hi (by simp [show T i' i = 0 from h0])
theorem columnFinite_smul {T : KernelMatrix N N'} (h : ColumnFinite T) (z : ℂ) :
    ColumnFinite (z • T) := fun i =>
  (h i).subset fun i' hi' h0 => hi' (by simp [show T i' i = 0 from h0])
structure LocallyReads (M : (N → ℂ) → N' → ℂ) (R : N' → Set N) : Prop where
  map_add : ∀ f g, M (f + g) = M f + M g
  map_smul : ∀ (z : ℂ) f, M (z • f) = z • M f
  reads_finite : ∀ i', (R i').Finite
  readers_finite : ∀ i, {i' | i ∈ R i'}.Finite
  apply_eq_zero : ∀ f i', (∀ i ∈ R i', f i = 0) → M f i' = 0
def basisKernel (M : (N → ℂ) → N' → ℂ) : KernelMatrix N N' :=
  open Classical in fun i' i => M (Pi.single i 1) i'
namespace LocallyReads
variable {M : (N → ℂ) → N' → ℂ} {R : N' → Set N}
theorem basisKernel_eq_zero (h : LocallyReads M R) {i : N} {i' : N'} (hi : i ∉ R i') :
    basisKernel M i' i = 0 := by
  classical
  refine h.apply_eq_zero _ _ fun i₂ h₂ => ?_
  rw [Pi.single_eq_of_ne]
  rintro rfl
  exact hi h₂
theorem rowFinite (h : LocallyReads M R) : RowFinite (basisKernel M) := fun i' =>
  (h.reads_finite i').subset fun i hi => by
    by_contra h'
    exact hi (h.basisKernel_eq_zero h')
theorem columnFinite (h : LocallyReads M R) : ColumnFinite (basisKernel M) := fun i =>
  (h.readers_finite i).subset fun i' hi' => by
    by_contra h'
    exact hi' (h.basisKernel_eq_zero h')
theorem represents (h : LocallyReads M R) : Represents (basisKernel M) M := by
  classical
  intro f
  refine ⟨applySummable_of_rowFinite h.rowFinite f, ?_⟩
  funext i'
  let Ml : (N → ℂ) →ₗ[ℂ] (N' → ℂ) := ⟨⟨M, h.map_add⟩, h.map_smul⟩
  let F : Finset N := (h.reads_finite i').toFinset
  let g : N → ℂ := ∑ i ∈ F, f i • Pi.single i (1 : ℂ)
  have hg : ∀ i ∈ R i', (f - g) i = 0 := by
    intro i hi
    have hF : i ∈ F := (h.reads_finite i').mem_toFinset.2 hi
    have : g i = f i := by
      simp only [g, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · exact fun h' => absurd hF h'
    simp [this]
  have e1 : Ml (f - g) i' = 0 := h.apply_eq_zero _ _ hg
  have e2 : M f i' = Ml g i' := by
    have : Ml f i' - Ml g i' = 0 := by
      rw [map_sub] at e1
      simpa using e1
    exact sub_eq_zero.1 this
  have e3 : Ml g i' = ∑ i ∈ F, basisKernel M i' i * f i := by
    simp only [g, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.map_smul Ml, Pi.smul_apply, smul_eq_mul, mul_comm]
    rfl
  rw [e2, e3]
  unfold applyKernel
  refine tsum_eq_sum fun i hi => ?_
  rw [h.basisKernel_eq_zero fun h' => hi ((h.reads_finite i').mem_toFinset.2 h'), zero_mul]
theorem add {M₁ M₂ : (N → ℂ) → N' → ℂ} {R₁ R₂ : N' → Set N} (h₁ : LocallyReads M₁ R₁)
    (h₂ : LocallyReads M₂ R₂) :
    LocallyReads (fun f => M₁ f + M₂ f) (fun i' => R₁ i' ∪ R₂ i') where
  map_add f g := by
    simp only [h₁.map_add, h₂.map_add]
    abel
  map_smul z f := by
    simp only [h₁.map_smul, h₂.map_smul, smul_add]
  reads_finite i' := (h₁.reads_finite i').union (h₂.reads_finite i')
  readers_finite i :=
    ((h₁.readers_finite i).union (h₂.readers_finite i)).subset fun i' h => h
  apply_eq_zero f i' h := by
    show M₁ f i' + M₂ f i' = 0
    rw [h₁.apply_eq_zero f i' fun i hi => h i (Or.inl hi),
      h₂.apply_eq_zero f i' fun i hi => h i (Or.inr hi), add_zero]
theorem comp {M₁ : (N → ℂ) → N' → ℂ} {M₂ : (N' → ℂ) → N'' → ℂ} {R₁ : N' → Set N}
    {R₂ : N'' → Set N'} (h₁ : LocallyReads M₁ R₁) (h₂ : LocallyReads M₂ R₂) :
    LocallyReads (fun f => M₂ (M₁ f)) (fun i'' => ⋃ i' ∈ R₂ i'', R₁ i') where
  map_add f g := by
    simp only [h₁.map_add, h₂.map_add]
  map_smul z f := by
    simp only [h₁.map_smul, h₂.map_smul]
  reads_finite i'' := (h₂.reads_finite i'').biUnion fun i' _ => h₁.reads_finite i'
  readers_finite i := by
    refine ((h₁.readers_finite i).biUnion fun i' _ => h₂.readers_finite i').subset
      fun i'' h => ?_
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop] at h ⊢
    obtain ⟨i', h', h''⟩ := h
    exact ⟨i', h'', h'⟩
  apply_eq_zero f i'' h := by
    refine h₂.apply_eq_zero _ _ fun i' hi' => h₁.apply_eq_zero _ _ fun i hi => h i ?_
    simp only [mem_iUnion, exists_prop]
    exact ⟨i', hi', hi⟩
end LocallyReads
end KernelMaps
section PauliCoeffs
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem sum_smul_pauli_mem (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.LieInnerProductProof.pauliCombination_mem_traceless <;> assumption
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by
  unfold pauliCoeff
  rw [dif_pos (sum_smul_pauli_mem x)]
  show (![_, _, _] : Fin 3 → ℂ) a = x a
  fin_cases a
  · simp [Fin.sum_univ_three, ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ]
    ring
  · simp [Fin.sum_univ_three, ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ]
    field_simp
    ring
  · simp [Fin.sum_univ_three, ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ]
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by
  have hY := sum_smul_pauli_mem fun a => pauliCoeff a X
  have e : OneLoop.pauliCoordinateEquiv ⟨_, hY⟩ = OneLoop.pauliCoordinateEquiv ⟨X, hX⟩ := by
    funext a
    have h := pauliCoeff_sum_smul (fun a => pauliCoeff a X) a
    have e₁ : pauliCoeff a (∑ b, pauliCoeff b X • ComplexMatrix2.pauliFamily b) =
        OneLoop.pauliCoordinateEquiv ⟨_, hY⟩ a := dif_pos hY
    have e₂ : pauliCoeff a X = OneLoop.pauliCoordinateEquiv ⟨X, hX⟩ a := dif_pos hX
    rw [← e₁, ← e₂]
    exact h
  exact congrArg Subtype.val (OneLoop.pauliCoordinateEquiv.injective e)
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by
  simpa using pauliCoeff_sum_smul (fun _ => 0) a
theorem halfTrace_mul_sums (hP : OneLoop.PauliMatrixRelations) (x y : Fin 3 → ℂ) :
    ComplexMatrix2.halfTrace
        ((∑ a, x a • ComplexMatrix2.pauliFamily a) * ∑ a, y a • ComplexMatrix2.pauliFamily a) =
      ∑ a, x a * y a :=
  hP.2.2.2.2.1 ⟨_, sum_smul_pauli_mem x⟩ ⟨_, sum_smul_pauli_mem y⟩ x y rfl rfl
end PauliCoeffs
structure IsFaithfulEvaluation (r : PauliComponentsOfSymmetricKernel) : Prop where
  ofCoeffs_mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  coeffs_ofCoeffs : ∀ c, r.coeffs (r.ofCoeffs c) = c
  ofCoeffs_coeffs : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  ofCoeffs_add : ∀ c c', r.ofCoeffs (c + c') = r.ofCoeffs c + r.ofCoeffs c'
  ofCoeffs_smul : ∀ (z : ℂ) c, r.ofCoeffs (z • c) = z • r.ofCoeffs c
  finite_iff : ∀ c, r.space.IsFinitelySupported (r.ofCoeffs c) ↔ (Function.support c).Finite
  pair_eq : ∀ a b, (Function.support b).Finite →
    r.space.pair (r.ofCoeffs a) (r.ofCoeffs b) = ∑ᶠ i, a i * b i
namespace IsFaithfulEvaluation
variable {r : PauliComponentsOfSymmetricKernel}
theorem coeffs_add (h : IsFaithfulEvaluation r) {f g : r.space.index → ComplexMatrix2}
    (hf : f ∈ r.space.complexSubmodule) (hg : g ∈ r.space.complexSubmodule) :
    r.coeffs (f + g) = r.coeffs f + r.coeffs g := by
  have e : f + g = r.ofCoeffs (r.coeffs f + r.coeffs g) := by
    rw [h.ofCoeffs_add, h.ofCoeffs_coeffs f hf, h.ofCoeffs_coeffs g hg]
  conv_lhs => rw [e, h.coeffs_ofCoeffs]
theorem coeffs_smul (h : IsFaithfulEvaluation r) (z : ℂ) {f : r.space.index → ComplexMatrix2}
    (hf : f ∈ r.space.complexSubmodule) : r.coeffs (z • f) = z • r.coeffs f := by
  have e : z • f = r.ofCoeffs (z • r.coeffs f) := by
    rw [h.ofCoeffs_smul, h.ofCoeffs_coeffs f hf]
  conv_lhs => rw [e, h.coeffs_ofCoeffs]
theorem ofCoeffs_zero (h : IsFaithfulEvaluation r) : r.ofCoeffs 0 = 0 := by
  have e := h.ofCoeffs_smul 0 0
  simpa using e
theorem coeffs_zero (h : IsFaithfulEvaluation r) : r.coeffs 0 = 0 := by
  have e := h.coeffs_ofCoeffs 0
  rwa [h.ofCoeffs_zero] at e
end IsFaithfulEvaluation
structure IsLocalMap (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2) : Prop where
  mapsTo : ∀ f ∈ r.space.complexSubmodule, m f ∈ r'.space.complexSubmodule
  exists_reads : ∃ R, LocallyReads (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m) R
section Local
variable {r r' r'' : PauliComponentsOfSymmetricKernel}
theorem isLocalMap_of_linear (hr : IsFaithfulEvaluation r) (hr' : IsFaithfulEvaluation r')
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (maps : ∀ f ∈ r.space.complexSubmodule, m f ∈ r'.space.complexSubmodule)
    (hadd : ∀ f ∈ r.space.complexSubmodule, ∀ g ∈ r.space.complexSubmodule,
      m (f + g) = m f + m g)
    (hsmul : ∀ f ∈ r.space.complexSubmodule, ∀ z : ℂ, m (z • f) = z • m f)
    (R : r'.Index → Set r.Index) (standingConstraints : ∀ i', (R i').Finite)
    (columns : ∀ i, {i' | i ∈ R i'}.Finite)
    (reads : ∀ f ∈ r.space.complexSubmodule, ∀ i', (∀ i ∈ R i', r.coeffs f i = 0) →
      r'.coeffs (m f) i' = 0) : IsLocalMap r r' m := by
  refine ⟨maps, R, ?_, ?_, standingConstraints, columns, ?_⟩
  · intro c c'
    show r'.coeffs (m (r.ofCoeffs (c + c'))) = r'.coeffs (m (r.ofCoeffs c)) +
      r'.coeffs (m (r.ofCoeffs c'))
    rw [hr.ofCoeffs_add, hadd _ (hr.ofCoeffs_mem c) _ (hr.ofCoeffs_mem c'),
      hr'.coeffs_add (maps _ (hr.ofCoeffs_mem c)) (maps _ (hr.ofCoeffs_mem c'))]
  · intro z c
    show r'.coeffs (m (r.ofCoeffs (z • c))) = z • r'.coeffs (m (r.ofCoeffs c))
    rw [hr.ofCoeffs_smul, hsmul _ (hr.ofCoeffs_mem c),
      hr'.coeffs_smul z (maps _ (hr.ofCoeffs_mem c))]
  · intro c i' h
    refine reads _ (hr.ofCoeffs_mem c) i' fun i hi => ?_
    rw [hr.coeffs_ofCoeffs]
    exact h i hi
theorem isLocalMap_of_finite (hr : IsFaithfulEvaluation r) (hr' : IsFaithfulEvaluation r')
    [Finite r.Index] [Finite r'.Index]
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (maps : ∀ f ∈ r.space.complexSubmodule, m f ∈ r'.space.complexSubmodule)
    (hadd : ∀ f ∈ r.space.complexSubmodule, ∀ g ∈ r.space.complexSubmodule,
      m (f + g) = m f + m g)
    (hsmul : ∀ f ∈ r.space.complexSubmodule, ∀ z : ℂ, m (z • f) = z • m f) :
    IsLocalMap r r' m := by
  refine isLocalMap_of_linear hr hr' maps hadd hsmul (fun _ => univ) (fun _ => toFinite _)
    (fun _ => toFinite _) ?_
  intro f hf i' h
  have e : r.coeffs f = 0 := funext fun i => h i (mem_univ _)
  have e0 : f = 0 := by
    rw [← hr.ofCoeffs_coeffs f hf, e, hr.ofCoeffs_zero]
  have e1 : m 0 = 0 := by
    have := hsmul 0 (r.space.complexSubmodule.zero_mem) 0
    simpa using this
  rw [e0, e1, hr'.coeffs_zero]
  rfl
theorem IsLocalMap.id (hr : IsFaithfulEvaluation r) : IsLocalMap r r fun f => f :=
  isLocalMap_of_linear hr hr (fun _ h => h) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun i => {i}) (fun _ => finite_singleton _) (fun i => by simp) fun _ _ i' h => h i' rfl
theorem IsLocalMap.add (hr : IsFaithfulEvaluation r) (hr' : IsFaithfulEvaluation r')
    {m₁ m₂ : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (h₁ : IsLocalMap r r' m₁) (h₂ : IsLocalMap r r' m₂) :
    IsLocalMap r r' fun f => m₁ f + m₂ f := by
  obtain ⟨hm₁, R₁, hR₁⟩ := h₁
  obtain ⟨hm₂, R₂, hR₂⟩ := h₂
  refine ⟨fun f hf => r'.space.complexSubmodule.add_mem (hm₁ f hf) (hm₂ f hf),
    fun i' => R₁ i' ∪ R₂ i', ?_⟩
  have e : PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' (fun f => m₁ f + m₂ f) =
      fun c => PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m₁ c + PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m₂ c := by
    funext c
    exact hr'.coeffs_add (hm₁ _ (hr.ofCoeffs_mem c)) (hm₂ _ (hr.ofCoeffs_mem c))
  rw [e]
  exact hR₁.add hR₂
theorem IsLocalMap.comp (hr : IsFaithfulEvaluation r) (hr' : IsFaithfulEvaluation r')
    {m₁ : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    {m₂ : (r'.space.index → ComplexMatrix2) → r''.space.index → ComplexMatrix2}
    (h₁ : IsLocalMap r r' m₁) (h₂ : IsLocalMap r' r'' m₂) :
    IsLocalMap r r'' fun f => m₂ (m₁ f) := by
  obtain ⟨hm₁, R₁, hR₁⟩ := h₁
  obtain ⟨hm₂, R₂, hR₂⟩ := h₂
  refine ⟨fun f hf => hm₂ _ (hm₁ f hf), fun i'' => ⋃ i' ∈ R₂ i'', R₁ i', ?_⟩
  have e : PauliComponentsOfSymmetricKernel.mapOnCoeffs r r'' (fun f => m₂ (m₁ f)) =
      fun c => PauliComponentsOfSymmetricKernel.mapOnCoeffs r' r'' m₂ (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m₁ c) := by
    funext c
    show r''.coeffs (m₂ (m₁ (r.ofCoeffs c))) =
      r''.coeffs (m₂ (r'.ofCoeffs (r'.coeffs (m₁ (r.ofCoeffs c)))))
    rw [hr'.ofCoeffs_coeffs _ (hm₁ _ (hr.ofCoeffs_mem c))]
  rw [e]
  exact hR₁.comp hR₂
theorem IsLocalMap.hasLocalKernel (hT : RowFiniteKernels.TransposeDuality)
    (hr : IsFaithfulEvaluation r) (hr' : IsFaithfulEvaluation r')
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (h : IsLocalMap r r' m) : PauliComponentsOfSymmetricKernel.HasLocalKernel r r' m := by
  classical
  obtain ⟨hmaps, R, hR⟩ := h
  have hE : Represents (basisKernel (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m))
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m) := hR.represents
  have hK : Represents (PauliComponentsOfSymmetricKernel.kernel r r' m) (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m) :=
    Classical.epsilon_spec (p := fun T => Represents T (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m)) ⟨_, hE⟩
  have hKE : PauliComponentsOfSymmetricKernel.kernel r r' m = basisKernel (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m) :=
    kernelUnique _ _ _ _ _ hK hE
  have hrows : RowFinite (PauliComponentsOfSymmetricKernel.kernel r r' m) := hKE ▸ hR.rowFinite
  have hcols : ColumnFinite (PauliComponentsOfSymmetricKernel.kernel r r' m) := hKE ▸ hR.columnFinite
  set K := PauliComponentsOfSymmetricKernel.kernel r r' m with hKdef
  set M := PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m with hMdef
  have hrowsT : RowFinite (swapKernel K) := hcols
  have hcolsT : ColumnFinite (swapKernel K) := hrows
  have hm_eq : ∀ f ∈ r.space.complexSubmodule, m f = r'.ofCoeffs (M (r.coeffs f)) := by
    intro f hf
    show m f = r'.ofCoeffs (r'.coeffs (m (r.ofCoeffs (r.coeffs f))))
    rw [hr.ofCoeffs_coeffs f hf, hr'.ofCoeffs_coeffs _ (hmaps f hf)]
  have hsupp : ∀ c : r.Index → ℂ, (Function.support c).Finite →
      (Function.support (M c)).Finite := by
    intro c hc
    refine (hc.biUnion fun i _ => hR.readers_finite i).subset fun i' hi' => ?_
    by_contra hn
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop, not_exists, not_and] at hn
    refine hi' (hR.apply_eq_zero c i' fun i hi => ?_)
    by_contra hc'
    exact hn i hc' hi
  have hA₀ : ∃ A : r.space.complexSubmodule →ₗ[ℂ] r'.space.complexSubmodule,
      ∀ f : r.space.complexSubmodule, (A f : r'.space.index → ComplexMatrix2) = m f := by
    refine ⟨{
      toFun := fun f => ⟨m f, hmaps f f.2⟩
      map_add' := fun f g => ?_
      map_smul' := fun z f => ?_ }, fun f => rfl⟩
    · apply Subtype.ext
      show m (f.1 + g.1) = m f.1 + m g.1
      rw [hm_eq _ (r.space.complexSubmodule.add_mem f.2 g.2), hr.coeffs_add f.2 g.2,
        hR.map_add, hr'.ofCoeffs_add, ← hm_eq _ f.2, ← hm_eq _ g.2]
    · apply Subtype.ext
      show m (z • f.1) = z • m f.1
      rw [hm_eq _ (r.space.complexSubmodule.smul_mem z f.2), hr.coeffs_smul z f.2,
        hR.map_smul, hr'.ofCoeffs_smul, ← hm_eq _ f.2]
  have hA : ∀ f : r.space.complexSubmodule,
      (PairedFunctionSpace.linearOfValues r.space r'.space m f :
        r'.space.index → ComplexMatrix2) = m f :=
    Classical.epsilon_spec
      (p := fun T : r.space.complexSubmodule →ₗ[ℂ] r'.space.complexSubmodule =>
        ∀ f : r.space.complexSubmodule, (T f : r'.space.index → ComplexMatrix2) = m f) hA₀
  set A := PairedFunctionSpace.linearOfValues r.space r'.space m with hAdef
  let A' : r'.space.complexSubmodule →ₗ[ℂ] r.space.complexSubmodule :=
    { toFun := fun g =>
        ⟨r.ofCoeffs (applyKernel (swapKernel K) (r'.coeffs g.1)), hr.ofCoeffs_mem _⟩
      map_add' := fun g g' => by
        apply Subtype.ext
        show r.ofCoeffs (applyKernel (swapKernel K) (r'.coeffs (g.1 + g'.1))) = _
        rw [hr'.coeffs_add g.2 g'.2, applyKernel_add hrowsT, hr.ofCoeffs_add]
        rfl
      map_smul' := fun z g => by
        apply Subtype.ext
        show r.ofCoeffs (applyKernel (swapKernel K) (r'.coeffs (z • g.1))) = _
        rw [hr'.coeffs_smul z g.2, applyKernel_smul, hr.ofCoeffs_smul]
        rfl }
  have hIT : PairedFunctionSpace.IsTransposeMap A A' := by
    intro g f hf
    have hcf : (Function.support (r.coeffs f.1)).Finite := by
      have e := (hr.finite_iff (r.coeffs f.1)).1
      rw [hr.ofCoeffs_coeffs f.1 f.2] at e
      exact e hf
    have eL : r.space.pair (A' g) f =
        ∑ᶠ i, applyKernel (swapKernel K) (r'.coeffs g.1) i * r.coeffs f.1 i := by
      have e := hr.pair_eq (applyKernel (swapKernel K) (r'.coeffs g.1)) (r.coeffs f.1) hcf
      rw [hr.ofCoeffs_coeffs f.1 f.2] at e
      exact e
    have eR : r'.space.pair g (A f) = ∑ᶠ i', r'.coeffs g.1 i' * M (r.coeffs f.1) i' := by
      have e := hr'.pair_eq (r'.coeffs g.1) (M (r.coeffs f.1)) (hsupp _ hcf)
      rw [hr'.ofCoeffs_coeffs g.1 g.2, ← hm_eq f.1 f.2, ← hA f] at e
      exact e
    rw [eL, eR]
    have key := (hT r.Index r'.Index (swapKernel K) (fun _ => 1) (fun _ => 1) hrowsT
      (fun _ => one_pos) (fun _ => one_pos) (r.coeffs f.1) hcf (r'.coeffs g.1)).2.2.2.2.2
    have eT : wTranspose (fun _ : r'.Index => (1 : ℝ)) (fun _ : r.Index => (1 : ℝ))
        (swapKernel K) = K := by
      funext i' i
      simp [wTranspose, swapKernel]
    rw [eT, (hK _).2] at key
    simp only [Complex.ofReal_one, one_mul] at key
    calc _ = ∑ᶠ i, r.coeffs f.1 i * applyKernel (swapKernel K) (r'.coeffs g.1) i :=
          finsum_congr fun i => mul_comm _ _
      _ = ∑ᶠ i', M (r.coeffs f.1) i' * r'.coeffs g.1 i' := key.symm
      _ = _ := finsum_congr fun i => mul_comm _ _
  have hTt : PairedFunctionSpace.IsTransposeMap A (PairedFunctionSpace.transposeMap A) :=
    Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap A) ⟨A', hIT⟩
  have hcol : ∀ g : r'.space.complexSubmodule,
      r.coeffs (PairedFunctionSpace.transposeMap A g).1 =
        applyKernel (swapKernel K) (r'.coeffs g.1) := by
    intro g
    funext i
    have hfin : (Function.support (Pi.single i (1 : ℂ) : r.Index → ℂ)).Finite :=
      (finite_singleton i).subset fun x hx => by
        by_contra hne
        exact hx (Pi.single_eq_of_ne hne _)
    have he : r.space.IsFinitelySupported (r.ofCoeffs (Pi.single i 1)) :=
      (hr.finite_iff _).2 hfin
    have ev : ∀ X ∈ r.space.complexSubmodule,
        r.space.pair X (r.ofCoeffs (Pi.single i 1)) = r.coeffs X i := by
      intro X hX
      have e := hr.pair_eq (r.coeffs X) (Pi.single i 1) hfin
      rw [hr.ofCoeffs_coeffs X hX] at e
      rw [e, finsum_eq_single _ i]
      · simp
      · intro x hx
        simp [Pi.single_eq_of_ne hx]
    have h1 := hTt g ⟨_, hr.ofCoeffs_mem (Pi.single i 1)⟩ he
    have h2 := hIT g ⟨_, hr.ofCoeffs_mem (Pi.single i 1)⟩ he
    rw [← h2] at h1
    have e1 := ev _ (PairedFunctionSpace.transposeMap A g).2
    have e2 := ev _ (A' g).2
    have e3 : r.coeffs (A' g).1 = applyKernel (swapKernel K) (r'.coeffs g.1) :=
      hr.coeffs_ofCoeffs _
    rw [← e1, h1, e2, e3]
  have htr : PauliComponentsOfSymmetricKernel.transposeOnCoeffs r r' m = applyKernel (swapKernel K) := by
    funext c
    show r.coeffs (PairedFunctionSpace.transposeOfValues r.space r'.space m (r'.ofCoeffs c)) = _
    unfold PairedFunctionSpace.transposeOfValues
    rw [dif_pos (hr'.ofCoeffs_mem c)]
    have e := hcol ⟨_, hr'.ofCoeffs_mem c⟩
    rw [show r'.coeffs (r'.ofCoeffs c) = c from hr'.coeffs_ofCoeffs c] at e
    exact e
  have hgT : Represents (swapKernel K) (PauliComponentsOfSymmetricKernel.transposeOnCoeffs r r' m) := fun c =>
    ⟨applySummable_of_rowFinite hrowsT c, by rw [htr]⟩
  exact
    { represents := hK
      unique := fun T hT' => kernelUnique _ _ _ _ _ hT' hK
      row_finite := hrows
      column_finite := hcols
      finitely_supported := fun f hf hfs => by
        have hc : (Function.support (r.coeffs f)).Finite := by
          have e := (hr.finite_iff (r.coeffs f)).1
          rw [hr.ofCoeffs_coeffs f hf] at e
          exact e hfs
        rw [hm_eq f hf]
        exact (hr'.finite_iff _).2 (hsupp _ hc)
      swap_represents := hgT
      smul_represents := fun z => represents_smul hK z
      smul_row_finite := fun z => rowFinite_smul hrows z
      smul_column_finite := fun z => columnFinite_smul hcols z
      smul_swap_represents := fun z => represents_smul hgT z
      smul_swap_row_finite := fun z => rowFinite_smul hrowsT z
      smul_swap_column_finite := fun z => columnFinite_smul hcolsT z }
end Local
section Vertices
variable {σ : Type}
theorem ofPauliCoeffs_mem (c : Fin 3 × σ → ℂ) (i : σ) :
    ofPauliCoeffs c i ∈ ComplexMatrix2.traceless :=
  sum_smul_pauli_mem fun a => c (a, i)
theorem toPauliCoeffs_ofPauliCoeffs (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c :=
  funext fun p => pauliCoeff_sum_smul (fun a => c (a, p.2)) p.1
theorem ofPauliCoeffs_add (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (c + c') = ofPauliCoeffs c + ofPauliCoeffs c' :=
  funext fun i => by
    simp [ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
theorem ofPauliCoeffs_smul (z : ℂ) (c : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (z • c) = z • ofPauliCoeffs c :=
  funext fun i => by
    simp [ofPauliCoeffs, Finset.smul_sum, mul_smul]
theorem hasFiniteSupp_ofPauliCoeffs_iff (c : Fin 3 × σ → ℂ) :
    HasFiniteSupp (ofPauliCoeffs c) ↔ (Function.support c).Finite := by
  constructor
  · intro h
    refine (Set.Finite.prod (Set.finite_univ (α := Fin 3)) h).subset ?_
    rintro ⟨a, i⟩ hp
    refine ⟨mem_univ _, fun h0 => hp ?_⟩
    have e := pauliCoeff_sum_smul (fun a => c (a, i)) a
    have h0' : ∑ b, c (b, i) • ComplexMatrix2.pauliFamily b = 0 := h0
    rw [h0', pauliCoeff_zero] at e
    exact e.symm
  · intro h
    refine (h.image Prod.snd).subset ?_
    intro i hi
    by_contra hn
    apply hi
    refine Finset.sum_eq_zero fun a _ => ?_
    have e : c (a, i) = 0 := by
      by_contra hc
      exact hn ⟨(a, i), hc, rfl⟩
    simp [e]
theorem traceFinsumPairing_ofPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    (a b : Fin 3 × σ → ℂ) (hb : (Function.support b).Finite) :
    traceFinsumPairing (ofPauliCoeffs a) (ofPauliCoeffs b) = ∑ᶠ p, a p * b p := by
  unfold traceFinsumPairing
  have e : ∀ i, ComplexMatrix2.halfTrace (ofPauliCoeffs a i * ofPauliCoeffs b i) =
      ∑ e, a (e, i) * b (e, i) := fun i =>
    halfTrace_mul_sums hP (fun e => a (e, i)) (fun e => b (e, i))
  simp only [e]
  have hs : (Function.support fun p => a p * b p).Finite :=
    hb.subset fun p h h0 => h (by simp [show b p = 0 from h0])
  have e₂ : ∑ᶠ p, a p * b p = ∑ e : Fin 3, ∑ᶠ i, a (e, i) * b (e, i) := by
    rw [finsum_curry _ hs]
    exact finsum_eq_sum_of_fintype _
  rw [e₂]
  refine finsum_sum_comm _ _ fun e _ => ?_
  have hinj : Function.Injective fun i : σ => (e, i) := fun i i' h => (Prod.ext_iff.1 h).2
  exact hs.preimage hinj.injOn
theorem vertexCoordinate_isFaithful (hP : OneLoop.PauliMatrixRelations) (σ : Type) :
    IsFaithfulEvaluation (vertexCoordinate σ) where
  ofCoeffs_mem c := fun i _ => ofPauliCoeffs_mem c i
  coeffs_ofCoeffs c := toPauliCoeffs_ofPauliCoeffs c
  ofCoeffs_coeffs f hf := funext fun i => sum_pauliCoeff_smul (hf i (mem_univ i))
  ofCoeffs_add c c' := ofPauliCoeffs_add c c'
  ofCoeffs_smul z c := ofPauliCoeffs_smul z c
  finite_iff c := hasFiniteSupp_ofPauliCoeffs_iff c
  pair_eq a b hb := traceFinsumPairing_ofPauliCoeffs hP a b hb
theorem eq_zero_of_pauliCoeffs {f : σ → ComplexMatrix2} {x : σ}
    (hx : f x ∈ ComplexMatrix2.traceless) (h : ∀ a, toPauliCoeffs f (a, x) = 0) : f x = 0 := by
  rw [← sum_pauliCoeff_smul hx]
  exact Finset.sum_eq_zero fun a _ => by
    have e : pauliCoeff a (f x) = 0 := h a
    rw [e, zero_smul]
end Vertices
section Oriented
variable (S : PairedFunctionSpace) (pos : S.index → Prop) (rev : S.index → S.index)
def oddExtension (f : S.index → ComplexMatrix2) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if pos b then f b else -f (rev b)
def zeroExtension (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if h : pos b then ofPauliCoeffs c ⟨b, h⟩ else 0
def formOfCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  oddExtension S pos rev (zeroExtension S pos c)
def positivePart (B : S.index → ComplexMatrix2) : {b : S.index // pos b} → ComplexMatrix2 :=
  fun b => B b.1
def positiveRepresentation : PauliComponentsOfSymmetricKernel where
  space := S
  Place := {b : S.index // pos b}
  ofCoeffs := formOfCoeffs S pos rev
  coeffs := fun B => toPauliCoeffs (positivePart S pos B)
structure IsOrientedSpace : Prop where
  xor_pos : ∀ b, Xor (pos b) (pos (rev b))
  rev_rev : ∀ b, rev (rev b) = b
  mem_complex_iff : ∀ B, B ∈ S.complexSubmodule ↔
    (∀ b, pos b → B b ∈ ComplexMatrix2.traceless) ∧ ∀ b, B (rev b) = -B b
  finitelySupported_iff : ∀ B, S.IsFinitelySupported B ↔ HasFiniteSupp (positivePart S pos B)
  pair_eq : ∀ B B', S.pair B B' = traceFinsumPairing (positivePart S pos B) (positivePart S pos B')
variable {S pos rev}
theorem oddExtension_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : pos b) :
    oddExtension S pos rev f b = f b :=
  if_pos h
theorem oddExtension_neg {f : S.index → ComplexMatrix2} {b : S.index} (h : ¬ pos b) :
    oddExtension S pos rev f b = -f (rev b) :=
  if_neg h
theorem oddExtension_rev (hF : IsOrientedSpace S pos rev) (f : S.index → ComplexMatrix2)
    (b : S.index) : oddExtension S pos rev f (rev b) = -oddExtension S pos rev f b := by
  rcases hF.xor_pos b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [oddExtension_neg h₂, oddExtension_pos h₁, hF.rev_rev]
  · rw [oddExtension_pos h₁, oddExtension_neg h₂, neg_neg]
theorem oddExtension_add (f g : S.index → ComplexMatrix2) :
    oddExtension S pos rev (f + g) = oddExtension S pos rev f + oddExtension S pos rev g := by
  funext b
  by_cases h : pos b
  · simp only [Pi.add_apply, oddExtension_pos h]
  · simp only [Pi.add_apply, oddExtension_neg h, neg_add]
theorem oddExtension_smul (z : ℂ) (f : S.index → ComplexMatrix2) :
    oddExtension S pos rev (z • f) = z • oddExtension S pos rev f := by
  funext b
  by_cases h : pos b
  · simp only [Pi.smul_apply, oddExtension_pos h]
  · simp only [Pi.smul_apply, oddExtension_neg h, smul_neg]
theorem formOfCoeffs_apply (c : Fin 3 × {b : S.index // pos b} → ℂ) (b : S.index)
    (hb : pos b) : formOfCoeffs S pos rev c b = ofPauliCoeffs c ⟨b, hb⟩ := by
  unfold formOfCoeffs zeroExtension
  rw [oddExtension_pos hb, dif_pos hb]
theorem positivePart_formOfCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    positivePart S pos (formOfCoeffs S pos rev c) = ofPauliCoeffs c :=
  funext fun b => formOfCoeffs_apply c b.1 b.2
theorem zeroExtension_add (c c' : Fin 3 × {b : S.index // pos b} → ℂ) :
    zeroExtension S pos (c + c') = zeroExtension S pos c + zeroExtension S pos c' := by
  funext b
  by_cases hb : pos b
  · simp only [zeroExtension, Pi.add_apply, dif_pos hb, ofPauliCoeffs_add]
  · simp only [zeroExtension, Pi.add_apply, dif_neg hb, add_zero]
theorem zeroExtension_smul (z : ℂ) (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    zeroExtension S pos (z • c) = z • zeroExtension S pos c := by
  funext b
  by_cases hb : pos b
  · simp only [zeroExtension, Pi.smul_apply, dif_pos hb, ofPauliCoeffs_smul]
  · simp only [zeroExtension, Pi.smul_apply, dif_neg hb, smul_zero]
theorem formOfCoeffs_add (c c' : Fin 3 × {b : S.index // pos b} → ℂ) :
    formOfCoeffs S pos rev (c + c') = formOfCoeffs S pos rev c + formOfCoeffs S pos rev c' := by
  unfold formOfCoeffs
  rw [zeroExtension_add, oddExtension_add]
theorem formOfCoeffs_smul (z : ℂ) (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    formOfCoeffs S pos rev (z • c) = z • formOfCoeffs S pos rev c := by
  unfold formOfCoeffs
  rw [zeroExtension_smul, oddExtension_smul]
theorem formOfCoeffs_toPauliCoeffs (hF : IsOrientedSpace S pos rev) {f : S.index → ComplexMatrix2}
    (h₁ : ∀ b, pos b → f b ∈ ComplexMatrix2.traceless) (h₂ : ∀ b, f (rev b) = -f b) :
    formOfCoeffs S pos rev (toPauliCoeffs (positivePart S pos f)) = f := by
  have hpos : ∀ b (hb : pos b),
      formOfCoeffs S pos rev (toPauliCoeffs (positivePart S pos f)) b = f b := fun b hb =>
    (formOfCoeffs_apply _ b hb).trans (sum_pauliCoeff_smul (h₁ b hb))
  funext b
  by_cases hb : pos b
  · exact hpos b hb
  · have hrb : pos (rev b) := by
      rcases hF.xor_pos b with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hb
      · exact h
    have e : formOfCoeffs S pos rev (toPauliCoeffs (positivePart S pos f)) b =
        -zeroExtension S pos (toPauliCoeffs (positivePart S pos f)) (rev b) :=
      oddExtension_neg hb
    have e' : zeroExtension S pos (toPauliCoeffs (positivePart S pos f)) (rev b) = f (rev b) := by
      rw [← hpos _ hrb]
      exact (oddExtension_pos hrb).symm
    rw [e, e', h₂, neg_neg]
theorem positiveRepresentation_isFaithful (hP : OneLoop.PauliMatrixRelations)
    (hF : IsOrientedSpace S pos rev) : IsFaithfulEvaluation (positiveRepresentation S pos rev) where
  ofCoeffs_mem c := (hF.mem_complex_iff _).2 ⟨fun b hb => by
    have e : formOfCoeffs S pos rev c b ∈ ComplexMatrix2.traceless := by
      rw [formOfCoeffs_apply c b hb]
      exact ofPauliCoeffs_mem c _
    exact e, fun b => oddExtension_rev hF _ b⟩
  coeffs_ofCoeffs c := (congrArg toPauliCoeffs (positivePart_formOfCoeffs c)).trans
    (toPauliCoeffs_ofPauliCoeffs c)
  ofCoeffs_coeffs f hf := formOfCoeffs_toPauliCoeffs hF ((hF.mem_complex_iff f).1 hf).1
    ((hF.mem_complex_iff f).1 hf).2
  ofCoeffs_add c c' := formOfCoeffs_add c c'
  ofCoeffs_smul z c := formOfCoeffs_smul z c
  finite_iff c := by
    refine (hF.finitelySupported_iff _).trans ?_
    have e : positivePart S pos ((positiveRepresentation S pos rev).ofCoeffs c) = ofPauliCoeffs c :=
      positivePart_formOfCoeffs c
    rw [e]
    exact hasFiniteSupp_ofPauliCoeffs_iff c
  pair_eq a b hb := by
    refine (hF.pair_eq _ _).trans ?_
    have e₁ : positivePart S pos ((positiveRepresentation S pos rev).ofCoeffs a) = ofPauliCoeffs a :=
      positivePart_formOfCoeffs a
    have e₂ : positivePart S pos ((positiveRepresentation S pos rev).ofCoeffs b) = ofPauliCoeffs b :=
      positivePart_formOfCoeffs b
    rw [e₁, e₂]
    exact traceFinsumPairing_ofPauliCoeffs hP a b hb
end Oriented
theorem conjugateBy_add (V A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (A + B) =
      ComplexMatrix2.conjugateBy V A + ComplexMatrix2.conjugateBy V B := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (V A : ComplexMatrix2) (z : ℂ) :
    ComplexMatrix2.conjugateBy V (z • A) = z • ComplexMatrix2.conjugateBy V A := by
  simp only [ComplexMatrix2.conjugateBy, mul_smul_comm, smul_mul_assoc]
theorem conjugateBy_zero (V : ComplexMatrix2) : ComplexMatrix2.conjugateBy V 0 = 0 := by
  simp only [ComplexMatrix2.conjugateBy, mul_zero, zero_mul]
theorem conjugateBy_mem_traceless (hA : ComplexMatrix2.ConjugationPreservesTraceless)
    {V X : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.unitDeterminant)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless :=
  (hA.2.2 V (hA.1 V hV)).2.2.2.1 hX
section CovariantDifference
variable {σ : Type} {S : PairedFunctionSpace} {pos : S.index → Prop} {rev : S.index → S.index}
def covDiffMap (S : PairedFunctionSpace) (pos : S.index → Prop) (rev : S.index → S.index)
    (head tail : S.index → σ) (W : S.index → ComplexMatrix2) (l : σ → ComplexMatrix2) :
    S.index → ComplexMatrix2 :=
  oddExtension S pos rev fun b => ComplexMatrix2.conjugateBy (W b) (l (head b)) - l (tail b)
theorem covDiffMap_add (head tail : S.index → σ) (W : S.index → ComplexMatrix2)
    (l l' : σ → ComplexMatrix2) :
    covDiffMap S pos rev head tail W (l + l') =
      covDiffMap S pos rev head tail W l + covDiffMap S pos rev head tail W l' := by
  unfold covDiffMap
  rw [← oddExtension_add]
  congr 1
  funext b
  simp only [Pi.add_apply, conjugateBy_add]
  abel
theorem covDiffMap_smul (head tail : S.index → σ) (W : S.index → ComplexMatrix2)
    (l : σ → ComplexMatrix2) (z : ℂ) :
    covDiffMap S pos rev head tail W (z • l) = z • covDiffMap S pos rev head tail W l := by
  unfold covDiffMap
  rw [← oddExtension_smul]
  congr 1
  funext b
  simp only [Pi.smul_apply, conjugateBy_smul, smul_sub]
theorem covDiffMap_isLocalMap (hA : ComplexMatrix2.ConjugationPreservesTraceless)
    (hP : OneLoop.PauliMatrixRelations) (hF : IsOrientedSpace S pos rev)
    (head tail : S.index → σ) (W : S.index → ComplexMatrix2)
    (hW : ∀ b, pos b → W b ∈ ComplexMatrix2.unitDeterminant)
    (hinc : ∀ x, {b : {b : S.index // pos b} | head b.1 = x ∨ tail b.1 = x}.Finite) :
    IsLocalMap (vertexCoordinate σ) (positiveRepresentation S pos rev)
      (covDiffMap S pos rev head tail W) := by
  refine isLocalMap_of_linear (vertexCoordinate_isFaithful hP σ) (positiveRepresentation_isFaithful hP hF)
    ?_ (fun l _ l' _ => covDiffMap_add head tail W l l')
    (fun l _ z => covDiffMap_smul head tail W l z)
    (fun p' => {p | p.2 = head p'.2.1 ∨ p.2 = tail p'.2.1}) ?_ ?_ ?_
  · intro l hl
    refine (hF.mem_complex_iff _).2 ⟨fun b hb => ?_, fun b => oddExtension_rev hF _ b⟩
    have e : covDiffMap S pos rev head tail W l b =
        ComplexMatrix2.conjugateBy (W b) (l (head b)) - l (tail b) := oddExtension_pos hb
    exact e ▸ ComplexMatrix2.traceless.sub_mem
      (conjugateBy_mem_traceless hA (hW b hb) (hl _ (mem_univ _))) (hl _ (mem_univ _))
  · intro p'
    refine (Set.Finite.prod (Set.finite_univ (α := Fin 3))
      (Set.toFinite ({head p'.2.1, tail p'.2.1} : Set σ))).subset ?_
    rintro ⟨a, x⟩ h
    exact ⟨mem_univ _, h⟩
  · rintro ⟨a, x⟩
    refine (Set.Finite.prod (Set.finite_univ (α := Fin 3)) (hinc x)).subset ?_
    rintro ⟨a', b⟩ h
    refine ⟨mem_univ _, ?_⟩
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro l hl ⟨a, b⟩ h
    have e₁ : l (head b.1) = 0 := eq_zero_of_pauliCoeffs (hl _ (mem_univ _)) fun a' =>
      h (a', head b.1) (Or.inl rfl)
    have e₂ : l (tail b.1) = 0 := eq_zero_of_pauliCoeffs (hl _ (mem_univ _)) fun a' =>
      h (a', tail b.1) (Or.inr rfl)
    have e : covDiffMap S pos rev head tail W l b.1 = 0 := by
      have e₃ : covDiffMap S pos rev head tail W l b.1 =
          ComplexMatrix2.conjugateBy (W b.1) (l (head b.1)) - l (tail b.1) :=
        oddExtension_pos b.2
      rw [e₃, e₁, e₂, conjugateBy_zero, sub_zero]
    exact (congrArg (pauliCoeff a) e).trans (pauliCoeff_zero a)
end CovariantDifference
section WeightedSums
variable {σ τ : Type}
def weightedConjSum (w : ℂ) (S : τ → Set σ) (g : τ → σ → ComplexMatrix2)
    (l : σ → ComplexMatrix2) (y : τ) : ComplexMatrix2 :=
  w • ∑ᶠ x ∈ S y, ComplexMatrix2.conjugateBy (g y x) (l x)
theorem weightedConjSum_eq_sum (w : ℂ) {S : τ → Set σ} (g : τ → σ → ComplexMatrix2)
    (hS : ∀ y, (S y).Finite) (l : σ → ComplexMatrix2) (y : τ) :
    weightedConjSum w S g l y =
      w • ∑ x ∈ (hS y).toFinset, ComplexMatrix2.conjugateBy (g y x) (l x) := by
  unfold weightedConjSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (hS y)]
theorem weightedConjSum_add (w : ℂ) {S : τ → Set σ} (g : τ → σ → ComplexMatrix2)
    (hS : ∀ y, (S y).Finite) (l l' : σ → ComplexMatrix2) :
    weightedConjSum w S g (l + l') = weightedConjSum w S g l + weightedConjSum w S g l' := by
  funext y
  simp only [Pi.add_apply, weightedConjSum_eq_sum w g hS, conjugateBy_add,
    Finset.sum_add_distrib, smul_add]
theorem weightedConjSum_smul (w : ℂ) {S : τ → Set σ} (g : τ → σ → ComplexMatrix2)
    (hS : ∀ y, (S y).Finite) (l : σ → ComplexMatrix2) (z : ℂ) :
    weightedConjSum w S g (z • l) = z • weightedConjSum w S g l := by
  funext y
  simp only [Pi.smul_apply, weightedConjSum_eq_sum w g hS, conjugateBy_smul]
  rw [← Finset.smul_sum, smul_comm]
theorem weightedConjSum_eq_zero (w : ℂ) {S : τ → Set σ} (g : τ → σ → ComplexMatrix2)
    (hS : ∀ y, (S y).Finite) (l : σ → ComplexMatrix2) (y : τ) (h : ∀ x ∈ S y, l x = 0) :
    weightedConjSum w S g l y = 0 := by
  rw [weightedConjSum_eq_sum w g hS, Finset.sum_eq_zero, smul_zero]
  intro x hx
  rw [h x ((hS y).mem_toFinset.1 hx), conjugateBy_zero]
theorem weightedConjSum_isLocalMap (hA : ComplexMatrix2.ConjugationPreservesTraceless)
    (hP : OneLoop.PauliMatrixRelations) (w : ℂ) (S : τ → Set σ) (g : τ → σ → ComplexMatrix2)
    (hS : ∀ y, (S y).Finite) (hinc : ∀ x, {y | x ∈ S y}.Finite)
    (hg : ∀ y, ∀ x ∈ S y, g y x ∈ ComplexMatrix2.unitDeterminant) :
    IsLocalMap (vertexCoordinate σ) (vertexCoordinate τ) (weightedConjSum w S g) := by
  refine isLocalMap_of_linear (vertexCoordinate_isFaithful hP σ) (vertexCoordinate_isFaithful hP τ) ?_
    (fun l _ l' _ => weightedConjSum_add w g hS l l')
    (fun l _ z => weightedConjSum_smul w g hS l z)
    (fun p' => {p | p.2 ∈ S p'.2}) ?_ ?_ ?_
  · intro l hl y _
    have e := weightedConjSum_eq_sum w g hS l y
    refine e ▸ ComplexMatrix2.traceless.smul_mem _ (Submodule.sum_mem _ fun x hx => ?_)
    exact conjugateBy_mem_traceless hA (hg y x ((hS y).mem_toFinset.1 hx)) (hl _ (mem_univ _))
  · intro p'
    refine (Set.Finite.prod (Set.finite_univ (α := Fin 3)) (hS p'.2)).subset ?_
    rintro ⟨a, x⟩ h
    exact ⟨mem_univ _, h⟩
  · rintro ⟨a, x⟩
    refine (Set.Finite.prod (Set.finite_univ (α := Fin 3)) (hinc x)).subset ?_
    rintro ⟨a', y⟩ h
    exact ⟨mem_univ _, h⟩
  · rintro l hl ⟨a, y⟩ h
    have e : weightedConjSum w S g l y = 0 := weightedConjSum_eq_zero w g hS l y fun x hx =>
      eq_zero_of_pauliCoeffs (hl _ (mem_univ _)) fun a' => h (a', x) hx
    exact (congrArg (pauliCoeff a) e).trans (pauliCoeff_zero a)
end WeightedSums
structure Hypotheses : Prop where
  kernels : RowFiniteKernels.Claim
  derivatives : AsDifferentials.CovariantMeansAreDerivatives
  conjugation : ComplexMatrix2.ConjugationPreservesTraceless
  pauli : OneLoop.PauliMatrixRelations
  blocks : BlockStructure
  meanInGroup : ComplexMeanLiesInComplexGaugeGroup
  polydiscs : DoubleBlockPolydisc.PolydiscsHold
  nearIdentity : SmoothingNearIdentity
  projections : SublatticesSymmetriesScalingsAndProjections.Statement
  endpoints : PeriodicLattice.BondEndpointsOrientation.Statement
  bondSets : BondSetFields.ProductStructureHolds
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹⁻¹ = X := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
section TorusSide
variable {L n k : ℕ}
theorem edge_isOrientedSpace (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) :
    IsOrientedSpace (edgePairedSpace L n k j) (fun b => b.IsPositivelyOriented)
      PeriodicLattice.Bond.opposite where
  xor_pos b := ((G.endpoints ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
  rev_rev _ := rfl
  mem_complex_iff _ := Iff.rfl
  finitelySupported_iff _ := Iff.rfl
  pair_eq _ _ := rfl
theorem edgePauliCoordinates_isFaithful (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) : IsFaithfulEvaluation (edgePauliCoordinates L n k j) :=
  positiveRepresentation_isFaithful G.pauli (edge_isOrientedSpace G hL hn hk hj)
theorem vertexCoordinate_faithful (G : Hypotheses) (σ : Type) : IsFaithfulEvaluation (vertexCoordinate σ) :=
  vertexCoordinate_isFaithful G.pauli σ
theorem extendOddly_opposite (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) (f : Edge L n k j → ComplexMatrix2)
    (b : Edge L n k j) : extendOddly f b.opposite = -extendOddly f b :=
  oddExtension_rev (edge_isOrientedSpace G hL hn hk hj) f b
theorem finite_edge (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) : Finite (Edge L n k j) :=
  Set.finite_univ_iff.1 ((G.bondSets L hL k j hj).1 n hn).2.1
theorem finite_vertex (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) : Finite (Vertex L n k j) :=
  have := finite_edge G hL hn hj
  Finite.of_injective (fun x : Vertex L n k j => PeriodicLattice.Bond.forwardFrom x 0)
    fun _ _ h => congrArg PeriodicLattice.Bond.source h
theorem covDiff_isLocalMap (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) {W : Edge L n k j → ComplexMatrix2}
    (hW : ∀ b : Edge L n k j, b.IsPositivelyOriented → W b ∈ ComplexMatrix2.unitDeterminant) :
    IsLocalMap (vertexCoordinate (Vertex L n k j)) (edgePauliCoordinates L n k j) (covDiff W) :=
  have := finite_edge G hL hn hj
  covDiffMap_isLocalMap (S := edgePairedSpace L n k j) (pos := fun b => b.IsPositivelyOriented)
    (rev := PeriodicLattice.Bond.opposite) G.conjugation G.pauli
    (edge_isOrientedSpace G hL hn hk hj) PeriodicLattice.Bond.target PeriodicLattice.Bond.source
    W hW fun _ =>
      (Set.finite_univ_iff.2 (inferInstance : Finite (PositiveEdge L n k j))).subset
        (Set.subset_univ _)
theorem complexSmoothingDeriv_opposite (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ}
    (hj : j < k) (V B : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)) :
    complexSmoothingDeriv V B c.opposite = -complexSmoothingDeriv V B c := by
  unfold complexSmoothingDeriv holLeftDifferential
  exact extendOddly_opposite G hL hn hk (show j + 1 ≤ k from hj) _ c
theorem mem_nearIdentityPolydisc {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L n k j) (c : Edge L n k (j + 1)) :
    V ∈ nearIdentityPolydisc (polydiscRadius L) c :=
  ⟨⟨fun b _ => hV.1.1 b (mem_univ b), fun b _ => hV.1.2 b (mem_univ b)⟩, fun b _ => hV.2 b⟩
theorem mem_complexGaugeGroup_at (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j < k) {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L n k j) {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) :
    (∀ y : Vertex L n k (j + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        PeriodicLattice.complexMeanContourHolonomy V y x ∈ PeriodicLattice.complexGaugeGroup) ∧
      PeriodicLattice.complexBlockAverage V c ∈ PeriodicLattice.complexGaugeGroup :=
  (G.meanInGroup.2 L k (j + 1) hL (by omega) hj).1 n hn c V hc
    (((G.nearIdentity.1 L hL).2.2.periodic n k j hn hj c hc).subset_complexDomain
      (mem_nearIdentityPolydisc hV c))
theorem step_isLocalMap (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j < k) {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L n k j) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L n k) :
    IsLocalMap (edgePauliCoordinates L n k j) (edgePauliCoordinates L n k (j + 1)) (covariantSmoothingDeriv V) ∧
      IsLocalMap (vertexCoordinate (Vertex L n k j)) (vertexCoordinate (Vertex L n k (j + 1)))
        (adjointCubeAverage V) := by
  have hs := ((G.derivatives L hL k hk).1 n hn).1 j hj V hV U hU
  have hr := edgePauliCoordinates_isFaithful G hL hn hk hj.le
  have hr' := edgePauliCoordinates_isFaithful G hL hn hk (show j + 1 ≤ k from hj)
  have := finite_edge G hL hn hj.le
  have := finite_edge G hL hn (show j + 1 ≤ k from hj)
  have := finite_vertex G hL hn hj.le
  have := finite_vertex G hL hn (show j + 1 ≤ k from hj)
  have : Finite (edgePauliCoordinates L n k j).Index :=
    (inferInstance : Finite (Fin 3 × PositiveEdge L n k j))
  have : Finite (edgePauliCoordinates L n k (j + 1)).Index :=
    (inferInstance : Finite (Fin 3 × PositiveEdge L n k (j + 1)))
  have : Finite (vertexCoordinate (Vertex L n k (j + 1))).Index :=
    (inferInstance : Finite (Fin 3 × Vertex L n k (j + 1)))
  have hQ : IsLocalMap (edgePauliCoordinates L n k j) (edgePauliCoordinates L n k (j + 1))
      (complexSmoothingDeriv V) :=
    isLocalMap_of_finite hr hr'
      (fun B hB => ⟨fun c hc => hs.mem_mean c hc B hB,
        fun c => complexSmoothingDeriv_opposite G hL hn hk hj V B c⟩)
      (fun B hB B' hB' => (hs.linear_mean B hB B' hB' 0).1)
      (fun B hB z => (hs.linear_mean B hB B hB z).2)
  have hN : IsLocalMap (edgePauliCoordinates L n k j) (vertexCoordinate (Vertex L n k (j + 1)))
      (contourLogDrift V) :=
    isLocalMap_of_finite hr (vertexCoordinate_faithful G _)
      (fun B hB y _ => hs.mem_contour y B hB)
      (fun B hB B' hB' => (hs.linear_contour B hB B' hB' 0).1)
      (fun B hB z => (hs.linear_contour B hB B hB z).2)
  have hW := covDiff_isLocalMap G hL hn hk (show j + 1 ≤ k from hj)
    (W := PeriodicLattice.complexBlockAverageStep j V)
    fun c hc => by
      have e := (mem_complexGaugeGroup_at G hL hn hj hV hc).2
      exact e
  refine ⟨hQ.add hr hr' (hN.comp hr (vertexCoordinate_faithful G _) hW), ?_⟩
  refine weightedConjSum_isLocalMap G.conjugation G.pauli
    (PeriodicLattice.inverseFourthPowerWeight L)
    (fun y : Vertex L n k (j + 1) => PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    (PeriodicLattice.complexMeanContourHolonomy V) (fun _ => Set.toFinite _)
    (fun _ => Set.toFinite _) ?_
  intro y x hx
  have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, add_sub_cancel_left _ _⟩
  exact (mem_complexGaugeGroup_at G hL hn hj hV hc).1 y (Or.inl rfl) x hx
theorem iterate_isLocalMap (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L n k) (j : ℕ) (hj : j ≤ k) :
    IsLocalMap (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k j) (iterCovariantDeriv L n k U j) ∧
      IsLocalMap (vertexCoordinate (Vertex L n k 0)) (vertexCoordinate (Vertex L n k j))
        (iterAdjointCubeAverage L n k U j) := by
  induction j with
  | zero =>
    have e₁ : iterCovariantDeriv L n k U 0 = fun B => B := funext fun _ => rfl
    have e₂ : iterAdjointCubeAverage L n k U 0 = fun l => l := funext fun _ => rfl
    rw [e₁, e₂]
    exact ⟨IsLocalMap.id (edgePauliCoordinates_isFaithful G hL hn hk (Nat.zero_le k)),
      IsLocalMap.id (vertexCoordinate_faithful G _)⟩
  | succ j ih =>
    have hj' : j < k := hj
    obtain ⟨h₁, h₂⟩ := ih hj'.le
    obtain ⟨h₃, h₄⟩ := step_isLocalMap G hL hn hk hj' (hU.2 j hj') hU
    exact ⟨h₁.comp (edgePauliCoordinates_isFaithful G hL hn hk (Nat.zero_le k))
        (edgePauliCoordinates_isFaithful G hL hn hk hj'.le) h₃,
      h₂.comp (vertexCoordinate_faithful G _) (vertexCoordinate_faithful G _) h₄⟩
theorem onTorus_holds (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) : OnTorus L n k := by
  have hT := G.kernels.2.2.2
  refine ⟨fun i j _ _ => ⟨kernelUnique _ _, kernelUnique _ _, kernelUnique _ _,
    kernelUnique _ _⟩, fun W hW => ?_, fun W hW => ?_, fun U hU => ?_⟩
  · exact (covDiff_isLocalMap G hL hn hk (Nat.zero_le k)
      fun b _ => hW.1 b (mem_univ b)).hasLocalKernel hT (vertexCoordinate_faithful G _)
        (edgePauliCoordinates_isFaithful G hL hn hk (Nat.zero_le k))
  · exact (covDiff_isLocalMap G hL hn hk le_rfl
      fun b _ => hW.1 b (mem_univ b)).hasLocalKernel hT (vertexCoordinate_faithful G _)
        (edgePauliCoordinates_isFaithful G hL hn hk le_rfl)
  · obtain ⟨h₁, h₂⟩ := iterate_isLocalMap G hL hn hk hU k le_rfl
    exact ⟨h₁.hasLocalKernel hT (edgePauliCoordinates_isFaithful G hL hn hk (Nat.zero_le k))
        (edgePauliCoordinates_isFaithful G hL hn hk le_rfl),
      h₂.hasLocalKernel hT (vertexCoordinate_faithful G _) (vertexCoordinate_faithful G _)⟩
end TorusSide
section FullSpaceSide
variable {L k : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem fullSpace_isOrientedSpace {a : ℝ} (ha : 0 < a) :
    IsOrientedSpace (FullSpace.edgePairedSpace a) (fun b => b.IsPositivelyOriented)
      InfiniteLattice.Link.opposite where
  xor_pos b := by
    rcases InfiniteLattice.xor_mem_positiveLinks ha b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
    · exact Or.inr ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
  rev_rev _ := rfl
  mem_complex_iff _ := Iff.rfl
  finitelySupported_iff _ := Iff.rfl
  pair_eq _ _ := rfl
theorem fullSpace_edgeBasis_isFaithful (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℕ) :
    IsFaithfulEvaluation (FullSpace.edgePauliCoordinates L k j) :=
  positiveRepresentation_isFaithful G.pauli (fullSpace_isOrientedSpace (meshAt_pos hL k j))
theorem fullSpace_extendOddly_opposite {a : ℝ} (ha : 0 < a)
    (f : InfiniteLattice.Link a → ComplexMatrix2) (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem finite_links_at {a : ℝ} (y : InfiniteLattice.LatticePoint a) :
    {c : InfiniteLattice.Link a | c.initial = y ∨ c.terminal = y}.Finite := by apply _root_.YangMills.Construction.Tower.MeanStableFields.Infinite.finite_links_with_endpoint <;> assumption
theorem fullSpace_complexSmoothingDeriv_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    {j : ℕ} (V B : FullSpace.Edge L k j → ComplexMatrix2) (c : FullSpace.Edge L k (j + 1)) :
    FullSpace.complexSmoothingDeriv V B c.opposite = -FullSpace.complexSmoothingDeriv V B c := by
  unfold FullSpace.complexSmoothingDeriv FullSpace.holLeftDifferential
  exact fullSpace_extendOddly_opposite (meshAt_pos hL k (j + 1)) _ c
theorem fullSpace_covDiff_isLocalMap (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℕ)
    {W : FullSpace.Edge L k j → ComplexMatrix2}
    (hW : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
      W b ∈ ComplexMatrix2.unitDeterminant) :
    IsLocalMap (vertexCoordinate (FullSpace.Vertex L k j)) (FullSpace.edgePauliCoordinates L k j)
      (FullSpace.covDiff W) :=
  covDiffMap_isLocalMap (S := FullSpace.edgePairedSpace (meshAt L k j))
    (pos := fun b => b.IsPositivelyOriented) (rev := InfiniteLattice.Link.opposite)
    G.conjugation G.pauli (fullSpace_isOrientedSpace (meshAt_pos hL k j))
    InfiniteLattice.Link.terminal InfiniteLattice.Link.initial W hW fun x => by
      refine ((finite_links_at x).preimage Subtype.val_injective.injOn).subset ?_
      rintro b (h | h)
      · exact Or.inr h
      · exact Or.inl h
theorem finite_doubleCube_incidence (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k)
    (b : FullSpace.Edge L k i) :
    {c : FullSpace.Edge L k (i + 1) | c.IsPositivelyOriented ∧
      b ∈ FullSpace.doubleCubeLinks L (meshAt L k i) c}.Finite := by
  obtain ⟨y, _, huniq⟩ :=
    (G.blocks L k (i + 1) hL (by omega) (by omega) (by omega)).2.2.1.2.1 b.initial
  refine (finite_links_at y).subset ?_
  rintro c ⟨hcp, hb⟩
  have hb' : b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c := hb
  rw [((G.polydiscs L hL k i hi).2 c hcp).doubleBlockBonds_eq] at hb'
  rcases hb'.1 with h | h
  · exact Or.inl (huniq _ h)
  · exact Or.inr (huniq _ h)
theorem fullSpace_mem_nearIdentityPolydisc {j : ℕ} {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ FullSpace.smallComplexFields L k j) (c : FullSpace.Edge L k (j + 1)) :
    V ∈ FullSpace.nearIdentityPolydisc L k j (polydiscRadius L) c :=
  ⟨⟨fun b _ => hV.1.1 b, fun b _ => hV.1.2 b⟩, fun b _ => hV.2 b⟩
theorem mem_nearIdentityPolydisc_congr {j : ℕ} {c : FullSpace.Edge L k (j + 1)}
    (hrev : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c,
      b.opposite ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c)
    {ρ : ℝ} {V V' : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ FullSpace.nearIdentityPolydisc L k j ρ c)
    (he : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    V' ∈ FullSpace.nearIdentityPolydisc L k j ρ c := by
  refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
  · rw [← he b hb]
    exact hV.1.1 b hb
  · rw [← he b hb, ← he _ (hrev b hb)]
    exact hV.1.2 b hb
  · rw [← he b hb]
    exact hV.2 b hb
theorem complexSmoothing_congr (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) {i : ℕ} (hi : i < k) {c : FullSpace.Edge L k (i + 1)}
    (hc : c.IsPositivelyOriented) {V V' : FullSpace.Edge L k i → ComplexMatrix2}
    (hV : V ∈ FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c)
    (hV' : V' ∈ FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c)
    (he : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k i) c, V b = V' b) :
    FullSpace.complexSmoothing L V c = FullSpace.complexSmoothing L V' c := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hserve := (G.nearIdentity.1 L hL).2.2.fullSpace k i hi c hc
  have hQ' := ((G.projections L hL0 hL k).2.2.2.2.2.2 hk 1 one_pos).2 i hi c hc
  have e1 := hQ'.complexSmoothing_eq V (hserve.subset_complexDomain hV)
  have e2 := hQ'.complexSmoothing_eq V' (hserve.subset_complexDomain hV')
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext x
  unfold FullSpace.projField
  split_ifs with h
  · exact he _ h.choose_spec.1
  · rfl
theorem complexContourMean_congr (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {y : FullSpace.Vertex L k (j + 1)} (hy : y = c.initial ∨ y = c.terminal)
    {x : FullSpace.Vertex L k j} (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y)
    {V V' : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ FullSpace.nearIdentityPolydisc L k j (polydiscRadius L) c)
    (hV' : V' ∈ FullSpace.nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    FullSpace.complexContourMean L V y x = FullSpace.complexContourMean L V' y x := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hserve := (G.nearIdentity.1 L hL).2.2.fullSpace k j hj c hc
  have hQ' := ((G.projections L hL0 hL k).2.2.2.2.2.2 hk 1 one_pos).2 j hj c hc
  have e1 := hQ'.complexContourMean_eq V (hserve.subset_complexDomain hV) y hy x hx
  have e2 := hQ'.complexContourMean_eq V' (hserve.subset_complexDomain hV') y hy x hx
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext z
  unfold FullSpace.projField
  split_ifs with h
  · exact he _ h.choose_spec.1
  · rfl
theorem expTwist_eqOn {a : ℝ} (ha : 0 < a) {P : Set (InfiniteLattice.Link a)}
    (hrev : ∀ b ∈ P, b.opposite ∈ P) {V B : InfiniteLattice.Link a → ComplexMatrix2}
    (hV : FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup V)
    (hB : ∀ b ∈ P, b.IsPositivelyOriented → B b = 0) (t : ℂ) :
    ∀ b ∈ P, V b = FullSpace.expTwist (t • B) V b := by
  intro b hb
  unfold FullSpace.expTwist
  by_cases hp : b.IsPositivelyOriented
  · rw [if_pos hp]
    simp [hB b hb hp, NormedSpace.exp_zero]
  · have hrp : b.opposite.IsPositivelyOriented := by
      rcases (fullSpace_isOrientedSpace ha).xor_pos b with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hp
      · exact h
    rw [if_neg hp]
    simp only [Pi.smul_apply, hB _ (hrev b hb) hrp, smul_zero, NormedSpace.exp_zero, one_mul]
    rw [hV.2 b, inv_inv_of_mem_unitDeterminant (hV.1 b)]
structure StepHyp (L k j : ℕ) (V : FullSpace.Edge L k j → ComplexMatrix2)
    (U : FullSpace.Edge L k 0 → ComplexMatrix2) : Prop where
  lt : j < k
  mem : V ∈ FullSpace.smallComplexFields L k j
  clauses : FullSpace.AsDifferentials.StepConditions j V U
theorem complexSmoothingDeriv_eq_zero (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ}
    {V : FullSpace.Edge L k j → ComplexMatrix2} {U : FullSpace.Edge L k 0 → ComplexMatrix2}
    (D : StepHyp L k j V U) {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j))
    (hz : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c, b.IsPositivelyOriented → B b = 0) :
    FullSpace.complexSmoothingDeriv V B c = 0 := by
  have hrev := ((G.polydiscs L hL k j D.lt).2 c hc).finite_open.opposite_mem
  have hd := D.clauses.deriv_mean c hc B hB
  have hP := fullSpace_mem_nearIdentityPolydisc D.mem c
  have ht : ∀ t : ℂ, FullSpace.complexSmoothing L (FullSpace.expTwist (t • B) V) c =
      FullSpace.complexSmoothing L V c := fun t => by
    have e := expTwist_eqOn (meshAt_pos hL k j) hrev D.mem.1 hz t
    exact (complexSmoothing_congr G hL hk D.lt hc hP
      (mem_nearIdentityPolydisc_congr hrev hP e) e).symm
  have hconst : (fun t : ℂ => FullSpace.AsDifferentials.meanLogRatio V c (t • B)) =
      fun _ => Complex.I⁻¹ • ComplexMatrix2.logSeries (FullSpace.complexSmoothing L V c *
        (FullSpace.complexSmoothing L V c)⁻¹) := by
    funext t
    unfold FullSpace.AsDifferentials.meanLogRatio FullSpace.AsDifferentials.meanRatio
    rw [ht t]
  unfold AsDifferentials.HasDerivAtZeroAlong at hd
  rw [hconst] at hd
  exact hd.unique (hasDerivAt_const _ _)
theorem contourLogDrift_eq_zero (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ}
    {V : FullSpace.Edge L k j → ComplexMatrix2} {U : FullSpace.Edge L k 0 → ComplexMatrix2}
    (D : StepHyp L k j V U) {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j))
    (hz : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c, b.IsPositivelyOriented → B b = 0) :
    FullSpace.contourLogDrift V B c.initial = 0 := by
  have hrev := ((G.polydiscs L hL k j D.lt).2 c hc).finite_open.opposite_mem
  have hP := fullSpace_mem_nearIdentityPolydisc D.mem c
  unfold FullSpace.contourLogDrift
  suffices h : ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial,
      logDirectionalDeriv ℂ
        (fun X => FullSpace.complexContourMean L (FullSpace.expTwist X V) c.initial x)
        (FullSpace.complexContourMean L V c.initial x) B = 0 by
    refine (congrArg _ (finsum_eq_zero_of_forall_eq_zero fun x => ?_)).trans (smul_zero _)
    classical
    rw [finsum_eq_if]
    split_ifs with hx
    · exact h x hx
    · rfl
  intro x hx
  have hd := D.clauses.deriv_contour c.initial x hx B hB
  have ht : ∀ t : ℂ, FullSpace.complexContourMean L (FullSpace.expTwist (t • B) V) c.initial x =
      FullSpace.complexContourMean L V c.initial x := fun t => by
    have e := expTwist_eqOn (meshAt_pos hL k j) hrev D.mem.1 hz t
    exact (complexContourMean_congr G hL hk D.lt hc (Or.inl rfl) hx hP
      (mem_nearIdentityPolydisc_congr hrev hP e) e).symm
  have hconst : (fun t : ℂ =>
      FullSpace.AsDifferentials.contourLogRatio V c.initial x (t • B)) =
      fun _ => Complex.I⁻¹ • ComplexMatrix2.logSeries
        (FullSpace.complexContourMean L V c.initial x *
          (FullSpace.complexContourMean L V c.initial x)⁻¹) := by
    funext t
    unfold FullSpace.AsDifferentials.contourLogRatio FullSpace.AsDifferentials.contourRatio
    rw [ht t]
  unfold AsDifferentials.HasDerivAtZeroAlong at hd
  rw [hconst] at hd
  exact hd.unique (hasDerivAt_const _ _)
def firstLink {a : ℝ} (y : InfiniteLattice.LatticePoint a) : InfiniteLattice.Link a :=
  InfiniteLattice.Link.forwardFrom y 0
theorem firstLink_isPositivelyOriented {a : ℝ} (y : InfiniteLattice.LatticePoint a) :
    (firstLink y).IsPositivelyOriented :=
  ⟨0, add_sub_cancel_left _ _⟩
theorem fullSpace_mem_complexGaugeGroup_at (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2} (hV : V ∈ FullSpace.smallComplexFields L k j)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    (∀ y : FullSpace.Vertex L k (j + 1), (y = c.initial ∨ y = c.terminal) →
      ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) y,
        FullSpace.complexContourMean L V y x ∈ PeriodicLattice.complexGaugeGroup) ∧
      FullSpace.complexSmoothing L V c ∈ PeriodicLattice.complexGaugeGroup :=
  (G.meanInGroup.2 L k (j + 1) hL (by omega) hj).2 c V hc
    (((G.nearIdentity.1 L hL).2.2.fullSpace k j hj c hc).subset_complexDomain
      (fullSpace_mem_nearIdentityPolydisc hV c))
theorem finite_pairs {I J : Type} {P : I → Set J} (h : ∀ i, (P i).Finite) (i : I) :
    {p : Fin 3 × J | p.2 ∈ P i}.Finite :=
  (Set.Finite.prod (Set.finite_univ (α := Fin 3)) (h i)).subset fun _ hp => ⟨mem_univ _, hp⟩
theorem fullSpace_step_isLocalMap (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) {j : ℕ} (hj : j < k) {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ FullSpace.smallComplexFields L k j)
    {U : FullSpace.Edge L k 0 → ComplexMatrix2} (hU : U ∈ FullSpace.smallIterateFields L k) :
    IsLocalMap (FullSpace.edgePauliCoordinates L k j) (FullSpace.edgePauliCoordinates L k (j + 1))
        (FullSpace.covariantSmoothingDeriv V) ∧
      IsLocalMap (vertexCoordinate (FullSpace.Vertex L k j))
        (vertexCoordinate (FullSpace.Vertex L k (j + 1))) (FullSpace.adjointCubeAverage V) := by
  have hs := (G.derivatives L hL k hk).2.1 j hj V hV U hU
  have D : StepHyp L k j V U := ⟨hj, hV, hs⟩
  have hr := fullSpace_edgeBasis_isFaithful (k := k) G hL j
  have hr' := fullSpace_edgeBasis_isFaithful (k := k) G hL (j + 1)
  have hsite := vertexCoordinate_faithful G (FullSpace.Vertex L k (j + 1))
  have hfin : ∀ c : FullSpace.PositiveEdge (meshAt L k (j + 1)),
      {b : FullSpace.PositiveEdge (meshAt L k j) |
        b.1 ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c.1}.Finite := fun c =>
    ((G.polydiscs L hL k j hj).2 c.1 c.2).finite_open.finite.preimage
      Subtype.val_injective.injOn
  have hQ : IsLocalMap (FullSpace.edgePauliCoordinates L k j) (FullSpace.edgePauliCoordinates L k (j + 1))
      (FullSpace.complexSmoothingDeriv V) := by
    refine isLocalMap_of_linear hr hr'
      (fun B hB => ⟨fun c hc => hs.mem_mean c hc B hB,
        fun c => fullSpace_complexSmoothingDeriv_opposite hL V B c⟩)
      (fun B hB B' hB' => (hs.linear_mean B hB B' hB' 0).1)
      (fun B hB z => (hs.linear_mean B hB B hB z).2)
      (fun p' => {p | p.2.1 ∈ FullSpace.doubleCubeLinks L (meshAt L k j) p'.2.1})
      (fun p' => finite_pairs hfin p'.2) ?_ ?_
    · rintro ⟨a, b⟩
      refine (Set.Finite.prod (Set.finite_univ (α := Fin 3))
        ((finite_doubleCube_incidence G hL hj b.1).preimage
          Subtype.val_injective.injOn)).subset ?_
      rintro ⟨a', c⟩ h
      exact ⟨mem_univ _, c.2, h⟩
    · rintro B hB ⟨a, c⟩ h
      show pauliCoeff a (FullSpace.complexSmoothingDeriv V B c.1) = 0
      rw [complexSmoothingDeriv_eq_zero G hL hk D c.2 hB, pauliCoeff_zero]
      intro b hb hp
      exact eq_zero_of_pauliCoeffs (f := FullSpace.restrictToPositiveEdges B) (x := ⟨b, hp⟩)
        (hB.1 b hp) fun a' => h (a', ⟨b, hp⟩) hb
  have hN : IsLocalMap (FullSpace.edgePauliCoordinates L k j)
      (vertexCoordinate (FullSpace.Vertex L k (j + 1))) (FullSpace.contourLogDrift V) := by
    refine isLocalMap_of_linear hr hsite
      (fun B hB y _ => hs.mem_contour y B hB)
      (fun B hB B' hB' => (hs.linear_contour B hB B' hB' 0).1)
      (fun B hB z => (hs.linear_contour B hB B hB z).2)
      (fun p' => {p | p.2.1 ∈ FullSpace.doubleCubeLinks L (meshAt L k j) (firstLink p'.2)})
      (fun p' => finite_pairs (fun y : FullSpace.Vertex L k (j + 1) =>
        hfin ⟨firstLink y, firstLink_isPositivelyOriented y⟩) p'.2) ?_ ?_
    · rintro ⟨a, b⟩
      have hinj : Function.Injective
          (firstLink : FullSpace.Vertex L k (j + 1) → FullSpace.Edge L k (j + 1)) :=
        fun y y' h => congrArg InfiniteLattice.Link.initial h
      refine (Set.Finite.prod (Set.finite_univ (α := Fin 3))
        ((finite_doubleCube_incidence G hL hj b.1).preimage hinj.injOn)).subset ?_
      rintro ⟨a', y⟩ h
      exact ⟨mem_univ _, firstLink_isPositivelyOriented y, h⟩
    · rintro B hB ⟨a, y⟩ h
      show pauliCoeff a (FullSpace.contourLogDrift V B y) = 0
      have e := contourLogDrift_eq_zero G hL hk D (firstLink_isPositivelyOriented y) hB
        fun b hb hp =>
          eq_zero_of_pauliCoeffs (f := FullSpace.restrictToPositiveEdges B) (x := ⟨b, hp⟩)
            (hB.1 b hp) fun a' => h (a', ⟨b, hp⟩) hb
      have e' : FullSpace.contourLogDrift V B y = 0 := e
      rw [e', pauliCoeff_zero]
  have hW := fullSpace_covDiff_isLocalMap (k := k) G hL (j + 1)
    (W := FullSpace.smoothingMap L k j V) fun c hc =>
      (fullSpace_mem_complexGaugeGroup_at G hL hj hV hc).2
  refine ⟨hQ.add hr hr' (hN.comp hr hsite hW), ?_⟩
  have hblocks := G.blocks L k (j + 1) hL (by omega) (by omega) (by omega)
  refine weightedConjSum_isLocalMap G.conjugation G.pauli
    (PeriodicLattice.inverseFourthPowerWeight L)
    (fun y : FullSpace.Vertex L k (j + 1) => FullSpace.cubeVertices L (meshAt L k j) y)
    (FullSpace.complexContourMean L V) ?_ ?_ ?_
  · intro y
    have hcard := (hblocks.2.1 y).2.2.1
    have hpos : 0 < L ^ 4 := by
      have := hL.2
      positivity
    have hf : (FullSpace.cube L (meshAt L k j) y).Finite :=
      Set.finite_of_ncard_pos (hcard.symm ▸ hpos)
    exact hf.preimage Subtype.val_injective.injOn
  · intro x
    obtain ⟨y, _, huniq⟩ := hblocks.2.2.1.2.1 x
    exact (Set.finite_singleton y).subset fun y' h => huniq y' h
  · intro y x hx
    exact (fullSpace_mem_complexGaugeGroup_at G hL hj hV (firstLink_isPositivelyOriented y)).1
      y (Or.inl rfl) x hx
theorem fullSpace_iterate_isLocalMap (G : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : FullSpace.Edge L k 0 → ComplexMatrix2} (hU : U ∈ FullSpace.smallIterateFields L k)
    (j : ℕ) (hj : j ≤ k) :
    IsLocalMap (FullSpace.edgePauliCoordinates L k 0) (FullSpace.edgePauliCoordinates L k j)
        (FullSpace.iterCovariantDeriv L k U j) ∧
      IsLocalMap (vertexCoordinate (FullSpace.Vertex L k 0)) (vertexCoordinate (FullSpace.Vertex L k j))
        (FullSpace.iterAdjointCubeAverage L k U j) := by
  induction j with
  | zero =>
    have e₁ : FullSpace.iterCovariantDeriv L k U 0 = fun B => B := funext fun _ => rfl
    have e₂ : FullSpace.iterAdjointCubeAverage L k U 0 = fun l => l := funext fun _ => rfl
    rw [e₁, e₂]
    exact ⟨IsLocalMap.id (fullSpace_edgeBasis_isFaithful G hL 0),
      IsLocalMap.id (vertexCoordinate_faithful G _)⟩
  | succ j ih =>
    have hj' : j < k := hj
    obtain ⟨h₁, h₂⟩ := ih hj'.le
    obtain ⟨h₃, h₄⟩ := fullSpace_step_isLocalMap G hL hk hj' (hU.2 j hj') hU
    exact ⟨h₁.comp (fullSpace_edgeBasis_isFaithful G hL 0)
        (fullSpace_edgeBasis_isFaithful G hL j) h₃,
      h₂.comp (vertexCoordinate_faithful G _) (vertexCoordinate_faithful G _) h₄⟩
theorem onFullSpace_holds (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) : OnFullSpace L k := by
  have hT := G.kernels.2.2.2
  refine ⟨fun i j _ _ => ⟨kernelUnique _ _, kernelUnique _ _, kernelUnique _ _,
    kernelUnique _ _⟩, fun W hW => ?_, fun W hW => ?_, fun U hU => ?_⟩
  · exact (fullSpace_covDiff_isLocalMap G hL 0 fun b _ => hW.1 b).hasLocalKernel hT
      (vertexCoordinate_faithful G _) (fullSpace_edgeBasis_isFaithful G hL 0)
  · exact (fullSpace_covDiff_isLocalMap G hL k fun b _ => hW.1 b).hasLocalKernel hT
      (vertexCoordinate_faithful G _) (fullSpace_edgeBasis_isFaithful G hL k)
  · obtain ⟨h₁, h₂⟩ := fullSpace_iterate_isLocalMap G hL hk hU k le_rfl
    exact ⟨h₁.hasLocalKernel hT (fullSpace_edgeBasis_isFaithful G hL 0)
        (fullSpace_edgeBasis_isFaithful G hL k),
      h₂.hasLocalKernel hT (vertexCoordinate_faithful G _) (vertexCoordinate_faithful G _)⟩
end FullSpaceSide
theorem claim_holds (h₁ : RowFiniteKernels.Claim)
    (h₂ : AsDifferentials.CovariantMeansAreDerivatives)
    (h₃ : ComplexMatrix2.ConjugationPreservesTraceless)
    (h₄ : OneLoop.PauliMatrixRelations) (h₅ : BlockStructure)
    (h₆ : ComplexMeanLiesInComplexGaugeGroup) (h₇ : DoubleBlockPolydisc.PolydiscsHold)
    (h₈ : SmoothingNearIdentity)
    (h₉ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (h₁₀ : PeriodicLattice.BondEndpointsOrientation.Statement)
    (h₁₁ : BondSetFields.ProductStructureHolds) : Claim := by
  have G : Hypotheses := ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩
  intro L hL k hk
  exact ⟨fun n hn => onTorus_holds G hL hn hk, onFullSpace_holds G hL hk⟩
end YangMills.Construction.Tower.ThreeMapKernels
end
