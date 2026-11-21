import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.PlaquettesOfABond
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernel
import YangMills.Construction.Towers.TransposesOfTheCovariantDifferenceAndOfTheDifferences
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.Tower.CovDiffTransposes
open PeriodicOperators Matrices
section Kernels
variable {N N' N'' : Type}
theorem applySummable_of_rowFinite {T : KernelMatrix N N'} (hT : RowFinite T) (f : N → ℂ) :
    ApplySummable T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applySummable_of_rowFinite <;> assumption
theorem applyKernel_add {T : KernelMatrix N N'} (hT : RowFinite T) (f g : N → ℂ) :
    applyKernel T (f + g) = applyKernel T f + applyKernel T g := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_add <;> assumption
theorem applyKernel_smul (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel T (z • f) = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_smul <;> assumption
structure IsFinitelyDetermined (M : (N → ℂ) → N' → ℂ) (R : N' → Set N) : Prop where
  map_add : ∀ f g, M (f + g) = M f + M g
  map_smul : ∀ (z : ℂ) f, M (z • f) = z • M f
  support_finite : ∀ i', (R i').Finite
  dependents_finite : ∀ i, {i' | i ∈ R i'}.Finite
  eq_zero_of_vanish : ∀ f i', (∀ i ∈ R i', f i = 0) → M f i' = 0
def kernelOfBasis (M : (N → ℂ) → N' → ℂ) : KernelMatrix N N' :=
  open Classical in fun i' i => M (Pi.single i 1) i'
namespace IsFinitelyDetermined
variable {M : (N → ℂ) → N' → ℂ} {R : N' → Set N}
theorem kernelOfBasis_eq_zero (h : IsFinitelyDetermined M R) {i : N} {i' : N'} (hi : i ∉ R i') :
    kernelOfBasis M i' i = 0 := by
  classical
  refine h.eq_zero_of_vanish _ _ fun j hj => ?_
  rw [Pi.single_eq_of_ne]
  rintro rfl
  exact hi hj
theorem rowFinite (h : IsFinitelyDetermined M R) : RowFinite (kernelOfBasis M) := fun i' =>
  (h.support_finite i').subset fun i hi => by
    by_contra h'
    exact hi (h.kernelOfBasis_eq_zero h')
theorem columnFinite (h : IsFinitelyDetermined M R) : ColumnFinite (kernelOfBasis M) := fun i =>
  (h.dependents_finite i).subset fun i' hi' => by
    by_contra h'
    exact hi' (h.kernelOfBasis_eq_zero h')
theorem represents (h : IsFinitelyDetermined M R) : Represents (kernelOfBasis M) M := by
  classical
  intro f
  refine ⟨applySummable_of_rowFinite h.rowFinite f, ?_⟩
  funext i'
  let Ml : (N → ℂ) →ₗ[ℂ] (N' → ℂ) := ⟨⟨M, h.map_add⟩, h.map_smul⟩
  let F : Finset N := (h.support_finite i').toFinset
  let g : N → ℂ := ∑ i ∈ F, f i • Pi.single i (1 : ℂ)
  have hg : ∀ i ∈ R i', (f - g) i = 0 := by
    intro i hi
    have hF : i ∈ F := (h.support_finite i').mem_toFinset.2 hi
    have : g i = f i := by
      simp only [g, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · exact fun h' => absurd hF h'
    simp [this]
  have e1 : Ml (f - g) i' = 0 := h.eq_zero_of_vanish _ _ hg
  have e2 : M f i' = Ml g i' := by
    have : Ml f i' - Ml g i' = 0 := by
      rw [map_sub] at e1
      simpa using e1
    exact sub_eq_zero.1 this
  have e3 : Ml g i' = ∑ i ∈ F, kernelOfBasis M i' i * f i := by
    simp only [g, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show M (f i • Pi.single i 1) i' = kernelOfBasis M i' i * f i
    rw [h.map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    rfl
  rw [e2, e3]
  unfold applyKernel
  refine tsum_eq_sum fun i hi => ?_
  rw [h.kernelOfBasis_eq_zero fun h' => hi ((h.support_finite i').mem_toFinset.2 h'), zero_mul]
end IsFinitelyDetermined
end Kernels
section Coefficients
theorem pauliCombination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
end Coefficients
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
end IsFaithfulEvaluation
structure IsLocalMap (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2) : Prop where
  maps_into : ∀ f ∈ r.space.complexSubmodule, m f ∈ r'.space.complexSubmodule
  determined : ∃ R, IsFinitelyDetermined (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m) R
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
    rw [hr.ofCoeffs_smul, hsmul _ (hr.ofCoeffs_mem c), hr'.coeffs_smul z (maps _ (hr.ofCoeffs_mem c))]
  · intro c i' h
    refine reads _ (hr.ofCoeffs_mem c) i' fun i hi => ?_
    rw [hr.coeffs_ofCoeffs]
    exact h i hi
theorem matrixKernel_eq (r r' : PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2) :
    matrixKernel r r' m = kernelOfBasis (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m) := by
  classical
  funext i' i
  have e : (fun κ => if κ = i then (1 : ℂ) else 0) = Pi.single i 1 := by
    funext κ
    by_cases h : κ = i
    · subst h
      simp
    · simp [h]
  unfold matrixKernel kernelOfBasis PauliComponentsOfSymmetricKernel.mapOnCoeffs
  simp only [e]
  congr!
theorem IsLocalMap.hasTransposeKernel (hT : RowFiniteKernels.TransposeDuality)
    (hr : IsFaithfulEvaluation r) (hr' : IsFaithfulEvaluation r')
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (h : IsLocalMap r r' m) : HasTransposeKernel r r' m := by
  classical
  obtain ⟨hmaps, R, hR⟩ := h
  have hKE := matrixKernel_eq r r' m
  have hK : Represents (kernelOfBasis (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m))
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m) := hR.represents
  have hrows : RowFinite (kernelOfBasis (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m)) := hR.rowFinite
  have hcols : ColumnFinite (kernelOfBasis (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m)) :=
    hR.columnFinite
  set K := kernelOfBasis (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m) with hKdef
  set M := PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m with hMdef
  have hrowsT : RowFinite (swapKernel K) := hcols
  have hm_eq : ∀ f ∈ r.space.complexSubmodule, m f = r'.ofCoeffs (M (r.coeffs f)) := by
    intro f hf
    show m f = r'.ofCoeffs (r'.coeffs (m (r.ofCoeffs (r.coeffs f))))
    rw [hr.ofCoeffs_coeffs f hf, hr'.ofCoeffs_coeffs _ (hmaps f hf)]
  have hsupp : ∀ c : r.Index → ℂ, (Function.support c).Finite →
      (Function.support (M c)).Finite := by
    intro c hc
    refine (hc.biUnion fun i _ => hR.dependents_finite i).subset fun i' hi' => ?_
    by_contra hn
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop, not_exists, not_and] at hn
    refine hi' (hR.eq_zero_of_vanish c i' fun i hi => ?_)
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
      rw [hm_eq _ (r.space.complexSubmodule.smul_mem z f.2), hr.coeffs_smul z f.2, hR.map_smul,
        hr'.ofCoeffs_smul, ← hm_eq _ f.2]
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
    have eT : PeriodicOperators.wTranspose (fun _ : r'.Index => (1 : ℝ))
        (fun _ : r.Index => (1 : ℝ)) (swapKernel K) = K := by
      funext i' i
      simp [PeriodicOperators.wTranspose, swapKernel]
    rw [eT, (hK _).2] at key
    simp only [Complex.ofReal_one, one_mul] at key
    calc _ = ∑ᶠ i, r.coeffs f.1 i * applyKernel (swapKernel K) (r'.coeffs g.1) i :=
          finsum_congr fun i => mul_comm _ _
      _ = ∑ᶠ i', M (r.coeffs f.1) i' * r'.coeffs g.1 i' := key.symm
      _ = _ := finsum_congr fun i => mul_comm _ _
  have hTt : PairedFunctionSpace.IsTransposeMap A (PairedFunctionSpace.transposeMap A) :=
    Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap A) ⟨A', hIT⟩
  have hcol : ∀ g : r'.space.complexSubmodule, r.coeffs (PairedFunctionSpace.transposeMap A g).1 =
      applyKernel (swapKernel K) (r'.coeffs g.1) := by
    intro g
    funext i
    have hfin : (Function.support (Pi.single i (1 : ℂ) : r.Index → ℂ)).Finite :=
      (finite_singleton i).subset fun x hx => by
        by_contra hne
        exact hx (Pi.single_eq_of_ne hne _)
    have he : r.space.IsFinitelySupported (r.ofCoeffs (Pi.single i 1)) :=
      (hr.finite_iff _).2 hfin
    have ev : ∀ X ∈ r.space.complexSubmodule, r.space.pair X (r.ofCoeffs (Pi.single i 1)) =
        r.coeffs X i := by
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
  have hgiven : IsRepresentedBy r r' m K := by
    intro f hf κ'
    refine ⟨(hrows κ').subset fun κ hκ => left_ne_zero_of_mul hκ, ?_⟩
    have e := congrFun (hK (r.coeffs f)).2 κ'
    rw [e]
    show r'.coeffs (m f) κ' = r'.coeffs (m (r.ofCoeffs (r.coeffs f))) κ'
    rw [hr.ofCoeffs_coeffs f hf]
  have htgiven : IsRepresentedBy r' r (PairedFunctionSpace.transposeOfValues r.space r'.space m)
      (swapKernel K) := by
    intro g hg κ
    refine ⟨(hcols κ).subset fun κ' hκ' => left_ne_zero_of_mul hκ', ?_⟩
    unfold PairedFunctionSpace.transposeOfValues
    rw [dif_pos hg]
    exact congrFun (hcol ⟨g, hg⟩) κ
  refine ⟨hA, fun f hf => ?_, hTt, ?_, ?_, ?_, ?_⟩
  · have hc : (Function.support (r.coeffs f.1)).Finite := by
      have e := (hr.finite_iff (r.coeffs f.1)).1
      rw [hr.ofCoeffs_coeffs f.1 f.2] at e
      exact e hf
    rw [hA f, hm_eq f.1 f.2]
    exact (hr'.finite_iff _).2 (hsupp _ hc)
  · rw [hKE]
    exact hrows
  · rw [hKE]
    exact hcols
  · rw [hKE]
    exact hgiven
  · rw [hKE]
    exact htgiven
theorem transposeOfValues_mem {S S' : PairedFunctionSpace}
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    {g : S'.index → ComplexMatrix2} (hg : g ∈ S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m g ∈ S.complexSubmodule := by
  unfold PairedFunctionSpace.transposeOfValues
  rw [dif_pos hg]
  exact Subtype.property _
theorem comp_represents (hAP : RowFiniteKernels.ApplyComp)
    {M₁ : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    {M₂ : (r'.space.index → ComplexMatrix2) → r''.space.index → ComplexMatrix2}
    {K₁ : KernelMatrix r.Index r'.Index} {K₂ : KernelMatrix r'.Index r''.Index}
    (h₁ : IsRepresentedBy r r' M₁ K₁) (h₂ : IsRepresentedBy r' r'' M₂ K₂)
    (hm : ∀ f ∈ r.space.complexSubmodule, M₁ f ∈ r'.space.complexSubmodule)
    (rows₁ : RowFinite K₁) (rows₂ : RowFinite K₂) :
    IsRepresentedByComp r r' r'' (fun f => M₂ (M₁ f)) K₂ K₁ := by
  obtain ⟨_, hprod⟩ := hAP r'.Index r.Index K₁ rows₁
  obtain ⟨_, hPr, hall⟩ := hprod r''.Index K₂ rows₂
  refine ⟨fun κ'' κ => (rows₂ κ'').subset fun κ' h => left_ne_zero_of_mul h, fun f hf κ'' => ?_⟩
  refine ⟨(hPr κ'').subset fun κ h => left_ne_zero_of_mul h, ?_⟩
  rw [(hall (r.coeffs f)).2.2, (h₂ (M₁ f) (hm f hf) κ'').2]
  congr 1
  funext κ'
  exact (h₁ f hf κ').2
theorem latticeTransposeData_of_local (hK : RowFiniteKernels.Claim)
    {rs rb rp : PauliComponentsOfSymmetricKernel}
    (hs : IsFaithfulEvaluation rs) (hb : IsFaithfulEvaluation rb) (hp : IsFaithfulEvaluation rp)
    {D d₀ : (rs.space.index → ComplexMatrix2) → rb.space.index → ComplexMatrix2}
    {d₁ : (rb.space.index → ComplexMatrix2) → rp.space.index → ComplexMatrix2}
    {A : (rb.space.index → ComplexMatrix2) → rb.space.index → ComplexMatrix2}
    {T : KernelMatrix rb.Index rb.Index}
    (lD : IsLocalMap rs rb D) (l0 : IsLocalMap rs rb d₀) (l1 : IsLocalMap rb rp d₁)
    (hform : ∀ B ∈ rb.space.complexSubmodule, ∀ i, ApplySummableAt T (rb.coeffs B) i)
    (hA : ∀ B, A B = rb.ofCoeffs (applyKernel T (rb.coeffs B))) :
    LatticeTransposeData rs rb rp D d₀ d₁ A T := by
  have cD := lD.hasTransposeKernel hK.2.2.2 hs hb
  have hmT : ∀ B ∈ rb.space.complexSubmodule,
      PairedFunctionSpace.transposeOfValues rs.space rb.space D B ∈ rs.space.complexSubmodule :=
    fun B hB => transposeOfValues_mem D hB
  have rowsT : RowFinite (swapKernel (matrixKernel rs rb D)) := cD.column_finite
  have hAA : ∀ B ∈ rb.space.complexSubmodule, compTranspose rs rb D B ∈ rb.space.complexSubmodule :=
    fun B hB => lD.maps_into _ (hmT B hB)
  refine ⟨cD, l0.hasTransposeKernel hK.2.2.2 hs hb, l1.hasTransposeKernel hK.2.2.2 hb hp,
    fun l hl => ⟨lD.maps_into l hl, hmT _ (lD.maps_into l hl)⟩, fun B hB => ⟨hmT B hB, hAA B hB⟩,
    fun B hB => ⟨hform B hB, ?_, ?_⟩, ?_, ?_⟩
  · rw [hA]
    exact hb.ofCoeffs_mem _
  · refine rb.space.complexSubmodule.add_mem ?_ (hAA B hB)
    rw [hA]
    exact hb.ofCoeffs_mem _
  · exact comp_represents hK.1 cD.represents cD.transpose_represents lD.maps_into cD.row_finite
      rowsT
  · exact comp_represents hK.1 cD.transpose_represents cD.represents hmT rowsT cD.row_finite
end Local
section Sites
variable {σ : Type}
theorem ofPauliCoeffs_mem (c : Fin 3 × σ → ℂ) (i : σ) :
    ofPauliCoeffs c i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem ofPauliCoeffs_add (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (c + c') = ofPauliCoeffs c + ofPauliCoeffs c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_add <;> assumption
theorem ofPauliCoeffs_smul (z : ℂ) (c : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (z • c) = z • ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_smul <;> assumption
theorem hasFiniteSupp_ofPauliCoeffs_iff (c : Fin 3 × σ → ℂ) :
    HasFiniteSupp (ofPauliCoeffs c) ↔ (Function.support c).Finite := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.hasFiniteSupp_ofPauliCoeffs_iff <;> assumption
theorem traceFinsumPairing_ofPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    (a b : Fin 3 × σ → ℂ) (hb : (Function.support b).Finite) :
    traceFinsumPairing (ofPauliCoeffs a) (ofPauliCoeffs b) = ∑ᶠ i, a i * b i := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.traceFinsumPairing_ofPauliCoeffs <;> assumption
theorem vertexCoordinate_isFaithful (hP : OneLoop.PauliMatrixRelations) (σ : Type) :
    IsFaithfulEvaluation (vertexCoordinate σ) where
  ofCoeffs_mem c := fun i _ => ofPauliCoeffs_mem c i
  coeffs_ofCoeffs c := toPauliCoeffs_ofPauliCoeffs c
  ofCoeffs_coeffs _ hf := funext fun i => pauliCombination_pauliCoeff (hf i (mem_univ i))
  ofCoeffs_add c c' := ofPauliCoeffs_add c c'
  ofCoeffs_smul z c := ofPauliCoeffs_smul z c
  finite_iff c := hasFiniteSupp_ofPauliCoeffs_iff c
  pair_eq a b hb := traceFinsumPairing_ofPauliCoeffs hP a b hb
theorem eq_zero_of_toPauliCoeffs_eq_zero {f : σ → ComplexMatrix2} {x : σ}
    (hx : f x ∈ ComplexMatrix2.traceless) (h : ∀ a, toPauliCoeffs f (a, x) = 0) : f x = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.eq_zero_of_pauliCoeffs <;> assumption
end Sites
section Frames
variable (S : PairedFunctionSpace) (pos : S.index → Prop) (rev : S.index → S.index)
def antisymmetrize (f : S.index → ComplexMatrix2) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if pos b then f b else -f (rev b)
def extendByZero (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if h : pos b then ofPauliCoeffs c ⟨b, h⟩ else 0
def formOfCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  antisymmetrize S pos rev (extendByZero S pos c)
def restrictPositive (B : S.index → ComplexMatrix2) : {b : S.index // pos b} → ComplexMatrix2 :=
  fun b => B b.1
def positiveRepresentation : PauliComponentsOfSymmetricKernel where
  space := S
  Place := {b : S.index // pos b}
  ofCoeffs := formOfCoeffs S pos rev
  coeffs := fun B => toPauliCoeffs (restrictPositive S pos B)
structure IsOrientationFrame : Prop where
  xor_opposite : ∀ b, Xor (pos b) (pos (rev b))
  opposite_opposite : ∀ b, rev (rev b) = b
  mem_iff : ∀ B, B ∈ S.complexSubmodule ↔
    (∀ b, pos b → B b ∈ ComplexMatrix2.traceless) ∧ ∀ b, B (rev b) = -B b
  finite_iff : ∀ B, S.IsFinitelySupported B ↔ HasFiniteSupp (restrictPositive S pos B)
  pair_eq : ∀ B B', S.pair B B' =
    traceFinsumPairing (restrictPositive S pos B) (restrictPositive S pos B')
variable {S pos rev}
theorem antisymmetrize_of_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : pos b) :
    antisymmetrize S pos rev f b = f b := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_pos <;> assumption
theorem antisymmetrize_of_not_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : ¬ pos b) :
    antisymmetrize S pos rev f b = -f (rev b) := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_neg <;> assumption
theorem antisymmetrize_opposite (hF : IsOrientationFrame S pos rev) (f : S.index → ComplexMatrix2)
    (b : S.index) : antisymmetrize S pos rev f (rev b) = -antisymmetrize S pos rev f b := by
  rcases hF.xor_opposite b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [antisymmetrize_of_not_pos h₂, antisymmetrize_of_pos h₁, hF.opposite_opposite]
  · rw [antisymmetrize_of_pos h₁, antisymmetrize_of_not_pos h₂, neg_neg]
theorem antisymmetrize_add (f g : S.index → ComplexMatrix2) :
    antisymmetrize S pos rev (f + g) = antisymmetrize S pos rev f + antisymmetrize S pos rev g := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_add <;> assumption
theorem antisymmetrize_smul (z : ℂ) (f : S.index → ComplexMatrix2) :
    antisymmetrize S pos rev (z • f) = z • antisymmetrize S pos rev f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_smul <;> assumption
theorem formOfCoeffs_apply (c : Fin 3 × {b : S.index // pos b} → ℂ) (b : S.index) (hb : pos b) :
    formOfCoeffs S pos rev c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_apply <;> assumption
theorem restrictPositive_formOfCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    restrictPositive S pos (formOfCoeffs S pos rev c) = ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.positivePart_formOfCoeffs <;> assumption
theorem extendByZero_add (c c' : Fin 3 × {b : S.index // pos b} → ℂ) :
    extendByZero S pos (c + c') = extendByZero S pos c + extendByZero S pos c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.zeroExtension_add <;> assumption
theorem extendByZero_smul (z : ℂ) (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    extendByZero S pos (z • c) = z • extendByZero S pos c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.zeroExtension_smul <;> assumption
theorem formOfCoeffs_add (c c' : Fin 3 × {b : S.index // pos b} → ℂ) :
    formOfCoeffs S pos rev (c + c') = formOfCoeffs S pos rev c + formOfCoeffs S pos rev c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_add <;> assumption
theorem formOfCoeffs_smul (z : ℂ) (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    formOfCoeffs S pos rev (z • c) = z • formOfCoeffs S pos rev c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_smul <;> assumption
theorem formOfCoeffs_toPauliCoeffs (hF : IsOrientationFrame S pos rev)
    {f : S.index → ComplexMatrix2}
    (h₁ : ∀ b, pos b → f b ∈ ComplexMatrix2.traceless) (h₂ : ∀ b, f (rev b) = -f b) :
    formOfCoeffs S pos rev (toPauliCoeffs (restrictPositive S pos f)) = f := by
  have hpos : ∀ b (hb : pos b),
      formOfCoeffs S pos rev (toPauliCoeffs (restrictPositive S pos f)) b = f b := fun b hb =>
    (formOfCoeffs_apply _ b hb).trans (pauliCombination_pauliCoeff (h₁ b hb))
  funext b
  by_cases hb : pos b
  · exact hpos b hb
  · have hrb : pos (rev b) := by
      rcases hF.xor_opposite b with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hb
      · exact h
    have e : formOfCoeffs S pos rev (toPauliCoeffs (restrictPositive S pos f)) b =
        -extendByZero S pos (toPauliCoeffs (restrictPositive S pos f)) (rev b) :=
      antisymmetrize_of_not_pos hb
    have e' : extendByZero S pos (toPauliCoeffs (restrictPositive S pos f)) (rev b) =
        f (rev b) := by
      rw [← hpos _ hrb]
      exact (antisymmetrize_of_pos hrb).symm
    rw [e, e', h₂, neg_neg]
theorem positiveRepresentation_isFaithful (hP : OneLoop.PauliMatrixRelations)
    (hF : IsOrientationFrame S pos rev) : IsFaithfulEvaluation (positiveRepresentation S pos rev) where
  ofCoeffs_mem c := (hF.mem_iff _).2 ⟨fun b hb => by
    have e : formOfCoeffs S pos rev c b ∈ ComplexMatrix2.traceless := by
      rw [formOfCoeffs_apply c b hb]
      exact ofPauliCoeffs_mem c _
    exact e, fun b => antisymmetrize_opposite hF _ b⟩
  coeffs_ofCoeffs c := (congrArg toPauliCoeffs (restrictPositive_formOfCoeffs c)).trans
    (toPauliCoeffs_ofPauliCoeffs c)
  ofCoeffs_coeffs f hf := formOfCoeffs_toPauliCoeffs hF ((hF.mem_iff f).1 hf).1
    ((hF.mem_iff f).1 hf).2
  ofCoeffs_add c c' := formOfCoeffs_add c c'
  ofCoeffs_smul z c := formOfCoeffs_smul z c
  finite_iff c := by
    refine (hF.finite_iff _).trans ?_
    have e : restrictPositive S pos ((positiveRepresentation S pos rev).ofCoeffs c) = ofPauliCoeffs c :=
      restrictPositive_formOfCoeffs c
    rw [e]
    exact hasFiniteSupp_ofPauliCoeffs_iff c
  pair_eq a b hb := by
    refine (hF.pair_eq _ _).trans ?_
    have e₁ : restrictPositive S pos ((positiveRepresentation S pos rev).ofCoeffs a) = ofPauliCoeffs a :=
      restrictPositive_formOfCoeffs a
    have e₂ : restrictPositive S pos ((positiveRepresentation S pos rev).ofCoeffs b) = ofPauliCoeffs b :=
      restrictPositive_formOfCoeffs b
    rw [e₁, e₂]
    exact traceFinsumPairing_ofPauliCoeffs hP a b hb
end Frames
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
    (hX : X ∈ ComplexMatrix2.traceless) : ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless :=
  (hA.2.2 V (hA.1 V hV)).2.2.2.1 hX
section Difference
variable {σ : Type} {S : PairedFunctionSpace} {pos : S.index → Prop} {rev : S.index → S.index}
def twistedDifference (S : PairedFunctionSpace) (pos : S.index → Prop) (rev : S.index → S.index)
    (head tail : S.index → σ) (W : S.index → ComplexMatrix2) (l : σ → ComplexMatrix2) :
    S.index → ComplexMatrix2 :=
  antisymmetrize S pos rev fun b => ComplexMatrix2.conjugateBy (W b) (l (head b)) - l (tail b)
theorem twistedDifference_add (head tail : S.index → σ) (W : S.index → ComplexMatrix2)
    (l l' : σ → ComplexMatrix2) :
    twistedDifference S pos rev head tail W (l + l') =
      twistedDifference S pos rev head tail W l + twistedDifference S pos rev head tail W l' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.covDiffMap_add <;> assumption
theorem twistedDifference_smul (head tail : S.index → σ) (W : S.index → ComplexMatrix2)
    (l : σ → ComplexMatrix2) (z : ℂ) :
    twistedDifference S pos rev head tail W (z • l) =
      z • twistedDifference S pos rev head tail W l := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.covDiffMap_smul <;> assumption
theorem twistedDifference_isLocalMap (hA : ComplexMatrix2.ConjugationPreservesTraceless)
    (hP : OneLoop.PauliMatrixRelations) (hF : IsOrientationFrame S pos rev)
    (head tail : S.index → σ) (W : S.index → ComplexMatrix2)
    (hW : ∀ b, pos b → W b ∈ ComplexMatrix2.unitDeterminant)
    (hinc : ∀ x, {b : {b : S.index // pos b} | head b.1 = x ∨ tail b.1 = x}.Finite) :
    IsLocalMap (vertexCoordinate σ) (positiveRepresentation S pos rev)
      (twistedDifference S pos rev head tail W) := by
  refine isLocalMap_of_linear (vertexCoordinate_isFaithful hP σ) (positiveRepresentation_isFaithful hP hF) ?_
    (fun l _ l' _ => twistedDifference_add head tail W l l')
    (fun l _ z => twistedDifference_smul head tail W l z)
    (fun i' => {i | i.2 = head i'.2.1 ∨ i.2 = tail i'.2.1}) ?_ ?_ ?_
  · intro l hl
    refine (hF.mem_iff _).2 ⟨fun b hb => ?_, fun b => antisymmetrize_opposite hF _ b⟩
    have e : twistedDifference S pos rev head tail W l b =
        ComplexMatrix2.conjugateBy (W b) (l (head b)) - l (tail b) := antisymmetrize_of_pos hb
    exact e ▸ ComplexMatrix2.traceless.sub_mem
      (conjugateBy_mem_traceless hA (hW b hb) (hl _ (mem_univ _))) (hl _ (mem_univ _))
  · intro i'
    refine (Set.Finite.prod (Set.finite_univ (α := Fin 3))
      (Set.toFinite ({head i'.2.1, tail i'.2.1} : Set σ))).subset ?_
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
    have e₁ : l (head b.1) = 0 := eq_zero_of_toPauliCoeffs_eq_zero (hl _ (mem_univ _)) fun a' =>
      h (a', head b.1) (Or.inl rfl)
    have e₂ : l (tail b.1) = 0 := eq_zero_of_toPauliCoeffs_eq_zero (hl _ (mem_univ _)) fun a' =>
      h (a', tail b.1) (Or.inr rfl)
    have e : twistedDifference S pos rev head tail W l b.1 = 0 := by
      have e₃ : twistedDifference S pos rev head tail W l b.1 =
          ComplexMatrix2.conjugateBy (W b.1) (l (head b.1)) - l (tail b.1) :=
        antisymmetrize_of_pos b.2
      rw [e₃, e₁, e₂, conjugateBy_zero, sub_zero]
    exact (congrArg (pauliCoeff a) e).trans (pauliCoeff_zero a)
end Difference
theorem plainDifference_isLocalMap {σ : Type} {S : PairedFunctionSpace} {pos : S.index → Prop}
    {rev : S.index → S.index} (hA : ComplexMatrix2.ConjugationPreservesTraceless)
    (hP : OneLoop.PauliMatrixRelations) (hF : IsOrientationFrame S pos rev)
    (head tail : S.index → σ) (hh : ∀ b, head (rev b) = tail b) (ht : ∀ b, tail (rev b) = head b)
    (hinc : ∀ x, {b : {b : S.index // pos b} | head b.1 = x ∨ tail b.1 = x}.Finite) :
    IsLocalMap (vertexCoordinate σ) (positiveRepresentation S pos rev)
      (fun l b => l (head b) - l (tail b)) := by
  have e : (fun (l : σ → ComplexMatrix2) (b : S.index) => l (head b) - l (tail b)) =
      twistedDifference S pos rev head tail (fun _ => 1) := by
    funext l b
    by_cases hb : pos b
    · rw [twistedDifference, antisymmetrize_of_pos hb]
      simp [ComplexMatrix2.conjugateBy]
    · rw [twistedDifference, antisymmetrize_of_not_pos hb]
      simp [ComplexMatrix2.conjugateBy, hh, ht]
  have h1 : (1 : ComplexMatrix2) ∈ ComplexMatrix2.unitDeterminant := by
    show (1 : ComplexMatrix2).det = 1
    simp
  have := twistedDifference_isLocalMap hA hP hF head tail (fun _ => 1) (fun _ _ => h1) hinc
  exact (congrArg (fun m : (σ → ComplexMatrix2) → S.index → ComplexMatrix2 =>
    IsLocalMap (vertexCoordinate σ) (positiveRepresentation S pos rev) m) e).mpr this
theorem mem_list_four {α : Type*} {x a b c d : α} (h : x = a ∨ x = b ∨ x = c ∨ x = d) :
    x ∈ [a, b, c, d] := by
  simpa using h
theorem alternatingSum_four_add (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ComplexMatrix2) :
    (x₁ + y₁) + (x₂ + y₂) - (x₃ + y₃) - (x₄ + y₄) =
      (x₁ + x₂ - x₃ - x₄) + (y₁ + y₂ - y₃ - y₄) := by
  abel
theorem alternatingSum_four_smul (z : ℂ) (x₁ x₂ x₃ x₄ : ComplexMatrix2) :
    z • x₁ + z • x₂ - z • x₃ - z • x₄ = z • (x₁ + x₂ - x₃ - x₄) := by
  simp only [smul_sub, smul_add]
theorem faceSum_isLocalMap {ρ : Type} {S : PairedFunctionSpace} {pos : S.index → Prop}
    {rev : S.index → S.index} (hP : OneLoop.PauliMatrixRelations)
    (hF : IsOrientationFrame S pos rev) (c₁ c₂ c₃ c₄ : ρ → S.index) (h₁ : ∀ p, pos (c₁ p))
    (h₂ : ∀ p, pos (c₂ p)) (h₃ : ∀ p, pos (c₃ p)) (h₄ : ∀ p, pos (c₄ p))
    (hinc : ∀ b : {b : S.index // pos b},
      {p | b.1 = c₁ p ∨ b.1 = c₂ p ∨ b.1 = c₃ p ∨ b.1 = c₄ p}.Finite) :
    IsLocalMap (positiveRepresentation S pos rev) (vertexCoordinate ρ)
      (fun B p => B (c₁ p) + B (c₂ p) - B (c₃ p) - B (c₄ p)) := by
  refine isLocalMap_of_linear (positiveRepresentation_isFaithful hP hF) (vertexCoordinate_isFaithful hP ρ)
    ?_ ?_ ?_
    (fun i' => {i | i.2.1 = c₁ i'.2 ∨ i.2.1 = c₂ i'.2 ∨ i.2.1 = c₃ i'.2 ∨ i.2.1 = c₄ i'.2})
    ?_ ?_ ?_
  · intro B hB p _
    have hv := ((hF.mem_iff B).1 hB).1
    exact ComplexMatrix2.traceless.sub_mem (ComplexMatrix2.traceless.sub_mem
      (ComplexMatrix2.traceless.add_mem (hv _ (h₁ p)) (hv _ (h₂ p))) (hv _ (h₃ p))) (hv _ (h₄ p))
  · intro B _ B' _
    funext p
    exact alternatingSum_four_add (B (c₁ p)) (B (c₂ p)) (B (c₃ p)) (B (c₄ p)) (B' (c₁ p))
      (B' (c₂ p)) (B' (c₃ p)) (B' (c₄ p))
  · intro B _ z
    funext p
    exact alternatingSum_four_smul z (B (c₁ p)) (B (c₂ p)) (B (c₃ p)) (B (c₄ p))
  · intro i'
    refine (Set.Finite.prod (Set.finite_univ (α := Fin 3))
      (Set.toFinite ({⟨c₁ i'.2, h₁ _⟩, ⟨c₂ i'.2, h₂ _⟩, ⟨c₃ i'.2, h₃ _⟩, ⟨c₄ i'.2, h₄ _⟩} :
        Set {b : S.index // pos b}))).subset ?_
    rintro ⟨a, b⟩ h
    refine ⟨mem_univ _, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  · rintro ⟨a, b⟩
    refine (Set.Finite.prod (Set.finite_univ (α := Fin 3)) (hinc b)).subset ?_
    rintro ⟨a', p⟩ h
    exact ⟨mem_univ _, h⟩
  · rintro B hB ⟨a, p⟩ h
    have hv := ((hF.mem_iff B).1 hB).1
    have z : ∀ c : S.index, ∀ hc : pos c,
        (c = c₁ p ∨ c = c₂ p ∨ c = c₃ p ∨ c = c₄ p) → B c = 0 := fun c hc hm =>
      eq_zero_of_toPauliCoeffs_eq_zero (f := restrictPositive S pos B) (x := ⟨c, hc⟩) (hv c hc)
        fun a' => h (a', ⟨c, hc⟩) hm
    have e : B (c₁ p) + B (c₂ p) - B (c₃ p) - B (c₄ p) = 0 := by
      rw [z _ (h₁ p) (Or.inl rfl), z _ (h₂ p) (Or.inr (Or.inl rfl)),
        z _ (h₃ p) (Or.inr (Or.inr (Or.inl rfl))), z _ (h₄ p) (Or.inr (Or.inr (Or.inr rfl)))]
      simp
    exact (congrArg (pauliCoeff a) e).trans (pauliCoeff_zero a)
theorem wTranspose_of_const_weights {J J' : Type} {c : ℝ} (hc : c ≠ 0) (w : J → ℝ) (w' : J' → ℝ)
    (hw : ∀ i, w i = c) (hw' : ∀ i, w' i = c) (T : KernelMatrix J J') :
    PeriodicOperators.wTranspose w w' T = swapKernel T := by
  funext i i'
  simp [PeriodicOperators.wTranspose, swapKernel, hw, hw', hc]
structure Hypotheses : Prop where
  kernels : RowFiniteKernels.Claim
  conjugation : ComplexMatrix2.ConjugationPreservesTraceless
  pauli : OneLoop.PauliMatrixRelations
  orientation : PeriodicLattice.BondEndpointsOrientation.Statement
  finiteEdges : BondSetFields.ProductStructureHolds
  hessian : HessianKernel.KernelProperties
  faces : FacesContainingEdge.Holds
section FiniteSide
variable {L n k j : ℕ}
theorem edge_xor_opposite (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  have key : ∀ d : ℤ, d = PeriodicLattice.levelDepth (k + 1) (j + 1) →
      ∀ c : PeriodicLattice.Bond L n d,
      Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented := by
    rintro d rfl c
    exact ((G.orientation ⟨L, hL, ⟨k + 1, Nat.succ_pos k⟩, ⟨n, hn⟩⟩ (j + 1)
      (Nat.succ_le_succ hj)).2.2.2 c).2.2.2.2.2
  exact key _ (by simp [PeriodicLattice.levelDepth]) b
theorem edge_isOrientationFrame (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) :
    IsOrientationFrame (edgePairedSpace L n k j) (fun b => b.IsPositivelyOriented)
      PeriodicLattice.Bond.opposite where
  xor_opposite b := edge_xor_opposite G hL hn hj b
  opposite_opposite _ := rfl
  mem_iff _ := Iff.rfl
  finite_iff _ := Iff.rfl
  pair_eq _ _ := rfl
theorem edge_finite (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) : Finite (Edge L n k j) :=
  Set.finite_univ_iff.1 ((G.finiteEdges L hL k j hj).1 n hn).2.1
theorem onTorus_holds (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) : OnTorus L n k j := by
  intro U hU
  have hF := edge_isOrientationFrame G hL hn hj
  have hb : IsFaithfulEvaluation (edgePauliCoordinates L n k j) := positiveRepresentation_isFaithful G.pauli hF
  have := edge_finite G hL hn hj
  have hinc : ∀ x : Vertex L n k j, {b : {b : Edge L n k j // b.IsPositivelyOriented} |
      b.1.target = x ∨ b.1.source = x}.Finite := fun _ =>
    (Set.finite_univ_iff.2 (inferInstance : Finite (PositiveEdge L n k j))).subset
      (Set.subset_univ _)
  have lD : IsLocalMap (vertexCoordinate (Vertex L n k j)) (edgePauliCoordinates L n k j) (covDiff U) :=
    twistedDifference_isLocalMap (S := edgePairedSpace L n k j)
      (pos := fun b => b.IsPositivelyOriented) (rev := PeriodicLattice.Bond.opposite)
      G.conjugation G.pauli hF PeriodicLattice.Bond.target PeriodicLattice.Bond.source U
      (fun b _ => hU.1 b (mem_univ b)) hinc
  have l0 : IsLocalMap (vertexCoordinate (Vertex L n k j)) (edgePauliCoordinates L n k j) vertexCoboundary :=
    plainDifference_isLocalMap (S := edgePairedSpace L n k j)
      (pos := fun b => b.IsPositivelyOriented) (rev := PeriodicLattice.Bond.opposite)
      G.conjugation G.pauli hF PeriodicLattice.Bond.target PeriodicLattice.Bond.source
      (fun _ => rfl) (fun _ => rfl) hinc
  have l1 : IsLocalMap (edgePauliCoordinates L n k j) (vertexCoordinate (Face L n k j)) edgeCoboundary :=
    faceSum_isLocalMap (ρ := Face L n k j) (S := edgePairedSpace L n k j)
      (pos := fun b => b.IsPositivelyOriented) (rev := PeriodicLattice.Bond.opposite) G.pauli hF
      (fun p => PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis)
      (fun p => PeriodicLattice.Bond.forwardFrom
        (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis) p.secondAxis)
      (fun p => PeriodicLattice.Bond.forwardFrom
        (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis) p.firstAxis)
      (fun p => PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis)
      (fun p => ⟨_, add_sub_cancel_left _ _⟩) (fun p => ⟨_, add_sub_cancel_left _ _⟩)
      (fun p => ⟨_, add_sub_cancel_left _ _⟩) (fun p => ⟨_, add_sub_cancel_left _ _⟩)
      fun b => by
        refine (((G.faces L hL k j hj).1 n hn).2.2 {b} (finite_singleton b)).subset ?_
        intro p hp
        refine ⟨b, rfl, ?_⟩
        exact mem_list_four hp
  exact latticeTransposeData_of_local G.kernels (vertexCoordinate_isFaithful G.pauli _) hb
    (vertexCoordinate_isFaithful G.pauli _) lD l0 l1
    ((G.hessian L hL k j hj).1 n hn U hU).2.2.2.1 fun _ => rfl
end FiniteSide
section WholeSide
variable {L k j : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem fullSpace_isOrientationFrame {a : ℝ} (ha : 0 < a) :
    IsOrientationFrame (FullSpace.edgePairedSpace a) (fun b => b.IsPositivelyOriented)
      InfiniteLattice.Link.opposite where
  xor_opposite b := by
    rcases InfiniteLattice.xor_mem_positiveLinks ha b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
    · exact Or.inr ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
  opposite_opposite _ := rfl
  mem_iff _ := Iff.rfl
  finite_iff _ := Iff.rfl
  pair_eq _ _ := rfl
theorem links_with_endpoint_finite {a : ℝ} (y : InfiniteLattice.LatticePoint a) :
    {c : InfiniteLattice.Link a | c.initial = y ∨ c.terminal = y}.Finite := by apply _root_.YangMills.Construction.Tower.MeanStableFields.Infinite.finite_links_with_endpoint <;> assumption
theorem onFullSpace_holds (G : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j ≤ k) : OnFullSpace L k j := by
  intro U hU
  have hF := fullSpace_isOrientationFrame (meshAt_pos hL k j)
  have hb : IsFaithfulEvaluation (FullSpace.edgePauliCoordinates L k j) :=
    positiveRepresentation_isFaithful G.pauli hF
  have hinc : ∀ x : FullSpace.Vertex L k j,
      {b : {b : FullSpace.Edge L k j // b.IsPositivelyOriented} |
        b.1.terminal = x ∨ b.1.initial = x}.Finite :=
    fun x => by
      refine ((links_with_endpoint_finite x).preimage Subtype.val_injective.injOn).subset ?_
      rintro b (h | h)
      · exact Or.inr h
      · exact Or.inl h
  have lD : IsLocalMap (vertexCoordinate (FullSpace.Vertex L k j)) (FullSpace.edgePauliCoordinates L k j)
      (FullSpace.covDiff U) :=
    twistedDifference_isLocalMap (S := FullSpace.edgePairedSpace (meshAt L k j))
      (pos := fun b => b.IsPositivelyOriented) (rev := InfiniteLattice.Link.opposite)
      G.conjugation G.pauli hF InfiniteLattice.Link.terminal InfiniteLattice.Link.initial U
      (fun b _ => hU.1 b) hinc
  have l0 : IsLocalMap (vertexCoordinate (FullSpace.Vertex L k j)) (FullSpace.edgePauliCoordinates L k j)
      FullSpace.vertexCoboundary :=
    plainDifference_isLocalMap (S := FullSpace.edgePairedSpace (meshAt L k j))
      (pos := fun b => b.IsPositivelyOriented) (rev := InfiniteLattice.Link.opposite)
      G.conjugation G.pauli hF InfiniteLattice.Link.terminal InfiniteLattice.Link.initial
      (fun _ => rfl) (fun _ => rfl) hinc
  have l1 : IsLocalMap (FullSpace.edgePauliCoordinates L k j) (vertexCoordinate (FullSpace.Face L k j))
      FullSpace.edgeCoboundary :=
    faceSum_isLocalMap (ρ := FullSpace.Face L k j)
      (S := FullSpace.edgePairedSpace (meshAt L k j)) (pos := fun b => b.IsPositivelyOriented)
      (rev := InfiniteLattice.Link.opposite) G.pauli hF
      (fun p => InfiniteLattice.Link.forwardFrom p.corner p.lowAxis)
      (fun p => InfiniteLattice.Link.forwardFrom
        (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis)
      (fun p => InfiniteLattice.Link.forwardFrom
        (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis)
      (fun p => InfiniteLattice.Link.forwardFrom p.corner p.highAxis)
      (fun p => ⟨_, add_sub_cancel_left _ _⟩) (fun p => ⟨_, add_sub_cancel_left _ _⟩)
      (fun p => ⟨_, add_sub_cancel_left _ _⟩) (fun p => ⟨_, add_sub_cancel_left _ _⟩)
      fun b => by
        refine (((G.faces L hL k j hj).2).2.2 {b} (finite_singleton b)).subset ?_
        intro p hp
        refine ⟨b, rfl, ?_⟩
        exact mem_list_four hp
  have hc : meshAt L k j ^ 4 ≠ 0 := pow_ne_zero _ (meshAt_pos hL k j).ne'
  exact ⟨latticeTransposeData_of_local G.kernels (vertexCoordinate_isFaithful G.pauli _) hb
      (vertexCoordinate_isFaithful G.pauli _) lD l0 l1
      ((G.hessian L hL k j hj).2 U hU).2.2.2.1 fun _ => rfl,
    wTranspose_of_const_weights hc _ _ (fun _ => rfl) (fun _ => rfl) _,
    wTranspose_of_const_weights hc _ _ (fun _ => rfl) (fun _ => rfl) _,
    wTranspose_of_const_weights hc _ _ (fun _ => rfl) (fun _ => rfl) _⟩
end WholeSide
theorem claim_holds (h₁ : RowFiniteKernels.Claim)
    (h₂ : ComplexMatrix2.ConjugationPreservesTraceless)
    (h₃ : OneLoop.PauliMatrixRelations)
    (h₄ : PeriodicLattice.BondEndpointsOrientation.Statement)
    (h₅ : BondSetFields.ProductStructureHolds)
    (h₆ : HessianKernel.KernelProperties)
    (h₇ : FacesContainingEdge.Holds) : Claim := by
  have G : Hypotheses := ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  intro L hL k j hj
  exact ⟨fun n hn => onTorus_holds G hL hn hj, onFullSpace_holds G hL hj⟩
end YangMills.Construction.Tower.CovDiffTransposes
end
