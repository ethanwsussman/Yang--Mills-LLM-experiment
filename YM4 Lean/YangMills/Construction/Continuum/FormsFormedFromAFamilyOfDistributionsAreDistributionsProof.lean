import YangMills.Construction.Continuum.FormsFormedFromAFamilyOfDistributionsAreDistributions
import Mathlib
set_option autoImplicit false
open TopologicalSpace YangMills.Construction.ReflectionSpaces.Euclidean YangMills.Construction.SetPartition YangMills.Construction.AmbientPoints YangMills.Construction.Continuum.TensorProduct
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.Continuum.BlockProducts.AssembledForms
section Norms
variable {n : ℕ}
private theorem bddAbove_norm_partialDeriv {W : Opens (Coord n)} (F : testFunctionSpace W) {k : ℕ}
    (c : Fin k → Fin n) :
    BddAbove (Set.range fun x => ‖partialDeriv c (F : Coord n → ℂ) x‖) := by
  obtain ⟨hF, cF, -⟩ := F.2
  have hcont : Continuous (partialDeriv c (F : Coord n → ℂ)) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Coord n) ℂ
      fun j => Pi.single (c j) 1).continuous.comp
      (hF.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hsupp : HasCompactSupport (partialDeriv c (F : Coord n → ℂ)) :=
    (cF.iteratedFDeriv k).comp_left (g := fun A : (Coord n) [×k]→L[ℝ] ℂ =>
      A fun j => Pi.single (c j) 1) rfl
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
  exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
private theorem uniformNorm_partialDeriv_le_cNorm (ν : ℕ) (F : Coord n → ℂ) {k : ℕ} (hk : k ≤ ν)
    (c : Fin k → Fin n) :
    YangMills.Construction.TestFunctions.uniformNorm (partialDeriv c F) ≤ cNorm ν F :=
  le_ciSup (f := fun p : DerivIndex n ν =>
      YangMills.Construction.TestFunctions.uniformNorm (partialDeriv p.2 F))
    (Set.finite_range _).bddAbove ⟨⟨k, Nat.lt_succ_of_le hk⟩, c⟩
private instance instNonemptyDerivIndex (ν : ℕ) : Nonempty (DerivIndex n ν) :=
  ⟨⟨0, fun i => absurd i.2 (by simp)⟩⟩
private theorem cNorm_mono {ν ν' : ℕ} (h : ν ≤ ν') (F : Coord n → ℂ) :
    cNorm ν F ≤ cNorm ν' F :=
  ciSup_le fun p => uniformNorm_partialDeriv_le_cNorm ν' F (by have := p.1.2; omega) p.2
end Norms
section Sums
variable {n : ℕ} {W : Opens (Coord n)}
private def distribAdd (S T : Distribution W) : Distribution W where
  form := S.form + T.form
  bound K hK hKW := by
    obtain ⟨ν₁, C₁, hC₁, b₁⟩ := S.bound K hK hKW
    obtain ⟨ν₂, C₂, hC₂, b₂⟩ := T.bound K hK hKW
    refine ⟨max ν₁ ν₂, C₁ + C₂, add_nonneg hC₁ hC₂, fun F hF => ?_⟩
    have h₁ := mul_le_mul_of_nonneg_left
      (cNorm_mono (le_max_left ν₁ ν₂) (F : Coord n → ℂ)) hC₁
    have h₂ := mul_le_mul_of_nonneg_left
      (cNorm_mono (le_max_right ν₁ ν₂) (F : Coord n → ℂ)) hC₂
    calc ‖(S.form + T.form) F‖ ≤ ‖S.form F‖ + ‖T.form F‖ := norm_add_le _ _
      _ ≤ C₁ * cNorm ν₁ (F : Coord n → ℂ) + C₂ * cNorm ν₂ (F : Coord n → ℂ) :=
        add_le_add (b₁ F hF) (b₂ F hF)
      _ ≤ (C₁ + C₂) * cNorm (max ν₁ ν₂) (F : Coord n → ℂ) := by
        rw [add_mul]
        exact add_le_add h₁ h₂
private theorem exists_distribution_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → Module.Dual ℂ (testFunctionSpace W))
    (h : ∀ i ∈ s, ∃ T : Distribution W, T.form = f i) :
    ∃ T : Distribution W, T.form = ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⟨0, fun _ _ _ => ⟨0, 0, le_rfl, fun _ _ => by simp⟩⟩, by simp⟩
  | insert a s ha ih =>
    obtain ⟨S, hS⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨T, hT⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨distribAdd S T, by
      rw [Finset.sum_insert ha, ← hS, ← hT]
      rfl⟩
end Sums
section Permutations
variable {m n : ℕ} (e : Fin m ≃ Fin n)
private def coordPerm : Coord m ≃L[ℝ] Coord n :=
  (LinearEquiv.funCongrLeft ℝ ℝ e.symm).toContinuousLinearEquiv
private theorem coordPerm_apply (y : Coord m) :
    coordPerm e y = y ∘ e.symm :=
  rfl
private theorem coordPerm_single (a : Fin m) :
    coordPerm e (Pi.single a 1) = Pi.single (e a) 1 := by
  funext k
  rw [coordPerm_apply, Function.comp_apply]
  by_cases h : k = e a
  · subst h
    simp
  · have h' : e.symm k ≠ a := fun h'' => h (by rw [← h'']; simp)
    simp [h, h']
private theorem partialDeriv_comp_coordPerm {F : Coord n → ℂ} (hF : ContDiff ℝ ∞ F) {k : ℕ}
    (c : Fin k → Fin m) (y : Coord m) :
    partialDeriv c (F ∘ coordPerm e) y =
      partialDeriv (e ∘ c) F (coordPerm e y) := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right
    (coordPerm e : Coord m →L[ℝ] Coord n) hF y (i := k)
    (by exact_mod_cast le_top)
  change iteratedFDeriv ℝ k (F ∘ (coordPerm e : Coord m →L[ℝ] Coord n)) y _ = _
  rw [h]
  exact congrArg (iteratedFDeriv ℝ k F (coordPerm e y))
    (funext fun j => coordPerm_single e (c j))
private theorem cNorm_comp_coordPerm_le {W : Opens (Coord n)} (F : testFunctionSpace W) (ν : ℕ) :
    cNorm ν ((F : Coord n → ℂ) ∘ coordPerm e) ≤
      cNorm ν (F : Coord n → ℂ) := by
  refine ciSup_le fun p => ?_
  refine le_trans ?_ (uniformNorm_partialDeriv_le_cNorm ν (F : Coord n → ℂ)
    (Nat.lt_succ_iff.1 p.1.2) (e ∘ p.2))
  refine ciSup_le fun y => ?_
  rw [partialDeriv_comp_coordPerm e F.2.1]
  exact le_ciSup (bddAbove_norm_partialDeriv F (e ∘ p.2)) (coordPerm e y)
end Permutations
variable {Q : ℕ} {π : PartitionsFin Q}
private theorem exists_distribution_partitionForm (u : DistribFamily)
    (hπ : π ∈ nonSingletonPartitions Q) :
    ∃ T : Distribution (distinctWithinBlocks π), T.form = partitionForm u hπ := by
  set T := tensorDist fun i => u (orderedBlockCard π i) (two_le_orderedBlockCard hπ i) with hT
  refine ⟨⟨partitionForm u hπ, fun K hK hKW => ?_⟩, rfl⟩
  have hK' : IsCompact (regroup π '' K) := hK.image (regroup π).continuous
  have hKW' : regroup π '' K ⊆ (blockConfigProd π : Set _) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (regroup_mem_blockConfigProd_iff π x).2 (hKW hx)
  obtain ⟨ν, C, hC, hb⟩ := T.bound _ hK' hKW'
  refine ⟨ν, C, hC, fun F hF => ?_⟩
  have hsupp : tsupport (regroupTest π F : Coord (∑ i, 4 * orderedBlockCard π i) → ℂ) ⊆
      regroup π '' K := by
    intro y hy
    have hy' : y ∈ tsupport ((F : Coord (4 * Q) → ℂ) ∘ (regroup π).symm) := hy
    rw [tsupport_comp_eq_preimage] at hy'
    exact ⟨_, hF hy', by simp⟩
  calc ‖partitionForm u hπ F‖ = ‖T.form (regroupTest π F)‖ := rfl
    _ ≤ C * cNorm ν (regroupTest π F : Coord (∑ i, 4 * orderedBlockCard π i) → ℂ) := hb _ hsupp
    _ ≤ C * cNorm ν (F : Coord (4 * Q) → ℂ) :=
      mul_le_mul_of_nonneg_left (cNorm_comp_coordPerm_le (blockCoordEquiv π) F ν) hC
theorem assembledFormsAreDistributions : AssembledFormsAreDistributions := by
  intro u
  refine ⟨fun Q _ π hπ => exists_distribution_partitionForm u hπ, fun Q _ => ?_⟩
  refine exists_distribution_finsetSum _ _ fun π _ => ?_
  obtain ⟨T, hT⟩ := exists_distribution_partitionForm u π.2
  exact ⟨T.restrict (configSpace_le_distinctWithinBlocks π.1), by
    rw [← hT]
    rfl⟩
end YangMills.Construction.Continuum.BlockProducts.AssembledForms
end
