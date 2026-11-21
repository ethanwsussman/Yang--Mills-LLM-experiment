import YangMills.Construction.PeriodicOperators.IdentityOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.IdKernelFacts
open TorusMetric (euclidNormVec)
theorem translate_injective {I : PeriodicData} (hI : IsPeriodic I) (ι : I.Carrier)
    {m m' : Fin 4 → ℤ} (h : I.translate m ι = I.translate m' ι) : m = m' := by
  have h₁ : I.translate (m - m') (I.translate m' ι) = I.translate m' ι := by
    rw [← hI.translate_add, add_sub_cancel, h]
  exact sub_eq_zero.mp (hI.free _ _ h₁)
theorem idKernel_expDecay (I : PeriodicData) {C : ℝ} (hC : 1 ≤ C) (δ : ℝ) :
    ExpDecay I I (idKernel I) C δ := by
  intro ι' ι
  by_cases h : ι' = ι
  · subst h
    have h₀ : euclidNormVec (I.pos ι' - I.pos ι') = 0 := by simp [euclidNormVec]
    rw [h₀]
    simpa [idKernel] using hC
  · have h₀ : idKernel I ι' ι = 0 := by simp [idKernel, h]
    rw [h₀, norm_zero]
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
theorem idKernel_isDecayRate (I : PeriodicData) {δ : ℝ} (hδ : 0 < δ) :
    IsDecayRate I I (idKernel I) δ :=
  ⟨hδ, 1, one_pos, idKernel_expDecay I le_rfl δ⟩
theorem idKernel_symbolSummable {I : PeriodicData} (hI : IsPeriodic I) :
    SymbolSummableOn I I (idKernel I) univ := by
  classical
  intro κ _ ι' ι
  by_cases h : ∃ n, ι' = I.translate n ι
  · obtain ⟨n, hn⟩ := h
    refine summable_of_ne_finset_zero (s := {n}) fun m hm => ?_
    have hne : ι' ≠ I.translate m ι := fun e =>
      hm (Finset.mem_singleton.mpr (translate_injective hI ι (e.symm.trans hn)))
    simp [symbolSummand, idKernel, hne]
  · refine summable_of_ne_finset_zero (s := ∅) fun m _ => ?_
    have hne : ι' ≠ I.translate m ι := fun e => h ⟨m, e⟩
    simp [symbolSummand, idKernel, hne]
theorem pairsWithId_of_isPeriodicKernel {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hid : IsPeriodicKernel I I (idKernel I))
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) :
    PairsWithId I I' T where
  exists_rate := by
    obtain ⟨-, C, δ, hC, hδ, hb⟩ := hT
    exact ⟨δ, hδ, C, hC, hb⟩
  withRate := fun δ hr =>
    ⟨hI, hI', hI, hT, hr, hid, idKernel_isDecayRate I hr.1⟩
  common_bound := fun δ C _ _ hb =>
    ⟨fun ι' ι => (hb ι' ι).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.exp_pos _).le),
      idKernel_expDecay I (le_max_right C 1) δ⟩
theorem claim_of (h₁ : CovariantFiniteRange.Claim)
    (h₂ : SymbolOnQuotients.Claim) : IdKernelFacts.Claim := by
  intro I hI
  obtain ⟨-, hid, -, hmatrix⟩ := h₁.1 I hI
  have hformed := idKernel_symbolSummable hI
  have hrate : ∀ δ : ℝ, 0 < δ → IsDecayRate I I (idKernel I) δ :=
    fun δ hδ => idKernel_isDecayRate I hδ
  refine ⟨hid, hrate, hformed, fun κ ι' ι => ?_, hmatrix,
    fun I' hI' T hT => pairsWithId_of_isPeriodicKernel hI hI' hid hT,
    pairsWithId_of_isPeriodicKernel hI hI hid hid,
    fun δ hδ => ⟨hI, hI, hI, hid, hrate δ hδ, hid, hrate δ hδ⟩⟩
  rw [← (h₂ I I hI hI _ hid).quotSymbol_mkQuot κ (hformed κ (mem_univ κ)) ι' ι, hmatrix κ]
end YangMills.Construction.PeriodicOperators.IdKernelFacts
end
