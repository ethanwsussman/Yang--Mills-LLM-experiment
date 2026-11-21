import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.Towers.ComplexAveragesCommuteWithIntegerTranslations
import YangMills.Construction.Towers.ConfigurationsNearOneHaveSmallIterates
import YangMills.Construction.Towers.FieldsAndTheirValuesProof
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLattice
import YangMills.Construction.Towers.TheIteratedDriftIsGivenByItsKernel
import YangMills.Construction.Towers.TranslationRelationsOfTheTwoOperatorFunctions
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.FullSpace.ShiftCovariance
open PeriodicOperators
open InfiniteLattice (AmbientSpace latticeSubgroup)
open FieldValueFunctions
open _root_.YangMills.Construction.Tower.AsDifferentials (boundedSubmodule)
open _root_.YangMills.Construction.Tower.AsDifferentials
  (BoundedBilinear HasUniqueQuadraticTerm IsQuadraticExpansion quadraticTerm quadraticTermAt)
open _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials
  (complexQuadraticTerm iterMean iterLogRatio iterRatio topLogRatio topDeriv)
open _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded (IsDefinedAt)
open _root_.YangMills.Construction.Tower.FullSpace.Translations (spaceShift)
section Kernels
variable {N N' : Type}
theorem entry_eq_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ} (h : Represents T M)
    (i' : N') (i : N) : T i' i = M (basisFunction i : N → ℂ) i' := by apply _root_.YangMills.Construction.Tower.FreeOperators.kernel_eq_apply_indicator <;> assumption
theorem kernel_entries_eq_of_maps_related {T₁ T₂ : KernelMatrix N N'} {M₁ M₂ : (N → ℂ) → N' → ℂ}
    (σ : N ≃ N) (σ' : N' ≃ N') (h₁ : Represents T₁ M₁) (h₂ : Represents T₂ M₂)
    (hc : ∀ f, M₂ (f ∘ σ.symm) = M₁ f ∘ σ'.symm) (i' : N') (i : N) :
    T₂ (σ' i') (σ i) = T₁ i' i := by
  rw [entry_eq_of_represents h₂, entry_eq_of_represents h₁]
  have e : (basisFunction (σ i) : N → ℂ) = (basisFunction i : N → ℂ) ∘ σ.symm := by
    funext x
    simp only [basisFunction, Function.comp]
    by_cases hx : x = σ i
    · subst hx
      simp
    · have : σ.symm x ≠ i := fun h => hx (by rw [← h]; simp)
      simp [hx, this]
  rw [e, hc]
  simp
theorem maps_related_of_kernel_entries {T₁ T₂ : KernelMatrix N N'} {M₁ M₂ : (N → ℂ) → N' → ℂ}
    (σ : N ≃ N) (σ' : N' ≃ N') (h₁ : Represents T₁ M₁) (h₂ : Represents T₂ M₂)
    (he : ∀ i' i, T₂ (σ' i') (σ i) = T₁ i' i) (f : N → ℂ) :
    M₂ (f ∘ σ.symm) = M₁ f ∘ σ'.symm := by
  funext i'
  rw [← (h₂ _).2, Function.comp_apply, ← (h₁ _).2]
  simp only [applyKernel, Function.comp]
  rw [← Equiv.tsum_eq σ]
  refine tsum_congr fun i => ?_
  have := he (σ'.symm i') i
  simp only [Equiv.apply_symm_apply] at this
  simp [this]
end Kernels
structure IsCompatibleRelabelling (r : PauliComponentsOfSymmetricKernel) (σ : r.Index ≃ r.Index)
    (a : (r.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2) : Prop where
  ofCoeffs_mem : ∀ f, r.ofCoeffs f ∈ r.space.complexSubmodule
  ofCoeffs_coeffs : ∀ g ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs g) = g
  coeffs_ofCoeffs : ∀ f, r.coeffs (r.ofCoeffs f) = f
  coeffs_act : ∀ g, r.coeffs (a g) = r.coeffs g ∘ σ.symm
  act_mem : ∀ g ∈ r.space.complexSubmodule, a g ∈ r.space.complexSubmodule
section Compatible
variable {r r' : PauliComponentsOfSymmetricKernel} {σ : r.Index ≃ r.Index} {σ' : r'.Index ≃ r'.Index}
  {a : (r.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2}
  {a' : (r'.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
theorem IsCompatibleRelabelling.ofCoeffs_comp_symm (h : IsCompatibleRelabelling r σ a)
    (f : r.Index → ℂ) : r.ofCoeffs (f ∘ σ.symm) = a (r.ofCoeffs f) := by
  have e := h.coeffs_act (r.ofCoeffs f)
  rw [h.coeffs_ofCoeffs] at e
  rw [← e, h.ofCoeffs_coeffs _ (h.act_mem _ (h.ofCoeffs_mem f))]
theorem mapOnCoeffs_comp_symm (h : IsCompatibleRelabelling r σ a)
    {m₁ m₂ : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hm : ∀ g ∈ r.space.complexSubmodule, r'.coeffs (m₂ (a g)) = r'.coeffs (m₁ g) ∘ σ'.symm)
    (f : r.Index → ℂ) :
    PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m₂ (f ∘ σ.symm) =
      PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m₁ f ∘ σ'.symm := by
  simp only [PauliComponentsOfSymmetricKernel.mapOnCoeffs]
  rw [h.ofCoeffs_comp_symm, hm _ (h.ofCoeffs_mem f)]
theorem transposeOfValues_act (h : IsCompatibleRelabelling r σ a)
    (h' : IsCompatibleRelabelling r' σ' a')
    {m₁ m₂ : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hm : ∀ g ∈ r.space.complexSubmodule, r'.coeffs (m₂ (a g)) = r'.coeffs (m₁ g) ∘ σ'.symm)
    (G₁ : Represents (PauliComponentsOfSymmetricKernel.kernel r r' m₁) (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m₁))
    (G₂ : Represents (PauliComponentsOfSymmetricKernel.kernel r r' m₂) (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m₂))
    (T₁ : Represents (swapKernel (PauliComponentsOfSymmetricKernel.kernel r r' m₁))
      (PauliComponentsOfSymmetricKernel.transposeOnCoeffs r r' m₁))
    (T₂ : Represents (swapKernel (PauliComponentsOfSymmetricKernel.kernel r r' m₂))
      (PauliComponentsOfSymmetricKernel.transposeOnCoeffs r r' m₂))
    {g : r'.space.index → ComplexMatrix2} (hg : g ∈ r'.space.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues r.space r'.space m₂ (a' g) =
      a (PairedFunctionSpace.transposeOfValues r.space r'.space m₁ g) := by
  have he := kernel_entries_eq_of_maps_related σ σ' G₁ G₂ (mapOnCoeffs_comp_symm h hm)
  have hr := maps_related_of_kernel_entries σ' σ T₁ T₂ (fun i i' => he i' i) (r'.coeffs g)
  simp only [PauliComponentsOfSymmetricKernel.transposeOnCoeffs, PauliComponentsOfSymmetricKernel.mapOnCoeffs] at hr
  rw [h'.ofCoeffs_comp_symm, h'.ofCoeffs_coeffs _ hg] at hr
  have m₁mem : PairedFunctionSpace.transposeOfValues r.space r'.space m₁ g ∈
      r.space.complexSubmodule := by
    simp only [PairedFunctionSpace.transposeOfValues, dif_pos hg]
    exact Subtype.property _
  have m₂mem : PairedFunctionSpace.transposeOfValues r.space r'.space m₂ (a' g) ∈
      r.space.complexSubmodule := by
    simp only [PairedFunctionSpace.transposeOfValues, dif_pos (h'.act_mem _ hg)]
    exact Subtype.property _
  rw [← h.ofCoeffs_coeffs _ m₂mem, hr, ← h.coeffs_act, h.ofCoeffs_coeffs _ (h.act_mem _ m₁mem)]
end Compatible
theorem pauli_sum_mem_traceless (c : Fin 3 → ℂ) :
    (∑ a, c a • ComplexMatrix2.pauliFamily a) ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_sum (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ a', c a' • ComplexMatrix2.pauliFamily a') = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
section Links
variable {a : ℝ}
theorem opposite_isPositivelyOriented_of_not {b : InfiniteLattice.Link a}
    (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem not_opposite_isPositivelyOriented (ha : a ≠ 0) {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.not_opposite_isPositivelyOriented <;> assumption
theorem castVec_mem_latticeSubgroup (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ) :
    castVec n ∈ latticeSubgroup a := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValues.castVec_mem <;> assumption
theorem castVec_neg (n : Fin 4 → ℤ) : castVec (-n) = -castVec n := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.castVec_neg <;> assumption
theorem coe_vertexImage_latticeShift (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (x : InfiniteLattice.LatticePoint a) :
    ((vertexImage (latticeShift n) x : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      (x : AmbientSpace) + castVec n := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValues.coe_vertexImage_intShift <;> assumption
theorem coe_vertexPreimage_latticeShift (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (x : InfiniteLattice.LatticePoint a) :
    ((vertexPreimage (latticeShift n) x : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      (x : AmbientSpace) - castVec n := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValues.coe_vertexPreimage_intShift <;> assumption
theorem vertexImage_latticeShift_neg (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (x : InfiniteLattice.LatticePoint a) :
    vertexImage (latticeShift (-n)) x = vertexPreimage (latticeShift n) x := by
  refine Subtype.ext ?_
  rw [coe_vertexImage_latticeShift h, coe_vertexPreimage_latticeShift h, castVec_neg,
    sub_eq_add_neg]
theorem vertexPreimage_vertexImage (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (x : InfiniteLattice.LatticePoint a) :
    vertexPreimage (latticeShift n) (vertexImage (latticeShift n) x) = x := by
  refine Subtype.ext ?_
  rw [coe_vertexPreimage_latticeShift h, coe_vertexImage_latticeShift h, add_sub_cancel_right]
theorem vertexImage_vertexPreimage (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (x : InfiniteLattice.LatticePoint a) :
    vertexImage (latticeShift n) (vertexPreimage (latticeShift n) x) = x := by
  refine Subtype.ext ?_
  rw [coe_vertexImage_latticeShift h, coe_vertexPreimage_latticeShift h, sub_add_cancel]
def translateLink (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ) (b : InfiniteLattice.Link a) :
    InfiniteLattice.Link a where
  initial := ⟨(b.initial : AmbientSpace) + castVec n,
    add_mem b.initial.2 (castVec_mem_latticeSubgroup h n)⟩
  terminal := ⟨(b.terminal : AmbientSpace) + castVec n,
    add_mem b.terminal.2 (castVec_mem_latticeSubgroup h n)⟩
  isAdjacent := by
    obtain ⟨μ, e⟩ := b.isAdjacent
    refine ⟨μ, ?_⟩
    have d : (⟨(b.terminal : AmbientSpace) + castVec n,
        add_mem b.terminal.2 (castVec_mem_latticeSubgroup h n)⟩ :
        InfiniteLattice.LatticePoint a) -
        ⟨(b.initial : AmbientSpace) + castVec n,
          add_mem b.initial.2 (castVec_mem_latticeSubgroup h n)⟩ =
        b.terminal - b.initial := Subtype.ext (add_sub_add_right_eq_sub _ _ _)
    rwa [d]
theorem translateLink_sub (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) :
    (translateLink h n b).terminal - (translateLink h n b).initial = b.terminal - b.initial :=
  Subtype.ext (add_sub_add_right_eq_sub _ _ _)
theorem edgeImage_latticeShift_eq (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) :
    edgeImage (latticeShift n) b = translateLink h n b := by
  have hs : ∀ x : InfiniteLattice.LatticePoint a,
      (⟨(x : AmbientSpace) + castVec n, add_mem x.2 (castVec_mem_latticeSubgroup h n)⟩ :
        InfiniteLattice.LatticePoint a) =
      vertexImage (latticeShift n) x := fun x =>
    Subtype.ext (coe_vertexImage_latticeShift h n x).symm
  have e := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a => b'.initial = vertexImage (latticeShift n) b.initial ∧
      b'.terminal = vertexImage (latticeShift n) b.terminal) ⟨translateLink h n b, hs _, hs _⟩
  exact InfiniteLattice.Link.ext (e.1.trans (hs _).symm) (e.2.trans (hs _).symm)
theorem edgePreimage_latticeShift_eq (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) :
    edgePreimage (latticeShift n) b = translateLink h (-n) b := by
  have hs : ∀ x : InfiniteLattice.LatticePoint a,
      (⟨(x : AmbientSpace) + castVec (-n), add_mem x.2 (castVec_mem_latticeSubgroup h (-n))⟩ :
      InfiniteLattice.LatticePoint a) = vertexPreimage (latticeShift n) x := fun x =>
    Subtype.ext (by
      rw [coe_vertexPreimage_latticeShift h n x]
      change (x : AmbientSpace) + castVec (-n) = _
      rw [castVec_neg, sub_eq_add_neg])
  have e := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = vertexPreimage (latticeShift n) b.initial ∧
      b'.terminal = vertexPreimage (latticeShift n) b.terminal)
    ⟨translateLink h (-n) b, hs _, hs _⟩
  exact InfiniteLattice.Link.ext (e.1.trans (hs _).symm) (e.2.trans (hs _).symm)
theorem translateLink_isPositivelyOriented (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    (translateLink h n b).IsPositivelyOriented := by
  obtain ⟨μ, e⟩ := hb
  exact ⟨μ, (translateLink_sub h n b).trans e⟩
theorem translateLink_opposite (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) : translateLink h n b.opposite = (translateLink h n b).opposite :=
  rfl
theorem translateLink_neg_translateLink (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) : translateLink h (-n) (translateLink h n b) = b := by
  refine InfiniteLattice.Link.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change (b.initial : AmbientSpace) + castVec n + castVec (-n) = _
    rw [castVec_neg, add_neg_cancel_right]
  · change (b.terminal : AmbientSpace) + castVec n + castVec (-n) = _
    rw [castVec_neg, add_neg_cancel_right]
theorem translateLink_translateLink_neg (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) : translateLink h n (translateLink h (-n) b) = b := by
  have := translateLink_neg_translateLink h (-n) b
  rwa [neg_neg] at this
theorem edgePreimage_edgeImage (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) :
    edgePreimage (latticeShift n) (edgeImage (latticeShift n) b) = b := by
  rw [edgePreimage_latticeShift_eq h, edgeImage_latticeShift_eq h, translateLink_neg_translateLink]
theorem edgeImage_edgePreimage (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) :
    edgeImage (latticeShift n) (edgePreimage (latticeShift n) b) = b := by
  rw [edgePreimage_latticeShift_eq h, edgeImage_latticeShift_eq h, translateLink_translateLink_neg]
theorem edgePreimage_isPositivelyOriented (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    (edgePreimage (latticeShift n) b).IsPositivelyOriented := by
  rw [edgePreimage_latticeShift_eq h]
  exact translateLink_isPositivelyOriented h _ hb
theorem edgeImage_isPositivelyOriented (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    (edgeImage (latticeShift n) b).IsPositivelyOriented := by
  rw [edgeImage_latticeShift_eq h]
  exact translateLink_isPositivelyOriented h _ hb
theorem edgePreimage_opposite (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) :
    edgePreimage (latticeShift n) b.opposite = (edgePreimage (latticeShift n) b).opposite := by
  rw [edgePreimage_latticeShift_eq h, edgePreimage_latticeShift_eq h, translateLink_opposite]
theorem edgePreimage_initial (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) :
    (edgePreimage (latticeShift n) b).initial = vertexPreimage (latticeShift n) b.initial := by
  rw [edgePreimage_latticeShift_eq h]
  refine Subtype.ext ?_
  rw [coe_vertexPreimage_latticeShift h, sub_eq_add_neg, ← castVec_neg]
  rfl
theorem edgePreimage_terminal (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (b : InfiniteLattice.Link a) :
    (edgePreimage (latticeShift n) b).terminal = vertexPreimage (latticeShift n) b.terminal := by
  rw [edgePreimage_latticeShift_eq h]
  refine Subtype.ext ?_
  rw [coe_vertexPreimage_latticeShift h, sub_eq_add_neg, ← castVec_neg]
  rfl
theorem isometryOnTangent_of_isPositivelyOriented (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (U B : InfiniteLattice.Link a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) :
    isometryOnTangent (latticeShift n) U B b = B (edgePreimage (latticeShift n) b) := by
  simp only [isometryOnTangent, extendOddly, tangentEdgeValue, if_pos hb,
    if_pos (edgePreimage_isPositivelyOriented h n hb)]
theorem isometryOnTangent_eq_pushField (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (U : InfiniteLattice.Link a → ComplexMatrix2) {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms a) :
    isometryOnTangent (latticeShift n) U B = pushField (latticeShift n) B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact isometryOnTangent_of_isPositivelyOriented h n U B hb
  · have hr := opposite_isPositivelyOriented_of_not hb
    have e : isometryOnTangent (latticeShift n) U B b =
        -tangentEdgeValue U B (edgePreimage (latticeShift n) b.opposite) := by
      simp only [isometryOnTangent, extendOddly, if_neg hb]
    rw [e]
    simp only [tangentEdgeValue, if_pos (edgePreimage_isPositivelyOriented h n hr)]
    rw [edgePreimage_opposite h]
    change -B (edgePreimage (latticeShift n) b).opposite = B (edgePreimage _ b)
    rw [hB.2, neg_neg]
theorem pushField_mem_complexEdgeForms (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    {B : InfiniteLattice.Link a → ComplexMatrix2} (hB : B ∈ complexEdgeForms a) :
    pushField (latticeShift n) B ∈ complexEdgeForms a := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValues.pushField_mem <;> assumption
end Links
section BlockEvaluations
variable {L k : ℕ}
theorem meshAt_ne_zero (hL : 0 < L) (k j : ℕ) : meshAt L k j ≠ 0 :=
  zpow_ne_zero _ (Nat.cast_ne_zero.2 hL.ne')
theorem exists_int_mul_meshAt_eq_one (hL : 0 < L) {j : ℕ} (hj : j ≤ k) :
    ∃ m : ℤ, (m : ℝ) * meshAt L k j = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValues.exists_int_mul_meshAt_eq_one <;> assumption
theorem shiftEdge_val (hL : 0 < L) {j : ℕ} (hj : j ≤ k) (n : Fin 4 → ℤ)
    (b : PeriodicOperators.PosEdge L k j) :
    (shiftEdge n b).1 = edgeImage (latticeShift n) b.1 := by
  have h := exists_int_mul_meshAt_eq_one (k := k) hL hj
  exact Classical.epsilon_spec
    (p := fun b' : PeriodicOperators.PosEdge L k j => b'.1 = edgeImage (intShift n) b.1)
    ⟨⟨edgeImage (latticeShift n) b.1, edgeImage_isPositivelyOriented h n b.2⟩, rfl⟩
def vertexColourShift (hL : 0 < L) {i : ℕ} (hi : i ≤ k) (n : Fin 4 → ℤ) :
    (Fin 3 × Vertex L k i) ≃ (Fin 3 × Vertex L k i) where
  toFun := (colourVertices L k i).translate n
  invFun := (colourVertices L k i).translate (-n)
  left_inv p := by
    obtain ⟨c, x⟩ := p
    change (c, vertexImage (latticeShift (-n)) (vertexImage (latticeShift n) x)) = (c, x)
    rw [vertexImage_latticeShift_neg (exists_int_mul_meshAt_eq_one hL hi),
      vertexPreimage_vertexImage (exists_int_mul_meshAt_eq_one hL hi)]
  right_inv p := by
    obtain ⟨c, x⟩ := p
    change (c, vertexImage (latticeShift n) (vertexImage (latticeShift (-n)) x)) = (c, x)
    rw [vertexImage_latticeShift_neg (exists_int_mul_meshAt_eq_one hL hi),
      vertexImage_vertexPreimage (exists_int_mul_meshAt_eq_one hL hi)]
def edgeColourShift (hL : 0 < L) {i : ℕ} (hi : i ≤ k) (n : Fin 4 → ℤ) :
    (Fin 3 × PeriodicOperators.PosEdge L k i) ≃ (Fin 3 × PeriodicOperators.PosEdge L k i) where
  toFun := (colourEdges L k i).translate n
  invFun := (colourEdges L k i).translate (-n)
  left_inv p := by
    obtain ⟨c, b⟩ := p
    change (c, shiftEdge (-n) (shiftEdge n b)) = (c, b)
    refine congrArg _ (Subtype.ext ?_)
    rw [shiftEdge_val hL hi, shiftEdge_val hL hi,
      edgeImage_latticeShift_eq (exists_int_mul_meshAt_eq_one hL hi),
      edgeImage_latticeShift_eq (exists_int_mul_meshAt_eq_one hL hi),
      translateLink_neg_translateLink]
  right_inv p := by
    obtain ⟨c, b⟩ := p
    change (c, shiftEdge n (shiftEdge (-n) b)) = (c, b)
    refine congrArg _ (Subtype.ext ?_)
    rw [shiftEdge_val hL hi, shiftEdge_val hL hi,
      edgeImage_latticeShift_eq (exists_int_mul_meshAt_eq_one hL hi),
      edgeImage_latticeShift_eq (exists_int_mul_meshAt_eq_one hL hi),
      translateLink_translateLink_neg]
theorem vertexCoordinate_compatible (hL : 0 < L) {i : ℕ} (hi : i ≤ k) (n : Fin 4 → ℤ) :
    IsCompatibleRelabelling (vertexCoordinate (Vertex L k i)) (vertexColourShift hL hi n)
      (pushSiteFunction (latticeShift n)) where
  ofCoeffs_mem f := fun x _ => pauli_sum_mem_traceless _
  ofCoeffs_coeffs g hg := by
    funext x
    exact sum_pauliCoeff_smul (hg x (mem_univ _))
  coeffs_ofCoeffs f := by
    funext p
    exact pauliCoeff_sum (fun a => f (a, p.2)) p.1
  coeffs_act g := by
    funext p
    exact congrArg (fun y : Vertex L k i => pauliCoeff p.1 (g y))
      (vertexImage_latticeShift_neg (exists_int_mul_meshAt_eq_one hL hi) n (p.2 : Vertex L k i)).symm
  act_mem _ hg := fun x _ => hg _ (mem_univ _)
variable {j : ℕ}
theorem ofCoeffs_coeffs_of_mem (B : Edge L k j → ComplexMatrix2)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    (edgePauliCoordinates L k j).ofCoeffs ((edgePauliCoordinates L k j).coeffs B) = B := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofCoeffs_coeffs <;> assumption
theorem ofCoeffs_mem_complexEdgeForms (hL : 0 < L)
    (c : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) :
    (edgePauliCoordinates L k j).ofCoeffs c ∈ complexEdgeForms (meshAt L k j) := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValues.ofCoeffs_mem <;> assumption
theorem coeffs_ofCoeffs_edge (c : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) :
    (edgePauliCoordinates L k j).coeffs ((edgePauliCoordinates L k j).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValues.coeffs_ofCoeffs <;> assumption
theorem coeffs_isometryOnTangent (hL : 0 < L) (hj : j ≤ k) (n : Fin 4 → ℤ)
    (U B : Edge L k j → ComplexMatrix2) :
    (edgePauliCoordinates L k j).coeffs (isometryOnTangent (latticeShift n) U B) =
      (edgePauliCoordinates L k j).coeffs B ∘ (edgeColourShift hL hj n).symm := by
  have h := exists_int_mul_meshAt_eq_one (k := k) hL hj
  funext p
  obtain ⟨c, b, hb⟩ := p
  change pauliCoeff c (isometryOnTangent (latticeShift n) U B b) =
    pauliCoeff c (B (shiftEdge (-n) ⟨b, hb⟩).1)
  rw [isometryOnTangent_of_isPositivelyOriented h n U B hb, shiftEdge_val hL hj,
    edgeImage_latticeShift_eq h, edgePreimage_latticeShift_eq h]
theorem coeffs_pushField (hL : 0 < L) (hj : j ≤ k) (n : Fin 4 → ℤ)
    (B : Edge L k j → ComplexMatrix2) :
    (edgePauliCoordinates L k j).coeffs (pushField (latticeShift n) B) =
      (edgePauliCoordinates L k j).coeffs B ∘ (edgeColourShift hL hj n).symm := by
  have h := exists_int_mul_meshAt_eq_one (k := k) hL hj
  funext p
  obtain ⟨c, b, hb⟩ := p
  change pauliCoeff c (B (edgePreimage (latticeShift n) b)) =
    pauliCoeff c (B (shiftEdge (-n) ⟨b, hb⟩).1)
  rw [shiftEdge_val hL hj, edgeImage_latticeShift_eq h, edgePreimage_latticeShift_eq h]
theorem edgePauliCoordinates_compatible (hL : 0 < L) (hj : j ≤ k) (n : Fin 4 → ℤ) :
    IsCompatibleRelabelling (edgePauliCoordinates L k j) (edgeColourShift hL hj n)
      (pushField (latticeShift n)) where
  ofCoeffs_mem f := ofCoeffs_mem_complexEdgeForms hL f
  ofCoeffs_coeffs g hg := ofCoeffs_coeffs_of_mem g hg
  coeffs_ofCoeffs f := coeffs_ofCoeffs_edge f
  coeffs_act g := coeffs_pushField hL hj n g
  act_mem _ hg := pushField_mem_complexEdgeForms (exists_int_mul_meshAt_eq_one hL hj) n hg
end BlockEvaluations
section Maps
variable {L k : ℕ}
theorem kernel_eq_of_compatible {r r' : PauliComponentsOfSymmetricKernel} {σ : r.Index ≃ r.Index}
    {σ' : r'.Index ≃ r'.Index}
    {a : (r.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2}
    (h : IsCompatibleRelabelling r σ a)
    {m₁ m₂ : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hm : ∀ g ∈ r.space.complexSubmodule, r'.coeffs (m₂ (a g)) = r'.coeffs (m₁ g) ∘ σ'.symm)
    (G₁ : Represents (PauliComponentsOfSymmetricKernel.kernel r r' m₁) (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m₁))
    (G₂ : Represents (PauliComponentsOfSymmetricKernel.kernel r r' m₂) (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m₂))
    (i' : r'.Index) (i : r.Index) :
    PauliComponentsOfSymmetricKernel.kernel r r' m₂ (σ' i') (σ i) = PauliComponentsOfSymmetricKernel.kernel r r' m₁ i' i :=
  kernel_entries_eq_of_maps_related σ σ' G₁ G₂ (mapOnCoeffs_comp_symm h hm) i' i
variable (hL : 0 < L) (hLs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
  (n : Fin 4 → ℤ)
  (hTr : Tower.Translations.TranslationProperties)
  (hIso : CovariantSmoothingIsometryEquivariance)
  (hKer : ThreeMapKernels.Claim)
  (hDrift : IteratedDriftKernel.DriftKernelRepresents)
  {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
  (hU' : pushField (latticeShift n) U ∈ smallIterateFields L k)
include hTr hLs in
theorem latticeShift_isDistancePreserving : IsDistancePreserving (latticeShift n) :=
  ((hTr L hLs 0 0 le_rfl).2.2.2.1 n).1
include hTr hLs in
theorem latticeShift_mapsSublatticeOnto {i : ℕ} (hi : i ≤ k) :
    MapsSublatticeOnto (meshAt L k i) (latticeShift n) :=
  ((hTr L hLs k 0 (Nat.zero_le k)).2.2.2.1 n).2.1 i hi
include hTr hIso hLs hU in
theorem covDiff_latticeShift (g : Vertex L k 0 → ComplexMatrix2)
    (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) :
    covDiff (pushField (latticeShift n) U) (pushSiteFunction (latticeShift n) g) =
      isometryOnTangent (latticeShift n) U (covDiff U g) :=
  ((hIso L hLs k 0 (Nat.zero_le k) _ (latticeShift_isDistancePreserving hLs n hTr)
    (latticeShift_mapsSublatticeOnto hLs n hTr le_rfl) U hU).1 g hg).1
include hTr hIso hLs hU in
theorem iterAdjointCubeAverage_latticeShift (g : Vertex L k 0 → ComplexMatrix2)
    (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) :
    iterAdjointCubeAverage L k (pushField (latticeShift n) U) k
        (pushSiteFunction (latticeShift n) g) =
      pushSiteFunction (latticeShift n) (iterAdjointCubeAverage L k U k g) :=
  ((hIso L hLs k k le_rfl _ (latticeShift_isDistancePreserving hLs n hTr)
    (latticeShift_mapsSublatticeOnto hLs n hTr le_rfl) U hU).1 g hg).2
include hL hTr hIso hKer hLs hk hU hU' in
theorem covDiffKernel_latticeShift (i' : Fin 3 × PeriodicOperators.PosEdge L k 0)
    (i : Fin 3 × Vertex L k 0) :
    covDiffKernel L k 0 (pushField (latticeShift n) U)
        (edgeColourShift hL (Nat.zero_le k) n i') (vertexColourShift hL (Nat.zero_le k) n i) =
      covDiffKernel L k 0 U i' i :=
  kernel_eq_of_compatible (vertexCoordinate_compatible hL (Nat.zero_le k) n) (fun g hg => by
      rw [covDiff_latticeShift hLs n hTr hIso hU g fun x => hg x (mem_univ x)]
      exact coeffs_isometryOnTangent hL (Nat.zero_le k) n _ _)
    ((hKer L hLs k hk).2.2.1 U hU.1).represents ((hKer L hLs k hk).2.2.1 _ hU'.1).represents i' i
include hL hTr hIso hKer hLs hk hU hU' in
theorem iterAverageKernel_latticeShift (i' : Fin 3 × Vertex L k k) (i : Fin 3 × Vertex L k 0) :
    iterAverageKernel L k (pushField (latticeShift n) U)
        (vertexColourShift hL le_rfl n i') (vertexColourShift hL (Nat.zero_le k) n i) =
      iterAverageKernel L k U i' i :=
  kernel_eq_of_compatible (vertexCoordinate_compatible hL (Nat.zero_le k) n) (fun g hg => by
      rw [iterAdjointCubeAverage_latticeShift hLs n hTr hIso hU g fun x => hg x (mem_univ x)]
      exact (vertexCoordinate_compatible hL le_rfl n).coeffs_act _)
    ((hKer L hLs k hk).2.2.2.2 U hU).2.represents ((hKer L hLs k hk).2.2.2.2 _ hU').2.represents
    i' i
include hL hTr hIso hKer hLs hk hU hU' in
theorem iterCovariantKernel_latticeShift (i' : Fin 3 × PeriodicOperators.PosEdge L k k)
    (i : Fin 3 × PeriodicOperators.PosEdge L k 0) :
    iterCovariantKernel L k (pushField (latticeShift n) U)
        (edgeColourShift hL le_rfl n i') (edgeColourShift hL (Nat.zero_le k) n i) =
      iterCovariantKernel L k U i' i :=
  kernel_eq_of_compatible (edgePauliCoordinates_compatible hL (Nat.zero_le k) n) (fun g hg => by
      have e := ((hIso L hLs k k le_rfl _ (latticeShift_isDistancePreserving hLs n hTr)
        (latticeShift_mapsSublatticeOnto hLs n hTr le_rfl) U hU).2 g hg).2.1
      rw [isometryOnTangent_eq_pushField (exists_int_mul_meshAt_eq_one hL (Nat.zero_le k)) n U hg]
        at e
      rw [e]
      exact coeffs_isometryOnTangent hL le_rfl n _ _)
    ((hKer L hLs k hk).2.2.2.2 U hU).1.represents ((hKer L hLs k hk).2.2.2.2 _ hU').1.represents
    i' i
include hL hTr hIso hDrift hLs hk hU hU' in
theorem driftKernel_latticeShift (i' : Fin 3 × Vertex L k k)
    (i : Fin 3 × PeriodicOperators.PosEdge L k 0) :
    (edgePauliCoordinates L k 0).kernel (vertexCoordinate (Vertex L k k))
        (iterContourLogDrift L k (pushField (latticeShift n) U) k)
        (vertexColourShift hL le_rfl n i') (edgeColourShift hL (Nat.zero_le k) n i) =
      (edgePauliCoordinates L k 0).kernel (vertexCoordinate (Vertex L k k))
        (iterContourLogDrift L k U k) i' i :=
  kernel_eq_of_compatible (edgePauliCoordinates_compatible hL (Nat.zero_le k) n) (fun g hg => by
      have e := ((hIso L hLs k k le_rfl _ (latticeShift_isDistancePreserving hLs n hTr)
        (latticeShift_mapsSublatticeOnto hLs n hTr le_rfl) U hU).2 g hg).2.2
      rw [isometryOnTangent_eq_pushField (exists_int_mul_meshAt_eq_one hL (Nat.zero_le k)) n U hg]
        at e
      rw [e]
      exact (vertexCoordinate_compatible hL le_rfl n).coeffs_act _)
    (hDrift L hLs k hk U hU) (hDrift L hLs k hk _ hU') i' i
include hL hTr hIso hKer hLs hk hU hU' in
theorem covDiffTranspose_latticeShift (g : Edge L k 0 → ComplexMatrix2)
    (hg : g ∈ complexEdgeForms (meshAt L k 0)) :
    covDiffTranspose L k (pushField (latticeShift n) U) (isometryOnTangent (latticeShift n) U g) =
      pushSiteFunction (latticeShift n) (covDiffTranspose L k U g) := by
  rw [isometryOnTangent_eq_pushField (exists_int_mul_meshAt_eq_one hL (Nat.zero_le k)) n U hg]
  exact transposeOfValues_act (vertexCoordinate_compatible hL (Nat.zero_le k) n)
    (edgePauliCoordinates_compatible hL (Nat.zero_le k) n)
    (fun g hg => by
      rw [covDiff_latticeShift hLs n hTr hIso hU g fun x => hg x (mem_univ x)]
      exact coeffs_isometryOnTangent hL (Nat.zero_le k) n _ _)
    ((hKer L hLs k hk).2.2.1 U hU.1).represents ((hKer L hLs k hk).2.2.1 _ hU'.1).represents
    ((hKer L hLs k hk).2.2.1 U hU.1).swap_represents
    ((hKer L hLs k hk).2.2.1 _ hU'.1).swap_represents hg
include hL hTr hIso hKer hLs hk hU hU' in
theorem iterAverageTranspose_latticeShift (g : Vertex L k k → ComplexMatrix2)
    (hg : ∀ y, g y ∈ ComplexMatrix2.traceless) :
    iterAverageTranspose L k (pushField (latticeShift n) U) (pushSiteFunction (latticeShift n) g) =
      pushSiteFunction (latticeShift n) (iterAverageTranspose L k U g) :=
  transposeOfValues_act (vertexCoordinate_compatible hL (Nat.zero_le k) n)
    (vertexCoordinate_compatible hL le_rfl n)
    (fun g hg => by
      rw [iterAdjointCubeAverage_latticeShift hLs n hTr hIso hU g fun x => hg x (mem_univ x)]
      exact (vertexCoordinate_compatible hL le_rfl n).coeffs_act _)
    ((hKer L hLs k hk).2.2.2.2 U hU).2.represents ((hKer L hLs k hk).2.2.2.2 _ hU').2.represents
    ((hKer L hLs k hk).2.2.2.2 U hU).2.swap_represents
    ((hKer L hLs k hk).2.2.2.2 _ hU').2.swap_represents (fun y _ => hg y)
end Maps
section Iterates
variable {L k : ℕ} (hLs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (n : Fin 4 → ℤ)
  (hTr : Tower.Translations.TranslationProperties)
  (hComm : ComplexSmoothingCommutesWithIntShift)
  (hForm : LevelwiseMeans.LevelwiseMeansHold)
  {W : Edge L k 0 → ComplexMatrix2} (hW : W ∈ smallIterateFields L k)
include hLs hComm hW in
theorem complexIter_pushField : ∀ j ≤ k,
    complexIter L k j (pushField (latticeShift n) W) =
      pushField (latticeShift n) (complexIter L k j W) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hj' : j < k := by omega
    simp only [complexIter]
    rw [ih hj'.le]
    exact (hComm L hLs k j hj' n _ (hW.2 j hj')).2.2.2
include hLs hTr hComm hW in
theorem pushField_mem_smallIterateFields :
    pushField (latticeShift n) W ∈ smallIterateFields L k := by
  refine ⟨((hTr L hLs k 0 (Nat.zero_le k)).2.2.2.2.1.2.2.1 _
      (latticeShift_isDistancePreserving hLs n hTr)
      (latticeShift_mapsSublatticeOnto hLs n hTr (Nat.zero_le k)) W hW.1).1,
    fun j hj => ?_⟩
  rw [complexIter_pushField hLs n hComm hW j hj.le]
  exact (hComm L hLs k j hj n _ (hW.2 j hj)).1
include hLs hk hComm hForm hW in
theorem levelwiseMean_of_mem_smallIterateFields {i : ℕ} (hi : i ≤ k) (c : Edge L k i) :
    LevelwiseMeans.Unbounded.levelwiseMean W i c = some (complexIter L k i W c) := by
  refine (hForm L hLs k hk).2.sequence_is_levelwise k le_rfl (fun i => complexIter L k i W)
    ⟨fun i hi => ?_, fun i hi b => (hW.2 i hi).2 b, fun i _ c _ => rfl⟩ i hi c
  cases i with
  | zero => exact hW.1
  | succ i => exact (hComm L hLs k i (by omega) 0 _ (hW.2 i (by omega))).2.1
include hLs hk hComm hForm hW in
theorem isDefinedAt_of_mem_smallIterateFields (c : Edge L k k) : IsDefinedAt W k c := by
  change (LevelwiseMeans.Unbounded.levelwiseMean W k c).isSome
  rw [levelwiseMean_of_mem_smallIterateFields hLs hk hComm hForm hW le_rfl]
  rfl
include hLs hk hComm hForm hW in
theorem iterMean_of_mem_smallIterateFields (c : Edge L k k) :
    iterMean W k c = complexIter L k k W c := by
  change (LevelwiseMeans.Unbounded.levelwiseMean W k c).getD 1 = _
  rw [levelwiseMean_of_mem_smallIterateFields hLs hk hComm hForm hW le_rfl]
  rfl
include hLs hk hTr hComm hForm hW in
theorem iterMean_pushField (hL : 0 < L) (c : Edge L k k) :
    iterMean (pushField (latticeShift n) W) k (edgeImage (latticeShift n) c) = iterMean W k c := by
  rw [iterMean_of_mem_smallIterateFields hLs hk hComm hForm
      (pushField_mem_smallIterateFields hLs n hTr hComm hW),
    iterMean_of_mem_smallIterateFields hLs hk hComm hForm hW,
    complexIter_pushField hLs n hComm hW k le_rfl]
  change complexIter L k k W (edgePreimage _ (edgeImage _ c)) = _
  rw [edgePreimage_edgeImage (exists_int_mul_meshAt_eq_one hL le_rfl)]
end Iterates
section Exponentials
variable {a : ℝ}
theorem expTwist_pushField (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (U B : InfiniteLattice.Link a → ComplexMatrix2) :
    expTwist (isometryOnTangent (latticeShift n) U B) (pushField (latticeShift n) U) =
      pushField (latticeShift n) (expTwist B U) := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · have hb' := edgePreimage_isPositivelyOriented h n hb
    change (open Classical in if b.IsPositivelyOriented then
        ComplexMatrix2.matExp (Complex.I • isometryOnTangent (latticeShift n) U B b) *
          U (edgePreimage (latticeShift n) b) else _) =
      (open Classical in if (edgePreimage (latticeShift n) b).IsPositivelyOriented then _ else _)
    rw [if_pos hb, if_pos hb', isometryOnTangent_of_isPositivelyOriented h n U B hb]
  · have hr := opposite_isPositivelyOriented_of_not hb
    have hb' : ¬(edgePreimage (latticeShift n) b).IsPositivelyOriented := fun hp => hb (by
      have := edgeImage_isPositivelyOriented h n hp
      rwa [edgeImage_edgePreimage h] at this)
    change (open Classical in if b.IsPositivelyOriented then _ else
        (ComplexMatrix2.matExp (Complex.I • isometryOnTangent (latticeShift n) U B b.opposite) *
          U (edgePreimage (latticeShift n) b.opposite))⁻¹) =
      (open Classical in if (edgePreimage (latticeShift n) b).IsPositivelyOriented then _ else
        (ComplexMatrix2.matExp (Complex.I • B (edgePreimage (latticeShift n) b).opposite) *
          U (edgePreimage (latticeShift n) b).opposite)⁻¹)
    rw [if_neg hb, if_neg hb', isometryOnTangent_of_isPositivelyOriented h n U B hr,
      edgePreimage_opposite h]
theorem operatorNorm_matExp_mul_matExp_sub_one_le (hE : ComplexMatrix2.ExpLogEstimates)
    (X Y : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp X * ComplexMatrix2.matExp Y - 1) ≤
      Real.exp (ComplexMatrix2.operatorNorm X + ComplexMatrix2.operatorNorm Y) - 1 := by
  have h₁ := hE.2.2.1 (ComplexMatrix2.matExp X) Y
  have h₂ := (hE.1 X).2
  have h₃ : (1 + ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp X - 1)) *
        Real.exp (ComplexMatrix2.operatorNorm Y) ≤
      Real.exp (ComplexMatrix2.operatorNorm X) * Real.exp (ComplexMatrix2.operatorNorm Y) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  rw [Real.exp_add]
  linarith
theorem expTwist_isFieldIn (ha : a ≠ 0) (hE : ComplexMatrix2.ExpLogEstimates)
    {B U : InfiniteLattice.Link a → ComplexMatrix2} (hB : B ∈ complexEdgeForms a)
    (hU : IsFieldIn PeriodicLattice.complexGaugeGroup U) :
    IsFieldIn PeriodicLattice.complexGaugeGroup (expTwist B U) := by
  have hdet : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • B b) * U b).det = 1 := fun b hb => by
    have h₁ : (ComplexMatrix2.matExp (Complex.I • B b)).det = 1 := by
      rw [hE.2.2.2.2.2.1]
      have : Matrix.trace (B b) = 0 := hB.1 b hb
      simp [ComplexMatrix2.fullTrace, Matrix.trace_smul, this]
    have h₂ : (U b).det = 1 := hU.1 b
    rw [Matrix.det_mul, h₁, h₂, one_mul]
  have pos : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
      expTwist B U b = ComplexMatrix2.matExp (Complex.I • B b) * U b := fun b hb => by
    simp only [expTwist, if_pos hb]
  have neg : ∀ b : InfiniteLattice.Link a, ¬b.IsPositivelyOriented →
      expTwist B U b = (ComplexMatrix2.matExp (Complex.I • B b.opposite) * U b.opposite)⁻¹ :=
    fun b hb => by
      simp only [expTwist, if_neg hb]
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [pos b hb]
      exact hdet b hb
    · rw [neg b hb]
      change Matrix.det _ = 1
      rw [Matrix.det_nonsing_inv, hdet _ (opposite_isPositivelyOriented_of_not hb)]
      simp
  · by_cases hb : b.IsPositivelyOriented
    · rw [neg _ (not_opposite_isPositivelyOriented ha hb), pos b hb]
      rfl
    · rw [pos _ (opposite_isPositivelyOriented_of_not hb), neg b hb,
        Matrix.nonsing_inv_nonsing_inv]
      rw [hdet _ (opposite_isPositivelyOriented_of_not hb)]
      exact isUnit_one
end Exponentials
section Near
variable {L k : ℕ}
theorem exists_expTwist_mem_smallIterateFields (hE : ComplexMatrix2.ExpLogEstimates)
    (hF : FieldValues.FieldsAndValuesClaim) (hL : 0 < L) {υ₀ : ℝ}
    (hW : ∀ W ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (W b - 1) < υ₀) → W ∈ smallIterateFields L k)
    {f : (fieldPeriodicData L k hL).Carrier → ℂ} {r : ℝ} (hr : ∀ κ, ‖f κ‖ ≤ r)
    (hlt : Real.sqrt 6 * r < Real.log (1 + υ₀)) (hυ : 0 < υ₀)
    (hU : FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈
      fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) :
    ∃ ς : ℝ, 0 < ς ∧ ∀ B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)),
      GroupLieProduct.supNorm B < ς →
        expTwist B (FieldValueFunctions.gaugeFieldOfCoeffs hL f) ∈ smallIterateFields L k := by
  obtain ⟨ζ, rfl⟩ := (hF L hL k).2.1 f
  have hA := fun b => (hF L hL k).2.2.2 ζ r hr b
  rw [((hF L hL k).1 ζ).2.2.2.2.2] at hU ⊢
  refine ⟨Real.log (1 + υ₀) - Real.sqrt 6 * r, by linarith, fun B hB hn => ?_⟩
  obtain ⟨hBf, C, hC⟩ := hB
  have hBb : ∀ b, ComplexMatrix2.operatorNorm (B b) ≤ GroupLieProduct.supNorm B := fun b =>
    le_ciSup (f := fun b => ComplexMatrix2.operatorNorm (B b)) ⟨C, by rintro _ ⟨b, rfl⟩; exact hC b⟩ b
  have lim : ∀ x y : ℝ, x ≤ GroupLieProduct.supNorm B → y ≤ Real.sqrt 6 * r →
      Real.exp (x + y) - 1 < υ₀ := fun x y hx hy => by
    have e : Real.exp (Real.log (1 + υ₀)) = 1 + υ₀ := Real.exp_log (by linarith)
    have := Real.exp_lt_exp.2 (show x + y < Real.log (1 + υ₀) by linarith)
    linarith
  have normI : ∀ X : ComplexMatrix2,
      ComplexMatrix2.operatorNorm (Complex.I • X) = ComplexMatrix2.operatorNorm X := fun X => by
    simp [ComplexMatrix2.operatorNorm, norm_smul]
  refine hW _ (expTwist_isFieldIn (meshAt_ne_zero hL k 0) hE hBf hU) fun b => ?_
  by_cases hb : b.IsPositivelyOriented
  · have e : expTwist B (ζ.gaugeField) b =
        ComplexMatrix2.matExp (Complex.I • B b) *
          ComplexMatrix2.matExp (Complex.I • (ζ.1 : Edge L k 0 → ComplexMatrix2) b) := by
      have e₁ : ζ.gaugeField b =
          ComplexMatrix2.matExp (Complex.I • (ζ.1 : Edge L k 0 → ComplexMatrix2) b) *
            (1 : Edge L k 0 → ComplexMatrix2) b := by
        simp only [FullField.gaugeField, expForm, expTwist, if_pos hb]
      simp only [expTwist, if_pos hb]
      rw [e₁]
      change _ * (_ * (1 : ComplexMatrix2)) = _
      rw [mul_one]
    rw [e]
    refine (operatorNorm_matExp_mul_matExp_sub_one_le hE _ _).trans_lt (lim _ _ ?_ ?_)
    · rw [normI]; exact hBb b
    · rw [normI]; exact hA b
  · have hr' := opposite_isPositivelyOriented_of_not hb
    have e : expTwist B (ζ.gaugeField) b =
        ComplexMatrix2.matExp (-(Complex.I • (ζ.1 : Edge L k 0 → ComplexMatrix2) b.opposite)) *
          ComplexMatrix2.matExp (-(Complex.I • B b.opposite)) := by
      have e₁ : ζ.gaugeField b.opposite =
          ComplexMatrix2.matExp (Complex.I • (ζ.1 : Edge L k 0 → ComplexMatrix2) b.opposite) *
            (1 : Edge L k 0 → ComplexMatrix2) b.opposite := by
        simp only [FullField.gaugeField, expForm, expTwist, if_pos hr']
      simp only [expTwist, if_neg hb]
      rw [e₁]
      change (_ * (_ * (1 : ComplexMatrix2)))⁻¹ = _
      rw [mul_one, Matrix.mul_inv_rev, ComplexMatrix2.matExp, ComplexMatrix2.matExp,
        ComplexMatrix2.matExp, ComplexMatrix2.matExp, Matrix.exp_neg, Matrix.exp_neg]
    rw [e]
    refine (operatorNorm_matExp_mul_matExp_sub_one_le hE _ _).trans_lt ?_
    rw [add_comm]
    refine lim _ _ ?_ ?_
    · rw [ComplexMatrix2.operatorNorm, norm_neg, ← ComplexMatrix2.operatorNorm, normI]
      exact hBb _
    · rw [ComplexMatrix2.operatorNorm, norm_neg, ← ComplexMatrix2.operatorNorm, normI]
      exact hA _
end Near
section Term
variable {β γ : Type} {P : Submodule ℂ (β → ComplexMatrix2)}
def pullbackBilinear (q : BoundedBilinear P γ)
    (t : boundedSubmodule P →ₗ[ℂ] boundedSubmodule P) (p : γ → γ) : BoundedBilinear P γ :=
  LinearMap.mk₂ ℂ (fun B B' c => q (t B) (t B') (p c))
    (fun B₁ B₂ B' => by funext c; simp)
    (fun z B B' => by funext c; simp)
    (fun B B₁ B₂ => by funext c; simp)
    (fun z B B' => by funext c; simp)
theorem quadraticTerm_eq_pullbackBilinear {v₁ v₂ : γ → (β → ComplexMatrix2) → ComplexMatrix2}
    {Q₁ Q₂ : (β → ComplexMatrix2) → γ → ComplexMatrix2}
    (t : boundedSubmodule P →ₗ[ℂ] boundedSubmodule P) (p : γ → γ)
    (E₁ : HasUniqueQuadraticTerm P v₁ Q₁) (E₂ : HasUniqueQuadraticTerm P v₂ Q₂)
    (hn : ∀ B : boundedSubmodule P, GroupLieProduct.supNorm (t B : β → ComplexMatrix2) =
      GroupLieProduct.supNorm (B : β → ComplexMatrix2))
    (hv : ∃ ς : ℝ, 0 < ς ∧ ∀ B : boundedSubmodule P,
      GroupLieProduct.supNorm (B : β → ComplexMatrix2) < ς → ∀ c, v₂ (p c) (t B) = v₁ c B)
    (hQ : ∀ (B : boundedSubmodule P) (c : γ), Q₂ (t B) (p c) = Q₁ B c) :
    quadraticTerm P v₁ Q₁ = pullbackBilinear (quadraticTerm P v₂ Q₂) t p := by
  obtain ⟨ς, hς, hv⟩ := hv
  have hq : Tower.AsDifferentials.IsQuadraticExpansion P v₁ Q₁ (pullbackBilinear (quadraticTerm P v₂ Q₂) t p) := by
    refine ⟨fun B B' => ?_, fun c => ?_⟩
    · funext c
      exact congrFun (E₂.2.1.1 (t B) (t B')) (p c)
    · obtain ⟨K, δ, hδ, h⟩ := E₂.2.1.2 (p c)
      refine ⟨K, min δ ς, lt_min hδ hς, fun B hB => ?_⟩
      have h₁ := h (t B) (by rw [hn]; exact hB.trans_le (min_le_left _ _))
      rw [hv B (hB.trans_le (min_le_right _ _)) c, hQ, hn] at h₁
      exact h₁
  exact E₁.1.unique E₁.2.1 hq
end Term
section QuadraticTermOfTheTower
variable {L k : ℕ}
theorem supNorm_pushField (hL : 0 < L) (n : Fin 4 → ℤ) (B : Edge L k 0 → ComplexMatrix2) :
    GroupLieProduct.supNorm (pushField (latticeShift n) B) = GroupLieProduct.supNorm B := by
  have h := exists_int_mul_meshAt_eq_one (k := k) hL (Nat.zero_le k)
  exact Function.Surjective.iSup_comp (f := edgePreimage (latticeShift n))
    (fun b => ⟨edgeImage (latticeShift n) b, edgePreimage_edgeImage h n b⟩)
    (fun b => ComplexMatrix2.operatorNorm (B b))
def boundedShift (hL : 0 < L) (n : Fin 4 → ℤ) :
    boundedSubmodule (complexEdgeForms (meshAt L k 0)) →ₗ[ℂ]
      boundedSubmodule (complexEdgeForms (meshAt L k 0)) where
  toFun B := ⟨pushField (latticeShift n) (B : Edge L k 0 → ComplexMatrix2), by
    obtain ⟨h₁, C, hC⟩ := B.2
    exact ⟨pushField_mem_complexEdgeForms (exists_int_mul_meshAt_eq_one hL (Nat.zero_le k)) n h₁,
      C, fun b => hC _⟩⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
variable (hL : 0 < L) (hLs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
  (n : Fin 4 → ℤ)
  (hTr : Tower.Translations.TranslationProperties)
  (hIso : CovariantSmoothingIsometryEquivariance)
  (hComm : ComplexSmoothingCommutesWithIntShift)
  (hForm : LevelwiseMeans.LevelwiseMeansHold)
  (hDiff : _root_.YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
  {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
  (hς : ∃ ς : ℝ, 0 < ς ∧ ∀ B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)),
    GroupLieProduct.supNorm B < ς → expTwist B U ∈ smallIterateFields L k)
include hLs hk hTr hComm hForm hU hς in
theorem topLogRatio_boundedShift : ∃ ς : ℝ, 0 < ς ∧
    ∀ B : boundedSubmodule (complexEdgeForms (meshAt L k 0)),
      GroupLieProduct.supNorm (B : Edge L k 0 → ComplexMatrix2) < ς →
      ∀ c : PositiveEdge (meshAt L k k),
        topLogRatio L k (pushField (latticeShift n) U) (shiftEdge n c)
            (boundedShift hL n B) = topLogRatio L k U c B := by
  obtain ⟨ς, hς₀, hς⟩ := hς
  refine ⟨ς, hς₀, fun B hB c => ?_⟩
  have h₀ := exists_int_mul_meshAt_eq_one (k := k) hL (Nat.zero_le k)
  have e₁ : iterMean (expTwist (boundedShift hL n B : Edge L k 0 → ComplexMatrix2)
      (pushField (latticeShift n) U)) k (shiftEdge n c).1 =
      iterMean (expTwist (B : Edge L k 0 → ComplexMatrix2) U) k c.1 := by
    have e : (boundedShift hL n B : Edge L k 0 → ComplexMatrix2) =
        isometryOnTangent (latticeShift n) U (B : Edge L k 0 → ComplexMatrix2) := by
      obtain ⟨h₁, -⟩ := B.2
      exact (isometryOnTangent_eq_pushField h₀ n U h₁).symm
    rw [e, expTwist_pushField h₀, shiftEdge_val hL le_rfl]
    exact iterMean_pushField hLs hk n hTr hComm hForm (hς _ B.2 hB) hL _
  have e₂ : iterMean (pushField (latticeShift n) U) k (shiftEdge n c).1 = iterMean U k c.1 := by
    rw [shiftEdge_val hL le_rfl]
    exact iterMean_pushField hLs hk n hTr hComm hForm hU hL _
  simp only [topLogRatio, FullSpace.AsDifferentials.iterLogRatio,
    FullSpace.AsDifferentials.iterRatio]
  rw [e₁, e₂]
include hLs hTr hIso hU in
theorem topDeriv_boundedShift (B : boundedSubmodule (complexEdgeForms (meshAt L k 0)))
    (c : PositiveEdge (meshAt L k k)) :
    topDeriv L k (pushField (latticeShift n) U) (boundedShift hL n B) (shiftEdge n c) =
      topDeriv L k U B c := by
  have h₀ := exists_int_mul_meshAt_eq_one (k := k) hL (Nat.zero_le k)
  have hk' := exists_int_mul_meshAt_eq_one (k := k) hL le_rfl
  obtain ⟨h₁, -⟩ := B.2
  have e := ((hIso L hLs k k le_rfl _ (latticeShift_isDistancePreserving hLs n hTr)
    (latticeShift_mapsSublatticeOnto hLs n hTr le_rfl) U hU).2 _ h₁).1
  rw [isometryOnTangent_eq_pushField h₀ n U h₁] at e
  change complexIterDeriv L k k _ (pushField (latticeShift n) _)
    (shiftEdge n c).1 = complexIterDeriv L k k U _ c.1
  rw [e, shiftEdge_val hL le_rfl,
    isometryOnTangent_of_isPositivelyOriented hk' n _ _
      (edgeImage_isPositivelyOriented hk' n c.2),
    edgePreimage_edgeImage hk']
include hL hLs hk hTr hIso hComm hForm hDiff hU hς in
theorem complexQuadraticTerm_latticeShift
    (hU' : pushField (latticeShift n) U ∈ smallIterateFields L k)
    {B B' : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)))
    (hB' : B' ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)))
    (c c' : PositiveEdge (meshAt L k k))
    (hc : c'.1 = edgeImage (latticeShift n) c.1) :
    complexQuadraticTerm L k (pushField (latticeShift n) U)
        (isometryOnTangent (latticeShift n) U B) (isometryOnTangent (latticeShift n) U B') c' =
      complexQuadraticTerm L k U B B' c := by
  have h₀ := exists_int_mul_meshAt_eq_one (k := k) hL (Nat.zero_le k)
  have E₁ := (hDiff L hLs k hk).2.2 U hU
  have E₂ := (hDiff L hLs k hk).2.2 _ hU'
  have T := quadraticTerm_eq_pullbackBilinear (boundedShift hL n) (shiftEdge n) E₁ E₂
    (fun B => supNorm_pushField hL n _)
    (topLogRatio_boundedShift hL hLs hk n hTr hComm hForm hU hς)
    (topDeriv_boundedShift hL hLs n hTr hIso hU)
  obtain ⟨h₁, -⟩ := id hB
  obtain ⟨h₂, -⟩ := id hB'
  rw [isometryOnTangent_eq_pushField h₀ n U h₁, isometryOnTangent_eq_pushField h₀ n U h₂]
  have hs := (boundedShift hL n ⟨B, hB⟩).2
  have hs' := (boundedShift hL n ⟨B', hB'⟩).2
  have hp : shiftEdge n c = c' := Subtype.ext ((shiftEdge_val hL le_rfl n c).trans hc.symm)
  simp only [complexQuadraticTerm, quadraticTermAt]
  rw [dif_pos ⟨hs, hs'⟩, dif_pos ⟨hB, hB'⟩, T, ← hp]
  rfl
end QuadraticTermOfTheTower
section EdgeByEdge
variable {a : ℝ}
theorem extendOddly_congr {f g : InfiniteLattice.Link a → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → f b = g b) : extendOddly f = extendOddly g := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_congr <;> assumption
theorem levelBracketTerm_latticeShift (h : ∃ m : ℤ, (m : ℝ) * a = 1) (n : Fin 4 → ℤ)
    (U : InfiniteLattice.Link a → ComplexMatrix2) (l : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) :
    levelBracketTerm (pushField (latticeShift n) U)
        (pushSiteFunction (latticeShift n) l) (isometryOnTangent (latticeShift n) U B) =
      isometryOnTangent (latticeShift n) U (levelBracketTerm U l B) := by
  refine extendOddly_congr fun b hb => ?_
  have hb' := edgePreimage_isPositivelyOriented h n hb
  rw [isometryOnTangent_of_isPositivelyOriented h n U B hb]
  simp only [tangentEdgeValue, if_pos hb', levelBracketTerm, extendOddly]
  rw [edgePreimage_initial h, edgePreimage_terminal h]
  rfl
end EdgeByEdge
section ZeroExtension
variable {L k : ℕ}
theorem zeroExtend_latticeShift (hL : 0 < L) (n : Fin 4 → ℤ) (g : Vertex L k k → ComplexMatrix2) :
    (zeroExtend (pushSiteFunction (latticeShift n) g) : Vertex L k 0 → ComplexMatrix2) =
      pushSiteFunction (latticeShift n) (zeroExtend g) := by
  have hk := exists_int_mul_meshAt_eq_one (k := k) hL le_rfl
  have h₀ := exists_int_mul_meshAt_eq_one (k := k) hL (Nat.zero_le k)
  funext x
  have hiff : (∃ y : Vertex L k k, (y : AmbientSpace) = (x : AmbientSpace)) ↔
      ∃ y : Vertex L k k, (y : AmbientSpace) =
        (vertexPreimage (latticeShift n) x : Vertex L k 0) := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨vertexPreimage (latticeShift n) y, ?_⟩
      rw [coe_vertexPreimage_latticeShift hk, coe_vertexPreimage_latticeShift h₀, hy]
    · rintro ⟨y, hy⟩
      refine ⟨vertexImage (latticeShift n) y, ?_⟩
      rw [coe_vertexImage_latticeShift hk, hy, coe_vertexPreimage_latticeShift h₀, sub_add_cancel]
  simp only [zeroExtend, pushSiteFunction]
  by_cases h : ∃ y : Vertex L k k, (y : AmbientSpace) = (x : AmbientSpace)
  · have h' := hiff.1 h
    rw [dif_pos h, dif_pos h']
    refine congrArg g (Subtype.ext ?_)
    rw [coe_vertexPreimage_latticeShift hk, h.choose_spec, h'.choose_spec,
      coe_vertexPreimage_latticeShift h₀]
  · have h' := fun hh => h (hiff.2 hh)
    rw [dif_neg h, dif_neg h']
end ZeroExtension
section Assembly
variable {L k : ℕ}
theorem gaugeFieldOfCoeffs_shiftField (hF : FieldValues.FieldsAndValuesClaim) (hL : 0 < L)
    (n : Fin 4 → ℤ) (f : (fieldPeriodicData L k hL).Carrier → ℂ) :
    FieldValueFunctions.gaugeFieldOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f) =
      pushField (latticeShift n) (FieldValueFunctions.gaugeFieldOfCoeffs hL f) := by
  have h₀ := exists_int_mul_meshAt_eq_one (k := k) hL (Nat.zero_le k)
  obtain ⟨ζ, rfl⟩ := (hF L hL k).2.1 f
  obtain ⟨ζ', ht, hc⟩ := (hF L hL k).2.2.1 n ζ
  rw [← hc, ((hF L hL k).1 ζ').2.2.2.2.2, ((hF L hL k).1 ζ).2.2.2.2.2]
  have e := expTwist_pushField h₀ n (1 : Edge L k 0 → ComplexMatrix2)
    (ζ.1 : Edge L k 0 → ComplexMatrix2)
  rw [isometryOnTangent_eq_pushField h₀ n _ ζ.1.2] at e
  change expTwist (ζ'.1 : Edge L k 0 → ComplexMatrix2) 1 = _
  rw [ht.1]
  exact e
theorem shiftCommutesAt (hL : 0 < L) (hLs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (n : Fin 4 → ℤ)
    (hTr : Tower.Translations.TranslationProperties)
    (hIso : CovariantSmoothingIsometryEquivariance)
    (hKer : ThreeMapKernels.Claim)
    (hComm : ComplexSmoothingCommutesWithIntShift)
    (hForm : LevelwiseMeans.LevelwiseMeansHold)
    (hDiff : _root_.YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
    (hς : ∃ ς : ℝ, 0 < ς ∧ ∀ B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)),
      GroupLieProduct.supNorm B < ς → expTwist B U ∈ smallIterateFields L k) :
    ShiftCommutesAt L k U n := by
  have hU' := pushField_mem_smallIterateFields hLs n hTr hComm hU
  have h₀ := exists_int_mul_meshAt_eq_one (k := k) hL (Nat.zero_le k)
  refine ⟨covDiffTranspose_latticeShift hL hLs hk n hTr hIso hKer hU hU',
    iterAverageTranspose_latticeShift hL hLs hk n hTr hIso hKer hU hU', ?_,
    fun B hB B' hB' c c' hc => complexQuadraticTerm_latticeShift hL hLs hk n hTr hIso hComm hForm
      hDiff hU hς hU' hB hB' c c' hc,
    fun l _ B _ => levelBracketTerm_latticeShift h₀ n U l B,
    fun g _ => zeroExtend_latticeShift hL n g⟩
  obtain ⟨ς, hς₀, hς⟩ := hς
  refine ⟨ς, hς₀, fun B hB hn c _ => ?_⟩
  have hW := hς B hB hn
  have hW' := pushField_mem_smallIterateFields hLs n hTr hComm hW
  rw [expTwist_pushField h₀]
  exact ⟨isDefinedAt_of_mem_smallIterateFields hLs hk hComm hForm hW c,
    isDefinedAt_of_mem_smallIterateFields hLs hk hComm hForm hW' _,
    iterMean_pushField hLs hk n hTr hComm hForm hW hL c⟩
theorem kernelsShiftCovariant (hF : FieldValues.FieldsAndValuesClaim) (hL : 0 < L)
    (hLs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (n : Fin 4 → ℤ)
    (hTr : Tower.Translations.TranslationProperties)
    (hIso : CovariantSmoothingIsometryEquivariance)
    (hKer : ThreeMapKernels.Claim)
    (hDrift : IteratedDriftKernel.DriftKernelRepresents)
    {f : (fieldPeriodicData L k hL).Carrier → ℂ}
    (hU : FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈ smallIterateFields L k)
    (hU' : pushField (latticeShift n) (FieldValueFunctions.gaugeFieldOfCoeffs hL f) ∈
      smallIterateFields L k) :
    KernelsShiftCovariant L k hL f n := by
  have hT := gaugeFieldOfCoeffs_shiftField hF hL n f
  refine ⟨fun i' i => ?_, fun i' i => ?_, fun i' i => ?_, fun i' i => ?_⟩
  · change covDiffKernel L k 0
      (FieldValueFunctions.gaugeFieldOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f)) _ _ = _
    rw [hT]
    exact covDiffKernel_latticeShift hL hLs hk n hTr hIso hKer hU hU' i' i
  · change iterAverageKernel L k
      (FieldValueFunctions.gaugeFieldOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f)) _ _ = _
    rw [hT]
    exact iterAverageKernel_latticeShift hL hLs hk n hTr hIso hKer hU hU' i' i
  · change (edgePauliCoordinates L k 0).kernel (vertexCoordinate (Vertex L k k))
      (iterContourLogDrift L k
        (FieldValueFunctions.gaugeFieldOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f))
          k) _ _ = _
    rw [hT]
    exact driftKernel_latticeShift hL hLs hk n hTr hIso hDrift hU hU' i' i
  · change iterCovariantKernel L k
      (FieldValueFunctions.gaugeFieldOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f)) _ _ = _
    rw [hT]
    exact iterCovariantKernel_latticeShift hL hLs hk n hTr hIso hKer hU hU' i' i
end Assembly
theorem claim_holds
    (hDiff : _root_.YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hTr : Tower.Translations.TranslationProperties)
    (hSmall : SmallIterates.SmallIteratesNearOne)
    (hF : FieldValues.FieldsAndValuesClaim)
    (hComm : ComplexSmoothingCommutesWithIntShift)
    (hIso : CovariantSmoothingIsometryEquivariance)
    (hKer : ThreeMapKernels.Claim)
    (hDrift : IteratedDriftKernel.DriftKernelRepresents)
    (hForm : LevelwiseMeans.LevelwiseMeansHold)
    (hE : ComplexMatrix2.ExpLogEstimates) : Claim := by
  intro L hL hLs k hk
  obtain ⟨⟨υ, hυ, -, -, hW⟩, ρ₁, hρ₁, hρ⟩ := hSmall L hL hLs k hk
  have hυ₀ : 0 < υ 0 := hυ 0 (by omega)
  have hs6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hlog : 0 < Real.log (1 + υ 0) := Real.log_pos (by linarith)
  refine ⟨min ρ₁ (Real.log (1 + υ 0) / Real.sqrt 6), lt_min hρ₁ (div_pos hlog hs6),
    fun f hf n => ?_⟩
  obtain ⟨r, hr, hb⟩ := id hf
  have hU := hρ f ⟨r, hr.trans_le (min_le_left _ _), hb⟩
  have hU' := pushField_mem_smallIterateFields hLs n hTr hComm hU
  have hlt : Real.sqrt 6 * max r 0 < Real.log (1 + υ 0) := by
    have h₁ : max r 0 < Real.log (1 + υ 0) / Real.sqrt 6 :=
      max_lt (hr.trans_le (min_le_right _ _)) (div_pos hlog hs6)
    rw [lt_div_iff₀ hs6] at h₁
    linarith
  refine ⟨hU, hU', ?_, gaugeFieldOfCoeffs_shiftField hF hL n f,
    shiftCommutesAt hL hLs hk n hTr hIso hKer hComm hForm hDiff hU
      (exists_expTwist_mem_smallIterateFields hE hF hL (fun W h₁ h₂ => (hW W h₁ h₂).1)
        (fun κ => (hb κ).trans (le_max_left _ _)) hlt hυ₀ hU.1),
    kernelsShiftCovariant hF hL hLs hk n hTr hIso hKer hDrift hU hU'⟩
  exact ⟨r, hr, fun κ => hb _⟩
end Tower.FullSpace.ShiftCovariance
end YangMills.Construction
end
