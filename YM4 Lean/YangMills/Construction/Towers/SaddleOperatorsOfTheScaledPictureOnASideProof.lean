import YangMills.Construction.Towers.KernelAlgebraOfTheScaledPicture
import YangMills.Construction.Towers.KernelDeterminedByABilinearForm
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnASide
import YangMills.Construction.Towers.SaddleOperatorsOfTheScaledPictureOnASide
import YangMills.Construction.Towers.TheBackgroundKernelAtZeroProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.RescaledSaddleOperators
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.RescaledConditions
open YangMills.Construction.Tower.HessianKernel (IsSymmBilinearOn)
open YangMills.Construction.Matrices
section Entries
variable {N N' N'' : Type}
theorem compKernel_smul_smul (x y : ℂ) (T : KernelMatrix N' N'') (S : KernelMatrix N N') :
    compKernel (x • T) (y • S) = (x * y) • compKernel T S := by
  funext i'' i
  simp only [compKernel, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring
variable {S₀ B₀ S B : Type}
theorem saddleScaling_of_multiples (p : RescaledOperators S₀ B₀ S B)
    (Kd : KernelMatrix (Fin 3 × S₀) (Fin 3 × B₀))
    (Kq : KernelMatrix (Fin 3 × B₀) (Fin 3 × B)) (bg : KernelMatrix (Fin 3 × B₀) (Fin 3 × B₀))
    (hη : p.eta ≠ 0) (hcoarse : p.coarse = 1)
    (hD : p.D = ((p.eta⁻¹ : ℝ) : ℂ) • Kd)
    (hDt : p.Dt = ((p.eta⁻¹ * (p.eta ^ 4 * (p.eta ^ 4)⁻¹) : ℝ) : ℂ) • swapKernel Kd)
    (hQ : p.Q = (p.eta : ℂ) • Kq)
    (hQt : p.Qt = ((p.eta * (p.coarse ^ 4 * (p.eta ^ 4)⁻¹) : ℝ) : ℂ) • swapKernel Kq)
    (hbg : bg = ((p.eta : ℂ) ^ 2) • p.X) :
    SaddleScaling p (saddleMatrix bg (swapKernel Kq) Kq)
      (saddleMatrix (compKernel (swapKernel Kd) Kd) (swapKernel p.R) p.R) := by
  have hc : (p.eta : ℂ) ≠ 0 := by exact_mod_cast hη
  refine ⟨?_, ?_⟩
  · funext j' j
    rcases j' with i' | c' <;> rcases j with i | c
    · show bg i' i = (p.eta : ℂ) ^ 2 * p.X i' i * 1
      rw [hbg]
      simp
    · show swapKernel Kq i' c = (p.eta : ℂ) ^ 2 * p.Qt i' c * (p.eta : ℂ)
      rw [hQt, hcoarse]
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      field_simp
    · show Kq c' i = (p.eta : ℂ)⁻¹ * p.Q c' i * 1
      rw [hQ]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    · show (0 : ℂ) = (p.eta : ℂ)⁻¹ * 0 * (p.eta : ℂ)
      simp
  · have hΔ : p.Delta = (((p.eta : ℂ)⁻¹) ^ 2) • compKernel (swapKernel Kd) Kd := by
      show compKernel p.Dt p.D = _
      rw [hDt, hD, compKernel_smul_smul]
      congr 1
      push_cast
      field_simp
    funext j' j
    rcases j' with i' | c' <;> rcases j with i | c
    · show compKernel (swapKernel Kd) Kd i' i = (p.eta : ℂ) ^ 2 * p.Delta i' i * 1
      rw [hΔ]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    · show swapKernel p.R i' c = (p.eta : ℂ) ^ 2 * p.Rt i' c * (p.eta : ℂ) ^ 2
      show _ = (p.eta : ℂ) ^ 2 *
        (((meshWeight p.coarse (c) / meshWeight p.eta (i') : ℝ) : ℂ) * p.R c i') * (p.eta : ℂ) ^ 2
      simp only [meshWeight, hcoarse, swapKernel]
      push_cast
      field_simp
    · show p.R c' i = 1 * p.R c' i * 1
      simp
    · show (0 : ℂ) = 1 * 0 * (p.eta : ℂ) ^ 2
      simp
end Entries
section Coefficients
theorem sum_smul_pauliFamily_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_sum_smul_pauliFamily (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem edgePauliCoordinates_coeffsRealHomogeneous (L n k j : ℕ) :
    ScalarMultipleKernels.CoeffsRealHomogeneous (edgePauliCoordinates L n k j) := by apply _root_.YangMills.Construction.Tower.IterTransposesOnTorus.edgePauliCoordinates_coeffsRealHomogeneous <;> assumption
variable {σ : Type}
theorem ofPauliCoeffs_add (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (c + c') = ofPauliCoeffs c + ofPauliCoeffs c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_add <;> assumption
theorem ofPauliCoeffs_smul (z : ℂ) (c : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (z • c) = z • ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_smul <;> assumption
end Coefficients
section Forms
variable {L n k : ℕ}
abbrev formOfCoeffs (L n k : ℕ) : (Fin 3 × PositiveEdge L n k 0 → ℂ) → Edge L n k 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L n k 0).ofCoeffs
open Classical in
theorem formOfCoeffs_eq (c : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    formOfCoeffs L n k c = @extendOddly L n k 0 fun b =>
      if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0 := rfl
theorem formOfCoeffs_pos (c : Fin 3 × PositiveEdge L n k 0 → ℂ) (b : PositiveEdge L n k 0) :
    formOfCoeffs L n k c b.1 = ofPauliCoeffs c b := by
  classical
  rw [formOfCoeffs_eq]
  unfold extendOddly
  rw [if_pos b.2]
  exact dif_pos b.2
theorem formOfCoeffs_neg (c : Fin 3 × PositiveEdge L n k 0 → ℂ) {b : Edge L n k 0}
    (hb : ¬ b.IsPositivelyOriented) (hr : b.opposite.IsPositivelyOriented) :
    formOfCoeffs L n k c b = -ofPauliCoeffs c ⟨b.opposite, hr⟩ := by
  classical
  rw [formOfCoeffs_eq]
  unfold extendOddly
  rw [if_neg hb]
  exact congrArg Neg.neg (dif_pos hr)
variable (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
include hx
theorem opposite_pos_of_not_pos {b : Edge L n k 0} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  rcases hx b with h | h
  · exact absurd h.1 hb
  · exact h.1
theorem opposite_not_pos_of_pos {b : Edge L n k 0} (hb : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by
  rcases hx b with h | h
  · exact h.2
  · exact absurd hb h.2
theorem formOfCoeffs_mem (c : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    formOfCoeffs L n k c ∈ complexEdgeForms L n k 0 := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · have e := formOfCoeffs_pos c ⟨b, hb⟩
    have e' : formOfCoeffs L n k c b = ofPauliCoeffs c ⟨b, hb⟩ := e
    rw [e']
    exact sum_smul_pauliFamily_mem_traceless fun a => c (a, ⟨b, hb⟩)
  · by_cases hb : b.IsPositivelyOriented
    · have e := formOfCoeffs_neg c (opposite_not_pos_of_pos hx hb) hb
      have e' := formOfCoeffs_pos c ⟨b, hb⟩
      have e'' : formOfCoeffs L n k c b = ofPauliCoeffs c ⟨b, hb⟩ := e'
      rw [e'']
      exact e
    · have hr := opposite_pos_of_not_pos hx hb
      rw [formOfCoeffs_neg c hb hr, neg_neg]
      exact formOfCoeffs_pos c ⟨b.opposite, hr⟩
theorem formOfCoeffs_add (c c' : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    formOfCoeffs L n k (c + c') = formOfCoeffs L n k c + formOfCoeffs L n k c' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · have e := formOfCoeffs_pos (c + c') ⟨b, hb⟩
    have e₁ := formOfCoeffs_pos c ⟨b, hb⟩
    have e₂ := formOfCoeffs_pos c' ⟨b, hb⟩
    show formOfCoeffs L n k (c + c') b = formOfCoeffs L n k c b + formOfCoeffs L n k c' b
    refine Eq.trans e ?_
    rw [ofPauliCoeffs_add]
    exact congrArg₂ (· + ·) e₁.symm e₂.symm
  · have hr := opposite_pos_of_not_pos hx hb
    show formOfCoeffs L n k (c + c') b = formOfCoeffs L n k c b + formOfCoeffs L n k c' b
    rw [formOfCoeffs_neg _ hb hr, formOfCoeffs_neg _ hb hr, formOfCoeffs_neg _ hb hr,
      ofPauliCoeffs_add, Pi.add_apply, neg_add]
theorem formOfCoeffs_smul (z : ℂ) (c : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    formOfCoeffs L n k (z • c) = z • formOfCoeffs L n k c := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · have e := formOfCoeffs_pos (z • c) ⟨b, hb⟩
    have e₁ := formOfCoeffs_pos c ⟨b, hb⟩
    show formOfCoeffs L n k (z • c) b = z • formOfCoeffs L n k c b
    refine Eq.trans e ?_
    rw [ofPauliCoeffs_smul]
    exact congrArg (z • ·) e₁.symm
  · have hr := opposite_pos_of_not_pos hx hb
    show formOfCoeffs L n k (z • c) b = z • formOfCoeffs L n k c b
    rw [formOfCoeffs_neg _ hb hr, formOfCoeffs_neg _ hb hr, ofPauliCoeffs_smul, Pi.smul_apply,
      smul_neg]
omit hx in
theorem coeffs_formOfCoeffs (c : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    (edgePauliCoordinates L n k 0).coeffs (formOfCoeffs L n k c) = c := by
  refine funext fun i : Fin 3 × PositiveEdge L n k 0 => ?_
  exact (congrArg (pauliCoeff i.1) (formOfCoeffs_pos c i.2)).trans
    (pauliCoeff_sum_smul_pauliFamily (fun a => c (a, i.2)) i.1)
omit hx in
theorem formOfCoeffs_unitKernel (i : Fin 3 × PositiveEdge L n k 0) :
    formOfCoeffs L n k (fun j => unitKernel (Fin 3 × PositiveEdge L n k 0) j i) =
      basisForm i.1 i.2 := by
  classical
  rw [formOfCoeffs_eq]
  unfold basisForm
  refine congrArg (@extendOddly L n k 0) (funext fun b => ?_)
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb]
    by_cases e : b = i.2.1
    · have e' : (⟨b, hb⟩ : PositiveEdge L n k 0) = i.2 := Subtype.ext e
      rw [if_pos e, e']
      unfold ofPauliCoeffs
      rw [Finset.sum_eq_single i.1]
      · have : unitKernel (Fin 3 × PositiveEdge L n k 0) (i.1, i.2) i = 1 := if_pos rfl
        beta_reduce
        rw [this, one_smul]
      · intro a _ ha
        have : unitKernel (Fin 3 × PositiveEdge L n k 0) (a, i.2) i = 0 :=
          if_neg fun h => ha (Prod.ext_iff.1 h).1
        beta_reduce
        rw [this, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg e]
      unfold ofPauliCoeffs
      refine Finset.sum_eq_zero fun a _ => ?_
      have : unitKernel (Fin 3 × PositiveEdge L n k 0) (a, ⟨b, hb⟩) i = 0 :=
        if_neg fun h => e (congrArg Subtype.val (Prod.ext_iff.1 h).2)
      beta_reduce
      rw [this, zero_smul]
  · rw [dif_neg hb, if_neg]
    intro e
    exact hb (e ▸ i.2.2)
end Forms
section Pairings
variable {ι : Type} [Finite ι]
theorem traceFinsumPairing_add_smul_left (z : ℂ) (f g h : ι → ComplexMatrix2) :
    traceFinsumPairing (z • f + g) h =
      z * traceFinsumPairing f h + traceFinsumPairing g h := by
  have := Fintype.ofFinite ι
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : Matrix.trace ((z • f i + g i) * h i) =
      z * Matrix.trace (f i * h i) + Matrix.trace (g i * h i) := by
    rw [add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  show (1 / 2 : ℂ) * Matrix.trace ((z • f i + g i) * h i) =
    z * ((1 / 2 : ℂ) * Matrix.trace (f i * h i)) + (1 / 2 : ℂ) * Matrix.trace (g i * h i)
  rw [e]
  ring
omit [Finite ι] in
theorem traceFinsumPairing_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.traceFinsumPairing_comm <;> assumption
theorem traceFinsumPairing_add_smul_right (z : ℂ) (f g h : ι → ComplexMatrix2) :
    traceFinsumPairing h (z • f + g) =
      z * traceFinsumPairing h f + traceFinsumPairing h g := by
  rw [traceFinsumPairing_comm, traceFinsumPairing_add_smul_left z f g h,
    traceFinsumPairing_comm f, traceFinsumPairing_comm g]
omit [Finite ι] in
theorem real_smul_fun_eq (r : ℝ) (f : ι → ComplexMatrix2) : r • f = (r : ℂ) • f := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
end Pairings
section Bilinear
variable {α : Type} {𝒮 : Submodule ℂ (α → ComplexMatrix2)}
  {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
theorem bilin_zero_left (hQ : IsSymmBilinearOn (𝒮 : Set (α → ComplexMatrix2)) Q)
    {x : α → ComplexMatrix2} (hx : x ∈ 𝒮) : Q 0 x = 0 := by
  have e := (hQ 1 0 𝒮.zero_mem 0 𝒮.zero_mem x hx).1
  simp only [one_smul, add_zero, one_mul] at e
  have e' : Q 0 x + Q 0 x = Q 0 x := e.symm
  simpa using e'
theorem bilin_smul_left (hQ : IsSymmBilinearOn (𝒮 : Set (α → ComplexMatrix2)) Q) (z : ℂ)
    {x y : α → ComplexMatrix2} (hx : x ∈ 𝒮) (hy : y ∈ 𝒮) : Q (z • x) y = z * Q x y := by
  have e := (hQ z x hx 0 𝒮.zero_mem y hy).1
  rwa [add_zero, bilin_zero_left hQ hy, add_zero] at e
theorem bilin_symm (hQ : IsSymmBilinearOn (𝒮 : Set (α → ComplexMatrix2)) Q)
    {x y : α → ComplexMatrix2} (hx : x ∈ 𝒮) (hy : y ∈ 𝒮) : Q x y = Q y x :=
  (hQ 0 x hx 0 𝒮.zero_mem y hy).2.2
theorem bilin_smul_right (hQ : IsSymmBilinearOn (𝒮 : Set (α → ComplexMatrix2)) Q) (z : ℂ)
    {x y : α → ComplexMatrix2} (hx : x ∈ 𝒮) (hy : y ∈ 𝒮) : Q x (z • y) = z * Q x y := by
  rw [bilin_symm hQ hx (𝒮.smul_mem z hy), bilin_smul_left hQ z hy hx, bilin_symm hQ hy hx]
end Bilinear
section Gauge
variable {L n k : ℕ}
theorem transposeOfValues_eq_transposeMap (S S' : PairedFunctionSpace)
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    (g : S'.complexSubmodule) : PairedFunctionSpace.transposeOfValues S S' m g.1 =
      (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues S S' m) g).1 := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.transposeOfValues_val <;> assumption
def gaugeFixingLinearMap (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2) :
    (edgePairedSpace L n k 0).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L n k 0)).complexSubmodule :=
  PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
      (pairedFunctions (Vertex L n k 0)) (edgePairedSpace L n k 0) (covDiff U)) -
    ((((L : ℝ) ^ (4 * k) : ℝ)) : ℂ) •
      ((PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
          (pairedFunctions (Vertex L n k 0))
          (pairedFunctions (Vertex L n k k)) (iterAdjointCubeAverage L n k U k))).comp
        ((PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L n k 0))
          (pairedFunctions (Vertex L n k k)) (iterAdjointCubeAverage L n k U k)).comp
          (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
            (pairedFunctions (Vertex L n k 0)) (edgePairedSpace L n k 0) (covDiff U)))))
theorem gaugeFixingLinearMap_apply {U : Edge L n k 0 → ComplexMatrix2}
    (hA : ∀ f : (pairedFunctions (Vertex L n k 0)).complexSubmodule,
      (PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L n k 0))
        (pairedFunctions (Vertex L n k k)) (iterAdjointCubeAverage L n k U k) f).1 =
          iterAdjointCubeAverage L n k U k f.1)
    (B : (edgePairedSpace L n k 0).complexSubmodule) :
    (gaugeFixingLinearMap L n k U B).1 = gaugeFixingTerm L n k U B.1 := by
  set D := PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
    (pairedFunctions (Vertex L n k 0)) (edgePairedSpace L n k 0) (covDiff U)) with hD
  set A := PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L n k 0))
    (pairedFunctions (Vertex L n k k)) (iterAdjointCubeAverage L n k U k) with hAdef
  have e₁ : covDiffTranspose L n k U B.1 = (D B).1 :=
    transposeOfValues_eq_transposeMap _ _ _ B
  have e₂ : iterAdjointCubeAverage L n k U k (D B).1 = (A (D B)).1 := (hA _).symm
  have e₃ : iterAverageTranspose L n k U (A (D B)).1 =
      (PairedFunctionSpace.transposeMap A (A (D B))).1 :=
    transposeOfValues_eq_transposeMap _ _ _ (A (D B))
  unfold gaugeFixingTerm
  rw [e₁, e₂, e₃]
  have e₄ := real_smul_fun_eq ((L : ℝ) ^ (4 * k))
    ((PairedFunctionSpace.transposeMap A (A (D B))).1 : Vertex L n k 0 → ComplexMatrix2)
  refine Eq.trans ?_ (congrArg (Sub.sub (α := Vertex L n k 0 → ComplexMatrix2) (D B).1) e₄.symm)
  rfl
end Gauge
section Background
variable {L n k : ℕ}
theorem backgroundForm_isSymmBilinearOn [Finite (Vertex L n k 0)]
    {U : Edge L n k 0 → ComplexMatrix2}
    (hQ : IsSymmBilinearOn (complexEdgeForms L n k 0 : Set (Edge L n k 0 → ComplexMatrix2))
      (complexActionHessian U))
    (hA : ∀ f : (pairedFunctions (Vertex L n k 0)).complexSubmodule,
      (PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L n k 0))
        (pairedFunctions (Vertex L n k k)) (iterAdjointCubeAverage L n k U k) f).1 =
          iterAdjointCubeAverage L n k U k f.1) :
    IsSymmBilinearOn (complexEdgeForms L n k 0 : Set (Edge L n k 0 → ComplexMatrix2))
      (backgroundForm L n k U) := by
  have hGlin : ∀ (z : ℂ), ∀ B ∈ complexEdgeForms L n k 0, ∀ B' ∈ complexEdgeForms L n k 0,
      gaugeFixingTerm L n k U (z • B + B') =
        z • gaugeFixingTerm L n k U B + gaugeFixingTerm L n k U B' := by
    intro z B hB B' hB'
    let b₁ : (edgePairedSpace L n k 0).complexSubmodule := ⟨B, hB⟩
    let b₂ : (edgePairedSpace L n k 0).complexSubmodule := ⟨B', hB'⟩
    have e₁ := gaugeFixingLinearMap_apply hA (z • b₁ + b₂)
    have e₂ := gaugeFixingLinearMap_apply hA b₁
    have e₃ := gaugeFixingLinearMap_apply hA b₂
    rw [map_add, map_smul] at e₁
    have e₁' : gaugeFixingTerm L n k U (z • B + B') = _ := e₁.symm
    have e₂' : gaugeFixingTerm L n k U B = _ := e₂.symm
    have e₃' : gaugeFixingTerm L n k U B' = _ := e₃.symm
    rw [e₁', e₂', e₃']
    rfl
  intro z E₁ m₁ E₂ m₂ E₃ m₃
  obtain ⟨a, b, c⟩ := hQ z E₁ m₁ E₂ m₂ E₃ m₃
  refine ⟨?_, ?_, ?_⟩
  · unfold backgroundForm
    rw [a, hGlin z E₁ m₁ E₂ m₂, traceFinsumPairing_add_smul_left z]
    ring
  · unfold backgroundForm
    rw [b, hGlin z E₁ m₁ E₂ m₂, traceFinsumPairing_add_smul_right z]
    ring
  · unfold backgroundForm
    rw [c, traceFinsumPairing_comm]
theorem basisForm_mem
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (i : Fin 3 × PositiveEdge L n k 0) : basisForm i.1 i.2 ∈ complexEdgeForms L n k 0 := by
  rw [← formOfCoeffs_unitKernel i]
  exact formOfCoeffs_mem hx _
theorem backgroundKernel_eq (hK : RescaledKernelAlgebra.Claim)
    (hPol : PolarisedKernel.ValueAtUnits) [Finite (Edge L n k 0)]
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {U : Edge L n k 0 → ComplexMatrix2}
    (hη : 0 < finestMesh L k) (hcoarse : 0 < meshAt L k k)
    (hQ : IsSymmBilinearOn (complexEdgeForms L n k 0 : Set (Edge L n k 0 → ComplexMatrix2))
      (complexActionHessian U))
    (hP : IsSymmBilinearOn (complexEdgeForms L n k 0 : Set (Edge L n k 0 → ComplexMatrix2))
      (backgroundForm L n k U))
    {Dm Qm Rm Wm} {DW}
    (hR : CoreRelations (vertexCoordinate (Vertex L n k 0)) (edgePauliCoordinates L n k 0)
      (vertexCoordinate (Vertex L n k k)) (edgePauliCoordinates L n k k) (rescaledOperators L n k U)
      Dm Qm Rm Wm DW (backgroundForm L n k U)) :
    backgroundKernel L n k U =
      (((finestMesh L k : ℝ) : ℂ) ^ 2) • (rescaledOperators L n k U).X := by
  classical
  set η := finestMesh L k with hηdef
  have hc : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  set p := rescaledOperators L n k U with hp
  have hpos : Finite (PositiveEdge L n k 0) := Subtype.finite
  have hrows : ∀ {T : KernelMatrix (Fin 3 × PositiveEdge L n k 0)
      (Fin 3 × PositiveEdge L n k 0)}, RowFinite T := fun _ => Set.toFinite _
  have hcons := hK _ _ _ _ p hη hcoarse
    ⟨hR.row_finite.2.2.1, hR.row_finite.2.2.2.2.2, hR.row_finite.1, hR.row_finite.2.2.2.2.1,
      hrows⟩ hR.R_comp_Rt
  have hsmul : ∀ {B}, B ∈ complexEdgeForms L n k 0 → η • B ∈ complexEdgeForms L n k 0 := by
    intro B hB
    rw [real_smul_fun_eq]
    exact (complexEdgeForms L n k 0).smul_mem _ hB
  have hFm : ∀ c, η • formOfCoeffs L n k c ∈ complexEdgeForms L n k 0 := fun c =>
    hsmul (formOfCoeffs_mem hx c)
  have hT : ∀ i i', gaugeFixedKernel p i i' = gaugeFixedKernel p i' i := by
    intro i i'
    have e₁ : p.H i i' = p.H i' i := by
      show _ * complexActionHessian U _ _ = _ * complexActionHessian U _ _
      rw [bilin_symm hQ (hsmul (basisForm_mem hx i)) (hsmul (basisForm_mem hx i'))]
    have e₂ := hcons.correction_symm i i'
    show p.H i i' + RescaledKernelAlgebra.gaugeCorrection p i i' =
      p.H i' i + RescaledKernelAlgebra.gaugeCorrection p i' i
    rw [e₁, e₂]
  let β : (Fin 3 × PositiveEdge L n k 0 → ℂ) → (Fin 3 × PositiveEdge L n k 0 → ℂ) → ℂ :=
    fun c c' => backgroundForm L n k U (η • formOfCoeffs L n k c)
      (η • formOfCoeffs L n k c')
  have hβ : PolarisedKernel.IsSymmBilinearOnFinite β := by
    refine ⟨fun z f g h _ _ _ => ?_, fun f g _ _ => bilin_symm hP (hFm f) (hFm g)⟩
    have e : η • formOfCoeffs L n k (z • f + g) =
        z • (η • formOfCoeffs L n k f) + η • formOfCoeffs L n k g := by
      rw [formOfCoeffs_add hx, formOfCoeffs_smul hx]
      simp only [real_smul_fun_eq, smul_add]
      rw [smul_comm]
    show backgroundForm L n k U (η • formOfCoeffs L n k (z • f + g)) _ = _
    rw [e]
    exact (hP z _ (hFm f) _ (hFm g) _ (hFm h)).1
  have hquad : ∀ c : Fin 3 × PositiveEdge L n k 0 → ℂ, HasFiniteSupport c →
      β c c = PeriodicOperators.wPairing (fun _ => η ^ 4) c
        (applyKernel (gaugeFixedKernel p) c) := by
    intro c _
    have e := hR.background_eq (formOfCoeffs L n k c) (formOfCoeffs_mem hx c) (Set.toFinite _)
    rw [coeffs_formOfCoeffs] at e
    exact e
  funext i i'
  have e := hPol _ (gaugeFixedKernel p) (η ^ 4) β hrows hT hβ hquad i i'
  have e₁ : β (fun j => unitKernel _ j i) (fun j => unitKernel _ j i') =
      backgroundForm L n k U (η • basisForm i.1 i.2) (η • basisForm i'.1 i'.2) := by
    show backgroundForm L n k U (η • formOfCoeffs L n k _) (η • formOfCoeffs L n k _) = _
    rw [formOfCoeffs_unitKernel, formOfCoeffs_unitKernel]
  have e₂ : backgroundForm L n k U (η • basisForm i.1 i.2)
      (η • basisForm i'.1 i'.2) = (η : ℂ) ^ 2 * backgroundKernel L n k U i i' := by
    rw [real_smul_fun_eq, real_smul_fun_eq,
      bilin_smul_left hP _ (basisForm_mem hx i)
        ((complexEdgeForms L n k 0).smul_mem _ (basisForm_mem hx i')),
      bilin_smul_right hP _ (basisForm_mem hx i) (basisForm_mem hx i')]
    show _ = (η : ℂ) ^ 2 * backgroundForm L n k U _ _
    ring
  rw [e₁, e₂] at e
  have e₃ : (rescaledOperators L n k U).X i i' = gaugeFixedKernel p i i' :=
    congrFun (congrFun hcons.X_eq i) i'
  show backgroundKernel L n k U i i' = (η : ℂ) ^ 2 * (rescaledOperators L n k U).X i i'
  rw [e₃]
  push_cast at e
  have h2 : (η : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hc
  apply mul_left_cancel₀ h2
  rw [e]
  ring
end Background
theorem statement_holds
    (h₁ : RescaledIterRelations)
    (h₂ : RescaledKernelAlgebra.Claim)
    (h₃ : ScalarMultipleKernels.Statement)
    (h₄ : PolarisedKernel.ValueAtUnits)
    (h₅ : ThreeMapKernels.Claim)
    (h₆ : CovariantIterRelations)
    (h₇ : HessianKernel.KernelProperties)
    (h₈ : PeriodicLattice.BondEndpointsOrientation.Statement) : Statement := by
  intro L hL k hk n hn U hU
  classical
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hfs : Finite (Vertex L n k 0) := SeparatedSequences.BaseParameters.site_finite hL0 n _
  have hfb : Finite (Edge L n k 0) :=
    Finite.of_injective (fun b : Edge L n k 0 => (b.source, b.target)) fun _ _ h =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
    have key : ∀ d : ℤ, d = PeriodicLattice.levelDepth (k + 1) (0 + 1) →
        ∀ c : PeriodicLattice.Bond L n d,
        Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented := by
      rintro d rfl c
      exact ((h₈ ⟨L, hL, ⟨k + 1, Nat.succ_pos k⟩, ⟨n, hn⟩⟩ (0 + 1)
        (Nat.succ_le_succ (Nat.zero_le k))).2.2.2 c).2.2.2.2.2
    exact key _ (by simp [PeriodicLattice.levelDepth])
  have hpos : ∀ j, 0 < meshAt L k j := fun j => zpow_pos (by exact_mod_cast hL0) _
  have hcoarse : meshAt L k k = 1 := by simp [meshAt]
  have hRel := h₁ L hL k hk n hn U hU
  have hKer := (h₅ L hL k hk).1 n hn
  have hUc : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup := hU.1
  have hKd := hKer.2.1 U hUc
  obtain ⟨hKq, -⟩ := hKer.2.2.2 U hU
  have hAt := hKer.1 0 k (Nat.zero_le k) le_rfl
  have hAt₀ := hKer.1 0 0 (Nat.zero_le k) (Nat.zero_le k)
  have hQ := ((h₇ L hL k 0 (Nat.zero_le k)).1 n hn U hUc).1
  obtain ⟨T, hTval, -, -⟩ := (h₆ L hL n k k hn le_rfl U hU).2.2
  have hA : ∀ f : (pairedFunctions (Vertex L n k 0)).complexSubmodule,
      (PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L n k 0))
        (pairedFunctions (Vertex L n k k)) (iterAdjointCubeAverage L n k U k) f).1 =
          iterAdjointCubeAverage L n k U k f.1 :=
    Classical.epsilon_spec
      (p := fun T : (pairedFunctions (Vertex L n k 0)).complexSubmodule →ₗ[ℂ]
          (pairedFunctions (Vertex L n k k)).complexSubmodule =>
        ∀ f : (pairedFunctions (Vertex L n k 0)).complexSubmodule,
          (T f : (pairedFunctions (Vertex L n k k)).index → ComplexMatrix2) =
            iterAdjointCubeAverage L n k U k f.1) ⟨T, hTval⟩
  have hP := backgroundForm_isSymmBilinearOn hQ hA
  have hbg := backgroundKernel_eq h₂ h₄ hx (hpos 0) (hpos k) hQ hP hRel
  have mD := h₃ (vertexCoordinate (Vertex L n k 0)) (edgePauliCoordinates L n k 0) (covDiff U)
    (edgePauliCoordinates_coeffsRealHomogeneous L n k 0) hKd hAt₀.2.1 (finestMesh L k)⁻¹ (finestMesh L k)
    (finestMesh L k)
  have mQ := h₃ (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k) (iterCovariantDeriv L n k U k)
    (edgePauliCoordinates_coeffsRealHomogeneous L n k k) hKq hAt.2.2.2 (finestMesh L k) (finestMesh L k)
    (meshAt L k k)
  exact saddleScaling_of_multiples (rescaledOperators L n k U) (covDiffKernel L n k 0 U)
    (iterCovariantKernel L n k U) (backgroundKernel L n k U) (hpos 0).ne' hcoarse mD.1 mD.2
    mQ.1 mQ.2 hbg
end YangMills.Construction.Tower.RescaledSaddleOperators
end
