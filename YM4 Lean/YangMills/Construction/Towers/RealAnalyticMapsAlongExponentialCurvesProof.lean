import YangMills.Construction.OneLoop.PauliMatrixComputations
import YangMills.Construction.Towers.HessianOnAFibreOfTheCriticalBranchProof
import YangMills.Construction.Towers.RealAnalyticMapsAlongExponentialCurves
import YangMills.Construction.Towers.RealAnalyticMapsAlongPathsProof
import YangMills.Construction.Towers.RealAnalyticMapsNearAConfiguration
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.Tower.AnalyticAlongExpCurves
open Matrices
open AnalyticNearField
theorem exists_pauliCoeffs {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ∃ c : Fin 3 → ℝ, ∑ a, c a • ComplexMatrix2.pauliFamily a = X := by
  obtain ⟨hherm, htrace⟩ := hX
  have e00 : X 0 0 = star (X 0 0) := congrFun (congrFun hherm 0) 0
  have e01 : X 0 1 = star (X 1 0) := congrFun (congrFun hherm 0) 1
  have hsum : X 0 0 + X 1 1 = 0 := by
    simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using htrace
  have im00 : (X 0 0).im = 0 := by
    have := congrArg Complex.im e00
    simp at this
    linarith
  have diag11 : X 1 1 = -X 0 0 := by linear_combination hsum
  have re01 : (X 0 1).re = (X 1 0).re := by rw [e01]; simp
  have im01 : (X 0 1).im = -(X 1 0).im := by rw [e01]; simp
  have s0 : ComplexMatrix2.pauliFamily 0 = !![0, 1; 1, 0] := rfl
  have s1 : ComplexMatrix2.pauliFamily 1 = !![0, -Complex.I; Complex.I, 0] := rfl
  have s2 : ComplexMatrix2.pauliFamily 2 = !![1, 0; 0, -1] := rfl
  refine ⟨![(X 1 0).re, (X 1 0).im, (X 0 0).re], ?_⟩
  rw [Fin.sum_univ_three, s0, s1, s2]
  ext r s
  fin_cases r <;> fin_cases s <;> apply Complex.ext <;> simp [im00, diag11, re01, im01]
theorem pauliFamily_mem (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
section EdgeForms
variable {L n k j : ℕ}
theorem not_opposite_positive (hlat : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (e : Edge L n k j)
    (he : e.IsPositivelyOriented) : ¬ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem edgeFormOfPositiveValues_mem
    (hopp : ∀ e : Edge L n k j, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented)
    {w : PositiveEdge L n k j → ComplexMatrix2}
    (hw : ∀ e, w e ∈ ComplexMatrix2.hermitianTraceless) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.Tower.FibreHessian.edgeForm_mem <;> assumption
theorem pauliBasisForm_mem
    (hopp : ∀ e : Edge L n k j, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented)
    (e : PositiveEdge L n k j) (a : Fin 3) : pauliBasisForm e a ∈ edgeFormSpace L n k j := by
  refine edgeFormOfPositiveValues_mem hopp fun d => ?_
  split_ifs
  · exact pauliFamily_mem a
  · exact ComplexMatrix2.hermitianTraceless.zero_mem
theorem edgeForm_ext {A A' : Edge L n k j → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k j)
    (hA' : A' ∈ edgeFormSpace L n k j)
    (h : ∀ e, e.IsPositivelyOriented → A e = A' e) : A = A' := by apply _root_.YangMills.SharedProofs.p88895 <;> assumption
theorem pauliBasisForm_apply (e d : PositiveEdge L n k j) (a : Fin 3) :
    pauliBasisForm e a d.1 =
      open Classical in if d = e then ComplexMatrix2.pauliFamily a else 0 := by
  simp only [pauliBasisForm, edgeFormOfPositiveValues, dif_pos d.2]
variable [Fintype (PositiveEdge L n k j)] {N : ℕ} (ι : PositiveEdge L n k j × Fin 3 ≃ Fin N)
theorem formOfCoords_eq_sum (y : Fin N → ℝ) :
    formOfCoords ι y = ∑ p : PositiveEdge L n k j × Fin 3,
      y (ι p) • pauliBasisForm p.1 p.2 := by
  unfold formOfCoords formOfCoeffs
  exact finsum_eq_sum_of_fintype _
theorem formOfCoords_apply (y : Fin N → ℝ) (e : PositiveEdge L n k j) :
    formOfCoords ι y e.1 = ∑ a, y (ι (e, a)) • ComplexMatrix2.pauliFamily a := by
  classical
  rw [formOfCoords_eq_sum, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single e]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [pauliBasisForm_apply]
  · intro d _ hd
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [pauliBasisForm_apply, Ne.symm hd]
  · simp
theorem formOfCoords_mem
    (hopp : ∀ e : Edge L n k j, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented)
    (y : Fin N → ℝ) : formOfCoords ι y ∈ edgeFormSpace L n k j := by
  rw [formOfCoords_eq_sum]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (pauliBasisForm_mem hopp p.1 p.2)
theorem formOfCoords_smul (t : ℝ) (y : Fin N → ℝ) :
    formOfCoords ι (t • y) = t • formOfCoords ι y := by
  simp only [formOfCoords_eq_sum, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
theorem exists_formOfCoords_eq
    (hopp : ∀ e : Edge L n k j, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented)
    {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k j) :
    ∃ y : Fin N → ℝ, formOfCoords ι y = A := by
  have hc : ∀ e : PositiveEdge L n k j,
      ∃ c : Fin 3 → ℝ, ∑ a, c a • ComplexMatrix2.pauliFamily a = A e.1 :=
    fun e => exists_pauliCoeffs (hA.1 e.1 e.2)
  choose c hc using hc
  refine ⟨fun i => c (ι.symm i).1 (ι.symm i).2, ?_⟩
  refine edgeForm_ext (formOfCoords_mem ι hopp _) hA fun e he => ?_
  have h := formOfCoords_apply ι (fun i => c (ι.symm i).1 (ι.symm i).2) ⟨e, he⟩
  simp only [Equiv.symm_apply_apply] at h
  rw [hc] at h
  exact h
end EdgeForms
theorem exists_openInterval_subset {S : Set ℝ} (hS : S ∈ 𝓝 (0 : ℝ)) :
    ∃ I ⊆ S, IsOpenIntervalAroundZero I := by
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 hS
  refine ⟨Metric.ball 0 ε, h, Metric.isOpen_ball, ?_, Metric.mem_ball_self hε⟩
  rw [Real.ball_eq_Ioo]
  exact ordConnected_Ioo
theorem statement_holds (hnear : AnalyticNearField.CompositionAndExpTwist)
    (hlat : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hchart : LeftChartFields.Claim) :
    AnalyticAlongExpCurves.Statement := by
  intro L n k j j' hL hn hj hj' U A 𝒩 F hU hmem hA hF
  have hopp : ∀ e : Edge L n k j, e.IsPositivelyOriented → ¬ e.opposite.IsPositivelyOriented :=
    fun e he => not_opposite_positive hlat hL hn hj e he
  have : Finite (PositiveEdge L n k j) := (((hchart.2.2 L k j hL hj).1 n hn).2.1).1
  have : Fintype (PositiveEdge L n k j) := Fintype.ofFinite _
  have ι := Fintype.equivFin (PositiveEdge L n k j × Fin 3)
  obtain ⟨𝒪, ⟨⟨O, hO, hOeq⟩, h0⟩, hexp, hsmooth⟩ :=
    ((hnear L n k j j' j' hL hn hj hj' hj').2 U 𝒩 hU hmem).2 F hF
  obtain ⟨y, hy⟩ := exists_formOfCoords_eq ι hopp hA
  have hscaled : ∀ t : ℝ, formOfCoords ι (t • y) = (t : ℂ) • A := by
    intro t
    rw [formOfCoords_smul, hy]
    exact (algebraMap_smul ℂ t A).symm
  have hray : ∀ t : ℝ, (t : ℂ) • A ∈ edgeFormSpace L n k j := by
    intro t
    rw [← hscaled]
    exact formOfCoords_mem ι hopp _
  have hzero : (0 : Edge L n k j → ComplexMatrix2) ∈ O := by
    rw [hOeq] at h0
    exact h0.1
  have hcont : Continuous fun t : ℝ => (t : ℂ) • A :=
    (Complex.continuous_ofReal).smul continuous_const
  have hpre : (fun t : ℝ => (t : ℂ) • A) ⁻¹' O ∈ 𝓝 (0 : ℝ) := by
    refine hcont.continuousAt.preimage_mem_nhds (hO.mem_nhds ?_)
    simpa using hzero
  obtain ⟨I, hIsub, hI⟩ := exists_openInterval_subset hpre
  have hIin : ∀ t ∈ I, (t : ℂ) • A ∈ 𝒪 := by
    intro t ht
    rw [hOeq]
    exact ⟨hIsub ht, hray t⟩
  refine ⟨I, hI, fun t ht => hexp _ (hIin t ht), fun e r s => ?_⟩
  have hlin : ContDiff ℝ ∞ fun t : ℝ => t • y := contDiff_id.smul contDiff_const
  refine ((hsmooth _ ι e r s).2.comp hlin.contDiffOn fun t ht => ?_).congr fun t _ => ?_
  · show formOfCoords ι (t • y) ∈ 𝒪
    rw [hscaled]
    exact hIin t ht
  · simp only [Function.comp_def, hscaled]
end YangMills.Construction.Tower.AnalyticAlongExpCurves
end
