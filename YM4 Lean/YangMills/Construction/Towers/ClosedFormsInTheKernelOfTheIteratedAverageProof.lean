import YangMills.Construction.Towers.BackgroundGaugeFunctionalIsFormedAtTheTrivialPointProof
import YangMills.Construction.Towers.ClosedFormsInTheKernelOfTheIteratedAverage
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ClosedInSmoothingKernel
open TrivialLinearization
section Lattice
variable {L n k j : ℕ}
theorem vertexCoboundary_mem_edgeFormSpace {f : Vertex L n k j → Matrices.ComplexMatrix2}
    (hf : f ∈ vertexFunctionSpace L n k j) :
    vertexCoboundary f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.Tower.ClosedFormsSmoothing.vertexCoboundary_mem <;> assumption
theorem restrictVertexFunction_mem (i : ℕ) {f : Vertex L n k j → Matrices.ComplexMatrix2}
    (hf : f ∈ vertexFunctionSpace L n k j) :
    restrictVertexFunction i f ∈ vertexFunctionSpace L n k i :=
  fun _ _ => hf _ trivial
theorem eq_zero_of_forwardFrom_eq_zero {a : Edge L n k j → Matrices.ComplexMatrix2}
    (ha : a ∈ edgeFormSpace L n k j)
    (hzero : ∀ (x : Vertex L n k j) (μ : Fin 4), a (PeriodicLattice.Bond.forwardFrom x μ) = 0) :
    a = 0 := by apply _root_.YangMills.Construction.Tower.TrivialFieldGauge.edgeForm_eq_zero_of_forward <;> assumption
theorem smoothingIter_coboundary_add_constant
    (hstep : ∀ j, j < k → OneStepIdentities L n k j ∧ OneStepConstantForms L n k j)
    (hsub : ∀ j, j < k → ∀ ξ ∈ edgeFormSpace L n k j, ∀ η ∈ edgeFormSpace L n k j,
      linearSmoothing L n k j (ξ - η) = linearSmoothing L n k j ξ - linearSmoothing L n k j η)
    {f : Vertex L n k 0 → Matrices.ComplexMatrix2} (hf : f ∈ vertexFunctionSpace L n k 0)
    {a : Edge L n k 0 → Matrices.ComplexMatrix2} (ha : a ∈ edgeFormSpace L n k 0)
    (c : Fin 4 → Matrices.ComplexMatrix2)
    (hac : ∀ (x : Vertex L n k 0) (μ : Fin 4), a (PeriodicLattice.Bond.forwardFrom x μ) = c μ)
    (j : ℕ) (hj : j ≤ k) :
    ∃ g ∈ vertexFunctionSpace L n k j, ∃ b ∈ edgeFormSpace L n k j,
      (∀ (x : Vertex L n k j) (μ : Fin 4),
        b (PeriodicLattice.Bond.forwardFrom x μ) = ((L : ℂ) ^ j) • c μ) ∧
      linearSmoothingIter L n k j (vertexCoboundary f + a) = vertexCoboundary g + b := by
  induction j with
  | zero => exact ⟨f, hf, a, ha, fun x μ => by rw [hac, pow_zero, one_smul], rfl⟩
  | succ j ih =>
    obtain ⟨g, hg, b, hb, hv, he⟩ := ih (by omega)
    have hjk : j < k := by omega
    obtain ⟨⟨-, hd⟩, hc⟩ := hstep j hjk
    obtain ⟨-, -, hlin, hmem, hval⟩ := hc b hb (fun μ => ((L : ℂ) ^ j) • c μ) hv
    refine ⟨restrictVertexFunction (j + 1) g, restrictVertexFunction_mem _ hg,
      crossingSmoothing L n k j b, hmem, fun x μ => ?_, ?_⟩
    · rw [hval, smul_smul, pow_succ']
    · have hit : linearSmoothingIter L n k (j + 1) (vertexCoboundary f + a) =
          linearSmoothing L n k j (linearSmoothingIter L n k j (vertexCoboundary f + a)) := rfl
      have h1 := hsub j hjk (vertexCoboundary g + b)
        (add_mem (vertexCoboundary_mem_edgeFormSpace hg) hb) b hb
      rw [add_sub_cancel_right, (hd g hg).1] at h1
      rw [hit, he, ← hlin, h1, sub_add_cancel]
end Lattice
theorem nsmul_eq_zero_of_sub_eq_const {A V : Type*} [AddCommGroup A] [AddCommGroup V]
    {f : A → V} {s : A} {v : V} {N : ℕ} (hN : N • s = 0) (h : ∀ x, f (x + s) - f x = v) :
    N • v = 0 := by
  have key : ∀ i : ℕ, f (0 + i • s) - f 0 = i • v := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc f (0 + (i + 1) • s) - f 0
          = (f (0 + i • s + s) - f (0 + i • s)) + (f (0 + i • s) - f 0) := by
            rw [succ_nsmul, add_assoc]
            abel
        _ = (i + 1) • v := by
            rw [h, ih, succ_nsmul]
            abel
  have e := key N
  rw [hN, add_zero, sub_self] at e
  exact e.symm
theorem exists_nsmul_unitStep_eq_zero
    (hcoord : PeriodicLattice.CoordinateDescription) {L n : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ μ : Fin 4,
      N • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ = 0 := by
  open PeriodicLattice in
  obtain ⟨-, hpos, -, -, hmod, -⟩ :=
    (hcoord L n hL.1 hL.2 hn).1 (levelDepth k k) (by simp only [levelDepth]; omega)
  refine ⟨_, hpos, fun μ => ?_⟩
  have e := (hmod 0 (Pi.single μ ((2 * halfPeriod L n (levelDepth k k) : ℕ) : ℤ)) 0).2
    (fun ν => by
      by_cases hν : ν = μ
      · subst hν
        simp [Int.ModEq]
      · simp [Pi.single_eq_of_ne hν])
  simp only [offsetSite, Pi.single_apply, ite_smul, zero_smul, Pi.zero_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero,
    zero_add] at e
  rw [← natCast_zsmul]
  exact e
theorem closedInSmoothingKernelIsExact_of
    (hclosed : Tower.ClosedEdgeFormsOnPeriodicLattice)
    (hrel : TrivialLinearization.AllRelationsStatement)
    (hunder : Tower.LinearSmoothingOnClosedForms)
    (hcoord : PeriodicLattice.CoordinateDescription) :
    Tower.ClosedInSmoothingKernelIsExact := by
  intro L hL k n _ hn E hE hcl hQ
  obtain ⟨f, hf, a, ha, hconst, rfl⟩ := (hclosed L n k 0 hL hn (Nat.zero_le k) E hE).1 hcl
  obtain ⟨g, -, b, -, hv, he⟩ := smoothingIter_coboundary_add_constant
    (fun j hj =>
      have h := (hrel L hL).1 n k j 0 hn hj (Nat.zero_le k)
      ⟨h.1, h.2.1⟩)
    (fun j hj => (hunder L n k j hL hn hj).1) hf ha
    (fun μ => a (PeriodicLattice.Bond.forwardFrom 0 μ)) (fun x μ => hconst μ x 0) k le_rfl
  rw [he] at hQ
  obtain ⟨N, hN, hNs⟩ := exists_nsmul_unitStep_eq_zero hcoord hL hn k
  have hLne : (L : ℂ) ≠ 0 := by
    have : 0 < L := by have := hL.2; omega
    exact_mod_cast this.ne'
  have hw : ((N : ℂ) * (L : ℂ) ^ k) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hN.ne') (pow_ne_zero _ hLne)
  have hzero : ∀ (x : Vertex L n k 0) (μ : Fin 4),
      a (PeriodicLattice.Bond.forwardFrom x μ) = 0 := by
    intro x μ
    rw [hconst μ x 0]
    set c := a (PeriodicLattice.Bond.forwardFrom 0 μ) with hc
    have hz := nsmul_eq_zero_of_sub_eq_const (f := g) (v := -(((L : ℂ) ^ k) • c))
      (hNs μ) (fun y => by
        have e := congrFun hQ (PeriodicLattice.Bond.forwardFrom y μ)
        simp only [Pi.add_apply, Pi.zero_apply, hv] at e
        exact eq_neg_of_add_eq_zero_left e)
    have hz' : ((N : ℂ) * (L : ℂ) ^ k) • c = 0 := by
      rw [smul_neg, neg_eq_zero] at hz
      rw [mul_smul, Nat.cast_smul_eq_nsmul, hz]
    calc c = ((N : ℂ) * (L : ℂ) ^ k)⁻¹ • (((N : ℂ) * (L : ℂ) ^ k) • c) :=
          (inv_smul_smul₀ hw c).symm
      _ = 0 := by rw [hz', smul_zero]
  refine ⟨f, hf, ?_⟩
  rw [eq_zero_of_forwardFrom_eq_zero ha hzero, add_zero]
end YangMills.Construction.Tower.ClosedInSmoothingKernel
end
