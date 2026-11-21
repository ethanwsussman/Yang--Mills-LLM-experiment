import YangMills.Construction.Matrices.ExpansionInThePeterWeylBasis
import YangMills.Construction.Matrices.PeterWeylFunctionsOfSeveralVariablesAndKernelsForm
import YangMills.Construction.Matrices.PolynomialsAreSpannedByThePeterWeylFunctionsForm
import YangMills.Construction.Matrices.ProjectionsOntoSpacesOfSeveralVariables
import YangMills.Construction.Matrices.RealPolynomialsOnPowersOfGAreDense
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics.PeterWeylExpansion
open MeasureTheory Matrices.ComplexMatrix2 HilbertSpaceBasics SeveralVariables
variable {J : Type} [Finite J]
theorem toLp_mem_span_peterWeylVec {H : C(J → specialUnitary, ℂ)}
    (hH : H ∈ Submodule.span ℂ (Set.range (peterWeylFn : PeterWeylIndex J → C(J → specialUnitary, ℂ)))) :
    ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ H ∈
      Submodule.span ℂ (Set.range (peterWeylVec : PeterWeylIndex J → HaarL2 J)) := by
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, rfl⟩ := hx
    exact Submodule.subset_span ⟨α, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx
theorem mem_closure_span_peterWeylFn (hDense : RealPolyDense J)
    (hSpan : ∀ F : (J → specialUnitary) → ℂ, IsEntryPolynomial F ↔
      IsRealizedIn F (Submodule.span ℂ (Set.range (peterWeylFn : PeterWeylIndex J → C(J → specialUnitary, ℂ)))))
    (f : C(J → specialUnitary, ℂ)) :
    f ∈ closure (Submodule.span ℂ
      (Set.range (peterWeylFn : PeterWeylIndex J → C(J → specialUnitary, ℂ))) : Set C(J → specialUnitary, ℂ)) := by
  obtain ⟨-, -, -, -, hApprox⟩ := hDense
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  let a : C(J → specialUnitary, ℝ) := ⟨fun u => (f u).re, Complex.continuous_re.comp f.continuous⟩
  let c : C(J → specialUnitary, ℝ) := ⟨fun u => (f u).im, Complex.continuous_im.comp f.continuous⟩
  obtain ⟨Pa, hPa, hPa'⟩ := hApprox a (ε / 4) (by positivity)
  obtain ⟨Pc, hPc, hPc'⟩ := hApprox c (ε / 4) (by positivity)
  obtain ⟨Ha, hHa, hHa'⟩ := (hSpan Pa).mp hPa.1
  obtain ⟨Hc, hHc, hHc'⟩ := (hSpan Pc).mp hPc.1
  refine ⟨Ha + Complex.I • Hc, add_mem hHa (Submodule.smul_mem _ _ hHc), ?_⟩
  rw [dist_comm, dist_eq_norm]
  refine lt_of_le_of_lt ((ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ ε / 2)).mpr
    fun u => ?_) (half_lt_self hε)
  have hu : f u = (a u : ℂ) + Complex.I * (c u : ℂ) := by
    change f u = ((f u).re : ℂ) + Complex.I * ((f u).im : ℂ)
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have e : (Ha + Complex.I • Hc - f) u =
      (Pa u - (a u : ℂ)) + Complex.I * (Pc u - (c u : ℂ)) := by
    simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      smul_eq_mul, ← hHa' u, ← hHc' u]
    rw [hu]
    ring
  rw [e]
  calc ‖(Pa u - (a u : ℂ)) + Complex.I * (Pc u - (c u : ℂ))‖
      ≤ ‖Pa u - (a u : ℂ)‖ + ‖Complex.I * (Pc u - (c u : ℂ))‖ := norm_add_le _ _
    _ = ‖Pa u - (a u : ℂ)‖ + ‖Pc u - (c u : ℂ)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ε / 4 + ε / 4 := add_le_add (hPa' u).le (hPc' u).le
    _ = ε / 2 := by ring
theorem top_le_closure_span_peterWeylVec (hDense : RealPolyDense J)
    (hSpan : ∀ F : (J → specialUnitary) → ℂ, IsEntryPolynomial F ↔
      IsRealizedIn F (Submodule.span ℂ (Set.range (peterWeylFn : PeterWeylIndex J → C(J → specialUnitary, ℂ))))) :
    ⊤ ≤ (Submodule.span ℂ (Set.range
      (peterWeylVec : PeterWeylIndex J → HaarL2 J))).topologicalClosure := by
  set S := (Submodule.span ℂ (Set.range
    (peterWeylVec : PeterWeylIndex J → HaarL2 J))).topologicalClosure with hS
  have hclosed : IsClosed (S : Set (HaarL2 J)) :=
    Submodule.isClosed_topologicalClosure _
  have hcont : Continuous (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ) :=
    (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ).continuous
  have hrange : ∀ f : C(J → specialUnitary, ℂ),
      ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ f ∈ (S : Set (HaarL2 J)) := by
    intro f
    have hsub : (Submodule.span ℂ (Set.range (peterWeylFn : PeterWeylIndex J → C(J → specialUnitary, ℂ))) :
        Set C(J → specialUnitary, ℂ)) ⊆
        (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ) ⁻¹' (S : Set (HaarL2 J)) :=
      fun H hH => Submodule.le_topologicalClosure _ (toLp_mem_span_peterWeylVec hH)
    exact closure_minimal hsub (hclosed.preimage hcont) (mem_closure_span_peterWeylFn hDense hSpan f)
  have hd : DenseRange (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ) :=
    ContinuousMap.toLp_denseRange ℂ (haarPi J) ℂ (by norm_num)
  intro F _
  have hF : F ∈ closure (Set.range (ContinuousMap.toLp (E := ℂ) 2 (haarPi J) ℂ)) :=
    hd F
  refine closure_minimal ?_ hclosed hF
  rintro _ ⟨f, rfl⟩
  exact hrange f
theorem peterWeylExpansionHolds_of (hPW : PeterWeylOrthonormalAndKernel)
    (hPoly : PolynomialIffInPeterWeylSpan)
    (hProj : IsotypicProjProperties)
    (hDense : RealPolyDenseOnPowers) : PeterWeylExpansionHolds := by
  intro J _ _ F
  have hOrtho : Orthonormal ℂ (peterWeylVec : PeterWeylIndex J → HaarL2 J) :=
    (hPW J fun _ => ⟨0⟩).1
  have hsp := top_le_closure_span_peterWeylVec (hDense J) (hPoly J)
  let b := HilbertBasis.mk hOrtho hsp
  have hb : ∀ α, b α = peterWeylVec α := fun α =>
    congrFun (HilbertBasis.coe_mk hOrtho hsp) α
  have h1 : HasSum (fun α : PeterWeylIndex J =>
      (inner ℂ (peterWeylVec α) F : ℂ) • peterWeylVec α) F := by
    have h := b.hasSum_repr F
    simpa only [b.repr_apply_apply, hb] using h
  refine ⟨h1, ?_, ?_⟩
  · have hs := (Equiv.sigmaFiberEquiv (spins (ι := J))).hasSum_iff.mpr h1
    refine hs.sigma fun s => ?_
    rw [(hProj J s ⟨0⟩).1 F]
    have hmem : ∀ α, α ∈ indicesWithSpins s ↔ spins α = s := fun α =>
      Set.Finite.mem_toFinset _
    have h := (indicesWithSpins s).hasSum (fun α : PeterWeylIndex J =>
      (inner ℂ (peterWeylVec α) F : ℂ) • peterWeylVec α)
    exact (Equiv.subtypeEquivRight hmem).hasSum_iff.mp h
  · have h := b.hasSum_inner_mul_inner F F
    have key : ∀ α : PeterWeylIndex J, (inner ℂ F (b α) : ℂ) * inner ℂ (b α) F =
        ((‖(inner ℂ (peterWeylVec α) F : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      intro α
      rw [← inner_conj_symm F (b α), Complex.conj_mul', hb]
      push_cast
      rfl
    have hF : (inner ℂ F F : ℂ) = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    simp only [key, hF] at h
    exact Complex.hasSum_ofReal.mp h
end YangMills.Construction.SpinHarmonics.PeterWeylExpansion
end
