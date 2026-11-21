import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.RunningCouplingSlope.ColourCoordinatesOfATower
import YangMills.Construction.Towers.BackgroundOperatorFromAMatrixOfItsFormProof
import YangMills.Construction.Towers.DeterminantsOfTheTwoOperatorFunctionsOnTheTorusProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace PauliCoords
open Tower Matrices
private theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, c b • ComplexMatrix2.pauliFamily b) = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
private theorem sum_pauliCoeff_smul {M : ComplexMatrix2} (hM : M ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a M • ComplexMatrix2.pauliFamily a = M := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem mem_traceless_of_mem_hermitianTraceless {M : ComplexMatrix2}
    (hM : M ∈ ComplexMatrix2.hermitianTraceless) : M ∈ ComplexMatrix2.traceless := hM.2
private theorem pauliCoeff_im_eq_zero {M : ComplexMatrix2}
    (hM : M ∈ ComplexMatrix2.hermitianTraceless) (a : Fin 3) :
    (pauliCoeff a M).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
private theorem real_sum_smul_mem_hermitianTraceless (c : Fin 3 → ℝ) :
    (∑ b, ((c b : ℝ) : ℂ) • ComplexMatrix2.pauliFamily b) ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.real_pauli_sum_mem_hermitianTraceless <;> assumption
private theorem halfTrace_mul_eq_sum {M N : ComplexMatrix2} (hM : M ∈ ComplexMatrix2.traceless)
    (hN : N ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (M * N) = ∑ a, pauliCoeff a M * pauliCoeff a N := by apply _root_.YangMills.Construction.Tower.HessianOfFormMatrix.halfTrace_mul_eq_sum <;> assumption
section Charts
variable {L n k j : ℕ}
private def oddFormOfCoeffs (c : Fin 3 × PositiveEdge L n k j → ℂ) : Edge L n k j → ComplexMatrix2 :=
  extendOddly fun e => open Classical in
    if h : e.IsPositivelyOriented then ofPauliCoeffs c ⟨e, h⟩ else 0
private theorem oddFormOfCoeffs_positive (c : Fin 3 × PositiveEdge L n k j → ℂ)
    (e : PositiveEdge L n k j) :
    oddFormOfCoeffs c e.1 = ofPauliCoeffs c e := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.edgeFormOfCoeffs_of_pos <;> assumption
private theorem oddFormOfCoeffs_opposite
    (hxor : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (c : Fin 3 × PositiveEdge L n k j → ℂ) (e : Edge L n k j) :
    oddFormOfCoeffs c e.opposite = -oddFormOfCoeffs c e := by apply _root_.YangMills.Construction.Tower.PeriodicDeterminants.edgeFormOfCoeffs_opposite <;> assumption
private theorem oddForm_ext
    (hxor : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    {A A' : Edge L n k j → ComplexMatrix2} (hA : ∀ e, A e.opposite = -A e)
    (hA' : ∀ e, A' e.opposite = -A' e)
    (h : ∀ e : PositiveEdge L n k j, A e.1 = A' e.1) : A = A' := by apply _root_.YangMills.Construction.Tower.PeriodicDeterminants.oddForm_ext <;> assumption
private def edgeChart
    (hxor : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented) :
    (Fin 3 × PositiveEdge L n k j → ℝ) →ₗ[ℝ] edgeFormSpace L n k j where
  toFun c := ⟨oddFormOfCoeffs fun i => ((c i : ℝ) : ℂ),
    show _ ∈ edgeFormSpace L n k j from ⟨fun e he => by
      have h1 := oddFormOfCoeffs_positive (fun i => ((c i : ℝ) : ℂ)) ⟨e, he⟩
      change oddFormOfCoeffs _ e = _ at h1
      rw [h1]
      exact real_sum_smul_mem_hermitianTraceless _, oddFormOfCoeffs_opposite hxor _⟩⟩
  map_add' c c' := by
    apply Subtype.ext
    refine oddForm_ext hxor (oddFormOfCoeffs_opposite hxor _) (fun e => ?_) fun e => ?_
    · change oddFormOfCoeffs _ e.opposite + oddFormOfCoeffs _ e.opposite =
        -(oddFormOfCoeffs _ e + oddFormOfCoeffs _ e)
      rw [oddFormOfCoeffs_opposite hxor, oddFormOfCoeffs_opposite hxor]
      abel
    · change oddFormOfCoeffs _ e.1 = oddFormOfCoeffs _ e.1 + oddFormOfCoeffs _ e.1
      simp only [oddFormOfCoeffs_positive, ofPauliCoeffs, Pi.add_apply, Complex.ofReal_add, add_smul,
        Finset.sum_add_distrib]
  map_smul' r c := by
    apply Subtype.ext
    refine oddForm_ext hxor (oddFormOfCoeffs_opposite hxor _) (fun e => ?_) fun e => ?_
    · change r • oddFormOfCoeffs _ e.opposite = -(r • oddFormOfCoeffs _ e)
      rw [oddFormOfCoeffs_opposite hxor, smul_neg]
    · change oddFormOfCoeffs _ e.1 = r • oddFormOfCoeffs _ e.1
      simp only [oddFormOfCoeffs_positive, ofPauliCoeffs, Pi.smul_apply, smul_eq_mul,
        Complex.ofReal_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_smul]
      rfl
private theorem toPauliCoeffs_edgeChart
    (hxor : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (c : Fin 3 × PositiveEdge L n k j → ℝ) (i : Fin 3 × PositiveEdge L n k j) :
    toPauliCoeffs (restrictToPositiveEdges (edgeChart hxor c : Edge L n k j → ComplexMatrix2)) i =
      ((c i : ℝ) : ℂ) := by
  change pauliCoeff i.1 (oddFormOfCoeffs _ i.2.1) = _
  rw [oddFormOfCoeffs_positive]
  exact pauliCoeff_sum_smul (fun a => ((c (a, i.2) : ℝ) : ℂ)) i.1
private theorem edgeChart_re
    (hxor : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (f : edgeFormSpace L n k j) :
    edgeChart hxor (fun i =>
      (toPauliCoeffs (restrictToPositiveEdges (f : Edge L n k j → ComplexMatrix2)) i).re) = f := by
  apply Subtype.ext
  refine oddForm_ext hxor (oddFormOfCoeffs_opposite hxor _) f.2.2 fun e => ?_
  have hm : (f : Edge L n k j → ComplexMatrix2) e.1 ∈ ComplexMatrix2.hermitianTraceless :=
    f.2.1 e.1 e.2
  change oddFormOfCoeffs _ e.1 = _
  rw [oddFormOfCoeffs_positive]
  conv_rhs => rw [← sum_pauliCoeff_smul (mem_traceless_of_mem_hermitianTraceless hm)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  apply Complex.ext
  · rfl
  · simpa using (pauliCoeff_im_eq_zero hm a).symm
private def vertexChart : (Fin 3 × Vertex L n k j → ℝ) →ₗ[ℝ] vertexFunctionSpace L n k j where
  toFun c := ⟨ofPauliCoeffs fun i => ((c i : ℝ) : ℂ),
    fun x _ => real_sum_smul_mem_hermitianTraceless _⟩
  map_add' c c' := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_add, Pi.add_apply, ofPauliCoeffs, Complex.ofReal_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' r c := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, ofPauliCoeffs,
      Finset.smul_sum, smul_eq_mul, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul]
    rfl
private theorem toPauliCoeffs_vertexChart (c : Fin 3 × Vertex L n k j → ℝ)
    (i : Fin 3 × Vertex L n k j) :
    toPauliCoeffs (vertexChart c : Vertex L n k j → ComplexMatrix2) i = ((c i : ℝ) : ℂ) :=
  pauliCoeff_sum_smul (fun a => ((c (a, i.2) : ℝ) : ℂ)) i.1
private theorem vertexChart_re (f : vertexFunctionSpace L n k j) :
    vertexChart (fun i => (toPauliCoeffs (f : Vertex L n k j → ComplexMatrix2) i).re) = f := by
  apply Subtype.ext
  funext x
  have hm : (f : Vertex L n k j → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
    f.2 x (Set.mem_univ x)
  change ofPauliCoeffs
    (fun i => (((toPauliCoeffs (f : Vertex L n k j → ComplexMatrix2) i).re : ℝ) : ℂ)) x = _
  simp only [ofPauliCoeffs]
  conv_rhs => rw [← sum_pauliCoeff_smul (mem_traceless_of_mem_hermitianTraceless hm)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  apply Complex.ext
  · rfl
  · simpa using (pauliCoeff_im_eq_zero hm a).symm
private theorem exists_linearEquiv_coords {X σ : Type} (p : Submodule ℝ (X → ComplexMatrix2))
    (coords : (X → ComplexMatrix2) → Fin 3 × σ → ℂ) (G : (Fin 3 × σ → ℝ) →ₗ[ℝ] p)
    (h1 : ∀ c i, coords (G c) i = ((c i : ℝ) : ℂ))
    (h2 : ∀ f : p, G (fun i => (coords f i).re) = f) :
    ∃ Ψ : p ≃ₗ[ℝ] (Fin 3 × σ → ℝ), ∀ (f : p) i, coords f i = ((Ψ f i : ℝ) : ℂ) := by apply _root_.YangMills.Construction.Tower.PeriodicDeterminants.exists_realCoords <;> assumption
private theorem traceFinsumPairing_eq_sum {σ : Type} [inst : Fintype (Fin 3 × σ)]
    (f g : σ → ComplexMatrix2)
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) :
    traceFinsumPairing f g = ∑ i : Fin 3 × σ, toPauliCoeffs f i * toPauliCoeffs g i := by
  have : Finite σ := Finite.of_surjective (Prod.snd : Fin 3 × σ → σ) Prod.snd_surjective
  let _ : Fintype σ := Fintype.ofFinite σ
  obtain rfl : inst = instFintypeProd _ _ := Subsingleton.elim _ _
  rw [traceFinsumPairing, finsum_eq_sum_of_fintype, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact halfTrace_mul_eq_sum (hf x) (hg x)
end Charts
end PauliCoords
open PauliCoords Tower Matrices in
theorem pauliCoordsOrthonormal_holds : PauliCoordsOrthonormal := by
  intro L n k j hL hn hj
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  have hxor : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented :=
    fun e => PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) e
  refine ⟨?_, ?_⟩
  · intro _
    obtain ⟨Ψ, hΨ⟩ := exists_linearEquiv_coords (edgeFormSpace L n k j)
      (fun f => toPauliCoeffs (restrictToPositiveEdges f))
      (edgeChart hxor) (toPauliCoeffs_edgeChart hxor) (edgeChart_re hxor)
    refine ⟨Ψ, hΨ, fun f g => ?_⟩
    rw [edgeFormPairing, traceFinsumPairing_eq_sum
      (restrictToPositiveEdges (f : Edge L n k j → ComplexMatrix2))
      (restrictToPositiveEdges (g : Edge L n k j → ComplexMatrix2))
      (fun e : PositiveEdge L n k j => mem_traceless_of_mem_hermitianTraceless (f.2.1 e.1 e.2))
      (fun e : PositiveEdge L n k j => mem_traceless_of_mem_hermitianTraceless (g.2.1 e.1 e.2))]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [hΨ, hΨ]
  · intro _
    obtain ⟨Ψ, hΨ⟩ := exists_linearEquiv_coords (vertexFunctionSpace L n k j)
      (fun f => toPauliCoeffs f) vertexChart toPauliCoeffs_vertexChart vertexChart_re
    refine ⟨Ψ, hΨ, fun f g => ?_⟩
    rw [traceFinsumPairing_eq_sum _ _
      (fun x => mem_traceless_of_mem_hermitianTraceless (f.2 x (Set.mem_univ x)))
      (fun x => mem_traceless_of_mem_hermitianTraceless (g.2 x (Set.mem_univ x)))]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [hΨ, hΨ]
end YangMills.Construction.RunningCouplingSlope
end
