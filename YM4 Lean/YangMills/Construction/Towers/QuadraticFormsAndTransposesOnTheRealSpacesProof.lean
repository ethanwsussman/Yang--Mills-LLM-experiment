import YangMills.Construction.Lattice.AveragingMapIsABorelMapProof
import YangMills.Construction.LinearAlgebra.SymmetricOperatorOfBilinForm
import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASideProof
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChartProof
import YangMills.Construction.Towers.FibresOfTheAveragingMaps
import YangMills.Construction.Towers.IterateOfTheAveragingMapsNearTheTrivialConfigurationProof
import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import YangMills.Construction.Towers.PlaquettesAndSumsOfATowerProof
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOnTheSidesProof
import YangMills.Construction.Towers.SecondDifferentialInTheLeftChart
import YangMills.Construction.Towers.TheActionOnATower
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.RealQuadraticTransposes
theorem traceless_of_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.hermitianTraceless) :
    X ∈ ComplexMatrix2.traceless := h.2
def hermPart (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def antiHermPart (X : ComplexMatrix2) : ComplexMatrix2 :=
  (-(Complex.I / 2)) • (X - X.conjTranspose)
theorem fullTrace_conjTranspose_eq_zero {X : ComplexMatrix2} (h : ComplexMatrix2.fullTrace X = 0) :
    ComplexMatrix2.fullTrace X.conjTranspose = 0 := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.fullTrace_conjTranspose_eq_zero <;> assumption
theorem hermPart_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    hermPart X ∈ ComplexMatrix2.hermitianTraceless := by
  have hX : ComplexMatrix2.fullTrace X = 0 := h
  have hX' := fullTrace_conjTranspose_eq_zero hX
  refine ⟨?_, ?_⟩
  · simp only [hermPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm]
    congr 1
    simp [Complex.ext_iff]
  · simp only [ComplexMatrix2.fullTrace] at hX hX' ⊢
    simp [hermPart, Matrix.trace_smul, Matrix.trace_add, hX, hX']
theorem antiHermPart_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    antiHermPart X ∈ ComplexMatrix2.hermitianTraceless := by
  have hX : ComplexMatrix2.fullTrace X = 0 := h
  have hX' := fullTrace_conjTranspose_eq_zero hX
  refine ⟨?_, ?_⟩
  · simp only [antiHermPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by
      simp [Complex.ext_iff]
      norm_num
    rw [this, ← neg_sub X, smul_neg, neg_smul]
  · simp only [ComplexMatrix2.fullTrace] at hX hX' ⊢
    simp [antiHermPart, Matrix.trace_smul, Matrix.trace_sub, hX, hX']
theorem hermPart_add_I_smul_antiHermPart (X : ComplexMatrix2) :
    X = hermPart X + Complex.I • antiHermPart X := by
  simp only [hermPart, antiHermPart, smul_smul]
  have h : Complex.I * -(Complex.I / 2) = 1 / 2 := by
    have := Complex.I_mul_I
    linear_combination (-1 / 2 : ℂ) * this
  rw [h, ← smul_add]
  have : X + X.conjTranspose + (X - X.conjTranspose) = (2 : ℂ) • X := by
    rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num
theorem eq_zero_of_add_I_smul_eq_zero {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    (h : X + Complex.I • Y = 0) : X = 0 ∧ Y = 0 := by
  have h' := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_zero,
    ← hX.1, ← hY.1] at h'
  have hs : star Complex.I = -Complex.I := by simp [Complex.ext_iff]
  rw [hs, neg_smul] at h'
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]
    calc X + X = (X + Complex.I • Y) + (X + -(Complex.I • Y)) := by abel
      _ = 0 := by rw [h, h', add_zero]
  have hX0 : X = 0 := by
    simpa using h2
  refine ⟨hX0, ?_⟩
  rw [hX0, zero_add] at h
  simpa using h
theorem halfTrace_mul_im {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    (ComplexMatrix2.halfTrace (X * Y)).im = 0 := by apply _root_.YangMills.Construction.Tower.FaceSums.halfTrace_mul_im <;> assumption
theorem eq_zero_of_halfTrace_mul_self {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (h : (ComplexMatrix2.halfTrace (X * X)).re = 0) : X = 0 := by apply _root_.YangMills.Construction.Tower.FaceSums.eq_zero_of_halfTrace_mul_self_re <;> assumption
theorem halfTrace_mul_self_nonneg {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (ComplexMatrix2.halfTrace (X * X)).re := by apply _root_.YangMills.SharedProofs.p2980 <;> assumption
section Sums
variable {ι : Type*} [Finite ι]
theorem tracePair_eq_sum [Fintype ι] (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = ∑ i, ComplexMatrix2.halfTrace (f i * g i) :=
  finsum_eq_sum_of_fintype _
theorem tracePair_add_left (f f' g : ι → ComplexMatrix2) :
    traceFinsumPairing (f + f') g = traceFinsumPairing f g + traceFinsumPairing f' g := by
  cases nonempty_fintype ι
  simp only [tracePair_eq_sum, Pi.add_apply, add_mul, ComplexMatrix2.halfTrace,
    ComplexMatrix2.fullTrace, Matrix.trace_add, mul_add, Finset.sum_add_distrib]
theorem tracePair_smul_left (a : ℂ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (a • f) g = a * traceFinsumPairing f g := by
  cases nonempty_fintype ι
  simp only [tracePair_eq_sum, Pi.smul_apply, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Finset.mul_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem tracePair_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by
  cases nonempty_fintype ι
  simp only [tracePair_eq_sum, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  exact Finset.sum_congr rfl fun i _ => by rw [Matrix.trace_mul_comm]
theorem tracePair_im {f g : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless)
    (hg : ∀ i, g i ∈ ComplexMatrix2.hermitianTraceless) :
    (traceFinsumPairing f g).im = 0 := by
  cases nonempty_fintype ι
  rw [tracePair_eq_sum, Complex.im_sum]
  exact Finset.sum_eq_zero fun i _ => halfTrace_mul_im (hf i) (hg i)
theorem tracePair_self_nonneg {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (traceFinsumPairing f f).re := by
  cases nonempty_fintype ι
  rw [tracePair_eq_sum, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => halfTrace_mul_self_nonneg (hf i)
theorem eq_zero_of_tracePair_self {f : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless)
    (h : traceFinsumPairing f f = 0) : f = 0 := by
  cases nonempty_fintype ι
  have h' := congrArg Complex.re h
  rw [tracePair_eq_sum, Complex.re_sum, Complex.zero_re] at h'
  have h1 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => halfTrace_mul_self_nonneg (hf i)).mp h'
  funext i
  exact eq_zero_of_halfTrace_mul_self (hf i) (h1 i (Finset.mem_univ i))
end Sums
structure IsFinDimEuclidean (S : PairedFunctionSpace) : Prop where
  finDim : FiniteDimensional ℝ S.realSubmodule
  finSupp : ∀ f, S.IsFinitelySupported f
  mem_complex_of_mem_real : ∀ f ∈ S.realSubmodule, f ∈ S.complexSubmodule
  existsUnique_decomp : ∀ f : S.complexSubmodule, ∃! p : S.realSubmodule × S.realSubmodule,
    (f : S.index → ComplexMatrix2) =
      (p.1 : S.index → ComplexMatrix2) + Complex.I • (p.2 : S.index → ComplexMatrix2)
  pair_add_left : ∀ f f' g, S.pair (f + f') g = S.pair f g + S.pair f' g
  pair_smul_left : ∀ (a : ℂ) f g, S.pair (a • f) g = a * S.pair f g
  pair_symm : ∀ f g, S.pair f g = S.pair g f
  pair_im : ∀ f ∈ S.realSubmodule, ∀ g ∈ S.realSubmodule, (S.pair f g).im = 0
  pair_nonneg : ∀ f ∈ S.realSubmodule, 0 ≤ (S.pair f f).re
  pair_definite : ∀ f ∈ S.realSubmodule, S.pair f f = 0 → f = 0
namespace IsFinDimEuclidean
variable {S S' : PairedFunctionSpace}
theorem pair_smul_right (h : IsFinDimEuclidean S) (a : ℂ) (f g : S.index → ComplexMatrix2) :
    S.pair f (a • g) = a * S.pair f g := by
  rw [h.pair_symm, h.pair_smul_left, h.pair_symm]
theorem pair_add_right (h : IsFinDimEuclidean S) (f g g' : S.index → ComplexMatrix2) :
    S.pair f (g + g') = S.pair f g + S.pair f g' := by
  rw [h.pair_symm, h.pair_add_left, h.pair_symm, h.pair_symm g']
theorem pair_split_expand (h : IsFinDimEuclidean S) (a b c d : S.index → ComplexMatrix2) :
    S.pair (a + Complex.I • b) (c + Complex.I • d) =
      S.pair a c + Complex.I * S.pair a d + Complex.I * S.pair b c - S.pair b d := by
  rw [h.pair_add_left, h.pair_add_right, h.pair_add_right, h.pair_smul_left, h.pair_smul_left,
    h.pair_smul_right, h.pair_smul_right]
  have := Complex.I_mul_I
  linear_combination (S.pair b d) * this
@[instance_reducible]
def innerCore (h : IsFinDimEuclidean S) : InnerProductSpace.Core ℝ S.realSubmodule where
  inner f g := (S.pair f g).re
  conj_inner_symm f g := by
    simp only [conj_trivial]
    rw [h.pair_symm]
  re_inner_nonneg f := by
    simpa using h.pair_nonneg f f.2
  add_left f f' g := by
    show (S.pair (f + f' : S.index → ComplexMatrix2) g).re = _
    rw [h.pair_add_left, Complex.add_re]
  smul_left f g c := by
    show (S.pair ((c : ℝ) • (f : S.index → ComplexMatrix2)) g).re = _
    have : (c : ℝ) • (f : S.index → ComplexMatrix2) = (c : ℂ) • (f : S.index → ComplexMatrix2) :=
      (algebraMap_smul ℂ c (f : S.index → ComplexMatrix2)).symm
    rw [this, h.pair_smul_left]
    simp
  definite f hf := by
    have h0 : S.pair f f = 0 := Complex.ext hf (h.pair_im f f.2 f f.2)
    exact Subtype.ext (h.pair_definite f f.2 h0)
theorem pair_eq_ofReal (h : IsFinDimEuclidean S) (f g : S.realSubmodule) :
    S.pair f g = (((S.pair f g).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simpa using h.pair_im f f.2 g g.2)
theorem exists_realAdjoint (h : IsFinDimEuclidean S) (h' : IsFinDimEuclidean S')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) :
    ∃ R : S'.realSubmodule →ₗ[ℝ] S.realSubmodule, ∀ (g : S'.realSubmodule) (f : S.realSubmodule),
      S.pair (R g) f = S'.pair g (T₀ f) := by
  haveI := h.finDim
  haveI := h'.finDim
  letI : NormedAddCommGroup S.realSubmodule := h.innerCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ S.realSubmodule := InnerProductSpace.ofCore h.innerCore.toCore
  letI : NormedAddCommGroup S'.realSubmodule := h'.innerCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ S'.realSubmodule := InnerProductSpace.ofCore h'.innerCore.toCore
  haveI : FiniteDimensional ℝ S.realSubmodule := h.finDim
  haveI : FiniteDimensional ℝ S'.realSubmodule := h'.finDim
  refine ⟨LinearMap.adjoint T₀, fun g f => ?_⟩
  have e := LinearMap.adjoint_inner_left T₀ f g
  have e' : (S.pair (LinearMap.adjoint T₀ g : S.realSubmodule) f).re = (S'.pair g (T₀ f)).re := e
  rw [h.pair_eq_ofReal, h'.pair_eq_ofReal, e']
theorem exists_complexification (h : IsFinDimEuclidean S) (h' : IsFinDimEuclidean S')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) :
    ∃ T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule,
      PairedFunctionSpace.IsComplexification T₀ T := by
  have hs := h.existsUnique_decomp
  choose p hp hu using hs
  have hmem : ∀ x y : S.realSubmodule, (T₀ x : S'.index → ComplexMatrix2) +
      Complex.I • (T₀ y : S'.index → ComplexMatrix2) ∈ S'.complexSubmodule := fun x y =>
    S'.complexSubmodule.add_mem (h'.mem_complex_of_mem_real _ (T₀ x).2)
      (S'.complexSubmodule.smul_mem _ (h'.mem_complex_of_mem_real _ (T₀ y).2))
  have hadd : ∀ f g : S.complexSubmodule, p (f + g) = p f + p g := by
    intro f g
    refine (hu (f + g) (p f + p g) ?_).symm ▸ rfl
    show ((f + g : S.complexSubmodule) : S.index → ComplexMatrix2) = _
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
    rw [show (f : S.index → ComplexMatrix2) = _ from hp f,
      show (g : S.index → ComplexMatrix2) = _ from hp g]
    abel
  have hsmul : ∀ (c : ℂ) (f : S.complexSubmodule), p (c • f) =
      (c.re • (p f).1 - c.im • (p f).2, c.im • (p f).1 + c.re • (p f).2) := by
    intro c f
    refine (hu (c • f) _ ?_).symm ▸ rfl
    simp only [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sub]
    rw [show (f : S.index → ComplexMatrix2) = _ from hp f]
    have r : ∀ (t : ℝ) (F : S.index → ComplexMatrix2), t • F = (t : ℂ) • F := fun t F =>
      (algebraMap_smul ℂ t F).symm
    simp only [r]
    conv_lhs => rw [← Complex.re_add_im c]
    have := Complex.I_mul_I
    match_scalars <;> first | ring1 | linear_combination (c.im : ℂ) * this | linear_combination (-(c.im : ℂ)) * this
  refine ⟨{ toFun := fun f => ⟨_, hmem (p f).1 (p f).2⟩, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro f g
    apply Subtype.ext
    simp only [hadd, Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add, smul_add]
    abel
  · intro c f
    apply Subtype.ext
    simp only [hsmul, map_add, map_sub, map_smul, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_smul, RingHom.id_apply]
    have r : ∀ (t : ℝ) (F : S'.index → ComplexMatrix2), t • F = (t : ℂ) • F := fun t F =>
      (algebraMap_smul ℂ t F).symm
    simp only [r]
    conv_rhs => rw [← Complex.re_add_im c]
    have := Complex.I_mul_I
    match_scalars <;> first | ring1 | linear_combination (c.im : ℂ) * this | linear_combination (-(c.im : ℂ)) * this
  · intro f f' g hg
    have e : p g = (f, f') := (hu g (f, f') hg).symm ▸ rfl
    show (T₀ (p g).1 : S'.index → ComplexMatrix2) +
      Complex.I • (T₀ (p g).2 : S'.index → ComplexMatrix2) = _
    rw [e]
end IsFinDimEuclidean
namespace IsFinDimEuclidean
variable {S S' : PairedFunctionSpace}
theorem complexification_unique (h : IsFinDimEuclidean S)
    {T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule}
    {T T' : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule}
    (hT : PairedFunctionSpace.IsComplexification T₀ T)
    (hT' : PairedFunctionSpace.IsComplexification T₀ T') : T = T' := by
  ext1 f
  obtain ⟨p, hp, -⟩ := h.existsUnique_decomp f
  exact Subtype.ext ((hT p.1 p.2 f hp).trans (hT' p.1 p.2 f hp).symm)
theorem eq_zero_of_pair (h : IsFinDimEuclidean S) (D : S.complexSubmodule)
    (hD : ∀ f : S.complexSubmodule, S.pair D f = 0) : D = 0 := by
  obtain ⟨p, hp, -⟩ := h.existsUnique_decomp D
  have key : ∀ x : S.realSubmodule, S.pair p.1 x = 0 ∧ S.pair p.2 x = 0 := by
    intro x
    have e := hD ⟨x, h.mem_complex_of_mem_real x x.2⟩
    have e' : S.pair (D : S.index → ComplexMatrix2) x = 0 := e
    rw [hp, h.pair_add_left, h.pair_smul_left] at e'
    have a := h.pair_eq_ofReal p.1 x
    have b := h.pair_eq_ofReal p.2 x
    rw [a, b] at e'
    have r := congrArg Complex.re e'
    have i := congrArg Complex.im e'
    simp at r i
    rw [a, b, r, i]
    simp
  have z1 := h.pair_definite p.1 p.1.2 (key p.1).1
  have z2 := h.pair_definite p.2 p.2.2 (key p.2).2
  apply Subtype.ext
  show (D : S.index → ComplexMatrix2) = 0
  rw [hp, z1, z2]
  simp
theorem transpose_facts (h : IsFinDimEuclidean S) (h' : IsFinDimEuclidean S')
    {T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule}
    {T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule}
    (hT : PairedFunctionSpace.IsComplexification T₀ T) :
    (∀ (g : S'.realSubmodule) (f : S.realSubmodule),
      S.pair (PairedFunctionSpace.realTransposeMap T₀ g) f = S'.pair g (T₀ f)) ∧
    ∀ (g : S'.realSubmodule) (k : S'.complexSubmodule), (k : S'.index → ComplexMatrix2) = g →
      (PairedFunctionSpace.realTransposeMap T₀ g : S.index → ComplexMatrix2) =
        PairedFunctionSpace.transposeMap T k := by
  obtain ⟨R, hR⟩ := h.exists_realAdjoint h' T₀
  obtain ⟨T', hT'⟩ := h'.exists_complexification h R
  have hc : PairedFunctionSpace.complexification T₀ = T :=
    h.complexification_unique
      (Classical.epsilon_spec (p := PairedFunctionSpace.IsComplexification T₀) ⟨T, hT⟩) hT
  have hIs : PairedFunctionSpace.IsTransposeMap T T' := by
    intro g f _
    obtain ⟨p, hp, -⟩ := h'.existsUnique_decomp g
    obtain ⟨q, hq, -⟩ := h.existsUnique_decomp f
    rw [hT' p.1 p.2 g hp, hq, hp, hT q.1 q.2 f hq, h.pair_split_expand, h'.pair_split_expand,
      hR, hR, hR, hR]
  have hte : PairedFunctionSpace.transposeMap T = T' := by
    have hs : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) :=
      Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap T) ⟨T', hIs⟩
    ext1 g
    have hz := h.eq_zero_of_pair (PairedFunctionSpace.transposeMap T g - T' g) fun f => ?_
    · exact sub_eq_zero.mp hz
    · have e1 := hs g f (h.finSupp _)
      have e2 := hIs g f (h.finSupp _)
      have : ((PairedFunctionSpace.transposeMap T g - T' g : S.complexSubmodule) :
          S.index → ComplexMatrix2) =
          (PairedFunctionSpace.transposeMap T g : S.index → ComplexMatrix2) +
            (-1 : ℂ) • (T' g : S.index → ComplexMatrix2) := by
        simp [sub_eq_add_neg]
      rw [this, h.pair_add_left, h.pair_smul_left, e1, e2]
      ring
  have hRT : PairedFunctionSpace.IsRealTransposeMap T₀ R := by
    intro g k hk
    rw [hc, hte]
    have hk' : (k : S'.index → ComplexMatrix2) = (g : S'.index → ComplexMatrix2) +
        Complex.I • ((0 : S'.realSubmodule) : S'.index → ComplexMatrix2) := by simpa using hk
    rw [hT' g 0 k hk']
    simp
  have hreal : PairedFunctionSpace.realTransposeMap T₀ = R := by
    have hs : PairedFunctionSpace.IsRealTransposeMap T₀ (PairedFunctionSpace.realTransposeMap T₀) :=
      Classical.epsilon_spec (p := PairedFunctionSpace.IsRealTransposeMap T₀) ⟨R, hRT⟩
    ext1 g
    apply Subtype.ext
    have e1 := hs g ⟨g, h'.mem_complex_of_mem_real g g.2⟩ rfl
    have e2 := hRT g ⟨g, h'.mem_complex_of_mem_real g g.2⟩ rfl
    exact e1.trans e2.symm
  refine ⟨fun g f => by rw [hreal]; exact hR g f, fun g k hk => ?_⟩
  rw [hreal, hRT g k hk, hc]
theorem transposePreservesReal (h : IsFinDimEuclidean S) (h' : IsFinDimEuclidean S')
    {T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule}
    {T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule}
    (hT : PairedFunctionSpace.IsComplexification T₀ T) : TransposePreservesReal T T₀ := by
  obtain ⟨h1, h2⟩ := h.transpose_facts h' hT
  refine ⟨fun k hk => ?_, h2, h1⟩
  have := h2 ⟨k, hk⟩ k rfl
  rw [← this]
  exact (PairedFunctionSpace.realTransposeMap T₀ ⟨k, hk⟩).2
theorem isComplexification_of_eq (h : IsFinDimEuclidean S)
    {F : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2}
    {T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule}
    {T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule}
    (hT : ∀ f : S.complexSubmodule, (T f : S'.index → ComplexMatrix2) = F f)
    (hT₀ : ∀ f : S.realSubmodule, (T₀ f : S'.index → ComplexMatrix2) = F f) :
    PairedFunctionSpace.IsComplexification T₀ T := by
  intro f f' k hk
  have e : k = ⟨f, h.mem_complex_of_mem_real f f.2⟩ +
      Complex.I • ⟨f', h.mem_complex_of_mem_real f' f'.2⟩ := Subtype.ext hk
  rw [e, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, hT, hT, hT₀, hT₀]
end IsFinDimEuclidean
theorem isFinDimEuclidean_pairedFunctions (ι : Type) [Finite ι] :
    IsFinDimEuclidean (pairedFunctions ι) where
  finDim := by
    show FiniteDimensional ℝ (Matrices.GroupLieProduct.hermitianTracelessFunctions ι)
    cases nonempty_fintype ι
    infer_instance
  finSupp f := Set.toFinite _
  mem_complex_of_mem_real f hf := fun x _ => traceless_of_mem (hf x trivial)
  existsUnique_decomp f := by
    refine ⟨(⟨fun x => hermPart (f.1 x), fun x _ => hermPart_mem (f.2 x trivial)⟩,
      ⟨fun x => antiHermPart (f.1 x), fun x _ => antiHermPart_mem (f.2 x trivial)⟩), ?_, ?_⟩
    · funext x
      exact hermPart_add_I_smul_antiHermPart (f.1 x)
    · rintro ⟨a, b⟩ hab
      have hx : ∀ x, a.1 x = hermPart (f.1 x) ∧ b.1 x = antiHermPart (f.1 x) := by
        intro x
        have e₁ : f.1 x = a.1 x + Complex.I • b.1 x := congrFun hab x
        have e₂ := hermPart_add_I_smul_antiHermPart (f.1 x)
        have m₁ : a.1 x - hermPart (f.1 x) ∈ ComplexMatrix2.hermitianTraceless :=
          ComplexMatrix2.hermitianTraceless.sub_mem (a.2 x trivial) (hermPart_mem (f.2 x trivial))
        have m₂ : b.1 x - antiHermPart (f.1 x) ∈ ComplexMatrix2.hermitianTraceless :=
          ComplexMatrix2.hermitianTraceless.sub_mem (b.2 x trivial)
            (antiHermPart_mem (f.2 x trivial))
        have z := eq_zero_of_add_I_smul_eq_zero m₁ m₂ (by
          rw [smul_sub]
          have : a.1 x + Complex.I • b.1 x = hermPart (f.1 x) + Complex.I • antiHermPart (f.1 x) :=
            e₁.symm.trans e₂
          calc _ = (a.1 x + Complex.I • b.1 x) -
                (hermPart (f.1 x) + Complex.I • antiHermPart (f.1 x)) := by abel
            _ = 0 := by rw [this, sub_self])
        exact ⟨sub_eq_zero.mp z.1, sub_eq_zero.mp z.2⟩
      refine Prod.ext (Subtype.ext (funext fun x => (hx x).1))
        (Subtype.ext (funext fun x => (hx x).2))
  pair_add_left f f' g := tracePair_add_left (ι := ι) f f' g
  pair_smul_left a f g := tracePair_smul_left (ι := ι) a f g
  pair_symm f g := tracePair_comm (ι := ι) f g
  pair_im f hf g hg := tracePair_im (ι := ι) (fun x => hf x trivial) fun x => hg x trivial
  pair_nonneg f hf := tracePair_self_nonneg (ι := ι) fun x => hf x trivial
  pair_definite f hf := eq_zero_of_tracePair_self (ι := ι) fun x => hf x trivial
theorem eq_hermPart_and_antiHermPart {X a b : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (ha : a ∈ ComplexMatrix2.hermitianTraceless) (hb : b ∈ ComplexMatrix2.hermitianTraceless)
    (h : X = a + Complex.I • b) : a = hermPart X ∧ b = antiHermPart X := by
  have e₂ := hermPart_add_I_smul_antiHermPart X
  have m₁ : a - hermPart X ∈ ComplexMatrix2.hermitianTraceless :=
    ComplexMatrix2.hermitianTraceless.sub_mem ha (hermPart_mem hX)
  have m₂ : b - antiHermPart X ∈ ComplexMatrix2.hermitianTraceless :=
    ComplexMatrix2.hermitianTraceless.sub_mem hb (antiHermPart_mem hX)
  have z := eq_zero_of_add_I_smul_eq_zero m₁ m₂ (by
    rw [smul_sub]
    have : a + Complex.I • b = hermPart X + Complex.I • antiHermPart X := h.symm.trans e₂
    calc _ = (a + Complex.I • b) - (hermPart X + Complex.I • antiHermPart X) := by abel
      _ = 0 := by rw [this, sub_self])
  exact ⟨sub_eq_zero.mp z.1, sub_eq_zero.mp z.2⟩
theorem hermPart_neg (X : ComplexMatrix2) : hermPart (-X) = -hermPart X := by
  simp only [hermPart, Matrix.conjTranspose_neg, ← neg_add, smul_neg]
theorem antiHermPart_neg (X : ComplexMatrix2) : antiHermPart (-X) = -antiHermPart X := by
  simp only [antiHermPart, Matrix.conjTranspose_neg, smul_sub, smul_neg]
  abel
section Lattice
variable {L n k j : ℕ}
theorem isPos_or_opposite_isPos (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_isPos_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
def OppositeFlipsOrientation (L n k j : ℕ) : Prop :=
  ∀ b : Edge L n k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented
theorem oppositeFlipsOrientation (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    OppositeFlipsOrientation L n k j := by apply _root_.YangMills.Construction.Tower.LeftChartFields.finite_opposite_isPos_iff <;> assumption
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := rfl
theorem extendOddly_of_pos {f : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos hb
theorem extendOddly_of_not_pos {f : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := if_neg hb
theorem extendOddly_opposite (hr : OppositeFlipsOrientation L n k j)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.extendOddly_opposite <;> assumption
theorem extendOddly_mem_edgeFormSpace (hr : OppositeFlipsOrientation L n k j)
    {f : Edge L n k j → ComplexMatrix2}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j :=
  ⟨fun b hb => by rw [extendOddly_of_pos hb]; exact h b hb, extendOddly_opposite hr f⟩
theorem extendOddly_mem_complexEdgeForms (hr : OppositeFlipsOrientation L n k j)
    {f : Edge L n k j → ComplexMatrix2}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms L n k j :=
  ⟨fun b hb => by rw [extendOddly_of_pos hb]; exact h b hb, extendOddly_opposite hr f⟩
theorem mem_complexEdgeForms_of_mem {B : Edge L n k j → ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j) : B ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
theorem edgeForm_apply_mem {B : Edge L n k j → ComplexMatrix2} (h : B ∈ edgeFormSpace L n k j)
    (b : Edge L n k j) : B b ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.edgeForm_apply_mem <;> assumption
theorem complexEdgeForm_apply_mem {B : Edge L n k j → ComplexMatrix2}
    (h : B ∈ complexEdgeForms L n k j) (b : Edge L n k j) : B b ∈ ComplexMatrix2.traceless := by
  rcases isPos_or_opposite_isPos b with hb | hb
  · exact h.1 b hb
  · have e : B b = -B b.opposite := by rw [h.2 b, neg_neg]
    rw [e]
    exact ComplexMatrix2.traceless.neg_mem (h.1 _ hb)
theorem eq_of_restrictToPositiveEdges_eq {B B' : Edge L n k j → ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j) (h' : B' ∈ edgeFormSpace L n k j)
    (e : restrictToPositiveEdges B = restrictToPositiveEdges B') : B = B' := by
  funext b
  rcases isPos_or_opposite_isPos b with hb | hb
  · exact congrFun e ⟨b, hb⟩
  · have e' : B b.opposite = B' b.opposite := congrFun e ⟨b.opposite, hb⟩
    rw [h.2 b, h'.2 b] at e'
    exact neg_injective e'
theorem hermPart_form_mem {B : Edge L n k j → ComplexMatrix2} (h : B ∈ complexEdgeForms L n k j) :
    (fun b => hermPart (B b)) ∈ edgeFormSpace L n k j :=
  ⟨fun b hb => hermPart_mem (h.1 b hb), fun b => by
    show hermPart (B b.opposite) = -hermPart (B b)
    rw [h.2 b, hermPart_neg]⟩
theorem antiHermPart_form_mem {B : Edge L n k j → ComplexMatrix2}
    (h : B ∈ complexEdgeForms L n k j) :
    (fun b => antiHermPart (B b)) ∈ edgeFormSpace L n k j :=
  ⟨fun b hb => antiHermPart_mem (h.1 b hb), fun b => by
    show antiHermPart (B b.opposite) = -antiHermPart (B b)
    rw [h.2 b, antiHermPart_neg]⟩
theorem isFinDimEuclidean_edgePairedSpace (hf : Finite (PositiveEdge L n k j))
    (hd : FiniteDimensional ℝ (edgeFormSpace L n k j)) :
    IsFinDimEuclidean (edgePairedSpace L n k j) where
  finDim := hd
  finSupp f := Set.toFinite _
  mem_complex_of_mem_real f hf := mem_complexEdgeForms_of_mem hf
  existsUnique_decomp f := by
    have hf' : ∀ b, f.1 b ∈ ComplexMatrix2.traceless := complexEdgeForm_apply_mem f.2
    refine ⟨(⟨_, hermPart_form_mem f.2⟩, ⟨_, antiHermPart_form_mem f.2⟩), ?_, ?_⟩
    · funext b
      exact hermPart_add_I_smul_antiHermPart (f.1 b)
    · rintro ⟨a, c⟩ hab
      have hx : ∀ b, a.1 b = hermPart (f.1 b) ∧ c.1 b = antiHermPart (f.1 b) := fun b =>
        eq_hermPart_and_antiHermPart (hf' b) (edgeForm_apply_mem a.2 b)
          (edgeForm_apply_mem c.2 b) (congrFun hab b)
      exact Prod.ext (Subtype.ext (funext fun b => (hx b).1))
        (Subtype.ext (funext fun b => (hx b).2))
  pair_add_left f f' g := tracePair_add_left (restrictToPositiveEdges f)
    (restrictToPositiveEdges f') (restrictToPositiveEdges g)
  pair_smul_left a f g := tracePair_smul_left a (restrictToPositiveEdges f)
    (restrictToPositiveEdges g)
  pair_symm f g := tracePair_comm (restrictToPositiveEdges f) (restrictToPositiveEdges g)
  pair_im f hf g hg := tracePair_im (f := restrictToPositiveEdges f)
    (g := restrictToPositiveEdges g) (fun b => hf.1 b.1 b.2) fun b => hg.1 b.1 b.2
  pair_nonneg f hf := tracePair_self_nonneg (f := restrictToPositiveEdges f)
    fun b => hf.1 b.1 b.2
  pair_definite f hf h := by
    have z := eq_zero_of_tracePair_self (f := restrictToPositiveEdges f)
      (fun b => hf.1 b.1 b.2) h
    exact eq_of_restrictToPositiveEdges_eq hf (edgeFormSpace L n k j).zero_mem z
theorem conjugateBy_add (V X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (X + Y) =
      ComplexMatrix2.conjugateBy V X + ComplexMatrix2.conjugateBy V Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (V : ComplexMatrix2) (c : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (c • X) = c • ComplexMatrix2.conjugateBy V X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
theorem conjugateBy_real_smul (V : ComplexMatrix2) (c : ℝ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (c • X) = c • ComplexMatrix2.conjugateBy V X := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
theorem conjugateBy_traceless_of_det_eq_one {V X : ComplexMatrix2} (hV : V.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem conjugateBy_hermitianTraceless_of_mem (hP : OneLoop.PauliMatrixRelations)
    {V X : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary)
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.hermitianTraceless := by
  have h := hP.2.2.2.2.2.2.2.2.2.2 V hV
  have m := Set.mem_image_of_mem (ComplexMatrix2.conjugateBy V)
    (show X ∈ (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) from hX)
  rw [h] at m
  exact m
theorem det_eq_one_of_mem {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) :
    V.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.mp hV).2
theorem extendOddly_smul (c : ℂ) (f : Edge L n k j → ComplexMatrix2) :
    extendOddly (c • f) = c • extendOddly f := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.smul_apply, extendOddly_of_pos hb]
  · simp only [Pi.smul_apply, extendOddly_of_not_pos hb, smul_neg]
theorem covDiff_add (V : Edge L n k j → ComplexMatrix2) (l l' : Vertex L n k j → ComplexMatrix2) :
    covDiff V (l + l') = covDiff V l + covDiff V l' := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.covDiff_add <;> assumption
theorem covDiff_smul (V : Edge L n k j → ComplexMatrix2) (c : ℂ)
    (l : Vertex L n k j → ComplexMatrix2) :
    covDiff V (c • l) = c • covDiff V l := by
  simp only [covDiff, ← extendOddly_smul]
  congr 1
  funext b
  simp only [Pi.smul_apply, conjugateBy_smul, smul_sub]
def covDiffComplex (hr : OppositeFlipsOrientation L n k j) {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    (pairedFunctions (Vertex L n k j)).complexSubmodule →ₗ[ℂ]
      (edgePairedSpace L n k j).complexSubmodule where
  toFun l := ⟨covDiff V l.1, extendOddly_mem_complexEdgeForms hr fun b _ =>
    ComplexMatrix2.traceless.sub_mem
      (conjugateBy_traceless_of_det_eq_one (det_eq_one_of_mem (hV.1 b trivial)) (l.2 _ trivial))
      (l.2 _ trivial)⟩
  map_add' l l' := Subtype.ext (covDiff_add V l.1 l'.1)
  map_smul' c l := Subtype.ext (covDiff_smul V c l.1)
def tracePairBilin (ι : Type*) [Finite ι] :
    (ι → ComplexMatrix2) →ₗ[ℝ] (ι → ComplexMatrix2) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => (traceFinsumPairing f g).re)
    (fun f f' g => by rw [tracePair_add_left, Complex.add_re])
    (fun c f g => by
      have r : c • f = (c : ℂ) • f := (algebraMap_smul ℂ c f).symm
      rw [r, tracePair_smul_left]
      simp)
    (fun f g g' => by
      rw [tracePair_comm, tracePair_add_left, Complex.add_re, tracePair_comm g, tracePair_comm g'])
    (fun c f g => by
      have r : c • g = (c : ℂ) • g := (algebraMap_smul ℂ c g).symm
      rw [r, tracePair_comm, tracePair_smul_left, tracePair_comm g]
      simp)
theorem isRealQuadratic_of_bilin {F : edgeFormSpace L n k 0 → ℂ}
    (β : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 →ₗ[ℝ] ℝ)
    (h : ∀ B, F B = (β B B : ℂ)) : IsRealQuadratic F :=
  ⟨LinearMap.BilinMap.toQuadraticMap β, fun B => by
    rw [h, LinearMap.BilinMap.toQuadraticMap_apply]⟩
end Lattice
section Transposes
variable {L n k : ℕ}
open CovariantSmoothingProperties
theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → ComplexMatrix2)}
    {p' : Submodule ℝ (β → ComplexMatrix2)} {f : (α → ComplexMatrix2) → β → ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
theorem inverseFourthPowerWeight_pow (L k : ℕ) :
    PeriodicLattice.inverseFourthPowerWeight L ^ k = ((((L : ℝ) ^ (4 * k))⁻¹ : ℝ) : ℂ) := by
  simp only [PeriodicLattice.inverseFourthPowerWeight]
  rw [← Complex.ofReal_pow]
  congr 1
  rw [zpow_neg, inv_pow, pow_mul]
  norm_cast
theorem covDiffTransposePreservesReal_of (hr : ∀ i ≤ k, OppositeFlipsOrientation L n k i)
    (hS : ∀ i ≤ k, IsFinDimEuclidean (pairedFunctions (Vertex L n k i)))
    (hB : ∀ i ≤ k, IsFinDimEuclidean (edgePairedSpace L n k i))
    (hlin : ∀ i ≤ k, ∀ V' ∈ fieldSpace L n k i,
      ∃ T : vertexFunctionSpace L n k i →ₗ[ℝ] edgeFormSpace L n k i,
        ∀ l : vertexFunctionSpace L n k i,
          (T l : Edge L n k i → ComplexMatrix2) = covDiff V' (l : Vertex L n k i → ComplexMatrix2)) :
    CovDiffTransposePreservesReal L n k := by
  intro i hi V' hV'
  refine ⟨covDiffComplex (hr i hi) hV', fun f => rfl, ?_⟩
  exact (hS i hi).transposePreservesReal (hB i hi)
    ((hS i hi).isComplexification_of_eq (S' := edgePairedSpace L n k i)
      (F := covDiff V') (T := covDiffComplex (hr i hi) hV') (fun f => rfl)
      (fun f => linearMapWithValues_apply (hlin i hi V' hV') f))
structure TransposeHypotheses (U : Edge L n k 0 → ComplexMatrix2) : Prop where
  vertex0 : IsFinDimEuclidean (pairedFunctions (Vertex L n k 0))
  vertexTop : IsFinDimEuclidean (pairedFunctions (Vertex L n k k))
  edge0 : IsFinDimEuclidean (edgePairedSpace L n k 0)
  finite_vertex0 : Finite (Vertex L n k 0)
  oppositeFlips0 : OppositeFlipsOrientation L n k 0
  L_ne_zero : (L : ℝ) ≠ 0
  mem_fieldSpace : U ∈ fieldSpace L n k 0
  covDiff_exists_linear : ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0,
    ∀ l : vertexFunctionSpace L n k 0,
      (T l : Edge L n k 0 → ComplexMatrix2) = covDiff U (l : Vertex L n k 0 → ComplexMatrix2)
  average_exists_linear : ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
    ∀ l : vertexFunctionSpace L n k 0, (T l : Vertex L n k k → ComplexMatrix2) =
      iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → ComplexMatrix2)
  covariantDeriv_exists_linear : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k,
    ∀ B : edgeFormSpace L n k 0, (T B : Edge L n k k → ComplexMatrix2) =
      iterCovariantDeriv L n k U k (B : Edge L n k 0 → ComplexMatrix2)
  drift_exists_linear : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
    ∀ B : edgeFormSpace L n k 0, (T B : Vertex L n k k → ComplexMatrix2) =
      iterContourLogDrift L n k U k (B : Edge L n k 0 → ComplexMatrix2)
  deriv_relation_forms : ∀ B ∈ complexEdgeForms L n k 0,
    iterCovariantDeriv L n k U k B =
      complexIterDeriv L n k k U B +
        covDiff (PeriodicLattice.complexBlockFieldAtLevel k U) (iterContourLogDrift L n k U k B)
  deriv_relation_vertices : ∀ l : Vertex L n k 0 → ComplexMatrix2,
    (∀ x, l x ∈ ComplexMatrix2.traceless) →
      iterCovariantDeriv L n k U k (covDiff U l) =
        covDiff (PeriodicLattice.complexBlockFieldAtLevel k U) (iterAdjointCubeAverage L n k U k l)
  transposeProduct : PairedFunctionSpace.HasTransposeProduct (pairedFunctions (Vertex L n k 0))
    (pairedFunctions (Vertex L n k k)) (iterAdjointCubeAverage L n k U k)
    (PeriodicLattice.inverseFourthPowerWeight L ^ k)
  complexIterDeriv_onto : ∀ C ∈ edgeFormSpace L n k k, ∃ B ∈ edgeFormSpace L n k 0,
    complexIterDeriv L n k k U B = C
namespace TransposeHypotheses
variable {U : Edge L n k 0 → ComplexMatrix2}
theorem covDiffLinear_apply (d : TransposeHypotheses U) (l : vertexFunctionSpace L n k 0) :
    (covDiffLinear L n k U l : Edge L n k 0 → ComplexMatrix2) =
      covDiff U (l : Vertex L n k 0 → ComplexMatrix2) :=
  linearMapWithValues_apply d.covDiff_exists_linear l
theorem iterAverageLinear_apply (d : TransposeHypotheses U) (l : vertexFunctionSpace L n k 0) :
    (iterAverageLinear L n k U l : Vertex L n k k → ComplexMatrix2) =
      iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → ComplexMatrix2) :=
  linearMapWithValues_apply d.average_exists_linear l
theorem iterCovariantDerivLinear_apply (d : TransposeHypotheses U) (B : edgeFormSpace L n k 0) :
    (iterCovariantDerivLinear L n k U B : Edge L n k k → ComplexMatrix2) =
      iterCovariantDeriv L n k U k (B : Edge L n k 0 → ComplexMatrix2) :=
  linearMapWithValues_apply d.covariantDeriv_exists_linear B
theorem covDiffRealTranspose_pair (d : TransposeHypotheses U) (g : edgeFormSpace L n k 0)
    (f : vertexFunctionSpace L n k 0) :
    traceFinsumPairing (covDiffRealTranspose L n k U g : Vertex L n k 0 → ComplexMatrix2)
        (f : Vertex L n k 0 → ComplexMatrix2) =
      edgeFormPairing (g : Edge L n k 0 → ComplexMatrix2)
        (covDiffLinear L n k U f : Edge L n k 0 → ComplexMatrix2) :=
  (d.vertex0.transpose_facts d.edge0
    (d.vertex0.isComplexification_of_eq (S' := edgePairedSpace L n k 0) (F := covDiff U)
      (T := covDiffComplex d.oppositeFlips0 d.mem_fieldSpace) (fun f => rfl)
      (fun f => d.covDiffLinear_apply f))).1 g f
theorem exists_average_transpose (d : TransposeHypotheses U) :
    ∃ T : (pairedFunctions (Vertex L n k 0)).complexSubmodule →ₗ[ℂ]
        (pairedFunctions (Vertex L n k k)).complexSubmodule,
      (∀ f : (pairedFunctions (Vertex L n k 0)).complexSubmodule,
        (T f).1 = iterAdjointCubeAverage L n k U k f.1) ∧
      TransposePreservesReal (S := pairedFunctions (Vertex L n k 0))
        (S' := pairedFunctions (Vertex L n k k)) T (iterAverageLinear L n k U) := by
  obtain ⟨T, hT, -, -⟩ := d.transposeProduct
  exact ⟨T, hT, d.vertex0.transposePreservesReal d.vertexTop
    (d.vertex0.isComplexification_of_eq (S' := pairedFunctions (Vertex L n k k))
      (F := iterAdjointCubeAverage L n k U k) hT fun f => d.iterAverageLinear_apply f)⟩
theorem average_comp_transpose (d : TransposeHypotheses U) (g : vertexFunctionSpace L n k k) :
    iterAverageLinear L n k U (iterAverageRealTranspose L n k U g) =
      ((L : ℝ) ^ (4 * k))⁻¹ • g := by
  obtain ⟨T, hT, -, hTT⟩ := d.transposeProduct
  have hc := d.vertex0.isComplexification_of_eq (S' := pairedFunctions (Vertex L n k k))
    (T₀ := iterAverageLinear L n k U)
    (F := iterAdjointCubeAverage L n k U k) hT fun f => d.iterAverageLinear_apply f
  let g' : (pairedFunctions (Vertex L n k k)).complexSubmodule :=
    ⟨g.1, d.vertexTop.mem_complex_of_mem_real g.1 g.2⟩
  have e1 := (d.vertex0.transpose_facts d.vertexTop hc).2 g g' rfl
  have e2 := hTT g'
  apply Subtype.ext
  rw [d.iterAverageLinear_apply]
  show iterAdjointCubeAverage L n k U k
    (PairedFunctionSpace.realTransposeMap (S := pairedFunctions (Vertex L n k 0))
      (S' := pairedFunctions (Vertex L n k k)) (iterAverageLinear L n k U) g).1 = _
  rw [e1, ← hT, e2, inverseFourthPowerWeight_pow]
  exact algebraMap_smul ℂ ((L : ℝ) ^ (4 * k))⁻¹ (g : Vertex L n k k → ComplexMatrix2)
theorem iterAverageLinear_surjective (d : TransposeHypotheses U) :
    Function.Surjective (iterAverageLinear L n k U) := by
  intro g
  refine ⟨((L : ℝ) ^ (4 * k)) • iterAverageRealTranspose L n k U g, ?_⟩
  rw [map_smul, d.average_comp_transpose, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ d.L_ne_zero), one_smul]
theorem iterCovariantDerivLinear_surjective (d : TransposeHypotheses U) :
    Function.Surjective (iterCovariantDerivLinear L n k U) := by
  intro C
  obtain ⟨B₀, hB₀, hC⟩ := d.complexIterDeriv_onto C C.2
  obtain ⟨N, hN⟩ := d.drift_exists_linear
  obtain ⟨l, hl⟩ := d.iterAverageLinear_surjective (N ⟨B₀, hB₀⟩)
  refine ⟨⟨B₀, hB₀⟩ - covDiffLinear L n k U l, ?_⟩
  apply Subtype.ext
  rw [map_sub, Submodule.coe_sub, d.iterCovariantDerivLinear_apply,
    d.iterCovariantDerivLinear_apply, d.covDiffLinear_apply,
    d.deriv_relation_forms B₀ (mem_complexEdgeForms_of_mem hB₀),
    d.deriv_relation_vertices _ fun x => traceless_of_mem (l.2 x trivial), hC]
  have e : iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → ComplexMatrix2) =
      iterContourLogDrift L n k U k B₀ := by
    rw [← d.iterAverageLinear_apply, hl, hN]
  rw [e]
  simp
theorem covDiffRealTranspose_symm (d : TransposeHypotheses U)
    (l l' : vertexFunctionSpace L n k 0) :
    traceFinsumPairing (l : Vertex L n k 0 → ComplexMatrix2)
        (covDiffRealTranspose L n k U (covDiffLinear L n k U l') :
          Vertex L n k 0 → ComplexMatrix2) =
      traceFinsumPairing
        (covDiffRealTranspose L n k U (covDiffLinear L n k U l) :
          Vertex L n k 0 → ComplexMatrix2) (l' : Vertex L n k 0 → ComplexMatrix2) := by
  have := d.finite_vertex0
  rw [tracePair_comm, d.covDiffRealTranspose_pair, d.covDiffRealTranspose_pair]
  exact d.edge0.pair_symm _ _
end TransposeHypotheses
end Transposes
section Terms
variable {L n k : ℕ}
theorem halfI_smul_bracket_mem {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    (Complex.I / 2) • ⁅X, Y⁆ ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · have hs : star (Complex.I / 2) = -(Complex.I / 2) := by
      simp [Complex.ext_iff]
      norm_num
    simp only [Ring.lie_def, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, ← hX.1, ← hY.1, hs]
    rw [neg_smul, ← smul_neg, neg_sub]
  · show Matrix.trace _ = 0
    rw [Matrix.trace_smul, Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self,
      smul_zero]
def bracketOnPositive (U : Edge L n k 0 → ComplexMatrix2) :
    (Vertex L n k 0 → ComplexMatrix2) →ₗ[ℝ] (Edge L n k 0 → ComplexMatrix2) →ₗ[ℝ]
      (PositiveEdge L n k 0 → ComplexMatrix2) :=
  LinearMap.mk₂ ℝ
    (fun l B b => (Complex.I / 2) •
      ⁅l b.1.source + ComplexMatrix2.conjugateBy (U b.1) (l b.1.target), B b.1⁆)
    (fun l l' B => by
      funext b
      simp only [Pi.add_apply, conjugateBy_add, Ring.lie_def, add_mul, mul_add]
      module)
    (fun c l B => by
      funext b
      simp only [Pi.smul_apply, conjugateBy_real_smul, Ring.lie_def, Matrix.smul_mul,
        Matrix.mul_smul, add_mul, mul_add, ← smul_add]
      module)
    (fun l B B' => by
      funext b
      simp only [Pi.add_apply, Ring.lie_def, add_mul, mul_add]
      module)
    (fun c l B => by
      funext b
      simp only [Pi.smul_apply, Ring.lie_def, Matrix.smul_mul, Matrix.mul_smul]
      module)
theorem restrictToPositiveEdges_bracketTerm (U : Edge L n k 0 → ComplexMatrix2)
    (l : Vertex L n k 0 → ComplexMatrix2) (B : Edge L n k 0 → ComplexMatrix2) :
    restrictToPositiveEdges (bracketTerm U l B) = bracketOnPositive U l B := by
  funext b
  exact extendOddly_of_pos (f := fun b : Edge L n k 0 =>
    (Complex.I / 2) • ⁅l b.source + ComplexMatrix2.conjugateBy (U b) (l b.target), B b⁆) b.2
theorem bracketOnPositive_mem (hP : OneLoop.PauliMatrixRelations)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    {l : Vertex L n k 0 → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0)
    (b : PositiveEdge L n k 0) :
    bracketOnPositive U l B b ∈ ComplexMatrix2.hermitianTraceless :=
  halfI_smul_bracket_mem
    (ComplexMatrix2.hermitianTraceless.add_mem (hl _)
      (conjugateBy_hermitianTraceless_of_mem hP (hU.1 b.1 trivial) (hl _)))
    (hB.1 b.1 b.2)
theorem tracePair_eq_ofReal_re {ι : Type*} [Finite ι] {f g : ι → ComplexMatrix2}
    (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless)
    (hg : ∀ i, g i ∈ ComplexMatrix2.hermitianTraceless) :
    traceFinsumPairing f g = (((traceFinsumPairing f g).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simpa using tracePair_im hf hg)
theorem termsRealValued (hP : OneLoop.PauliMatrixRelations)
    (hf : Finite (PositiveEdge L n k 0)) (hfk : Finite (PositiveEdge L n k k))
    (hr : OppositeFlipsOrientation L n k 0) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0)
    (hD : ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0,
      ∀ l : vertexFunctionSpace L n k 0,
        (T l : Edge L n k 0 → ComplexMatrix2) = covDiff U (l : Vertex L n k 0 → ComplexMatrix2))
    (hq : ∀ (B B' : edgeFormSpace L n k 0) (c : PositiveEdge L n k k),
      iterQuadraticTerm U B B' c ∈ ComplexMatrix2.hermitianTraceless) : TermsRealValued U := by
  obtain ⟨D, hDv⟩ := hD
  have hJ : ∀ {j : ℕ} (J : edgeFormSpace L n k j) (b : PositiveEdge L n k j),
      restrictToPositiveEdges (J : Edge L n k j → ComplexMatrix2) b ∈
        ComplexMatrix2.hermitianTraceless := fun J b => J.2.1 b.1 b.2
  have hcomm : ∀ {l : Vertex L n k 0 → ComplexMatrix2} {B : Edge L n k 0 → ComplexMatrix2},
      (∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) →
      B ∈ edgeFormSpace L n k 0 → ∀ (J : edgeFormSpace L n k 0),
      edgeFormPairing (J : Edge L n k 0 → ComplexMatrix2) (bracketTerm U l B) =
        ((tracePairBilin (PositiveEdge L n k 0)
          (restrictToPositiveEdges (J : Edge L n k 0 → ComplexMatrix2))
          (bracketOnPositive U l B) : ℝ) : ℂ) := by
    intro l B hl hB J
    show traceFinsumPairing _ (restrictToPositiveEdges (bracketTerm U l B)) = _
    rw [restrictToPositiveEdges_bracketTerm]
    exact tracePair_eq_ofReal_re (hJ J) (bracketOnPositive_mem hP hU hl hB)
  refine ⟨hq, fun l B => ?_, fun J σ => ?_, fun J σ => ?_, fun μ τ => ?_⟩
  · exact extendOddly_mem_edgeFormSpace hr fun b hb =>
      bracketOnPositive_mem hP hU (fun x => l.2 x trivial) B.2 ⟨b, hb⟩
  · refine isRealQuadratic_of_bilin
      ((((bracketOnPositive U).compl₁₂ ((vertexFunctionSpace L n k 0).subtype ∘ₗ σ)
        (edgeFormSpace L n k 0).subtype).compr₂
        (tracePairBilin (PositiveEdge L n k 0)
          (restrictToPositiveEdges (J : Edge L n k 0 → ComplexMatrix2))))) ?_
    intro B
    exact hcomm (fun x => (σ B).2 x trivial) B.2 J
  · refine isRealQuadratic_of_bilin
      ((((bracketOnPositive U).compl₁₂ ((vertexFunctionSpace L n k 0).subtype ∘ₗ σ)
        ((edgeFormSpace L n k 0).subtype ∘ₗ D ∘ₗ σ)).compr₂
        (tracePairBilin (PositiveEdge L n k 0)
          (restrictToPositiveEdges (J : Edge L n k 0 → ComplexMatrix2))))) ?_
    intro B
    have e := hDv (σ B)
    have := hcomm (l := (σ B : Vertex L n k 0 → ComplexMatrix2))
      (B := (D (σ B) : Edge L n k 0 → ComplexMatrix2)) (fun x => (σ B).2 x trivial) (D (σ B)).2 J
    rw [e] at this
    rw [this]
    simp [e]
  · refine isRealQuadratic_of_bilin
      (((iterQuadraticTerm U).compl₁₂ τ τ).compr₂
        (tracePairBilin (PositiveEdge L n k k)
          (restrictToPositiveEdges (μ : Edge L n k k → ComplexMatrix2)))) ?_
    intro B
    exact tracePair_eq_ofReal_re (hJ μ) (hq (τ B) (τ B))
theorem extendByZero_eq (g : Vertex L n k k → ComplexMatrix2) :
    RealLinearMaps.extendByZero (L := L) (m := n) (k := k) g = extendByZero g := by
  funext x
  unfold RealLinearMaps.extendByZero extendByZero
  by_cases h : (x : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k)
  · have h' : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x := ⟨⟨x, h⟩, rfl⟩
    rw [dif_pos h, dif_pos h']
    congr 1
    exact Subtype.ext h'.choose_spec.symm
  · have h' : ¬ ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x := by
      rintro ⟨y, e⟩
      exact h (e ▸ y.2)
    rw [dif_neg h, dif_neg h']
theorem existsUnique_symmetric_operator (hH : SymmetricOperator.SymmetricOperatorOfBilinForm)
    {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (c : InnerProductSpace.Core ℝ V) (Q : QuadraticForm ℝ V) :
    ∃! T : V →ₗ[ℝ] V, (∀ x y, c.inner x (T y) = c.inner (T x) y) ∧
      ∀ x, c.inner x (T x) = Q x := by
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore c.toCore
  haveI : FiniteDimensional ℝ V := ‹_›
  let β : LinearMap.BilinForm ℝ V := (1 / 2 : ℝ) • QuadraticMap.polarBilin Q
  have hβ : ∀ v, β v v = Q v := by
    intro v
    simp [β, QuadraticMap.polar_self]
  obtain ⟨T, ⟨hs, hd⟩, hu⟩ := hH.1 V β
  refine ⟨T, ⟨fun x y => ?_, fun x => ?_⟩, fun T' h => hu T' ⟨fun x y => ?_, fun x => ?_⟩⟩
  · exact (hs x y).symm
  · exact (hd x).trans (hβ x)
  · exact (h.1 x y).symm
  · exact (h.2 x).trans (hβ x).symm
end Terms
section Operator
variable {L n k : ℕ}
namespace TransposeHypotheses
variable {U : Edge L n k 0 → ComplexMatrix2}
theorem gaugeFixing_isRealQuadratic (d : TransposeHypotheses U) :
    IsRealQuadratic fun B : edgeFormSpace L n k 0 =>
      ((traceFinsumNorm (gaugeSliceResidual U B : Vertex L n k 0 → ComplexMatrix2) ^ 2 : ℝ) : ℂ) := by
  have := d.finite_vertex0
  let G : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0 :=
    covDiffRealTranspose L n k U - ((L : ℝ) ^ (4 * k)) •
      (iterAverageRealTranspose L n k U ∘ₗ iterAverageLinear L n k U ∘ₗ
        covDiffRealTranspose L n k U)
  refine isRealQuadratic_of_bilin
    ((tracePairBilin (Vertex L n k 0)).compl₁₂ ((vertexFunctionSpace L n k 0).subtype ∘ₗ G)
      ((vertexFunctionSpace L n k 0).subtype ∘ₗ G)) ?_
  intro B
  have hG : gaugeSliceResidual U B = G B := rfl
  rw [hG]
  congr 1
  have hm : ∀ x, (G B : Vertex L n k 0 → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
    fun x => (G B).2 x trivial
  rw [traceFinsumNorm, Real.sq_sqrt (tracePair_self_nonneg hm)]
  rfl
theorem transposeProperties (d : TransposeHypotheses U) : TransposeProperties U :=
  ⟨d.exists_average_transpose, d.average_comp_transpose, d.iterAverageLinear_surjective,
    d.iterCovariantDerivLinear_surjective, d.covDiffRealTranspose_symm,
    d.gaugeFixing_isRealQuadratic⟩
theorem exists_gaugeParameter_linear (d : TransposeHypotheses U)
    {r : (pairedFunctions (Vertex L n k 0)).realSubmodule →ₗ[ℝ]
      (pairedFunctions (Vertex L n k k)).realSubmodule}
    (hr : RealLinearMaps.RestrictionTranspose L n k r) :
    ∃ σ : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0, ∀ B : edgeFormSpace L n k 0,
      (σ B : Vertex L n k 0 → ComplexMatrix2) = RealLinearMaps.extendByZero
          (iterContourLogDrift L n k U k (B : Edge L n k 0 → ComplexMatrix2)) ∧
        (σ B : Vertex L n k 0 → ComplexMatrix2) = backgroundGaugeParameter U B := by
  obtain ⟨N, hN⟩ := d.drift_exists_linear
  refine ⟨PairedFunctionSpace.realTransposeMap r ∘ₗ N, fun B => ?_⟩
  have e : ((PairedFunctionSpace.realTransposeMap r ∘ₗ N) B).1 =
      RealLinearMaps.extendByZero (L := L) (m := n) (k := k)
        (iterContourLogDrift L n k U k (B : Edge L n k 0 → ComplexMatrix2)) :=
    (hr.transpose_eq_extendByZero (N B)).trans (congrArg _ (hN B))
  exact ⟨e, e.trans (extendByZero_eq _)⟩
theorem backgroundShift_eq (d : TransposeHypotheses U)
    {σ : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0}
    (hσ : ∀ B : edgeFormSpace L n k 0,
      (σ B : Vertex L n k 0 → ComplexMatrix2) = backgroundGaugeParameter U B)
    (B : edgeFormSpace L n k 0) :
    (backgroundShift L n k U B : Edge L n k 0 → ComplexMatrix2) =
      (B : Edge L n k 0 → ComplexMatrix2) + covDiff U (backgroundGaugeParameter U B) := by
  refine linearMapWithValues_apply
    (f := fun B => B + covDiff U (backgroundGaugeParameter U B))
    ⟨LinearMap.id + covDiffLinear L n k U ∘ₗ σ, fun B => ?_⟩ B
  show (B : Edge L n k 0 → ComplexMatrix2) + (covDiffLinear L n k U (σ B) : _) = _
  rw [d.covDiffLinear_apply, hσ]
theorem exists_hessian_quadratic (d : TransposeHypotheses U) (hT : TermsRealValued U)
    {σ : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0}
    (hσ : ∀ B : edgeFormSpace L n k 0,
      (σ B : Vertex L n k 0 → ComplexMatrix2) = backgroundGaugeParameter U B)
    (hA : IsRealQuadratic fun B : edgeFormSpace L n k 0 =>
      ((leftSecondDeriv (plaquetteAction L n k) U B B : ℝ) : ℂ))
    (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k) :
    ∃ Q : QuadraticForm ℝ (edgeFormSpace L n k 0),
      (∀ B, hessianFunction U J μ B = (Q B : ℂ)) ∧
        ∀ B, backgroundHessianForm U J μ B = Q B := by
  obtain ⟨Q₀, h₀⟩ := hA
  obtain ⟨Q₁, h₁⟩ := hT.bracket_isRealQuadratic J σ
  obtain ⟨Q₂, h₂⟩ := hT.bracket_covDiff_isRealQuadratic J σ
  obtain ⟨Q₃, h₃⟩ := hT.quadraticTerm_isRealQuadratic μ (backgroundShift L n k U)
  obtain ⟨Q₄, h₄⟩ := d.gaugeFixing_isRealQuadratic
  simp only [hσ] at h₁ h₂
  have h₀' : ∀ B : edgeFormSpace L n k 0,
      leftSecondDeriv (plaquetteAction L n k) U B B = Q₀ B := fun B =>
    Complex.ofReal_injective (h₀ B)
  have h₄' : ∀ B : edgeFormSpace L n k 0,
      traceFinsumNorm (gaugeSliceResidual U B : Vertex L n k 0 → ComplexMatrix2) ^ 2 = Q₄ B :=
    fun B => Complex.ofReal_injective (h₄ B)
  refine ⟨Q₀ + (2 : ℝ) • Q₁ + Q₂ - Q₃ + Q₄, fun B => ?_, fun B => ?_⟩
  · simp only [hessianFunction, h₀, h₁, h₂, h₃, h₄, QuadraticMap.add_apply,
      QuadraticMap.sub_apply, QuadraticMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  · simp only [backgroundHessianForm, sourceQuadraticForm, h₀', h₁, h₂, h₃, h₄',
      Complex.ofReal_re, QuadraticMap.add_apply, QuadraticMap.sub_apply,
      QuadraticMap.smul_apply, smul_eq_mul]
    ring
theorem backgroundOperatorProperties (hH : SymmetricOperator.SymmetricOperatorOfBilinForm)
    (d : TransposeHypotheses U) (hT : TermsRealValued U)
    {r : (pairedFunctions (Vertex L n k 0)).realSubmodule →ₗ[ℝ]
      (pairedFunctions (Vertex L n k k)).realSubmodule}
    (hr : RealLinearMaps.RestrictionTranspose L n k r)
    (hA : IsRealQuadratic fun B : edgeFormSpace L n k 0 =>
      ((leftSecondDeriv (plaquetteAction L n k) U B B : ℝ) : ℂ))
    (hfd : FiniteDimensional ℝ (edgeFormSpace L n k 0))
    (c : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0))
    (hc : ∀ B B' : edgeFormSpace L n k 0,
      edgeFormPairing (B : Edge L n k 0 → ComplexMatrix2) (B' : Edge L n k 0 → ComplexMatrix2) =
        ((c.inner B B' : ℝ) : ℂ)) : BackgroundOperatorProperties U := by
  obtain ⟨σ, hσ⟩ := d.exists_gaugeParameter_linear hr
  have hσ' := fun B => (hσ B).2
  refine ⟨⟨σ, hσ⟩, d.backgroundShift_eq hσ', fun J μ => ?_, fun J μ B => ?_, fun J μ => ?_⟩
  · obtain ⟨Q, h, -⟩ := d.exists_hessian_quadratic hT hσ' hA J μ
    exact ⟨Q, h⟩
  · obtain ⟨Q, h, h'⟩ := d.exists_hessian_quadratic hT hσ' hA J μ
    rw [h, h']
  · obtain ⟨Q, -, h'⟩ := d.exists_hessian_quadratic hT hσ' hA J μ
    obtain ⟨T, ⟨hs, hd⟩, hu⟩ := existsUnique_symmetric_operator hH c Q
    refine ⟨T, ⟨fun B B' => ?_, fun B => ?_⟩, fun X hX => hu X ⟨fun x y => ?_, fun x => ?_⟩⟩
    · rw [hc, hc, hs]
    · rw [hc, hd, h']
    · have := hX.1 x y
      rw [hc, hc] at this
      exact Complex.ofReal_injective this
    · have := hX.2 x
      rw [hc, h'] at this
      exact Complex.ofReal_injective this
end TransposeHypotheses
end Operator
section SecondDerivative
variable {L n k : ℕ}
open LeftChartSecondDerivative ActionFacts
theorem inv_mem_specialUnitary {W : ComplexMatrix2} (hW : W ∈ ComplexMatrix2.specialUnitary) :
    W⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem inv_inv_of_mem {W : ComplexMatrix2} (hW : W ∈ ComplexMatrix2.specialUnitary) :
    (W⁻¹)⁻¹ = W := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
theorem expTwist_of_pos {X U : Edge L n k 0 → ComplexMatrix2} {b : Edge L n k 0}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist X U b = ComplexMatrix2.matExp (Complex.I • X b) * U b := if_pos hb
theorem expTwist_of_not_pos {X U : Edge L n k 0 → ComplexMatrix2} {b : Edge L n k 0}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist X U b =
      (ComplexMatrix2.matExp (Complex.I • X b.opposite) * U b.opposite)⁻¹ :=
  if_neg hb
theorem expTwist_mem_fieldSpace (hC : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hr : OppositeFlipsOrientation L n k 0)
    {U X : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    (hX : X ∈ edgeFormSpace L n k 0) :
    PeriodicLattice.expTwist X U ∈ fieldSpace L n k 0 := by
  have hv := ((hC.2.2 L k 0 hL (Nat.zero_le k)).1 n hn).1.1.1 U hU X hX
  have hpos : ∀ b : Edge L n k 0, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • X b) * U b ∈ ComplexMatrix2.specialUnitary := by
    intro b hb
    have := (hv ⟨b, hb⟩).1 1
    simpa [LeftChartFields.leftExpMul, LeftChartFields.LatticeData.onPositive,
      LeftChartFields.finiteData] using this
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_of_pos hb]
      exact hpos b hb
    · rw [expTwist_of_not_pos hb]
      exact inv_mem_specialUnitary (hpos _ ((hr b).mpr hb))
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_of_not_pos (fun h => (hr b).mp h hb), expTwist_of_pos hb, opposite_opposite]
    · rw [expTwist_of_pos ((hr b).mpr hb), expTwist_of_not_pos hb]
      exact (inv_inv_of_mem (hpos _ ((hr b).mpr hb))).symm
def entryReImCoords {N : ℕ} (e : PositiveEdge L n k 0 → Fin N) (w : Fin N → ComplexMatrix2) :
    PositiveEdge L n k 0 × Fin 2 × Fin 2 × Bool → ℝ
  | (b, r, c, false) => (w (e b) r c).re
  | (b, r, c, true) => (w (e b) r c).im
theorem contDiff_matrixEntry {N : ℕ} (i : Fin N) (r c : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun w : Fin N → ComplexMatrix2 => w i r c := by
  let l : (Fin N → ComplexMatrix2) →ₗ[ℝ] ℂ :=
    { toFun := fun w => w i r c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap l).contDiff
theorem contDiff_entryReImCoords {N : ℕ} (e : PositiveEdge L n k 0 → Fin N)
    (p : PositiveEdge L n k 0 × Fin 2 × Fin 2 × Bool) :
    ContDiff ℝ (⊤ : ℕ∞) fun w : Fin N → ComplexMatrix2 => entryReImCoords e w p := by
  obtain ⟨b, r, c, fl⟩ := p
  cases fl
  · exact Complex.reCLM.contDiff.comp (contDiff_matrixEntry (e b) r c)
  · exact Complex.imCLM.contDiff.comp (contDiff_matrixEntry (e b) r c)
theorem contDiff_mvPolynomial_eval {N : ℕ} (e : PositiveEdge L n k 0 → Fin N)
    (P : MvPolynomial (PositiveEdge L n k 0 × Fin 2 × Fin 2 × Bool) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun w : Fin N → ComplexMatrix2 =>
      MvPolynomial.eval (entryReImCoords e w) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_entryReImCoords e i)
theorem hasDifferentiablePartialsOn_of_contDiff {N : ℕ} {f : (Fin N → ComplexMatrix2) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    EmbeddedSubmanifold.HasDifferentiablePartialsOn (specialUnitaryPower (Fin N))
      (specialUnitaryPower (Fin N)) f := by
  have hO : ComplexMatrix2.IsRelativelyOpen (specialUnitaryPower (Fin N))
      (specialUnitaryPower (Fin N)) :=
    ⟨Set.univ, isOpen_univ, by simp⟩
  have hc : ∀ c : EmbeddedSubmanifold.Chart (specialUnitaryPower (Fin N)),
      ContDiffOn ℝ (⊤ : ℕ∞) (c.pullback f) c.source := fun c =>
    hf.comp_contDiffOn (c.contDiffOn_param.of_le (by exact_mod_cast le_top))
  refine ⟨⟨hO, fun c => ?_⟩, fun c j => ?_⟩
  · exact ((hc c).differentiableOn (by simp)).mono Set.inter_subset_left
  · have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (c.pullback f)) c.source :=
      (hc c).fderiv_of_isOpen c.isOpen_source (by simp)
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun u => fderiv ℝ (c.pullback f) u (Pi.single j 1)) c.source :=
      h1.clm_apply contDiffOn_const
    exact (h2.differentiableOn (by simp)).mono Set.inter_subset_left
theorem real_smul_eq_algebraMap_smul {ι : Type*} (c : ℝ) (B : ι → ComplexMatrix2) :
    c • B = (algebraMap ℝ ℂ c) • B := (algebraMap_smul ℂ c B).symm
theorem leftSecondDeriv_isRealQuadratic (hS : LeftChartSecondDerivative.MainStatement)
    (hAct : ActionFacts.Statement) (hC : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hr : OppositeFlipsOrientation L n k 0)
    (hf : Finite (PositiveEdge L n k 0)) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) :
    IsRealQuadratic fun B : edgeFormSpace L n k 0 =>
      ((leftSecondDeriv (plaquetteAction L n k) U B B : ℝ) : ℂ) := by
  obtain ⟨P, hP⟩ := (hAct L k n hL hn).1.1
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (PositiveEdge L n k 0)
  have hpos : Nonempty (PositiveEdge L n k 0) := by
    let b : Edge L n k 0 := PeriodicLattice.Bond.forwardFrom 0 0
    rcases isPos_or_opposite_isPos b with h | h
    · exact ⟨⟨b, h⟩⟩
    · exact ⟨⟨b.opposite, h⟩⟩
  have hN : 1 ≤ N := by
    obtain ⟨p⟩ := hpos
    exact Nat.one_le_iff_ne_zero.mpr fun h => by
      subst h
      exact (e p).elim0
  let f : (Fin N → ComplexMatrix2) → ℝ := fun w => MvPolynomial.eval (entryReImCoords e w) P
  let bs : Fin N → Edge L n k 0 :=
    (fun b : PositiveEdge L n k 0 => (b.1 : Edge L n k 0)) ∘ e.symm
  have hO : specialUnitaryPower.IsOpenSubset (specialUnitaryPower (Fin N)) :=
    ⟨Set.univ, isOpen_univ, by simp⟩
  have hfacts : MixedPartialProperties ℝ (edgeFormSpace L n k 0 : Set (Edge L n k 0 → ComplexMatrix2))
      (specialUnitaryPower (Fin N)) f bs U :=
    ((hS L k 0 N hL (Nat.zero_le k) hN).1 n hn e.symm).1 _ f hO
      (hasDifferentiablePartialsOn_of_contDiff (contDiff_mvPolynomial_eval e P)) U hU
      (fun i => hU.1 _ trivial)
  obtain ⟨-, hl, hr', -, -⟩ := hfacts
  have hval : ∀ X ∈ edgeFormSpace L n k 0,
      plaquetteAction L n k (PeriodicLattice.expTwist X U) = chartValue f bs U X := by
    intro X hX
    rw [hP _ (expTwist_mem_fieldSpace hC hL hn hr hU hX)]
    have hcoord : ActionFacts.edgeEntryCoordinates (PeriodicLattice.expTwist X U) =
        entryReImCoords e (chartPoint bs U X) := by
      funext p
      obtain ⟨b, r, c, fl⟩ := p
      have e1 : PeriodicLattice.expTwist X U b.1 = chartPoint bs U X (e b) := by
        rw [expTwist_of_pos b.2]
        simp [chartPoint, bs]
      cases fl
      · simp [ActionFacts.edgeEntryCoordinates, entryReImCoords, e1]
      · simp [ActionFacts.edgeEntryCoordinates, entryReImCoords, e1]
    rw [hcoord]
    rfl
  have hsd : ∀ B B' : edgeFormSpace L n k 0, leftSecondDeriv (plaquetteAction L n k) U B B' =
      mixedAt ℝ f bs U (B : Edge L n k 0 → ComplexMatrix2) B' := by
    intro B B'
    show deriv _ 0 = deriv _ 0
    congr 1
    funext s
    congr 1
    funext t
    apply hval
    rw [← real_smul_eq_algebraMap_smul, ← real_smul_eq_algebraMap_smul]
    exact (edgeFormSpace L n k 0).add_mem ((edgeFormSpace L n k 0).smul_mem _ B.2)
      ((edgeFormSpace L n k 0).smul_mem _ B'.2)
  have hz : ∀ B' : edgeFormSpace L n k 0,
      mixedAt ℝ f bs U (0 : Edge L n k 0 → ComplexMatrix2) B' = 0 := by
    intro B'
    have := hl 0 (edgeFormSpace L n k 0).zero_mem 0 (edgeFormSpace L n k 0).zero_mem B' B'.2 1
    simpa using this
  have hz' : ∀ B : edgeFormSpace L n k 0,
      mixedAt ℝ f bs U (B : Edge L n k 0 → ComplexMatrix2) 0 = 0 := by
    intro B
    have := hr' B B.2 0 (edgeFormSpace L n k 0).zero_mem 0 (edgeFormSpace L n k 0).zero_mem 1
    simpa using this
  let β : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun B B' => mixedAt ℝ f bs U (B : Edge L n k 0 → ComplexMatrix2) B')
      (fun B₁ B₂ B' => by
        have := hl B₁ B₁.2 B₂ B₂.2 B' B'.2 1
        simpa using this)
      (fun c B B' => by
        have := hl B B.2 0 (edgeFormSpace L n k 0).zero_mem B' B'.2 c
        simp only [add_zero, hz] at this
        rw [← real_smul_eq_algebraMap_smul] at this
        simpa using this)
      (fun B B₁ B₂ => by
        have := hr' B B.2 B₁ B₁.2 B₂ B₂.2 1
        simpa using this)
      (fun c B B' => by
        have := hr' B B.2 B' B'.2 0 (edgeFormSpace L n k 0).zero_mem c
        simp only [add_zero, hz'] at this
        rw [← real_smul_eq_algebraMap_smul] at this
        simpa using this)
  exact isRealQuadratic_of_bilin β fun B => by rw [hsd B B]; rfl
end SecondDerivative
section Iterate
variable {L n k : ℕ}
open Filter Topology
theorem inv_eq_star_of_mem {W : ComplexMatrix2} (hW : W ∈ ComplexMatrix2.specialUnitary) :
    W⁻¹ = star W := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.inv_eq_star_of_mem_specialUnitary <;> assumption
theorem continuous_exp_complexMatrix2 :
    Continuous (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2) := by
  letI : NormedAlgebra ℚ ComplexMatrix2 := NormedAlgebra.restrictScalars ℚ ℂ ComplexMatrix2
  exact NormedSpace.exp_continuous
theorem tendsto_expTwist (hC : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hr : OppositeFlipsOrientation L n k 0)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0) :
    Tendsto (fun B : edgeFormSpace L n k 0 =>
        PeriodicLattice.expTwist (B : Edge L n k 0 → ComplexMatrix2) U)
      (𝓝 0) (𝓝[fieldSpace L n k 0] U) := by
  have hmem : ∀ B : edgeFormSpace L n k 0,
      PeriodicLattice.expTwist (B : Edge L n k 0 → ComplexMatrix2) U ∈ fieldSpace L n k 0 :=
    fun B => expTwist_mem_fieldSpace hC hL hn hr hU B.2
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hmem⟩
  have hcont : ∀ b' : Edge L n k 0, Continuous fun B : edgeFormSpace L n k 0 =>
      ComplexMatrix2.matExp (Complex.I • (B : Edge L n k 0 → ComplexMatrix2) b') * U b' := by
    intro b'
    have h1 : Continuous fun B : edgeFormSpace L n k 0 => (B : Edge L n k 0 → ComplexMatrix2) b' :=
      (continuous_apply b').comp continuous_subtype_val
    exact (continuous_exp_complexMatrix2.comp (h1.const_smul Complex.I)).mul continuous_const
  have h0 : ∀ b' : Edge L n k 0,
      ComplexMatrix2.matExp (Complex.I •
        ((0 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) b') * U b' = U b' := by
    intro b'
    simp
  refine tendsto_pi_nhds.mpr fun b => ?_
  by_cases hb : b.IsPositivelyOriented
  · simp only [expTwist_of_pos hb]
    exact (hcont b).tendsto' 0 (U b) (h0 b)
  · have hb' := (hr b).mpr hb
    have e : ∀ B : edgeFormSpace L n k 0,
        PeriodicLattice.expTwist (B : Edge L n k 0 → ComplexMatrix2) U b =
          star (ComplexMatrix2.matExp (Complex.I • (B : Edge L n k 0 → ComplexMatrix2) b.opposite) *
            U b.opposite) := by
      intro B
      have hm := (hmem B).1 b.opposite trivial
      rw [expTwist_of_pos hb'] at hm
      rw [expTwist_of_not_pos hb, inv_eq_star_of_mem hm]
    have e0 : U b = star (U b.opposite) := by
      have h1 := hU.2 b.opposite trivial
      rw [opposite_opposite] at h1
      rw [h1, inv_eq_star_of_mem (hU.1 _ trivial)]
    simp only [e]
    rw [e0]
    have hc : Continuous fun B : edgeFormSpace L n k 0 =>
        star (ComplexMatrix2.matExp (Complex.I • (B : Edge L n k 0 → ComplexMatrix2) b.opposite) *
          U b.opposite) :=
      continuous_star.comp (hcont b.opposite)
    exact hc.tendsto' 0 _ (by rw [h0])
theorem iterLogRatio_mem (hE : ComplexMatrix2.ExpLogEstimates)
    {U V : Edge L n k 0 → ComplexMatrix2} {B : Edge L n k 0 → ComplexMatrix2}
    (hV : V = PeriodicLattice.expTwist B U)
    (hreal : CovariantIterEqRealIterAt U) (hUk : smoothingIter L n k k U ∈ fieldSpace L n k k)
    (hreal' : CovariantIterEqRealIterAt V)
    (hVk : smoothingIter L n k k V ∈ fieldSpace L n k k) (c : PositiveEdge L n k k)
    (hlog : PeriodicLattice.complexBlockFieldAtLevel k V c *
        (PeriodicLattice.complexBlockFieldAtLevel k U c)⁻¹ ∈ ComplexMatrix2.logBall) :
    iterLogRatio U c B ∈ ComplexMatrix2.hermitianTraceless := by
  subst hV
  have w₁ : PeriodicLattice.complexBlockFieldAtLevel k (PeriodicLattice.expTwist B U) c ∈
      ComplexMatrix2.specialUnitary := by
    rw [hreal' c]
    exact hVk.1 c.1 trivial
  have w₀ : PeriodicLattice.complexBlockFieldAtLevel k U c ∈ ComplexMatrix2.specialUnitary := by
    rw [hreal c]
    exact hUk.1 c.1 trivial
  have hA := ComplexMatrix2.specialUnitary.mul_mem w₁ (inv_mem_specialUnitary w₀)
  obtain ⟨H, -, -, -, -, -, h⟩ := hE.2.2.2.2.2.2.2.1 _
    (Matrix.mem_specialUnitaryGroup_iff.mp hA).1 hlog
  obtain ⟨-, -, ⟨Y, hY, e⟩, -⟩ := h (Matrix.mem_specialUnitaryGroup_iff.mp hA).2
  unfold iterLogRatio
  rw [e, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  exact hY
theorem isClosed_hermitianTraceless :
    IsClosed (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.LeftChartFields.isClosed_hermitianTraceless <;> assumption
theorem edgeFormNorm_smul (hf : Finite (PositiveEdge L n k 0)) (t : ℝ)
    (B : edgeFormSpace L n k 0) :
    edgeFormNorm ((t • B : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
      |t| * edgeFormNorm (B : Edge L n k 0 → ComplexMatrix2) := by
  have e : restrictToPositiveEdges ((t • B : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
      (t : ℂ) • restrictToPositiveEdges (B : Edge L n k 0 → ComplexMatrix2) := by
    funext b
    exact (algebraMap_smul ℂ t ((B : Edge L n k 0 → ComplexMatrix2) b.1)).symm
  unfold edgeFormNorm traceFinsumNorm
  rw [e, tracePair_smul_left, tracePair_comm, tracePair_smul_left, tracePair_comm]
  have : ((t : ℂ) * ((t : ℂ) *
      traceFinsumPairing (restrictToPositiveEdges (B : Edge L n k 0 → ComplexMatrix2))
        (restrictToPositiveEdges (B : Edge L n k 0 → ComplexMatrix2)))).re =
      t * t * (traceFinsumPairing (restrictToPositiveEdges (B : Edge L n k 0 → ComplexMatrix2))
        (restrictToPositiveEdges (B : Edge L n k 0 → ComplexMatrix2))).re := by
    simp [Complex.mul_re]
    ring
  rw [this, Real.sqrt_mul (mul_self_nonneg t), Real.sqrt_mul_self_eq_abs]
end Iterate
section Expansion
variable {L n k : ℕ}
open Filter Topology
theorem norm_real_smul_complexMatrix2 (t : ℝ) (X : ComplexMatrix2) : ‖t • X‖ = |t| * ‖X‖ := by
  rw [← algebraMap_smul ℂ t X, norm_smul]
  simp
theorem iterQuadraticTerm_diag_mem (hf : Finite (PositiveEdge L n k 0))
    {U : Edge L n k 0 → ComplexMatrix2}
    (hexp : IsIterQuadraticExpansion U (iterQuadraticTerm U))
    {T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k}
    (hT : ∀ B : edgeFormSpace L n k 0, (T B : Edge L n k k → ComplexMatrix2) =
      complexIterDeriv L n k k U (B : Edge L n k 0 → ComplexMatrix2))
    (c : PositiveEdge L n k k)
    (hev : ∀ᶠ B : edgeFormSpace L n k 0 in 𝓝 0,
      iterLogRatio U c (B : Edge L n k 0 → ComplexMatrix2) ∈ ComplexMatrix2.hermitianTraceless)
    (B : edgeFormSpace L n k 0) :
    iterQuadraticTerm U B B c ∈ ComplexMatrix2.hermitianTraceless := by
  obtain ⟨C, hC⟩ := hexp.2 c
  set q := iterQuadraticTerm U with hqdef
  have ht : Tendsto (fun t : ℝ => t • B) (𝓝[≠] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => t • B) (𝓝 0) (𝓝 ((0 : ℝ) • B)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 := ht.eventually hC
  have h2 := ht.eventually hev
  set b := edgeFormNorm (B : Edge L n k 0 → ComplexMatrix2) with hb
  set Y : ComplexMatrix2 := (T B : Edge L n k k → ComplexMatrix2) c with hY
  have hYm : Y ∈ ComplexMatrix2.hermitianTraceless := (T B).2.1 c.1 c.2
  let g : ℝ → ComplexMatrix2 := fun t =>
    (t ^ 2)⁻¹ • (iterLogRatio U c ((t • B : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) -
      t • Y)
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖g t - (1 / 2 : ℝ) • q B B c‖ ≤ C * b ^ 3 * |t| := by
    filter_upwards [h1, self_mem_nhdsWithin] with t ht1 ht0
    have ht0' : t ≠ 0 := ht0
    have e1 : complexIterDeriv L n k k U
        ((t • B : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) c = t • Y := by
      rw [← hT, map_smul]
      rfl
    have e2 : q (t • B) (t • B) c = (t * t) • q B B c := by
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_smul]
    rw [e1, e2, edgeFormNorm_smul hf] at ht1
    have e3 : g t - (1 / 2 : ℝ) • q B B c = (t ^ 2)⁻¹ •
        (iterLogRatio U c ((t • B : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) -
          t • Y - (1 / 2 : ℝ) • (t * t) • q B B c) := by
      have e4 : (t ^ 2)⁻¹ • (1 / 2 : ℝ) • (t * t) • q B B c = (1 / 2 : ℝ) • q B B c := by
        rw [smul_smul, smul_smul]
        congr 1
        field_simp
      rw [smul_sub _ _ ((1 / 2 : ℝ) • (t * t) • q B B c), e4]
    rw [e3, norm_real_smul_complexMatrix2]
    have hp : 0 < t ^ 2 := by positivity
    rw [abs_of_pos (inv_pos.mpr hp)]
    have hle := mul_le_mul_of_nonneg_left ht1 (inv_pos.mpr hp).le
    refine hle.trans (le_of_eq ?_)
    have hne : |t| ≠ 0 := abs_ne_zero.mpr ht0'
    rw [← sq_abs t]
    field_simp
    rw [hb]
  have hz : Tendsto (fun t : ℝ => C * b ^ 3 * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => C * b ^ 3 * |t|) (𝓝 0) (𝓝 (C * b ^ 3 * |(0 : ℝ)|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simp only [abs_zero, mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hg : Tendsto g (𝓝[≠] 0) (𝓝 ((1 / 2 : ℝ) • q B B c)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) hbound hz
  have hm : ∀ᶠ t in 𝓝[≠] (0 : ℝ), g t ∈ (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) := by
    filter_upwards [h2] with t ht2
    exact ComplexMatrix2.hermitianTraceless.smul_mem _
      (ComplexMatrix2.hermitianTraceless.sub_mem ht2
        (ComplexMatrix2.hermitianTraceless.smul_mem _ hYm))
  have hlim := isClosed_hermitianTraceless.mem_of_tendsto hg hm
  have := ComplexMatrix2.hermitianTraceless.smul_mem (2 : ℝ) hlim
  rwa [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] at this
theorem iterQuadraticTerm_mem {U : Edge L n k 0 → ComplexMatrix2}
    (hsym : ∀ B B' : edgeFormSpace L n k 0, iterQuadraticTerm U B B' = iterQuadraticTerm U B' B)
    {c : PositiveEdge L n k k}
    (hd : ∀ B : edgeFormSpace L n k 0, iterQuadraticTerm U B B c ∈ ComplexMatrix2.hermitianTraceless)
    (B B' : edgeFormSpace L n k 0) :
    iterQuadraticTerm U B B' c ∈ ComplexMatrix2.hermitianTraceless := by
  set q := iterQuadraticTerm U
  have e : q (B + B') (B + B') c = q B B c + (2 : ℝ) • q B B' c + q B' B' c := by
    have := hsym B' B
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, this, two_smul]
    abel
  have e' : q B B' c = (1 / 2 : ℝ) • (q (B + B') (B + B') c - q B B c - q B' B' c) := by
    rw [e]
    have : q B B c + (2 : ℝ) • q B B' c + q B' B' c - q B B c - q B' B' c =
        (2 : ℝ) • q B B' c := by abel
    rw [this, smul_smul]
    norm_num
  rw [e']
  exact ComplexMatrix2.hermitianTraceless.smul_mem _
    (ComplexMatrix2.hermitianTraceless.sub_mem
      (ComplexMatrix2.hermitianTraceless.sub_mem (hd _) (hd _)) (hd _))
theorem eq_of_eq_on_positive {j : ℕ} {f g F G : Edge L n k j → ComplexMatrix2}
    (hF : F = extendOddly f) (hG : G = extendOddly g)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → F b = G b) : F = G := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · rcases isPos_or_opposite_isPos b with h' | h'
    · exact absurd h' hb
    · have e := h _ h'
      rw [hF, hG, extendOddly_of_pos h', extendOddly_of_pos h'] at e
      rw [hF, hG, extendOddly_of_not_pos hb, extendOddly_of_not_pos hb, e]
theorem complexIterDeriv_eq_leftDifferential {U : Edge L n k 0 → ComplexMatrix2}
    (he : ∀ᶠ B : edgeFormSpace L n k 0 in 𝓝 0,
      CovariantIterEqRealIterAt (PeriodicLattice.expTwist (B : Edge L n k 0 → ComplexMatrix2) U))
    (hreal : CovariantIterEqRealIterAt U)
    (hfirst : IterDerivIsLinearTaylorTerm U) (B : edgeFormSpace L n k 0)
    (hd : ∀ c : Edge L n k k, c.IsPositivelyOriented →
      HasDerivAt (fun t : ℝ => ComplexMatrix2.logSeries (smoothingIter L n k k
          (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2)) U) c *
            (smoothingIter L n k k U c)⁻¹))
        (Complex.I • leftDifferential (smoothingIter L n k k) U B c) 0) :
    complexIterDeriv L n k k U B = leftDifferential (smoothingIter L n k k) U B := by
  refine eq_of_eq_on_positive
    (f := fun c => logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexBlockFieldAtLevel k (PeriodicLattice.expTwist X U) c)
      (PeriodicLattice.complexBlockFieldAtLevel k U c) B)
    (g := fun c => logDirectionalDeriv ℝ
      (fun X => smoothingIter L n k k (PeriodicLattice.expTwist X U) c)
      (smoothingIter L n k k U c) B) rfl rfl fun c hc => ?_
  have ht : Tendsto (fun t : ℝ => t • B) (𝓝 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => t • B) (𝓝 0) (𝓝 ((0 : ℝ) • B)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rwa [zero_smul] at h0
  have ev : (fun t : ℝ => iterLogRatio U ⟨c, hc⟩ ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2)))
      =ᶠ[𝓝 0] fun t : ℝ => Complex.I⁻¹ • ComplexMatrix2.logSeries (smoothingIter L n k k
          (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2)) U) c *
            (smoothingIter L n k k U c)⁻¹) := by
    filter_upwards [ht.eventually he] with t h
    have e : ((t • B : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
        (t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2) :=
      (algebraMap_smul ℂ t (B : Edge L n k 0 → ComplexMatrix2)).symm
    rw [e] at h
    unfold iterLogRatio
    rw [h ⟨c, hc⟩, hreal ⟨c, hc⟩]
  have hder : HasDerivAt
      (fun t : ℝ => iterLogRatio U ⟨c, hc⟩ ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2)))
      (leftDifferential (smoothingIter L n k k) U B c) 0 := by
    have h := (hd c hc).const_smul Complex.I⁻¹
    rw [smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul] at h
    exact h.congr_of_eventuallyEq ev
  have := (hfirst B ⟨c, hc⟩).2
  rw [hder.deriv] at this
  exact this.symm
end Expansion
open Filter Topology in
theorem realQuadraticTransposes_holds
    (hSym : SymmetricOperator.SymmetricOperatorOfBilinForm)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hExp : IterLeftChartExpansion)
    (hFib : SmoothingFibres)
    (hProp : CovariantSmoothingProperties.Statement)
    (hFormed : LevelwiseMeans.LevelwiseMeansHold)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hG : FiniteSideFormSpaces)
    (hPl : FaceSums.FacesAndPairings)
    (hC : LeftChartFields.Claim)
    (hS : LeftChartSecondDerivative.MainStatement)
    (hAct : ActionFacts.Statement)
    (hPauli : OneLoop.PauliMatrixRelations)
    (hE : ComplexMatrix2.ExpLogEstimates) : Statement := by
  intro L n k hL hn hk
  have hflip : ∀ i ≤ k, OppositeFlipsOrientation L n k i := fun i hi =>
    oppositeFlipsOrientation hA hL hn hi
  have hG' := fun i (hi : i ≤ k) => hG L n k i hL hn hi
  have hbond : ∀ i ≤ k, IsFinDimEuclidean (edgePairedSpace L n k i) := fun i hi =>
    isFinDimEuclidean_edgePairedSpace (hG' i hi).1 (hG' i hi).2.1
  have hsiteFin : ∀ i ≤ k, Finite (Vertex L n k i) := fun i hi =>
    Set.finite_univ_iff.mp (((hPl L hL k i hi).1 n hn).2.1 Set.univ).2.1
  have hsite : ∀ i ≤ k, IsFinDimEuclidean (pairedFunctions (Vertex L n k i)) := fun i hi => by
    haveI := hsiteFin i hi
    exact isFinDimEuclidean_pairedFunctions _
  have hL0 : (L : ℝ) ≠ 0 := by
    have : L ≠ 0 := by
      have := hL.2
      omega
    exact_mod_cast this
  obtain ⟨hsteps, htower⟩ := hY L n k hL hn hk
  refine ⟨covDiffTransposePreservesReal_of hflip hsite hbond htower.covDiff_isLinear, ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have h0 : 0 ≤ i + 1 := Nat.zero_le _
  have st := hsteps i (Nat.lt_succ_self i)
  have hrel := (((hProp L hL).1 n (i + 1) hn).2 (i + 1) le_rfl).1
  obtain ⟨r, -, hr⟩ := htower.exists_restriction
  have hside := (hFormed L hL (i + 1) hk).1 n hn
  have hfib := (hFib L n (i + 1) i hL hn (Nat.lt_succ_self i)).2.2.1
  have hnear : ∀ᶠ U in 𝓝[fieldSpace L n (i + 1) 0] (fun _ => (1 : ComplexMatrix2)),
      ∀ᶠ V in 𝓝[fieldSpace L n (i + 1) 0] U,
        smoothingIter L n (i + 1) (i + 1) V ∈ fieldSpace L n (i + 1) (i + 1) :=
    eventually_eventually_nhdsWithin.mpr
      (Eventually.mono hside.iterates_defined fun U h => (h (i + 1) le_rfl).1)
  show ∀ᶠ U in 𝓝[fieldSpace L n (i + 1) 0] (fun _ => (1 : ComplexMatrix2)), _
  filter_upwards [self_mem_nhdsWithin, hExp L n (i + 1) hL hn hk, hfib,
    hside.iterates_defined, hnear, st.iterAdjointCubeAverage_isLinear,
    st.iterCovariantDeriv_isLinear, st.iterContourLogDrift_isLinear,
    st.complexIterDeriv_isLinear] with U hU he hon hfm hnr hav hcv hdr hcq
  obtain ⟨⟨hsm, hreal, hev, -⟩, hfirst, hsec⟩ := he
  have hUk := (hfm (i + 1) le_rfl).1
  have hnr' := (tendsto_expTwist hC hL hn (hflip 0 h0) hU).eventually hnr
  obtain ⟨Q, hQ⟩ := hcq
  have hexpn := hsec.2.1
  have hdiag : ∀ (c : PositiveEdge L n (i + 1) (i + 1)) (B : edgeFormSpace L n (i + 1) 0),
      iterQuadraticTerm U B B c ∈ ComplexMatrix2.hermitianTraceless := fun c =>
    iterQuadraticTerm_diag_mem (hG' 0 h0).1 hexpn hQ c (by
      filter_upwards [hev, hnr'] with B h₁ h₂
      exact iterLogRatio_mem hE rfl hreal hUk h₁.2.1 h₂ c (h₁.2.2 c))
  have hq : ∀ (B B' : edgeFormSpace L n (i + 1) 0) (c : PositiveEdge L n (i + 1) (i + 1)),
      iterQuadraticTerm U B B' c ∈ ComplexMatrix2.hermitianTraceless := fun B B' c =>
    iterQuadraticTerm_mem hexpn.1 (hdiag c) B B'
  have hdiff := htower.covDiff_isLinear 0 h0 U hU
  have terms : TermsRealValued U :=
    termsRealValued hPauli (hG' 0 h0).1 (hG' (i + 1) le_rfl).1 (hflip 0 h0) hU hdiff hq
  have honto : ∀ C ∈ edgeFormSpace L n (i + 1) (i + 1), ∃ B ∈ edgeFormSpace L n (i + 1) 0,
      complexIterDeriv L n (i + 1) (i + 1) U B = C := by
    intro C hC'
    obtain ⟨B, hB, h⟩ := hon C hC'
    refine ⟨B, hB, ?_⟩
    have e := complexIterDeriv_eq_leftDifferential (B := ⟨B, hB⟩) (hev.mono fun _ h => h.2.1)
      hreal hfirst (fun c hc => (((hfm (i + 1) le_rfl).2.2.2 B hB c hc).1))
    exact e.trans h
  have hPU := hrel U hsm
  have d : TransposeHypotheses U :=
    { vertex0 := hsite 0 h0
      vertexTop := hsite (i + 1) le_rfl
      edge0 := hbond 0 h0
      finite_vertex0 := hsiteFin 0 h0
      oppositeFlips0 := hflip 0 h0
      L_ne_zero := hL0
      mem_fieldSpace := hU
      covDiff_exists_linear := hdiff
      average_exists_linear := hav
      covariantDeriv_exists_linear := hcv
      drift_exists_linear := hdr
      deriv_relation_forms := hPU.1
      deriv_relation_vertices := fun l hl => (hPU.2.1 l hl).2
      transposeProduct := hPU.2.2
      complexIterDeriv_onto := honto }
  obtain ⟨c, hc⟩ := (hG' 0 h0).2.2.2
  exact ⟨terms, d.transposeProperties, d.backgroundOperatorProperties hSym terms hr
    (leftSecondDeriv_isRealQuadratic hS hAct hC hL hn (hflip 0 h0) (hG' 0 h0).1 hU)
    (hG' 0 h0).2.1 c hc⟩
end Tower.RealQuadraticTransposes
end YangMills.Construction
end
