import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASideProof
import YangMills.Construction.Towers.BackgroundGaugeFunctionalIsFormedAtTheTrivialPoint
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOneProof
import YangMills.Construction.Towers.TheActionOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
namespace TrivialFieldGauge
open Matrices
theorem saddleDetOfCores_ne_zero {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (c : InnerProductSpace.Core ℝ V) (c' : InnerProductSpace.Core ℝ W) (X : V →ₗ[ℝ] V)
    (M : V →ₗ[ℝ] W) (hM : Function.Surjective M)
    (hX : ∀ B, M B = 0 → c.inner B (X B) = 0 → B = 0) :
    GaussianConstraint.saddleDetOfCores c c' X M ≠ 0 := by
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c.toCore
  let := c'.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c'.toCore
  unfold GaussianConstraint.saddleDetOfCores
  have hinj : Function.Injective (GaussianConstraint.saddlePointOperator X M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ h
    have h₁ : X x + LinearMap.adjoint M y = 0 := congrArg Prod.fst h
    have h₂ : M x = 0 := congrArg Prod.snd h
    have h₃ : inner ℝ x (X x) = 0 := by
      rw [eq_neg_of_add_eq_zero_left h₁, inner_neg_right, LinearMap.adjoint_inner_right, h₂,
        inner_zero_left, neg_zero]
    have hx : x = 0 := hX x h₂ h₃
    subst hx
    have h₄ : LinearMap.adjoint M y = 0 := by simpa using h₁
    obtain ⟨z, rfl⟩ := hM y
    have h₅ : inner ℝ (M z) (M z) = 0 := by
      rw [← LinearMap.adjoint_inner_right, h₄, inner_zero_right]
    rw [inner_self_eq_zero] at h₅
    rw [h₅]
    rfl
  have hdet := (LinearEquiv.ofInjectiveEndo _ hinj).isUnit_det'
  have hcoe : ((LinearEquiv.ofInjectiveEndo _ hinj : _ ≃ₗ[ℝ] _) : _ →ₗ[ℝ] _) =
      GaussianConstraint.saddlePointOperator X M := LinearMap.ext fun _ => rfl
  rw [hcoe] at hdet
  exact hdet.ne_zero
section Functions
variable {ι : Type} [Fintype ι]
def lieValue (f : GroupLieProduct.hermitianTracelessFunctions ι) (i : ι) :
    ComplexMatrix2.LieElement :=
  ⟨(f : ι → ComplexMatrix2) i, f.2 i (Set.mem_univ i)⟩
@[instance_reducible]
def sumInnerCore : InnerProductSpace.Core ℝ (GroupLieProduct.hermitianTracelessFunctions ι) where
  inner f g := ∑ i, ComplexMatrix2.LieElement.innerProductCore.inner (lieValue f i) (lieValue g i)
  conj_inner_symm f g := by
    simp only [conj_trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    simpa using ComplexMatrix2.LieElement.innerProductCore.conj_inner_symm (lieValue f i) (lieValue g i)
  re_inner_nonneg f := by
    simp only [RCLike.re_to_real]
    exact Finset.sum_nonneg fun i _ =>
      ComplexMatrix2.LieElement.innerProductCore.re_inner_nonneg (lieValue f i)
  add_left f f' g := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      ComplexMatrix2.LieElement.innerProductCore.add_left (lieValue f i) (lieValue f' i) (lieValue g i)
  smul_left f g c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      ComplexMatrix2.LieElement.innerProductCore.smul_left (lieValue f i) (lieValue g i) c
  definite f h := by
    have h₀ := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      ComplexMatrix2.LieElement.innerProductCore.re_inner_nonneg (lieValue f i)).mp h
    refine Subtype.ext (funext fun i => ?_)
    have := ComplexMatrix2.LieElement.innerProductCore.definite _ (h₀ i (Finset.mem_univ i))
    exact congrArg ComplexMatrix2.LieElement.toMatrix this
theorem traceFinsumPairing_eq_inner (f g : GroupLieProduct.hermitianTracelessFunctions ι) :
    traceFinsumPairing (f : ι → ComplexMatrix2) (g : ι → ComplexMatrix2) =
      (((sumInnerCore (ι := ι)).inner f g : ℝ) : ℂ) := by
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_fintype]
  show ∑ i, _ =
    ((∑ i, ComplexMatrix2.LieElement.innerProductCore.inner (lieValue f i) (lieValue g i) : ℝ) : ℂ)
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have him : (ComplexMatrix2.fullTrace ((lieValue f i).toMatrix * (lieValue g i).toMatrix)).im = 0 :=
    Complex.conj_eq_iff_im.mp (ComplexMatrix2.LieElement.star_fullTrace_mul (lieValue f i) (lieValue g i))
  apply Complex.ext
  · rw [Complex.ofReal_re]
    rfl
  · show (ComplexMatrix2.halfTrace ((lieValue f i).toMatrix * (lieValue g i).toMatrix)).im = _
    simp [ComplexMatrix2.halfTrace, him]
theorem eq_zero_of_traceFinsumNorm_eq_zero (f : GroupLieProduct.hermitianTracelessFunctions ι)
    (h : traceFinsumNorm (f : ι → ComplexMatrix2) = 0) : f = 0 := by
  have h₁ : (traceFinsumPairing (f : ι → ComplexMatrix2) (f : ι → ComplexMatrix2)).re ≤ 0 :=
    Real.sqrt_eq_zero'.mp h
  rw [traceFinsumPairing_eq_inner, Complex.ofReal_re] at h₁
  have h₂ : 0 ≤ (sumInnerCore (ι := ι)).inner f f := (sumInnerCore (ι := ι)).re_inner_nonneg f
  exact (sumInnerCore (ι := ι)).definite f (le_antisymm h₁ h₂)
end Functions
section Vertices
variable {L n k j : ℕ}
theorem vertex_eq_sum_unitSteps (y : Vertex L n k j) : ∃ z : Fin 4 → ℤ,
    y = ∑ μ, z μ • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ := by
  obtain ⟨z, hz⟩ := y.2
  refine ⟨z, Subtype.ext (funext fun ν => ?_)⟩
  rw [AddSubgroup.val_finsetSum, Finset.sum_apply, hz ν, Finset.sum_eq_single ν]
  · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
  · intro μ _ h
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h.symm]
  · simp
theorem eq_of_vertexCoboundary_eq_zero {l : Vertex L n k j → ComplexMatrix2}
    (h : vertexCoboundary l = 0) (y : Vertex L n k j) : l y = l 0 := by
  let S : AddSubgroup (Vertex L n k j) :=
    { carrier := {s | ∀ x, l (x + s) = l x}
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      zero_mem' := fun x => by simp
      neg_mem' := fun {a} ha x => by
        have := ha (x + -a)
        simpa using this.symm }
  have hstep : ∀ μ, PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ ∈ S :=
    fun μ x => by
      have := congrFun h (PeriodicLattice.Bond.forwardFrom x μ)
      exact sub_eq_zero.mp this
  obtain ⟨z, hz⟩ := vertex_eq_sum_unitSteps y
  have hy : y ∈ S := hz ▸ S.sum_mem fun μ _ => S.zsmul_mem (hstep μ) (z μ)
  simpa using hy 0
theorem forwardFrom_isPositivelyOriented (x : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
theorem edgeForm_eq_zero_of_forward {a : Edge L n k j → ComplexMatrix2}
    (ha : a ∈ edgeFormSpace L n k j)
    (h : ∀ (x : Vertex L n k j) (μ : Fin 4), a (PeriodicLattice.Bond.forwardFrom x μ) = 0) :
    a = 0 := by
  funext b
  obtain ⟨μ, e | e⟩ := b.isNeighbour
  · have : b = PeriodicLattice.Bond.forwardFrom b.source μ :=
      PeriodicLattice.Bond.ext rfl (by simp [PeriodicLattice.Bond.forwardFrom, ← e])
    rw [this]
    exact h _ _
  · have : b.opposite = PeriodicLattice.Bond.forwardFrom b.target μ :=
      PeriodicLattice.Bond.ext rfl (by
        simp only [PeriodicLattice.Bond.opposite, PeriodicLattice.Bond.forwardFrom]
        rw [← neg_eq_iff_eq_neg.mpr e]
        abel)
    have h₁ := ha.2 b
    rw [this, h] at h₁
    exact neg_eq_zero.mp h₁.symm
theorem setAverage_const {ι : Type*} {S : Set ι} (hS : S.Finite) (hne : S.Nonempty)
    (c : ComplexMatrix2) :
    TrivialLinearization.setAverage S (fun _ => c) = c := by
  unfold TrivialLinearization.setAverage
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_const, Set.ncard_eq_toFinset_card S hS,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  simpa [Finset.card_eq_zero] using hne.ne_empty
theorem baseVerticesOfCube_nonempty (hB : PeriodicLattice.BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {m : ℕ} (hm : m ≤ k)
    (y : Vertex L n k m) :
    (TrivialLinearization.baseVerticesOfCube L n k m y).Nonempty := by
  have hj : -(n : ℤ) ≤ PeriodicLattice.levelDepth k m := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have h := (hB L n hL hn (PeriodicLattice.levelDepth k m) m 0 hj).2.1.1 y
  have hmem : (y : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k 0) := by
    have h₂ := h.2
    have he : PeriodicLattice.levelDepth k m + (m : ℤ) = PeriodicLattice.levelDepth k 0 := by
      simp only [PeriodicLattice.levelDepth]
      omega
    rwa [he] at h₂
  exact ⟨⟨y, hmem⟩, h⟩
end Vertices
section Iterates
variable {L n k : ℕ}
theorem crossingSmoothingIter_vertexCoboundary
    (hS : ∀ j < k, TrivialLinearization.OneStepIdentities L n k j)
    (hmem : ∀ m ≤ k, ∀ l ∈ vertexFunctionSpace L n k 0,
      vertexSmoothingIter L n k m l ∈ vertexFunctionSpace L n k m)
    {l : Vertex L n k 0 → ComplexMatrix2} (hl : l ∈ vertexFunctionSpace L n k 0) :
    ∀ m ≤ k, crossingSmoothingIter L n k m (vertexCoboundary l) =
      vertexCoboundary (vertexSmoothingIter L n k m l) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have h := ih (by omega)
    show crossingSmoothing L n k m (crossingSmoothingIter L n k m (vertexCoboundary l)) =
      vertexCoboundary (vertexSmoothing L n k m (vertexSmoothingIter L n k m l))
    rw [h]
    exact ((hS m (by omega)).2 _ (hmem m (by omega) l hl)).2.1
theorem crossingSmoothingIter_constant
    (hC : ∀ j < k, TrivialLinearization.OneStepConstantForms L n k j)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0)
    {a : Fin 4 → ComplexMatrix2}
    (ha : ∀ (x : Vertex L n k 0) (μ : Fin 4), B (PeriodicLattice.Bond.forwardFrom x μ) = a μ) :
    ∀ m ≤ k, crossingSmoothingIter L n k m B ∈ edgeFormSpace L n k m ∧
      ∀ (x : Vertex L n k m) (μ : Fin 4),
        crossingSmoothingIter L n k m B (PeriodicLattice.Bond.forwardFrom x μ) =
          (L : ℂ) ^ m • a μ := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨hB, fun x μ => by rw [pow_zero, one_smul]; exact ha x μ⟩
  | succ m ih =>
    intro hm
    obtain ⟨h₁, h₂⟩ := ih (by omega)
    obtain ⟨-, -, -, h₃, h₄⟩ := hC m (by omega) _ h₁ (fun μ => (L : ℂ) ^ m • a μ) h₂
    refine ⟨h₃, fun x μ => ?_⟩
    have h₅ := h₄ x μ
    rw [smul_smul, ← pow_succ'] at h₅
    exact h₅
end Iterates
section AtTrivial
variable (L n k : ℕ)
abbrev coboundaryAtTrivial : vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 :=
  covDiffLinear L n k (trivialField L n k 0)
abbrev coboundaryTransposeAtTrivial : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0 :=
  covDiffRealTranspose L n k (trivialField L n k 0)
abbrev averageAtTrivial : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k :=
  iterAverageLinear L n k (trivialField L n k 0)
abbrev averageTransposeAtTrivial : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0 :=
  iterAverageRealTranspose L n k (trivialField L n k 0)
abbrev derivAtTrivial : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k :=
  iterCovariantDerivLinear L n k (trivialField L n k 0)
variable {L n k}
structure KernelData (cs : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0))
    (cs' : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k))
    (cb : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)) : Prop where
  coboundary_apply : ∀ l : vertexFunctionSpace L n k 0,
    (coboundaryAtTrivial L n k l : Edge L n k 0 → ComplexMatrix2) =
      vertexCoboundary (l : Vertex L n k 0 → ComplexMatrix2)
  average_apply : ∀ l : vertexFunctionSpace L n k 0,
    (averageAtTrivial L n k l : Vertex L n k k → ComplexMatrix2) =
      vertexSmoothingIter L n k k (l : Vertex L n k 0 → ComplexMatrix2)
  deriv_apply : ∀ B : edgeFormSpace L n k 0,
    (derivAtTrivial L n k B : Edge L n k k → ComplexMatrix2) =
      crossingSmoothingIter L n k k (B : Edge L n k 0 → ComplexMatrix2)
  coboundary_transpose : ∀ (g : edgeFormSpace L n k 0) (f : vertexFunctionSpace L n k 0),
    cs.inner (coboundaryTransposeAtTrivial L n k g) f = cb.inner g (coboundaryAtTrivial L n k f)
  average_transpose : ∀ (g : vertexFunctionSpace L n k k) (f : vertexFunctionSpace L n k 0),
    cs.inner (averageTransposeAtTrivial L n k g) f = cs'.inner g (averageAtTrivial L n k f)
  average_const : ∀ c ∈ ComplexMatrix2.hermitianTraceless,
    vertexSmoothingIter L n k k (fun _ => c) = fun _ => c
  closed : ∀ B ∈ edgeFormSpace L n k 0, IsClosedEdgeForm B →
    ∃ l ∈ vertexFunctionSpace L n k 0, ∃ a ∈ edgeFormSpace L n k 0,
      IsTranslationInvariantEdgeForm a ∧ B = vertexCoboundary l + a
  smoothing_coboundary : ∀ l ∈ vertexFunctionSpace L n k 0,
    crossingSmoothingIter L n k k (vertexCoboundary l) =
      vertexCoboundary (vertexSmoothingIter L n k k l)
  smoothing_const : ∀ B ∈ edgeFormSpace L n k 0, ∀ a : Fin 4 → ComplexMatrix2,
    (∀ (x : Vertex L n k 0) (μ : Fin 4), B (PeriodicLattice.Bond.forwardFrom x μ) = a μ) →
    ∀ (x : Vertex L n k k) (μ : Fin 4),
      crossingSmoothingIter L n k k B (PeriodicLattice.Bond.forwardFrom x μ) = (L : ℂ) ^ k • a μ
  finite_vertices : Finite (Vertex L n k k)
  pos : 0 < L
variable {cs : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)}
  {cs' : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k)}
  {cb : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)}
def constVertexFunction (c : ComplexMatrix2) (hc : c ∈ ComplexMatrix2.hermitianTraceless) :
    vertexFunctionSpace L n k 0 :=
  ⟨fun _ => c, fun _ _ => hc⟩
theorem coboundary_constVertexFunction (h : KernelData cs cs' cb) (c : ComplexMatrix2)
    (hc : c ∈ ComplexMatrix2.hermitianTraceless) :
    coboundaryAtTrivial L n k (constVertexFunction c hc) = 0 := by
  refine Subtype.ext ?_
  rw [h.coboundary_apply]
  funext b
  simp [vertexCoboundary, constVertexFunction]
theorem vertex_kernel_trivial (h : KernelData cs cs' cb) (l : vertexFunctionSpace L n k 0)
    (hA : averageAtTrivial L n k l = 0)
    (hX : cs.inner l (coboundaryTransposeAtTrivial L n k (coboundaryAtTrivial L n k l)) = 0) :
    l = 0 := by
  have h₁ : cb.inner (coboundaryAtTrivial L n k l) (coboundaryAtTrivial L n k l) = 0 := by
    rw [← h.coboundary_transpose]
    have := cs.conj_inner_symm l (coboundaryTransposeAtTrivial L n k (coboundaryAtTrivial L n k l))
    simp only [conj_trivial] at this
    rw [this, hX]
  have h₂ : coboundaryAtTrivial L n k l = 0 := cb.definite _ h₁
  have h₃ : vertexCoboundary (l : Vertex L n k 0 → ComplexMatrix2) = 0 := by
    rw [← h.coboundary_apply, h₂]
    rfl
  have h₄ : (l : Vertex L n k 0 → ComplexMatrix2) = fun _ => (l : Vertex L n k 0 → ComplexMatrix2) 0 :=
    funext fun y => eq_of_vertexCoboundary_eq_zero h₃ y
  have hc : (l : Vertex L n k 0 → ComplexMatrix2) 0 ∈ ComplexMatrix2.hermitianTraceless :=
    l.2 0 (Set.mem_univ _)
  have h₅ := h.average_apply l
  rw [hA, h₄, h.average_const _ hc] at h₅
  have h₆ : (l : Vertex L n k 0 → ComplexMatrix2) 0 = 0 := (congrFun h₅ 0).symm
  refine Subtype.ext ?_
  rw [h₄, h₆]
  rfl
theorem edge_kernel_trivial (h : KernelData cs cs' cb) (B : edgeFormSpace L n k 0)
    (hQ : derivAtTrivial L n k B = 0) (hcl : IsClosedEdgeForm (B : Edge L n k 0 → ComplexMatrix2))
    (hg : coboundaryTransposeAtTrivial L n k B =
      ((L : ℝ) ^ (4 * k)) • averageTransposeAtTrivial L n k
        (averageAtTrivial L n k (coboundaryTransposeAtTrivial L n k B))) : B = 0 := by
  obtain ⟨l, hl, a, ha, hac, hBa⟩ := h.closed _ B.2 hcl
  have hB : B = coboundaryAtTrivial L n k ⟨l, hl⟩ + ⟨a, ha⟩ := by
    refine Subtype.ext ?_
    rw [Submodule.coe_add, h.coboundary_apply]
    exact hBa
  have hz : derivAtTrivial L n k (coboundaryAtTrivial L n k ⟨l, hl⟩) +
      derivAtTrivial L n k ⟨a, ha⟩ = 0 := by
    rw [← map_add, ← hB, hQ]
  have hd : (derivAtTrivial L n k (coboundaryAtTrivial L n k ⟨l, hl⟩) : Edge L n k k → ComplexMatrix2) =
      vertexCoboundary (vertexSmoothingIter L n k k l) := by
    rw [h.deriv_apply, h.coboundary_apply]
    exact h.smoothing_coboundary l hl
  have hv : ∀ (x : Vertex L n k k) (μ : Fin 4),
      vertexSmoothingIter L n k k l (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ) =
        vertexSmoothingIter L n k k l x -
          (L : ℂ) ^ k • a (PeriodicLattice.Bond.forwardFrom 0 μ) := by
    intro x μ
    have h₁ := congrFun (congrArg Subtype.val hz) (PeriodicLattice.Bond.forwardFrom x μ)
    rw [Submodule.coe_add, Pi.add_apply, hd, h.deriv_apply] at h₁
    rw [h.smoothing_const a ha (fun μ => a (PeriodicLattice.Bond.forwardFrom 0 μ))
      (fun y μ => hac μ y 0) x μ] at h₁
    have h₂ : vertexCoboundary (vertexSmoothingIter L n k k l) (PeriodicLattice.Bond.forwardFrom x μ) =
        vertexSmoothingIter L n k k l
            (x + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ) -
          vertexSmoothingIter L n k k l x := rfl
    rw [h₂] at h₁
    have h₃ : ((0 : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2)
        (PeriodicLattice.Bond.forwardFrom x μ) = 0 := rfl
    rw [h₃] at h₁
    refine eq_sub_of_add_eq (sub_eq_zero.mp ?_)
    rw [← h₁]
    abel
  have hN : ∀ (N : ℕ) (x : Vertex L n k k) (μ : Fin 4),
      vertexSmoothingIter L n k k l
          (x + N • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ) =
        vertexSmoothingIter L n k k l x -
          N • ((L : ℂ) ^ k • a (PeriodicLattice.Bond.forwardFrom 0 μ)) := by
    intro N x μ
    induction N with
    | zero => simp
    | succ N ih =>
      rw [succ_nsmul, ← add_assoc, hv, ih, succ_nsmul]
      abel
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast h.pos.ne'
  have hfin := h.finite_vertices
  have hcard : 0 < Nat.card (Vertex L n k k) := Nat.card_pos
  have ha₀ : ∀ μ : Fin 4, a (PeriodicLattice.Bond.forwardFrom 0 μ) = 0 := by
    intro μ
    have h₁ := hN (Nat.card (Vertex L n k k)) 0 μ
    rw [card_nsmul_eq_zero', add_zero] at h₁
    have h₂ : Nat.card (Vertex L n k k) •
        ((L : ℂ) ^ k • a (PeriodicLattice.Bond.forwardFrom 0 μ)) = 0 :=
      sub_eq_self.mp h₁.symm
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_eq_zero] at h₂
    rcases h₂ with h₂ | h₂
    · exact absurd h₂ (mul_ne_zero (Nat.cast_ne_zero.mpr hcard.ne') (pow_ne_zero _ hL))
    · exact h₂
  have haz : a = 0 := edgeForm_eq_zero_of_forward ha fun x μ => by rw [hac μ x 0, ha₀]
  have hB₁ : B = coboundaryAtTrivial L n k ⟨l, hl⟩ := by
    rw [hB]
    have : (⟨a, ha⟩ : edgeFormSpace L n k 0) = 0 := Subtype.ext haz
    rw [this, add_zero]
  have hf : vertexCoboundary (vertexSmoothingIter L n k k l) = 0 := by
    rw [← hd, ← hB₁, hQ]
    rfl
  have hc : vertexSmoothingIter L n k k l 0 ∈ ComplexMatrix2.hermitianTraceless := by
    have := (averageAtTrivial L n k ⟨l, hl⟩).2 0 (Set.mem_univ _)
    rwa [h.average_apply] at this
  have hA : averageAtTrivial L n k ⟨l, hl⟩ =
      averageAtTrivial L n k (constVertexFunction _ hc) := by
    refine Subtype.ext ?_
    rw [h.average_apply, h.average_apply,
      show ((constVertexFunction _ hc : vertexFunctionSpace L n k 0) :
          Vertex L n k 0 → ComplexMatrix2) =
        fun _ => vertexSmoothingIter L n k k l 0 from rfl, h.average_const _ hc]
    exact funext fun y => eq_of_vertexCoboundary_eq_zero hf y
  have hs : ∀ f : vertexFunctionSpace L n k 0, cs.inner (coboundaryTransposeAtTrivial L n k B) f =
      (L : ℝ) ^ (4 * k) *
        cs'.inner (averageAtTrivial L n k (coboundaryTransposeAtTrivial L n k B))
          (averageAtTrivial L n k f) := by
    intro f
    conv_lhs => rw [hg]
    rw [cs.smul_left, h.average_transpose]
    simp
  have hfin₀ : cb.inner B B = 0 := by
    conv_lhs => rw [show cb.inner B B = cb.inner B (coboundaryAtTrivial L n k ⟨l, hl⟩) by
      rw [← hB₁]]
    rw [← h.coboundary_transpose, hs, hA, ← hs, h.coboundary_transpose,
      coboundary_constVertexFunction h _ hc]
    have h₁ := cb.smul_left 0 B 0
    have h₂ := cb.conj_inner_symm B 0
    simp only [smul_zero, map_zero, zero_mul, conj_trivial] at h₁ h₂
    rw [← h₂, h₁]
  exact cb.definite _ hfin₀
end AtTrivial
section Spaces
theorem trivialField_mem (L n k j : ℕ) : trivialField L n k j ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.trivialField_mem <;> assumption
theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → ComplexMatrix2)}
    {p' : Submodule ℝ (β → ComplexMatrix2)} {f : (α → ComplexMatrix2) → β → ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
variable {L n k j : ℕ}
theorem finite_vertices (hP : FaceSums.FacesAndPairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Finite (Vertex L n k j) :=
  Set.finite_univ_iff.mp (((hP L hL k j hj).1 n hn).2.1 Set.univ).2.1
theorem finite_faces (hP : FaceSums.FacesAndPairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Finite (Face L n k j) :=
  Set.finite_univ_iff.mp (((hP L hL k j hj).1 n hn).2.2.2 Set.univ).2.1
theorem vertexFunctionsEuclidean_of (hP : FaceSums.FacesAndPairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    VertexFunctionsEuclidean L n k j := by
  have := finite_vertices hP hL hn hj
  let := Fintype.ofFinite (Vertex L n k j)
  refine ⟨inferInstance, sumInnerCore, fun l l' => ?_⟩
  rw [traceFinsumPairing_eq_inner, Complex.ofReal_re]
theorem edgeFormsEuclidean_of (hS : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    EdgeFormsEuclidean L n k j := by
  obtain ⟨-, f, -, c, h⟩ := hS L n k j hL hn hj
  exact ⟨f, c, fun B B' => by rw [h B B', Complex.ofReal_re]⟩
theorem traceFinsumPairing_zero_left {ι : Type*} (f : ι → ComplexMatrix2) :
    traceFinsumPairing (0 : ι → ComplexMatrix2) f = 0 := by
  simp [traceFinsumPairing, ComplexMatrix2.halfTrace]
theorem sourceQuadraticForm_zero (U : Edge L n k 0 → ComplexMatrix2) (B : edgeFormSpace L n k 0) :
    sourceQuadraticForm U 0 0 B = 0 := by
  have h₁ : ∀ C : Edge L n k 0 → ComplexMatrix2,
      edgeFormPairing (0 : Edge L n k 0 → ComplexMatrix2) C = 0 :=
    fun C => traceFinsumPairing_zero_left _
  have h₂ : ∀ C : PositiveEdge L n k k → ComplexMatrix2,
      traceFinsumPairing (restrictToPositiveEdges (0 : Edge L n k k → ComplexMatrix2)) C = 0 :=
    fun C => traceFinsumPairing_zero_left _
  simp [sourceQuadraticForm, h₁, h₂]
end Spaces
end TrivialFieldGauge
open Matrices TrivialFieldGauge in
theorem BackgroundFunctionalWellDefinedAtTrivialField.holds
    (hQ : RealQuadraticTransposes.Statement)
    (hC : TrivialFieldAverages.AtTrivialField)
    (hR : TrivialLinearization.AllRelationsStatement)
    (hCl : ClosedEdgeFormsOnPeriodicLattice)
    (hAct : ActionFacts.Statement)
    (hF : LeftChartFacts.HoldEverywhere)
    (hB : PeriodicLattice.BlockPartition.Properties)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hP : FaceSums.FacesAndPairings)
    (hS : FiniteSideFormSpaces) :
    BackgroundFunctionalWellDefinedAtTrivialField := by
  intro L n k hL hn hk
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have hL₀ : 0 < L := by
    have := hL.2
    omega
  have h₁ := trivialField_mem L n (i + 1) 0
  obtain ⟨hDT, hnear⟩ := hQ L n (i + 1) hL hn hk
  obtain ⟨-, hTr, hOp⟩ := hnear.self_of_nhdsWithin h₁
  obtain ⟨-, hIt, -, -⟩ := (hC L hL).1 n (i + 1) hn (by omega)
  obtain ⟨hAt, hTower⟩ := hY L n (i + 1) hL hn hk
  have hRel : ∀ j < i + 1, _ := fun j hj => (hR L hL).1 n (i + 1) j (i + 1) hn hj le_rfl
  obtain ⟨-, hFn, -⟩ := hF L (i + 1) 0 0 0 hL (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨-, -, -, hGD, -⟩ := hFn n hn
  have hmem : ∀ m ≤ i + 1, ∀ l ∈ vertexFunctionSpace L n (i + 1) 0,
      vertexSmoothingIter L n (i + 1) m l ∈ vertexFunctionSpace L n (i + 1) m := by
    intro m hm l hl
    cases m with
    | zero => exact hl
    | succ m =>
      obtain ⟨T, hT⟩ := (hAt m (by omega)).iterAdjointCubeAverage_isLinear.self_of_nhdsWithin h₁
      have h₂ := (T ⟨l, hl⟩).2
      rw [hT] at h₂
      rwa [(hIt (m + 1) hm).2 l hl] at h₂
  have hfin₀ := finite_vertices (k := i + 1) (j := 0) hP hL hn (Nat.zero_le _)
  have hSS : VertexFunctionsEuclidean L n (i + 1) 0 ∧
      VertexFunctionsEuclidean L n (i + 1) (i + 1) :=
    ⟨vertexFunctionsEuclidean_of hP hL hn (Nat.zero_le _), vertexFunctionsEuclidean_of hP hL hn le_rfl⟩
  have hFF : EdgeFormsEuclidean L n (i + 1) 0 ∧ EdgeFormsEuclidean L n (i + 1) (i + 1) :=
    ⟨edgeFormsEuclidean_of hS hL hn (Nat.zero_le _), edgeFormsEuclidean_of hS hL hn le_rfl⟩
  have hData : KernelData hSS.1.2.choose hSS.2.2.choose hFF.1.2.choose :=
    { coboundary_apply := fun l => by
        rw [← hGD.2]
        exact linearMapWithValues_apply
          (hTower.covDiff_isLinear 0 (Nat.zero_le _) _ h₁) l
      average_apply := fun l => by
        rw [← (hIt (i + 1) le_rfl).2 _ l.2]
        exact linearMapWithValues_apply
          ((hAt i (by omega)).iterAdjointCubeAverage_isLinear.self_of_nhdsWithin h₁) l
      deriv_apply := fun B => by
        rw [← ((hIt (i + 1) le_rfl).1 _ B.2).2.1]
        exact linearMapWithValues_apply
          ((hAt i (by omega)).iterCovariantDeriv_isLinear.self_of_nhdsWithin h₁) B
      coboundary_transpose := fun g f => by
        obtain ⟨T, -, hK⟩ := hDT 0 (Nat.zero_le _) _ h₁
        rw [hSS.1.2.choose_spec, hFF.1.2.choose_spec]
        exact congrArg Complex.re (hK.2.2 g f)
      average_transpose := fun g f => by
        obtain ⟨T, -, hK⟩ := hTr.average_transpose
        rw [hSS.1.2.choose_spec, hSS.2.2.choose_spec]
        exact congrArg Complex.re (hK.2.2 g f)
      average_const := fun c hc => by
        funext y
        have hmean := (hRel i (by omega)).2.2.2.2.2.2 (fun _ => c) (fun _ _ => hc) y
        rw [hmean]
        exact setAverage_const (Set.toFinite _)
          (baseVerticesOfCube_nonempty hB hL hn le_rfl y) c
      closed := fun B hB' hcl => (hCl L n (i + 1) 0 hL hn (Nat.zero_le _) B hB').mp hcl
      smoothing_coboundary := fun l hl =>
        crossingSmoothingIter_vertexCoboundary (fun j hj => (hRel j hj).1) hmem hl (i + 1) le_rfl
      smoothing_const := fun B hB' a ha =>
        (crossingSmoothingIter_constant (fun j hj => (hRel j hj).2.1) hB' ha (i + 1) le_rfl).2
      finite_vertices := finite_vertices hP hL hn le_rfl
      pos := hL₀ }
  refine ⟨?_, ?_⟩
  · unfold hessianSaddleDet saddleDetOnEdgeForms
    rw [dif_pos hFF]
    have := hFF.1.1
    have := hFF.2.1
    refine saddleDetOfCores_ne_zero _ _ _ _ hTr.covariantDeriv_surjective
      fun B hBk hX => ?_
    have hspec : IsBackgroundHessian (trivialField L n (i + 1) 0) 0 0
        (backgroundHessian (trivialField L n (i + 1) 0) 0 0) :=
      Classical.epsilon_spec (hOp.existsUnique_hessian 0 0).exists
    have hq : backgroundHessianForm (trivialField L n (i + 1) 0) 0 0 B = 0 := by
      rw [hFF.1.2.choose_spec, hspec.2 B, Complex.ofReal_re] at hX
      exact hX
    have hsd : leftSecondDeriv (plaquetteAction L n (i + 1)) (trivialField L n (i + 1) 0)
        (B : Edge L n (i + 1) 0 → ComplexMatrix2) (B : Edge L n (i + 1) 0 → ComplexMatrix2) =
        traceFinsumNorm (edgeCoboundary (B : Edge L n (i + 1) 0 → ComplexMatrix2)) ^ 2 :=
      (hAct L (i + 1) n hL hn).2.2.2.2.2.2 B B.2
    unfold backgroundHessianForm at hq
    rw [sourceQuadraticForm_zero, add_zero, hsd] at hq
    have hz := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hq
    have hplaq := pow_eq_zero_iff (two_ne_zero) |>.mp hz.1
    have hgauge := pow_eq_zero_iff (two_ne_zero) |>.mp hz.2
    have hfp := finite_faces (k := i + 1) (j := 0) hP hL hn (Nat.zero_le _)
    let := Fintype.ofFinite (Face L n (i + 1) 0)
    let := Fintype.ofFinite (Vertex L n (i + 1) 0)
    have hdB : edgeCoboundary (B : Edge L n (i + 1) 0 → ComplexMatrix2) ∈
        faceFunctionSpace L n (i + 1) 0 := by
      intro p _
      have hpos := fun (x : Vertex L n (i + 1) 0) (μ : Fin 4) =>
        B.2.1 (PeriodicLattice.Bond.forwardFrom x μ) (forwardFrom_isPositivelyOriented x μ)
      exact ComplexMatrix2.hermitianTraceless.sub_mem
        (ComplexMatrix2.hermitianTraceless.sub_mem
          (ComplexMatrix2.hermitianTraceless.add_mem (hpos _ _) (hpos _ _)) (hpos _ _))
        (hpos _ _)
    have hcl : IsClosedEdgeForm (B : Edge L n (i + 1) 0 → ComplexMatrix2) :=
      congrArg Subtype.val (eq_zero_of_traceFinsumNorm_eq_zero ⟨_, hdB⟩ hplaq)
    have hg := eq_zero_of_traceFinsumNorm_eq_zero _ hgauge
    exact edge_kernel_trivial hData B hBk hcl (sub_eq_zero.mp hg)
  · unfold ghostSaddleDet saddleDetOnVertexFunctions
    rw [dif_pos hSS]
    have := hSS.1.1
    have := hSS.2.1
    exact saddleDetOfCores_ne_zero _ _ _ _ hTr.average_surjective
      fun l hl hX => vertex_kernel_trivial hData l hl hX
end YangMills.Construction.Tower
end
