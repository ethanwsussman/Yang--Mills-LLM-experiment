import YangMills.Construction.Towers.EntriesOfTheSaddleOperatorAreRealAnalyticNearOneProof
import YangMills.Construction.Towers.NormaliserIsPositiveNearOne
import YangMills.Construction.Towers.NormaliserIsRealAnalyticNearOne
import YangMills.Construction.Towers.TheFormOnAFibreOfTheCriticalBranch
import YangMills.Construction.Towers.TheSaddleDeterminant
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
namespace NormaliserAnalyticity
open Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces Coordinates PeriodicLattice
section Holomorphic
variable {R S : Type} [Fintype R] [Fintype S]
theorem isHolomorphicToCoords_comp (hH : ExpChartHolomorphy.ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {𝒳 : Set (R ⊕ S → ComplexMatrix2)}
    {Φ : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates 1}
    (hΦ : IsHolomorphicToCoords b (Equiv.refl (ComplexCoordinates 1)) 𝒳 Φ) {Ω : Set ℂ}
    (hΩ : IsOpen Ω) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h Ω) :
    IsHolomorphicToCoords b (Equiv.refl (ComplexCoordinates 1))
      (𝒳 ∩ (fun q => Φ q 0) ⁻¹' Ω)
      (fun q _ => h (Φ q 0) : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates 1) := by
  obtain ⟨hop, hcont, hloc⟩ := hΦ
  have hΩ₀ : IsOpen {v : ComplexCoordinates 1 | v 0 ∈ Ω} := hΩ.preimage (continuous_apply 0)
  have hcont' : ContinuousOn Φ 𝒳 := hcont
  have hT := (hH.2.1 (R ⊕ S)).1
  have hloc₀ := (hH.2.2.2.1 R S).1
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨O₀, hO₀, rfl⟩ := hop
    obtain ⟨u, hu, he⟩ := (continuousOn_iff'.1 hcont') _ hΩ₀
    refine ⟨u ∩ O₀, hu.inter hO₀, ?_⟩
    ext q
    constructor
    · rintro ⟨hq, hq'⟩
      have : q ∈ Φ ⁻¹' {v : ComplexCoordinates 1 | v 0 ∈ Ω} ∩ (O₀ ∩ GroupLieProduct R S) :=
        ⟨hq', hq⟩
      rw [he] at this
      exact ⟨⟨this.1, hq.1⟩, hq.2⟩
    · rintro ⟨⟨hq₁, hq₂⟩, hq₃⟩
      have : q ∈ u ∩ (O₀ ∩ GroupLieProduct R S) := ⟨hq₁, hq₂, hq₃⟩
      rw [← he] at this
      exact ⟨this.2, this.1⟩
  · have h1 : ContinuousOn (fun q => Φ q 0) (𝒳 ∩ (fun q => Φ q 0) ⁻¹' Ω) :=
      (continuousOn_pi.1 (hcont'.mono inter_subset_left)) 0
    have h2 : ContinuousOn (fun q => h (Φ q 0)) (𝒳 ∩ (fun q => Φ q 0) ⁻¹' Ω) :=
      hh.continuousOn.comp h1 fun q hq => hq.2
    exact continuousOn_pi.2 fun _ => h2
  · intro p hp
    obtain ⟨O, h0, hex, hO, hhol⟩ := hloc p hp.1
    have hpp : p ∈ GroupLieProduct R S := by
      obtain ⟨O₀, -, e⟩ := hop
      have := hp.1
      rw [e] at this
      exact this.2
    have hzero : expChartAt p 0 = p := (hloc₀ p hpp).2.2.2.1
    set ψ : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates 1 := Φ ∘ expChartAt p with hψ
    have hOsub : O ∩ {A | ψ A 0 ∈ Ω} ⊆ tracelessPi (R ⊕ S) := fun A hA => hO.1 hA.1
    have hpre : ∀ ν : R ⊕ S ≃ Fin (Fintype.card (R ⊕ S)),
        IsOpen (tupleOfCoords b ν ⁻¹' (O ∩ {A | ψ A 0 ∈ Ω})) := by
      intro ν
      obtain ⟨ho, hc, -⟩ := hhol ν
      have := ContinuousOn.isOpen_inter_preimage hc ho hΩ₀
      exact this
    refine ⟨O ∩ {A | ψ A 0 ∈ Ω}, ⟨h0, ?_⟩, fun A hA => ⟨hex A hA.1, hA.2⟩, ?_, ?_⟩
    · change Φ (expChartAt p 0) 0 ∈ Ω
      rw [hzero]
      exact hp.2
    · exact ((hT _ hOsub).2 b (Fintype.equivFin _)).2 (hpre _)
    · intro ν
      obtain ⟨ho, hc, hd⟩ := hhol ν
      have hopen := hpre ν
      refine ⟨hopen, ?_, ?_⟩
      · have h1 : ContinuousOn (fun z => ψ (tupleOfCoords b ν z) 0)
            (tupleOfCoords b ν ⁻¹' (O ∩ {A | ψ A 0 ∈ Ω})) :=
          (continuousOn_pi.1 (ContinuousOn.mono hc fun z hz => hz.1)) 0
        have h2 : ContinuousOn (fun z => h (ψ (tupleOfCoords b ν z) 0))
            (tupleOfCoords b ν ⁻¹' (O ∩ {A | ψ A 0 ∈ Ω})) :=
          hh.continuousOn.comp h1 fun z hz => hz.2
        exact continuousOn_pi.2 fun _ => h2
      · intro a ha j
        have hnear : ∀ᶠ ζ : ℂ in 𝓝 (0 : ℂ), a + ζ • ComplexCoordinates.stdBasisVector j ∈
            tupleOfCoords b ν ⁻¹' (O ∩ {A | ψ A 0 ∈ Ω}) := by
          have hc' : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by
            fun_prop
          refine hc'.continuousAt.eventually_mem (hopen.mem_nhds ?_)
          simpa using ha
        filter_upwards [(hd a ha.1 j), hnear] with ζ h₁ h₂
        have d₀ : DifferentiableAt ℂ
            (fun ζ : ℂ => ψ (tupleOfCoords b ν (a + ζ • ComplexCoordinates.stdBasisVector j)) 0) ζ :=
          (differentiableAt_pi.1 h₁) 0
        have dh : DifferentiableAt ℂ h
            (ψ (tupleOfCoords b ν (a + ζ • ComplexCoordinates.stdBasisVector j)) 0) :=
          hh.differentiableAt (hΩ.mem_nhds h₂.2)
        exact differentiableAt_pi.2 fun _ => dh.comp ζ d₀
theorem isSubspaceAnalyticToCoords_comp (hH : ExpChartHolomorphy.ExpChartTheory)
    {E : Submodule ℝ (S → ComplexMatrix2)} {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    {f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates 1} (hf : IsSubspaceAnalyticToCoords E 𝒲 f)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h Ω)
    (hmap : ∀ p ∈ 𝒲, f p 0 ∈ Ω) :
    IsSubspaceAnalyticToCoords E 𝒲
      (fun p _ => h (f p 0) : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates 1) := by
  refine ⟨hf.1, fun p hp => ?_⟩
  obtain ⟨𝒳, h1, h2, h3, Φ, hΦ, he⟩ := hf.2 p hp
  have hpp : p ∈ subspaceTimesGroup E R := by
    obtain ⟨O, -, e⟩ := hf.1.2
    have := hp
    rw [e] at this
    exact this.2
  have hfull := fun b => isHolomorphicToCoords_comp hH (hΦ b) hΩ hh
  refine ⟨𝒳 ∩ (fun q => Φ q 0) ⁻¹' Ω, ⟨h1, ?_⟩, (hfull OneLoop.pauliBasis).1, ?_,
    fun q _ => h (Φ q 0), hfull, ?_⟩
  · change Φ p 0 ∈ Ω
    rw [he ⟨h1, hpp⟩]
    exact hmap p hp
  · exact fun q hq => h3 ⟨hq.1.1, hq.2⟩
  · intro q hq
    have e₁ := he ⟨hq.1.1, hq.2⟩
    change (fun _ => h (Φ q 0)) = fun _ => h (f q 0)
    rw [e₁]
end Holomorphic
section Bases
variable {V V' : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup V'] [Module ℝ V'] [FiniteDimensional ℝ V']
def saddleBlockMatrix (c : InnerProductSpace.Core ℝ V') {d₁ d₂ : ℕ} (e : Fin d₁ → V)
    (f : Fin d₂ → V') (M : V →ₗ[ℝ] V') (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) ℝ :=
  Matrix.fromBlocks (Matrix.of fun a b => Q (e a) (e b))
    (Matrix.of fun a c' => c.inner (f c') (M (e a)))
    (Matrix.of fun c' a => c.inner (f c') (M (e a))) 0
open GaussianConstraint in
theorem constrainedGaussianNumberOfCores_eq_det (hS : SaddleDeterminantIdentity)
    (c₁ : InnerProductSpace.Core ℝ V) (c₂ : InnerProductSpace.Core ℝ V') :
    ∃ (d₁ d₂ : ℕ) (e : Fin d₁ → V) (f : Fin d₂ → V'),
      ∀ (M : V →ₗ[ℝ] V') (T : QuadraticForm ℝ (LinearMap.ker M)) (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ),
        Function.Surjective M → T.PosDef → (∀ B B', Q B B' = Q B' B) →
        (∀ B : LinearMap.ker M, Q B.1 B.1 = T B) →
        constrainedGaussianNumberOfCores c₁ c₂ M T =
          (2 * Real.pi) ^ (((Module.finrank ℝ V : ℝ) - (Module.finrank ℝ V' : ℝ)) / 2) *
            |(saddleBlockMatrix c₂ e f M Q).det| ^ (-(1 / 2) : ℝ) := by
  letI := c₁.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c₁.toCore
  letI := c₂.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c₂.toCore
  let e := stdOrthonormalBasis ℝ V
  let f := stdOrthonormalBasis ℝ V'
  refine ⟨_, _, e, f, fun M T Q hM hT hsym hQ => ?_⟩
  let Qm : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
    Matrix.of fun a b => Q (e a) (e b)
  let X : V →ₗ[ℝ] V := Matrix.toLin e.toBasis e.toBasis Qm
  have hrepr : ∀ (x : V) a, e.toBasis.repr x a = inner ℝ (e a) x := fun x a => by
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  have hrepr' : ∀ (x : V') a, f.toBasis.repr x a = inner ℝ (f a) x := fun x a => by
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  have hXe : ∀ a b, inner ℝ (e a) (X (e b)) = Q (e a) (e b) := fun a b => by
    have h1 : LinearMap.toMatrix e.toBasis e.toBasis X = Qm := LinearMap.toMatrix_toLin _ _ _
    have h2 := congrFun (congrFun h1 a) b
    rw [LinearMap.toMatrix_apply, hrepr, OrthonormalBasis.coe_toBasis] at h2
    exact h2
  have hXQ : ∀ x y, inner ℝ x (X y) = Q x y := by
    have h1 : (innerₗ V).compl₂ X = Q := by
      refine e.toBasis.ext fun a => e.toBasis.ext fun b => ?_
      simpa using hXe a b
    intro x y
    rw [← h1]
    simp
  have hXs : X.IsSymmetric := fun x y => by
    rw [real_inner_comm y (X x), hXQ, hXQ, hsym]
  obtain ⟨h₁, -⟩ := hS V V' M T hM hT X hXs fun B => by
    rw [hXQ]
    exact hQ B
  have hdet : LinearMap.det (saddlePointOperator X M) = (saddleBlockMatrix c₂ e f M Q).det := by
    rw [← LinearMap.det_toMatrix (e.toBasis.prod f.toBasis)]
    congr 1
    ext x y
    rcases x with a | c' <;> rcases y with b | d
    · simp [LinearMap.toMatrix_apply, saddlePointOperator, saddleBlockMatrix, hrepr, hXe]
    · simp [LinearMap.toMatrix_apply, saddlePointOperator, saddleBlockMatrix, hrepr,
        LinearMap.adjoint_inner_right]
      exact real_inner_comm _ _
    · simp [LinearMap.toMatrix_apply, saddlePointOperator, saddleBlockMatrix, hrepr']
    · simp [LinearMap.toMatrix_apply, saddlePointOperator, saddleBlockMatrix]
  change constrainedGaussianNumber M T = _
  rw [h₁, hdet]
end Bases
def detPowerFunction (K : ℝ) (z : ℂ) : ℂ := (K : ℂ) * (z ^ 2) ^ (-(1 / 4) : ℂ)
theorem detPowerFunction_differentiableOn (K : ℝ) :
    DifferentiableOn ℂ (detPowerFunction K) {z : ℂ | z ^ 2 ∈ Complex.slitPlane} :=
  fun _ hz => (((differentiableAt_id.pow 2).cpow (differentiableAt_const _) hz).const_mul
    _).differentiableWithinAt
theorem isOpen_sq_mem_slitPlane : IsOpen {z : ℂ | z ^ 2 ∈ Complex.slitPlane} :=
  Complex.isOpen_slitPlane.preimage (continuous_id.pow 2)
theorem ofReal_sq_mem_slitPlane {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) ∈ {z : ℂ | z ^ 2 ∈ Complex.slitPlane} := by
  change (x : ℂ) ^ 2 ∈ Complex.slitPlane
  rw [← Complex.ofReal_pow, Complex.ofReal_mem_slitPlane]
  positivity
theorem detPowerFunction_ofReal (K : ℝ) (x : ℝ) :
    detPowerFunction K x = ((K * |x| ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  have h1 : ((x ^ 2) ^ (-(1 / 4) : ℝ) : ℝ) = |x| ^ (-(1 / 2) : ℝ) := by
    rw [← sq_abs, ← Real.rpow_natCast |x| 2, ← Real.rpow_mul (abs_nonneg x)]
    norm_num
  unfold detPowerFunction
  rw [← h1, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity), Complex.ofReal_pow]
  push_cast
  rfl
section Functions
variable {L n k j : ℕ}
theorem isOpenInSubspaceTimesGroup_of_isOpenFieldSet [Fintype (PositiveEdge L n k j)]
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} (h : IsOpenFieldSet compactGaugeGroup 𝒰) :
    IsOpenInSubspaceTimesGroup (R := PositiveEdge L n k j) (S := Empty) ⊥
      {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by apply _root_.YangMills.SharedProofs.p979 <;> assumption
theorem analyticFieldFunction_congr {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    {F G : (Edge L n k j → ComplexMatrix2) → ℝ} (h : IsAnalyticFieldFunction 𝒰 F)
    (e : EqOn F G 𝒰) : IsAnalyticFieldFunction 𝒰 G := by
  obtain ⟨hop, i, a⟩ := h
  refine ⟨hop, i, a.1, fun p hp => ?_⟩
  obtain ⟨𝒳, h1, h2, h3, Φ, hΦ, he⟩ := a.2 p hp
  refine ⟨𝒳, h1, h2, h3, Φ, hΦ, fun q hq => (he hq).trans ?_⟩
  have hq𝒰 : fieldOfPositiveValues (groupComponent q) ∈ 𝒰 := h3 hq
  funext x
  simp only [e hq𝒰]
theorem analyticFieldFunction_mono (H : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 𝒰' : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h : IsAnalyticFieldFunction 𝒰 F) (h' : IsOpenFieldSet compactGaugeGroup 𝒰')
    (hsub : 𝒰' ⊆ 𝒰) : IsAnalyticFieldFunction 𝒰' F := by
  obtain ⟨-, i, a⟩ := h
  refine ⟨h', i, ?_⟩
  have hW := isOpenInSubspaceTimesGroup_of_isOpenFieldSet h'
  exact ((H Empty (PositiveEdge L n k j) Empty Empty ⊥ ⊥ bot_le bot_le _ a.1).1 _
    (fun q hq => hsub hq) hW.2).1 1 _ a
theorem analyticFieldFunction_add (H : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} {F₁ F₂ : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldFunction 𝒰 F₁) (h₂ : IsAnalyticFieldFunction 𝒰 F₂) :
    IsAnalyticFieldFunction 𝒰 fun V => F₁ V + F₂ V := by
  obtain ⟨hop, i₁, a₁⟩ := h₁
  obtain ⟨-, i₂, a₂⟩ := h₂
  obtain rfl : i₂ = i₁ := Subsingleton.elim _ _
  refine ⟨hop, i₂, ?_⟩
  have hs := (H Empty (PositiveEdge L n k j) Empty Empty ⊥ ⊥ bot_le bot_le _ a₁.1).2.2.1 1 _ _ a₁ a₂
  convert hs using 1
  funext q x
  simp
theorem analyticFieldFunction_const (H : AnalyticCalculus.AnalyticCalculusStatement)
    (hfin : Finite (PositiveEdge L n k j)) {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (hop : IsOpenFieldSet compactGaugeGroup 𝒰) (c : ℝ) :
    IsAnalyticFieldFunction 𝒰 fun _ => c := by
  letI := Fintype.ofFinite (PositiveEdge L n k j)
  refine ⟨hop, inferInstance, ?_⟩
  exact (((H Empty (PositiveEdge L n k j) Empty Empty).2.2.2 ⊥ ⊥ bot_le bot_le).2.2.1 _
    (isOpenInSubspaceTimesGroup_of_isOpenFieldSet hop)).1.1 1 fun _ => (c : ℂ)
theorem analyticFieldFunction_comp (hH : ExpChartHolomorphy.ExpChartTheory)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hF : IsAnalyticFieldFunction 𝒰 F) {Ω : Set ℂ} (hΩ : IsOpen Ω) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h Ω) {g : ℝ → ℝ} (hmap : ∀ W ∈ 𝒰, (F W : ℂ) ∈ Ω)
    (hg : ∀ W ∈ 𝒰, h (F W) = (g (F W) : ℂ)) :
    IsAnalyticFieldFunction 𝒰 fun W => g (F W) := by
  obtain ⟨hop, i, a⟩ := hF
  have c := isSubspaceAnalyticToCoords_comp hH a hΩ hh fun p hp => hmap _ hp
  refine ⟨hop, i, c.1, fun p hp => ?_⟩
  obtain ⟨𝒳, h1, h2, h3, Φ, hΦ, he⟩ := c.2 p hp
  refine ⟨𝒳, h1, h2, h3, Φ, hΦ, fun q hq => (he hq).trans ?_⟩
  funext x
  exact hg _ (h3 hq)
theorem analyticFieldFunction_smul (hH : ExpChartHolomorphy.ExpChartTheory)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hF : IsAnalyticFieldFunction 𝒰 F) (c : ℝ) :
    IsAnalyticFieldFunction 𝒰 fun W => c * F W :=
  analyticFieldFunction_comp hH hF (Ω := univ) isOpen_univ (h := fun z => (c : ℂ) * z)
    (g := fun x => c * x) ((differentiable_id.const_mul _).differentiableOn)
    (fun _ _ => mem_univ _) fun _ _ => by simp
theorem analyticFieldFunction_sq (hH : ExpChartHolomorphy.ExpChartTheory)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hF : IsAnalyticFieldFunction 𝒰 F) :
    IsAnalyticFieldFunction 𝒰 fun W => F W ^ 2 :=
  analyticFieldFunction_comp hH hF (Ω := univ) isOpen_univ (h := fun z => z ^ 2)
    (g := fun x => x ^ 2) ((differentiable_id.pow 2).differentiableOn)
    (fun _ _ => mem_univ _) fun _ _ => by simp
theorem analyticFieldFunction_mul (hH : ExpChartHolomorphy.ExpChartTheory)
    (H : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} {F₁ F₂ : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticFieldFunction 𝒰 F₁) (h₂ : IsAnalyticFieldFunction 𝒰 F₂) :
    IsAnalyticFieldFunction 𝒰 fun V => F₁ V * F₂ V := by
  have hs := analyticFieldFunction_sq hH (analyticFieldFunction_add H h₁ h₂)
  have hd := analyticFieldFunction_sq hH
    (analyticFieldFunction_add H h₁ (analyticFieldFunction_smul hH h₂ (-1)))
  have h := analyticFieldFunction_smul hH
    (analyticFieldFunction_add H hs (analyticFieldFunction_smul hH hd (-1))) (1 / 4)
  refine analyticFieldFunction_congr h fun V _ => ?_
  ring
theorem analyticFieldFunction_sum (H : LocalAnalyticity.LocalAnalyticityStatement)
    (hC : AnalyticCalculus.AnalyticCalculusStatement)
    (hfin : Finite (PositiveEdge L n k j)) {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (hop : IsOpenFieldSet compactGaugeGroup 𝒰) {ι : Type} (s : Finset ι)
    (F : ι → (Edge L n k j → ComplexMatrix2) → ℝ) (h : ∀ i ∈ s, IsAnalyticFieldFunction 𝒰 (F i)) :
    IsAnalyticFieldFunction 𝒰 fun W => ∑ i ∈ s, F i W := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analyticFieldFunction_const hC hfin hop 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact analyticFieldFunction_add H (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem analyticFieldFunction_prod (hH : ExpChartHolomorphy.ExpChartTheory)
    (H : LocalAnalyticity.LocalAnalyticityStatement)
    (hC : AnalyticCalculus.AnalyticCalculusStatement)
    (hfin : Finite (PositiveEdge L n k j)) {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (hop : IsOpenFieldSet compactGaugeGroup 𝒰) {ι : Type} (s : Finset ι)
    (F : ι → (Edge L n k j → ComplexMatrix2) → ℝ) (h : ∀ i ∈ s, IsAnalyticFieldFunction 𝒰 (F i)) :
    IsAnalyticFieldFunction 𝒰 fun W => ∏ i ∈ s, F i W := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analyticFieldFunction_const hC hfin hop 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact analyticFieldFunction_mul hH H (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem analyticFieldFunction_det (hH : ExpChartHolomorphy.ExpChartTheory)
    (H : LocalAnalyticity.LocalAnalyticityStatement)
    (hC : AnalyticCalculus.AnalyticCalculusStatement)
    (hfin : Finite (PositiveEdge L n k j)) {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (hop : IsOpenFieldSet compactGaugeGroup 𝒰) {m : Type} [Fintype m] [DecidableEq m]
    (A : (Edge L n k j → ComplexMatrix2) → Matrix m m ℝ)
    (hA : ∀ x y, IsAnalyticFieldFunction 𝒰 fun W => A W x y) :
    IsAnalyticFieldFunction 𝒰 fun W => (A W).det := by
  simp only [Matrix.det_apply']
  refine analyticFieldFunction_sum H hC hfin hop _ _ fun σ _ => ?_
  exact analyticFieldFunction_mul hH H (analyticFieldFunction_const hC hfin hop _)
    (analyticFieldFunction_prod hH H hC hfin hop _ _ fun x _ => hA _ _)
theorem exists_open_of_eventuallyNearIdentity (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝒰₀ : Set (Edge L n k j → ComplexMatrix2)} {P : (Edge L n k j → ComplexMatrix2) → Prop}
    (h : IsOpenNhdOfOne 𝒰₀) (hne : EventuallyNearIdentity (fieldSpace L n k j) P) :
    ∃ 𝒰 : Set (Edge L n k j → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧ 𝒰 ⊆ 𝒰₀ ∧ ∀ W ∈ 𝒰, P W := by apply _root_.YangMills.Construction.Tower.SaddleAnalytic.exists_isOpenNhdOfOne_of_eventually <;> assumption
end Functions
end NormaliserAnalyticity
open NormaliserAnalyticity Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
  PeriodicLattice in
theorem gaussianNormaliserAnalyticNearIdentity_proof
    (h₁ : SaddleFormAnalyticNearIdentity)
    (h₂ : CriticalFibreHessianPosDef)
    (h₃ : GaussianNormaliserPositiveNearOne)
    (h₄ : GaussianConstraint.SaddleDeterminantIdentity)
    (h₅ : FiniteSideFormSpaces)
    (h₆ : LocalAnalyticity.LocalAnalyticityStatement)
    (h₇ : AnalyticCalculus.AnalyticCalculusStatement)
    (h₈ : ExpChartHolomorphy.ExpChartTheory)
    (h₉ : BondSetFields.ProductStructureHolds) :
    GaussianNormaliserAnalyticNearIdentity := by
  intro L n k hL hn i hi
  obtain ⟨𝒰₀, ho, Q, hsym, hQ, hQa, hMa⟩ := h₁ L n k hL hn i hi
  obtain ⟨-, f₁, -, c₁, e₁⟩ := h₅ L n k i hL hn (by omega)
  obtain ⟨hfin, f₂, -, c₂, e₂⟩ := h₅ L n k (i + 1) hL hn hi
  have hE : EdgeFormsEuclidean L n k i ∧ EdgeFormsEuclidean L n k (i + 1) :=
    ⟨⟨f₁, c₁, fun B B' => by rw [e₁ B B', Complex.ofReal_re]⟩,
      ⟨f₂, c₂, fun B B' => by rw [e₂ B B', Complex.ofReal_re]⟩⟩
  have := hE.1.1
  have := hE.2.1
  obtain ⟨d₁, d₂, e, f, hnum⟩ :=
    constrainedGaussianNumberOfCores_eq_det h₄ hE.1.2.choose hE.2.2.choose
  obtain ⟨𝒰, h𝒰, hsub, hP⟩ := exists_open_of_eventuallyNearIdentity
    (P := fun W => Function.Surjective (constraintDifferential L n k i W) ∧
      (fibreHessianForm L n k i W).PosDef ∧ 0 < gaussianNormaliser L n k i W) h₉ hL hn hi ho
    (by
      filter_upwards [h₂ L n k hL hn i hi, h₃ L n k hL hn i hi] with W a b
      exact ⟨a.2.1, a.2.2.2.2, b⟩)
  have hop := h𝒰.1
  set K : ℝ := (2 * Real.pi) ^ (((Module.finrank ℝ (edgeFormSpace L n k i) : ℝ) -
    (Module.finrank ℝ (edgeFormSpace L n k (i + 1)) : ℝ)) / 2) with hK
  have hN : ∀ W ∈ 𝒰, gaussianNormaliser L n k i W = K *
      |(saddleBlockMatrix hE.2.2.choose e f (constraintDifferential L n k i W) (Q W)).det| ^
        (-(1 / 2) : ℝ) := by
    intro W hW
    obtain ⟨hM, hT, -⟩ := hP W hW
    have e₀ : gaussianNormaliser L n k i W =
        GaussianConstraint.constrainedGaussianNumberOfCores hE.1.2.choose hE.2.2.choose
          (constraintDifferential L n k i W) (fibreHessianForm L n k i W) := by
      unfold gaussianNormaliser constrainedGaussianOnEdgeForms
      rw [dif_pos hE]
    rw [e₀]
    exact hnum _ _ _ hM hT (hsym W (hsub hW)) (hQ W (hsub hW))
  have hne : ∀ W ∈ 𝒰,
      (saddleBlockMatrix hE.2.2.choose e f (constraintDifferential L n k i W) (Q W)).det ≠ 0 := by
    intro W hW h0
    have hpos := (hP W hW).2.2
    rw [hN W hW, h0, abs_zero, Real.zero_rpow (by norm_num), mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hin : ∀ (W : Edge L n k (i + 1) → ComplexMatrix2) a c',
      hE.2.2.choose.inner (f c') (constraintDifferential L n k i W (e a)) =
        (edgeFormPairing (f c' : Edge L n k (i + 1) → ComplexMatrix2)
          (constraintDifferential L n k i W (e a) : Edge L n k (i + 1) → ComplexMatrix2)).re :=
    fun W a c' => hE.2.2.choose_spec _ _
  have hD : IsAnalyticFieldFunction 𝒰 fun W =>
      (saddleBlockMatrix hE.2.2.choose e f (constraintDifferential L n k i W) (Q W)).det := by
    refine analyticFieldFunction_det h₈ h₆ h₇ hfin hop _ fun x y => ?_
    rcases x with a | c' <;> rcases y with b | d
    · exact analyticFieldFunction_mono h₆ (hQa (e a) (e b)) hop hsub
    · refine analyticFieldFunction_congr
        (analyticFieldFunction_mono h₆ (hMa (e a) (f d)) hop hsub) fun W _ => ?_
      exact (hin W a d).symm
    · refine analyticFieldFunction_congr
        (analyticFieldFunction_mono h₆ (hMa (e b) (f c')) hop hsub) fun W _ => ?_
      exact (hin W b c').symm
    · simpa [saddleBlockMatrix] using analyticFieldFunction_const h₇ hfin hop 0
  have hfinal := analyticFieldFunction_comp h₈ hD isOpen_sq_mem_slitPlane
    (detPowerFunction_differentiableOn K) (g := fun x => K * |x| ^ (-(1 / 2) : ℝ))
    (fun W hW => ofReal_sq_mem_slitPlane (hne W hW))
    fun W _ => detPowerFunction_ofReal K _
  exact ⟨𝒰, h𝒰, analyticFieldFunction_congr hfinal fun W hW => (hN W hW).symm⟩
end YangMills.Construction.Tower
end
