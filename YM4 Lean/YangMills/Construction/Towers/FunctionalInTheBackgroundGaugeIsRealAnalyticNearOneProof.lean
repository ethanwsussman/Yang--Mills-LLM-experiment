import YangMills.Construction.Towers.BackgroundGaugeFunctionalIsFormedAtTheTrivialPoint
import YangMills.Construction.Towers.EntriesOfTheBackgroundDeterminantsAreRealAnalytic
import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeIsRealAnalyticNearOne
import YangMills.Construction.Towers.HessianOnAFibreOfTheCriticalBranchProof
import YangMills.Construction.Towers.NormaliserIsRealAnalyticNearOneProof
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAndTheTwoDeterminantsProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace Tower.BackgroundFunctionalAnalyticity
open Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
section Holomorphic
variable {R S : Type} [Fintype R] [Fintype S]
theorem isHolomorphicToCoords_comp (hH : ExpChartHolomorphy.ExpChartTheory)
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {𝒳 : Set (R ⊕ S → ComplexMatrix2)}
    {Φ : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (hΦ : IsHolomorphicToCoords b (Equiv.refl (Coordinates.ComplexCoordinates 1)) 𝒳 Φ)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h Ω) :
    IsHolomorphicToCoords b (Equiv.refl (Coordinates.ComplexCoordinates 1))
      (𝒳 ∩ (fun q => Φ q 0) ⁻¹' Ω)
      (fun q _ => h (Φ q 0) : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates 1) := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.isHolomorphicToCoords_comp <;> assumption
theorem isSubspaceAnalyticToCoords_comp (hH : ExpChartHolomorphy.ExpChartTheory)
    {E : Submodule ℝ (S → ComplexMatrix2)} {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
    {f : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (hf : IsSubspaceAnalyticToCoords E 𝒲 f)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h Ω)
    (hmap : ∀ p ∈ 𝒲, f p 0 ∈ Ω) :
    IsSubspaceAnalyticToCoords E 𝒲
      (fun p _ => h (f p 0) : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates 1) := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.isSubspaceAnalyticToCoords_comp <;> assumption
abbrev IsAnalyticReal (E : Submodule ℝ (S → ComplexMatrix2)) (𝒲 : Set (R ⊕ S → ComplexMatrix2))
    (F : (R ⊕ S → ComplexMatrix2) → ℝ) : Prop :=
  IsSubspaceAnalyticToCoords (l := 1) E 𝒲 fun q _ => (F q : ℂ)
variable {E : Submodule ℝ (S → ComplexMatrix2)} {𝒲 : Set (R ⊕ S → ComplexMatrix2)}
theorem analyticReal_congr {F G : (R ⊕ S → ComplexMatrix2) → ℝ} (h : IsAnalyticReal E 𝒲 F)
    (e : EqOn F G 𝒲) : IsAnalyticReal E 𝒲 G := by
  refine ⟨h.1, fun p hp => ?_⟩
  obtain ⟨𝒳, h1, h2, h3, Φ, hΦ, he⟩ := h.2 p hp
  refine ⟨𝒳, h1, h2, h3, Φ, hΦ, fun q hq => (he hq).trans ?_⟩
  funext x
  simp only [e (h3 hq)]
theorem analyticReal_mono (H : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒲' : Set (R ⊕ S → ComplexMatrix2)}
    {F : (R ⊕ S → ComplexMatrix2) → ℝ} (h : IsAnalyticReal E 𝒲 F)
    (h' : IsOpenInSubspaceTimesGroup E 𝒲') (hsub : 𝒲' ⊆ 𝒲) : IsAnalyticReal E 𝒲' F :=
  ((H S R Empty Empty E ⊥ h.1.1 bot_le _ h.1).1 _ hsub h'.2).1 1 _ h
theorem analyticReal_add (H : LocalAnalyticity.LocalAnalyticityStatement)
    {F₁ F₂ : (R ⊕ S → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticReal E 𝒲 F₁) (h₂ : IsAnalyticReal E 𝒲 F₂) :
    IsAnalyticReal E 𝒲 fun q => F₁ q + F₂ q := by
  have hs := (H S R Empty Empty E ⊥ h₁.1.1 bot_le _ h₁.1).2.2.1 1 _ _ h₁ h₂
  convert hs using 1
  funext q x
  simp
theorem analyticReal_const (hC : AnalyticCalculus.AnalyticCalculusStatement)
    (hop : IsOpenInSubspaceTimesGroup E 𝒲) (c : ℝ) : IsAnalyticReal E 𝒲 fun _ => c :=
  (((hC S R Empty Empty).2.2.2 E ⊥ hop.1 bot_le).2.2.1 _ hop).1.1 1 fun _ => (c : ℂ)
theorem analyticReal_comp (hH : ExpChartHolomorphy.ExpChartTheory)
    {F : (R ⊕ S → ComplexMatrix2) → ℝ} (hF : IsAnalyticReal E 𝒲 F) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h Ω) {g : ℝ → ℝ} (hmap : ∀ p ∈ 𝒲, (F p : ℂ) ∈ Ω)
    (hg : ∀ p ∈ 𝒲, h (F p) = (g (F p) : ℂ)) :
    IsAnalyticReal E 𝒲 fun p => g (F p) := by
  have c := isSubspaceAnalyticToCoords_comp hH hF hΩ hh fun p hp => hmap _ hp
  refine ⟨c.1, fun p hp => ?_⟩
  obtain ⟨𝒳, h1, h2, h3, Φ, hΦ, he⟩ := c.2 p hp
  refine ⟨𝒳, h1, h2, h3, Φ, hΦ, fun q hq => (he hq).trans ?_⟩
  funext x
  exact hg _ (h3 hq)
theorem analyticReal_smul (hH : ExpChartHolomorphy.ExpChartTheory)
    {F : (R ⊕ S → ComplexMatrix2) → ℝ} (hF : IsAnalyticReal E 𝒲 F) (c : ℝ) :
    IsAnalyticReal E 𝒲 fun p => c * F p :=
  analyticReal_comp hH hF (Ω := univ) isOpen_univ (h := fun z => (c : ℂ) * z)
    (g := fun x => c * x) ((differentiable_id.const_mul _).differentiableOn)
    (fun _ _ => mem_univ _) fun _ _ => by simp
theorem analyticReal_sq (hH : ExpChartHolomorphy.ExpChartTheory)
    {F : (R ⊕ S → ComplexMatrix2) → ℝ} (hF : IsAnalyticReal E 𝒲 F) :
    IsAnalyticReal E 𝒲 fun p => F p ^ 2 :=
  analyticReal_comp hH hF (Ω := univ) isOpen_univ (h := fun z => z ^ 2)
    (g := fun x => x ^ 2) ((differentiable_id.pow 2).differentiableOn)
    (fun _ _ => mem_univ _) fun _ _ => by simp
theorem analyticReal_mul (hH : ExpChartHolomorphy.ExpChartTheory)
    (H : LocalAnalyticity.LocalAnalyticityStatement) {F₁ F₂ : (R ⊕ S → ComplexMatrix2) → ℝ}
    (h₁ : IsAnalyticReal E 𝒲 F₁) (h₂ : IsAnalyticReal E 𝒲 F₂) :
    IsAnalyticReal E 𝒲 fun p => F₁ p * F₂ p := by
  have hs := analyticReal_sq hH (analyticReal_add H h₁ h₂)
  have hd := analyticReal_sq hH (analyticReal_add H h₁ (analyticReal_smul hH h₂ (-1)))
  have h := analyticReal_smul hH (analyticReal_add H hs (analyticReal_smul hH hd (-1))) (1 / 4)
  refine analyticReal_congr h fun p _ => ?_
  ring
theorem analyticReal_sum (H : LocalAnalyticity.LocalAnalyticityStatement)
    (hC : AnalyticCalculus.AnalyticCalculusStatement) (hop : IsOpenInSubspaceTimesGroup E 𝒲)
    {ι : Type} (s : Finset ι) (F : ι → (R ⊕ S → ComplexMatrix2) → ℝ)
    (h : ∀ i ∈ s, IsAnalyticReal E 𝒲 (F i)) :
    IsAnalyticReal E 𝒲 fun p => ∑ i ∈ s, F i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analyticReal_const hC hop 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact analyticReal_add H (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem analyticReal_prod (hH : ExpChartHolomorphy.ExpChartTheory)
    (H : LocalAnalyticity.LocalAnalyticityStatement)
    (hC : AnalyticCalculus.AnalyticCalculusStatement) (hop : IsOpenInSubspaceTimesGroup E 𝒲)
    {ι : Type} (s : Finset ι) (F : ι → (R ⊕ S → ComplexMatrix2) → ℝ)
    (h : ∀ i ∈ s, IsAnalyticReal E 𝒲 (F i)) :
    IsAnalyticReal E 𝒲 fun p => ∏ i ∈ s, F i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analyticReal_const hC hop 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact analyticReal_mul hH H (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem analyticReal_det (hH : ExpChartHolomorphy.ExpChartTheory)
    (H : LocalAnalyticity.LocalAnalyticityStatement)
    (hC : AnalyticCalculus.AnalyticCalculusStatement) (hop : IsOpenInSubspaceTimesGroup E 𝒲)
    {m : Type} [Fintype m] [DecidableEq m] (A : (R ⊕ S → ComplexMatrix2) → Matrix m m ℝ)
    (hA : ∀ x y, IsAnalyticReal E 𝒲 fun p => A p x y) :
    IsAnalyticReal E 𝒲 fun p => (A p).det := by
  simp only [Matrix.det_apply']
  refine analyticReal_sum H hC hop _ _ fun σ _ => ?_
  exact analyticReal_mul hH H (analyticReal_const hC hop _)
    (analyticReal_prod hH H hC hop _ _ fun x _ => hA _ _)
theorem isOpen_sq_mem_slitPlane : IsOpen {z : ℂ | z ^ 2 ∈ Complex.slitPlane} :=
  Complex.isOpen_slitPlane.preimage (continuous_id.pow 2)
theorem ofReal_mem_sq_slitPlane {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) ∈ {z : ℂ | z ^ 2 ∈ Complex.slitPlane} := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.ofReal_sq_mem_slitPlane <;> assumption
theorem half_log_sq_eq (x : ℝ) :
    (1 / 2 : ℂ) * Complex.log ((x : ℂ) ^ 2) = ((Real.log |x| : ℝ) : ℂ) := by
  have h1 : (x : ℂ) ^ 2 = ((x ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, ← Complex.ofReal_log (sq_nonneg x), ← sq_abs x, Real.log_pow]
  push_cast
  ring
theorem analyticReal_log_abs (hH : ExpChartHolomorphy.ExpChartTheory)
    {F : (R ⊕ S → ComplexMatrix2) → ℝ} (hF : IsAnalyticReal E 𝒲 F) (hne : ∀ p ∈ 𝒲, F p ≠ 0) :
    IsAnalyticReal E 𝒲 fun p => Real.log |F p| := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => (1 / 2 : ℂ) * Complex.log (z ^ 2))
      {z : ℂ | z ^ 2 ∈ Complex.slitPlane} := fun z hz =>
    (((differentiableAt_id.pow 2).clog hz).const_mul _).differentiableWithinAt
  have hm : ∀ p ∈ 𝒲, (F p : ℂ) ∈ {z : ℂ | z ^ 2 ∈ Complex.slitPlane} := fun p hp =>
    ofReal_mem_sq_slitPlane (hne p hp)
  have hg : ∀ p ∈ 𝒲, (fun z : ℂ => (1 / 2 : ℂ) * Complex.log (z ^ 2)) (F p) =
      ((fun x : ℝ => Real.log |x|) (F p) : ℂ) := fun p _ => half_log_sq_eq _
  exact analyticReal_comp (h := fun z : ℂ => (1 / 2 : ℂ) * Complex.log (z ^ 2))
    (g := fun x : ℝ => Real.log |x|) hH hF isOpen_sq_mem_slitPlane hd hm hg
theorem subspaceTimesGroup_subset (hE : E ≤ hermitianTracelessFunctions S) :
    subspaceTimesGroup E R ⊆ GroupLieProduct R S := by
  rintro q ⟨hq₁, hq₂⟩ (r | s)
  · exact (Matrix.mem_specialUnitaryGroup_iff.1 (hq₂ r)).2
  · exact ((Submodule.mem_pi.1 (hE hq₁)) s (mem_univ s)).2
theorem isOpen_ne_zero (hH : ExpChartHolomorphy.ExpChartTheory)
    {F : (R ⊕ S → ComplexMatrix2) → ℝ} (hF : IsAnalyticReal E 𝒲 F) :
    IsOpenInSubspaceTimesGroup E (𝒲 ∩ {q | F q ≠ 0}) := by
  have hsubset := subspaceTimesGroup_subset (R := R) hF.1.1
  have hW : 𝒲 ⊆ subspaceTimesGroup E R := by
    obtain ⟨O, -, e⟩ := hF.1.2
    rw [e]
    exact inter_subset_right
  have key : ∀ p ∈ 𝒲 ∩ {q | F q ≠ 0}, ∃ O : Set (R ⊕ S → ComplexMatrix2), IsOpen O ∧ p ∈ O ∧
      O ∩ subspaceTimesGroup E R ⊆ 𝒲 ∩ {q | F q ≠ 0} := by
    rintro p ⟨hp, hne⟩
    obtain ⟨𝒳, h1, h2, h3, Φ, hΦ, he⟩ := hF.2 p hp
    have hc := isHolomorphicToCoords_comp hH (hΦ OneLoop.pauliBasis) (Ω := {0}ᶜ)
      isOpen_compl_singleton (h := id) differentiableOn_id
    obtain ⟨O, hO, e⟩ := hc.1
    have hmem : ∀ q ∈ 𝒳 ∩ subspaceTimesGroup E R, Φ q 0 = (F q : ℂ) := fun q hq =>
      congrFun (he hq) 0
    refine ⟨O, hO, ?_, ?_⟩
    · have : p ∈ 𝒳 ∩ (fun q => Φ q 0) ⁻¹' {0}ᶜ := by
        refine ⟨h1, ?_⟩
        change Φ p 0 ≠ 0
        rw [hmem p ⟨h1, hW hp⟩]
        exact_mod_cast hne
      rw [e] at this
      exact this.1
    · rintro q ⟨hqO, hqs⟩
      have hq : q ∈ O ∩ GroupLieProduct R S := ⟨hqO, hsubset hqs⟩
      rw [← e] at hq
      refine ⟨h3 ⟨hq.1, hqs⟩, ?_⟩
      have h0 : Φ q 0 ≠ 0 := hq.2
      rw [hmem q ⟨hq.1, hqs⟩] at h0
      exact_mod_cast h0
  refine ⟨hF.1.1, ⋃₀ {O | IsOpen O ∧ O ∩ subspaceTimesGroup E R ⊆ 𝒲 ∩ {q | F q ≠ 0}},
    isOpen_sUnion fun _ h => h.1, ?_⟩
  ext q
  constructor
  · intro hq
    obtain ⟨O, hO, hqO, hs⟩ := key q hq
    exact ⟨⟨O, ⟨hO, hs⟩, hqO⟩, hW hq.1⟩
  · rintro ⟨⟨O, ⟨-, hs⟩, hqO⟩, hqs⟩
    exact hs ⟨hqO, hqs⟩
def subspaceMember (E : Submodule ℝ (S → ComplexMatrix2)) (q : R ⊕ S → ComplexMatrix2) : E :=
  open Classical in if h : algebraComponent q ∈ E then ⟨_, h⟩ else 0
theorem subspaceMember_coe {q : R ⊕ S → ComplexMatrix2} (h : q ∈ subspaceTimesGroup E R) :
    (subspaceMember E q : S → ComplexMatrix2) = algebraComponent q := by
  simp only [subspaceMember, dif_pos h.1]
theorem isOpen_subspaceTimesGroup (hE : E ≤ hermitianTracelessFunctions S) :
    IsOpenInSubspaceTimesGroup E (subspaceTimesGroup E R) :=
  ⟨hE, univ, isOpen_univ, (univ_inter _).symm⟩
theorem analyticReal_basis_repr (hC : AnalyticCalculus.AnalyticCalculusStatement)
    (hE : E ≤ hermitianTracelessFunctions S) {d : ℕ} (b : Module.Basis (Fin d) ℝ E) (i : Fin d) :
    IsAnalyticReal E (subspaceTimesGroup E R) fun q => b.repr (subspaceMember E q) i := by
  have hcomp := (hC S R S Empty).2.2.2 E E hE hE
  have hb := (hcomp.2.2.1 _ (isOpen_subspaceTimesGroup hE)).2.2.2 d b algebraComponent
    (fun i p => b.repr (subspaceMember E p) i) (fun p hp => by
      calc algebraComponent p = ((subspaceMember E p : E) : S → ComplexMatrix2) :=
            (subspaceMember_coe hp).symm
        _ = ((∑ i, b.repr (subspaceMember E p) i • b i : E) : S → ComplexMatrix2) := by
            rw [b.sum_repr]
        _ = ∑ i, b.repr (subspaceMember E p) i • ((b i : E) : S → ComplexMatrix2) := by
          simp only [Submodule.coe_sum, Submodule.coe_smul])
  have h := (hb.1 hcomp.2.1.1) i
  have e1 : ∀ z : ℂ, AnalyticCalculus.scalarEquiv z = fun _ => z :=
    fun z => by
      funext x
      simp [AnalyticCalculus.scalarEquiv]
  simpa only [e1] using h
end Holomorphic
section Bases
variable {V V' : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
def saddleBlockMatrix (c₁ : InnerProductSpace.Core ℝ V) (c₂ : InnerProductSpace.Core ℝ V')
    {d₁ d₂ : ℕ} (e : Fin d₁ → V) (f : Fin d₂ → V') (X : V →ₗ[ℝ] V) (M : V →ₗ[ℝ] V') :
    Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) ℝ :=
  Matrix.fromBlocks (Matrix.of fun a b => c₁.inner (e a) (X (e b)))
    (Matrix.of fun a c' => c₂.inner (f c') (M (e a)))
    (Matrix.of fun c' a => c₂.inner (f c') (M (e a))) 0
open GaussianConstraint in
theorem saddleDet_eq_det_blockMatrix [FiniteDimensional ℝ V] [FiniteDimensional ℝ V']
    (c₁ : InnerProductSpace.Core ℝ V) (c₂ : InnerProductSpace.Core ℝ V') :
    ∃ (d₁ d₂ : ℕ) (e : Fin d₁ → V) (f : Fin d₂ → V'), ∀ (X : V →ₗ[ℝ] V) (M : V →ₗ[ℝ] V'),
      saddleDetOfCores c₁ c₂ X M = (saddleBlockMatrix c₁ c₂ e f X M).det := by
  letI := c₁.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c₁.toCore
  letI := c₂.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c₂.toCore
  let e := stdOrthonormalBasis ℝ V
  let f := stdOrthonormalBasis ℝ V'
  refine ⟨_, _, e, f, fun X M => ?_⟩
  have hrepr : ∀ (x : V) a, e.toBasis.repr x a = inner ℝ (e a) x := fun x a => by
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  have hrepr' : ∀ (x : V') a, f.toBasis.repr x a = inner ℝ (f a) x := fun x a => by
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  change LinearMap.det (saddlePointOperator X M) = _
  rw [← LinearMap.det_toMatrix (e.toBasis.prod f.toBasis)]
  congr 1
  ext x y
  rcases x with a | c' <;> rcases y with b | d
  · simp [LinearMap.toMatrix_apply, saddlePointOperator, saddleBlockMatrix, hrepr]
  · simp [LinearMap.toMatrix_apply, saddlePointOperator, saddleBlockMatrix, hrepr,
      LinearMap.adjoint_inner_right]
    exact real_inner_comm _ _
  · simp [LinearMap.toMatrix_apply, saddlePointOperator, saddleBlockMatrix, hrepr']
  · simp [LinearMap.toMatrix_apply, saddlePointOperator, saddleBlockMatrix]
theorem inner_polarization (c : InnerProductSpace.Core ℝ V) (X : V →ₗ[ℝ] V)
    (hs : ∀ B B', c.inner B (X B') = c.inner (X B) B') (B B' : V) :
    c.inner B (X B') =
      1 / 4 * (c.inner (B + B') (X (B + B')) - c.inner (B - B') (X (B - B'))) := by
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  have hs' : ∀ x y : V, inner ℝ x (X y) = inner ℝ (X x) y := hs
  change inner ℝ B (X B') =
    1 / 4 * (inner ℝ (B + B') (X (B + B')) - inner ℝ (B - B') (X (B - B')))
  have h1 : inner ℝ B' (X B) = inner ℝ B (X B') := by
    rw [hs', real_inner_comm]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  linarith
theorem affine_eq_basis_expansion {d : ℕ} (b : Module.Basis (Fin d) ℝ V) (l : V →ₗ[ℝ] ℝ)
    (C : ℝ) (G : V → ℝ) (hG : ∀ a, G a = C + l a) (a : V) :
    G a = G 0 + ∑ i, b.repr a i * (G (b i) - G 0) := by
  have h1 : l a = ∑ i, b.repr a i * l (b i) := by
    calc l a = l (∑ i, b.repr a i • b i) := by rw [b.sum_repr]
      _ = ∑ i, b.repr a i * l (b i) := by simp only [map_sum, map_smul, smul_eq_mul]
  simp only [hG, map_zero, add_zero, add_sub_cancel_left]
  rw [h1]
end Bases
section Functions
variable {L n k j : ℕ}
theorem isAnalyticFieldFunction_mono (H : LocalAnalyticity.LocalAnalyticityStatement)
    {𝒰 𝒰' : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h : IsAnalyticFieldFunction 𝒰 F) (h' : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰')
    (hsub : 𝒰' ⊆ 𝒰) : IsAnalyticFieldFunction 𝒰' F := by apply _root_.YangMills.Construction.Tower.NormaliserAnalyticity.analyticFieldFunction_mono <;> assumption
theorem exists_isOpenNhdOfOne_subset (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝒰₀ : Set (Edge L n k j → ComplexMatrix2)} {P : (Edge L n k j → ComplexMatrix2) → Prop}
    (h : IsOpenNhdOfOne 𝒰₀) (hne : EventuallyNearIdentity (fieldSpace L n k j) P) :
    ∃ 𝒰 : Set (Edge L n k j → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧ 𝒰 ⊆ 𝒰₀ ∧ ∀ W ∈ 𝒰, P W := by apply _root_.YangMills.Construction.Tower.SaddleAnalytic.exists_isOpenNhdOfOne_of_eventually <;> assumption
theorem not_isPositivelyOriented_opposite (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.NearIdentitySurjectivity.not_isPositivelyOriented_opposite <;> assumption
theorem edgeFormOfPositiveValues_mem
    (hnb : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    {w : PositiveEdge L n k j → ComplexMatrix2} (hw : ∀ c, w c ∈ ComplexMatrix2.hermitianTraceless) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.Tower.FibreHessian.edgeForm_mem <;> assumption
variable {S : Type}
def positiveEdgeFormMap
    (hnb : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (ι : PositiveEdge L n k j → S) : hermitianTracelessFunctions S →ₗ[ℝ] edgeFormSpace L n k j where
  toFun a := ⟨edgeFormOfPositiveValues fun c => (a : S → ComplexMatrix2) (ι c),
    edgeFormOfPositiveValues_mem hnb fun c => Submodule.mem_pi.1 a.2 (ι c) (mem_univ _)⟩
  map_add' a a' := by
    apply Subtype.ext
    funext b
    by_cases hb : b.IsPositivelyOriented
    · simp [edgeFormOfPositiveValues, hb]
    · by_cases hr : b.opposite.IsPositivelyOriented
      · simp [edgeFormOfPositiveValues, hb, hr, add_comm]
      · simp [edgeFormOfPositiveValues, hb, hr]
  map_smul' c a := by
    apply Subtype.ext
    funext b
    by_cases hb : b.IsPositivelyOriented
    · simp [edgeFormOfPositiveValues, hb]
    · by_cases hr : b.opposite.IsPositivelyOriented
      · simp [edgeFormOfPositiveValues, hb, hr]
      · simp [edgeFormOfPositiveValues, hb, hr]
theorem traceFinsumPairing_add_left {ι : Type} [Finite ι] (f g h : ι → ComplexMatrix2) :
    traceFinsumPairing (f + g) h = traceFinsumPairing f h + traceFinsumPairing g h := by apply _root_.YangMills.Construction.Tower.HessianDeterminants.traceFinsumPairing_add_left <;> assumption
theorem traceFinsumPairing_smul_left {ι : Type} [Finite ι] (c : ℝ) (f h : ι → ComplexMatrix2) :
    traceFinsumPairing (c • f) h = (c : ℂ) * traceFinsumPairing f h := by
  letI := Fintype.ofFinite ι
  simp only [traceFinsumPairing, finsum_eq_sum_of_fintype, Pi.smul_apply,
    ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, Matrix.trace_smul, Complex.real_smul]
  ring
theorem edgeFormPairing_add_left [Finite (PositiveEdge L n k j)]
    (f g h : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing (f + g) h = edgeFormPairing f h + edgeFormPairing g h :=
  traceFinsumPairing_add_left _ _ _
theorem edgeFormPairing_smul_left [Finite (PositiveEdge L n k j)] (c : ℝ)
    (f h : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing (c • f) h = (c : ℂ) * edgeFormPairing f h :=
  traceFinsumPairing_smul_left c _ _
theorem restrictToPositiveEdges_add (f g : Edge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (f + g) = restrictToPositiveEdges f + restrictToPositiveEdges g := rfl
theorem restrictToPositiveEdges_smul (c : ℝ) (f : Edge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (c • f) = c • restrictToPositiveEdges f := rfl
def sourceFormLinear [Finite (PositiveEdge L n k 0)] [Finite (PositiveEdge L n k k)]
    (U : Edge L n k 0 → ComplexMatrix2) (B : edgeFormSpace L n k 0) {W : Type} [AddCommGroup W]
    [Module ℝ W] (cur : W →ₗ[ℝ] edgeFormSpace L n k 0) (mul : W →ₗ[ℝ] edgeFormSpace L n k k) :
    W →ₗ[ℝ] ℝ where
  toFun a := sourceQuadraticForm U (cur a) (mul a) B
  map_add' a a' := by
    simp only [sourceQuadraticForm, map_add, Submodule.coe_add, edgeFormPairing_add_left,
      restrictToPositiveEdges_add, traceFinsumPairing_add_left, Complex.add_re]
    ring
  map_smul' c a := by
    simp only [sourceQuadraticForm, map_smul, Submodule.coe_smul, edgeFormPairing_smul_left,
      restrictToPositiveEdges_smul, traceFinsumPairing_smul_left, Complex.re_ofReal_mul,
      RingHom.id_apply, smul_eq_mul]
    ring
theorem inner_backgroundHessian_polarization {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)}
    (hc : IsEdgePairingCore c) {U : Edge L n k 0 → ComplexMatrix2} {J : edgeFormSpace L n k 0}
    {μ : edgeFormSpace L n k k} (hX : ∃ X, IsBackgroundHessian U J μ X)
    (B B' : edgeFormSpace L n k 0) :
    c.inner B (backgroundHessian U J μ B') =
      1 / 4 * (backgroundHessianForm U J μ (B + B') - backgroundHessianForm U J μ (B - B')) := by
  have hs : IsBackgroundHessian U J μ (backgroundHessian U J μ) := Classical.epsilon_spec hX
  have hq : ∀ x, c.inner x (backgroundHessian U J μ x) = backgroundHessianForm U J μ x :=
    fun x => by rw [hc, hs.2, Complex.ofReal_re]
  rw [inner_polarization c _ (fun x y => by rw [hc, hc, hs.1]) B B', hq, hq]
end Functions
section Point
variable {L n k : ℕ} [iR : Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)]
def productPointsOver (𝒰 : Set (Edge L n k 0 → ComplexMatrix2)) : Set (ProductPoint L n k) :=
  subspaceTimesGroup (hermitianTracelessFunctions (SourceEdge L n k)) (PositiveEdge L n k 0) ∩
    {q | fieldOfProductPoint q ∈ 𝒰}
theorem analyticReal_fieldOfProductPoint (hC : AnalyticCalculus.AnalyticCalculusStatement)
    {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)} {F : (Edge L n k 0 → ComplexMatrix2) → ℝ}
    (h : IsAnalyticFieldFunction 𝒰 F) :
    IsAnalyticReal (R := PositiveEdge L n k 0) (S := SourceEdge L n k)
      (hermitianTracelessFunctions (SourceEdge L n k)) (productPointsOver 𝒰)
      fun q => F (fieldOfProductPoint q) := by
  obtain ⟨-, i, a⟩ := h
  obtain rfl : i = iR := Subsingleton.elim _ _
  have hc := (hC (SourceEdge L n k) (PositiveEdge L n k 0) Empty (PositiveEdge L n k 0)).2.2.2
    (hermitianTracelessFunctions (SourceEdge L n k)) ⊥ le_rfl bot_le
  have hcomp := ((hc.2.2.1 _ (isOpen_subspaceTimesGroup le_rfl)).2.2.1 _ hc.2.1.2).2 _ a.1
  exact hcomp.2.1 1 _ a
theorem analyticReal_backgroundHessianForm (hH : ExpChartHolomorphy.ExpChartTheory)
    (H : LocalAnalyticity.LocalAnalyticityStatement)
    (hC : AnalyticCalculus.AnalyticCalculusStatement) {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)}
    (hQa : ∀ (J B : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k),
      IsAnalyticFieldFunction 𝒰 fun U => backgroundHessianForm U J μ B)
    (cur : hermitianTracelessFunctions (SourceEdge L n k) →ₗ[ℝ] edgeFormSpace L n k 0)
    (mul : hermitianTracelessFunctions (SourceEdge L n k) →ₗ[ℝ] edgeFormSpace L n k k) {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (hermitianTracelessFunctions (SourceEdge L n k)))
    (B : edgeFormSpace L n k 0) :
    IsAnalyticReal (R := PositiveEdge L n k 0) (S := SourceEdge L n k)
      (hermitianTracelessFunctions (SourceEdge L n k)) (productPointsOver 𝒰) fun q =>
        backgroundHessianForm (fieldOfProductPoint q) (cur (subspaceMember _ q))
          (mul (subspaceMember _ q)) B := by
  have hF := fun x => analyticReal_fieldOfProductPoint hC (hQa (cur x) B (mul x))
  have hW := (hF 0).1
  have hco := fun i => analyticReal_mono H
    (analyticReal_basis_repr (R := PositiveEdge L n k 0) hC le_rfl b i) hW inter_subset_left
  have hdiff : ∀ i, IsAnalyticReal (R := PositiveEdge L n k 0) (S := SourceEdge L n k)
      (hermitianTracelessFunctions (SourceEdge L n k)) (productPointsOver 𝒰) fun q =>
        backgroundHessianForm (fieldOfProductPoint q) (cur (b i)) (mul (b i)) B -
          backgroundHessianForm (fieldOfProductPoint q) (cur 0) (mul 0) B := fun i =>
    analyticReal_congr (analyticReal_add H (hF (b i)) (analyticReal_smul hH (hF 0) (-1)))
      fun q _ => by ring
  have hsum := analyticReal_add H (hF 0) (analyticReal_sum H hC hW Finset.univ (fun i q =>
    b.repr (subspaceMember _ q) i *
      (backgroundHessianForm (fieldOfProductPoint q) (cur (b i)) (mul (b i)) B -
        backgroundHessianForm (fieldOfProductPoint q) (cur 0) (mul 0) B))
    fun i _ => analyticReal_mul hH H (hco i) (hdiff i))
  refine analyticReal_congr hsum fun q _ => ?_
  refine (affine_eq_basis_expansion b (sourceFormLinear (fieldOfProductPoint q) B cur mul)
    (leftSecondDeriv (plaquetteAction L n k) (fieldOfProductPoint q) B B +
      traceFinsumNorm (gaugeSliceResidual (fieldOfProductPoint q) B :
        Vertex L n k 0 → ComplexMatrix2) ^ 2)
    (fun a => backgroundHessianForm (fieldOfProductPoint q) (cur a) (mul a) B)
    (fun a => ?_) (subspaceMember _ q)).symm
  change backgroundHessianForm _ _ _ _ = _ + sourceQuadraticForm _ _ _ _
  unfold backgroundHessianForm
  ring
theorem exists_analytic_domain (hH : ExpChartHolomorphy.ExpChartTheory)
    (H : LocalAnalyticity.LocalAnalyticityStatement)
    (hC : AnalyticCalculus.AnalyticCalculusStatement)
    (hnb₀ : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (hnbk : ∀ b : Edge L n k k, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)} (h𝒰 : IsOpenNhdOfOne 𝒰)
    (hEf : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k)
    (hEs : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k)
    (hform : BackgroundFunctionalWellDefined (trivialField L n k 0) 0 0)
    (hOp : ∀ U ∈ 𝒰, ∀ (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k),
      ∃ X, IsBackgroundHessian U J μ X)
    (hQa : ∀ (J B : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k),
      IsAnalyticFieldFunction 𝒰 fun U => backgroundHessianForm U J μ B)
    (hCa : ∀ (B : edgeFormSpace L n k 0) (C : edgeFormSpace L n k k),
      IsAnalyticFieldFunction 𝒰 fun U =>
        (edgeFormPairing (C : Edge L n k k → ComplexMatrix2)
          (iterCovariantDerivLinear L n k U B : Edge L n k k → ComplexMatrix2)).re)
    (hDa : ∀ l l' : vertexFunctionSpace L n k 0, IsAnalyticFieldFunction 𝒰 fun U =>
      (traceFinsumPairing (l : Vertex L n k 0 → ComplexMatrix2)
        (covDiffRealTranspose L n k U (covDiffLinear L n k U l') :
          Vertex L n k 0 → ComplexMatrix2)).re)
    (hAa : ∀ (l : vertexFunctionSpace L n k 0) (g : vertexFunctionSpace L n k k),
      IsAnalyticFieldFunction 𝒰 fun U =>
        (traceFinsumPairing (g : Vertex L n k k → ComplexMatrix2)
          (iterAverageLinear L n k U l : Vertex L n k k → ComplexMatrix2)).re) :
    ∃ 𝒲 : Set (ProductPoint L n k), identityProductPoint L n k ∈ 𝒲 ∧
      (∀ q ∈ 𝒲, BackgroundFunctionalDefinedAt q) ∧
      IsAnalyticReal (R := PositiveEdge L n k 0) (S := SourceEdge L n k)
        (hermitianTracelessFunctions (SourceEdge L n k)) 𝒲 backgroundFunctionalAt := by
  classical
  have hfd : FiniteDimensional ℝ (hermitianTracelessFunctions (SourceEdge L n k)) :=
    (hC (SourceEdge L n k) Empty Empty Empty).1 _ le_rfl
  have fd₁ := hEf.1.1
  have fd₂ := hEf.2.1
  have fd₃ := hEs.1.1
  have fd₄ := hEs.2.1
  let cur := positiveEdgeFormMap hnb₀ (Sum.inl : PositiveEdge L n k 0 → SourceEdge L n k)
  let mul := positiveEdgeFormMap hnbk (Sum.inr : PositiveEdge L n k k → SourceEdge L n k)
  let b := Module.finBasis ℝ (hermitianTracelessFunctions (SourceEdge L n k))
  obtain ⟨d₁, d₂, e, f, hdet₁⟩ := saddleDet_eq_det_blockMatrix hEf.1.2.choose hEf.2.2.choose
  obtain ⟨d₃, d₄, e', f', hdet₂⟩ := saddleDet_eq_det_blockMatrix hEs.1.2.choose hEs.2.2.choose
  let D₁ : ProductPoint L n k → ℝ := fun q =>
    hessianSaddleDet (fieldOfProductPoint q) (cur (subspaceMember _ q))
      (mul (subspaceMember _ q))
  let D₂ : ProductPoint L n k → ℝ := fun q =>
    ghostSaddleDet L n k (fieldOfProductPoint q)
  have hW := (analyticReal_fieldOfProductPoint hC (hQa 0 0 0)).1
  have hD₁ : IsAnalyticReal (R := PositiveEdge L n k 0) (S := SourceEdge L n k)
      (hermitianTracelessFunctions (SourceEdge L n k)) (productPointsOver 𝒰) D₁ := by
    refine analyticReal_congr (analyticReal_det hH H hC hW (fun q =>
      saddleBlockMatrix hEf.1.2.choose hEf.2.2.choose e f
        (backgroundHessian (fieldOfProductPoint q) (cur (subspaceMember _ q))
          (mul (subspaceMember _ q)))
        (iterCovariantDerivLinear L n k (fieldOfProductPoint q))) fun x y => ?_)
      fun q _ => ?_
    · rcases x with i | i <;> rcases y with j | j
      · refine analyticReal_congr (analyticReal_smul hH (analyticReal_add H
          (analyticReal_backgroundHessianForm hH H hC hQa cur mul b (e i + e j))
          (analyticReal_smul hH
            (analyticReal_backgroundHessianForm hH H hC hQa cur mul b (e i - e j)) (-1)))
          (1 / 4)) fun q hq => ?_
        simp only [saddleBlockMatrix, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
        rw [inner_backgroundHessian_polarization hEf.1.2.choose_spec (hOp _ hq.2 _ _)]
        ring
      · refine analyticReal_congr (analyticReal_fieldOfProductPoint hC (hCa (e i) (f j)))
          fun q _ => ?_
        simp only [saddleBlockMatrix, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
        exact (hEf.2.2.choose_spec _ _).symm
      · refine analyticReal_congr (analyticReal_fieldOfProductPoint hC (hCa (e j) (f i)))
          fun q _ => ?_
        simp only [saddleBlockMatrix, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
        exact (hEf.2.2.choose_spec _ _).symm
      · simpa [saddleBlockMatrix] using analyticReal_const hC hW 0
    · change _ = hessianSaddleDet _ _ _
      unfold hessianSaddleDet saddleDetOnEdgeForms
      rw [dif_pos hEf]
      exact (hdet₁ _ _).symm
  have hD₂ : IsAnalyticReal (R := PositiveEdge L n k 0) (S := SourceEdge L n k)
      (hermitianTracelessFunctions (SourceEdge L n k)) (productPointsOver 𝒰) D₂ := by
    refine analyticReal_congr (analyticReal_det hH H hC hW (fun q =>
      saddleBlockMatrix hEs.1.2.choose hEs.2.2.choose e' f'
        (covDiffRealTranspose L n k (fieldOfProductPoint q) ∘ₗ
          covDiffLinear L n k (fieldOfProductPoint q))
        (iterAverageLinear L n k (fieldOfProductPoint q))) fun x y => ?_) fun q _ => ?_
    · rcases x with i | i <;> rcases y with j | j
      · refine analyticReal_congr (analyticReal_fieldOfProductPoint hC (hDa (e' i) (e' j)))
          fun q _ => ?_
        simp only [saddleBlockMatrix, Matrix.fromBlocks_apply₁₁, Matrix.of_apply,
          LinearMap.comp_apply]
        exact (hEs.1.2.choose_spec _ _).symm
      · refine analyticReal_congr (analyticReal_fieldOfProductPoint hC (hAa (e' i) (f' j)))
          fun q _ => ?_
        simp only [saddleBlockMatrix, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
        exact (hEs.2.2.choose_spec _ _).symm
      · refine analyticReal_congr (analyticReal_fieldOfProductPoint hC (hAa (e' j) (f' i)))
          fun q _ => ?_
        simp only [saddleBlockMatrix, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
        exact (hEs.2.2.choose_spec _ _).symm
      · simpa [saddleBlockMatrix] using analyticReal_const hC hW 0
    · change _ = ghostSaddleDet _ _ _ _
      unfold ghostSaddleDet saddleDetOnVertexFunctions
      rw [dif_pos hEs]
      exact (hdet₂ _ _).symm
  have hO₁ := isOpen_ne_zero hH hD₁
  have hO₂ := isOpen_ne_zero hH (analyticReal_mono H hD₂ hO₁ inter_subset_left)
  have hcur : ∀ q ∈ subspaceTimesGroup (hermitianTracelessFunctions (SourceEdge L n k))
      (PositiveEdge L n k 0),
      ((cur (subspaceMember _ q) : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
        sourceOfProductPoint q := by
    intro q hq
    change edgeFormOfPositiveValues (fun c =>
      ((subspaceMember _ q : hermitianTracelessFunctions (SourceEdge L n k)) :
        SourceEdge L n k → ComplexMatrix2) (Sum.inl c)) = _
    rw [subspaceMember_coe hq]
    rfl
  have hmul : ∀ q ∈ subspaceTimesGroup (hermitianTracelessFunctions (SourceEdge L n k))
      (PositiveEdge L n k 0),
      ((mul (subspaceMember _ q) : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2) =
        multiplierOfProductPoint q := by
    intro q hq
    change edgeFormOfPositiveValues (fun c =>
      ((subspaceMember _ q : hermitianTracelessFunctions (SourceEdge L n k)) :
        SourceEdge L n k → ComplexMatrix2) (Sum.inr c)) = _
    rw [subspaceMember_coe hq]
    rfl
  refine ⟨(productPointsOver 𝒰 ∩ {q | D₁ q ≠ 0}) ∩ {q | D₂ q ≠ 0}, ?_, ?_, ?_⟩
  · have hp : identityProductPoint L n k ∈
        subspaceTimesGroup (hermitianTracelessFunctions (SourceEdge L n k))
          (PositiveEdge L n k 0) := by
      refine ⟨?_, fun r => ?_⟩
      · change (0 : SourceEdge L n k → ComplexMatrix2) ∈ _
        exact zero_mem _
      · exact one_mem _
    have hU : fieldOfProductPoint (identityProductPoint L n k) = trivialField L n k 0 := by
      funext b'
      simp only [fieldOfProductPoint, fieldOfPositiveValues, identityProductPoint,
        groupComponent, ofParts, Sum.elim_inl]
      split_ifs <;> simp
    have hm : subspaceMember (hermitianTracelessFunctions (SourceEdge L n k))
        (identityProductPoint L n k) = 0 :=
      Subtype.ext (subspaceMember_coe hp)
    refine ⟨⟨⟨hp, ?_⟩, ?_⟩, ?_⟩
    · change fieldOfProductPoint _ ∈ 𝒰
      rw [hU]
      exact h𝒰.2
    · change hessianSaddleDet _ _ _ ≠ 0
      rw [hU, hm, map_zero, map_zero]
      exact hform.1
    · change ghostSaddleDet _ _ _ _ ≠ 0
      rw [hU]
      exact hform.2
  · rintro q ⟨⟨⟨hq, -⟩, h1⟩, h2⟩
    exact ⟨cur (subspaceMember _ q), mul (subspaceMember _ q), hcur q hq, hmul q hq, h1, h2⟩
  · have hr := analyticReal_add H
      (analyticReal_smul hH (analyticReal_log_abs hH
        (analyticReal_mono H hD₁ hO₂ fun q hq => hq.1.1) fun p hp => hp.1.2) (-(1 / 2)))
      (analyticReal_log_abs hH (analyticReal_mono H hD₂ hO₂ fun q hq => hq.1.1)
        fun p hp => hp.2)
    refine analyticReal_congr hr fun q hq => ?_
    have hqs := hq.1.1.1
    have hJ : sourceOfProductPoint q ∈ edgeFormSpace L n k 0 := hcur q hqs ▸ (cur _).2
    have hμ : multiplierOfProductPoint q ∈ edgeFormSpace L n k k := hmul q hqs ▸ (mul _).2
    have e₁ : (⟨sourceOfProductPoint q, hJ⟩ : edgeFormSpace L n k 0) =
        cur (subspaceMember _ q) :=
      Subtype.ext (hcur q hqs).symm
    have e₂ : (⟨multiplierOfProductPoint q, hμ⟩ : edgeFormSpace L n k k) =
        mul (subspaceMember _ q) :=
      Subtype.ext (hmul q hqs).symm
    unfold backgroundFunctionalAt
    rw [dif_pos ⟨hJ, hμ⟩, e₁, e₂]
    rfl
end Point
end Tower.BackgroundFunctionalAnalyticity
open Tower.BackgroundFunctionalAnalyticity Tower Matrices Matrices.GroupLieProduct
  Matrices.GroupLieProduct.Subspaces in
theorem Tower.backgroundFunctionalAnalyticNearIdentity_holds
    (h₁ : Tower.BackgroundDeterminantEntriesAnalytic)
    (h₂ : Tower.BackgroundFunctionalWellDefinedAtTrivialField)
    (h₃ : Tower.RealQuadraticTransposes.Statement)
    (h₄ : LocalAnalyticity.LocalAnalyticityStatement)
    (h₅ : AnalyticCalculus.AnalyticCalculusStatement)
    (h₆ : ExpChartHolomorphy.ExpChartTheory)
    (h₇ : Tower.BondSetFields.ProductStructureHolds)
    (h₈ : Tower.FiniteSideFormSpaces) :
    Tower.BackgroundFunctionalAnalyticNearIdentityAtEverySide := by
  intro L n k hL hn hk
  obtain ⟨𝒰₀, ho, hQa, hCa, hDa, hAa⟩ := h₁ L n k hL hn hk
  obtain ⟨hfin₀, fd₀, -, c₀, e₀⟩ := h₈ L n k 0 hL hn (Nat.zero_le k)
  obtain ⟨hfink, fdk, -, ck, ek⟩ := h₈ L n k k hL hn le_rfl
  have hform := h₂ L n k hL hn hk
  have hEf : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k :=
    ⟨⟨fd₀, c₀, fun B B' => by rw [e₀ B B', Complex.ofReal_re]⟩,
      ⟨fdk, ck, fun B B' => by rw [ek B B', Complex.ofReal_re]⟩⟩
  have hEs : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k := by
    by_contra hno
    apply hform.2
    unfold ghostSaddleDet saddleDetOnVertexFunctions
    rw [dif_neg hno]
  obtain ⟨𝒰, h𝒰, hsub, hP⟩ := exists_isOpenNhdOfOne_subset
    (P := fun U => ∀ (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k),
      ∃ X, IsBackgroundHessian U J μ X)
    h₇ hL hn (Nat.zero_le k) ho (by
      filter_upwards [(h₃ L n k hL hn hk).2] with U hU J μ
      exact (hU.2.2.existsUnique_hessian J μ).exists)
  letI i₀ := Fintype.ofFinite (PositiveEdge L n k 0)
  letI i₁ := Fintype.ofFinite (PositiveEdge L n k k)
  have hop := h𝒰.1
  obtain ⟨𝒲, a, b, c⟩ := exists_analytic_domain h₆ h₄ h₅
    (fun b => not_isPositivelyOriented_opposite h₇ hL hn (Nat.zero_le k) b)
    (fun b => not_isPositivelyOriented_opposite h₇ hL hn le_rfl b) h𝒰 hEf hEs hform hP
    (fun J B μ => isAnalyticFieldFunction_mono h₄ (hQa J B μ) hop hsub)
    (fun B C => isAnalyticFieldFunction_mono h₄ (hCa B C) hop hsub)
    (fun l l' => isAnalyticFieldFunction_mono h₄ (hDa l l') hop hsub)
    (fun l g => isAnalyticFieldFunction_mono h₄ (hAa l g) hop hsub)
  exact ⟨i₀, i₁, 𝒲, a, b, c⟩
end YangMills.Construction
end
